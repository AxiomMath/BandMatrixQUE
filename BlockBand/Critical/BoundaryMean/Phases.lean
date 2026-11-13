module

public import BlockBand.Critical.BoundaryMean.Fubini
public import BlockBand.Critical.Collar.DilationVariance

/-!
# Retained and exceptional dilation phases

* `exceptional_phase_mass`: Cauchy mass of `{t : d(X_t) > d(X) + ε}` is `≤ C g/(W ε²)`, from
  `Collar.dilation_trace_pow_exceptional_phases` (`k = 1`, the two block projectors `blockProj j`,
  `‖blockProj j‖ ≤ 1`), with `g = dissipationWeight = conductance (oldScattering b e X)`
  (`dissipationWeight_eq`). At `ε = W^{-1/8}` this is `C g W^{-3/4}`.
* `abs_integral_sub_le_of_phases`: `|E_t h - c| ≤ a + K P(E)` if `|h - c| ≤ a` off `E` and `≤ K`
  everywhere.
* Scalar facts: `omitted_rate_le` (`(a√W + 1)/(W·W^{-1/4}) ≤ (a + 1)W^{-1/4}`), `Im z_b ≤ 1`,
  `‖conj(z_b + e)‖ ≤ 5` on the bulk.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Collar.Density (collarMatrix collarRowVec collarRowConst)
open BlockBand.Critical.Collar.Kernel (topLift rePart)
open BlockBand.Critical.Collar (stdCauchy dilationResolvent absorbedResolvent dissipationWeight)
open scoped ComplexOrder ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The diagonal projector onto the old port block `j`. -/
def blockProj (j : Fin 2) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  diagonal fun x => if x.1 = j then 1 else 0

theorem norm_blockProj_le (j : Fin 2) : ‖(blockProj j : Matrix (Fin 2 × Fin W) _ ℂ)‖ ≤ 1 := by
  rw [blockProj, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun x => ?_
  split_ifs <;> simp

theorem blockTrace_eq_trace (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) :
    blockTrace M j = (W : ℂ)⁻¹ * trace (blockProj j * M) := by
  rw [blockTrace, blockProj, trace]
  congr 1
  simp only [diag_apply, diagonal_mul, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
  simp

theorem blockTrace_sub (M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) :
    blockTrace (M - N) j = blockTrace M j - blockTrace N j := by
  simp only [blockTrace, Matrix.sub_apply, Finset.sum_sub_distrib]
  ring

/-- Scalar distance under a perturbation of both block traces. -/
theorem matchedDistance_le_add (b e : ℝ) (X X' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {ε : ℝ} (h : ∀ j : Fin 2, ‖blockTrace ((boundaryZ b e • 1 - X')⁻¹ -
      (boundaryZ b e • 1 - X)⁻¹) j‖ ≤ ε) :
    matchedDistance b e X' ≤ matchedDistance b e X + ε := by
  have hj : ∀ j : Fin 2, ‖blockTrace ((boundaryZ b e • 1 - X')⁻¹) j - matchedA e‖ ≤
      ‖blockTrace ((boundaryZ b e • 1 - X)⁻¹) j - matchedA e‖ + ε := by
    intro j
    have := h j
    rw [blockTrace_sub] at this
    calc ‖blockTrace ((boundaryZ b e • 1 - X')⁻¹) j - matchedA e‖
        = ‖(blockTrace ((boundaryZ b e • 1 - X)⁻¹) j - matchedA e) +
          (blockTrace ((boundaryZ b e • 1 - X')⁻¹) j - blockTrace ((boundaryZ b e • 1 - X)⁻¹) j)‖ := by
          ring_nf
      _ ≤ _ := (norm_add_le _ _).trans (by gcongr)
  unfold matchedDistance
  refine max_le ((hj 0).trans ?_) ((hj 1).trans ?_)
  · gcongr; exact le_max_left _ _
  · gcongr; exact le_max_right _ _

theorem dilationResolvent_eq (z : ℂ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (t : ℝ) :
    dilationResolvent (rePart X) (-imPart X) z t = (z • 1 - dilatedOld X t)⁻¹ := by
  rw [dilationResolvent, dilatedOld]
  congr 1
  abel

theorem absorbedResolvent_eq (z : ℂ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    absorbedResolvent (rePart X) (-imPart X) z = (z • 1 - X)⁻¹ := by
  rw [absorbedResolvent]
  congr 1
  conv_rhs => rw [← Collar.Kernel.rePart_sub_I_smul_neg_imPart X]
  abel

theorem dissipationWeight_eq (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosSemidef) :
    dissipationWeight (rePart X) (-imPart X) (boundaryZ b e) =
      conductance (oldScattering b e X) := by
  have h := Collar.re_trace_one_sub_conjTranspose_mul_scattering
    (Collar.Kernel.rePart_isHermitian X) hY hη
  rw [← h, conductance, Collar.Kernel.rePart_sub_I_smul_neg_imPart X]
  congr 4 <;> simp [oldScattering]

/-- **Retained and omitted phases** (abstract form): if `|h - c| ≤ a` off `E` and `|h - c| ≤ K`
everywhere, then `|E_t h - c| ≤ a + K m` whenever `P(E) ≤ m`. -/
theorem abs_integral_sub_le_of_phases {h : ℝ → ℝ} (hint : Integrable h stdCauchy) {E : Set ℝ}
    {c a K m : ℝ} (ha : 0 ≤ a) (hK0 : 0 ≤ K) (hm0 : 0 ≤ m)
    (hK : ∀ t, |h t - c| ≤ K) (hret : ∀ t ∉ E, |h t - c| ≤ a)
    (hm : stdCauchy E ≤ ENNReal.ofReal m) :
    |∫ t, h t ∂stdCauchy - c| ≤ a + K * m := by
  set E' := toMeasurable stdCauchy E
  have hE' : MeasurableSet E' := measurableSet_toMeasurable _ _
  have hsub : ∫ t, h t ∂stdCauchy - c = ∫ t, (h t - c) ∂stdCauchy := by
    rw [integral_sub hint (integrable_const c)]
    simp
  have hφ : Integrable (fun t => a + K * E'.indicator (fun _ => (1 : ℝ)) t) stdCauchy :=
    (integrable_const a).add ((integrable_const (1 : ℝ)).indicator hE' |>.const_mul K)
  have hpt : ∀ t, |h t - c| ≤ a + K * E'.indicator (fun _ => (1 : ℝ)) t := by
    intro t
    by_cases ht : t ∈ E'
    · rw [Set.indicator_of_mem ht, mul_one]; linarith [hK t]
    · rw [Set.indicator_of_notMem ht, mul_zero, add_zero]
      exact hret t fun htE => ht (subset_toMeasurable _ _ htE)
  rw [hsub]
  refine (abs_integral_le_integral_abs).trans ?_
  refine (integral_mono (hint.sub (integrable_const c)).abs hφ hpt).trans ?_
  rw [integral_add (integrable_const a) ((integrable_const (1 : ℝ)).indicator hE' |>.const_mul K),
    integral_const_mul, integral_indicator hE']
  simp only [integral_const, smul_eq_mul, mul_one, probReal_univ, one_mul]
  have hμ : stdCauchy.real E' ≤ m := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hm0 hm
  rw [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter]
  nlinarith

/-- **Exceptional dilation phases** (the dilation variance lemma with `k = 1` and the block
projectors):
the Cauchy mass of the phases with `d(X_t) > d(X) + ε` is at most `C g/(W ε²)`, `g = Tr(I - r*r)`,
uniformly in `W ≥ 1`, `Im z_b ≥ η₀`, `Y ⪰ 0` and `ε > 0`. -/
theorem exceptional_phase_mass {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → ∀ b e : ℝ, η₀ ≤ (boundaryZ b e).im →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (-imPart X).PosSemidef →
      ∀ ε : ℝ, 0 < ε →
        stdCauchy {t | ¬ matchedDistance b e (dilatedOld X t) ≤ matchedDistance b e X + ε} ≤
          ENNReal.ofReal (C * conductance (oldScattering b e X) / (W * ε ^ 2)) := by
  obtain ⟨C, hC, h⟩ := Collar.dilation_trace_pow_exceptional_phases 1 2 2 η₀ hη₀
  refine ⟨C, hC, fun W hW b e hη X hY ε hε => ?_⟩
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hcard : (Fintype.card (Fin 2 × Fin W) : ℝ) ≤ 2 * W := by simp
  have hη' : 0 < (boundaryZ b e).im := hη₀.trans_le hη
  have hmain := h (W : ℝ) hWr (Fin 2 × Fin W) hcard (rePart X) (-imPart X) (boundaryZ b e)
    (Collar.Kernel.rePart_isHermitian X) hY hη (fun j => blockProj j) (fun _ => 1)
    (fun j => norm_blockProj_le j) (fun _ => le_refl 1) ε hε
  rw [dissipationWeight_eq b e hη' hY] at hmain
  refine (measure_mono ?_).trans hmain
  intro t ht
  simp only [Set.mem_ofPred_eq] at ht ⊢
  by_contra hcon
  push Not at hcon
  refine ht (matchedDistance_le_add b e X (dilatedOld X t) fun j => ?_)
  have := (hcon j).le
  rw [pow_one, pow_one, dilationResolvent_eq, absorbedResolvent_eq, Complex.ofReal_natCast] at this
  rw [blockTrace_eq_trace]
  exact this

/-- `(W^{-1/8})² = W^{-1/4}` and `W (W^{-1/4})² = √W` (`W > 0`). -/
theorem rpow_eighth_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (-(1 : ℝ) / 8)) ^ 2 = x ^ (-(1 : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num

theorem mul_rpow_quarter_sq {x : ℝ} (hx : 0 < x) :
    x * (x ^ (-(1 : ℝ) / 4)) ^ 2 = Real.sqrt x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, Real.sqrt_eq_rpow]
  have h1 : x * x ^ (-(1 : ℝ) / 4 * ((2 : ℕ) : ℝ)) = x ^ ((1 : ℝ) + -(1 : ℝ) / 4 * ((2 : ℕ) : ℝ)) := by
    rw [Real.rpow_add hx, Real.rpow_one]
  rw [h1]
  norm_num

/-- `(a√W + 1)/(W (W^{-1/8})²) ≤ (a + 1) W^{-1/4}` for `W ≥ 1`. -/
theorem omitted_rate_le {x : ℝ} (hx : 1 ≤ x) (a : ℝ) :
    (a * Real.sqrt x + 1) / (x * (x ^ (-(1 : ℝ) / 8)) ^ 2) ≤ (a + 1) * x ^ (-(1 : ℝ) / 4) := by
  have hx0 : 0 < x := by linarith
  have hw : 0 < x ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos hx0 _
  rw [rpow_eighth_sq hx0, div_le_iff₀ (by positivity)]
  have h2 := mul_rpow_quarter_sq hx0
  have hs : 1 ≤ Real.sqrt x := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx
  calc a * Real.sqrt x + 1 ≤ (a + 1) * Real.sqrt x := by nlinarith
    _ = (a + 1) * x ^ (-(1 : ℝ) / 4) * (x * x ^ (-(1 : ℝ) / 4)) := by
        rw [← h2]; ring

/-- `Im z_b ≤ 1` on `bulkInterval κ` (`b ≥ 0`). -/
theorem boundaryZ_im_le_one {b κ e : ℝ} (hb0 : 0 ≤ b) (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    (boundaryZ b e).im ≤ 1 := by
  have habs : |e| ≤ 2 := (BlockBand.Layers.abs_le_of_mem_bulkInterval he).trans (by linarith)
  rw [BlockBand.Layers.boundaryZ_im habs, BlockBand.Layers.matchedA_im]
  have hs : Real.sqrt (4 - e ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs0 := Real.sqrt_nonneg (4 - e ^ 2)
  have hb1 : b < 1 ∨ 1 ≤ b := lt_or_ge b 1
  nlinarith

/-- `‖conj(z_b + e)‖ ≤ 5` on `bulkInterval κ` (`0 ≤ b ≤ 1`). -/
theorem norm_rowCoeff_le {b κ e : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hκ : 0 < κ)
    (he : e ∈ bulkInterval κ) : ‖Collar.Kernel.rowCoeff b e 0‖ ≤ ‖(5 : ℂ)‖ := by
  have habs : |e| ≤ 2 := (BlockBand.Layers.abs_le_of_mem_bulkInterval he).trans (by linarith)
  have hz := BlockBand.Layers.norm_boundaryZ_le hb0 hb1 habs
  rw [Collar.Kernel.rowCoeff, norm_star]
  calc ‖boundaryZ b e + ((e + 0 : ℝ) : ℂ)‖ ≤ ‖boundaryZ b e‖ + ‖((e + 0 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ 3 + 2 := by
        gcongr
        rw [Complex.norm_real, add_zero, Real.norm_eq_abs]
        exact habs
    _ = ‖(5 : ℂ)‖ := by norm_num

end BlockBand.Critical.BoundaryMean
