module

public import BlockBand.Coarea.FreshPalmDensityRank
public import BlockBand.Coarea.FixedOmegaGaussian
public import BlockBand.Coarea.ContractClauses

/-!
# Domination bounds for the fresh eigenpair fiber

*Measures.* `gueMeasure ι t` (`GUE_ι(t)`, any `t : ℝ≥0`, any finite `ι`). Entrywise
complex norms. Exact finite bounds; no limit.

* `lintegral_ofReal_entrySum_pow_lt_top`: `∫ (a + Σ_ab |G_ab|)^m dGUE_ι(t) < ∞` (all
  polynomial moments; from the circular Gaussian representation).
* `normSq_det_le`: `|det M|² ≤ (n! xⁿ)²` when all entries satisfy `|M_ij| ≤ x`.
* `norm_frameM_apply_le`: entries of `M = U*FU + G' - E` for an orthonormal frame `U` are
  bounded by `Σ|F_kl| + Σ|G'_ab| + |E|`.
* `regressionFactor_le_one`, `coareaConstant_nonneg`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FreshPalm

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
  BlockBand.Coarea.ContractClauses BlockBand.SourceProcess
open scoped ENNReal NNReal ComplexConjugate

section Moment

variable {ι : Type*} [Fintype ι]

/-- Entrywise bound of a GUE sample by the real circular inputs. -/
theorem norm_gueSample_circ_le (t : ℝ≥0) (r : RealIndex ι → ℝ) (a b : ι) :
    ‖gueSample t (circularBrownianCoordinates r) a b‖ ≤ 4 * gueScale t * ∑ k, |r k| := by
  have hs : 0 ≤ gueScale t := by unfold gueScale; positivity
  have hk : ∀ k, |r k| ≤ ∑ k, |r k| := fun k =>
    Finset.single_le_sum (f := fun k => |r k|) (fun k _ => abs_nonneg (r k)) (Finset.mem_univ k)
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [gueSample_circ_re, gueSample_circ_im, abs_mul, abs_mul, abs_of_nonneg hs]
  have h1 := abs_add_le (r ((a, b), 0)) (r ((b, a), 0))
  have h2 := abs_sub (r ((a, b), 1)) (r ((b, a), 1))
  have := hk ((a, b), 0); have := hk ((b, a), 0); have := hk ((a, b), 1); have := hk ((b, a), 1)
  nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 hs]

/-- Entry sum of a matrix. -/
def entrySum (G : Matrix ι ι ℂ) : ℝ := ∑ a, ∑ b, ‖G a b‖

theorem entrySum_nonneg (G : Matrix ι ι ℂ) : 0 ≤ entrySum G :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem continuous_entrySum : Continuous (entrySum (ι := ι)) := by
  unfold entrySum
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (continuous_apply_apply a b).norm

theorem norm_apply_le_entrySum (G : Matrix ι ι ℂ) (a b : ι) : ‖G a b‖ ≤ entrySum G := by
  classical
  unfold entrySum
  calc ‖G a b‖ ≤ ∑ b', ‖G a b'‖ :=
        Finset.single_le_sum (f := fun b' => ‖G a b'‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', ‖G a' b'‖ :=
        Finset.single_le_sum (f := fun a' => ∑ b', ‖G a' b'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)

/-- All polynomial moments of the entry sum are finite under `GUE_ι(t)`. -/
theorem lintegral_ofReal_entrySum_pow_lt_top (t : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    ∫⁻ G, ENNReal.ofReal ((a + entrySum G) ^ m) ∂gueMeasure ι t < ∞ := by
  classical
  set K : ℝ := (Fintype.card ι : ℝ) ^ 2 * (4 * gueScale t)
  have hs : 0 ≤ gueScale t := by unfold gueScale; positivity
  have hK : 0 ≤ K := by positivity
  have hmeas : Measurable fun G : Matrix ι ι ℂ => ENNReal.ofReal ((a + entrySum G) ^ m) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_const.add continuous_entrySum).pow m).measurable
  unfold gueMeasure commonCircularIncrementLaw
  rw [Measure.map_map (measurable_gueSample t) measurable_circularBrownianCoordinates,
    lintegral_map hmeas ((measurable_gueSample t).comp measurable_circularBrownianCoordinates)]
  set P : Measure (RealIndex ι → ℝ) := Measure.pi fun _ : RealIndex ι => gaussianReal 0 1
  have hbound : ∀ r : RealIndex ι → ℝ,
      ENNReal.ofReal ((a + entrySum ((gueSample t ∘ circularBrownianCoordinates) r)) ^ m) ≤
        ENNReal.ofReal ((a + K * ∑ k, |r k|) ^ m) := by
    intro r
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (add_nonneg ha (entrySum_nonneg _))
    apply add_le_add_right
    unfold entrySum
    calc ∑ x, ∑ y, ‖(gueSample t ∘ circularBrownianCoordinates) r x y‖
        ≤ ∑ _x : ι, ∑ _y : ι, 4 * gueScale t * ∑ k, |r k| :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => norm_gueSample_circ_le t r x y
      _ = K * ∑ k, |r k| := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, K]; ring
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  have hmem : ∀ k : RealIndex ι, MemLp (fun r : RealIndex ι → ℝ => r k) (m : ℝ≥0) P := by
    intro k
    exact (memLp_id_gaussianReal (μ := 0) (v := 1) (m : ℝ≥0)).comp_measurePreserving
      (measurePreserving_eval (fun _ : RealIndex ι => gaussianReal 0 1) k)
  have hsum : MemLp (fun r : RealIndex ι → ℝ => a + K * ∑ k, |r k|) (m : ℝ≥0) P := by
    refine (memLp_const a).add ((memLp_finsetSum _ fun k _ => (hmem k).norm).const_mul K)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hint := hsum.integrable_norm_pow (p := m) (by omega)
    have : (fun r : RealIndex ι → ℝ => ‖a + K * ∑ k, |r k|‖ ^ m) =
        fun r => (a + K * ∑ k, |r k|) ^ m := by
      funext r
      rw [Real.norm_of_nonneg (add_nonneg ha (mul_nonneg hK
        (Finset.sum_nonneg fun k _ => abs_nonneg _)))]
    rw [this] at hint
    exact hint.lintegral_lt_top

end Moment

section Det

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `|det M|² ≤ (n! xⁿ)²` under an entrywise bound `|M_ij| ≤ x`. -/
theorem normSq_det_le (M : Matrix n n ℂ) {x : ℝ} (hx : ∀ i j, ‖M i j‖ ≤ x) :
    Complex.normSq M.det ≤ ((Fintype.card n).factorial * x ^ Fintype.card n) ^ 2 := by
  have h := Matrix.det_le (A := M) (abv := NormedField.toAbsoluteValue ℂ) hx
  simp only [NormedField.toAbsoluteValue_apply, nsmul_eq_mul] at h
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end Det

section Frame

variable {N : ℕ}

theorem norm_frame_apply_le {m : Type*} [Fintype m] [DecidableEq m]
    (U : Matrix (Fin N) m ℂ) (hUU : Uᴴ * U = 1) (k : Fin N) (i : m) : ‖U k i‖ ≤ 1 := by
  have h := congrFun (congrFun hUU i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have hsum : ∑ k, ‖U k i‖ ^ 2 = 1 := by
    have h' : ∑ k, star (U k i) * U k i = ((∑ k, ‖U k i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [RCLike.star_def, Complex.conj_mul']
    rw [h'] at h
    exact_mod_cast h
  have hle : ‖U k i‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun k => ‖U k i‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ k)
  nlinarith [norm_nonneg (U k i)]

/-- Entries of `M = U*FU + G' - E` for an orthonormal frame. -/
theorem norm_frameM_apply_le (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ)
    (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) (v : Fin N → ℂ)
    (G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ) (hUU : (U v)ᴴ * U v = 1)
    (i j : Fin (N - 1)) :
    ‖freshFrameM U F E v G' i j‖ ≤ entrySum F + entrySum G' + |E| := by
  unfold freshFrameM
  rw [Matrix.sub_apply, Matrix.add_apply]
  have h1 : ‖((U v)ᴴ * F * U v) i j‖ ≤ entrySum F := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    unfold entrySum
    rw [Finset.sum_comm]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, norm_mul, norm_star]
    have ha := norm_frame_apply_le (U v) hUU a i
    have hb := norm_frame_apply_le (U v) hUU b j
    calc ‖U v a i‖ * ‖F a b‖ * ‖U v b j‖ ≤ 1 * ‖F a b‖ * 1 := by
          gcongr
      _ = ‖F a b‖ := by ring
  have h2 : ‖G' i j‖ ≤ entrySum G' := norm_apply_le_entrySum G' i j
  have h3 : ‖((E : ℂ) • (1 : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ)) i j‖ ≤ |E| := by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij]; simp
  calc _ ≤ ‖((U v)ᴴ * F * U v) i j + G' i j‖ + ‖((E : ℂ) • (1 : Matrix (Fin (N - 1))
        (Fin (N - 1)) ℂ)) i j‖ := norm_sub_le _ _
    _ ≤ ‖((U v)ᴴ * F * U v) i j‖ + ‖G' i j‖ + ‖((E : ℂ) • (1 : Matrix (Fin (N - 1))
        (Fin (N - 1)) ℂ)) i j‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith

end Frame

theorem regressionFactor_nonneg {ι : Type*} [Fintype ι] (t E : ℝ) (v : ι → ℂ)
    (F : Matrix ι ι ℂ) : 0 ≤ regressionFactor t E v F := by
  unfold regressionFactor; exact (Real.exp_pos _).le

theorem regressionFactor_le_one {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 ≤ t) (E : ℝ)
    (v : ι → ℂ) (F : Matrix ι ι ℂ) : regressionFactor t E v F ≤ 1 := by
  unfold regressionFactor
  apply Real.exp_le_one_iff.mpr
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have : 0 ≤ (E - (star v ⬝ᵥ (F *ᵥ v)).re) ^ 2 +
      2 * l2Norm (F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) ^ 2 := by positivity
  linarith

theorem coareaConstant_nonneg (d : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ coareaConstant d t := by
  unfold coareaConstant; positivity

end BlockBand.Coarea.FreshPalm
