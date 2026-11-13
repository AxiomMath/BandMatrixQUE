module

public import BlockBand.Critical.Collar.Kernel.Reduction
public import BlockBand.Critical.Collar.DilationVariance
public import BlockBand.Critical.Collar.Density.RegularWindow

/-!
# Exceptional Cauchy phases of the matched distance

*Law.* `t ~ stdCauchy`; deterministic `X = X_h - iY`, `Y = -Im X ⪰ 0`, `X_t = X_h + tY`.

`stdCauchy_matchedDistance_gt_le`: for `b < 1`, `κ > 0` there is `C ≥ 0` with, for all `W ≥ 1`,
`e ∈ bulkInterval κ`, every such `X` and `d₁ > 0` with `d(X) ≤ d₁/2`,
`P_t(d(X_t) > d₁) ≤ C g /(W (d₁/2)²)`, `g = Tr(I - r*r)` (`conductance (oldScattering b e X)`).
Proof: `dilation_trace_pow_exceptional_phases` (`k = 1`, `D_j` = block projectors) and
`re_trace_one_sub_conjTranspose_mul_scattering`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open MeasureTheory Matrix
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The projector onto block `j` of `Fin 2 × Fin W`. -/
def blockProj (W : ℕ) (j : Fin 2) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  diagonal fun x => if x.1 = j then 1 else 0

theorem norm_blockProj_le (j : Fin 2) : ‖blockProj W j‖ ≤ 1 := by
  rw [blockProj, l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun x => ?_
  split_ifs <;> simp

theorem inv_mul_trace_blockProj (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) :
    (W : ℂ)⁻¹ * trace (blockProj W j * M) = blockTrace M j := by
  simp only [blockProj, blockTrace, trace, diag, diagonal_mul, ite_mul, one_mul, zero_mul,
    Fintype.sum_prod_type]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem blockTrace_sub (M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) :
    blockTrace (M - N) j = blockTrace M j - blockTrace N j := by
  simp only [blockTrace, Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]

/-- **Exceptional phases**: `P_t(d(X_t) > d₁) ≤ C g/(W(d₁/2)²)` when `d(X) ≤ d₁/2`. -/
theorem stdCauchy_matchedDistance_gt_le {b κ : ℝ} (hb1 : b < 1) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → ∀ e ∈ bulkInterval κ,
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (-Critical.imPart X).PosSemidef →
      ∀ d₁ : ℝ, 0 < d₁ → matchedDistance b e X ≤ d₁ / 2 →
        stdCauchy {t : ℝ | d₁ < matchedDistance b e (rePart X + (t : ℂ) • (-Critical.imPart X))} ≤
          ENNReal.ofReal (C * Critical.conductance (Critical.oldScattering b e X) /
            (W * (d₁ / 2) ^ 2)) := by
  set κ' := min κ 2
  have hκ' : 0 < κ' := lt_min hκ two_pos
  set η₀ := (1 - b) * Real.sqrt (4 - (2 - κ') ^ 2) / 2
  have hη₀ : 0 < η₀ := by
    have : 0 < 4 - (2 - κ') ^ 2 :=
      BlockBand.Layers.four_sub_sq_pos hκ' (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    have : 0 < 1 - b := by linarith
    positivity
  obtain ⟨C, hC, hmain⟩ := BlockBand.Critical.Collar.dilation_trace_pow_exceptional_phases
    1 2 2 η₀ hη₀
  refine ⟨C, hC, fun W hW e he X hY d₁ hd₁ hdX => ?_⟩
  have he' : e ∈ bulkInterval κ' := ⟨by have := he.1; have := min_le_left κ 2; linarith,
    by have := he.2; have := min_le_left κ 2; linarith⟩
  have hzη : η₀ ≤ (boundaryZ b e).im :=
    BlockBand.Layers.boundaryZ_im_ge_of_mem_bulkInterval hb1.le hκ' he'
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set Xh := rePart X
  set Y := -Critical.imPart X
  set z := boundaryZ b e
  have hXh : Xh.IsHermitian := rePart_isHermitian X
  have hX : Xh - Complex.I • Y = X := rePart_sub_I_smul_neg_imPart X
  have hcard : (Fintype.card (Fin 2 × Fin W) : ℝ) ≤ 2 * (W : ℝ) := by simp
  have h := hmain (W : ℝ) hWr (Fin 2 × Fin W) hcard Xh Y z hXh hY hzη (blockProj W)
    (fun _ => 1) (fun j => norm_blockProj_le j) (fun _ => le_rfl) (d₁ / 2) (by positivity)
  have hg : BlockBand.Critical.Collar.dissipationWeight Xh Y z =
      Critical.conductance (Critical.oldScattering b e X) := by
    have hz : 0 < z.im := hη₀.trans_le hzη
    have hs : (((2 * z.im : ℝ)) : ℂ) * Complex.I = 2 * ((boundaryZ b e).im : ℂ) * Complex.I := by
      push_cast; ring
    rw [← BlockBand.Critical.Collar.re_trace_one_sub_conjTranspose_mul_scattering hXh hY hz,
      hX, hs]
    rfl
  rw [hg] at h
  refine (measure_mono fun t ht => ?_).trans h
  simp only [Set.mem_ofPred_eq] at ht ⊢
  by_contra hno
  push Not at hno
  apply absurd ht
  push Not
  have hR : BlockBand.Critical.Collar.absorbedResolvent Xh Y z = (z • 1 - X)⁻¹ := by
    rw [BlockBand.Critical.Collar.absorbedResolvent, ← hX]
    congr 1
    abel
  have hRt : BlockBand.Critical.Collar.dilationResolvent Xh Y z t =
      (z • 1 - (Xh + (t : ℂ) • Y))⁻¹ := by
    rw [BlockBand.Critical.Collar.dilationResolvent, sub_sub]
  have hj : ∀ j : Fin 2, ‖blockTrace (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      (Xh + (t : ℂ) • Y))⁻¹ j - blockTrace (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ j‖
        < d₁ / 2 := by
    intro j
    have := hno j
    simp only [pow_one] at this
    rw [hR, hRt, Complex.ofReal_natCast, inv_mul_trace_blockProj, blockTrace_sub] at this
    exact this
  have hd : ∀ j : Fin 2, ‖blockTrace (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ j -
      matchedA e‖ ≤ d₁ / 2 := by
    intro j
    refine le_trans ?_ hdX
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have key : ∀ j : Fin 2, ‖blockTrace (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      (Xh + (t : ℂ) • Y))⁻¹ j - matchedA e‖ ≤ d₁ := by
    intro j
    calc _ = ‖(blockTrace (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
            (Xh + (t : ℂ) • Y))⁻¹ j - blockTrace (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
              X)⁻¹ j) + (blockTrace (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ j -
                matchedA e)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ d₁ / 2 + d₁ / 2 := add_le_add (hj j).le (hd j)
      _ = d₁ := by ring
  exact max_le (key 0) (key 1)

end BlockBand.Critical.Collar.Kernel
