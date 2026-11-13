module

public import BlockBand.Critical.Collar.Density.ShiftBound

/-!
# The conditional collar density `T Σ_F(0) T*` and its pointwise bounds 

Deterministic; no measure. Common-port layer sample `ω = (A, B)`, every `W`, real `b`, `e`, and
deterministic `X`.

* `portEquiv W : Fin 1 × Fin W ≃ Fin W`; `collarFW`, `collarTW`: `F`, `T` with the port index
  reindexed to `Fin W` (the index of `WeightedDensity.sigma`).
* `condCollarDensity b e X ω = T Σ_F(0) T*`, `Σ_F = WeightedDensity.sigma F (1-2b)` (the canonical
  expected matrix spectral density of `F + G`, `G ~ GUE_W((1-2b)/W)`, the middle block's law).
* `quadForm_condCollarDensity_le`: if `(F + i)Σ_F(0)(F - i) ⪯ C I` (both
  clauses of the global weighted-density bound have this form at `η = 1`) and `|w| ≤ 1`, then
  `q*K T Σ_F(0) T*K*q ≤ 2C‖L*q‖²`, `L = commonPortL` (that is, `K_XTΣ_F(0)T*K_X* ⪯ 2C LL*`).
  When `D` is singular Lean's `D⁻¹ = 0` gives `T = 0` and the bound is trivial.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ComplexOrder

variable {W : ℕ}

/-- The port index `Fin 1 × Fin W ≃ Fin W`. -/
def portEquiv (W : ℕ) : Fin 1 × Fin W ≃ Fin W := Equiv.uniqueProd (Fin W) (Fin 1)

/-- `F` on `Fin W`. -/
def collarFW (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : LayerSample W .common) :
    Matrix (Fin W) (Fin W) ℂ :=
  (collarF e X ω).submatrix (portEquiv W).symm (portEquiv W).symm

/-- `T` with columns indexed by `Fin W`. -/
def collarTW (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : LayerSample W .common) :
    Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  (collarT e X ω).submatrix id (portEquiv W).symm

/-- **The conditional top density at zero**, `T Σ_F(0) T*`. -/
def condCollarDensity (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  collarTW e X ω * sigma (collarFW e X ω) (1 - 2 * b) 0 * (collarTW e X ω)ᴴ

theorem collarFW_isHermitian (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ω : LayerSample W .common} (hA : ∀ k, (ω.1 k).IsHermitian) :
    (collarFW e X ω).IsHermitian :=
  (collarF_isHermitian e hX hA).submatrix _

theorem collarFW_sub_eq (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) :
    collarFW e X ω - collarShiftW b e • (1 : Matrix (Fin W) (Fin W) ℂ) =
      (collarF e X ω - collarShiftW b e • 1).submatrix (portEquiv W).symm (portEquiv W).symm := by
  ext i j
  simp only [collarFW, submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    EmbeddingLike.apply_eq_iff_eq]

theorem isUnit_det_collarFW_sub {b e : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ω : LayerSample W .common} (hA : ∀ k, (ω.1 k).IsHermitian)
    (hw : (collarShiftW b e).im < 0) :
    IsUnit (collarFW e X ω - collarShiftW b e • 1).det := by
  rw [collarFW_sub_eq, det_submatrix_equiv_self]
  exact isUnit_det_collarF_sub hX hA hw

/-- `K T_W (F_W - w)⁻¹ = L` with the port index reindexed. -/
theorem commonPortL_submatrix_eq (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) (hD : IsUnit (collarTopBlock e X ω).det)
    (hS : IsUnit (collarF e X ω - collarShiftW b e • 1).det) :
    matchedLeadK b e X * collarTW e X ω * (collarFW e X ω - collarShiftW b e • 1)⁻¹ =
      (commonPortL b e X ω).submatrix id (portEquiv W).symm := by
  rw [commonPortL_eq_mul b e X ω hD hS, collarFW_sub_eq, inv_submatrix_equiv, collarTW,
    Matrix.mul_assoc, submatrix_mul_equiv, Matrix.mul_assoc]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]

theorem sum_norm_sq_conjTranspose_submatrix (M : Matrix (Fin 2 × Fin W) (Fin 1 × Fin W) ℂ)
    (q : Fin 2 × Fin W → ℂ) :
    ∑ a, ‖((M.submatrix id (portEquiv W).symm)ᴴ *ᵥ q) a‖ ^ 2 = ∑ a, ‖(Mᴴ *ᵥ q) a‖ ^ 2 := by
  have h : ∀ a, ((M.submatrix id (portEquiv W).symm)ᴴ *ᵥ q) a = (Mᴴ *ᵥ q) ((portEquiv W).symm a) :=
    fun a => rfl
  simp_rw [h]
  exact Equiv.sum_comp (portEquiv W).symm (fun x => ‖(Mᴴ *ᵥ q) x‖ ^ 2)

/-- **Pointwise conditional bound**: if `(F + i)Σ_F(0)(F - i) ⪯ C I`
(with `C ≥ 0`), `A` and `X` are Hermitian and `w = -z₀ - e` has `Im w < 0`, `|w| ≤ 1`, then
`q*K_X T Σ_F(0) T* K_X*q ≤ 2C ‖L*q‖²`, `L = commonPortL b e X ω`. -/
theorem quadForm_condCollarDensity_le {b e : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ω : LayerSample W .common} (hA : ∀ k, (ω.1 k).IsHermitian)
    (hw : (collarShiftW b e).im < 0) (hw1 : ‖collarShiftW b e‖ ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hS : (((C : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) -
      (collarFW e X ω - ((0 : ℂ) - (1 : ℂ) * Complex.I) • 1) *
        sigma (collarFW e X ω) (1 - 2 * b) 0 *
        (collarFW e X ω - ((0 : ℂ) + (1 : ℂ) * Complex.I) • 1)).PosSemidef)
    (q : Fin 2 × Fin W → ℂ) :
    quadForm (matchedLeadK b e X * condCollarDensity b e X ω * (matchedLeadK b e X)ᴴ) q ≤
      2 * C * ∑ a, ‖((commonPortL b e X ω)ᴴ *ᵥ q) a‖ ^ 2 := by
  by_cases hD : IsUnit (collarTopBlock e X ω).det
  · have hSu := isUnit_det_collarF_sub (b := b) hX hA hw
    have hm : max 1 (‖collarShiftW b e‖ ^ 2) = 1 :=
      max_eq_left (pow_le_one₀ (norm_nonneg _) hw1)
    have h := quadForm_sandwich_le (collarFW_isHermitian e hX hA) hC hS
      (isUnit_det_collarFW_sub hX hA hw) (matchedLeadK b e X) (collarTW e X ω) q
    rw [hm, commonPortL_submatrix_eq b e X ω hD hSu, sum_norm_sq_conjTranspose_submatrix] at h
    have heq : matchedLeadK b e X * condCollarDensity b e X ω * (matchedLeadK b e X)ᴴ =
        matchedLeadK b e X * collarTW e X ω * sigma (collarFW e X ω) (1 - 2 * b) 0 *
          (collarTW e X ω)ᴴ * (matchedLeadK b e X)ᴴ := by
      simp only [condCollarDensity, Matrix.mul_assoc]
    rw [heq]
    linarith
  · have hT : collarTW e X ω = 0 := by
      have : (collarTopBlock e X ω)⁻¹ = 0 := nonsing_inv_apply_not_isUnit _ hD
      ext i j
      simp [collarTW, collarT, this]
    have h0 : 0 ≤ ∑ a, ‖((commonPortL b e X ω)ᴴ *ᵥ q) a‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [condCollarDensity, hT, Matrix.zero_mul, Matrix.mul_zero, quadForm, zero_mulVec,
      dotProduct_zero, Complex.zero_re]
    positivity

end BlockBand.Critical.Collar.Density
