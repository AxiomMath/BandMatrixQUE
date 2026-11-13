module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanInv

/-!
# The retained closed scatterer has no eigenvalue `1` (deterministic)

* **`isUnit_one_sub_retained`**: for a unitary `𝕊` with `1 - 𝕊` invertible and orthogonal
  projections `A`, `O`, the matrix `1 - (1 - O)𝕊(1 - A)` is invertible. Proof: if
  `(1 - O)𝕊(1 - A)u = u`, then `‖u‖² = ‖(1 - A)u‖² - ‖O𝕊(1 - A)u‖²`, so `Au = 0` and
  `O𝕊u = 0`, hence `𝕊u = u` and `u = 0`.
* `ae_isUnit_corner_affine`: the corner lemma `ae_isUnit_corner` with an affine constant term:
  `R₀ + zR₁ + zL(1 - zN)⁻¹T` is invertible at a.e. phase when `R₀` is.

These give the a.s. invertibility of `1 - 𝕊_pad(z)` for the **phase-padded** scatterer
`(1 - O)𝕊C(z)(1 - A) + zΠᴴA` (padding phase `z` instead of `1`), whose value at `z = 0` is
`1 - (1 - O)𝕊(1 - A)`. For `b3PadScatter` (padding phase `1`) the constant term is
`padZero = 1 - (1 - O)𝕊(1 - A) - ΠᴴA` and `B3PadZeroDet` stays open.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3LayerMean

open Matrix MeasureTheory
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.PhysApprox.ClosedForm
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem qf_mulVec (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    star (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = star x ⬝ᵥ ((Mᴴ * M) *ᵥ x) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

/-- **The retained closed scatterer has no eigenvalue `1`.** -/
theorem isUnit_one_sub_retained {S A O : Matrix ι ι ℂ} (hS : Sᴴ * S = 1) (hAH : Aᴴ = A)
    (hAA : A * A = A) (hOH : Oᴴ = O) (hOO : O * O = O) (h1S : IsUnit (1 - S)) :
    IsUnit (1 - (1 - O) * S * (1 - A)) := by
  set K := (1 - O) * S * (1 - A) with hKdef
  set B := O * S * (1 - A) with hBdef
  have hKK : Kᴴ * K = (1 - A) - Bᴴ * B := by
    have e1 : Kᴴ * K = (1 - A) * (Sᴴ * ((1 - O) * (1 - O)) * S) * (1 - A) := by
      simp only [hKdef, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hAH, hOH,
        Matrix.mul_assoc]
    have e2 : Sᴴ * ((1 - O) * (1 - O)) * S = 1 - (O * S)ᴴ * (O * S) := by
      rw [compl_mul_self' hOO, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hS,
        conjTranspose_mul, hOH]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc O O, hOO]
    have hB2 : Bᴴ * B = (1 - A) * ((O * S)ᴴ * (O * S)) * (1 - A) := by
      rw [hBdef, conjTranspose_mul (O * S) (1 - A), conjTranspose_sub, conjTranspose_one, hAH]
      simp only [Matrix.mul_assoc]
    rw [e1, e2, hB2, Matrix.mul_sub (1 - A) 1, Matrix.mul_one, Matrix.sub_mul,
      compl_mul_self' hAA]
  have hinj : ∀ u : ι → ℂ, (1 - K) *ᵥ u = 0 → u = 0 := by
    intro u hu
    have hKu : K *ᵥ u = u := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hu
      exact hu.symm
    have h1 : star u ⬝ᵥ u = star u ⬝ᵥ ((Kᴴ * K) *ᵥ u) := by rw [← qf_mulVec, hKu]
    have hA' : star u ⬝ᵥ (A *ᵥ u) = star (A *ᵥ u) ⬝ᵥ (A *ᵥ u) := by
      rw [qf_mulVec, hAH, hAA]
    rw [hKK, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_sub, hA', ← qf_mulVec] at h1
    have hsum : star (A *ᵥ u) ⬝ᵥ (A *ᵥ u) + star (B *ᵥ u) ⬝ᵥ (B *ᵥ u) = 0 := by
      linear_combination h1
    obtain ⟨hqa, hqb⟩ := (add_eq_zero_iff_of_nonneg (dotProduct_star_self_nonneg _)
      (dotProduct_star_self_nonneg _)).1 hsum
    have hAu : A *ᵥ u = 0 := dotProduct_star_self_eq_zero.1 hqa
    have hBu : B *ᵥ u = 0 := dotProduct_star_self_eq_zero.1 hqb
    have hcu : (1 - A) *ᵥ u = u := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hAu, sub_zero]
    have hBu' : B *ᵥ u = (O * S) *ᵥ u := by rw [hBdef, ← mulVec_mulVec, hcu]
    have hOSu : (O * S) *ᵥ u = 0 := by rw [← hBu', hBu]
    have hSu : S *ᵥ u = u := by
      have : K *ᵥ u = S *ᵥ u - (O * S) *ᵥ u := by
        rw [hKdef, ← mulVec_mulVec, hcu, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec]
      rw [hOSu, sub_zero, hKu] at this
      exact this.symm
    have h0 : (1 - S) *ᵥ u = 0 := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hSu, sub_self]
    have hinjS := (Matrix.mulVec_injective_iff_isUnit (A := 1 - S)).2 h1S
    exact hinjS (by rw [h0, Matrix.mulVec_zero])
  refine (Matrix.mulVec_injective_iff_isUnit (A := 1 - K)).1 fun u w huw => ?_
  have := hinj (u - w) (by rw [Matrix.mulVec_sub, huw, sub_self])
  exact sub_eq_zero.1 this

/-- **The affine closed corner** `R₀ + zR₁ + zL(1 - zN)⁻¹T` is invertible at a.e. phase when
`R₀` is. -/
theorem ae_isUnit_corner_affine {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p]
    [DecidableEq p] (R₀ R₁ : Matrix m m ℂ) (L : Matrix m p ℂ) (N : Matrix p p ℂ)
    (Rt : Matrix p m ℂ) (h₀ : IsUnit R₀.det) :
    ∀ᵐ θ ∂phaseLaw,
      IsUnit (R₀ + phase θ • R₁ + phase θ • (L * (1 - phase θ • N)⁻¹ * Rt)).det := by
  have hM₀ : IsUnit (fromBlocks (1 : Matrix p p ℂ) Rt 0 R₀).det := by
    rw [det_fromBlocks_zero₂₁, det_one, one_mul]; exact h₀
  filter_upwards [ae_isUnit_det_affine _ (fromBlocks (-N) 0 (-L) R₁) hM₀,
    (ae_isUnit_one_sub_smul 1 N)] with θ hθ hN
  rw [mul_one] at hN
  set z := phase θ
  have e : fromBlocks (1 : Matrix p p ℂ) Rt 0 R₀ + z • fromBlocks (-N) 0 (-L) R₁ =
      fromBlocks (1 - z • N) Rt (-(z • L)) (R₀ + z • R₁) := by
    rw [fromBlocks_smul, fromBlocks_add]
    simp only [smul_neg, smul_zero, add_zero, zero_add, sub_eq_add_neg]
  rw [e] at hθ
  let : Invertible (1 - z • N) := (isUnit_iff_isUnit_det _ |>.mpr hN).invertible
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv] at hθ
  have h2 := isUnit_of_mul_isUnit_right hθ
  convert h2 using 2
  simp only [Matrix.neg_mul, Matrix.smul_mul, sub_neg_eq_add, add_assoc]

end BlockBand.SourceProcess.PhysApprox.B3LayerMean
