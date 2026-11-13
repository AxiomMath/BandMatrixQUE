module

public import BlockBand.SourceProcess.ClosingAux.Spectral
public import BlockBand.SourceProcess.Closing.Defs

/-!
# The closed omitted block is a strict contraction on its eigenvectors

Let `A` be an orthogonal projection, `Π` a partial isometry onto `A` (`ΠΠᴴ = A`), `𝕊` unitary,
and `N = Π𝕊A` (`closingN`, the block `r = S_AA`). Put `P = ΠᴴΠ` (the projection onto the
paired outputs `A_+`). If `N v = k v` with `‖k‖ ≥ 1`, then `v = Av` and
`‖v‖² ≤ ‖k v‖² = ‖Π𝕊v‖² = ‖𝕊v‖² - ‖(1-P)𝕊v‖² = ‖v‖² - ‖(1-P)𝕊v‖²`, so `P𝕊v = 𝕊v`: the input `v`
is scattered entirely into `A_+`. `eigen_closingN` assumes this forces `v = 0` (hypothesis
`hinj`; for the physical path it is the injectivity of the far-to-near transmission block,
`corner_injective`), and `tendsto_closingN_pow` concludes `N^n → 0` through
`tendsto_pow_of_eigen`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingAux

open Matrix Filter Topology BlockBand.SourceProcess.Closing
open scoped ComplexOrder ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem quad_mulVec (M : Matrix ι ι ℂ) (u : ι → ℂ) :
    star (M *ᵥ u) ⬝ᵥ (M *ᵥ u) = star u ⬝ᵥ ((Mᴴ * M) *ᵥ u) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem proj_mul_partialIso {A Pi : Matrix ι ι ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) : A * Pi = Pi := by
  have h0 : ((1 - A) * Pi) * ((1 - A) * Pi)ᴴ = 0 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPi, conjTranspose_sub,
      conjTranspose_one, hAH, Matrix.mul_sub, Matrix.mul_one, hA2, sub_self, Matrix.mul_zero]
  have h := self_mul_conjTranspose_eq_zero.1 h0
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h.symm

theorem re_eq_zero_of_nonneg {x : ℂ} (hx : 0 ≤ x) (hre : x.re ≤ 0) : x = 0 := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 hx
  exact Complex.ext (le_antisymm hre h1) h2.symm

/-- **No eigenvalue of modulus `≥ 1`** for `N = Π𝕊A`, given that an input of `A` scattered
entirely into `ran ΠᴴΠ` vanishes. -/
theorem eigen_closingN {S A Pi : Matrix ι ι ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1)
    (hinj : ∀ v : ι → ℂ, A *ᵥ v = v → (Piᴴ * Pi) *ᵥ (S *ᵥ v) = S *ᵥ v → v = 0)
    (k : ℂ) (v : ι → ℂ) (hv : closingN S A Pi *ᵥ v = k • v) (hk : 1 ≤ ‖k‖) : v = 0 := by
  have hSS : Sᴴ * S = 1 := mul_eq_one_comm.1 hS
  have hAPi := proj_mul_partialIso hA2 hAH hPi
  set P := Piᴴ * Pi with hPdef
  have hP2 : P * P = P := by
    rw [hPdef, Matrix.mul_assoc, ← Matrix.mul_assoc Pi Piᴴ Pi, hPi, hAPi]
  have hPH : Pᴴ = P := by rw [hPdef, conjTranspose_mul, conjTranspose_conjTranspose]
  have hk0 : k ≠ 0 := by rintro rfl; norm_num at hk
  have hvN : v = k⁻¹ • (closingN S A Pi *ᵥ v) := by
    rw [hv, smul_smul, inv_mul_cancel₀ hk0, one_smul]
  have hAN : A * closingN S A Pi = closingN S A Pi := by
    simp only [closingN, ← Matrix.mul_assoc, hAPi]
  have hAv : A *ᵥ v = v := by
    conv_lhs => rw [hvN]
    rw [mulVec_smul, mulVec_mulVec, hAN, ← hvN]
  have hNv : closingN S A Pi *ᵥ v = Pi *ᵥ (S *ᵥ v) := by
    rw [closingN, ← mulVec_mulVec, hAv, ← mulVec_mulVec]
  set w := S *ᵥ v with hw
  have e1 : star w ⬝ᵥ w = star v ⬝ᵥ v := by rw [hw, quad_mulVec, hSS, one_mulVec]
  have e3 : star ((1 - P) *ᵥ w) ⬝ᵥ ((1 - P) *ᵥ w) = star w ⬝ᵥ w - star w ⬝ᵥ (P *ᵥ w) := by
    have h1 : (1 - P)ᴴ * (1 - P) = 1 - P := by
      rw [conjTranspose_sub, conjTranspose_one, hPH, Matrix.sub_mul, Matrix.one_mul,
        Matrix.mul_sub, Matrix.mul_one, hP2, sub_self, sub_zero]
    rw [quad_mulVec, h1, sub_mulVec, one_mulVec, dotProduct_sub]
  have e4 : star w ⬝ᵥ (P *ᵥ w) = (star k * k) * (star v ⬝ᵥ v) := by
    rw [hPdef, ← quad_mulVec, ← hNv, hv, star_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    ring
  have hkk : star k * k = ((‖k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  have hx : star ((1 - P) *ᵥ w) ⬝ᵥ ((1 - P) *ᵥ w) =
      ((1 - ‖k‖ ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ v) := by
    rw [e3, e4, e1, hkk]; push_cast; ring
  have hre : (star ((1 - P) *ᵥ w) ⬝ᵥ ((1 - P) *ᵥ w)).re ≤ 0 := by
    rw [hx, Complex.re_ofReal_mul]
    have ha : 0 ≤ (star v ⬝ᵥ v).re := (Complex.nonneg_iff.1 (dotProduct_star_self_nonneg v)).1
    have hk2 : 1 ≤ ‖k‖ ^ 2 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) ha
  have h0 := dotProduct_star_self_eq_zero.1
    (re_eq_zero_of_nonneg (dotProduct_star_self_nonneg _) hre)
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at h0
  exact hinj v hAv h0.symm

/-- **`N^n → 0`** under the hypotheses of `eigen_closingN`. -/
theorem tendsto_closingN_pow {S A Pi : Matrix ι ι ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1)
    (hinj : ∀ v : ι → ℂ, A *ᵥ v = v → (Piᴴ * Pi) *ᵥ (S *ᵥ v) = S *ᵥ v → v = 0) :
    Tendsto (fun n : ℕ => closingN S A Pi ^ n) atTop (𝓝 0) :=
  tendsto_pow_of_eigen fun k v hv hk => eigen_closingN hA2 hAH hPi hS hinj k v hv hk

end BlockBand.SourceProcess.ClosingAux
