module

public import BlockBand.Coarea.Native.BlockBand.Coarea.SchurData

/-!
# Normalized Schur-graph reconstruction

The normalization step in the clock identity of the coarea theorem: once a normalized full
eigenvector is a positive square-root multiple of a Schur-graph vector, its retained mass is the
inverse of the Schur-clock quadratic form.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix
open scoped ComplexOrder

/-- A normalized reconstruction `ψ = √mass (v,-Tv)` has
`mass⁻¹ = vᴴ (I+TᴴT) v` (the clock reconstruction identity of the coarea theorem).
All quantities are finite-dimensional and exact; there is no limiting or
probabilistic hypothesis. -/
theorem schurClock_eq_inv_mass_of_normalized
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) (v : m → ℂ) (mass : ℝ) (hmass : 0 < mass)
    (hnormalized :
      star ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) ⬝ᵥ
          ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) = 1) :
    star v ⬝ᵥ (schurClock T *ᵥ v) = ((mass⁻¹ : ℝ) : ℂ) := by
  have hsqrt : (Real.sqrt mass : ℂ) * (Real.sqrt mass : ℂ) = (mass : ℂ) := by
    norm_cast
    simpa [pow_two] using Real.sq_sqrt hmass.le
  have hscale :
      star ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) ⬝ᵥ
          ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) =
        (mass : ℂ) *
          (star (v ⊕ᵥ (-(T *ᵥ v))) ⬝ᵥ (v ⊕ᵥ (-(T *ᵥ v)))) := by
    rw [StarModule.star_smul, dotProduct_smul, smul_dotProduct]
    have hstar : star (Real.sqrt mass : ℂ) = (Real.sqrt mass : ℂ) := by simp
    rw [hstar]
    simp only [smul_eq_mul]
    rw [← mul_assoc, hsqrt]
  rw [hscale, dotProduct_schurReconstruction_eq_schurClock] at hnormalized
  have hm0 : (mass : ℂ) ≠ 0 := by exact_mod_cast hmass.ne'
  apply (mul_left_cancel₀ hm0)
  rw [hnormalized]
  norm_num [hmass.ne']

end CoareaNative.BlockBand
