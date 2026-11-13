module

public import BlockBand.Transmission.Bridge.AlmostSure

/-!
# The one-step transport of the two-input path: abstract linear algebra

`transport_algebra`: let `(U, ℝ)` solve the two-lead system `F U + C ℝ = 0`, `Cᴴ U + z ℝ = 1` of
the old path, with `C = C_n ι + C_f` (near coupling `C_n` through the near-row selector `ι`,
far coupling `C_f` with no near column). If `N` fixes the far rows (`C_f N = C_f`) and the fresh
identity `hfresh` holds, then the candidate `U' = [ιℝN ; UN]`, `ℝ' = z⁻¹(1 - C'ᴴU')` solves the
two-lead system of the grown path `F' = [[a, C_nᴴ],[C_n, F]]`, `C' = [[B'ι],[C_f]]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix
open scoped Matrix

theorem transport_algebra {o p ν : Type*} [Fintype o] [Fintype p] [Fintype ν] [DecidableEq p]
    [DecidableEq ν]
    (F : Matrix o o ℂ) (Cn : Matrix o ν ℂ) (Cf U : Matrix o p ℂ) (Rr N : Matrix p p ℂ)
    (ι : Matrix ν p ℂ) (a B' : Matrix ν ν ℂ) {z : ℂ} (hz : z ≠ 0)
    (hU1 : F * U + (Cn * ι + Cf) * Rr = 0)
    (hU2 : (Cn * ι + Cf)ᴴ * U + z • Rr = 1)
    (hιCf : ι * Cfᴴ = 0) (hιι : ι * ιᴴ = 1) (hCfN : Cf * N = Cf)
    (hfresh : (a - z • 1) * (ι * Rr * N) - z⁻¹ • (B' * B'ᴴ * (ι * Rr * N)) + ι * N +
      z⁻¹ • (B' * ι) = 0) :
    a * (ι * Rr * N) + Cnᴴ * (U * N) +
        (B' * ι) * (z⁻¹ • (1 - (B' * ι)ᴴ * (ι * Rr * N) - Cfᴴ * (U * N))) = 0 ∧
      Cn * (ι * Rr * N) + F * (U * N) +
        Cf * (z⁻¹ • (1 - (B' * ι)ᴴ * (ι * Rr * N) - Cfᴴ * (U * N))) = 0 ∧
      (B' * ι)ᴴ * (ι * Rr * N) + Cfᴴ * (U * N) +
        z • (z⁻¹ • (1 - (B' * ι)ᴴ * (ι * Rr * N) - Cfᴴ * (U * N))) = 1 := by
  have hCfι : Cf * ιᴴ = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hιCf
  have hCfι' : ∀ {q : Type _} (M : Matrix ν q ℂ), Cf * (ιᴴ * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, hCfι, Matrix.zero_mul]
  have hιCf' : ∀ {q : Type _} (M : Matrix o q ℂ), ι * (Cfᴴ * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, hιCf, Matrix.zero_mul]
  have hιι' : ∀ {q : Type _} (M : Matrix ν q ℂ), ι * (ιᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hιι, Matrix.one_mul]
  have h2 : ιᴴ * (Cnᴴ * U) + Cfᴴ * U + z • Rr = 1 := by
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.add_mul,
      Matrix.mul_assoc] using hU2
  -- `C_nᴴ U = ι - z ιℝ`
  have h3 : Cnᴴ * (U * N) = ι * N - z • (ι * (Rr * N)) := by
    have := congrArg (ι * ·) h2
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at this
    rw [hιι', hιCf', add_zero] at this
    rw [← Matrix.mul_assoc, eq_sub_of_add_eq this, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_assoc]
  -- `C_f C_fᴴ U = C_f - z C_f ℝ`
  have h4 : Cf * (Cfᴴ * (U * N)) = Cf * N - z • (Cf * (Rr * N)) := by
    have := congrArg (Cf * ·) h2
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at this
    rw [hCfι', zero_add] at this
    rw [← Matrix.mul_assoc Cfᴴ, ← Matrix.mul_assoc, eq_sub_of_add_eq this,
      Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
  have h5 : F * (U * N) = -(Cn * (ι * Rr * N)) - Cf * (Rr * N) := by
    rw [← Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hU1]
    simp only [Matrix.neg_mul, Matrix.add_mul, Matrix.mul_assoc, neg_add, sub_eq_add_neg]
  have e1 : B' * ι * (z⁻¹ • (1 - (B' * ι)ᴴ * (ι * Rr * N) - Cfᴴ * (U * N))) =
      z⁻¹ • (B' * ι - B' * B'ᴴ * (ι * Rr * N)) := by
    rw [Matrix.mul_smul]
    congr 1
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.conjTranspose_mul]
    have ea : B' * ι * (ιᴴ * B'ᴴ * (ι * Rr * N)) = B' * B'ᴴ * (ι * Rr * N) := by
      rw [Matrix.mul_assoc B', Matrix.mul_assoc ιᴴ, hιι', ← Matrix.mul_assoc]
    have eb : B' * ι * (Cfᴴ * (U * N)) = 0 := by
      rw [Matrix.mul_assoc B', hιCf', Matrix.mul_zero]
    rw [ea, eb, sub_zero]
  have e2 : Cf * (z⁻¹ • (1 - (B' * ι)ᴴ * (ι * Rr * N) - Cfᴴ * (U * N))) =
      z⁻¹ • Cf - z⁻¹ • (Cf * N) + Cf * (Rr * N) := by
    rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.conjTranspose_mul,
      Matrix.mul_assoc ιᴴ, hCfι', h4, sub_zero, smul_sub, smul_sub, smul_smul,
      inv_mul_cancel₀ hz, one_smul]
    abel
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, h3, ← hfresh]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
    module
  · rw [e2, h5, hCfN]
    simp only [Matrix.mul_assoc]
    abel
  · rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
    abel

end BlockBand.Transmission.Bridge
