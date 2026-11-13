module

public import BlockBand.SourceProcess.ClosedPath.Iterate

/-!
# Algebra of the closed current

Pure matrix algebra on a finite index type `ι`, with `P` an orthogonal projection (near inputs),
`A` an orthogonal projection (omitted inputs), `AΠ = Π`, and the closing map
`C(z) = (1 - A) + (1 - zN)⁻¹ zT` (`Closing.closingMap`):

* `current_step`: one near-end growth step conserves the current. If `𝕊₀, 𝕊₁` are unitary, the
  transport `N` keeps the far input (`(1-P)N = 1-P`) and the far output
  (`(1-P)𝕊₀N = (1-P)𝕊₁`), then `Nᴴ(𝕊₀ᴴP𝕊₀ - P)N = 𝕊₁ᴴP𝕊₁ - P`.
* `current_iterate`: the iterate along `stepProd`.
* `closed_omitted_current`: for `|z| = 1` and `1 - zN` invertible,
  `C(z)ᴴ (A - (Π𝕊)ᴴ(Π𝕊)) C(z) = 0` (closed omitted channels carry no current).
* `closingMap_conj_near`: if `PA = 0` and `PΠ = 0` then `C(z)ᴴ P C(z) = P`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3Cur

open Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **One growth step conserves the current**: `Nᴴ(𝕊₀ᴴP𝕊₀ - P)N = 𝕊₁ᴴP𝕊₁ - P`. -/
theorem current_step {P N S₀ S₁ : Matrix ι ι ℂ} (hPH : Pᴴ = P) (hPP : P * P = P)
    (hS₀ : S₀ᴴ * S₀ = 1) (hS₁ : S₁ᴴ * S₁ = 1) (hPN : (1 - P) * N = 1 - P)
    (hS : (1 - P) * S₀ * N = (1 - P) * S₁) :
    Nᴴ * (S₀ᴴ * P * S₀ - P) * N = S₁ᴴ * P * S₁ - P := by
  set Q : Matrix ι ι ℂ := 1 - P
  have hQH : Qᴴ = Q := by simp only [Q, conjTranspose_sub, conjTranspose_one, hPH]
  have hQQ : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]; abel
  have split : ∀ S : Matrix ι ι ℂ, Sᴴ * S = 1 → Sᴴ * P * S - P = Q - Sᴴ * Q * S := by
    intro S hS'
    simp only [Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hS']; abel
  have hQQ' : ∀ X : Matrix ι ι ℂ, Q * (Q * X) = Q * X := fun X => by
    rw [← Matrix.mul_assoc, hQQ]
  have hNQN : Nᴴ * Q * N = Q := by
    calc Nᴴ * Q * N = (Q * N)ᴴ * (Q * N) := by
          simp only [conjTranspose_mul, hQH, Matrix.mul_assoc, hQQ']
      _ = Q := by rw [hPN, hQH, hQQ]
  have hNSN : Nᴴ * (S₀ᴴ * Q * S₀) * N = S₁ᴴ * Q * S₁ := by
    calc Nᴴ * (S₀ᴴ * Q * S₀) * N = (Q * S₀ * N)ᴴ * (Q * S₀ * N) := by
          simp only [conjTranspose_mul, hQH, Matrix.mul_assoc, hQQ']
      _ = (Q * S₁)ᴴ * (Q * S₁) := by rw [hS]
      _ = S₁ᴴ * Q * S₁ := by simp only [conjTranspose_mul, hQH, Matrix.mul_assoc, hQQ']
  rw [split S₀ hS₀, split S₁ hS₁, Matrix.mul_sub, Matrix.sub_mul, hNQN, hNSN]

/-- **The current along the transport product**: one-step conservation iterates to
`(N_{j₀}⋯N_{j₀+m-1})ᴴ J_{j₀} (N_{j₀}⋯N_{j₀+m-1}) = J_{j₀+m}`. -/
theorem current_iterate (J N : ℕ → Matrix ι ι ℂ) (j₀ m : ℕ)
    (h : ∀ i, i < m → (N (j₀ + i))ᴴ * J (j₀ + i) * N (j₀ + i) = J (j₀ + i + 1)) :
    (stepProd N j₀ m)ᴴ * J j₀ * stepProd N j₀ m = J (j₀ + m) := by
  induction m with
  | zero => simp [stepProd]
  | succ m ih =>
    have ih' := ih fun i hi => h i (by omega)
    simp only [stepProd, conjTranspose_mul]
    calc (N (j₀ + m))ᴴ * (stepProd N j₀ m)ᴴ * J j₀ * (stepProd N j₀ m * N (j₀ + m)) =
        (N (j₀ + m))ᴴ * ((stepProd N j₀ m)ᴴ * J j₀ * stepProd N j₀ m) * N (j₀ + m) := by
          simp only [Matrix.mul_assoc]
      _ = J (j₀ + (m + 1)) := by rw [ih', h m (by omega), add_assoc]

variable {S A Pi : Matrix ι ι ℂ} {z : ℂ}

/-- **Closed omitted channels carry no current**: for `|z| = 1`,
`C(z)ᴴ (A - (Π𝕊)ᴴ(Π𝕊)) C(z) = 0`. -/
theorem closed_omitted_current (hAH : Aᴴ = A) (hAA : A * A = A) (hAPi : A * Pi = Pi)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (hz : ‖z‖ = 1) :
    (closingMap S A Pi z)ᴴ * (A - (Pi * S)ᴴ * (Pi * S)) * closingMap S A Pi z = 0 := by
  set C := closingMap S A Pi z
  have hF := closingMap_feedback hAA hAPi hU
  have hzz : star z * z = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hz]; simp
  have hAA' : ∀ X : Matrix ι ι ℂ, A * (A * X) = A * X := fun X => by
    rw [← Matrix.mul_assoc, hAA]
  have hA : Cᴴ * A * C = (A * C)ᴴ * (A * C) := by
    simp only [conjTranspose_mul, hAH, Matrix.mul_assoc, hAA']
  have hPi : Cᴴ * ((Pi * S)ᴴ * (Pi * S)) * C = (Pi * S * C)ᴴ * (Pi * S * C) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, hA, hPi, hF, conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hzz, one_smul, sub_self]

/-- **Closing does not change the near projection**: `PA = 0`, `PΠ = 0` give
`C(z)ᴴ P C(z) = P`. -/
theorem closingMap_conj_near {P : Matrix ι ι ℂ} (hPH : Pᴴ = P) (hPP : P * P = P)
    (hPA : P * A = 0) (hPPi : P * Pi = 0) :
    (closingMap S A Pi z)ᴴ * P * closingMap S A Pi z = P := by
  set M := 1 - z • closingN S A Pi
  have hPM : P * M = P := by
    simp only [M, closingN, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      hPPi, Matrix.zero_mul, smul_zero, sub_zero]
  have hPT : P * (z • closingT S A Pi) = 0 := by
    simp only [closingT, Matrix.mul_smul, ← Matrix.mul_assoc, hPPi, Matrix.zero_mul, smul_zero]
  have hPX : P * (M⁻¹ * (z • closingT S A Pi)) = 0 := by
    by_cases hU : IsUnit M.det
    · have : P * M⁻¹ = P := by
        calc P * M⁻¹ = P * M * M⁻¹ := by rw [hPM]
          _ = P := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hU, Matrix.mul_one]
      rw [← Matrix.mul_assoc, this, hPT]
    · rw [nonsing_inv_apply_not_isUnit _ hU, Matrix.zero_mul, Matrix.mul_zero]
  have hPC : P * closingMap S A Pi z = P := by
    rw [closingMap, Matrix.mul_add, hPX, add_zero, Matrix.mul_sub, Matrix.mul_one, hPA, sub_zero]
  calc (closingMap S A Pi z)ᴴ * P * closingMap S A Pi z =
      (P * closingMap S A Pi z)ᴴ * (P * closingMap S A Pi z) := by
        have hPP' : ∀ X : Matrix ι ι ℂ, P * (P * X) = P * X := fun X => by
          rw [← Matrix.mul_assoc, hPP]
        simp only [conjTranspose_mul, hPH, Matrix.mul_assoc, hPP']
    _ = P := by rw [hPC, hPH, hPP]

end BlockBand.SourceProcess.PhysApprox.B3Cur
