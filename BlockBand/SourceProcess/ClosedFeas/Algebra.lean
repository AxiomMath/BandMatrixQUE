module

public import BlockBand.SourceProcess.ClosedPath.Commute
public import BlockBand.SourceProcess.Stochastic.FiniteSource

/-!
# The closed projection identity

This file is pure linear algebra on a generic finite ambient space `ι`. `𝕊` unitary, `P` a
Hermitian projection (near port), `A` a Hermitian projection with `PA = 0` (omitted far inputs),
`Π` with `AΠ = Π`, `ΠΠᴴ = A`, `ΠP = 0` (pairing of the omitted far outputs `B = ΠᴴΠ` with `A`),
`|z| = 1` and `1 - zN` invertible. `C = C(z)` is the closing map `closingMap`.

* `splitCurrent 𝕊 P A Π = 𝕊ᴴ(P + ΠᴴΠ)𝕊 - (P + A)`: the current of the retained modes
  (`J - J_A`, `J_A = A - 𝕊ᴴB𝕊`).
* **`gramProjection_closed`**: if `X𝖣Xᴴ = splitCurrent`, then `P + (CᴴX)𝖣(CᴴX)ᴴ = Cᴴ𝕊ᴴP𝕊C`.
  Uses `CᴴPC = P` and, from the closing equations `AC = zΠ𝕊C` and `|z| = 1`, `CᴴAC = Cᴴ𝕊ᴴB𝕊C`.
* **`closedOutProj`**: `Cᴴ𝕊ᴴP𝕊C` is a Hermitian projection with the trace of `P`. With
  `U = (1-B)𝕊C`: `UᴴU = 1 - A`, hence `UUᴴ` is a projection below `1 - B` with the same trace,
  so `UUᴴ = 1 - B`, and `Cᴴ𝕊ᴴP𝕊C = UᴴPU`.
* **`twoProjection_closed`**: hence `TwoProjection P 𝖣 (CᴴX)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedFeas

open Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.Stochastic
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S P A Pi : Matrix ι ι ℂ} {z : ℂ}

/-- The current of the retained modes: `𝕊ᴴ(P + ΠᴴΠ)𝕊 - (P + A)`. -/
def splitCurrent (S P A Pi : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Sᴴ * (P + Piᴴ * Pi) * S - (P + A)

theorem one_sub_conj_mul_self {X : Matrix ι ι ℂ} (hH : Xᴴ = X) (hXX : X * X = X) :
    (1 - X)ᴴ * (1 - X) = 1 - X := by
  rw [conjTranspose_sub, conjTranspose_one, hH, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    hXX]; simp

theorem closingMap_mul_A (hAA : A * A = A) : closingMap S A Pi z * A = 0 := by
  have h : (1 - A) * A = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hAA, sub_self]
  simp only [closingMap, closingT, Matrix.add_mul, Matrix.mul_assoc, Matrix.smul_mul, h,
    Matrix.mul_zero, smul_zero, add_zero]

theorem P_mul_closingMap (hAA : A * A = A) (hAPi : A * Pi = Pi) (hPA : P * A = 0) :
    P * closingMap S A Pi z = P := by
  have hP : P * (1 - A) = P := by rw [Matrix.mul_sub, Matrix.mul_one, hPA, sub_zero]
  calc P * closingMap S A Pi z = P * ((1 - A) * closingMap S A Pi z) := by
        rw [← Matrix.mul_assoc, hP]
    _ = P := by rw [compl_mul_closingMap hAA hAPi, hP]

/-- **The omitted inputs carry exactly the fed-back omitted outputs** (`|z| = 1`). -/
theorem conj_A_closingMap (hAH : Aᴴ = A) (hAA : A * A = A) (hAPi : A * Pi = Pi)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (hz : star z * z = 1) :
    (closingMap S A Pi z)ᴴ * A * closingMap S A Pi z =
      (closingMap S A Pi z)ᴴ * Sᴴ * (Piᴴ * Pi) * S * closingMap S A Pi z := by
  set C := closingMap S A Pi z
  calc Cᴴ * A * C = (A * C)ᴴ * (A * C) := by
        rw [conjTranspose_mul, hAH, ← Matrix.mul_assoc, Matrix.mul_assoc Cᴴ A A, hAA]
    _ = (star z * z) • ((Pi * S * C)ᴴ * (Pi * S * C)) := by
        rw [closingMap_feedback hAA hAPi hU, conjTranspose_smul, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul]
    _ = _ := by rw [hz, one_smul]; simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- **The closed projection identity**: closing turns the retained current into a current. -/
theorem gramProjection_closed {κ : Type*} [Fintype κ] (hPH : Pᴴ = P) (hPA : P * A = 0)
    (hAH : Aᴴ = A) (hAA : A * A = A) (hAPi : A * Pi = Pi)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (hz : star z * z = 1) {D : Matrix κ κ ℂ}
    {X : Matrix ι κ ℂ} (hX : X * D * Xᴴ = splitCurrent S P A Pi) :
    gramProjection P ((closingMap S A Pi z)ᴴ * X) D =
      (closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z := by
  set C := closingMap S A Pi z
  have hPC : P * C = P := P_mul_closingMap hAA hAPi hPA
  have hCPC : Cᴴ * P * C = P := by
    rw [Matrix.mul_assoc, hPC, ← hPH, ← conjTranspose_mul, hPH, hPC, hPH]
  have hCAC := conj_A_closingMap hAH hAA hAPi hU hz
  have e1 : (Cᴴ * X) * D * (Cᴴ * X)ᴴ = Cᴴ * (X * D * Xᴴ) * C := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have e2 : Cᴴ * splitCurrent S P A Pi * C = Cᴴ * Sᴴ * P * S * C +
      Cᴴ * Sᴴ * (Piᴴ * Pi) * S * C - Cᴴ * P * C - Cᴴ * A * C := by
    simp only [splitCurrent, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
    abel
  rw [gramProjection, e1, hX, e2, hCPC, hCAC]
  abel

theorem one_sub_mul_self {X : Matrix ι ι ℂ} (hXX : X * X = X) : (1 - X) * (1 - X) = 1 - X := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hXX]; simp

/-- `UᴴPU` is a projection of the rank of `P` when `UUᴴ = 1 - B` and `P(1 - B) = P`. -/
theorem proj_of_coisometry {U B : Matrix ι ι ℂ} (hPH : Pᴴ = P) (hPP : P * P = P)
    (hY : U * Uᴴ = 1 - B) (hP1B : P * (1 - B) = P) :
    (Uᴴ * P * U)ᴴ = Uᴴ * P * U ∧ Uᴴ * P * U * (Uᴴ * P * U) = Uᴴ * P * U ∧
      (Uᴴ * P * U).trace = P.trace := by
  refine ⟨?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPH,
      Matrix.mul_assoc]
  · calc Uᴴ * P * U * (Uᴴ * P * U) = Uᴴ * (P * (U * Uᴴ) * P) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * P * U := by rw [hY, hP1B, hPP, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hY, hP1B]

/-- **The closed output projection `Cᴴ𝕊ᴴP𝕊C` is a projection of the rank of `P`.** -/
theorem closedOutProj (hS : Sᴴ * S = 1) (hPH : Pᴴ = P) (hPP : P * P = P)
    (hPiP : Pi * P = 0) (hAH : Aᴴ = A) (hAA : A * A = A) (hAPi : A * Pi = Pi)
    (hPiPi : Pi * Piᴴ = A) (hU : IsUnit (1 - z • closingN S A Pi).det) (hz : star z * z = 1) :
    ((closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z)ᴴ =
        (closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z ∧
      (closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z *
          ((closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z) =
        (closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z ∧
      ((closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z).trace = P.trace := by
  set C := closingMap S A Pi z
  set B := Piᴴ * Pi with hBdef
  have hBH : Bᴴ = B := by rw [hBdef, conjTranspose_mul, conjTranspose_conjTranspose]
  have hPiA : Piᴴ * A = Piᴴ := by rw [← hAH, ← conjTranspose_mul, hAPi]
  have hBB : B * B = B := by
    calc B * B = Piᴴ * (Pi * Piᴴ) * Pi := by simp only [hBdef, Matrix.mul_assoc]
      _ = B := by rw [hPiPi, hPiA]
  have hPB : P * B = 0 := by
    have h : B * P = 0 := by rw [hBdef, Matrix.mul_assoc, hPiP, Matrix.mul_zero]
    have := congrArg conjTranspose h
    rwa [conjTranspose_mul, hBH, hPH, conjTranspose_zero] at this
  have htrB : B.trace = A.trace := by rw [hBdef, ← hPiPi, Matrix.trace_mul_comm]
  have hCA : C * A = 0 := closingMap_mul_A hAA
  have hcC : (1 - A) * C = 1 - A := compl_mul_closingMap hAA hAPi
  have hCAC : Cᴴ * A * C = Cᴴ * Sᴴ * B * S * C := conj_A_closingMap hAH hAA hAPi hU hz
  have h1A := one_sub_conj_mul_self hAH hAA
  have h1B := one_sub_conj_mul_self hBH hBB
  have h1B' : (1 - B)ᴴ = 1 - B := by rw [conjTranspose_sub, conjTranspose_one, hBH]
  set U := (1 - B) * S * C with hUdef
  have hUU : Uᴴ * U = 1 - A := by
    calc Uᴴ * U = Cᴴ * (Sᴴ * ((1 - B)ᴴ * (1 - B)) * S) * C := by
          simp only [hUdef, conjTranspose_mul, Matrix.mul_assoc]
      _ = Cᴴ * (Sᴴ * S) * C - Cᴴ * Sᴴ * B * S * C := by
          rw [h1B]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = Cᴴ * ((1 - A)ᴴ * (1 - A)) * C := by
          rw [hS, Matrix.mul_one, ← hCAC, h1A]
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      _ = ((1 - A) * C)ᴴ * ((1 - A) * C) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 - A := by rw [hcC, h1A]
  have h2 : (1 - B) * (1 - B) = 1 - B := one_sub_mul_self hBB
  have hU1 : U * (1 - A) = U := by
    rw [Matrix.mul_sub, Matrix.mul_one, hUdef, Matrix.mul_assoc ((1 - B) * S) C A, hCA,
      Matrix.mul_zero, sub_zero]
  have hBU : (1 - B) * U = U := by
    rw [hUdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
  have hUB : Uᴴ * (1 - B) = Uᴴ := by
    have := congrArg conjTranspose hBU
    rwa [conjTranspose_mul, h1B'] at this
  have hP1B : P * (1 - B) = P := by rw [Matrix.mul_sub, Matrix.mul_one, hPB, sub_zero]
  have hPU : P * U = P * S * C := by
    rw [hUdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1B]
  have hR : Cᴴ * Sᴴ * P * S * C = Uᴴ * P * U := by
    calc Cᴴ * Sᴴ * P * S * C = (P * S * C)ᴴ * (P * S * C) := by
          rw [conjTranspose_mul, conjTranspose_mul, hPH]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc P P, hPP]
      _ = (P * U)ᴴ * (P * U) := by rw [hPU]
      _ = Uᴴ * P * U := by
          rw [conjTranspose_mul, hPH, ← Matrix.mul_assoc, Matrix.mul_assoc Uᴴ P P, hPP]
  clear_value U
  have hYY : U * Uᴴ * (U * Uᴴ) = U * Uᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hUU, ← Matrix.mul_assoc, hU1]
  have hY : U * Uᴴ = 1 - B := by
    have hEH : ((1 - B) - U * Uᴴ)ᴴ = (1 - B) - U * Uᴴ := by
      rw [conjTranspose_sub, h1B', conjTranspose_mul, conjTranspose_conjTranspose]
    have hEE : ((1 - B) - U * Uᴴ) * ((1 - B) - U * Uᴴ) = (1 - B) - U * Uᴴ := by
      have h3 : (1 - B) * (U * Uᴴ) = U * Uᴴ := by rw [← Matrix.mul_assoc, hBU]
      have h4 : U * Uᴴ * (1 - B) = U * Uᴴ := by rw [Matrix.mul_assoc, hUB]
      rw [sub_mul (1 - B), mul_sub (1 - B), mul_sub (U * Uᴴ), h2, h3, h4, hYY]
      abel
    have htr : ((1 - B) - U * Uᴴ).trace = 0 := by
      rw [trace_sub, trace_sub, trace_one, Matrix.trace_mul_comm U Uᴴ, hUU, trace_sub,
        trace_one, htrB]
      ring
    have h0 : (((1 - B) - U * Uᴴ)ᴴ * ((1 - B) - U * Uᴴ)).trace = 0 := by rw [hEH, hEE, htr]
    rw [trace_conjTranspose_mul_self_eq_zero_iff] at h0
    exact (sub_eq_zero.mp h0).symm
  rw [hR]
  exact proj_of_coisometry hPH hPP hY hP1B

/-- **Closing preserves the two-projection constraint**: if `X𝖣Xᴴ` is the retained current,
the closed frame `C(z)ᴴX` satisfies `TwoProjection P 𝖣`. -/
theorem twoProjection_closed {κ : Type*} [Fintype κ] (hS : Sᴴ * S = 1) (hPH : Pᴴ = P)
    (hPP : P * P = P) (hPA : P * A = 0) (hPiP : Pi * P = 0) (hAH : Aᴴ = A) (hAA : A * A = A)
    (hAPi : A * Pi = Pi) (hPiPi : Pi * Piᴴ = A) (hU : IsUnit (1 - z • closingN S A Pi).det)
    (hz : star z * z = 1) {D : Matrix κ κ ℂ} {X : Matrix ι κ ℂ}
    (hX : X * D * Xᴴ = splitCurrent S P A Pi) :
    TwoProjection P D ((closingMap S A Pi z)ᴴ * X) := by
  unfold TwoProjection
  rw [gramProjection_closed hPH hPA hAH hAA hAPi hU hz hX]
  exact closedOutProj hS hPH hPP hPiP hAH hAA hAPi hPiPi hU hz

end BlockBand.SourceProcess.ClosedFeas
