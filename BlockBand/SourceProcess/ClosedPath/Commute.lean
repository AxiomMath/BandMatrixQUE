module

public import BlockBand.SourceProcess.Closing.Defs

/-!
# Closing at time `s` or at final time eliminates the same linear equations

Pure algebra on the closing map `C(z) = (1 - A) + (1 - zN)⁻¹ zT` (`Closing.closingMap`),
`N = Π𝕊A`, `T = Π𝕊(1-A)`, with `A` an orthogonal projection and `AΠ = Π`.

* `closingMap_conj_fix`: `C(z)ᴴ V = V` whenever `AV = 0` (no invertibility needed). Retained
  current columns are not moved by the closing.
* `closingMap_feedback`: if `1 - zN` is invertible, `C(z)` solves the closing equations
  `A·C = zΠ𝕊·C` (omitted inputs fed by the paired omitted outputs), `(1-A)C = 1-A`.
* `closingMap_unique`: every solution `Y` of `AY = zΠ𝕊Y` is `Y = C(z)(1-A)Y`.
* **`transport_mul_closingMap`** (one growth step `j → j+1`, near-end growth): if the transport
  `N_j` keeps the far input (`(1-P)N_j = 1-P`) and the far output (`(1-P)𝕊_jN_j = (1-P)𝕊_{j+1}`),
  and `A, Π` live on the far port, then `N_j C_{j+1}(z) = C_j(z)·N^cl_j` with the **closed
  transport** `N^cl_j = (1-A)N_jC_{j+1}(z)`. Equivalently (`closingMap_conj_transport`)
  `C_{j+1}ᴴ N_jᴴ = (N^cl_j)ᴴ C_jᴴ`: a closed column `C(z)ᴴv` at `j+1` is the closed
  transport of the closed column at `j`. Iterating from `n_s` (closing at time `s`) to `⌊WT⌋`
  gives the final-time closed probes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedPath

open Matrix BlockBand.SourceProcess.Closing

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S A Pi : Matrix ι ι ℂ} {z : ℂ}

/-- A matrix commuting with `M` commutes with Lean's `M⁻¹` (also when `M` is singular). -/
theorem inv_comm_of_comm {A M : Matrix ι ι ℂ} (h : A * M = M * A) : M⁻¹ * A = A * M⁻¹ := by
  by_cases hM : IsUnit M.det
  · calc M⁻¹ * A = M⁻¹ * A * (M * M⁻¹) := by rw [mul_nonsing_inv _ hM, Matrix.mul_one]
      _ = M⁻¹ * (M * A) * M⁻¹ := by rw [← h]; simp only [Matrix.mul_assoc]
      _ = A * M⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.one_mul]
  · rw [nonsing_inv_apply_not_isUnit _ hM, Matrix.zero_mul, Matrix.mul_zero]

omit [DecidableEq ι] in
theorem A_mul_closingN (hAPi : A * Pi = Pi) : A * closingN S A Pi = closingN S A Pi := by
  simp only [closingN, ← Matrix.mul_assoc, hAPi]

omit [DecidableEq ι] in
theorem closingN_mul_A (hAA : A * A = A) : closingN S A Pi * A = closingN S A Pi := by
  simp only [closingN, Matrix.mul_assoc, hAA]

theorem A_mul_closingT (hAPi : A * Pi = Pi) : A * closingT S A Pi = closingT S A Pi := by
  simp only [closingT, ← Matrix.mul_assoc, hAPi]

theorem closingT_mul_compl (hAA : A * A = A) :
    closingT S A Pi * (1 - A) = closingT S A Pi := by
  have : (1 - A) * (1 - A) = 1 - A := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hAA]; simp
  simp only [closingT, Matrix.mul_assoc, this]

/-- `A` commutes with `1 - zN`, hence with its inverse. -/
theorem A_mul_inv (hAA : A * A = A) (hAPi : A * Pi = Pi) :
    A * (1 - z • closingN S A Pi)⁻¹ = (1 - z • closingN S A Pi)⁻¹ * A := by
  refine (inv_comm_of_comm ?_).symm
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, A_mul_closingN hAPi, closingN_mul_A hAA]

/-- `A X = X` for `X = (1 - zN)⁻¹ zT`. -/
theorem A_mul_closingX (hAA : A * A = A) (hAPi : A * Pi = Pi) :
    A * ((1 - z • closingN S A Pi)⁻¹ * (z • closingT S A Pi)) =
      (1 - z • closingN S A Pi)⁻¹ * (z • closingT S A Pi) := by
  rw [← Matrix.mul_assoc, A_mul_inv hAA hAPi, Matrix.mul_assoc, Matrix.mul_smul,
    A_mul_closingT hAPi]

theorem A_mul_closingMap (hAA : A * A = A) (hAPi : A * Pi = Pi) :
    A * closingMap S A Pi z = (1 - z • closingN S A Pi)⁻¹ * (z • closingT S A Pi) := by
  rw [closingMap, Matrix.mul_add, A_mul_closingX hAA hAPi, Matrix.mul_sub, Matrix.mul_one, hAA,
    sub_self, zero_add]

theorem compl_mul_closingMap (hAA : A * A = A) (hAPi : A * Pi = Pi) :
    (1 - A) * closingMap S A Pi z = 1 - A := by
  rw [Matrix.sub_mul, Matrix.one_mul, A_mul_closingMap hAA hAPi, closingMap]; abel

/-- **Retained columns are fixed**: `AV = 0 ⇒ C(z)ᴴV = V`. -/
theorem closingMap_conj_fix {κ : Type*} (hAH : Aᴴ = A) (hAPi : A * Pi = Pi)
    {V : Matrix ι κ ℂ} (hV : A * V = 0) : (closingMap S A Pi z)ᴴ * V = V := by
  have hPiA : Piᴴ * A = Piᴴ := by rw [← hAH, ← conjTranspose_mul, hAPi]
  set M := 1 - z • closingN S A Pi
  have hPV : Piᴴ * V = 0 := by rw [← hPiA, Matrix.mul_assoc, hV, Matrix.mul_zero]
  have hMA : Mᴴ * V = V := by
    simp only [M, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, closingN,
      conjTranspose_mul, hAH, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc,
      hPV, Matrix.mul_zero, smul_zero, sub_zero]
  have hAinv : A * ((Mᴴ)⁻¹ * V) = 0 := by
    by_cases hU : IsUnit (Mᴴ).det
    · calc A * ((Mᴴ)⁻¹ * V) = A * ((Mᴴ)⁻¹ * (Mᴴ * V)) := by rw [hMA]
        _ = A * V := by rw [← Matrix.mul_assoc (Mᴴ)⁻¹, nonsing_inv_mul _ hU, Matrix.one_mul]
        _ = 0 := hV
    · rw [nonsing_inv_apply_not_isUnit _ hU, Matrix.zero_mul, Matrix.mul_zero]
  have hT : (z • closingT S A Pi)ᴴ * ((Mᴴ)⁻¹ * V) = 0 := by
    rw [conjTranspose_smul, closingT, conjTranspose_mul, conjTranspose_mul, ← hPiA]
    simp only [Matrix.smul_mul, Matrix.mul_assoc, hAinv, Matrix.mul_zero, smul_zero]
  rw [closingMap, conjTranspose_add, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.add_mul,
    Matrix.mul_assoc, hT, add_zero, conjTranspose_sub, conjTranspose_one, hAH, Matrix.sub_mul,
    Matrix.one_mul, hV, sub_zero]

/-- **The closing equations**: `A·C(z) = zΠ𝕊·C(z)` when `1 - zN` is invertible. -/
theorem closingMap_feedback (hAA : A * A = A) (hAPi : A * Pi = Pi)
    (hU : IsUnit (1 - z • closingN S A Pi).det) :
    A * closingMap S A Pi z = z • (Pi * S * closingMap S A Pi z) := by
  set X := (1 - z • closingN S A Pi)⁻¹ * (z • closingT S A Pi)
  have hX : X = z • closingT S A Pi + z • (closingN S A Pi * X) := by
    have h1 : (1 - z • closingN S A Pi) * X = z • closingT S A Pi := by
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ hU, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul] at h1
    rw [← h1]; abel
  have hAX : A * X = X := A_mul_closingX hAA hAPi
  have hNX : closingN S A Pi * X = Pi * S * X := by rw [closingN, Matrix.mul_assoc _ A, hAX]
  rw [hNX] at hX
  rw [A_mul_closingMap hAA hAPi]
  change X = _
  rw [closingMap, Matrix.mul_add, smul_add]
  exact hX

/-- **Uniqueness**: a solution of `AY = zΠ𝕊Y` is `Y = C(z)(1-A)Y`. -/
theorem closingMap_unique {κ : Type*} (hAA : A * A = A)
    (hU : IsUnit (1 - z • closingN S A Pi).det) {Y : Matrix ι κ ℂ}
    (hY : A * Y = z • (Pi * S * Y)) : Y = closingMap S A Pi z * ((1 - A) * Y) := by
  have hsplit : Pi * S * Y = closingT S A Pi * Y + closingN S A Pi * (A * Y) := by
    simp only [closingT, closingN, Matrix.mul_assoc, ← Matrix.mul_add, Matrix.sub_mul,
      Matrix.one_mul, ← Matrix.mul_assoc A A Y, hAA, sub_add_cancel]
  have hY' : A * Y = z • (closingT S A Pi * Y) + z • (closingN S A Pi * (A * Y)) := by
    rw [← smul_add, ← hsplit]; exact hY
  have h1 : (1 - z • closingN S A Pi) * (A * Y) = (z • closingT S A Pi) * Y := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul]
    rw [sub_eq_iff_eq_add]; exact hY'
  have h2 : A * Y = (1 - z • closingN S A Pi)⁻¹ * (z • closingT S A Pi) * ((1 - A) * Y) := by
    have hT : (z • closingT S A Pi) * ((1 - A) * Y) = (z • closingT S A Pi) * Y := by
      rw [← Matrix.mul_assoc, Matrix.smul_mul, closingT_mul_compl hAA, Matrix.smul_mul]
    rw [Matrix.mul_assoc, hT, ← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hU, Matrix.one_mul]
  have hcc : (1 - A) * ((1 - A) * Y) = (1 - A) * Y := by
    rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hAA]; simp
  rw [closingMap, Matrix.add_mul, hcc, ← h2, Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]

/-- **Closing commutes with one near-end growth step**. -/
theorem transport_mul_closingMap {P N S₀ S₁ : Matrix ι ι ℂ} (hAA : A * A = A)
    (hAPi : A * Pi = Pi) (hAP : A * (1 - P) = A) (hPiP : Pi * (1 - P) = Pi)
    (hPN : (1 - P) * N = 1 - P) (hS : (1 - P) * S₀ * N = (1 - P) * S₁)
    (hU₀ : IsUnit (1 - z • closingN S₀ A Pi).det) (hU₁ : IsUnit (1 - z • closingN S₁ A Pi).det) :
    N * closingMap S₁ A Pi z = closingMap S₀ A Pi z * ((1 - A) * (N * closingMap S₁ A Pi z)) := by
  refine closingMap_unique hAA hU₀ ?_
  have hAN : A * N = A := by rw [← hAP, Matrix.mul_assoc, hPN]
  rw [← Matrix.mul_assoc, hAN, closingMap_feedback hAA hAPi hU₁]
  congr 1
  calc Pi * S₁ * closingMap S₁ A Pi z = Pi * ((1 - P) * S₁) * closingMap S₁ A Pi z := by
        rw [← Matrix.mul_assoc, hPiP]
    _ = Pi * ((1 - P) * S₀ * N) * closingMap S₁ A Pi z := by rw [hS]
    _ = Pi * S₀ * (N * closingMap S₁ A Pi z) := by
        rw [← Matrix.mul_assoc Pi ((1 - P) * S₀) N, ← Matrix.mul_assoc Pi (1 - P) S₀, hPiP]
        simp only [Matrix.mul_assoc]

/-- **Closed columns are transported by the closed transport**:
`C_{j+1}ᴴ N_jᴴ = (N^cl_j)ᴴ C_jᴴ`, `N^cl_j = (1-A)N_jC_{j+1}`. -/
theorem closingMap_conj_transport {P N S₀ S₁ : Matrix ι ι ℂ} (hAA : A * A = A)
    (hAPi : A * Pi = Pi) (hAP : A * (1 - P) = A) (hPiP : Pi * (1 - P) = Pi)
    (hPN : (1 - P) * N = 1 - P) (hS : (1 - P) * S₀ * N = (1 - P) * S₁)
    (hU₀ : IsUnit (1 - z • closingN S₀ A Pi).det) (hU₁ : IsUnit (1 - z • closingN S₁ A Pi).det) :
    (closingMap S₁ A Pi z)ᴴ * Nᴴ =
      ((1 - A) * (N * closingMap S₁ A Pi z))ᴴ * (closingMap S₀ A Pi z)ᴴ := by
  rw [← conjTranspose_mul, ← conjTranspose_mul]
  exact congrArg conjTranspose (transport_mul_closingMap hAA hAPi hAP hPiP hPN hS hU₀ hU₁)

end BlockBand.SourceProcess.ClosedPath
