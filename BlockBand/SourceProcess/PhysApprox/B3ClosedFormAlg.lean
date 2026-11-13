module

public import BlockBand.SourceProcess.PhysApprox.ClosingAnalyticAlg
public import BlockBand.Transmission.PositiveResolvent
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.LinearCombination

/-!
# Algebra of the closed exact update

Pure finite-dimensional algebra. Old interior pencil `Pn` with inverse `G`, port coupling `C`,
boundary map `U`, port resolvent `ℝ`, `𝕊 = 1 - cℝ`, `c = ζ - ζ̄` (`ζ = z_∂`), closing data `A`, `Π`
(`AΠ = Π`), phase `z`, `Q = (1 - zΠ𝕊A)⁻¹`, `Z = zQΠ𝕊`, closing map `C(z)`:

* `closed_pencil_mul`: `Gcl = G - cz U QΠ𝕊 Uᴴ` is a right inverse of the **far-closed pencil**
  `Pn - C(κY₀Π)Cᴴ`, `Y₀ = (1 - tΠ)⁻¹`, `t = zζ̄/ζ`, `κ = -cz/ζ²` (the closed far boundary is
  a port self-energy, independent of the length);
* `gcl_mul_near`, `near_mul_gcl`, `near_gcl_near`: the near column, row and corner of `Gcl` are
  `-ζ U C(z)ι`, `-ζ ι*𝕊(1 + Z)Uᴴ` and the closed near resolvent `ι*ℝC(z)ι`;
* `posSemidef_closed_gram_sub`: `C(z)C(z)ᴴ - (ι*𝕊(1+Z))ᴴ(ι*𝕊(1+Z)) ⪰ 0` on `|z| = 1`
  (lossless closing; uses only the unitarity of the unclosed `𝕊`);
* `passiveY_of_contraction`: `z_∂ - R⁻¹` is passive when `1 - cR` is a contraction.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.ClosedForm

open Matrix BlockBand.SourceProcess.Closing
open scoped ComplexOrder

variable {O P n k : Type*} [Fintype O] [Fintype P] [Fintype n] [Fintype k] [DecidableEq O]
  [DecidableEq P] [DecidableEq n] [DecidableEq k]

/-!
## The resolvent factor `Q`
-/

section Q

variable {S A Pi Q : Matrix P P ℂ} {z : ℂ}

theorem q_eq (hQ : (1 - z • (Pi * S * A)) * Q = 1) :
    Q = 1 + z • (Pi * (S * (A * Q))) := by
  have h : Q - z • (Pi * (S * (A * Q))) = 1 := by
    rw [← hQ]; simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc]
  calc Q = (Q - z • (Pi * (S * (A * Q)))) + z • (Pi * (S * (A * Q))) := by abel
    _ = _ := by rw [h]

theorem a_mul_q_mul (hQ : (1 - z • (Pi * S * A)) * Q = 1) (hAPi : A * Pi = Pi) :
    A * (Q * Pi) = Q * Pi := by
  have hAQ : A * Q = A + (Q - 1) := by
    conv_lhs => rw [q_eq hQ]
    conv_rhs => rw [q_eq hQ]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc A Pi, hAPi]
    abel
  rw [← Matrix.mul_assoc, hAQ, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hAPi]
  abel

theorem q_mul_pi_s (hQ : (1 - z • (Pi * S * A)) * Q = 1) (hAPi : A * Pi = Pi) :
    Q * (Pi * S) = Pi * S + z • (Pi * (S * (Q * (Pi * S)))) := by
  have h : A * Q * (Pi * S) = Q * (Pi * S) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, ← Matrix.mul_assoc A, a_mul_q_mul hQ hAPi,
      Matrix.mul_assoc]
  conv_lhs => rw [q_eq hQ]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc] at h ⊢
  rw [h]

omit [Fintype k] [DecidableEq k] in
/-- `ι*Q = ι*` when `ι*Π = 0`. -/
theorem ns_mul_q {ns : Matrix k P ℂ} (hQ : (1 - z • (Pi * S * A)) * Q = 1)
    (hnsPi : ns * Pi = 0) : ns * Q = ns := by
  conv_lhs => rw [q_eq hQ]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hnsPi,
    Matrix.zero_mul, smul_zero, add_zero]

end Q

/-!
## The far-closed pencil
-/

theorem closed_pencil_mul {Pn G : Matrix O O ℂ} {C U : Matrix O P ℂ}
    {S Rr A Pi Q Y0 : Matrix P P ℂ} {ζ c z κ t : ℂ}
    (hG : Pn * G = 1) (hCG : Cᴴ * G = -(ζ • (S * Uᴴ))) (hPU : Pn * U = -(ζ⁻¹ • C))
    (hCU : Cᴴ * U = 1 - ζ • Rr) (hS : S = 1 - c • Rr) (hc : c = ζ - star ζ)
    (hAPi : A * Pi = Pi) (hQ : (1 - z • (Pi * S * A)) * Q = 1) (hY0 : Y0 * (1 - t • Pi) = 1)
    (hκ : ζ * κ + c * z * ζ⁻¹ = 0) (ht : ζ * t = z * star ζ) :
    (Pn - C * (κ • (Y0 * Pi)) * Cᴴ) * (G - (c * z) • (U * (Q * (Pi * (S * Uᴴ))))) = 1 := by
  set a2 := Q * (Pi * S) with ha2
  set b3 := Y0 * (Pi * a2) with hb3
  set b5 := Y0 * (Pi * (Rr * a2)) with hb5
  have hW : a2 = Pi * S + z • (Pi * (S * a2)) := q_mul_pi_s hQ hAPi
  have r1 : Y0 * a2 = Y0 * (Pi * S) + z • (Y0 * (Pi * (S * a2))) := by
    calc Y0 * a2 = Y0 * (Pi * S + z • (Pi * (S * a2))) := by rw [← hW]
      _ = _ := by rw [Matrix.mul_add, Matrix.mul_smul]
  have r2 : Y0 * a2 - t • b3 = a2 := by
    calc Y0 * a2 - t • b3 = Y0 * (1 - t • Pi) * a2 := by
          simp only [hb3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul,
            Matrix.smul_mul, Matrix.mul_assoc]
      _ = a2 := by rw [hY0, Matrix.one_mul]
  have r3 : Y0 * (Pi * (S * a2)) = b3 - c • b5 := by
    have e : S * a2 = a2 - c • (Rr * a2) := by
      rw [hS, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [e, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
  have r2' : Y0 * a2 = a2 + t • b3 := sub_eq_iff_eq_add.mp r2
  have h1 : Y0 * (Pi * S) = a2 + t • b3 - z • (b3 - c • b5) := by
    calc Y0 * (Pi * S) = Y0 * a2 - z • (Y0 * (Pi * (S * a2))) := by rw [r1]; abel
      _ = _ := by rw [r3, r2']
  have hB : ζ • (κ • (Y0 * (Pi * S))) + (c * z * ζ⁻¹) • a2 +
      (c * z) • (κ • (Y0 * (Pi * ((1 - ζ • Rr) * a2)))) = 0 := by
    have h2 : Y0 * (Pi * ((1 - ζ • Rr) * a2)) = b3 - ζ • b5 := by
      simp only [hb3, hb5, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub,
        Matrix.mul_smul]
    rw [h1, h2]
    match_scalars <;>
      first | linear_combination hκ | linear_combination κ * ht + z * κ * hc | ring
  set M := Q * (Pi * (S * Uᴴ)) with hM
  have e1 : (Pn - C * (κ • (Y0 * Pi)) * Cᴴ) * (G - (c * z) • (U * M)) =
      Pn * G - C * (κ • (Y0 * Pi)) * (Cᴴ * G) - (c * z) • (Pn * U * M) +
        (c * z) • (C * (κ • (Y0 * Pi)) * (Cᴴ * U) * M) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    module
  rw [e1, hG, hCG, hPU, hCU]
  have e2 : (1 : Matrix O O ℂ) - C * (κ • (Y0 * Pi)) * -(ζ • (S * Uᴴ)) -
      (c * z) • (-(ζ⁻¹ • C) * M) + (c * z) • (C * (κ • (Y0 * Pi)) * (1 - ζ • Rr) * M) =
      1 + C * (ζ • (κ • (Y0 * (Pi * S))) + (c * z * ζ⁻¹) • a2 +
        (c * z) • (κ • (Y0 * (Pi * ((1 - ζ • Rr) * a2))))) * Uᴴ := by
    simp only [hM, ha2, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.one_mul, Matrix.mul_one]
    module
  rw [e2, hB, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-!
## Near column, row and corner of the closed inverse
-/

section Near

variable {Pn G : Matrix O O ℂ} {C U : Matrix O P ℂ} {S Rr A Pi : Matrix P P ℂ} {ζ c z : ℂ}
  {ns : Matrix k P ℂ}

omit [Fintype P] [DecidableEq P] in
theorem g_mul_c (hGP : G * Pn = 1) (hPU : Pn * U = -(ζ⁻¹ • C)) (hζ : ζ ≠ 0) :
    G * C = -(ζ • U) := by
  have h := congrArg (G * ·) hPU
  simp only [← Matrix.mul_assoc, hGP, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_smul] at h
  rw [h, smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ hζ, one_smul]

theorem s_u_c (hGP : G * Pn = 1) (hPU : Pn * U = -(ζ⁻¹ • C)) (hζ : ζ ≠ 0)
    (hCG : Cᴴ * G = -(ζ • (S * Uᴴ))) (hCU : Cᴴ * U = 1 - ζ • Rr) :
    S * (Uᴴ * C) = 1 - ζ • Rr := by
  have h1 : Cᴴ * G * C = -(ζ • (S * (Uᴴ * C))) := by
    rw [hCG, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc]
  have h2 : Cᴴ * G * C = -(ζ • (1 - ζ • Rr)) := by
    rw [Matrix.mul_assoc, g_mul_c hGP hPU hζ, Matrix.mul_neg, Matrix.mul_smul, hCU]
  have h3 := h1.symm.trans h2
  rw [neg_inj] at h3
  have := congrArg (ζ⁻¹ • ·) h3
  simpa only [smul_smul, inv_mul_cancel₀ hζ, one_smul] using this

omit [Fintype k] [DecidableEq k] in
/-- **The near column of the closed inverse**: `Gcl Cιᴴ = -ζ U C(z) ιᴴ`. -/
theorem gcl_mul_near (hGP : G * Pn = 1) (hPU : Pn * U = -(ζ⁻¹ • C)) (hζ : ζ ≠ 0)
    (hCG : Cᴴ * G = -(ζ • (S * Uᴴ))) (hCU : Cᴴ * U = 1 - ζ • Rr) (hS : S = 1 - c • Rr)
    (hPins : Pi * nsᴴ = 0) (hAns : A * nsᴴ = 0) :
    (G - (c * z) • (U * ((1 - z • closingN S A Pi)⁻¹ * (Pi * (S * Uᴴ))))) * (C * nsᴴ) =
      -(ζ • (U * (closingMap S A Pi z * nsᴴ))) := by
  set Q := (1 - z • closingN S A Pi)⁻¹
  have hsuc := s_u_c hGP hPU hζ hCG hCU
  have hgc := g_mul_c hGP hPU hζ
  have k1 : Pi * ((1 - ζ • Rr) * nsᴴ) = -(ζ • (Pi * (Rr * nsᴴ))) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, hPins, Matrix.mul_smul,
      zero_sub]
  have k2 : Pi * (S * nsᴴ) = -(c • (Pi * (Rr * nsᴴ))) := by
    rw [hS, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, hPins,
      Matrix.mul_smul, zero_sub]
  have hC : closingMap S A Pi z * nsᴴ = nsᴴ + z • (Q * (Pi * (S * nsᴴ))) := by
    simp only [closingMap, closingT, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hAns,
      sub_zero, Matrix.mul_zero, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_sub,
      Matrix.mul_one, Q]
  rw [hC, k2]
  calc (G - (c * z) • (U * (Q * (Pi * (S * Uᴴ))))) * (C * nsᴴ)
      = G * C * nsᴴ - (c * z) • (U * (Q * (Pi * ((S * (Uᴴ * C)) * nsᴴ)))) := by
        simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [hgc, hsuc, k1]
        simp only [Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_neg,
          Matrix.mul_smul, smul_neg, smul_add, smul_smul]
        module

omit [DecidableEq O] [Fintype k] [DecidableEq k] in
/-- **The near row of the closed inverse**: `ι Cᴴ Gcl = -ζ ι𝕊(1 + Z)Uᴴ`. -/
theorem near_mul_gcl (hCG : Cᴴ * G = -(ζ • (S * Uᴴ))) (hCU : Cᴴ * U = 1 - ζ • Rr)
    (hS : S = 1 - c • Rr) (hnsPi : ns * Pi = 0)
    (hU : IsUnit (1 - z • closingN S A Pi).det) :
    ns * Cᴴ * (G - (c * z) • (U * ((1 - z • closingN S A Pi)⁻¹ * (Pi * (S * Uᴴ))))) =
      -(ζ • (ns * (S * ((1 + closingZ S A Pi z) * Uᴴ)))) := by
  set Q := (1 - z • closingN S A Pi)⁻¹
  have hQ : (1 - z • (Pi * S * A)) * Q = 1 := mul_nonsing_inv _ hU
  have hnsQ : ns * Q = ns := ns_mul_q hQ hnsPi
  set X := Q * (Pi * (S * Uᴴ))
  have hnsX : ns * X = 0 := by
    simp only [X, ← Matrix.mul_assoc, hnsQ, hnsPi, Matrix.zero_mul]
  have hSX : ns * (S * X) = -(c • (ns * (Rr * X))) := by
    rw [hS, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, hnsX,
      Matrix.mul_smul, zero_sub]
  have hZ : (1 + closingZ S A Pi z) * Uᴴ = Uᴴ + z • X := by
    simp only [closingZ, X, Q, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_assoc]
  rw [hZ]
  calc ns * Cᴴ * (G - (c * z) • (U * X)) = ns * (Cᴴ * G) - (c * z) • (ns * (Cᴴ * U) * X) := by
        simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_assoc]
    _ = _ := by
        rw [hCG, hCU]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_neg,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_assoc, hnsX, hSX]
        module

omit [Fintype k] [DecidableEq k] in
/-- `ι C(z) = ι` when `ιA = 0`, `ιΠ = 0`. -/
theorem ns_mul_closingMap (hnsA : ns * A = 0) (hnsPi : ns * Pi = 0)
    (hU : IsUnit (1 - z • closingN S A Pi).det) : ns * closingMap S A Pi z = ns := by
  have hQ : (1 - z • (Pi * S * A)) * (1 - z • closingN S A Pi)⁻¹ = 1 := mul_nonsing_inv _ hU
  rw [closingMap, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, hnsA, sub_zero,
    ← Matrix.mul_assoc, ns_mul_q hQ hnsPi, closingT, Matrix.mul_smul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hnsPi, Matrix.zero_mul, Matrix.zero_mul, smul_zero, add_zero]

omit [Fintype k] in
/-- **The near corner**: `ζ⁻¹(1 + ζ⁻¹ ιCᴴGclCιᴴ) = ιℝC(z)ιᴴ`, the closed near resolvent. -/
theorem near_gcl_near (hGP : G * Pn = 1) (hPU : Pn * U = -(ζ⁻¹ • C)) (hζ : ζ ≠ 0)
    (hCG : Cᴴ * G = -(ζ • (S * Uᴴ))) (hCU : Cᴴ * U = 1 - ζ • Rr) (hS : S = 1 - c • Rr)
    (hPins : Pi * nsᴴ = 0) (hAns : A * nsᴴ = 0) (hnsPi : ns * Pi = 0) (hnsA : ns * A = 0)
    (hns : ns * nsᴴ = 1) (hU : IsUnit (1 - z • closingN S A Pi).det) :
    ζ⁻¹ • (1 + ζ⁻¹ • (ns * Cᴴ * ((G - (c * z) •
        (U * ((1 - z • closingN S A Pi)⁻¹ * (Pi * (S * Uᴴ))))) * (C * nsᴴ)))) =
      ns * Rr * closingMap S A Pi z * nsᴴ := by
  rw [gcl_mul_near hGP hPU hζ hCG hCU hS hPins hAns]
  have e : ns * Cᴴ * -(ζ • (U * (closingMap S A Pi z * nsᴴ))) =
      -(ζ • (ns * closingMap S A Pi z * nsᴴ)) + (ζ * ζ) • (ns * Rr * closingMap S A Pi z * nsᴴ) := by
    simp only [Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Cᴴ U, hCU]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul]
    module
  rw [e, ns_mul_closingMap hnsA hnsPi hU, hns]
  match_scalars <;> field_simp
  ring

end Near

/-!
## Lossless closing: the frame inequality
-/

section Frame

variable {S A Pi : Matrix P P ℂ} {z : ℂ} {ns : Matrix k P ℂ}

/-- `Π𝕊(1 + Z) = z̄ Z` on `|z| = 1`. -/
theorem pi_s_one_add_z (hAPi : A * Pi = Pi) (hU : IsUnit (1 - z • closingN S A Pi).det)
    (hz : z * star z = 1) :
    Pi * (S * (1 + closingZ S A Pi z)) = star z • closingZ S A Pi z := by
  have hQ : (1 - z • (Pi * S * A)) * (1 - z • closingN S A Pi)⁻¹ = 1 := mul_nonsing_inv _ hU
  have hW := q_mul_pi_s hQ hAPi
  have hZ : closingZ S A Pi z = z • (Pi * (S * (1 + closingZ S A Pi z))) := by
    simp only [closingZ, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, smul_add]
    conv_lhs => rw [hW]
    simp only [smul_add, closingN]
  conv_rhs => rw [hZ]
  rw [smul_smul, mul_comm, hz, one_smul]

/-- `E = ιᴴι + ΠᴴΠ` is a Hermitian idempotent, so `1 - E ⪰ 0`. -/
theorem posSemidef_one_sub_near_pi (hAPi : A * Pi = Pi) (hPi : Pi * Piᴴ = A)
    (hPins : Pi * nsᴴ = 0) (hns : ns * nsᴴ = 1) :
    (1 - nsᴴ * ns - Piᴴ * Pi).PosSemidef := by
  set F : Matrix P P ℂ := 1 - nsᴴ * ns - Piᴴ * Pi
  have hFH : Fᴴ = F := by
    simp only [F, conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose]
  have hnsPi' : ns * Piᴴ = 0 := by
    have := congrArg conjTranspose hPins
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
  have e1 : nsᴴ * ns * (nsᴴ * ns) = nsᴴ * ns := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ns, hns, Matrix.one_mul]
  have e2 : Piᴴ * Pi * (Piᴴ * Pi) = Piᴴ * Pi := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPi, hAPi]
  have e3 : nsᴴ * ns * (Piᴴ * Pi) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ns, hnsPi', Matrix.zero_mul, Matrix.mul_zero]
  have e4 : Piᴴ * Pi * (nsᴴ * ns) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPins, Matrix.zero_mul, Matrix.mul_zero]
  have hFF : Fᴴ * F = F := by
    rw [hFH]
    simp only [F, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2, e3, e4]
    abel
  rw [← hFF]
  exact posSemidef_conjTranspose_mul_self F

/-- **Lossless closing, frame form**: `C(z)C(z)ᴴ - (ι𝕊(1+Z))ᴴ(ι𝕊(1+Z)) ⪰ 0` on `|z| = 1`. -/
theorem posSemidef_closed_gram_sub (hA2 : A * A = A) (hAH : Aᴴ = A) (hAPi : A * Pi = Pi)
    (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1) (hz : z * star z = 1)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (hPins : Pi * nsᴴ = 0) (hns : ns * nsᴴ = 1) :
    (closingMap S A Pi z * (closingMap S A Pi z)ᴴ -
      (ns * (S * (1 + closingZ S A Pi z)))ᴴ * (ns * (S * (1 + closingZ S A Pi z)))).PosSemidef := by
  set Z := closingZ S A Pi z
  set B := S * (1 + Z)
  have hSS : Sᴴ * S = 1 := mul_eq_one_comm.mp hS
  have hzz : star z * z = 1 := by rw [mul_comm]; exact hz
  have hCC := closingMap_mul_conj hA2 hAH hPi hS hz hU
  have hPB : Pi * B = star z • Z := pi_s_one_add_z hAPi hU hz
  have hBB : Bᴴ * B = (1 + Z)ᴴ * (1 + Z) := by
    simp only [B, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Sᴴ S, hSS, Matrix.one_mul]
  have hZZ : (Pi * B)ᴴ * (Pi * B) = Zᴴ * Z := by
    rw [hPB, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_star, hz,
      one_smul]
  have key : closingMap S A Pi z * (closingMap S A Pi z)ᴴ - (ns * B)ᴴ * (ns * B) =
      Bᴴ * (1 - nsᴴ * ns - Piᴴ * Pi) * B := by
    have e : Bᴴ * (1 - nsᴴ * ns - Piᴴ * Pi) * B =
        Bᴴ * B - (ns * B)ᴴ * (ns * B) - (Pi * B)ᴴ * (Pi * B) := by
      simp only [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.mul_assoc]
    rw [e, hBB, hZZ, hCC]
    simp only [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
    abel
  rw [key]
  exact (posSemidef_one_sub_near_pi hAPi hPi hPins hns).conjTranspose_mul_mul_same B

end Frame

/-!
## Passivity from a contraction
-/

/-- **`z_∂ - R⁻¹` is passive** when `R` is invertible and `1 - (1 - cR)ᴴ(1 - cR) ⪰ 0`,
`c = ζ - ζ̄ = 2iη`, `η > 0`. -/
theorem passiveY_of_contraction {R : Matrix n n ℂ} {ζ : ℂ} {η : ℝ} (hη : 0 < η)
    (hc : ζ - star ζ = ((2 * η : ℝ) : ℂ) * Complex.I) (hR : IsUnit R.det)
    (hr : (1 - (1 - (ζ - star ζ) • R)ᴴ * (1 - (ζ - star ζ) • R)).PosSemidef) :
    (-BlockBand.Transmission.matrixImaginaryPart (ζ • (1 : Matrix n n ℂ) - R⁻¹)).PosSemidef := by
  set c := ζ - star ζ with hcdef
  set Ri := R⁻¹
  have hRRi : R * Ri = 1 := mul_nonsing_inv _ hR
  have hRiH : Riᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRRi, conjTranspose_one]
  have hcs : star c = -c := by simp only [c, star_sub, star_star, neg_sub]
  have key : Riᴴ * (1 - (1 - c • R)ᴴ * (1 - c • R)) * Ri =
      c • ((ζ • (1 : Matrix n n ℂ) - Ri) - (ζ • (1 : Matrix n n ℂ) - Ri)ᴴ) := by
    have e1 : Riᴴ * (1 - (1 - c • R)ᴴ * (1 - c • R)) * Ri =
        c • (Riᴴ * (R * Ri)) + star c • ((Riᴴ * Rᴴ) * Ri) -
          (star c * c) • ((Riᴴ * Rᴴ) * (R * Ri)) := by
      simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc]
      module
    rw [e1, hRRi, hRiH, hcs]
    simp only [Matrix.mul_one, Matrix.one_mul, conjTranspose_sub, conjTranspose_smul,
      conjTranspose_one, smul_sub, smul_smul]
    rw [show star ζ = ζ - c by simp only [c]; ring]
    module
  have hc0 : c ≠ 0 := by
    rw [hc]; intro h0
    have := congrArg Complex.im h0
    simp at this; linarith
  have hY : -BlockBand.Transmission.matrixImaginaryPart (ζ • (1 : Matrix n n ℂ) - Ri) =
      (((4 * η)⁻¹ : ℝ) : ℂ) • (Riᴴ * (1 - (1 - c • R)ᴴ * (1 - c • R)) * Ri) := by
    rw [key, smul_smul, BlockBand.Transmission.matrixImaginaryPart, ← neg_smul]
    congr 1
    rw [hc]
    have hη0 : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    push_cast
    field_simp
    ring_nf
  rw [hY]
  refine (hr.conjTranspose_mul_mul_same Ri).smul ?_
  exact_mod_cast (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ 4 * η))

end BlockBand.SourceProcess.PhysApprox.ClosedForm
