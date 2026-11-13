module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `det(I + A)⁻¹` for positive semidefinite `A`: range and trace-Lipschitz bound

For `A, B ⪰ 0` (complex, finite index):
* `det_one_add_eq`: `det(I + A) = Π_k (1 + λ_k(A))`, real and `≥ 1`;
* `det_one_add_add_eq`: `det(I + A + B) = det(I + A) det(I + N)`, `N = R^{1/2} U*BU R^{1/2}`,
  `R = (I + D)⁻¹` in an eigenbasis `A = UDU*` of `A`; `N ⪰ 0` and `Re Tr N ≤ Re Tr B`;
* **`abs_re_inv_det_sub_le`**: `|Re det(I+A)⁻¹ - Re det(I+A+B)⁻¹| ≤ Re Tr B`, via
  `1 ≤ det(I+N) ≤ exp(Tr N)` and `1 - e^{-x} ≤ x`;
* `re_inv_det_mem`: `0 < Re det(I+A)⁻¹ ≤ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `det(I + A) = Π_k (1 + λ_k)` for Hermitian `A`. -/
theorem det_one_add_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (1 + A).det = ((∏ k, (1 + hA.eigenvalues k) : ℝ) : ℂ) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hs : A = U * diagonal (fun k => (hA.eigenvalues k : ℂ)) * star U := hA.spectral_theorem
  have h1 : 1 + A = U * diagonal (fun k => ((1 + hA.eigenvalues k : ℝ) : ℂ)) * star U := by
    have hd : diagonal (fun k => ((1 + hA.eigenvalues k : ℝ) : ℂ)) =
        1 + diagonal (fun k => (hA.eigenvalues k : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
    rw [hd, mul_add, add_mul, mul_one, hUU, ← hs]
  rw [h1, det_mul, det_mul, mul_right_comm, ← det_mul, hUU, det_one, one_mul, det_diagonal,
    Complex.ofReal_prod]

theorem one_le_prod_one_add {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    1 ≤ ∏ k, (1 + hA.1.eigenvalues k) :=
  Finset.one_le_prod₀ fun k _ => by linarith [hA.eigenvalues_nonneg k]

theorem re_trace_eq_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.trace.re = ∑ k, hA.eigenvalues k := by
  have h := hA.trace_eq_sum_eigenvalues
  have h2 : A.trace = ((∑ k, hA.eigenvalues k : ℝ) : ℂ) := by
    rw [h, Complex.ofReal_sum]; rfl
  rw [h2, Complex.ofReal_re]

theorem prod_one_add_le_exp {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    ∏ k, (1 + hA.1.eigenvalues k) ≤ Real.exp A.trace.re := by
  rw [re_trace_eq_sum hA.1, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun k _ => by linarith [hA.eigenvalues_nonneg k]) fun k _ => ?_
  have := Real.add_one_le_exp (hA.1.eigenvalues k)
  linarith

/-- The sandwich factor `R^{1/2} = diag((1 + λ_k)^{-1/2})`. -/
def rootRes {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  diagonal fun k => ((1 / Real.sqrt (1 + hA.eigenvalues k) : ℝ) : ℂ)

/-- `N = R^{1/2} U*BU R^{1/2}`. -/
def sandN {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n n ℂ) : Matrix n n ℂ :=
  rootRes hA * (star (hA.eigenvectorUnitary : Matrix n n ℂ) * B *
    (hA.eigenvectorUnitary : Matrix n n ℂ)) * rootRes hA

theorem rootRes_conjTranspose {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (rootRes hA)ᴴ = rootRes hA := by
  simp [rootRes, diagonal_conjTranspose]

theorem sandN_posSemidef {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.PosSemidef) :
    (sandN hA B).PosSemidef := by
  have h1 := hB.conjTranspose_mul_mul_same (hA.eigenvectorUnitary : Matrix n n ℂ)
  have h2 := h1.conjTranspose_mul_mul_same (rootRes hA)
  rw [rootRes_conjTranspose, ← star_eq_conjTranspose] at h2
  exact h2

theorem rootRes_sq_mul {A : Matrix n n ℂ} (hA : A.PosSemidef) (k : n) :
    (1 / Real.sqrt (1 + hA.1.eigenvalues k)) * (1 + hA.1.eigenvalues k) *
      (1 / Real.sqrt (1 + hA.1.eigenvalues k)) = 1 := by
  have hpos : 0 < 1 + hA.1.eigenvalues k := by linarith [hA.eigenvalues_nonneg k]
  have hs := Real.mul_self_sqrt hpos.le
  have hsp : 0 < Real.sqrt (1 + hA.1.eigenvalues k) := Real.sqrt_pos.2 hpos
  field_simp
  linarith

theorem det_one_add_add_eq {A B : Matrix n n ℂ} (hA : A.PosSemidef) :
    (1 + (A + B)).det = (1 + A).det * (1 + sandN hA.1 B).det := by
  set U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ)
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hUU' : star U * U = 1 := Unitary.coe_star_mul_self _
  have hs : A = U * diagonal (fun k => (hA.1.eigenvalues k : ℂ)) * star U := hA.1.spectral_theorem
  set D1 : Matrix n n ℂ := diagonal fun k => ((1 + hA.1.eigenvalues k : ℝ) : ℂ)
  have hD1 : D1 = 1 + diagonal (fun k => (hA.1.eigenvalues k : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [D1]
    · simp [D1, diagonal_apply_ne _ hij, one_apply_ne hij]
  set B' := star U * B * U
  have h1 : 1 + (A + B) = U * (D1 + B') * star U := by
    have e1 : U * (1 + diagonal (fun k => (hA.1.eigenvalues k : ℂ))) * star U = 1 + A := by
      rw [Matrix.mul_add, Matrix.add_mul, mul_one, hUU, ← hs]
    have e2 : U * B' * star U = B := by
      simp only [B', ← Matrix.mul_assoc]
      rw [hUU, one_mul, Matrix.mul_assoc, hUU, mul_one]
    rw [hD1, Matrix.mul_add, Matrix.add_mul, e1, e2, add_assoc]
  have hdet1 : (1 + (A + B)).det = (D1 + B').det := by
    rw [h1, det_mul, det_mul, mul_right_comm, ← det_mul, hUU, det_one, one_mul]
  set R := rootRes hA.1
  have hR : R * D1 * R = 1 := by
    simp only [R, rootRes, D1, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext k
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, rootRes_sq_mul hA k, Complex.ofReal_one]
  have h2 : 1 + sandN hA.1 B = R * (D1 + B') * R := by
    rw [Matrix.mul_add, Matrix.add_mul, hR]
    rfl
  have hdetR : R.det * R.det * (1 + A).det = 1 := by
    rw [det_one_add_eq hA.1]
    simp only [R, rootRes, det_diagonal, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
      ← Finset.prod_mul_distrib]
    rw [show (fun k => 1 / Real.sqrt (1 + hA.1.eigenvalues k) *
        (1 / Real.sqrt (1 + hA.1.eigenvalues k)) * (1 + hA.1.eigenvalues k)) = fun _ => 1 from
      funext fun k => by rw [mul_right_comm, rootRes_sq_mul hA k]]
    simp
  rw [h2, det_mul, det_mul, hdet1]
  linear_combination -(D1 + B').det * hdetR

theorem re_trace_sandN_le {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (sandN hA.1 B).trace.re ≤ B.trace.re := by
  set U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ)
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hB' : (star U * B * U).PosSemidef := by
    rw [star_eq_conjTranspose]; exact hB.conjTranspose_mul_mul_same U
  have htr : (star U * B * U).trace = B.trace := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hUU, mul_one]
  rw [← htr]
  simp only [sandN, rootRes, trace, diag, diagonal_mul, mul_diagonal, Complex.re_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hd := hB'.diag_nonneg (i := k)
  have hre : 0 ≤ (star U * B * U) k k := hd
  rw [Complex.nonneg_iff] at hre
  have hpos : 1 ≤ 1 + hA.1.eigenvalues k := by linarith [hA.eigenvalues_nonneg k]
  set r := 1 / Real.sqrt (1 + hA.1.eigenvalues k)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.2 (by linarith))]
    exact Real.one_le_sqrt.2 hpos
  have : ((r : ℂ) * (star U * B * U) k k * (r : ℂ)).re = r * r * ((star U * B * U) k k).re := by
    simp [Complex.mul_re]; ring
  rw [this]
  have := mul_le_mul hr1 hr1 hr0 zero_le_one
  nlinarith [hre.1]

/-- `0 < Re det(I + A)⁻¹ ≤ 1` for `A ⪰ 0`. -/
theorem re_inv_det_mem {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    0 < ((1 + A).det⁻¹).re ∧ ((1 + A).det⁻¹).re ≤ 1 := by
  rw [det_one_add_eq hA.1, ← Complex.ofReal_inv, Complex.ofReal_re]
  have h := one_le_prod_one_add hA
  exact ⟨inv_pos.2 (by linarith), inv_le_one_of_one_le₀ h⟩

/-- **Trace-Lipschitz bound**: `|Re det(I+A)⁻¹ - Re det(I+A+B)⁻¹| ≤ Re Tr B` for `A, B ⪰ 0`. -/
theorem abs_re_inv_det_sub_le {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    |((1 + A).det⁻¹).re - ((1 + (A + B)).det⁻¹).re| ≤ B.trace.re := by
  have hN := sandN_posSemidef hA.1 hB
  rw [det_one_add_add_eq hA, det_one_add_eq hA.1, det_one_add_eq hN.1, ← Complex.ofReal_mul,
    ← Complex.ofReal_inv, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re]
  set a := ∏ k, (1 + hA.1.eigenvalues k)
  set d := ∏ k, (1 + hN.1.eigenvalues k)
  have ha : 1 ≤ a := one_le_prod_one_add hA
  have hd : 1 ≤ d := one_le_prod_one_add hN
  have hdexp : d ≤ Real.exp (sandN hA.1 B).trace.re := prod_one_add_le_exp hN
  have htr := re_trace_sandN_le hA hB
  set x := (sandN hA.1 B).trace.re
  have hx : 0 ≤ x := by
    have := hN.trace_nonneg
    rw [Complex.nonneg_iff] at this
    exact this.1
  have ha0 : 0 < a := by linarith
  have hd0 : 0 < d := by linarith
  -- `1/d ≥ exp(-x) ≥ 1 - x`
  have hinv : 1 - x ≤ d⁻¹ := by
    have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    have h2 : Real.exp (-x) ≤ d⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ hd0 hdexp
    linarith
  have hdiff : a⁻¹ - (a * d)⁻¹ = a⁻¹ * (1 - d⁻¹) := by
    rw [mul_inv]; ring
  have hai : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
  have hai0 : 0 ≤ a⁻¹ := inv_nonneg.2 ha0.le
  have hdi : d⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd
  rw [hdiff, abs_of_nonneg (mul_nonneg hai0 (by linarith))]
  calc a⁻¹ * (1 - d⁻¹) ≤ 1 * (1 - d⁻¹) := mul_le_mul_of_nonneg_right hai (by linarith)
    _ ≤ B.trace.re := by linarith

end BlockBand.SourceProcess.SourceProcessLaw
