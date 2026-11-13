module

public import BlockBand.SourceProcess.SourceProcessLaw.DetBound

/-!
# Second-order expansion of `Π_j Re det(I + Z_j + c_j B)⁻¹` in a positive matrix `B`

For `Z ⪰ 0`, `B ⪰ 0` and `c ≥ 0`, `det_one_add_add_eq` gives
`det(I + Z + cB) = det(I + Z) det(I + cN)`, `N = R^{1/2}U*BU R^{1/2}`. With
`τ = Re Tr N = Re Tr(K B)` (`K = linKer`, linear in `B`) the factor `D = det(I + cN)` satisfies
`1 + cτ ≤ D ≤ e^{cτ}` and `0 ≤ τ ≤ Re Tr B`. Hence, with `S = Σ_j c_j τ_j`,
`|Π_j F(Z_j + c_jB) - Π_j F(Z_j)(1 - S)| ≤ S²` (`abs_prod_invDet_sub_le`), `F = invDet`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open Matrix BlockBand.SourceProcess.SourceProcessLaw
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `F(X) = Re det(I + X)⁻¹`. -/
def invDet (X : Matrix n n ℂ) : ℝ := ((1 + X).det⁻¹).re

theorem invDet_mem {X : Matrix n n ℂ} (hX : X.PosSemidef) : 0 < invDet X ∧ invDet X ≤ 1 :=
  re_inv_det_mem hX

/-- The kernel `K = U R U*` (`R = (I + D)⁻¹` in an eigenbasis of `A`), so `Tr N = Tr(K B)`. -/
def linKer {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) * (rootRes hA * rootRes hA) *
    star (hA.eigenvectorUnitary : Matrix n n ℂ)

theorem trace_sandN {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n n ℂ) :
    (sandN hA B).trace = (linKer hA * B).trace := by
  simp only [sandN, linKer]
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  set R := rootRes hA
  rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

theorem sandN_smul {A : Matrix n n ℂ} (hA : A.IsHermitian) (c : ℂ) (B : Matrix n n ℂ) :
    sandN hA (c • B) = c • sandN hA B := by
  simp only [sandN, Matrix.mul_smul, Matrix.smul_mul]

/-- `0 ≤ Re Tr(K B) ≤ Re Tr B` for `A, B ⪰ 0`. -/
theorem linTr_mem {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (linKer hA.1 * B).trace.re ∧ (linKer hA.1 * B).trace.re ≤ B.trace.re := by
  rw [← trace_sandN]
  refine ⟨?_, re_trace_sandN_le hA hB⟩
  have := (sandN_posSemidef hA.1 hB).trace_nonneg
  rw [Complex.nonneg_iff] at this
  exact this.1

/-- `1 + Σ x_i ≤ Π (1 + x_i)` for `x ≥ 0`. -/
theorem one_add_sum_le_prod {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
    have := mul_le_mul_of_nonneg_left ih (by linarith [hx a] : (0 : ℝ) ≤ 1 + x a)
    nlinarith [hx a]

/-- **One factor**: `F(A + cB) = F(A)/D` with `1 + cτ ≤ D ≤ e^{cτ}`, `τ = Re Tr(K B)`. -/
theorem invDet_add_smul {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) : ∃ D : ℝ, 1 + c * (linKer hA.1 * B).trace.re ≤ D ∧
      D ≤ Real.exp (c * (linKer hA.1 * B).trace.re) ∧
      invDet (A + (c : ℂ) • B) = invDet A * D⁻¹ := by
  have hcB : ((c : ℂ) • B).PosSemidef := hB.smul (by exact_mod_cast hc)
  have hN := sandN_posSemidef hA.1 hcB
  have htr : (sandN hA.1 ((c : ℂ) • B)).trace.re = c * (linKer hA.1 * B).trace.re := by
    rw [sandN_smul, trace_smul, trace_sandN, smul_eq_mul, Complex.re_ofReal_mul]
  refine ⟨∏ k, (1 + hN.1.eigenvalues k), ?_, ?_, ?_⟩
  · rw [← htr, re_trace_eq_sum hN.1]
    exact one_add_sum_le_prod _ _ fun k => hN.eigenvalues_nonneg k
  · rw [← htr]; exact prod_one_add_le_exp hN
  · unfold invDet
    rw [det_one_add_add_eq hA, det_one_add_eq hA.1, det_one_add_eq hN.1, ← Complex.ofReal_mul,
      ← Complex.ofReal_inv, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re, mul_inv]

/-- `|D⁻¹ - (1 - S)| ≤ S²` for `1 + S ≤ D ≤ e^S`, `S ≥ 0`. -/
theorem abs_inv_sub_le {D S : ℝ} (hS : 0 ≤ S) (h1 : 1 + S ≤ D) (h2 : D ≤ Real.exp S) :
    |D⁻¹ - (1 - S)| ≤ S ^ 2 := by
  have hD : 0 < D := by linarith
  have hlo : 1 - S ≤ D⁻¹ := by
    have e1 : 1 - S ≤ Real.exp (-S) := by linarith [Real.add_one_le_exp (-S)]
    have e2 : Real.exp (-S) ≤ D⁻¹ := by rw [Real.exp_neg]; exact inv_anti₀ hD h2
    linarith
  have hhi : D⁻¹ ≤ 1 - S + S ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hD]
    have : 1 ≤ (1 + S) * (1 - S + S ^ 2) := by nlinarith [pow_nonneg hS 3]
    have h3 : 0 ≤ 1 - S + S ^ 2 := by nlinarith
    nlinarith
  rw [abs_le]; constructor <;> nlinarith

/-- **Second-order expansion of the product.** -/
theorem abs_prod_invDet_sub_le {ι : Type*} [Fintype ι] {Z : ι → Matrix n n ℂ}
    (hZ : ∀ j, (Z j).PosSemidef) {B : Matrix n n ℂ} (hB : B.PosSemidef) {c : ι → ℝ}
    (hc : ∀ j, 0 ≤ c j) :
    |∏ j, invDet (Z j + (c j : ℂ) • B) -
        (∏ j, invDet (Z j)) * (1 - ∑ j, c j * (linKer (hZ j).1 * B).trace.re)| ≤
      (∑ j, c j * (linKer (hZ j).1 * B).trace.re) ^ 2 := by
  choose D hD1 hD2 hD3 using fun j => invDet_add_smul (hZ j) hB (hc j)
  set τ := fun j => (linKer (hZ j).1 * B).trace.re
  have hτ : ∀ j, 0 ≤ c j * τ j := fun j => mul_nonneg (hc j) (linTr_mem (hZ j) hB).1
  set S := ∑ j, c j * τ j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => hτ j
  have hP : ∏ j, invDet (Z j + (c j : ℂ) • B) = (∏ j, invDet (Z j)) * (∏ j, D j)⁻¹ := by
    rw [Finset.prod_congr rfl fun j _ => hD3 j, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hlo : 1 + S ≤ ∏ j, D j :=
    (one_add_sum_le_prod _ _ hτ).trans
      (Finset.prod_le_prod₀ (fun j _ => by linarith [hτ j]) fun j _ => hD1 j)
  have hhi : ∏ j, D j ≤ Real.exp S := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun j _ => by linarith [hτ j, hD1 j]) fun j _ => hD2 j
  have h0 : 0 ≤ ∏ j, invDet (Z j) := Finset.prod_nonneg fun j _ => (invDet_mem (hZ j)).1.le
  have h1 : ∏ j, invDet (Z j) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => (invDet_mem (hZ j)).1.le) fun j _ => (invDet_mem (hZ j)).2
  rw [hP, ← mul_sub, abs_mul, abs_of_nonneg h0]
  calc (∏ j, invDet (Z j)) * |(∏ j, D j)⁻¹ - (1 - S)| ≤ 1 * S ^ 2 :=
        mul_le_mul h1 (abs_inv_sub_le hS hlo hhi) (abs_nonneg _) zero_le_one
    _ = S ^ 2 := one_mul _

/-- `S = Σ_j c_j Re Tr(K_j B) ≤ (Σ_j c_j) Re Tr B`. -/
theorem sum_linTr_le {ι : Type*} [Fintype ι] {Z : ι → Matrix n n ℂ}
    (hZ : ∀ j, (Z j).PosSemidef) {B : Matrix n n ℂ} (hB : B.PosSemidef) {c : ι → ℝ}
    (hc : ∀ j, 0 ≤ c j) :
    0 ≤ ∑ j, c j * (linKer (hZ j).1 * B).trace.re ∧
      ∑ j, c j * (linKer (hZ j).1 * B).trace.re ≤ (∑ j, c j) * B.trace.re := by
  refine ⟨Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (linTr_mem (hZ j) hB).1, ?_⟩
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (linTr_mem (hZ j) hB).2 (hc j)

end BlockBand.SourceProcess.Sampling
