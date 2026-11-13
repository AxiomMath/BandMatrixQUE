module

public import BlockBand.Transmission.Generator.PowerExpand
public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The quadratic term about a diagonal representative

* `pe_pF2_sub`: `|Tr pF2 A B (k+1) - Tr pF2 A' B (k+1)| ≤ 3k(k+1)²M^{3k}‖A - A'‖‖B‖²_HS`
  (replace the mean representative by its diagonal part);
* `trace_pF2_diag`: for `A = diag(d)`,
  `Tr pF2 A B (j+2) = Σ_{im} B_im B_mi wsum j d_i d_m`, `wsum j x y = Σ_{a+b=j}(a+1)x^ay^b`;
* `pd_drift`: for real `t` and `P_m = Σ_i t_i^m`,
  `-(D(j+2)/2)P₁P_{j+2} + (D/2)Σ_{im} t_it_m(2 - t_i - t_m) wsum j t_i t_m = A_{j+2}(P)`
  (`transmissionDrift`), i.e. the eigenbasis tensor `½D₀t_it_m(2 - t_i - t_m)` contracted with
  the second differential of `Tr T^k`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder Matrix.Norms.L2Operator

/-!
## Scalar sums over the antidiagonal
-/

/-- `hsum j x y = Σ_{a+b=j} x^a y^b`. -/
def hsum {R : Type*} [CommSemiring R] (j : ℕ) (x y : R) : R :=
  ∑ p ∈ antidiagonal j, x ^ p.1 * y ^ p.2

/-- `wsum j x y = Σ_{a+b=j} (a+1) x^a y^b`. -/
def wsum {R : Type*} [CommSemiring R] (j : ℕ) (x y : R) : R :=
  ∑ p ∈ antidiagonal j, ((p.1 + 1 : ℕ) : R) * x ^ p.1 * y ^ p.2

section Scalar

variable {R : Type*} [CommSemiring R]

theorem hsum_succ (j : ℕ) (x y : R) : hsum (j + 1) x y = y ^ (j + 1) + x * hsum j x y := by
  rw [hsum, Finset.Nat.sum_antidiagonal_succ, hsum, Finset.mul_sum]
  simp only [pow_zero, one_mul, pow_succ]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem wsum_succ (j : ℕ) (x y : R) :
    wsum (j + 1) x y = y ^ (j + 1) + x * wsum j x y + x * hsum j x y := by
  rw [wsum, Finset.Nat.sum_antidiagonal_succ, wsum, hsum, Finset.mul_sum, Finset.mul_sum,
    add_assoc, ← Finset.sum_add_distrib]
  simp only [pow_zero, one_mul, zero_add, Nat.cast_one]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  push_cast
  ring

/-- `Σ_{a'+c=j} x^c hsum a' x y = wsum j x y`. -/
theorem sum_pow_hsum (j : ℕ) (x y : R) :
    ∑ p ∈ antidiagonal j, x ^ p.2 * hsum p.1 x y = wsum j x y := by
  induction j with
  | zero => simp [hsum, wsum]
  | succ j ih =>
    rw [Finset.Nat.sum_antidiagonal_succ', wsum_succ, hsum_succ, ← ih, Finset.mul_sum]
    dsimp only
    have h : ∑ p ∈ antidiagonal j, x ^ (p.2 + 1) * hsum p.1 x y =
        ∑ p ∈ antidiagonal j, x * (x ^ p.2 * hsum p.1 x y) :=
      Finset.sum_congr rfl fun p _ => by ring
    rw [h, pow_zero, one_mul]; ring

theorem wsum_add_swap (j : ℕ) (x y : R) :
    wsum j x y + wsum j y x = ((j + 2 : ℕ) : R) * hsum j x y := by
  have e : wsum j y x = ∑ p ∈ antidiagonal j, ((p.2 + 1 : ℕ) : R) * x ^ p.1 * y ^ p.2 := by
    have h := Finset.Nat.sum_antidiagonal_swap (n := j)
      (f := fun p : ℕ × ℕ => ((p.2 + 1 : ℕ) : R) * x ^ p.1 * y ^ p.2)
    rw [← h, wsum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]; ring
  rw [e, wsum, hsum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have : ((p.1 + 1 : ℕ) : R) + ((p.2 + 1 : ℕ) : R) = ((j + 2 : ℕ) : R) := by
    rw [← Nat.cast_add]; congr 1; omega
  rw [← this]; ring

end Scalar

theorem hsum_ofReal (j : ℕ) (x y : ℝ) : ((hsum j x y : ℝ) : ℂ) = hsum j (x : ℂ) (y : ℂ) := by
  simp [hsum]

theorem wsum_ofReal (j : ℕ) (x y : ℝ) : ((wsum j x y : ℝ) : ℂ) = wsum j (x : ℂ) (y : ℂ) := by
  simp [wsum]

/-!
## The diagonal evaluation
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem pF1_diag_apply (d : n → ℂ) (B : Matrix n n ℂ) (k : ℕ) (i l : n) :
    pF1 (diagonal d) B (k + 1) i l = B i l * hsum k (d i) (d l) := by
  rw [pF1, Matrix.sum_apply, hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [diagonal_pow, diagonal_pow, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.pow_apply]; ring

theorem trace_mul_diag (X B : Matrix n n ℂ) (e : n → ℂ) :
    (X * B * diagonal e).trace = ∑ i, ∑ m, X i m * B m i * e i := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Finset.sum_mul]

/-- **The quadratic term at a diagonal representative.** -/
theorem trace_pF2_diag (d : n → ℂ) (B : Matrix n n ℂ) (j : ℕ) :
    (pF2 (diagonal d) B (j + 2)).trace = ∑ i, ∑ m, B i m * B m i * wsum j (d i) (d m) := by
  rw [pF2, Finset.Nat.sum_antidiagonal_succ]
  show (pF1 (diagonal d) B 0 * B * diagonal d ^ (j + 1) +
    ∑ p ∈ antidiagonal j, pF1 (diagonal d) B (p.1 + 1) * B * diagonal d ^ p.2).trace = _
  rw [Matrix.trace_add, show pF1 (diagonal d) B 0 = 0 from rfl, Matrix.zero_mul, Matrix.zero_mul,
    Matrix.trace_zero, zero_add, Matrix.trace_sum]
  have h : ∀ p ∈ antidiagonal j, (pF1 (diagonal d) B (p.1 + 1) * B * diagonal d ^ p.2).trace =
      ∑ i, ∑ m, B i m * B m i * (d i ^ p.2 * hsum p.1 (d i) (d m)) := by
    intro p _
    rw [diagonal_pow, trace_mul_diag]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    rw [pF1_diag_apply]; simp only [Pi.pow_apply]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.mul_sum, sum_pow_hsum]

/-!
## Replacing the representative
-/

section Sub

variable {A A' B : Matrix n n ℂ} {M : ℝ}

theorem pe_pow_sub_le_of_le (hA : ‖A‖ ≤ M) (hA' : ‖A'‖ ≤ M) (hM : 1 ≤ M) {j k : ℕ} (hj : j ≤ k) :
    ‖A ^ j - A' ^ j‖ ≤ k * M ^ k * ‖A - A'‖ :=
  (pe_pow_sub_le hA hA' hM j).trans (mul_le_mul_of_nonneg_right (mul_le_mul
    (by exact_mod_cast hj) (pow_le_pow_right₀ hM hj) (by positivity) (by positivity))
    (norm_nonneg _))

theorem pe_word_sub (hA : ‖A‖ ≤ M) (hA' : ‖A'‖ ≤ M) (hM : 1 ≤ M) {a b c k : ℕ} (ha : a ≤ k)
    (hb : b ≤ k) (hc : c ≤ k) :
    ‖(A ^ a * B * A ^ b * B * A ^ c).trace - (A' ^ a * B * A' ^ b * B * A' ^ c).trace‖ ≤
      3 * k * M ^ (3 * k) * ‖A - A'‖ * frobSq B := by
  have e1 : ∀ Z : Matrix n n ℂ, (Z ^ a * B * Z ^ b * B * Z ^ c).trace =
      (Z ^ c * Z ^ a * B * (Z ^ b * B)).trace := fun Z => by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [e1, e1]
  set X := A ^ c * A ^ a
  set X' := A' ^ c * A' ^ a
  have e2 : (X * B * (A ^ b * B)).trace - (X' * B * (A' ^ b * B)).trace =
      ((X - X') * B * (A ^ b * B)).trace + (X' * B * ((A ^ b - A' ^ b) * B)).trace := by
    rw [← Matrix.trace_sub, ← Matrix.trace_add]; congr 1; noncomm_ring
  rw [e2]
  set d := ‖A - A'‖
  set m := M ^ k
  have hm : 1 ≤ m := one_le_pow₀ hM
  have hd : 0 ≤ d := norm_nonneg _
  have hk : (0 : ℝ) ≤ k := by positivity
  have hX : ‖X - X'‖ ≤ 2 * k * m * m * d := by
    have e : X - X' = (A ^ c - A' ^ c) * A ^ a + A' ^ c * (A ^ a - A' ^ a) := by noncomm_ring
    rw [e]
    have h1 := (Matrix.l2_opNorm_mul (A ^ c - A' ^ c) (A ^ a)).trans (mul_le_mul
      (pe_pow_sub_le_of_le hA hA' hM hc) (pe_pow_le_of_le hA hM ha) (norm_nonneg _)
      (by positivity))
    have h2 := (Matrix.l2_opNorm_mul (A' ^ c) (A ^ a - A' ^ a)).trans (mul_le_mul
      (pe_pow_le_of_le hA' hM hc) (pe_pow_sub_le_of_le hA hA' hM ha) (norm_nonneg _)
      (by positivity))
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
    ring
  have hX' : ‖X'‖ ≤ m * m := (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul
    (pe_pow_le_of_le hA' hM hc) (pe_pow_le_of_le hA' hM ha) (norm_nonneg _) (by positivity))
  have hY : ‖A ^ b‖ ≤ m := pe_pow_le_of_le hA hM hb
  have hY' := pe_pow_sub_le_of_le hA hA' hM hb
  have hf := frobSq_nonneg B
  have t1 := (norm_trace_XBYB_le (X - X') (A ^ b) B).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hX hY (norm_nonneg _) (by positivity)) hf)
  have t2 := (norm_trace_XBYB_le X' (A ^ b - A' ^ b) B).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hX' hY' (norm_nonneg _) (by positivity)) hf)
  refine (norm_add_le _ _).trans ((add_le_add t1 t2).trans_eq ?_)
  have : M ^ (3 * k) = m * m * m := by rw [show 3 * k = k + k + k by ring, pow_add, pow_add]
  rw [this]; ring

/-- **Changing the representative in the quadratic term.** -/
theorem pe_pF2_sub (hA : ‖A‖ ≤ M) (hA' : ‖A'‖ ≤ M) (hM : 1 ≤ M) (k : ℕ) :
    ‖(pF2 A B (k + 1)).trace - (pF2 A' B (k + 1)).trace‖ ≤
      (k + 1 : ℕ) * ((k + 1 : ℕ) * (3 * k * M ^ (3 * k) * ‖A - A'‖ * frobSq B)) := by
  set w := 3 * k * M ^ (3 * k) * ‖A - A'‖ * frobSq B
  have hw : 0 ≤ w := by have := frobSq_nonneg B; have := norm_nonneg (A - A'); positivity
  rw [pF2, pF2, Matrix.trace_sum, Matrix.trace_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ p ∈ antidiagonal k, ‖(pF1 A B p.1 * B * A ^ p.2).trace -
      (pF1 A' B p.1 * B * A' ^ p.2).trace‖ ≤ (k + 1 : ℕ) * w := by
    rintro ⟨_ | a', c⟩ hp
    · simp only [pF1, Matrix.zero_mul, Matrix.trace_zero, sub_zero, norm_zero]; positivity
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    simp only at hp' ⊢
    rw [pF1, pF1, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
      Matrix.trace_sum, Matrix.trace_sum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hq : ∀ q ∈ antidiagonal a', ‖(A ^ q.1 * B * A ^ q.2 * B * A ^ c).trace -
        (A' ^ q.1 * B * A' ^ q.2 * B * A' ^ c).trace‖ ≤ w := by
      intro q hq
      have hq' := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      exact pe_word_sub hA hA' hM (by omega) (by omega) (by omega)
    refine (Finset.sum_le_sum hq).trans ?_
    rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : a' + 1 ≤ k + 1)) hw
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]

end Sub

/-!
## Contraction with the eigenbasis tensor
-/

/-- Power sums `P_m = Σ_i t_i^m`. -/
def powSums {n : Type*} [Fintype n] (t : n → ℝ) : ℕ → ℝ := fun m => ∑ i, t i ^ m

omit [DecidableEq n] in
theorem pd_symm (t : n → ℝ) (w : n → n → ℝ) (hw : ∀ i m, w i m = w m i) (j : ℕ) :
    2 * ∑ i, ∑ m, w i m * wsum j (t i) (t m) =
      ((j + 2 : ℕ) : ℝ) * ∑ i, ∑ m, w i m * hsum j (t i) (t m) := by
  have e : ∑ i, ∑ m, w i m * wsum j (t i) (t m) = ∑ i, ∑ m, w i m * wsum j (t m) (t i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by rw [hw]
  rw [two_mul]
  nth_rewrite 2 [e]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_add, wsum_add_swap]; ring

omit [DecidableEq n] in
theorem pd_hsum (t : n → ℝ) (j : ℕ) :
    ∑ i, ∑ m, t i * t m * (2 - t i - t m) * hsum j (t i) (t m) =
      2 * ∑ p ∈ antidiagonal j, (powSums t (p.1 + 1) * powSums t (p.2 + 1) -
        powSums t (p.1 + 2) * powSums t (p.2 + 1)) := by
  have e1 : ∀ p : ℕ × ℕ, ∑ i, ∑ m, t i * t m * (2 - t i - t m) * (t i ^ p.1 * t m ^ p.2) =
      2 * (powSums t (p.1 + 1) * powSums t (p.2 + 1)) -
        powSums t (p.1 + 2) * powSums t (p.2 + 1) - powSums t (p.1 + 1) * powSums t (p.2 + 2) := by
    intro p
    simp only [powSums]
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have e2 : ∑ p ∈ antidiagonal j, powSums t (p.1 + 1) * powSums t (p.2 + 2) =
      ∑ p ∈ antidiagonal j, powSums t (p.1 + 2) * powSums t (p.2 + 1) := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
    exact Finset.sum_congr rfl fun p _ => by simp only [Prod.fst_swap, Prod.snd_swap]; ring
  have e3 : ∑ i, ∑ m, t i * t m * (2 - t i - t m) * hsum j (t i) (t m) =
      ∑ p ∈ antidiagonal j, ∑ i, ∑ m, t i * t m * (2 - t i - t m) * (t i ^ p.1 * t m ^ p.2) := by
    simp only [hsum, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [e3, Finset.sum_congr rfl fun p _ => e1 p, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    e2, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem pd_ico (P : ℕ → ℝ) (j : ℕ) :
    ∑ l ∈ Finset.Ico 1 (j + 2), (P l * P (j + 2 - l) - P (l + 1) * P (j + 2 - l)) =
      ∑ p ∈ antidiagonal j, (P (p.1 + 1) * P (p.2 + 1) - P (p.1 + 2) * P (p.2 + 1)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_Ico_eq_sum_range]
  have : j + 2 - 1 = j + 1 := by omega
  rw [this]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have e : j + 2 - (1 + i) = j - i + 1 := by omega
  rw [e, add_comm 1 i]

omit [DecidableEq n] in
/-- **The drift coefficient from the eigenbasis tensor.** -/
theorem pd_drift (D : ℝ) (t : n → ℝ) (j : ℕ) :
    -(D * ((j + 2 : ℕ) : ℝ) / 2) * powSums t 1 * powSums t (j + 2) +
        D / 2 * ∑ i, ∑ m, t i * t m * (2 - t i - t m) * wsum j (t i) (t m) =
      transmissionDrift D (j + 2) (powSums t) := by
  have hs := pd_symm t (fun i m => t i * t m * (2 - t i - t m)) (fun i m => by ring) j
  rw [pd_hsum] at hs
  rw [transmissionDrift, pd_ico]
  have : ∑ i, ∑ m, t i * t m * (2 - t i - t m) * wsum j (t i) (t m) =
      ((j + 2 : ℕ) : ℝ) * ∑ p ∈ antidiagonal j, (powSums t (p.1 + 1) * powSums t (p.2 + 1) -
        powSums t (p.1 + 2) * powSums t (p.2 + 1)) := by linarith
  rw [this]; ring

end BlockBand.Transmission.Generator
