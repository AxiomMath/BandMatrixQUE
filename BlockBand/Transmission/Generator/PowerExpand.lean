module

public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# Second-order expansion of `Tr (A + B)^k`

Matrix algebra for expanding traces about a Hermitian representative, with summable fixed
third-order remainders. For square complex matrices `A, B` (`‖·‖` the `L²` operator norm,
`frobSq B = Σ|B_ij|² = ‖B‖²_HS`), with
`pF1 A B (k+1) = Σ_{a+b=k} A^aBA^b` and `pF2 A B (k+1) = Σ_{p+c=k} pF1 A B p · B · A^c`
(the words with one, resp. two, letters `B`), and `‖A‖, ‖B‖ ≤ M`, `1 ≤ M`:
* `trace_pF1`: `Tr pF1 A B k = k Tr(A^{k-1}B)`;
* `pe_first`: `|Tr(A+B)^k - Tr A^k - k Tr(A^{k-1}B)| ≤ k(3M)^{2k} ‖B‖²_HS`;
* `pe_second`: `|Tr(A+B)^k - Tr A^k - k Tr(A^{k-1}B) - Tr pF2 A B k| ≤ k³(3M)^{2k}‖B‖‖B‖²_HS`.

The proofs bound the dual functionals `C ↦ Tr(R C)` of the remainders
(`R_{k+1} = R_k(A+B) + (lower word)·B`) and use `|Tr(XBYB)| ≤ ‖X‖‖Y‖‖B‖²_HS`
(`norm_trace_XBYB_le`). The comparison
`|Tr pF2 A B k - Tr pF2 A' B k| ≤ 3k³M^{3k}‖A - A'‖‖B‖²_HS` (also `‖A'‖ ≤ M`) is proved in the
sibling module, `pe_pF2_sub`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n]

/-!
## The Hilbert–Schmidt square
-/

/-- `‖B‖²_HS = Σ_{ij} |B_ij|²`. -/
def frobSq (B : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖B i j‖ ^ 2

theorem frobSq_nonneg (B : Matrix n n ℂ) : 0 ≤ frobSq B := by
  unfold frobSq; positivity

theorem frobSq_conjTranspose (B : Matrix n n ℂ) : frobSq Bᴴ = frobSq B := by
  unfold frobSq; rw [Finset.sum_comm]; simp [conjTranspose_apply]

theorem frobSq_eq_cols (B : Matrix n n ℂ) : frobSq B = ∑ j, vecNorm (fun i => B i j) ^ 2 := by
  unfold frobSq; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [vecNorm, Real.sq_sqrt (by positivity)]

/-- `|Tr(PQ)| ≤ ‖P‖_HS‖Q‖_HS`. -/
theorem norm_trace_mul_le (P Q : Matrix n n ℂ) :
    ‖(P * Q).trace‖ ≤ Real.sqrt (frobSq P) * Real.sqrt (frobSq Q) := by
  have e : (P * Q).trace = ∑ x : n × n, P x.1 x.2 * Q x.2 x.1 := by
    rw [Fintype.sum_prod_type]; simp [Matrix.trace, Matrix.mul_apply]
  have hP : frobSq P = ∑ x : n × n, ‖P x.1 x.2‖ ^ 2 := by rw [Fintype.sum_prod_type]; rfl
  have hQ : frobSq Q = ∑ x : n × n, ‖Q x.2 x.1‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [e, hP, hQ]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

variable [DecidableEq n]

theorem frobSq_mul_left_le (X B : Matrix n n ℂ) : frobSq (X * B) ≤ ‖X‖ ^ 2 * frobSq B := by
  rw [frobSq_eq_cols, frobSq_eq_cols, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : (fun i => (X * B) i j) = X *ᵥ (fun i => B i j) := by
    funext i; simp [Matrix.mul_apply, mulVec, dotProduct]
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ (vecNorm_nonneg _) (vecNorm_mulVec_le X _) 2

/-- **`|Tr(XBYB)| ≤ ‖X‖‖Y‖‖B‖²_HS`.** -/
theorem norm_trace_XBYB_le (X Y B : Matrix n n ℂ) :
    ‖(X * B * (Y * B)).trace‖ ≤ ‖X‖ * ‖Y‖ * frobSq B := by
  have h1 : Real.sqrt (frobSq (X * B)) ≤ ‖X‖ * Real.sqrt (frobSq B) := by
    rw [← Real.sqrt_sq (norm_nonneg X), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (frobSq_mul_left_le X B)
  have h2 : Real.sqrt (frobSq (Y * B)) ≤ ‖Y‖ * Real.sqrt (frobSq B) := by
    rw [← Real.sqrt_sq (norm_nonneg Y), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (frobSq_mul_left_le Y B)
  refine (norm_trace_mul_le _ _).trans ((mul_le_mul h1 h2 (Real.sqrt_nonneg _)
    (by positivity)).trans_eq ?_)
  have := Real.mul_self_sqrt (frobSq_nonneg B)
  calc ‖X‖ * Real.sqrt (frobSq B) * (‖Y‖ * Real.sqrt (frobSq B))
      = ‖X‖ * ‖Y‖ * (Real.sqrt (frobSq B) * Real.sqrt (frobSq B)) := by ring
    _ = _ := by rw [this]

/-!
## Words with one and two letters `B`
-/

/-- `pF1 A B (k+1) = Σ_{a+b=k} A^a B A^b` (one letter `B`). -/
def pF1 (A B : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => 0
  | k + 1 => ∑ p ∈ antidiagonal k, A ^ p.1 * B * A ^ p.2

/-- `pF2 A B (k+1) = Σ_{p+c=k} pF1 A B p · B · A^c` (two letters `B`). -/
def pF2 (A B : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => 0
  | k + 1 => ∑ p ∈ antidiagonal k, pF1 A B p.1 * B * A ^ p.2

theorem pF1_succ (A B : Matrix n n ℂ) (k : ℕ) : pF1 A B (k + 1) = pF1 A B k * A + A ^ k * B := by
  cases k with
  | zero => simp [pF1]
  | succ k =>
    rw [pF1, Finset.Nat.sum_antidiagonal_succ', pF1, Finset.sum_mul, pow_zero, Matrix.mul_one,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    show A ^ p.1 * B * A ^ (p.2 + 1) = A ^ p.1 * B * A ^ p.2 * A
    rw [pow_succ]; simp only [Matrix.mul_assoc]

theorem pF2_succ (A B : Matrix n n ℂ) (k : ℕ) : pF2 A B (k + 1) = pF2 A B k * A + pF1 A B k * B := by
  cases k with
  | zero => simp [pF2, pF1]
  | succ k =>
    rw [pF2, Finset.Nat.sum_antidiagonal_succ', pF2, Finset.sum_mul, pow_zero, Matrix.mul_one,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    show pF1 A B p.1 * B * A ^ (p.2 + 1) = pF1 A B p.1 * B * A ^ p.2 * A
    rw [pow_succ]; simp only [Matrix.mul_assoc]

theorem trace_pF1 (A B : Matrix n n ℂ) (k : ℕ) :
    (pF1 A B (k + 1)).trace = (k + 1 : ℕ) * (A ^ k * B).trace := by
  rw [pF1, Matrix.trace_sum]
  have : ∀ p ∈ antidiagonal k, (A ^ p.1 * B * A ^ p.2).trace = (A ^ k * B).trace := by
    intro p hp
    replace hp := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_add, add_comm, hp]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]

/-!
## Norm bookkeeping
-/

theorem pe_pow_le {A : Matrix n n ℂ} {M : ℝ} (hA : ‖A‖ ≤ M) (hM : 1 ≤ M) (j : ℕ) :
    ‖A ^ j‖ ≤ M ^ j := by
  induction j with
  | zero => simpa using (norm_one_matrix_le (n := n)).trans (le_refl _)
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul ih hA (norm_nonneg _) (by positivity))

theorem pe_pow_le_of_le {A : Matrix n n ℂ} {M : ℝ} (hA : ‖A‖ ≤ M) (hM : 1 ≤ M) {j k : ℕ}
    (hj : j ≤ k) : ‖A ^ j‖ ≤ M ^ k :=
  (pe_pow_le hA hM j).trans (pow_le_pow_right₀ hM hj)

theorem pe_pow_sub_le {A A' : Matrix n n ℂ} {M : ℝ} (hA : ‖A‖ ≤ M) (hA' : ‖A'‖ ≤ M) (hM : 1 ≤ M)
    (j : ℕ) : ‖A ^ j - A' ^ j‖ ≤ j * M ^ j * ‖A - A'‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : A ^ (j + 1) - A' ^ (j + 1) = (A ^ j - A' ^ j) * A + A' ^ j * (A - A') := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [e]
    have h1 := (Matrix.l2_opNorm_mul (A ^ j - A' ^ j) A).trans
      (mul_le_mul ih hA (norm_nonneg _) (by positivity))
    have h2 := (Matrix.l2_opNorm_mul (A' ^ j) (A - A')).trans
      (mul_le_mul_of_nonneg_right (pe_pow_le hA' hM j) (norm_nonneg _))
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
    have hMj : M ^ j ≤ M ^ j * M := le_mul_of_one_le_right (by positivity) hM
    have := norm_nonneg (A - A')
    push_cast
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hMj this]

/-- The `B`-single dual bound: `|Tr(pF1 A B k · B · C)| ≤ k M^{2k}‖C‖‖B‖²_HS`. -/
theorem pe_pF1_dual {A B : Matrix n n ℂ} {M : ℝ} (hA : ‖A‖ ≤ M) (hM : 1 ≤ M) (k : ℕ)
    (C : Matrix n n ℂ) :
    ‖(pF1 A B k * B * C).trace‖ ≤ k * M ^ (2 * k) * ‖C‖ * frobSq B := by
  cases k with
  | zero => simp [pF1]
  | succ k =>
    rw [pF1, Finset.sum_mul, Finset.sum_mul, Matrix.trace_sum]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ p ∈ antidiagonal k, ‖(A ^ p.1 * B * A ^ p.2 * B * C).trace‖ ≤
        M ^ (2 * (k + 1)) * ‖C‖ * frobSq B := by
      intro p hp
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have e : (A ^ p.1 * B * A ^ p.2 * B * C).trace = (C * A ^ p.1 * B * (A ^ p.2 * B)).trace := by
        rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      rw [e]
      refine (norm_trace_XBYB_le _ _ _).trans ?_
      have h1 : ‖C * A ^ p.1‖ ≤ ‖C‖ * M ^ (k + 1) := (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_left (pe_pow_le_of_le hA hM (by omega)) (norm_nonneg _))
      have h2 : ‖A ^ p.2‖ ≤ M ^ (k + 1) := pe_pow_le_of_le hA hM (by omega)
      have hf := frobSq_nonneg B
      calc ‖C * A ^ p.1‖ * ‖A ^ p.2‖ * frobSq B ≤ ‖C‖ * M ^ (k + 1) * M ^ (k + 1) * frobSq B :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) hf
        _ = _ := by rw [two_mul, pow_add]; ring
    refine (Finset.sum_le_sum hb).trans_eq ?_
    rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    push_cast; ring

/-- The remainder after the linear term (words with at least two letters `B`). -/
def peR1 (A B : Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ := (A + B) ^ k - A ^ k - pF1 A B k

/-- The remainder after the quadratic term (words with at least three letters `B`). -/
def peR3 (A B : Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ := peR1 A B k - pF2 A B k

theorem peR1_succ (A B : Matrix n n ℂ) (k : ℕ) :
    peR1 A B (k + 1) = pF1 A B k * B + peR1 A B k * (A + B) := by
  rw [peR1, peR1, pF1_succ, pow_succ, pow_succ]; noncomm_ring

theorem peR3_succ (A B : Matrix n n ℂ) (k : ℕ) :
    peR3 A B (k + 1) = peR3 A B k * (A + B) + pF2 A B k * B := by
  rw [peR3, peR3, peR1_succ, pF2_succ]; noncomm_ring

section Dual

variable {A B : Matrix n n ℂ} {M : ℝ}

theorem pe_add_mul_le (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) (C : Matrix n n ℂ) :
    ‖(A + B) * C‖ ≤ 2 * M * ‖C‖ :=
  (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _))

theorem pe_r1_dual (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) (hM : 1 ≤ M) (k : ℕ) (C : Matrix n n ℂ) :
    ‖(peR1 A B k * C).trace‖ ≤ k * (3 * M) ^ (2 * k) * ‖C‖ * frobSq B := by
  induction k generalizing C with
  | zero => simp [peR1, pF1]
  | succ k ih =>
    rw [peR1_succ, Matrix.add_mul, Matrix.trace_add, Matrix.mul_assoc (peR1 A B k)]
    have h1 := pe_pF1_dual (B := B) hA hM k C
    have h2 := (ih ((A + B) * C)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pe_add_mul_le hA hB C) (by positivity)) (frobSq_nonneg B))
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
    have hX : M ^ (2 * k) ≤ (3 * M) ^ (2 * k) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hc := mul_nonneg (norm_nonneg C) (frobSq_nonneg B)
    have hk : (0 : ℝ) ≤ k := by positivity
    have hX0 : 0 ≤ M ^ (2 * k) := by positivity
    have e : (3 * M) ^ (2 * (k + 1)) = 9 * M ^ 2 * (3 * M) ^ (2 * k) := by ring
    have key : (k : ℝ) * M ^ (2 * k) + k * (3 * M) ^ (2 * k) * (2 * M) ≤
        ((k + 1 : ℕ) : ℝ) * (3 * M) ^ (2 * (k + 1)) := by
      rw [e]; push_cast
      nlinarith [mul_le_mul_of_nonneg_left hX hk, mul_nonneg hk (by positivity :
        (0 : ℝ) ≤ (3 * M) ^ (2 * k)), mul_nonneg (mul_nonneg hk (by positivity :
        (0 : ℝ) ≤ (3 * M) ^ (2 * k))) (by nlinarith : (0 : ℝ) ≤ 9 * M ^ 2 - 2 * M - 1)]
    calc (k : ℝ) * M ^ (2 * k) * ‖C‖ * frobSq B + k * (3 * M) ^ (2 * k) * (2 * M * ‖C‖) * frobSq B
        = ((k : ℝ) * M ^ (2 * k) + k * (3 * M) ^ (2 * k) * (2 * M)) * (‖C‖ * frobSq B) := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * (3 * M) ^ (2 * (k + 1)) * (‖C‖ * frobSq B) :=
        mul_le_mul_of_nonneg_right key hc
      _ = _ := by ring

theorem pe_pF2_dual (hA : ‖A‖ ≤ M) (hM : 1 ≤ M) (k : ℕ) (C : Matrix n n ℂ) :
    ‖(pF2 A B k * C).trace‖ ≤ k ^ 2 * M ^ (2 * k) * ‖C‖ * frobSq B := by
  induction k generalizing C with
  | zero => simp [pF2]
  | succ k ih =>
    rw [pF2_succ, Matrix.add_mul, Matrix.trace_add, Matrix.mul_assoc (pF2 A B k)]
    have h1 := (ih (A * C)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul A C) (by positivity)) (frobSq_nonneg B))
    have h2 := pe_pF1_dual (B := B) hA hM k C
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
    have hc := mul_nonneg (norm_nonneg C) (frobSq_nonneg B)
    have hk : (0 : ℝ) ≤ k := by positivity
    have hX0 : 0 ≤ M ^ (2 * k) := by positivity
    have e : M ^ (2 * (k + 1)) = M ^ 2 * M ^ (2 * k) := by ring
    have hM2 : M ≤ M ^ 2 := by nlinarith
    have key : (k : ℝ) ^ 2 * M ^ (2 * k) * M + k * M ^ (2 * k) ≤
        ((k + 1 : ℕ) : ℝ) ^ 2 * M ^ (2 * (k + 1)) := by
      rw [e]; push_cast
      nlinarith [mul_le_mul_of_nonneg_left hM2 (mul_nonneg (sq_nonneg (k : ℝ)) hX0),
        mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ M ^ 2) (mul_nonneg hk hX0),
        mul_nonneg (mul_nonneg hk hX0) (by nlinarith : (0 : ℝ) ≤ M ^ 2)]
    calc (k : ℝ) ^ 2 * M ^ (2 * k) * (‖A‖ * ‖C‖) * frobSq B + k * M ^ (2 * k) * ‖C‖ * frobSq B
        ≤ (k : ℝ) ^ 2 * M ^ (2 * k) * (M * ‖C‖) * frobSq B + k * M ^ (2 * k) * ‖C‖ * frobSq B := by
          have := frobSq_nonneg B
          gcongr
      _ = ((k : ℝ) ^ 2 * M ^ (2 * k) * M + k * M ^ (2 * k)) * (‖C‖ * frobSq B) := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) ^ 2 * M ^ (2 * (k + 1)) * (‖C‖ * frobSq B) :=
        mul_le_mul_of_nonneg_right key hc
      _ = _ := by ring

theorem pe_r3_dual (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) (hM : 1 ≤ M) (k : ℕ) (C : Matrix n n ℂ) :
    ‖(peR3 A B k * C).trace‖ ≤ k ^ 3 * (3 * M) ^ (2 * k) * ‖B‖ * ‖C‖ * frobSq B := by
  induction k generalizing C with
  | zero => simp [peR3, peR1, pF1, pF2]
  | succ k ih =>
    rw [peR3_succ, Matrix.add_mul, Matrix.trace_add, Matrix.mul_assoc (peR3 A B k),
      Matrix.mul_assoc (pF2 A B k)]
    have h1 := (ih ((A + B) * C)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pe_add_mul_le hA hB C) (by positivity)) (frobSq_nonneg B))
    have h2 := (pe_pF2_dual (B := B) hA hM k (B * C)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul B C) (by positivity)) (frobSq_nonneg B))
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
    have hX : M ^ (2 * k) ≤ (3 * M) ^ (2 * k) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hc := mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg C)) (frobSq_nonneg B)
    have hk : (0 : ℝ) ≤ k := by positivity
    have hY : (0 : ℝ) ≤ (3 * M) ^ (2 * k) := by positivity
    have e : (3 * M) ^ (2 * (k + 1)) = 9 * M ^ 2 * (3 * M) ^ (2 * k) := by ring
    have key : (k : ℝ) ^ 3 * (3 * M) ^ (2 * k) * (2 * M) + k ^ 2 * M ^ (2 * k) ≤
        ((k + 1 : ℕ) : ℝ) ^ 3 * (3 * M) ^ (2 * (k + 1)) := by
      rw [e]; push_cast
      have h9 : 2 * M ≤ 9 * M ^ 2 := by nlinarith
      have h9' : 1 ≤ 9 * M ^ 2 := by nlinarith
      have hk3 : (k : ℝ) ^ 3 + k ^ 2 ≤ ((k : ℝ) + 1) ^ 3 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h9 (mul_nonneg (pow_nonneg hk 3) hY),
        mul_le_mul_of_nonneg_left hX (sq_nonneg (k : ℝ)),
        mul_le_mul_of_nonneg_left h9' (mul_nonneg (sq_nonneg (k : ℝ)) hY),
        mul_le_mul_of_nonneg_right hk3 (mul_nonneg (by positivity : (0 : ℝ) ≤ 9 * M ^ 2) hY)]
    calc (k : ℝ) ^ 3 * (3 * M) ^ (2 * k) * ‖B‖ * (2 * M * ‖C‖) * frobSq B +
          k ^ 2 * M ^ (2 * k) * (‖B‖ * ‖C‖) * frobSq B
        = ((k : ℝ) ^ 3 * (3 * M) ^ (2 * k) * (2 * M) + k ^ 2 * M ^ (2 * k)) *
            (‖B‖ * ‖C‖ * frobSq B) := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) ^ 3 * (3 * M) ^ (2 * (k + 1)) * (‖B‖ * ‖C‖ * frobSq B) :=
        mul_le_mul_of_nonneg_right key hc
      _ = _ := by ring

/-- **First-order expansion.** -/
theorem pe_first (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) (hM : 1 ≤ M) (k : ℕ) :
    ‖((A + B) ^ (k + 1)).trace - (A ^ (k + 1)).trace - (k + 1 : ℕ) * (A ^ k * B).trace‖ ≤
      (k + 1 : ℕ) * (3 * M) ^ (2 * (k + 1)) * frobSq B := by
  have h := pe_r1_dual hA hB hM (k + 1) 1
  rw [Matrix.mul_one, peR1, Matrix.trace_sub, Matrix.trace_sub, trace_pF1] at h
  refine h.trans ?_
  have := norm_one_matrix_le (n := n)
  have : 0 ≤ ((k + 1 : ℕ) : ℝ) * (3 * M) ^ (2 * (k + 1)) := by positivity
  nlinarith [frobSq_nonneg B, mul_nonneg this (frobSq_nonneg B)]

/-- **Second-order expansion.** -/
theorem pe_second (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) (hM : 1 ≤ M) (k : ℕ) :
    ‖((A + B) ^ (k + 1)).trace - (A ^ (k + 1)).trace - (k + 1 : ℕ) * (A ^ k * B).trace -
        (pF2 A B (k + 1)).trace‖ ≤
      (k + 1 : ℕ) ^ 3 * (3 * M) ^ (2 * (k + 1)) * ‖B‖ * frobSq B := by
  have h := pe_r3_dual hA hB hM (k + 1) 1
  rw [Matrix.mul_one, peR3, peR1, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    trace_pF1] at h
  refine h.trans ?_
  have := norm_one_matrix_le (n := n)
  have : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ 3 * (3 * M) ^ (2 * (k + 1)) * ‖B‖ := by positivity
  nlinarith [frobSq_nonneg B, mul_nonneg this (frobSq_nonneg B)]

end Dual

end BlockBand.Transmission.Generator
