module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# Hilbert–Schmidt bounds for cyclic words

Pure linear algebra, deterministic matrices. With `‖·‖₂` the Hilbert–Schmidt norm `hsNorm`:
* `norm_trace_mul_le`: `|Tr(AB)| ≤ ‖A‖₂‖B‖₂`; `hsNorm_mul_le`: `‖AB‖₂ ≤ ‖A‖₂‖B‖₂`;
* `norm_trace_list_prod_le`: a cyclic product of at least two factors has `|Tr| ≤ ∏‖A_i‖₂`;
* `gram_*`: a positive combination `G = Σ c_i S_iᴴS_i` has `‖G‖₂ ≤ Re Tr G` and
  `|Tr(GB)| ≤ Re Tr G` for every `B` with `‖SB‖₂ ≤ ‖S‖₂` (here `B = I` or `P`);
* `current_*`: for unitary `𝕊`, Hermitian idempotent `P` and `J = 𝕊ᴴP𝕊 - P`: `Tr J = 0`,
  `Tr JP = -½Tr J²`, `‖J‖₂² = Re Tr J²`.
The paper uses the operator norms `‖J‖, ‖P‖ ≤ 1`; we use instead that right multiplication by
`P` does not increase `‖·‖₂` (it deletes columns), which gives the same word bounds.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open Matrix
open scoped ComplexConjugate

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The Hilbert–Schmidt (Frobenius) norm `(Σ_{x,y} |A_xy|²)^{1/2}`. -/
def hsNorm {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  Real.sqrt (∑ x, ∑ y, ‖A x y‖ ^ 2)

section General

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

theorem frobenius_eq_hsNorm (A : Matrix m n ℂ) : ‖A‖ = hsNorm A := by
  rw [Matrix.frobenius_norm_def, hsNorm, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]

theorem hsNorm_nonneg (A : Matrix m n ℂ) : 0 ≤ hsNorm A := Real.sqrt_nonneg _

theorem hsNorm_sq (A : Matrix m n ℂ) : hsNorm A ^ 2 = ∑ x, ∑ y, ‖A x y‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)

theorem hsNorm_mul_le (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    hsNorm (A * B) ≤ hsNorm A * hsNorm B := by
  rw [← frobenius_eq_hsNorm, ← frobenius_eq_hsNorm, ← frobenius_eq_hsNorm]
  exact Matrix.frobenius_norm_mul A B

theorem hsNorm_conjTranspose (A : Matrix m n ℂ) : hsNorm Aᴴ = hsNorm A := by
  rw [← frobenius_eq_hsNorm, ← frobenius_eq_hsNorm, Matrix.frobenius_norm_conjTranspose]

theorem hsNorm_sum_smul_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (A : ι → Matrix m n ℂ) :
    hsNorm (∑ i ∈ s, ((c i : ℝ) : ℂ) • A i) ≤ ∑ i ∈ s, c i * hsNorm (A i) := by
  rw [← frobenius_eq_hsNorm]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
  rw [norm_smul, frobenius_eq_hsNorm, Complex.norm_real, Real.norm_of_nonneg (hc i hi)]

/-- `|Tr(AB)| ≤ ‖A‖₂‖B‖₂` (Cauchy–Schwarz). -/
theorem norm_trace_mul_le (A : Matrix n m ℂ) (B : Matrix m n ℂ) :
    ‖(A * B).trace‖ ≤ hsNorm A * hsNorm B := by
  have e : (A * B).trace = ∑ p : n × m, A p.1 p.2 * B p.2 p.1 := by
    rw [Matrix.trace, Fintype.sum_prod_type]; rfl
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans (le_of_eq ?_)
  rw [hsNorm, hsNorm, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm (s := Finset.univ)
    (t := Finset.univ) (f := fun (x : n) (y : m) => ‖B y x‖ ^ 2)]

/-- `Tr(SᴴS) = ‖S‖₂²`. -/
theorem trace_conjTranspose_mul_self (S : Matrix m n ℂ) :
    (Sᴴ * S).trace = ((hsNorm S ^ 2 : ℝ) : ℂ) := by
  rw [hsNorm_sq, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

/-- `‖SᴴSB‖`-type bound: `|Tr(SᴴSB)| ≤ ‖S‖₂²` whenever `‖SB‖₂ ≤ ‖S‖₂`. -/
theorem norm_trace_gram_mul_le (S : Matrix m n ℂ) (B : Matrix n n ℂ)
    (hB : hsNorm (S * B) ≤ hsNorm S) : ‖(Sᴴ * S * B).trace‖ ≤ hsNorm S ^ 2 := by
  rw [Matrix.mul_assoc]
  refine (norm_trace_mul_le _ _).trans ?_
  rw [hsNorm_conjTranspose, sq]
  exact mul_le_mul_of_nonneg_left hB (hsNorm_nonneg _)

/-- Right multiplication by a diagonal matrix with entries of modulus `≤ 1` does not increase
`‖·‖₂`. -/
theorem hsNorm_mul_diagonal_le [DecidableEq n] (A : Matrix m n ℂ) (d : n → ℂ)
    (hd : ∀ y, ‖d y‖ ≤ 1) : hsNorm (A * Matrix.diagonal d) ≤ hsNorm A := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_)
  rw [Matrix.mul_diagonal, norm_mul, mul_pow]
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) (hd y))

end General

section Square

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem hsNorm_list_prod_le (L : List (Matrix n n ℂ)) (hL : L ≠ []) :
    hsNorm L.prod ≤ (L.map hsNorm).prod := by
  induction L with
  | nil => exact absurd rfl hL
  | cons A L ih =>
    rcases eq_or_ne L [] with rfl | hL'
    · simp
    · rw [List.prod_cons, List.map_cons, List.prod_cons]
      exact (hsNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (ih hL') (hsNorm_nonneg _))

/-- A cyclic product of at least two factors: `|Tr(A₁⋯A_r)| ≤ ∏ ‖A_i‖₂`. -/
theorem norm_trace_list_prod_le (L : List (Matrix n n ℂ)) (hL : 2 ≤ L.length) :
    ‖L.prod.trace‖ ≤ (L.map hsNorm).prod := by
  match L, hL with
  | A :: B :: L, _ =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact (norm_trace_mul_le _ _).trans (mul_le_mul_of_nonneg_left
      (hsNorm_list_prod_le (B :: L) (List.cons_ne_nil _ _)) (hsNorm_nonneg _))

omit [DecidableEq n] in
/-- A positive Gram combination `G = Σ c_i S_iᴴS_i`: `Re Tr G = Σ c_i ‖S_i‖₂²`. -/
theorem gram_trace_re {ι k : Type*} [Fintype k] (s : Finset ι) (c : ι → ℝ) (S : ι → Matrix k n ℂ) :
    (∑ i ∈ s, ((c i : ℝ) : ℂ) • ((S i)ᴴ * S i)).trace.re = ∑ i ∈ s, c i * hsNorm (S i) ^ 2 := by
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, trace_conjTranspose_mul_self, smul_eq_mul, ← Complex.ofReal_mul,
    Complex.ofReal_re]

omit [DecidableEq n] in
theorem gram_hsNorm_le {ι k : Type*} [Fintype k] (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (S : ι → Matrix k n ℂ) :
    hsNorm (∑ i ∈ s, ((c i : ℝ) : ℂ) • ((S i)ᴴ * S i)) ≤
      (∑ i ∈ s, ((c i : ℝ) : ℂ) • ((S i)ᴴ * S i)).trace.re := by
  rw [gram_trace_re]
  refine (hsNorm_sum_smul_le s c hc _).trans (Finset.sum_le_sum fun i hi => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (hc i hi)
  calc hsNorm ((S i)ᴴ * S i) ≤ hsNorm (S i)ᴴ * hsNorm (S i) := hsNorm_mul_le _ _
    _ = hsNorm (S i) ^ 2 := by rw [hsNorm_conjTranspose, sq]

omit [DecidableEq n] in
theorem gram_trace_mul_le {ι k : Type*} [Fintype k] (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (S : ι → Matrix k n ℂ) (B : Matrix n n ℂ)
    (hB : ∀ T : Matrix k n ℂ, hsNorm (T * B) ≤ hsNorm T) :
    ‖((∑ i ∈ s, ((c i : ℝ) : ℂ) • ((S i)ᴴ * S i)) * B).trace‖ ≤
      (∑ i ∈ s, ((c i : ℝ) : ℂ) • ((S i)ᴴ * S i)).trace.re := by
  rw [gram_trace_re, Finset.sum_mul, Matrix.trace_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Matrix.smul_mul, Matrix.trace_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (hc i hi)]
  exact mul_le_mul_of_nonneg_left (norm_trace_gram_mul_le _ _ (hB _)) (hc i hi)

omit [DecidableEq n] in
theorem gram_trace_re_nonneg {ι k : Type*} [Fintype k] (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (S : ι → Matrix k n ℂ) :
    0 ≤ (∑ i ∈ s, ((c i : ℝ) : ℂ) • ((S i)ᴴ * S i)).trace.re := by
  rw [gram_trace_re]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (by positivity)

/-!
### The current `J = 𝕊ᴴP𝕊 - P`
-/

variable (S P : Matrix n n ℂ)

theorem current_trace (hS : S * Sᴴ = 1) : (Sᴴ * P * S - P).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_cycle, hS, Matrix.one_mul, sub_self]

omit [DecidableEq n] in
theorem current_isHermitian (hP : Pᴴ = P) : (Sᴴ * P * S - P)ᴴ = Sᴴ * P * S - P := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hP, Matrix.mul_assoc]

theorem current_trace_mul_proj (hS : S * Sᴴ = 1) (hPP : P * P = P) :
    ((Sᴴ * P * S - P) * P).trace = -((Sᴴ * P * S - P) ^ 2).trace / 2 := by
  set A := Sᴴ * P * S with hAdef
  have hAA : A * A = A := by
    calc A * A = Sᴴ * P * (S * Sᴴ) * P * S := by simp only [hAdef, Matrix.mul_assoc]
      _ = A := by rw [hS, Matrix.mul_one, Matrix.mul_assoc Sᴴ P P, hPP]
  have hTA : A.trace = P.trace := by rw [hAdef, Matrix.trace_mul_cycle, hS, Matrix.one_mul]
  have hPA : (P * A).trace = (A * P).trace := Matrix.trace_mul_comm _ _
  rw [sq]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, hAA, hPP, hTA, hPA]
  ring

theorem current_hsNorm_sq (hP : Pᴴ = P) :
    ((hsNorm (Sᴴ * P * S - P) ^ 2 : ℝ) : ℂ) = ((Sᴴ * P * S - P) ^ 2).trace := by
  rw [← trace_conjTranspose_mul_self, current_isHermitian S P hP, sq]

/-- `|Tr(JB)| ≤ ½‖J‖₂²` for `B = I` or `B = P`. -/
theorem current_trace_mul_le (hS : S * Sᴴ = 1) (hP : Pᴴ = P) (hPP : P * P = P) (B : Matrix n n ℂ)
    (hB : B = 1 ∨ B = P) : ‖((Sᴴ * P * S - P) * B).trace‖ ≤ hsNorm (Sᴴ * P * S - P) ^ 2 / 2 := by
  rcases hB with h | h <;> rw [h]
  · rw [Matrix.mul_one, current_trace S P hS, norm_zero]; positivity
  · rw [current_trace_mul_proj S P hS hPP, ← current_hsNorm_sq S P hP, norm_div, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    norm_num

end Square

end BlockBand.SourceProcess.FullSourceStops
