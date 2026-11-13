module

public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# Deterministic trace algebra for the full-source moments

A positive source is carried with an explicit factor, `Y = S*S` (a tag is
`Y_{j;k} = (P_k𝒰_j)*(P_k𝒰_j)`). With the conjugated rows `v_x = conj(S_{x·})`:
* `trace_factor_mul`: `Tr(S*S M) = Σ_x v_x* M v_x`;
* `sum_vecNorm_rowv`: `Σ_x ‖v_x‖² = Re Tr(S*S)`, and `Tr(S*S)` is real and `≥ 0`;
* `norm_trace_factor_le`: `|Tr(S*S M)| ≤ ‖M‖ Re Tr(S*S)` (operator norm);
* `pow_add_le`: `(t+y)^n ≤ t^n + n t^{n-1}y + 2^n(t^{n-2}y² + |y|^n)` for `t ≥ 0`, `n ≥ 2`
  (the binomial step: the linear term `n t^{n-1}y` is kept, and it has zero mean when `y` is a
  centered increment).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

section Factor

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The conjugated row `v_x(c) = conj S_{xc}`. -/
def rowv (S : Matrix m n ℂ) (x : m) : n → ℂ := fun c => star (S x c)

/-- `Tr(S*S M) = Σ_x v_x* M v_x`. -/
theorem trace_factor_mul (S : Matrix m n ℂ) (M : Matrix n n ℂ) :
    (Sᴴ * S * M).trace = ∑ x, bilinear (rowv S x) M (rowv S x) := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, bilinear,
    dotProduct, mulVec, rowv, Pi.star_apply, star_star, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem trace_factor_eq (S : Matrix m n ℂ) :
    (Sᴴ * S).trace = ∑ x, ((vecNorm (rowv S x) ^ 2 : ℝ) : ℂ) := by
  classical
  have h := trace_factor_mul S 1
  rw [Matrix.mul_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [bilinear, Matrix.one_mulVec, star_self_eq]

/-- `Σ_x ‖v_x‖² = Re Tr(S*S)`. -/
theorem sum_vecNorm_rowv (S : Matrix m n ℂ) :
    ∑ x, vecNorm (rowv S x) ^ 2 = (Sᴴ * S).trace.re := by
  rw [trace_factor_eq, Complex.re_sum]
  simp only [Complex.ofReal_re]

theorem trace_factor_im (S : Matrix m n ℂ) : (Sᴴ * S).trace.im = 0 := by
  rw [trace_factor_eq, Complex.im_sum]
  simp only [Complex.ofReal_im, Finset.sum_const_zero]

theorem trace_factor_re_nonneg (S : Matrix m n ℂ) : 0 ≤ (Sᴴ * S).trace.re := by
  rw [← sum_vecNorm_rowv]; positivity

theorem trace_factor_eq_re (S : Matrix m n ℂ) : (Sᴴ * S).trace = (((Sᴴ * S).trace.re : ℝ) : ℂ) :=
  Complex.ext rfl (by simp [trace_factor_im])

/-- `|Tr(S*S M)| ≤ ‖M‖ Re Tr(S*S)`. -/
theorem norm_trace_factor_le [DecidableEq n] (S : Matrix m n ℂ) (M : Matrix n n ℂ) :
    ‖(Sᴴ * S * M).trace‖ ≤ ‖M‖ * (Sᴴ * S).trace.re := by
  rw [trace_factor_mul, ← sum_vecNorm_rowv, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  have := norm_bilinear_le (rowv S x) M (rowv S x)
  nlinarith [vecNorm_nonneg (rowv S x)]

/-- Transport of a factored source: `(SN)*(SN) = N*(S*S)N`, and
`Tr((SN)*(SN)) = Tr(S*S) + Tr(S*S(NN* - I))`. -/
theorem trace_transport [DecidableEq n] (S : Matrix m n ℂ) (N : Matrix n n ℂ) :
    ((S * N)ᴴ * (S * N)).trace = (Sᴴ * S).trace + (Sᴴ * S * (N * Nᴴ - 1)).trace := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, add_sub_cancel,
    Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc]

end Factor

/-!
## The binomial step
-/

theorem mul_pow_le_of_two {t y : ℝ} (ht : 0 ≤ t) {a k : ℕ} (hak : a ≤ k) :
    t ^ a * |y| ^ (k + 2 - a) ≤ t ^ k * y ^ 2 + |y| ^ (k + 2) := by
  have hy := abs_nonneg y
  have hk2 : k + 2 - a = (k - a) + 2 := by omega
  rcases le_total |y| t with h | h
  · have h1 : t ^ a * |y| ^ (k - a) ≤ t ^ a * t ^ (k - a) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy h _) (pow_nonneg ht _)
    rw [← pow_add, Nat.add_sub_cancel' hak] at h1
    have h2 : t ^ a * |y| ^ (k + 2 - a) = t ^ a * |y| ^ (k - a) * y ^ 2 := by
      rw [hk2, pow_add, ← sq_abs y]; ring
    rw [h2]
    have := sq_nonneg y
    nlinarith [pow_nonneg hy (k + 2)]
  · have h1 : t ^ a ≤ |y| ^ a := pow_le_pow_left₀ ht h _
    have h2 : t ^ a * |y| ^ (k + 2 - a) ≤ |y| ^ a * |y| ^ (k + 2 - a) :=
      mul_le_mul_of_nonneg_right h1 (pow_nonneg hy _)
    rw [← pow_add, Nat.add_sub_cancel' (by omega)] at h2
    have := mul_nonneg (pow_nonneg ht k) (sq_nonneg y)
    linarith

/-- **The binomial step**: for `t ≥ 0`, `n ≥ 2`,
`(t+y)^n ≤ t^n + n t^{n-1} y + 2^n (t^{n-2} y² + |y|^n)`. -/
theorem pow_add_le {t : ℝ} (ht : 0 ≤ t) (y : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    (t + y) ^ n ≤ t ^ n + n * t ^ (n - 1) * y + 2 ^ n * (t ^ (n - 2) * y ^ 2 + |y| ^ n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one, Nat.choose_self,
    Nat.cast_one, show k + 2 - (k + 1) = 1 by omega, pow_one,
    show k + 2 - 1 = k + 1 by omega]
  have hsum : ∑ a ∈ Finset.range (k + 1), t ^ a * y ^ (k + 2 - a) * ((k + 2).choose a : ℝ) ≤
      ∑ a ∈ Finset.range (k + 1), ((k + 2).choose a : ℝ) * (t ^ k * y ^ 2 + |y| ^ (k + 2)) := by
    refine Finset.sum_le_sum fun a ha => ?_
    have hak : a ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have h1 : t ^ a * y ^ (k + 2 - a) ≤ t ^ a * |y| ^ (k + 2 - a) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_pow y _).le) (pow_nonneg ht _)
    have h2 := mul_pow_le_of_two (y := y) ht hak
    have h3 : (0 : ℝ) ≤ (k + 2).choose a := Nat.cast_nonneg _
    nlinarith
  have hch : ∑ a ∈ Finset.range (k + 1), ((k + 2).choose a : ℝ) ≤ 2 ^ (k + 2) := by
    have h := Nat.sum_range_choose (k + 2)
    have : ∑ a ∈ Finset.range (k + 1), (k + 2).choose a ≤ 2 ^ (k + 2) := by
      rw [← h]
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
    exact_mod_cast this
  rw [← Finset.sum_mul] at hsum
  rw [Nat.choose_succ_self_right]
  have hB : 0 ≤ t ^ k * y ^ 2 + |y| ^ (k + 2) := by positivity
  have := mul_le_mul_of_nonneg_right hch hB
  push_cast
  nlinarith

end BlockBand.SourceProcess.FullSource
