module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Hilbert–Schmidt estimates for the dilation variance

Finite matrices over `ℂ`, Euclidean operator norm `‖·‖` (`Matrix.Norms.L2Operator`) and the
Hilbert–Schmidt (Frobenius) norm `hsNorm A = (∑ᵢⱼ |Aᵢⱼ|²)^{1/2}`, realized as the Euclidean
norm of the flattened matrix so that the triangle inequality is Mathlib's.

* `hsNorm_mul_left_le`, `hsNorm_mul_right_le`: `‖AB‖_HS ≤ ‖A‖ ‖B‖_HS`, `‖AB‖_HS ≤ ‖A‖_HS ‖B‖`;
* `hsNorm_pow_sub_pow_le`: if `‖A‖, ‖B‖ ≤ c` then `‖A^k - B^k‖_HS ≤ k c^{k-1} ‖A - B‖_HS`
  (telescoping);
* `norm_trace_mul_sq_le`: `|Tr DA|² ≤ (card ι) ‖D‖² ‖A‖²_HS` (trace Cauchy–Schwarz);
* `hsSq_eq_sum_re_diag`: `‖A‖²_HS = ∑ⱼ Re (AᴴA)ⱼⱼ = Re Tr AᴴA`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace BlockBand.Critical.Collar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared Hilbert–Schmidt norm `∑ᵢ ∑ⱼ |Aᵢⱼ|²`. -/
def hsSq (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- The flattened matrix as a Euclidean vector indexed by `ι × ι`. -/
def hsVec (A : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 (fun p : ι × ι => A p.1 p.2)

/-- Hilbert–Schmidt norm. -/
def hsNorm (A : Matrix ι ι ℂ) : ℝ := ‖hsVec A‖

theorem hsNorm_nonneg (A : Matrix ι ι ℂ) : 0 ≤ hsNorm A := norm_nonneg _

theorem hsSq_nonneg (A : Matrix ι ι ℂ) : 0 ≤ hsSq A := by
  unfold hsSq
  positivity

theorem hsNorm_sq (A : Matrix ι ι ℂ) : hsNorm A ^ 2 = hsSq A := by
  rw [hsNorm, EuclideanSpace.norm_sq_eq, hsSq, Fintype.sum_prod_type]
  rfl

theorem hsNorm_eq_sqrt (A : Matrix ι ι ℂ) : hsNorm A = Real.sqrt (hsSq A) := by
  rw [← hsNorm_sq, Real.sqrt_sq (hsNorm_nonneg A)]

theorem hsNorm_add_le (A B : Matrix ι ι ℂ) : hsNorm (A + B) ≤ hsNorm A + hsNorm B := by
  have : hsVec (A + B) = hsVec A + hsVec B := rfl
  rw [hsNorm, this]
  exact norm_add_le _ _

theorem hsNorm_zero : hsNorm (0 : Matrix ι ι ℂ) = 0 := by
  rw [hsNorm_eq_sqrt]
  simp [hsSq]

theorem hsSq_conjTranspose (A : Matrix ι ι ℂ) : hsSq Aᴴ = hsSq A := by
  simp only [hsSq, conjTranspose_apply, norm_star]
  exact Finset.sum_comm

theorem hsNorm_conjTranspose (A : Matrix ι ι ℂ) : hsNorm Aᴴ = hsNorm A := by
  rw [hsNorm_eq_sqrt, hsNorm_eq_sqrt, hsSq_conjTranspose]

/-- Column decomposition of `hsSq`. -/
theorem hsSq_eq_sum_col (A : Matrix ι ι ℂ) :
    hsSq A = ∑ j, ‖(EuclideanSpace.equiv ι ℂ).symm (fun i => A i j)‖ ^ 2 := by
  rw [hsSq, Finset.sum_comm]
  congr 1
  funext j
  rw [EuclideanSpace.norm_sq_eq]
  rfl

theorem hsSq_mul_left_le (A B : Matrix ι ι ℂ) : hsSq (A * B) ≤ ‖A‖ ^ 2 * hsSq B := by
  rw [hsSq_eq_sum_col, hsSq_eq_sum_col, Finset.mul_sum]
  gcongr with j
  have hcol : (fun i => (A * B) i j) =
      A *ᵥ ((EuclideanSpace.equiv ι ℂ).symm (fun i => B i j)) := by
    funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hcol]
  have h := Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv ι ℂ).symm (fun i => B i j))
  calc ‖(EuclideanSpace.equiv ι ℂ).symm
          (A *ᵥ ((EuclideanSpace.equiv ι ℂ).symm (fun i => B i j)))‖ ^ 2
      ≤ (‖A‖ * ‖(EuclideanSpace.equiv ι ℂ).symm (fun i => B i j)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ‖A‖ ^ 2 * ‖(EuclideanSpace.equiv ι ℂ).symm (fun i => B i j)‖ ^ 2 := by ring

theorem hsNorm_mul_left_le (A B : Matrix ι ι ℂ) : hsNorm (A * B) ≤ ‖A‖ * hsNorm B := by
  have h := hsSq_mul_left_le A B
  rw [← hsNorm_sq, ← hsNorm_sq, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (hsNorm_nonneg _)
    (mul_nonneg (norm_nonneg _) (hsNorm_nonneg _)) two_ne_zero).mp h

theorem hsNorm_mul_right_le (A B : Matrix ι ι ℂ) : hsNorm (A * B) ≤ hsNorm A * ‖B‖ := by
  rw [← hsNorm_conjTranspose, conjTranspose_mul, ← hsNorm_conjTranspose A,
    ← Matrix.l2_opNorm_conjTranspose B, mul_comm]
  exact hsNorm_mul_left_le _ _

theorem hsNorm_mul_pow_le (X B : Matrix ι ι ℂ) {c : ℝ} (hc : 0 ≤ c) (hB : ‖B‖ ≤ c)
    (k : ℕ) : hsNorm (X * B ^ k) ≤ hsNorm X * c ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mul_assoc, pow_succ]
    calc hsNorm (X * B ^ k * B) ≤ hsNorm (X * B ^ k) * ‖B‖ := hsNorm_mul_right_le _ _
      _ ≤ (hsNorm X * c ^ k) * c :=
        mul_le_mul ih hB (norm_nonneg _) (mul_nonneg (hsNorm_nonneg _) (pow_nonneg hc _))
      _ = hsNorm X * (c ^ k * c) := by ring

/-- Telescoping bound `‖A^k - B^k‖_HS ≤ k c^{k-1} ‖A - B‖_HS` when `‖A‖, ‖B‖ ≤ c`
(Euclidean operator norms). -/
theorem hsNorm_pow_sub_pow_le (A B : Matrix ι ι ℂ) {c : ℝ} (hc : 0 ≤ c) (hA : ‖A‖ ≤ c)
    (hB : ‖B‖ ≤ c) (k : ℕ) :
    hsNorm (A ^ k - B ^ k) ≤ k * c ^ (k - 1) * hsNorm (A - B) := by
  induction k with
  | zero => simp [hsNorm_zero]
  | succ k ih =>
    have hdec : A ^ (k + 1) - B ^ (k + 1) = A * (A ^ k - B ^ k) + (A - B) * B ^ k := by
      rw [pow_succ', pow_succ', Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [hdec]
    have h1 : hsNorm (A * (A ^ k - B ^ k)) ≤ c * (k * c ^ (k - 1) * hsNorm (A - B)) :=
      (hsNorm_mul_left_le _ _).trans
        (mul_le_mul hA ih (hsNorm_nonneg _) hc)
    have h2 := hsNorm_mul_pow_le (A - B) B hc hB k
    calc hsNorm (A * (A ^ k - B ^ k) + (A - B) * B ^ k)
        ≤ hsNorm (A * (A ^ k - B ^ k)) + hsNorm ((A - B) * B ^ k) := hsNorm_add_le _ _
      _ ≤ c * (k * c ^ (k - 1) * hsNorm (A - B)) + hsNorm (A - B) * c ^ k := add_le_add h1 h2
      _ = ((k + 1 : ℕ) : ℝ) * c ^ (k + 1 - 1) * hsNorm (A - B) := by
        rcases k with _ | k
        · simp
        · simp only [Nat.add_sub_cancel]
          push_cast
          ring

/-- Trace Cauchy–Schwarz with the operator norm: `|Tr DA|² ≤ (card ι) ‖D‖² ‖A‖²_HS`. -/
theorem norm_trace_mul_sq_le (D A : Matrix ι ι ℂ) :
    ‖trace (D * A)‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ‖D‖ ^ 2 * hsSq A := by
  have h1 : ‖trace (D * A)‖ ≤ ∑ i, ‖(D * A) i i‖ := by
    rw [trace]
    exact norm_sum_le _ _
  have h2 : (∑ i, ‖(D * A) i i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖(D * A) i i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖(D * A) i i‖)
  have h3 : ∑ i, ‖(D * A) i i‖ ^ 2 ≤ hsSq (D * A) := by
    rw [hsSq]
    gcongr with i
    exact Finset.single_le_sum (f := fun j => ‖(D * A) i j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have h4 := hsSq_mul_left_le D A
  calc ‖trace (D * A)‖ ^ 2 ≤ (∑ i, ‖(D * A) i i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, ‖(D * A) i i‖ ^ 2 := h2
    _ ≤ (Fintype.card ι : ℝ) * hsSq (D * A) := by gcongr
    _ ≤ (Fintype.card ι : ℝ) * (‖D‖ ^ 2 * hsSq A) := by gcongr
    _ = (Fintype.card ι : ℝ) * ‖D‖ ^ 2 * hsSq A := by ring

/-- `‖A‖²_HS = Re Tr AᴴA`, written as a sum of diagonal entries. -/
theorem hsSq_eq_sum_re_diag (A : Matrix ι ι ℂ) :
    hsSq A = ∑ j, ((Aᴴ * A) j j).re := by
  rw [hsSq, Finset.sum_comm]
  congr 1
  funext j
  rw [Matrix.mul_apply, Complex.re_sum]
  congr 1
  funext i
  rw [conjTranspose_apply, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re]

end BlockBand.Critical.Collar
