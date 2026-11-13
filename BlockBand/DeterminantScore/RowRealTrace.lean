module

public import BlockBand.DeterminantScore.HorizontalVariation

/-!
# Real traces and the signed row square

Traces and quadratic forms of Hermitian matrices are real, and for a Hermitian minor inverse `C`,
a real `δ` and a variance `t > 0`, the signed cubic and quartic terms of the row restoration are the
trace of a complete negative matrix square (`signed_row_matrix_square_identity`), which gives the
variance-normalized bound `signed_row_matrix_square_le`. Deterministic identities.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.Row
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The trace of a Hermitian matrix is real. -/
theorem hermitian_trace_eq_ofReal (C : Matrix ι ι ℂ) (hC : C.IsHermitian) :
    C.trace = (C.trace.re : ℂ) := by
  have hs : star C.trace = C.trace := by rw [← Matrix.trace_conjTranspose, hC.eq]
  exact (RCLike.conj_eq_iff_re.mp hs).symm

omit [DecidableEq ι] in
/-- A Hermitian quadratic form is real. -/
theorem hermitian_quadratic_eq_ofReal (C : Matrix ι ι ℂ) (hC : C.IsHermitian) (y : ι → ℂ) :
    dotProduct (star y) (C *ᵥ y) = ((dotProduct (star y) (C *ᵥ y)).re : ℂ) := by
  exact (RCLike.conj_eq_iff_re.mp (hC.star_dotProduct_mulVec_comm y y)).symm

omit [DecidableEq ι] in
/-- Trace of a complex matrix Gram square has nonnegative real part. -/
theorem trace_gram_re_nonneg (A : Matrix ι ι ℂ) :
    0 ≤ (Aᴴ * A).trace.re := by
  change 0 ≤ (∑ i, ∑ j, star (A j i) * A j i).re
  simp only [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (A j i).re, sq_nonneg (A j i).im]

/-- The inverse spread `V = Tr(C²)` is nonnegative for every Hermitian `C`. -/
theorem hermitian_square_trace_re_nonneg (C : Matrix ι ι ℂ) (hC : C.IsHermitian) :
    0 ≤ (C ^ 2).trace.re := by
  have hp := trace_gram_re_nonneg C
  simpa only [hC.eq, ← pow_two] using hp

/-- The signed row's centered minor source. -/
def rowSource (C : Matrix ι ι ℂ) (δ t : ℝ) : Matrix ι ι ℂ :=
  δ • 1 - t • C

/-- C commutes with its real affine row source. -/
theorem commute_rowSource (C : Matrix ι ι ℂ) (δ t : ℝ) :
    C * rowSource C δ t = rowSource C δ t * C := by
  simp [rowSource, Matrix.mul_sub, Matrix.sub_mul]

omit [Fintype ι] in
/-- Real affine row sources preserve Hermiticity. -/
theorem hermitian_rowSource (C : Matrix ι ι ℂ) (hC : C.IsHermitian) (δ t : ℝ) :
    (rowSource C δ t).IsHermitian := by
  exact (Matrix.isHermitian_one.smul (IsSelfAdjoint.all δ)).sub
    (hC.smul (IsSelfAdjoint.all t))

/-- The matrix square retained in signed row restoration has nonnegative trace. -/
theorem signed_minor_square_trace_nonneg (C : Matrix ι ι ℂ) (hC : C.IsHermitian) (δ t : ℝ) :
    0 ≤ (C ^ 2 * (rowSource C δ t) ^ 2).trace.re := by
  let D := rowSource C δ t
  have hD : D.IsHermitian := hermitian_rowSource C hC δ t
  have hc : C * D = D * C := commute_rowSource C δ t
  have heq : C ^ 2 * D ^ 2 = (C * D)ᴴ * (C * D) := by
    calc
      C ^ 2 * D ^ 2 = C * (C * D) * D := by simp only [pow_two, Matrix.mul_assoc]
      _ = C * (D * C) * D := by rw [hc]
      _ = (C * D) * (C * D) := by simp only [Matrix.mul_assoc]
      _ = (C * D)ᴴ * (C * D) := by rw [Matrix.conjTranspose_mul, hD.eq, hC.eq, ← hc]
  rw [heq]
  exact trace_gram_re_nonneg _

/-- Square expansion of the row source at the matrix level. -/
theorem rowSource_sq (C : Matrix ι ι ℂ) (δ t : ℝ) :
    (rowSource C δ t) ^ 2 =
      δ ^ 2 • (1 : Matrix ι ι ℂ) - (2 * δ * t) • C + t ^ 2 • (C ^ 2) := by
  simp only [rowSource, pow_two, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  module

/-- The signed cubic and quartic terms are the trace of the retained minor square. -/
theorem signed_minor_square_trace_identity (C : Matrix ι ι ℂ) (δ t : ℝ) :
    (C ^ 2 * (rowSource C δ t) ^ 2).trace.re =
      δ ^ 2 * (C ^ 2).trace.re - 2 * δ * t * (C ^ 3).trace.re +
      t ^ 2 * (C ^ 4).trace.re := by
  rw [rowSource_sq]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Complex.add_re,
    Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  simp [pow_succ, Matrix.mul_assoc]

/-- The signed row contraction equals the complete negative matrix square. -/
theorem signed_row_matrix_square_identity (C : Matrix ι ι ℂ) (δ t : ℝ) :
    (C ^ 2).trace.re * (δ ^ 2 + t + t ^ 2 * (C ^ 2).trace.re) +
      (1 + t * (C ^ 2).trace.re) ^ 2 + 2 * t * δ * (C ^ 3).trace.re -
      t ^ 2 * (C ^ 4).trace.re =
      2 * (C ^ 2).trace.re * (δ ^ 2 + t + t ^ 2 * (C ^ 2).trace.re) +
      1 + t * (C ^ 2).trace.re - (C ^ 2 * (rowSource C δ t) ^ 2).trace.re := by
  rw [signed_minor_square_trace_identity]
  ring

/-- The variance-normalized signed row bound, for every Hermitian minor. -/
theorem signed_row_matrix_square_le (C : Matrix ι ι ℂ) (hC : C.IsHermitian)
    (δ t : ℝ) (ht : 0 < t) :
    (C ^ 2).trace.re * (δ ^ 2 + t + t ^ 2 * (C ^ 2).trace.re) +
      (1 + t * (C ^ 2).trace.re) ^ 2 + 2 * t * δ * (C ^ 3).trace.re -
      t ^ 2 * (C ^ 4).trace.re ≤
      (2 * (C ^ 2).trace.re + t⁻¹) * (δ ^ 2 + t + t ^ 2 * (C ^ 2).trace.re) := by
  rw [signed_row_matrix_square_identity]
  have hsq := signed_minor_square_trace_nonneg C hC δ t
  have hfloor : 1 + t * (C ^ 2).trace.re ≤
      (δ ^ 2 + t + t ^ 2 * (C ^ 2).trace.re) / t := by
    apply (le_div_iff₀ ht).2
    nlinarith [sq_nonneg δ]
  rw [div_eq_mul_inv] at hfloor
  nlinarith

end BlockBand.DeterminantScore.Row
