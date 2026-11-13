module

public import Mathlib

/-!
# Gauge invariance of kernel determinants

Row and column exponential gauges cancel in the determinant of a finite complex kernel matrix,
so a gauge `K(x, y) ↦ e^{-h(x)} K(x, y) e^{h(y)}` leaves every factorial correlation
determinant unchanged. No Hermitian, external-source or probabilistic hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.GaussianBulk

/-- Row and column exponential gauges cancel in a determinant, for any complex gauge and any
finite order (including the empty determinant). -/
theorem det_exponential_gauge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (h : ι → ℂ) :
    Matrix.det (fun i j => Complex.exp (-h i) * K i j * Complex.exp (h j)) =
      K.det := by
  have hreorder :
      (fun i j => Complex.exp (-h i) * K i j * Complex.exp (h j)) =
      Matrix.of (fun i j => Complex.exp (-h i) * (Complex.exp (h j) * K i j)) := by
    funext i j
    simp only [Matrix.of_apply]
    ring
  have hrow : Matrix.det (fun i j : ι => Complex.exp (h j) * K i j) =
      (∏ i, Complex.exp (h i)) * K.det :=
    Matrix.det_mul_row (fun i : ι => Complex.exp (h i)) K
  rw [hreorder,
    Matrix.det_mul_column (fun i : ι => Complex.exp (-h i))
      (fun i j : ι => Complex.exp (h j) * K i j),
    hrow,
    ← mul_assoc, ← Finset.prod_mul_distrib]
  simp_rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  simp

end BlockBand.GaussianBulk
