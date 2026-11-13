module

public import BlockBand.Palm.ProfileQuadratic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Spectral form of the covariance profile operators

Definitions of the zero-height and positive-height covariance operators of a Hermitian `D`, and
their expression as diagonal operators in the eigenbasis of `D`, with entries
`t/(a_j² + (tv)²)` and the corresponding positive-height profile, `a_j = λ_j(D) - x - tu`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open Matrix
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The operator imaginary part `Im M = (-i/2)(M - M*)`. -/
def operatorImaginaryPart (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (-Complex.I / 2) • (M - Mᴴ)

/-- The zero-height operator `t((D - (x + tu))² + (tv)²)⁻¹`. -/
def zeroHeightOperator (D : Matrix ι ι ℂ) (x t u v : ℝ) : Matrix ι ι ℂ :=
  (t : ℂ) • ((D - ((x + t * u : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) ^ 2 +
    (((t * v) ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ))⁻¹

/-- The positive-height operator `v⁻¹ Im (D - (x + ih + tm))⁻¹` for `m = u + iv`. -/
def positiveHeightOperator (D : Matrix ι ι ℂ) (x t u v h : ℝ) : Matrix ι ι ℂ :=
  ((v⁻¹ : ℝ) : ℂ) • operatorImaginaryPart
    (D - ((x : ℂ) + Complex.I * h + (t : ℂ) * ((u : ℂ) + Complex.I * v)) •
      (1 : Matrix ι ι ℂ))⁻¹

/-- Conjugation by the eigenvector unitary of `D`, as a star algebra automorphism. -/
def profileSpectralAut (D : Matrix ι ι ℂ) (hD : D.IsHermitian) :
    Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hD.eigenvectorUnitary

/-- The inverse of a diagonal matrix with nonzero entries. -/
theorem inv_diagonal_of_nonzero (d : ι → ℂ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [hd]
  · simp [hij]

/-- The inverse of the image of a diagonal matrix with nonzero entries under a star algebra
automorphism. -/
theorem inv_aut_diagonal_of_nonzero
    (Φ : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ)
    (d : ι → ℂ) (hd : ∀ i, d i ≠ 0) :
    (Φ (Matrix.diagonal d))⁻¹ = Φ (Matrix.diagonal (fun i => (d i)⁻¹)) := by
  apply Matrix.inv_eq_left_inv
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  have hp : Matrix.diagonal (fun i => (d i)⁻¹ * d i) = (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hd]
    · simp [hij]
  rw [hp, map_one]

omit [DecidableEq ι] in
/-- The operator imaginary part commutes with star algebra automorphisms. -/
theorem operatorImaginaryPart_aut
    (Φ : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ) (M : Matrix ι ι ℂ) :
    operatorImaginaryPart (Φ M) = Φ (operatorImaginaryPart M) := by
  unfold operatorImaginaryPart
  change (-Complex.I / 2) • (Φ M - star (Φ M)) =
    Φ ((-Complex.I / 2) • (M - star M))
  rw [map_smul, map_sub, map_star]

omit [Fintype ι] in
/-- On diagonal matrices, the operator imaginary part is the diagonal of the scalar imaginary
parts. -/
theorem operatorImaginaryPart_diagonal (d : ι → ℂ) :
    operatorImaginaryPart (Matrix.diagonal d) =
      Matrix.diagonal (fun i => ((d i).im : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    apply Complex.ext
    · simp [operatorImaginaryPart]
      ring
    · simp [operatorImaginaryPart]
  · simp [operatorImaginaryPart, hij]

/-- `D - z I` in the eigenbasis of `D`. -/
theorem hermitian_shift_eq_spectral
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (z : ℂ) :
    D - z • (1 : Matrix ι ι ℂ) =
      profileSpectralAut D hD (Matrix.diagonal (fun i => (hD.eigenvalues i : ℂ) - z)) := by
  have hDspec : D = profileSpectralAut D hD
      (Matrix.diagonal (fun i => (hD.eigenvalues i : ℂ))) := hD.spectral_theorem
  conv_lhs => rw [hDspec]
  have hdiag : Matrix.diagonal (fun i => (hD.eigenvalues i : ℂ)) -
      z • (1 : Matrix ι ι ℂ) = Matrix.diagonal (fun i => (hD.eigenvalues i : ℂ) - z) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [← hdiag, map_sub, map_smul, map_one]

/-- The spectral parameter `x + ih + t(u + iv)` is the centred shift `x + tu` plus the imaginary
height `h + tv`. -/
theorem profile_spectral_parameter (x t u v h : ℝ) :
    (x : ℂ) + Complex.I * h + (t : ℂ) * ((u : ℂ) + Complex.I * v) =
      ((x + t * u : ℝ) : ℂ) + Complex.I * ((t * v + h : ℝ) : ℂ) := by
  push_cast
  ring

/-- `Im (a - i(tv + h))⁻¹ / v` is the positive-height profile entry. -/
theorem profile_im_inv_div
    {a t v h : ℝ} (ht : 0 < t) (hv : 0 < v) (hh : 0 ≤ h) :
    (((a : ℂ) - Complex.I * ((t * v + h : ℝ) : ℂ))⁻¹).im / v =
      positiveHeightProfileEntry t (t * v) h a := by
  have htv : t * v ≠ 0 := (mul_pos ht hv).ne'
  have hden : 0 < a ^ 2 + (t * v + h) ^ 2 := by positivity
  rw [Complex.inv_im]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, zero_mul, zero_add, zero_sub,
    neg_neg, Complex.normSq_apply, Complex.sub_re, Complex.mul_re,
    mul_zero, sub_zero]
  unfold positiveHeightProfileEntry
  have hraw : a * a + (-(t * v + h)) * (-(t * v + h)) ≠ 0 := by
    nlinarith [hden]
  have hnew : a ^ 2 + ((1 + h / (t * v)) * (t * v)) ^ 2 ≠ 0 := by
    have heq : (1 + h / (t * v)) * (t * v) = t * v + h := by field_simp [htv]
    rw [heq]
    exact hden.ne'
  field_simp [hv.ne', htv, hraw, hnew]

/-- The zero-height operator in the eigenbasis of `D`, with `a_j = λ_j(D) - x - tu`. -/
theorem zeroHeightOperator_eq_spectral
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v : ℝ} (ht : 0 < t) (hv : 0 < v) :
    zeroHeightOperator D x t u v = profileSpectralAut D hD
      (Matrix.diagonal (fun i =>
        (zeroHeightProfileEntry t (t * v) (hD.eigenvalues i - x - t * u) : ℂ))) := by
  let a : ι → ℝ := fun i => hD.eigenvalues i - x - t * u
  let d : ι → ℂ := fun i => ((a i ^ 2 + (t * v) ^ 2 : ℝ) : ℂ)
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    dsimp [d]
    exact_mod_cast (show a i ^ 2 + (t * v) ^ 2 ≠ 0 from (by positivity))
  have hshift : D - ((x + t * u : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) =
      profileSpectralAut D hD (Matrix.diagonal (fun i => (a i : ℂ))) := by
    rw [hermitian_shift_eq_spectral D hD]
    congr 2
    ext i
    dsimp [a]
    push_cast
    ring
  have hden : (D - ((x + t * u : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) ^ 2 +
      (((t * v) ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) =
      profileSpectralAut D hD (Matrix.diagonal d) := by
    rw [hshift, ← map_pow, ← map_one (profileSpectralAut D hD), ← map_smul, ← map_add]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp [pow_two, d, Matrix.diagonal_mul_diagonal]
    · simp [pow_two, d, hij, Matrix.diagonal_mul_diagonal]
  unfold zeroHeightOperator
  rw [hden, inv_aut_diagonal_of_nonzero _ d hd, ← map_smul]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [zeroHeightProfileEntry, d, a, div_eq_mul_inv]
  · simp [hij]

/-- The positive-height operator in the eigenbasis of `D`, for every `h ≥ 0`. -/
theorem positiveHeightOperator_eq_spectral
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v h : ℝ} (ht : 0 < t) (hv : 0 < v) (hh : 0 ≤ h) :
    positiveHeightOperator D x t u v h = profileSpectralAut D hD
      (Matrix.diagonal (fun i =>
        (positiveHeightProfileEntry t (t * v) h (hD.eigenvalues i - x - t * u) : ℂ))) := by
  let a : ι → ℝ := fun i => hD.eigenvalues i - x - t * u
  let d : ι → ℂ := fun i => (a i : ℂ) - Complex.I * ((t * v + h : ℝ) : ℂ)
  have hd : ∀ i, d i ≠ 0 := by
    intro i hz
    have hz' := congrArg Complex.im hz
    simp [d] at hz'
    linarith [mul_pos ht hv]
  have hshift : D - ((x : ℂ) + Complex.I * h + (t : ℂ) * ((u : ℂ) + Complex.I * v)) •
      (1 : Matrix ι ι ℂ) = profileSpectralAut D hD (Matrix.diagonal d) := by
    rw [hermitian_shift_eq_spectral D hD, profile_spectral_parameter]
    congr 2
    ext i
    dsimp [a, d]
    push_cast
    ring
  unfold positiveHeightOperator
  rw [hshift, inv_aut_diagonal_of_nonzero _ d hd,
    operatorImaginaryPart_aut, operatorImaginaryPart_diagonal, ← map_smul]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
    have hs := profile_im_inv_div (a := a i) ht hv hh
    rw [show ((v⁻¹ : ℝ) : ℂ) * (((d i)⁻¹).im : ℂ) =
      ((((d i)⁻¹).im / v : ℝ) : ℂ) by push_cast; ring]
    exact congrArg Complex.ofReal hs
  · simp [hij]

end BlockBand.Palm
