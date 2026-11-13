module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Normed

/-!
# Centered trace unsmoothing

## Results

* `score_unsmoothing_of_unit_eigenvectors_nearSum`: the paper's angular hypothesis over every
  unit eigenvector, with the restricted Poisson sum.
* `score_unsmoothing`, `score_unsmoothing_of_unit_eigenvectors`: weaker forms,
  in Mathlib's eigenbasis / for every unit eigenvector, with the Poisson sum over all
  eigenvalues, as corollaries.

## Objects

* `specFun U μ f = U diag(f ∘ μ) U*` — spectral functional calculus for a unitary `U`.
* `IsMoorePenroseInverse A R` — the four Penrose equations; they determine `R` uniquely
  (`IsMoorePenroseInverse.unique`), and `U diag(μ⁻¹) U*` (with `0⁻¹ = 0`) satisfies them
  (`isMoorePenroseInverse_specFun_inv`), so the theorems quantify over `R = A⁺` exactly.
  `hermitianPinv hA` is this inverse in Mathlib's eigenbasis.
* `hsNorm M = (∑ᵢⱼ |Mᵢⱼ|²)^{1/2}`, the unnormalized Hilbert–Schmidt norm; it equals Mathlib's
  Frobenius norm (`hsNorm_eq_frobenius`).
* `‖G‖` is the Euclidean operator norm (`Matrix.Norms.L2Operator`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.ScoreUnsmoothing

open Matrix
open scoped BigOperators ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
## Spectral functional calculus
-/

/-- Spectral functional calculus `U diag(f(μⱼ)) U*` for a unitary `U` and real `μ`. -/
def specFun (U : Matrix.unitaryGroup n ℂ) (μ : n → ℝ) (f : ℝ → ℂ) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) * diagonal (fun j => f (μ j)) * star (U : Matrix n n ℂ)

section Calculus

variable (U : Matrix.unitaryGroup n ℂ) (μ : n → ℝ)

theorem unitary_star_mul : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 :=
  Unitary.coe_star_mul_self _

theorem unitary_mul_star : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
  Unitary.coe_mul_star_self _

theorem specFun_mul (f g : ℝ → ℂ) :
    specFun U μ f * specFun U μ g = specFun U μ (fun x => f x * g x) := by
  unfold specFun
  calc (U : Matrix n n ℂ) * diagonal (fun j => f (μ j)) * star (U : Matrix n n ℂ) *
        ((U : Matrix n n ℂ) * diagonal (fun j => g (μ j)) * star (U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * (diagonal (fun j => f (μ j)) *
          (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) *
          diagonal (fun j => g (μ j))) * star (U : Matrix n n ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [unitary_star_mul, Matrix.mul_one, diagonal_mul_diagonal]

theorem specFun_add (f g : ℝ → ℂ) :
    specFun U μ f + specFun U μ g = specFun U μ (fun x => f x + g x) := by
  unfold specFun
  rw [← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]

theorem specFun_sub (f g : ℝ → ℂ) :
    specFun U μ f - specFun U μ g = specFun U μ (fun x => f x - g x) := by
  unfold specFun
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]

theorem specFun_smul (c : ℂ) (f : ℝ → ℂ) :
    c • specFun U μ f = specFun U μ (fun x => c * f x) := by
  unfold specFun
  have h : c • diagonal (fun j => f (μ j)) = diagonal (fun j => c * f (μ j)) := by
    ext i j; by_cases hij : i = j <;> simp [diagonal, hij]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem specFun_const (c : ℂ) : specFun U μ (fun _ => c) = c • (1 : Matrix n n ℂ) := by
  unfold specFun
  have : diagonal (fun _ : n => c) = c • (1 : Matrix n n ℂ) := by
    ext i j; by_cases h : i = j <;> simp [diagonal, h]
  rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, unitary_mul_star]

theorem star_specFun (f : ℝ → ℂ) :
    star (specFun U μ f) = specFun U μ (fun x => star (f x)) := by
  unfold specFun
  rw [star_mul, star_mul, star_star, Matrix.mul_assoc, Matrix.star_eq_conjTranspose
    (diagonal _), diagonal_conjTranspose]
  rfl

theorem trace_specFun (f : ℝ → ℂ) : (specFun U μ f).trace = ∑ j, f (μ j) := by
  unfold specFun
  rw [Matrix.trace_mul_cycle, unitary_star_mul, Matrix.one_mul, trace_diagonal]

/-- The quadratic form on the `j`-th column `Uᵀ j` of `U` is the diagonal entry of `U* X U`. -/
theorem quadratic_column (X : Matrix n n ℂ) (j : n) :
    star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (X *ᵥ (U : Matrix n n ℂ)ᵀ j) =
      (star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) j j := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Matrix.star_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- The trace against a spectral function is the eigenbasis sum of the diagonal coefficients
`uⱼ* X uⱼ` (`uⱼ = Uᵀ j`) times `f(μⱼ)`. -/
theorem trace_mul_specFun (X : Matrix n n ℂ) (f : ℝ → ℂ) :
    (X * specFun U μ f).trace =
      ∑ j, (star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (X *ᵥ (U : Matrix n n ℂ)ᵀ j)) * f (μ j) := by
  unfold specFun
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, quadratic_column]

/-- The columns of a unitary are unit vectors. -/
theorem star_dotProduct_self_column (j : n) :
    star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (U : Matrix n n ℂ)ᵀ j = 1 := by
  have h := quadratic_column U 1 j
  rw [Matrix.one_mulVec, Matrix.mul_one, unitary_star_mul, Matrix.one_apply_eq] at h
  exact h

end Calculus

section Decomposition

variable {A : Matrix n n ℂ} (U : Matrix.unitaryGroup n ℂ) (μ : n → ℝ)
  (hAU : A = (U : Matrix n n ℂ) * diagonal (fun j => (μ j : ℂ)) * star (U : Matrix n n ℂ))
include hAU

theorem specFun_id : specFun U μ (fun x => (x : ℂ)) = A := hAU.symm

/-- The columns of `U` are eigenvectors: `uⱼ* A uⱼ = μⱼ`. -/
theorem quadratic_column_eq (j : n) :
    star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (A *ᵥ (U : Matrix n n ℂ)ᵀ j) = (μ j : ℂ) := by
  rw [quadratic_column, hAU]
  have : star (U : Matrix n n ℂ) * ((U : Matrix n n ℂ) * diagonal (fun j => (μ j : ℂ)) *
      star (U : Matrix n n ℂ)) * (U : Matrix n n ℂ) = diagonal (fun j => (μ j : ℂ)) := by
    simp only [← Matrix.mul_assoc]
    rw [unitary_star_mul, Matrix.one_mul, Matrix.mul_assoc, unitary_star_mul, Matrix.mul_one]
  rw [this, diagonal_apply_eq]

end Decomposition

/-- Mathlib's eigenbasis is an instance of the decomposition `A = U diag(μ) U*`. -/
theorem eq_eigenvectorUnitary_decomp {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun j => (hA.eigenvalues j : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

/-!
## Moore–Penrose inverse
-/

/-- The four Penrose equations: `R` is the Moore–Penrose inverse of `A`. -/
def IsMoorePenroseInverse (A R : Matrix n n ℂ) : Prop :=
  A * R * A = A ∧ R * A * R = R ∧ (A * R)ᴴ = A * R ∧ (R * A)ᴴ = R * A

omit [DecidableEq n] in
/-- The Penrose equations determine the inverse uniquely. -/
theorem IsMoorePenroseInverse.unique {A X Y : Matrix n n ℂ}
    (hX : IsMoorePenroseInverse A X) (hY : IsMoorePenroseInverse A Y) : X = Y := by
  obtain ⟨hX1, hX2, hX3, hX4⟩ := hX
  obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
  have hAh : Aᴴ = Aᴴ * Yᴴ * Aᴴ := by
    conv_lhs => rw [← hY1]
    rw [conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc]
  have hAh' : Aᴴ = Aᴴ * Xᴴ * Aᴴ := by
    conv_lhs => rw [← hX1]
    rw [conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc]
  have h1 : X = X * A * Y := by
    calc X = X * (A * X)ᴴ := by rw [hX3, ← Matrix.mul_assoc, hX2]
      _ = X * Xᴴ * Aᴴ := by rw [conjTranspose_mul, Matrix.mul_assoc]
      _ = X * Xᴴ * (Aᴴ * Yᴴ * Aᴴ) := by rw [← hAh]
      _ = X * (A * X)ᴴ * (A * Y)ᴴ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = X * A * Y := by
        rw [hX3, hY3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX2, Matrix.mul_assoc]
  have h2 : Y = X * A * Y := by
    calc Y = (Y * A)ᴴ * Y := by rw [hY4, hY2]
      _ = Aᴴ * Yᴴ * Y := by rw [conjTranspose_mul]
      _ = (Aᴴ * Xᴴ * Aᴴ) * Yᴴ * Y := by rw [← hAh']
      _ = (X * A)ᴴ * (Y * A)ᴴ * Y := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = X * A * Y := by
        rw [hX4, hY4, Matrix.mul_assoc (X * A) (Y * A) Y, hY2]
  exact h1.trans h2.symm

/-- `U diag(μ⁻¹) U*` (eigenvalue inverses on the range, zero on the kernel, `(0 : ℝ)⁻¹ = 0`)
satisfies the Penrose equations for `A = U diag(μ) U*`. -/
theorem isMoorePenroseInverse_specFun_inv {A : Matrix n n ℂ} (U : Matrix.unitaryGroup n ℂ)
    (μ : n → ℝ)
    (hAU : A = (U : Matrix n n ℂ) * diagonal (fun j => (μ j : ℂ)) * star (U : Matrix n n ℂ)) :
    IsMoorePenroseInverse A (specFun U μ (fun x => ((x⁻¹ : ℝ) : ℂ))) := by
  have hstar : ∀ f : ℝ → ℝ, (specFun U μ (fun x => ((f x : ℝ) : ℂ)))ᴴ =
      specFun U μ (fun x => ((f x : ℝ) : ℂ)) := by
    intro f
    rw [← Matrix.star_eq_conjTranspose, star_specFun]
    simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← specFun_id U μ hAU]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [specFun_mul, specFun_mul]
    congr 1; funext x; push_cast; exact mul_inv_mul_cancel _
  · rw [specFun_mul, specFun_mul]
    congr 1; funext x
    push_cast
    simpa using mul_inv_mul_cancel ((x : ℂ)⁻¹)
  · rw [specFun_mul]
    have e : (fun x : ℝ => (x : ℂ) * ((x⁻¹ : ℝ) : ℂ)) = fun x => ((x * x⁻¹ : ℝ) : ℂ) := by
      funext x; push_cast; ring
    rw [e]; exact hstar _
  · rw [specFun_mul]
    have e : (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ) * (x : ℂ)) = fun x => ((x⁻¹ * x : ℝ) : ℂ) := by
      funext x; push_cast; ring
    rw [e]; exact hstar _

/-- Moore–Penrose inverse of a Hermitian matrix in Mathlib's eigenbasis. -/
def hermitianPinv {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  specFun hA.eigenvectorUnitary hA.eigenvalues (fun x => ((x⁻¹ : ℝ) : ℂ))

theorem isMoorePenroseInverse_hermitianPinv {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    IsMoorePenroseInverse A (hermitianPinv hA) :=
  isMoorePenroseInverse_specFun_inv _ _ (eq_eigenvectorUnitary_decomp hA)

theorem IsMoorePenroseInverse.eq_specFun_inv {A R : Matrix n n ℂ}
    (U : Matrix.unitaryGroup n ℂ) (μ : n → ℝ)
    (hAU : A = (U : Matrix n n ℂ) * diagonal (fun j => (μ j : ℂ)) * star (U : Matrix n n ℂ))
    (hR : IsMoorePenroseInverse A R) : R = specFun U μ (fun x => ((x⁻¹ : ℝ) : ℂ)) :=
  hR.unique (isMoorePenroseInverse_specFun_inv U μ hAU)

theorem IsMoorePenroseInverse.eq_hermitianPinv {A R : Matrix n n ℂ} (hA : A.IsHermitian)
    (hR : IsMoorePenroseInverse A R) : R = hermitianPinv hA :=
  hR.unique (isMoorePenroseInverse_hermitianPinv hA)

/-!
## Hilbert–Schmidt norm
-/

/-- Unnormalized Hilbert–Schmidt norm `(∑ᵢⱼ |Mᵢⱼ|²)^{1/2}`. -/
def hsNorm (M : Matrix n n ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)

open scoped Matrix.Norms.Frobenius in
/-- `hsNorm` is Mathlib's Frobenius norm. -/
theorem hsNorm_eq_frobenius (M : Matrix n n ℂ) : hsNorm M = ‖M‖ := by
  rw [hsNorm, Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]

omit [DecidableEq n] in
theorem sum_norm_sq_eq_re_trace (M : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖M i j‖ ^ 2 = (Mᴴ * M).trace.re := by
  rw [Finset.sum_comm]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]

theorem hsNorm_specFun (U : Matrix.unitaryGroup n ℂ) (μ : n → ℝ) (f : ℝ → ℂ) :
    hsNorm (specFun U μ f) = Real.sqrt (∑ j, ‖f (μ j)‖ ^ 2) := by
  rw [hsNorm, sum_norm_sq_eq_re_trace, ← Matrix.star_eq_conjTranspose, star_specFun,
    specFun_mul, trace_specFun, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-!
## Scalar estimates
-/

/-- Scalar difference of the two inverses, `λ⁻¹ - λ/(λ²+η²)`. -/
def unsmoothKernel (η x : ℝ) : ℝ := x⁻¹ - x / (x ^ 2 + η ^ 2)

/-- The Poisson weight `η²/(λ²+η²)`. -/
def poissonWeight (η x : ℝ) : ℝ := η ^ 2 / (x ^ 2 + η ^ 2)

theorem poissonWeight_nonneg (η x : ℝ) : 0 ≤ poissonWeight η x := by
  unfold poissonWeight; positivity

theorem poissonWeight_le_one {η : ℝ} (hη : 0 < η) (x : ℝ) : poissonWeight η x ≤ 1 := by
  unfold poissonWeight
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg x]

theorem abs_unsmoothKernel {η : ℝ} (hη : 0 < η) (x : ℝ) :
    |unsmoothKernel η x| = |x⁻¹| * poissonWeight η x := by
  by_cases hx : x = 0
  · simp [unsmoothKernel, hx]
  have hpos : 0 < x ^ 2 + η ^ 2 := by positivity
  have : unsmoothKernel η x = x⁻¹ * poissonWeight η x := by
    unfold unsmoothKernel poissonWeight
    field_simp
    ring
  rw [this, abs_mul, abs_of_nonneg (poissonWeight_nonneg η x)]

theorem abs_mul_abs_unsmoothKernel_le {η : ℝ} (hη : 0 < η) (x : ℝ) :
    |x| * |unsmoothKernel η x| ≤ poissonWeight η x := by
  rw [abs_unsmoothKernel hη, ← mul_assoc, ← abs_mul]
  by_cases hx : x = 0
  · simp [hx, poissonWeight_nonneg]
  rw [mul_inv_cancel₀ hx, abs_one, one_mul]

theorem far_bound {η δ C₀ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hC₀ : 0 ≤ C₀) {x : ℝ}
    (hx : δ < |x|) :
    (|x| + 2 * C₀) * |unsmoothKernel η x| ≤ η ^ 2 * (1 / δ ^ 2 + 2 * C₀ / δ ^ 3) := by
  have ht : 0 < |x| := hδ.trans hx
  have hw : poissonWeight η x ≤ η ^ 2 / |x| ^ 2 := by
    unfold poissonWeight
    rw [sq_abs]
    exact div_le_div_of_nonneg_left (by positivity) (by rw [← sq_abs]; exact pow_pos ht 2)
      (by nlinarith)
  have hk : |unsmoothKernel η x| ≤ η ^ 2 / |x| ^ 3 := by
    rw [abs_unsmoothKernel hη, abs_inv]
    calc |x|⁻¹ * poissonWeight η x ≤ |x|⁻¹ * (η ^ 2 / |x| ^ 2) := by gcongr
      _ = η ^ 2 / |x| ^ 3 := by field_simp
  calc (|x| + 2 * C₀) * |unsmoothKernel η x| ≤ (|x| + 2 * C₀) * (η ^ 2 / |x| ^ 3) := by
        gcongr
    _ = η ^ 2 * (1 / |x| ^ 2 + 2 * C₀ / |x| ^ 3) := by field_simp
    _ ≤ η ^ 2 * (1 / δ ^ 2 + 2 * C₀ / δ ^ 3) := by
        gcongr

/-- Per-eigenvalue bound combining Steps 1–3: the Poisson-weight terms occur only for the
near nonzero eigenvalues (`x ≠ 0`, `|x| ≤ δ`); zero eigenvalues contribute nothing and far
eigenvalues are paid by `η² (1/δ² + 2C₀/δ³)`. -/
theorem term_bound {η δ C₀ a₀ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hC₀ : 0 ≤ C₀)
    (x : ℝ) (c : ℂ)
    (hnear : x ≠ 0 → |x| ≤ δ → ‖c‖ ≤ a₀ + C₀ * |x|)
    (hfar : δ < |x| → ‖c‖ ≤ |x| + 2 * C₀) :
    ‖c‖ * |unsmoothKernel η x| ≤
      (if x ≠ 0 ∧ |x| ≤ δ then a₀ * (|x⁻¹| * poissonWeight η x) + C₀ * poissonWeight η x
        else 0) + η ^ 2 * (1 / δ ^ 2 + 2 * C₀ / δ ^ 3) := by
  have hK : 0 ≤ η ^ 2 * (1 / δ ^ 2 + 2 * C₀ / δ ^ 3) := by positivity
  have hk := abs_nonneg (unsmoothKernel η x)
  split_ifs with hnd
  · have hc := hnear hnd.1 hnd.2
    calc ‖c‖ * |unsmoothKernel η x| ≤ (a₀ + C₀ * |x|) * |unsmoothKernel η x| := by gcongr
      _ = a₀ * |unsmoothKernel η x| + C₀ * (|x| * |unsmoothKernel η x|) := by ring
      _ ≤ a₀ * (|x⁻¹| * poissonWeight η x) + C₀ * poissonWeight η x := by
          rw [← abs_unsmoothKernel hη]
          gcongr
          exact abs_mul_abs_unsmoothKernel_le hη x
      _ ≤ _ := by linarith
  · rw [zero_add]
    by_cases hx0 : x = 0
    · subst hx0
      have h0 : unsmoothKernel η 0 = 0 := by simp [unsmoothKernel]
      rw [h0, abs_zero, mul_zero]
      exact hK
    have hxd : δ < |x| := lt_of_not_ge fun h => hnd ⟨hx0, h⟩
    exact (mul_le_mul_of_nonneg_right (hfar hxd) hk).trans (far_bound hη hδ hC₀ hxd)

/-!
## Quadratic forms
-/

theorem star_dotProduct_self_eigenvectorBasis {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (j : n) : star ⇑(hA.eigenvectorBasis j) ⬝ᵥ ⇑(hA.eigenvectorBasis j) = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
    hA.eigenvectorBasis.orthonormal.1 j]
  simp

open scoped Matrix.Norms.L2Operator in
/-- `|u* G u| ≤ ‖G‖` for a unit vector `u` (Euclidean operator norm). -/
theorem norm_quadratic_le (G : Matrix n n ℂ) (u : EuclideanSpace ℂ n) (hu : ‖u‖ = 1) :
    ‖star ⇑u ⬝ᵥ (G *ᵥ ⇑u)‖ ≤ ‖G‖ := by
  have h : star ⇑u ⬝ᵥ (G *ᵥ ⇑u) =
      inner ℂ u ((EuclideanSpace.equiv n ℂ).symm (G *ᵥ ⇑u)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  rw [h]
  calc ‖inner ℂ u ((EuclideanSpace.equiv n ℂ).symm (G *ᵥ ⇑u))‖
      ≤ ‖u‖ * ‖(EuclideanSpace.equiv n ℂ).symm (G *ᵥ ⇑u)‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖G‖ * ‖u‖) := by gcongr; exact Matrix.l2_opNorm_mulVec G u
    _ = ‖G‖ := by rw [hu]; ring

open scoped Matrix.Norms.L2Operator in
/-- `|v* G v| ≤ ‖G‖` for a plain vector with `v* v = 1`. -/
theorem norm_quadratic_le_of_dotProduct (G : Matrix n n ℂ) (v : n → ℂ)
    (hv : star v ⬝ᵥ v = 1) : ‖star v ⬝ᵥ (G *ᵥ v)‖ ≤ ‖G‖ := by
  have hu : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ n)
    rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct_comm, hv] at h
    have h1 : ((‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 : ℝ) : ℂ) = 1 := by
      push_cast; exact h.symm
    have h2 : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 = 1 := by exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  simpa using norm_quadratic_le G (WithLp.toLp 2 v) hu

/-!
## The resolvent and its real part in the eigenbasis
-/

section Resolvent

variable {A : Matrix n n ℂ} (U : Matrix.unitaryGroup n ℂ) (μ : n → ℝ)
  (hAU : A = (U : Matrix n n ℂ) * diagonal (fun j => (μ j : ℂ)) * star (U : Matrix n n ℂ))
include hAU

theorem sub_smul_one_eq_specFun (η : ℝ) :
    A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ) =
      specFun U μ (fun x => (x : ℂ) - (η : ℂ) * Complex.I) := by
  have h := specFun_sub U μ (fun x => (x : ℂ)) (fun _ => (η : ℂ) * Complex.I)
  rw [specFun_id U μ hAU, specFun_const] at h
  exact h

omit hAU in
theorem ofReal_sub_mul_I_ne_zero {η : ℝ} (hη : 0 < η) (x : ℝ) :
    (x : ℂ) - (η : ℂ) * Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hη.ne' this

/-- `R_η = (A - iη)⁻¹ = U diag((μⱼ - iη)⁻¹) U*`. -/
theorem resolvent_eq_specFun {η : ℝ} (hη : 0 < η) :
    (A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹ =
      specFun U μ (fun x => ((x : ℂ) - (η : ℂ) * Complex.I)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [sub_smul_one_eq_specFun U μ hAU, specFun_mul]
  have e : (fun x : ℝ => ((x : ℂ) - (η : ℂ) * Complex.I) * ((x : ℂ) - (η : ℂ) * Complex.I)⁻¹) =
      fun _ => (1 : ℂ) := by
    funext x; exact mul_inv_cancel₀ (ofReal_sub_mul_I_ne_zero hη x)
  rw [e, specFun_const, one_smul]

/-- `Re R_η = (R_η + R_η*)/2 = U diag(μⱼ/(μⱼ²+η²)) U*`. -/
theorem realPart_resolvent_eq_specFun {η : ℝ} (hη : 0 < η) :
    (1 / 2 : ℂ) • ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹ +
        ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹)ᴴ) =
      specFun U μ (fun x => ((x / (x ^ 2 + η ^ 2) : ℝ) : ℂ)) := by
  rw [← Matrix.star_eq_conjTranspose, resolvent_eq_specFun U μ hAU hη, star_specFun,
    specFun_add, specFun_smul]
  congr 1
  funext x
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.star_def, Complex.conj_re,
      Complex.inv_re, Complex.ofReal_re, Complex.sub_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.normSq_apply, Complex.add_im,
      Complex.conj_im, Complex.inv_im, Complex.sub_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
    simp only [mul_zero, zero_mul, sub_zero, zero_sub, mul_one, add_zero, neg_mul,
      neg_neg, zero_div, mul_neg]
    ring
  · simp only [Complex.mul_re, Complex.add_re, Complex.star_def, Complex.conj_re,
      Complex.inv_re, Complex.ofReal_re, Complex.sub_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.normSq_apply, Complex.add_im,
      Complex.conj_im, Complex.inv_im, Complex.sub_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
    ring

/-- Step 1: `R - Re R_η` is the spectral function of `λ⁻¹ - λ/(λ²+η²)` (zero at `λ = 0`). -/
theorem pinv_sub_realPart_resolvent {R : Matrix n n ℂ} (hR : IsMoorePenroseInverse A R)
    {η : ℝ} (hη : 0 < η) :
    R - (1 / 2 : ℂ) • ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹ +
        ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹)ᴴ) =
      specFun U μ (fun x => ((unsmoothKernel η x : ℝ) : ℂ)) := by
  rw [realPart_resolvent_eq_specFun U μ hAU hη, hR.eq_specFun_inv U μ hAU, specFun_sub]
  congr 1
  funext x
  simp only [unsmoothKernel, Complex.ofReal_sub]

end Resolvent

/-!
## Diagonal coefficients
-/

theorem centered_quadratic_column (U : Matrix.unitaryGroup n ℂ) (K : Matrix n n ℂ) (c : ℂ)
    (j : n) :
    star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ ((K - c • (1 : Matrix n n ℂ)) *ᵥ (U : Matrix n n ℂ)ᵀ j) =
      star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (K *ᵥ (U : Matrix n n ℂ)ᵀ j) - c := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, star_dotProduct_self_column, smul_eq_mul, mul_one]

/-!
## Main theorem
-/

universe u

open scoped Matrix.Norms.L2Operator in
/-- *Domain.* Deterministic: any finite index type `n` (dimension `d = Fintype.card n`, `d = 0`
allowed); any unitary `U` and real `μ : n → ℝ` with `A = U diag(μ) U*`, i.e. any orthonormal
eigenbasis of `A` (eigenvectors `uⱼ = Uᵀ j`, the columns of `U`, with eigenvalues `μⱼ` listed
with multiplicity); this decomposition makes `A` Hermitian, so no separate Hermitian hypothesis
is needed. `K₀, G` are any complex matrices with `A = K₀ + G` (`K₀`, `G` need not be Hermitian;
`uⱼ* K₀ uⱼ` is complex and `|·|` is the complex modulus). `R` is the Moore–Penrose inverse of
`A` (any matrix satisfying the four Penrose equations, which determine `R`);
`R_η = (A - iη)⁻¹` (Mathlib's matrix inverse; `A - iη` is invertible);
`Re R_η = (R_η + R_η*)/2`; `g : ℝ → ℝ`; `0 < η ≤ δ < 1`; `a₀ ≥ 0`.

*Norms.* `‖G‖` is the Euclidean operator norm (`Matrix.Norms.L2Operator`); `hsNorm R` is the
unnormalized Hilbert–Schmidt norm `(∑ᵢⱼ |Rᵢⱼ|²)^{1/2}` (= Mathlib's Frobenius norm,
`hsNorm_eq_frobenius`). The trace is unnormalized.

*Hypotheses.* `‖G‖ ≤ C₀`, `|g 0| ≤ C₀`, `g` is `C₀`-Lipschitz on `[-δ, δ]`; for every `j`
with `μⱼ ≠ 0` and `|μⱼ| ≤ δ`, `|uⱼ* K₀ uⱼ - g(μⱼ)| ≤ a₀` (in the consumer's own basis; with
degenerate eigenvalues these coefficients depend on the basis, and the proof in the paper works
"in the eigenbasis `(u_λ)` of `A`"); and the Poisson sum **restricted to those same `j`**,
`∑_{μⱼ ≠ 0, |μⱼ| ≤ δ} η²/(μⱼ² + η²) ≤ C₀ d η`. Steps 1–3 use the sum only there (zero
eigenvalues contribute nothing, far ones are paid by Step 3), so this is implied by the paper's
display under either reading of `∑_λ` (all eigenvalues, or the near nonzero ones). `a₀ ≥ 0` is
implicit in the paper (it bounds a modulus whenever the angular hypothesis is non-vacuous) and is
needed when that hypothesis is vacuous.

*Conclusion and quantifier order.* For all `C₀, δ` there is `C` (depending only on `C₀, δ`;
explicitly `max (max √C₀ C₀²) (1/δ² + 2C₀/δ³)`) such that for every dimension and all data as
above, `|Tr (K₀ - g(0))(R - Re R_η)| ≤ C a₀ √(dη) ‖R‖_HS + C dη + C dη²`. `‖K₀‖` is not used. -/
theorem score_unsmoothing_of_eigenbasis (C₀ δ : ℝ) :
    ∃ C : ℝ, ∀ (n : Type u) [Fintype n] [DecidableEq n] (A K₀ G R : Matrix n n ℂ)
      (U : Matrix.unitaryGroup n ℂ) (μ : n → ℝ) (g : ℝ → ℝ) (a₀ η : ℝ),
      A = (U : Matrix n n ℂ) * diagonal (fun j => (μ j : ℂ)) * star (U : Matrix n n ℂ) →
      A = K₀ + G → IsMoorePenroseInverse A R →
      0 < η → η ≤ δ → δ < 1 →
      ‖G‖ ≤ C₀ → |g 0| ≤ C₀ →
      (∀ x ∈ Set.Icc (-δ) δ, ∀ y ∈ Set.Icc (-δ) δ, |g x - g y| ≤ C₀ * |x - y|) →
      0 ≤ a₀ →
      (∀ j, μ j ≠ 0 → |μ j| ≤ δ →
        ‖star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (K₀ *ᵥ (U : Matrix n n ℂ)ᵀ j) -
          ((g (μ j) : ℝ) : ℂ)‖ ≤ a₀) →
      ∑ j ∈ Finset.univ.filter (fun j => μ j ≠ 0 ∧ |μ j| ≤ δ), η ^ 2 / (μ j ^ 2 + η ^ 2) ≤
        C₀ * (Fintype.card n : ℝ) * η →
      ‖((K₀ - ((g 0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *
          (R - (1 / 2 : ℂ) • ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹ +
            ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹)ᴴ))).trace‖ ≤
        C * a₀ * Real.sqrt ((Fintype.card n : ℝ) * η) * hsNorm R +
          C * (Fintype.card n : ℝ) * η + C * (Fintype.card n : ℝ) * η ^ 2 := by
  refine ⟨max (max (Real.sqrt C₀) (C₀ ^ 2)) (1 / δ ^ 2 + 2 * C₀ / δ ^ 3), ?_⟩
  intro n _ _ A K₀ G R U μ g a₀ η hAU hAK hR hη hηδ _hδ1 hG hg0 hLip ha₀ hK hW
  set C := max (max (Real.sqrt C₀) (C₀ ^ 2)) (1 / δ ^ 2 + 2 * C₀ / δ ^ 3)
  have hδ : 0 < δ := hη.trans_le hηδ
  have hC₀ : 0 ≤ C₀ := (abs_nonneg _).trans hg0
  set d : ℝ := (Fintype.card n : ℝ)
  set K : ℝ := 1 / δ ^ 2 + 2 * C₀ / δ ^ 3
  set w : n → ℝ := fun j => poissonWeight η (μ j)
  set S := Finset.univ.filter (fun j => μ j ≠ 0 ∧ |μ j| ≤ δ)
  -- Step 1: reduction to eigenvalues.
  rw [pinv_sub_realPart_resolvent U μ hAU hR hη, trace_mul_specFun]
  simp only [centered_quadratic_column]
  have hK₀ : K₀ = A - G := eq_sub_of_add_eq hAK.symm
  -- Per-eigenvalue bound (Steps 2 and 3).
  have hterm : ∀ j, ‖(star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (K₀ *ᵥ (U : Matrix n n ℂ)ᵀ j) -
      ((g 0 : ℝ) : ℂ)) * ((unsmoothKernel η (μ j) : ℝ) : ℂ)‖ ≤
      (if μ j ≠ 0 ∧ |μ j| ≤ δ then a₀ * (|(μ j)⁻¹| * w j) + C₀ * w j else 0) +
        η ^ 2 * K := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply term_bound hη hδ hC₀
    · intro hne hle
      have hmem : μ j ∈ Set.Icc (-δ) δ := abs_le.mp hle
      have h0 : (0 : ℝ) ∈ Set.Icc (-δ) δ := ⟨by linarith, hδ.le⟩
      have hL := hLip _ hmem _ h0
      rw [sub_zero] at hL
      calc ‖star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (K₀ *ᵥ (U : Matrix n n ℂ)ᵀ j) -
            ((g 0 : ℝ) : ℂ)‖
          = ‖(star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (K₀ *ᵥ (U : Matrix n n ℂ)ᵀ j) -
              ((g (μ j) : ℝ) : ℂ)) + (((g (μ j) - g 0 : ℝ)) : ℂ)‖ := by
            congr 1; push_cast; ring
        _ ≤ a₀ + C₀ * |μ j| := by
            refine (norm_add_le _ _).trans (add_le_add (hK j hne hle) ?_)
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact hL
    · intro _
      have hGq := norm_quadratic_le_of_dotProduct G ((U : Matrix n n ℂ)ᵀ j)
        (star_dotProduct_self_column U j)
      calc ‖star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (K₀ *ᵥ (U : Matrix n n ℂ)ᵀ j) -
            ((g 0 : ℝ) : ℂ)‖
          = ‖((μ j : ℝ) : ℂ) - star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ
              (G *ᵥ (U : Matrix n n ℂ)ᵀ j) - ((g 0 : ℝ) : ℂ)‖ := by
            rw [hK₀, Matrix.sub_mulVec, dotProduct_sub, quadratic_column_eq U μ hAU]
        _ ≤ |μ j| + C₀ + C₀ := by
            refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
              (add_le_add ?_ (hGq.trans hG))) ?_)
            · rw [Complex.norm_real, Real.norm_eq_abs]
            · rw [Complex.norm_real, Real.norm_eq_abs]; exact hg0
        _ = |μ j| + 2 * C₀ := by ring
  -- Summation; the Poisson-weight terms run over `S` only.
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    hterm j)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  -- Cauchy–Schwarz for the a₀ part (Step 2, first bracket).
  have hW' : ∑ j ∈ S, w j ≤ C₀ * d * η := hW
  have hwsq : ∑ j ∈ S, w j ^ 2 ≤ ∑ j ∈ S, w j := Finset.sum_le_sum fun j _ => by
    have h0 := poissonWeight_nonneg η (μ j)
    have h1 := poissonWeight_le_one hη (μ j)
    nlinarith
  have hHS : Real.sqrt (∑ j ∈ S, |(μ j)⁻¹| ^ 2) ≤ hsNorm R := by
    rw [hR.eq_specFun_inv U μ hAU, hsNorm_specFun]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j _ _ => sq_nonneg _)
  have hCS : ∑ j ∈ S, |(μ j)⁻¹| * w j ≤ hsNorm R * (Real.sqrt C₀ * Real.sqrt (d * η)) := by
    have hsq : Real.sqrt (∑ j ∈ S, w j ^ 2) ≤ Real.sqrt C₀ * Real.sqrt (d * η) := by
      rw [← Real.sqrt_mul hC₀, ← mul_assoc]
      exact Real.sqrt_le_sqrt (hwsq.trans hW')
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
    exact mul_le_mul hHS hsq (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hHS)
  have hdη : 0 ≤ d * η := by positivity
  have hHSnn : 0 ≤ hsNorm R := Real.sqrt_nonneg _
  have hsqrt_nn : 0 ≤ Real.sqrt (d * η) := Real.sqrt_nonneg _
  have hC1 : Real.sqrt C₀ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : C₀ ^ 2 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC3 : K ≤ C := le_max_right _ _
  have e1 : a₀ * ∑ j ∈ S, |(μ j)⁻¹| * w j ≤ C * a₀ * Real.sqrt (d * η) * hsNorm R := by
    calc a₀ * ∑ j ∈ S, |(μ j)⁻¹| * w j
        ≤ a₀ * (hsNorm R * (Real.sqrt C₀ * Real.sqrt (d * η))) := by gcongr
      _ = Real.sqrt C₀ * (a₀ * Real.sqrt (d * η) * hsNorm R) := by ring
      _ ≤ C * (a₀ * Real.sqrt (d * η) * hsNorm R) := by gcongr
      _ = _ := by ring
  have e2 : C₀ * ∑ j ∈ S, w j ≤ C * d * η := by
    calc C₀ * ∑ j ∈ S, w j ≤ C₀ * (C₀ * d * η) := by gcongr
      _ = C₀ ^ 2 * (d * η) := by ring
      _ ≤ C * (d * η) := by gcongr
      _ = _ := by ring
  have e3 : d * (η ^ 2 * K) ≤ C * d * η ^ 2 := by
    calc d * (η ^ 2 * K) = K * (d * η ^ 2) := by ring
      _ ≤ C * (d * η ^ 2) := by gcongr
      _ = _ := by ring
  have hsum' : ‖∑ j, (star ((U : Matrix n n ℂ)ᵀ j) ⬝ᵥ (K₀ *ᵥ (U : Matrix n n ℂ)ᵀ j) -
      ((g 0 : ℝ) : ℂ)) * ((unsmoothKernel η (μ j) : ℝ) : ℂ)‖ ≤
      a₀ * ∑ j ∈ S, |(μ j)⁻¹| * w j + C₀ * ∑ j ∈ S, w j + d * (η ^ 2 * K) := hsum
  linarith

open scoped Matrix.Norms.L2Operator in
/-- The paper's form of the angular hypothesis — `|u* K₀ u - g(λ)| ≤ a₀` for **every** unit
eigenvector `u` of `A` whose eigenvalue `λ` is nonzero with `|λ| ≤ δ` — with the Poisson sum
restricted to the nonzero eigenvalues in `[-δ, δ]` (with multiplicity, listed by Mathlib's
`hA.eigenvalues`). Corollary of `score_unsmoothing_of_eigenbasis` in Mathlib's eigenbasis. -/
theorem score_unsmoothing_of_unit_eigenvectors_nearSum (C₀ δ : ℝ) :
    ∃ C : ℝ, ∀ (n : Type u) [Fintype n] [DecidableEq n] (A K₀ G R : Matrix n n ℂ)
      (hA : A.IsHermitian) (g : ℝ → ℝ) (a₀ η : ℝ),
      A = K₀ + G → IsMoorePenroseInverse A R →
      0 < η → η ≤ δ → δ < 1 →
      ‖G‖ ≤ C₀ → |g 0| ≤ C₀ →
      (∀ x ∈ Set.Icc (-δ) δ, ∀ y ∈ Set.Icc (-δ) δ, |g x - g y| ≤ C₀ * |x - y|) →
      0 ≤ a₀ →
      (∀ (lam : ℝ) (v : n → ℂ), lam ≠ 0 → |lam| ≤ δ → A *ᵥ v = (lam : ℂ) • v →
        star v ⬝ᵥ v = 1 → ‖star v ⬝ᵥ (K₀ *ᵥ v) - ((g lam : ℝ) : ℂ)‖ ≤ a₀) →
      ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j ≠ 0 ∧ |hA.eigenvalues j| ≤ δ),
          η ^ 2 / (hA.eigenvalues j ^ 2 + η ^ 2) ≤ C₀ * (Fintype.card n : ℝ) * η →
      ‖((K₀ - ((g 0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *
          (R - (1 / 2 : ℂ) • ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹ +
            ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹)ᴴ))).trace‖ ≤
        C * a₀ * Real.sqrt ((Fintype.card n : ℝ) * η) * hsNorm R +
          C * (Fintype.card n : ℝ) * η + C * (Fintype.card n : ℝ) * η ^ 2 := by
  obtain ⟨C, hC⟩ := score_unsmoothing_of_eigenbasis.{u} C₀ δ
  refine ⟨C, ?_⟩
  intro n _ _ A K₀ G R hA g a₀ η hAK hR hη hηδ hδ1 hG hg0 hLip ha₀ hK hW
  refine hC n A K₀ G R hA.eigenvectorUnitary hA.eigenvalues g a₀ η
    (eq_eigenvectorUnitary_decomp hA) hAK hR hη hηδ hδ1 hG hg0 hLip ha₀
    (fun j hne hle => ?_) hW
  refine hK _ _ hne hle ?_ (star_dotProduct_self_eigenvectorBasis hA j)
  change A *ᵥ ⇑(hA.eigenvectorBasis j) = _
  rw [hA.mulVec_eigenvectorBasis]
  ext i
  simp [Complex.real_smul]

open scoped Matrix.Norms.L2Operator in
/-- Weaker form (implied by `score_unsmoothing_of_eigenbasis`): the angular
hypothesis along Mathlib's eigenbasis `hA.eigenvectorBasis`, and the Poisson sum over **all**
eigenvalues (with multiplicity), which bounds the restricted sum. -/
theorem score_unsmoothing (C₀ δ : ℝ) :
    ∃ C : ℝ, ∀ (n : Type u) [Fintype n] [DecidableEq n] (A K₀ G R : Matrix n n ℂ)
      (hA : A.IsHermitian) (g : ℝ → ℝ) (a₀ η : ℝ),
      A = K₀ + G → IsMoorePenroseInverse A R →
      0 < η → η ≤ δ → δ < 1 →
      ‖G‖ ≤ C₀ → |g 0| ≤ C₀ →
      (∀ x ∈ Set.Icc (-δ) δ, ∀ y ∈ Set.Icc (-δ) δ, |g x - g y| ≤ C₀ * |x - y|) →
      0 ≤ a₀ →
      (∀ j, hA.eigenvalues j ≠ 0 → |hA.eigenvalues j| ≤ δ →
        ‖star ⇑(hA.eigenvectorBasis j) ⬝ᵥ (K₀ *ᵥ ⇑(hA.eigenvectorBasis j)) -
          ((g (hA.eigenvalues j) : ℝ) : ℂ)‖ ≤ a₀) →
      ∑ j, η ^ 2 / (hA.eigenvalues j ^ 2 + η ^ 2) ≤ C₀ * (Fintype.card n : ℝ) * η →
      ‖((K₀ - ((g 0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *
          (R - (1 / 2 : ℂ) • ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹ +
            ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹)ᴴ))).trace‖ ≤
        C * a₀ * Real.sqrt ((Fintype.card n : ℝ) * η) * hsNorm R +
          C * (Fintype.card n : ℝ) * η + C * (Fintype.card n : ℝ) * η ^ 2 := by
  obtain ⟨C, hC⟩ := score_unsmoothing_of_eigenbasis.{u} C₀ δ
  refine ⟨C, ?_⟩
  intro n _ _ A K₀ G R hA g a₀ η hAK hR hη hηδ hδ1 hG hg0 hLip ha₀ hK hW
  refine hC n A K₀ G R hA.eigenvectorUnitary hA.eigenvalues g a₀ η
    (eq_eigenvectorUnitary_decomp hA) hAK hR hη hηδ hδ1 hG hg0 hLip ha₀ hK
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j _ _ => by positivity).trans hW)

open scoped Matrix.Norms.L2Operator in
/-- Weaker form: the paper's angular hypothesis over every unit eigenvector,
with the Poisson sum over **all** eigenvalues. Immediate from `score_unsmoothing`. -/
theorem score_unsmoothing_of_unit_eigenvectors (C₀ δ : ℝ) :
    ∃ C : ℝ, ∀ (n : Type u) [Fintype n] [DecidableEq n] (A K₀ G R : Matrix n n ℂ)
      (hA : A.IsHermitian) (g : ℝ → ℝ) (a₀ η : ℝ),
      A = K₀ + G → IsMoorePenroseInverse A R →
      0 < η → η ≤ δ → δ < 1 →
      ‖G‖ ≤ C₀ → |g 0| ≤ C₀ →
      (∀ x ∈ Set.Icc (-δ) δ, ∀ y ∈ Set.Icc (-δ) δ, |g x - g y| ≤ C₀ * |x - y|) →
      0 ≤ a₀ →
      (∀ (lam : ℝ) (v : n → ℂ), lam ≠ 0 → |lam| ≤ δ → A *ᵥ v = (lam : ℂ) • v →
        star v ⬝ᵥ v = 1 → ‖star v ⬝ᵥ (K₀ *ᵥ v) - ((g lam : ℝ) : ℂ)‖ ≤ a₀) →
      ∑ j, η ^ 2 / (hA.eigenvalues j ^ 2 + η ^ 2) ≤ C₀ * (Fintype.card n : ℝ) * η →
      ‖((K₀ - ((g 0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *
          (R - (1 / 2 : ℂ) • ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹ +
            ((A - ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ))⁻¹)ᴴ))).trace‖ ≤
        C * a₀ * Real.sqrt ((Fintype.card n : ℝ) * η) * hsNorm R +
          C * (Fintype.card n : ℝ) * η + C * (Fintype.card n : ℝ) * η ^ 2 := by
  obtain ⟨C, hC⟩ := score_unsmoothing.{u} C₀ δ
  refine ⟨C, ?_⟩
  intro n _ _ A K₀ G R hA g a₀ η hAK hR hη hηδ hδ1 hG hg0 hLip ha₀ hK hW
  refine hC n A K₀ G R hA g a₀ η hAK hR hη hηδ hδ1 hG hg0 hLip ha₀ (fun j hne hle => ?_) hW
  refine hK _ _ hne hle ?_ (star_dotProduct_self_eigenvectorBasis hA j)
  rw [hA.mulVec_eigenvectorBasis]
  ext i
  simp [Complex.real_smul]

end BlockBand.DeterminantScore.ScoreUnsmoothing
