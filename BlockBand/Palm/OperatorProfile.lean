module

public import BlockBand.Palm.OperatorSpectral
public import Mathlib.Analysis.Complex.Basic

/-!
# Positive-height operator covariance comparison

For a Hermitian `D`, the positive-height covariance operator `v⁻¹ Im (D - (x + ih + tm))⁻¹` is
compared with the zero-height operator `t((D - x - tu)² + (tv)²)⁻¹` in the Loewner order and on
every nonzero direction `q`: the ratio of the quadratic forms lies within the factor
`1 + h/(tv)`, which gives the relative error `h/(t c)` on a window where `v ≥ c > 0`, and
fixed-order products of such ratios have relative error `O_r(h/t)`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open Matrix
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real part of the quadratic form `q* M q`. -/
def operatorQuadratic (M : Matrix ι ι ℂ) (q : ι → ℂ) : ℝ :=
  (star q ⬝ᵥ (M *ᵥ q)).re

omit [Fintype ι] [DecidableEq ι] in
/-- `Im M = (M - M*)/(2i)`. -/
theorem operatorImaginaryPart_eq_div_two_I (M : Matrix ι ι ℂ) :
    operatorImaginaryPart M = ((2 * Complex.I)⁻¹ : ℂ) • (M - Mᴴ) := by
  have hmul : (-Complex.I / 2 : ℂ) * (2 * Complex.I) = 1 := by
    calc
      (-Complex.I / 2 : ℂ) * (2 * Complex.I) = -(Complex.I ^ 2) := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  have hc : (-Complex.I / 2 : ℂ) = (2 * Complex.I)⁻¹ :=
    (inv_eq_of_mul_eq_one_left hmul).symm
  unfold operatorImaginaryPart
  rw [hc]

omit [DecidableEq ι] in
/-- For Hermitian `M`, the complex quadratic form `q* M q` is real and equals
`operatorQuadratic M q`. -/
theorem hermitian_dotProduct_eq_operatorQuadratic
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (q : ι → ℂ) :
    star q ⬝ᵥ (M *ᵥ q) = (operatorQuadratic M q : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using hM.im_star_dotProduct_mulVec_self q

/-- The coordinates of the direction `q` in the eigenbasis of `D`. -/
def profileSpectralDirection (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    (q : ι → ℂ) : ι → ℂ :=
  (hD.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ q

/-- The spectral coordinates of a nonzero direction are nonzero. -/
theorem profileSpectralDirection_ne_zero
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) {q : ι → ℂ} (hq : q ≠ 0) :
    profileSpectralDirection D hD q ≠ 0 := by
  intro hzero
  have hh := congrArg (fun y => (hD.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ y) hzero
  have hU : (hD.eigenvectorUnitary : Matrix ι ι ℂ) *
      (hD.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self hD.eigenvectorUnitary
  simp only [profileSpectralDirection, Matrix.mulVec_mulVec, hU,
    Matrix.one_mulVec, Matrix.mulVec_zero] at hh
  exact hq hh

/-- The quadratic form of an operator diagonal in the eigenbasis of `D`, in spectral
coordinates. -/
theorem operatorQuadratic_spectral
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    (d : ι → ℝ) (q : ι → ℂ) :
    operatorQuadratic (profileSpectralAut D hD (Matrix.diagonal (fun i => (d i : ℂ)))) q =
      ∑ i, ‖profileSpectralDirection D hD q i‖ ^ 2 * d i := by
  unfold operatorQuadratic profileSpectralAut
  rw [Unitary.conjStarAlgAut_apply]
  let U : Matrix ι ι ℂ := hD.eigenvectorUnitary
  change (star q ⬝ᵥ ((U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) *ᵥ q)).re = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hs : star q ᵥ* U = star (Uᴴ *ᵥ q) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [hs]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  change Complex.reAddGroupHom
    (∑ i, star ((Uᴴ *ᵥ q) i) * ((d i : ℂ) * (Uᴴ *ᵥ q) i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (star ((Uᴴ *ᵥ q) i) * ((d i : ℂ) * (Uᴴ *ᵥ q) i)).re =
    ‖(Uᴴ *ᵥ q) i‖ ^ 2 * d i
  rw [Complex.sq_norm]
  simp only [RCLike.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  ring

/-- The quadratic form of the zero-height operator is the scalar profile form
`zeroHeightQuadratic`. -/
theorem zeroHeightOperator_quadratic_eq
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v : ℝ} (ht : 0 < t) (hv : 0 < v) (q : ι → ℂ) :
    operatorQuadratic (zeroHeightOperator D x t u v) q =
      zeroHeightQuadratic t (t * v)
        (fun i => hD.eigenvalues i - x - t * u) (profileSpectralDirection D hD q) := by
  rw [zeroHeightOperator_eq_spectral D hD ht hv, operatorQuadratic_spectral]
  rfl

/-- The quadratic form of the positive-height operator is the scalar profile form
`positiveHeightQuadratic`. -/
theorem positiveHeightOperator_quadratic_eq
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v h : ℝ} (ht : 0 < t) (hv : 0 < v) (hh : 0 ≤ h) (q : ι → ℂ) :
    operatorQuadratic (positiveHeightOperator D x t u v h) q =
      positiveHeightQuadratic t (t * v) h
        (fun i => hD.eigenvalues i - x - t * u) (profileSpectralDirection D hD q) := by
  rw [positiveHeightOperator_eq_spectral D hD ht hv hh, operatorQuadratic_spectral]
  rfl

/-- Nonzero directions have positive zero-height covariance (with no quantitative lower bound). -/
theorem zeroHeightOperator_quadratic_pos
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v : ℝ} (ht : 0 < t) (hv : 0 < v) {q : ι → ℂ} (hq : q ≠ 0) :
    0 < operatorQuadratic (zeroHeightOperator D x t u v) q := by
  rw [zeroHeightOperator_quadratic_eq D hD ht hv]
  exact zeroHeightQuadratic_pos ht (mul_pos ht hv) _
    (profileSpectralDirection_ne_zero D hD hq)

/-- The zero-height covariance operator is positive definite. -/
theorem zeroHeightOperator_posDef
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v : ℝ} (ht : 0 < t) (hv : 0 < v) :
    (zeroHeightOperator D x t u v).PosDef := by
  rw [zeroHeightOperator_eq_spectral D hD ht hv]
  unfold profileSpectralAut
  rw [Unitary.conjStarAlgAut_apply]
  have hd : (Matrix.diagonal (fun i =>
      (zeroHeightProfileEntry t (t * v) (hD.eigenvalues i - x - t * u) : ℂ))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    apply Complex.zero_lt_real.mpr
    unfold zeroHeightProfileEntry
    positivity
  exact hd.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.mpr Unitary.isUnit_coe)

/-- The positive-height covariance operator is positive definite, for every `h ≥ 0`. -/
theorem positiveHeightOperator_posDef
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v h : ℝ} (ht : 0 < t) (hv : 0 < v) (hh : 0 ≤ h) :
    (positiveHeightOperator D x t u v h).PosDef := by
  rw [positiveHeightOperator_eq_spectral D hD ht hv hh]
  unfold profileSpectralAut
  rw [Unitary.conjStarAlgAut_apply]
  have hd : (Matrix.diagonal (fun i =>
      (positiveHeightProfileEntry t (t * v) h (hD.eigenvalues i - x - t * u) : ℂ))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    apply Complex.zero_lt_real.mpr
    unfold positiveHeightProfileEntry
    positivity
  exact hd.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.mpr Unitary.isUnit_coe)

/-- Lower Loewner comparison of the positive-height and zero-height operators, for every
Hermitian `D` and `h ≥ 0`. -/
theorem positiveHeightOperator_lower
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v h : ℝ} (ht : 0 < t) (hv : 0 < v) (hh : 0 ≤ h) :
    (positiveHeightOperator D x t u v h -
      (((1 + h / (t * v))⁻¹ : ℝ) : ℂ) • zeroHeightOperator D x t u v).PosSemidef := by
  rw [positiveHeightOperator_eq_spectral D hD ht hv hh,
    zeroHeightOperator_eq_spectral D hD ht hv]
  unfold profileSpectralAut
  simp only [Unitary.conjStarAlgAut_apply]
  let a : ι → ℝ := fun i => hD.eigenvalues i - x - t * u
  let U : Matrix ι ι ℂ := hD.eigenvectorUnitary
  have hc := conjugated_positiveHeightProfile_lower ht (mul_pos ht hv) hh a U
  have hd : Matrix.diagonal (fun i =>
      (positiveHeightProfileEntry t (t * v) h (a i) : ℂ) -
        ((1 + h / (t * v))⁻¹ * zeroHeightProfileEntry t (t * v) (a i) : ℝ)) =
      Matrix.diagonal (fun i => (positiveHeightProfileEntry t (t * v) h (a i) : ℂ)) -
        (((1 + h / (t * v))⁻¹ : ℝ) : ℂ) •
          Matrix.diagonal (fun i => (zeroHeightProfileEntry t (t * v) (a i) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hd] at hc
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.star_eq_conjTranspose, U, a] using hc

/-- Upper Loewner comparison of the positive-height and zero-height operators. -/
theorem positiveHeightOperator_upper
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v h : ℝ} (ht : 0 < t) (hv : 0 < v) (hh : 0 ≤ h) :
    ((((1 + h / (t * v) : ℝ) : ℂ) • zeroHeightOperator D x t u v) -
      positiveHeightOperator D x t u v h).PosSemidef := by
  rw [positiveHeightOperator_eq_spectral D hD ht hv hh,
    zeroHeightOperator_eq_spectral D hD ht hv]
  unfold profileSpectralAut
  simp only [Unitary.conjStarAlgAut_apply]
  let a : ι → ℝ := fun i => hD.eigenvalues i - x - t * u
  let U : Matrix ι ι ℂ := hD.eigenvectorUnitary
  have hc := conjugated_positiveHeightProfile_upper ht (mul_pos ht hv) hh a U
  have hd : Matrix.diagonal (fun i =>
      ((1 + h / (t * v)) * zeroHeightProfileEntry t (t * v) (a i) : ℝ) -
        (positiveHeightProfileEntry t (t * v) h (a i) : ℂ)) =
      (((1 + h / (t * v) : ℝ) : ℂ) •
        Matrix.diagonal (fun i => (zeroHeightProfileEntry t (t * v) (a i) : ℂ))) -
      Matrix.diagonal (fun i => (positiveHeightProfileEntry t (t * v) h (a i) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hd] at hc
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.star_eq_conjTranspose, U, a] using hc

/-- The ratio of the positive-height and zero-height quadratic forms on a nonzero direction lies
in `[(1 + h/(tv))⁻¹, 1 + h/(tv)]`. -/
theorem positiveHeightOperator_quadratic_ratio_mem_Icc
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v h : ℝ} (ht : 0 < t) (hv : 0 < v) (hh : 0 ≤ h)
    {q : ι → ℂ} (hq : q ≠ 0) :
    operatorQuadratic (positiveHeightOperator D x t u v h) q /
      operatorQuadratic (zeroHeightOperator D x t u v) q ∈ Set.Icc
        (1 + h / (t * v))⁻¹ (1 + h / (t * v)) := by
  have hz := zeroHeightOperator_quadratic_pos (x := x) (u := u) D hD ht hv hq
  rw [positiveHeightOperator_quadratic_eq D hD ht hv hh,
    zeroHeightOperator_quadratic_eq D hD ht hv] at *
  have hb := positiveHeightQuadratic_mem_Icc ht (mul_pos ht hv) hh
    (fun i => hD.eigenvalues i - x - t * u) (profileSpectralDirection D hD q)
  exact ⟨(le_div_iff₀ hz).2 hb.1, (div_le_iff₀ hz).2 hb.2⟩

/-- On a regular window `v ≥ c > 0`, the relative error of the quadratic form is at most
`h/(t c)` for every nonzero direction, with no lower bound on its covariance. -/
theorem positiveHeightOperator_quadratic_relative_error
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v h c : ℝ} (ht : 0 < t) (hc : 0 < c) (hcv : c ≤ v) (hh : 0 ≤ h)
    {q : ι → ℂ} (hq : q ≠ 0) :
    |operatorQuadratic (positiveHeightOperator D x t u v h) q /
        operatorQuadratic (zeroHeightOperator D x t u v) q - 1| ≤ h / (t * c) := by
  rw [positiveHeightOperator_quadratic_eq D hD ht (hc.trans_le hcv) hh,
    zeroHeightOperator_quadratic_eq D hD ht (hc.trans_le hcv)]
  exact abs_positiveHeightQuadratic_ratio_sub_one_le_regular ht hc hcv hh _
    (profileSpectralDirection_ne_zero D hD hq)

/-- The same relative bound stated with complex quadratic forms `q* M q` and the complex norm. -/
theorem positiveHeightOperator_complex_relative_error
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v h c : ℝ} (ht : 0 < t) (hc : 0 < c) (hcv : c ≤ v) (hh : 0 ≤ h)
    {q : ι → ℂ} (hq : q ≠ 0) :
    ‖(star q ⬝ᵥ (positiveHeightOperator D x t u v h *ᵥ q)) /
        (star q ⬝ᵥ (zeroHeightOperator D x t u v *ᵥ q)) - 1‖ ≤ h / (t * c) := by
  rw [hermitian_dotProduct_eq_operatorQuadratic _
      (positiveHeightOperator_posDef D hD ht (hc.trans_le hcv) hh).isHermitian,
    hermitian_dotProduct_eq_operatorQuadratic _
      (zeroHeightOperator_posDef D hD ht (hc.trans_le hcv)).isHermitian]
  have he := positiveHeightOperator_quadratic_relative_error (x := x) (u := u) D hD ht hc hcv hh hq
  simpa only [← Complex.ofReal_div, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using he

/-- Fixed-order product comparison for a family of Hermitian operators and nonzero directions. Each
deformation, shift, variance and height may differ. The only common control is ε_h≤ε. No bound on
D_j or on a tested direction covariance occurs. -/
theorem prod_positiveHeightOperator_ratio_mem_Icc
    {α : Type*} (s : Finset α)
    (D : α → Matrix ι ι ℂ) (hD : ∀ j, (D j).IsHermitian)
    (x t u v h : α → ℝ) (q : α → ι → ℂ)
    (ht : ∀ j ∈ s, 0 < t j) (hv : ∀ j ∈ s, 0 < v j)
    (hh : ∀ j ∈ s, 0 ≤ h j) (hq : ∀ j ∈ s, q j ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) (hεj : ∀ j ∈ s, h j / (t j * v j) ≤ ε) :
    (∏ j ∈ s, operatorQuadratic (positiveHeightOperator (D j) (x j) (t j) (u j) (v j) (h j)) (q j)) /
      (∏ j ∈ s, operatorQuadratic (zeroHeightOperator (D j) (x j) (t j) (u j) (v j)) (q j)) ∈
      Set.Icc ((1 + ε)⁻¹ ^ s.card) ((1 + ε) ^ s.card) := by
  rw [← Finset.prod_div_distrib]
  have hbounds : ∀ j ∈ s,
      operatorQuadratic (positiveHeightOperator (D j) (x j) (t j) (u j) (v j) (h j)) (q j) /
        operatorQuadratic (zeroHeightOperator (D j) (x j) (t j) (u j) (v j)) (q j) ∈
        Set.Icc (1 + ε)⁻¹ (1 + ε) := by
    intro j hj
    have hb := positiveHeightOperator_quadratic_ratio_mem_Icc (x := x j) (u := u j) (D j) (hD j)
      (ht j hj) (hv j hj) (hh j hj) (hq j hj)
    have hjnonneg : 0 ≤ h j / (t j * v j) :=
      div_nonneg (hh j hj) (mul_pos (ht j hj) (hv j hj)).le
    have hp : 0 < 1 + h j / (t j * v j) := by linarith
    have hsum : 1 + h j / (t j * v j) ≤ 1 + ε :=
      add_le_add (le_refl (1 : ℝ)) (hεj j hj)
    have hc : (1 + ε)⁻¹ ≤ (1 + h j / (t j * v j))⁻¹ := inv_anti₀ hp hsum
    exact ⟨hc.trans hb.1, hb.2.trans hsum⟩
  have hp : 0 ≤ (1 + ε)⁻¹ := inv_nonneg.mpr (by linarith)
  constructor
  · calc
      (1 + ε)⁻¹ ^ s.card = ∏ _j ∈ s, (1 + ε)⁻¹ := by rw [Finset.prod_const]
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hp) (fun j hj => (hbounds j hj).1)
  · calc
      (∏ j ∈ s, _) ≤ ∏ _j ∈ s, (1 + ε) :=
        Finset.prod_le_prod₀ (fun j hj => hp.trans (hbounds j hj).1)
          (fun j hj => (hbounds j hj).2)
      _ = (1 + ε) ^ s.card := by rw [Finset.prod_const]

/-- Uniform deterministic fixed-order linear error bound for small relative
height. This is the explicit O_r(ε) consequence of the full product interval. -/
theorem profile_power_error_le (r : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 + ε) ^ r - 1 ≤ ((2 : ℝ) ^ r - 1) * ε := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hC : 0 ≤ (2 : ℝ) ^ r - 1 := by
      exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))
    have hh := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1 + ε by linarith)
    have he : 0 ≤ ((2 : ℝ) ^ r - 1) * ε * (1 - ε) :=
      mul_nonneg (mul_nonneg hC hε) (sub_nonneg.mpr hε1)
    simp only [pow_succ] at *
    nlinarith

/-- Turning the exact product interval into an absolute relative error
requires no covariance lower bound and has constant depending only on r. -/
theorem profile_product_error_le {r : ℕ} {P ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hP : P ∈ Set.Icc ((1 + ε)⁻¹ ^ r) ((1 + ε) ^ r)) :
    |P - 1| ≤ ((2 : ℝ) ^ r - 1) * ε := by
  have hpow : 1 ≤ (1 + ε) ^ r := one_le_pow₀ (by linarith)
  have hpos : 0 < (1 + ε) ^ r := by positivity
  have hinv : 2 - (1 + ε) ^ r ≤ (1 + ε)⁻¹ ^ r := by
    rw [inv_pow, inv_eq_one_div, le_div_iff₀ hpos]
    nlinarith [sq_nonneg ((1 + ε) ^ r - 1)]
  have he := profile_power_error_le r hε hε1
  rw [abs_le]
  constructor <;> linarith [hP.1, hP.2]

/-- Full source product relative error, explicit in arbitrary finite r.
Combining ε≤h/(t c*) on a regular window gives O_r(h/t), uniformly in
all operator dimensions, deformations and tested nonzero directions. -/
theorem prod_positiveHeightOperator_relative_error
    {α : Type*} (s : Finset α)
    (D : α → Matrix ι ι ℂ) (hD : ∀ j, (D j).IsHermitian)
    (x t u v h : α → ℝ) (q : α → ι → ℂ)
    (ht : ∀ j ∈ s, 0 < t j) (hv : ∀ j ∈ s, 0 < v j)
    (hh : ∀ j ∈ s, 0 ≤ h j) (hq : ∀ j ∈ s, q j ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεj : ∀ j ∈ s, h j / (t j * v j) ≤ ε) :
    |(∏ j ∈ s, operatorQuadratic (positiveHeightOperator (D j) (x j) (t j) (u j) (v j) (h j)) (q j)) /
      (∏ j ∈ s, operatorQuadratic (zeroHeightOperator (D j) (x j) (t j) (u j) (v j)) (q j)) - 1| ≤
      ((2 : ℝ) ^ s.card - 1) * ε :=
  profile_product_error_le hε hε1
    (prod_positiveHeightOperator_ratio_mem_Icc s D hD x t u v h q ht hv hh hq hε hεj)

/-- At `h = 0` the positive-height and zero-height operators coincide. -/
theorem positiveHeightOperator_zero_height
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    {x t u v : ℝ} (ht : 0 < t) (hv : 0 < v) :
    positiveHeightOperator D x t u v 0 = zeroHeightOperator D x t u v := by
  rw [positiveHeightOperator_eq_spectral D hD ht hv le_rfl,
    zeroHeightOperator_eq_spectral D hD ht hv]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [positiveHeightProfileEntry, zeroHeightProfileEntry]
  · simp [hij]

/-- Explicit fixed-order O_r(h/t) conclusion on a regular window v_j≥c*>0.
It follows from the exact finite product comparison whenever h/(tc*)≤1,
which holds eventually as h/t→0. No direction covariance lower bound occurs. -/
theorem prod_positiveHeightOperator_relative_error_regular
    {α : Type*} (s : Finset α)
    (D : α → Matrix ι ι ℂ) (hD : ∀ j, (D j).IsHermitian)
    (x u v : α → ℝ) (q : α → ι → ℂ)
    {t h c : ℝ} (ht : 0 < t) (hc : 0 < c)
    (hcv : ∀ j ∈ s, c ≤ v j) (hh : 0 ≤ h)
    (hq : ∀ j ∈ s, q j ≠ 0) (hsmall : h / (t * c) ≤ 1) :
    |(∏ j ∈ s, operatorQuadratic (positiveHeightOperator (D j) (x j) t (u j) (v j) h) (q j)) /
      (∏ j ∈ s, operatorQuadratic (zeroHeightOperator (D j) (x j) t (u j) (v j)) (q j)) - 1| ≤
      ((2 : ℝ) ^ s.card - 1) * h / (t * c) := by
  have hb : ∀ j ∈ s, h / (t * v j) ≤ h / (t * c) := by
    intro j hj
    exact div_le_div_of_nonneg_left hh (mul_pos ht hc)
      (mul_le_mul_of_nonneg_left (hcv j hj) ht.le)
  have he := prod_positiveHeightOperator_relative_error s D hD x
    (fun _ => t) u v (fun _ => h) q (fun _ _ => ht)
    (fun j hj => hc.trans_le (hcv j hj)) (fun _ _ => hh) hq
    (div_nonneg hh (mul_pos ht hc).le) hsmall hb
  simpa only [mul_div_assoc] using he

end BlockBand.Palm
