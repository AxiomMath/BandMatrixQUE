module

public import BlockBand.Palm.OperatorSpectral
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Trace residual and stability of the scalar Dyson equation

Definitions of the finite scalar Dyson residual `m - ⟨(λ - z - s m)⁻¹⟩`, its Jacobian, the
normalized matrix trace `⟨(F - z)⁻¹⟩` and the trace certificate
`certificateChi F c E μ = ⟨(F - E - cμ)⁻¹⟩ - μ`, with the Ward identities and a lower bound on the
real part of the Jacobian at the reference point.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- Uniform average over the index set (eigenvalues counted with multiplicity). -/
def certificateAverage (f : ι → ℂ) : ℂ := 𝔼 i, f i

/-- Real version of the same uniform average. -/
def certificateRealAverage (f : ι → ℝ) : ℝ := 𝔼 i, f i

/-- Scalar resolvent `(λ - z)⁻¹`. -/
def certificateScalarResolvent (spectrum : ℝ) (z : ℂ) : ℂ := ((spectrum : ℂ) - z)⁻¹

/-- The finite scalar Dyson residual `m - ⟨(λ - z - s m)⁻¹⟩`. -/
def certificateDysonResidual (spectrum : ι → ℝ) (s : ℝ) (z m : ℂ) : ℂ :=
  m - certificateAverage (fun i => certificateScalarResolvent (spectrum i) (z + s * m))

/-- The Jacobian `1 - s⟨(λ - z - s m)⁻²⟩` of the residual in `m`. -/
def certificateDysonJacobian (spectrum : ι → ℝ) (s : ℝ) (z m : ℂ) : ℂ :=
  1 - (s : ℂ) * certificateAverage
    (fun i => certificateScalarResolvent (spectrum i) (z + s * m) ^ 2)

/-- The matrix resolvent `(F - z)⁻¹`. -/
def certificateMatrixResolvent [DecidableEq ι]
    (F : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (F - z • (1 : Matrix ι ι ℂ))⁻¹

/-- The normalized trace `⟨(F - z)⁻¹⟩`. -/
def certificateMatrixTrace [DecidableEq ι]
    (F : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  (certificateMatrixResolvent F z).trace / (Fintype.card ι : ℂ)

/-- The trace certificate `χ = ⟨(F - E - cμ)⁻¹⟩ - μ`. -/
def certificateChi [DecidableEq ι]
    (F : Matrix ι ι ℂ) (c E : ℝ) (μ : ℂ) : ℂ :=
  certificateMatrixTrace F ((E : ℂ) + c * μ) - μ

/-- Real part commutes with the uniform spectral average. -/
theorem certificateAverage_re (f : ι → ℂ) :
    (certificateAverage f).re = certificateRealAverage (fun i => (f i).re) := by
  simp only [certificateAverage, certificateRealAverage, Fintype.expect_eq_sum_div_card,
    Complex.div_natCast_re]
  change Complex.reAddGroupHom (∑ i, f i) / (Fintype.card ι : ℝ) = _
  rw [map_sum]
  rfl

/-- Imaginary part commutes with the uniform spectral average. -/
theorem certificateAverage_im (f : ι → ℂ) :
    (certificateAverage f).im = certificateRealAverage (fun i => (f i).im) := by
  simp only [certificateAverage, certificateRealAverage, Fintype.expect_eq_sum_div_card,
    Complex.div_natCast_im]
  change Complex.imAddGroupHom (∑ i, f i) / (Fintype.card ι : ℝ) = _
  rw [map_sum]
  rfl

/-- Jensen for the real, normalized finite average. -/
theorem certificate_jensen [Nonempty ι] (f : ι → ℝ) :
    certificateRealAverage f ^ 2 ≤ certificateRealAverage (fun i => f i ^ 2) := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    f (fun _ => (1 : ℝ))
  simpa [certificateRealAverage] using h

/-- Conjugation by the eigenvector unitary preserves the trace. -/
theorem certificate_trace_spectralAut [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) (M : Matrix ι ι ℂ) :
    (profileSpectralAut F hF M).trace = M.trace := by
  unfold profileSpectralAut
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  have hU : star (hF.eigenvectorUnitary : Matrix ι ι ℂ) *
      (hF.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hF.eigenvectorUnitary.property
  rw [hU, one_mul]

/-- The resolvent in the eigenbasis of `F`. -/
theorem certificateMatrixResolvent_eq_spectral [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    certificateMatrixResolvent F z = profileSpectralAut F hF
      (Matrix.diagonal (fun i => certificateScalarResolvent (hF.eigenvalues i) z)) := by
  unfold certificateMatrixResolvent
  rw [hermitian_shift_eq_spectral, inv_aut_diagonal_of_nonzero]
  · rfl
  · intro i heq
    have him := congrArg Complex.im heq
    simp at him
    exact hz him

/-- The normalized trace equals the spectral average over the eigenvalues. -/
theorem certificateMatrixTrace_eq_average [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    certificateMatrixTrace F z = certificateAverage
      (fun i => certificateScalarResolvent (hF.eigenvalues i) z) := by
  unfold certificateMatrixTrace certificateAverage
  rw [certificateMatrixResolvent_eq_spectral F hF hz, certificate_trace_spectralAut,
    Matrix.trace_diagonal, Fintype.expect_eq_sum_div_card]

/-- `χ` is minus the spectral Dyson residual at the reference point. -/
theorem certificateChi_eq_neg_residual [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E : ℝ} {μ : ℂ}
    (hc : 0 < c) (hμ : 0 < μ.im) :
    certificateChi F c E μ =
      -certificateDysonResidual hF.eigenvalues c (E : ℂ) μ := by
  have hz : ((E : ℂ) + c * μ).im ≠ 0 := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero, zero_add]
    exact (mul_pos hc hμ).ne'
  unfold certificateChi certificateDysonResidual
  rw [certificateMatrixTrace_eq_average F hF hz]
  ring

/-- Scalar Ward identity for `(λ - z)⁻¹`. -/
theorem certificate_scalar_ward (spectrum : ℝ) (z : ℂ) :
    (certificateScalarResolvent spectrum z).im =
      z.im * Complex.normSq (certificateScalarResolvent spectrum z) := by
  unfold certificateScalarResolvent
  rw [Complex.inv_im, Complex.normSq_inv]
  simp
  ring

/-- `Re(1 - c r²) = 1 - c|r|² + 2c (Im r)²`. -/
theorem certificate_scalar_jacobian_identity (r : ℂ) (c : ℝ) :
    (1 - (c : ℂ) * r ^ 2).re =
      1 - c * Complex.normSq r + 2 * c * r.im ^ 2 := by
  simp [Complex.normSq_apply, pow_two]
  ring

/-- Averaged Ward identity for a finite Hermitian spectrum. -/
theorem certificate_average_ward (spectrum : ι → ℝ) (z : ℂ) :
    (certificateAverage (fun i => certificateScalarResolvent (spectrum i) z)).im =
      z.im * certificateRealAverage
        (fun i => Complex.normSq (certificateScalarResolvent (spectrum i) z)) := by
  rw [certificateAverage_im]
  unfold certificateRealAverage
  simp_rw [certificate_scalar_ward]
  rw [Finset.mul_expect]

/-- The real part of the Jacobian at the reference point in terms of `χ`. -/
theorem certificate_jacobian_identity [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E : ℝ} {μ : ℂ}
    (hc : 0 < c) (hμ : 0 < μ.im) :
    (certificateDysonJacobian hF.eigenvalues c (E : ℂ) μ).re =
      -(certificateChi F c E μ).im / μ.im + 2 * c * certificateRealAverage
        (fun i => (certificateScalarResolvent (hF.eigenvalues i)
          ((E : ℂ) + c * μ)).im ^ 2) := by
  let z : ℂ := (E : ℂ) + c * μ
  have hz : 0 < z.im := by
    dsimp [z]
    simpa using mul_pos hc hμ
  have hw := certificate_average_ward hF.eigenvalues z
  have htrace := certificateMatrixTrace_eq_average F hF hz.ne'
  have hchi : (certificateChi F c E μ).im =
      (certificateAverage (fun i => certificateScalarResolvent (hF.eigenvalues i) z)).im -
        μ.im := by
    unfold certificateChi
    rw [htrace]
    rfl
  have hzv : z.im = c * μ.im := by simp [z]
  rw [hzv] at hw
  unfold certificateDysonJacobian
  rw [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, certificateAverage_re]
  have hsq : certificateRealAverage
      (fun i => (certificateScalarResolvent (hF.eigenvalues i) z ^ 2).re) =
      certificateRealAverage (fun i => Complex.normSq
        (certificateScalarResolvent (hF.eigenvalues i) z)) -
      2 * certificateRealAverage (fun i =>
        (certificateScalarResolvent (hF.eigenvalues i) z).im ^ 2) := by
    have hs : ∀ r : ℂ, (r ^ 2).re = Complex.normSq r - 2 * r.im ^ 2 := by
      intro r
      simp [pow_two, Complex.normSq_apply]
      ring
    simp_rw [hs]
    simp only [certificateRealAverage, Finset.expect_sub_distrib, Finset.mul_expect]
  change 1 - c * certificateRealAverage
    (fun i => (certificateScalarResolvent (hF.eigenvalues i) z ^ 2).re) = _
  rw [hsq, hchi]
  rw [hw]
  field_simp [hμ.ne']
  ring

/-- Complex derivative of each scalar resolvent term. -/
theorem certificateScalarResolvent_hasDerivAt
    (spectrum s : ℝ) (z m : ℂ) (hz : (z + s * m).im ≠ 0) :
    HasDerivAt (fun w : ℂ => certificateScalarResolvent spectrum (z + s * w))
      ((s : ℂ) * certificateScalarResolvent spectrum (z + s * m) ^ 2) m := by
  have hd : (spectrum : ℂ) - (z + s * m) ≠ 0 := by
    intro heq
    have him := congrArg Complex.im heq
    exact hz (by simpa only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] using him)
  have h := ((hasDerivAt_const m (spectrum : ℂ)).sub
    ((hasDerivAt_const m z).add ((hasDerivAt_id m).const_mul (s : ℂ)))).inv hd
  convert h using 1
  · ext w
    rfl
  · simp only [Pi.sub_apply, Pi.add_apply, id_eq, certificateScalarResolvent,
      zero_add, mul_one, zero_sub, neg_neg, div_eq_mul_inv, inv_pow]

/-- `certificateDysonJacobian` is the derivative of the finite Dyson residual in `m`. -/
theorem certificateDysonResidual_hasDerivAt
    (spectrum : ι → ℝ) (s : ℝ) (z m : ℂ) (hz : (z + s * m).im ≠ 0) :
    HasDerivAt (fun w : ℂ => certificateDysonResidual spectrum s z w)
      (certificateDysonJacobian spectrum s z m) m := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => certificateScalarResolvent_hasDerivAt (spectrum i) s z m hz)
  have h := (hasDerivAt_id m).sub (hsum.div_const (Fintype.card ι : ℂ))
  convert h using 1
  · ext w
    simp only [certificateDysonResidual, certificateAverage, Fintype.expect_eq_sum_div_card]
    rfl
  · simp only [certificateDysonJacobian, certificateAverage, Fintype.expect_eq_sum_div_card]
    rw [← Finset.mul_sum]
    ring

/-- Jensen's inequality gives a lower bound on the real part of the Jacobian at the reference
point. -/
theorem certificate_jacobian_lower_jensen [Nonempty ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E : ℝ} {μ : ℂ}
    (hc : 0 < c) (hμ : 0 < μ.im) :
    -(certificateChi F c E μ).im / μ.im +
        2 * c * (μ.im + (certificateChi F c E μ).im) ^ 2 ≤
      (certificateDysonJacobian hF.eigenvalues c (E : ℂ) μ).re := by
  rw [certificate_jacobian_identity F hF hc hμ]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * c)
  have hmean : certificateRealAverage (fun i =>
      (certificateScalarResolvent (hF.eigenvalues i) ((E : ℂ) + c * μ)).im) =
      μ.im + (certificateChi F c E μ).im := by
    rw [← certificateAverage_im]
    unfold certificateChi
    rw [certificateMatrixTrace_eq_average F hF]
    · simp
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        zero_mul, add_zero, zero_add]
      exact (mul_pos hc hμ).ne'
  rw [← hmean]
  exact certificate_jensen _

/-- Explicit dimension-uniform stability threshold, independent of the norm
or spectrum of F. The two smallness bounds depend only on c and Im μ. -/
theorem certificate_jacobian_stable [Nonempty ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E : ℝ} {μ : ℂ}
    (hc : 0 < c) (hμ : 0 < μ.im)
    (hv : ‖certificateChi F c E μ‖ ≤ μ.im / 2)
    (hs : ‖certificateChi F c E μ‖ ≤ c * μ.im ^ 3 / 4) :
    c * μ.im ^ 2 / 4 ≤
      (certificateDysonJacobian hF.eigenvalues c (E : ℂ) μ).re := by
  have hi := Complex.abs_im_le_norm (certificateChi F c E μ)
  have hchib := abs_le.mp (hi.trans hv)
  have hsum : μ.im / 2 ≤ μ.im + (certificateChi F c E μ).im := by linarith
  have hsum0 : 0 ≤ μ.im + (certificateChi F c E μ).im := by linarith
  have hsq : μ.im ^ 2 / 4 ≤ (μ.im + (certificateChi F c E μ).im) ^ 2 := by
    nlinarith [sq_nonneg (μ.im + (certificateChi F c E μ).im - μ.im / 2)]
  have hdiv : (certificateChi F c E μ).im / μ.im ≤ c * μ.im ^ 2 / 4 := by
    rw [div_le_iff₀ hμ]
    have := (abs_le.mp (hi.trans hs)).2
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * c)
  apply le_trans _ (certificate_jacobian_lower_jensen F hF hc hμ)
  simp only [neg_div]
  nlinarith

/-- The Jacobian at the reference point is nonzero under the trace certificate. -/
theorem certificate_jacobian_ne_zero [Nonempty ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E : ℝ} {μ : ℂ}
    (hc : 0 < c) (hμ : 0 < μ.im)
    (hv : ‖certificateChi F c E μ‖ ≤ μ.im / 2)
    (hs : ‖certificateChi F c E μ‖ ≤ c * μ.im ^ 3 / 4) :
    certificateDysonJacobian hF.eigenvalues c (E : ℂ) μ ≠ 0 := by
  intro heq
  have h := certificate_jacobian_stable F hF hc hμ hv hs
  rw [heq, Complex.zero_re] at h
  have hp : 0 < c * μ.im ^ 2 / 4 := by positivity
  linarith

end BlockBand.Palm
