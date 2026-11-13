module

public import BlockBand.Native.CEH.ETH.BlockBand.Analysis.CauchyPoissonShifted
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Noncommuting matrix Cauchy–Poisson pencil

This module develops the noncommuting analytic matrix pencil behind the projected Wegner
estimate.  For Hermitian `A`, a positive-semidefinite
absorber `Q`, and `η > 0`, the pencil

`A + z Q + i η I`

has strictly positive matrix imaginary part throughout the closed upper half
plane.  We prove its invertibility there, the exact derivative of its inverse
and trace, and the nonnegativity and harmonicity of its negative-imaginary
trace in the open upper half plane.  These statements do not assume that `A`
and `Q` commute.

The Cauchy-average identity additionally needs the explicit bound
`-Im Tr R(z) ≤ card ι / η` (`neg_im_cauchyResolventTrace_le_card_div`) and a bounded
upper-half-plane Poisson representation (for matrix resolvent traces,
`BlockBand.Wegner.resolventTrace_poisson`); neither is used in this module.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix Set
open scoped ComplexOrder Matrix Matrix.Norms.L2Operator

namespace CEHNative.BlockBand

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The noncommuting matrix pencil used in the PSSS Poisson argument. -/
def cauchyResolventPencil
    (A Q : Matrix ι ι ℂ) (η : ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  A + z • Q + Complex.I • (η • (1 : Matrix ι ι ℂ))

/-- Its scalar trace resolvent. -/
def cauchyResolventTrace
    (A Q : Matrix ι ι ℂ) (η : ℝ) (z : ℂ) : ℂ :=
  (cauchyResolventPencil A Q η z)⁻¹.trace

omit [Fintype ι] in
/-- The pencil's matrix imaginary part is `Im(z) Q + η I`, without any
commutativity assumption. -/
theorem matrixImaginaryPart_cauchyResolventPencil
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (η : ℝ) (z : ℂ) :
    matrixImaginaryPart (cauchyResolventPencil A Q η z) =
      z.im • Q + η • (1 : Matrix ι ι ℂ) := by
  ext i j
  simp [cauchyResolventPencil, matrixImaginaryPart, hA.eq, hQ.eq]
  ring_nf
  rw [Complex.I_sq]
  simp
  apply Complex.ext <;> simp <;> ring

omit [Fintype ι] in
/-- Positive semidefiniteness of the pencil's imaginary part on the closed
upper half plane. -/
theorem matrixImaginaryPart_cauchyResolventPencil_posSemidef
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    (matrixImaginaryPart (cauchyResolventPencil A Q η z)).PosSemidef := by
  rw [matrixImaginaryPart_cauchyResolventPencil A Q hA hQ.isHermitian]
  exact (hQ.smul hz).add (Matrix.PosSemidef.one.smul hη.le)

omit [Fintype ι] in
/-- Strict positive definiteness supplied by the regulator. -/
theorem matrixImaginaryPart_cauchyResolventPencil_posDef
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    (matrixImaginaryPart (cauchyResolventPencil A Q η z)).PosDef := by
  rw [matrixImaginaryPart_cauchyResolventPencil A Q hA hQ.isHermitian]
  exact Matrix.PosDef.posSemidef_add (hQ.smul hz)
    (Matrix.PosDef.one.smul hη)

/-- There are no poles of the regulated pencil on the closed upper half
plane. -/
theorem isUnit_cauchyResolventPencil
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    IsUnit (cauchyResolventPencil A Q η z) :=
  isUnit_of_matrixImaginaryPart_posDef
    (matrixImaginaryPart_cauchyResolventPencil_posDef A Q hA hQ hη hz)

/-- Determinant version of pole exclusion. -/
theorem isUnit_det_cauchyResolventPencil
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    IsUnit (cauchyResolventPencil A Q η z).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp
    (isUnit_cauchyResolventPencil A Q hA hQ hη hz)

/-- The analytic-ring inverse agrees with the matrix nonsingular inverse at
an invertible matrix.  This bridges Mathlib's Banach-algebra calculus API to
the matrix resolvent notation. -/
theorem ringInverse_eq_nonsing_inv_of_isUnit
    (M : Matrix ι ι ℂ) (hM : IsUnit M) :
    Ring.inverse M = M⁻¹ := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  rw [Ring.inverse_of_isUnit hM]
  apply hM.mul_left_cancel
  calc
    M * (↑(hM.unit⁻¹) : Matrix ι ι ℂ) =
        (↑hM.unit : Matrix ι ι ℂ) * (↑(hM.unit⁻¹) : Matrix ι ι ℂ) :=
      congrArg (fun X : Matrix ι ι ℂ =>
        X * (↑(hM.unit⁻¹) : Matrix ι ι ℂ)) hM.unit_spec.symm
    _ = 1 := Units.mul_inv hM.unit
    _ = M * M⁻¹ := (M.mul_nonsing_inv hdet).symm

/-- The trace built from the analytic ring inverse.  On the regulated closed
upper half plane it agrees with `cauchyResolventTrace`. -/
def cauchyAnalyticResolventTrace
    (A Q : Matrix ι ι ℂ) (η : ℝ) (z : ℂ) : ℂ :=
  (Ring.inverse (cauchyResolventPencil A Q η z)).trace

/-- Agreement of the analytic trace and the matrix-resolvent trace on
the closed upper half plane. -/
theorem cauchyAnalyticResolventTrace_eq
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    cauchyAnalyticResolventTrace A Q η z =
      cauchyResolventTrace A Q η z := by
  rw [cauchyAnalyticResolventTrace, cauchyResolventTrace,
    ringInverse_eq_nonsing_inv_of_isUnit _
      (isUnit_cauchyResolventPencil A Q hA hQ hη hz)]

/-- Exact complex derivative of the (noncommuting) analytic-ring matrix resolvent. -/
theorem hasDerivAt_cauchyResolventPencil_ringInverse
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    HasDerivAt
      (fun w : ℂ => Ring.inverse (cauchyResolventPencil A Q η w))
      (-((cauchyResolventPencil A Q η z)⁻¹ * Q *
        (cauchyResolventPencil A Q η z)⁻¹)) z := by
  let M := cauchyResolventPencil A Q η z
  have hM : IsUnit M := isUnit_cauchyResolventPencil A Q hA hQ hη hz
  have hp0 := ((((hasDerivAt_id z).smul_const Q).const_add A).add_const
    (Complex.I • (η • (1 : Matrix ι ι ℂ))))
  have hp : HasDerivAt (cauchyResolventPencil A Q η) Q z := by
    convert hp0 using 1
    · funext w
      rfl
    · simp
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℂ) hM.unit).comp_hasDerivAt z hp
  convert hi using 1
  · funext w
    rfl
  · have huinv : (↑(hM.unit⁻¹) : Matrix ι ι ℂ) = M⁻¹ := by
      rw [← Ring.inverse_of_isUnit hM]
      exact ringInverse_eq_nonsing_inv_of_isUnit M hM
    simp [huinv, M]

/-- The analytic scalar trace resolvent is holomorphic at every point of the
open upper half plane. -/
theorem analyticAt_cauchyAnalyticResolventTrace
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (cauchyAnalyticResolventTrace A Q η) z := by
  let M := cauchyResolventPencil A Q η z
  have hM : IsUnit M :=
    isUnit_cauchyResolventPencil A Q hA hQ hη hz.le
  have hp : AnalyticAt ℂ (cauchyResolventPencil A Q η) z := by
    unfold cauchyResolventPencil
    fun_prop
  have hinv : AnalyticAt ℂ Ring.inverse M := by
    rw [← hM.unit_spec]
    exact analyticAt_inverse (𝕜 := ℂ) hM.unit
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap ι ℂ ℂ)
  have htr : AnalyticAt ℂ (fun X : Matrix ι ι ℂ => tr X)
      (Ring.inverse M) := tr.analyticAt _
  have htri : AnalyticAt ℂ (fun X : Matrix ι ι ℂ => tr (Ring.inverse X)) M :=
    htr.comp hinv
  have ht := htri.comp hp
  change AnalyticAt ℂ
    (fun w => (Ring.inverse (cauchyResolventPencil A Q η w)).trace) z
  simpa [tr, Function.comp_def] using ht

/-- The matrix-resolvent trace itself is holomorphic throughout the
open upper half plane.  The proof transfers analyticity from the ring inverse
using pole exclusion on a neighborhood of the point. -/
theorem analyticAt_cauchyResolventTrace
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (cauchyResolventTrace A Q η) z := by
  apply (analyticAt_cauchyAnalyticResolventTrace A Q hA hQ hη hz).congr
  have hopen : IsOpen {w : ℂ | 0 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact cauchyAnalyticResolventTrace_eq A Q hA hQ hη hw.le

/-- The ordinary negative-imaginary matrix trace is harmonic in
the open upper half plane, with no simultaneous diagonalization. -/
theorem harmonicAt_neg_im_cauchyResolventTrace
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 < z.im) :
    InnerProductSpace.HarmonicAt
      (fun w : ℂ => -(cauchyResolventTrace A Q η w).im) z := by
  exact (analyticAt_cauchyResolventTrace A Q hA hQ hη hz).harmonicAt_im.neg

/-- Analytic-ring form of the same harmonicity statement. -/
theorem harmonicAt_neg_im_cauchyAnalyticResolventTrace
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 < z.im) :
    InnerProductSpace.HarmonicAt
      (fun w : ℂ => -(cauchyAnalyticResolventTrace A Q η w).im) z := by
  exact (analyticAt_cauchyAnalyticResolventTrace A Q hA hQ hη hz).harmonicAt_im.neg

/-- The negative imaginary trace of the matrix resolvent is nonnegative
throughout the closed upper half plane.  This is the positivity input for
Tonelli in the projected Wegner argument. -/
theorem neg_im_cauchyResolventTrace_nonneg
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    0 ≤ -(cauchyResolventTrace A Q η z).im := by
  let M := cauchyResolventPencil A Q η z
  have hMdet : IsUnit M.det :=
    isUnit_det_cauchyResolventPencil A Q hA hQ hη hz
  have him : (matrixImaginaryPart M).PosSemidef :=
    matrixImaginaryPart_cauchyResolventPencil_posSemidef A Q hA hQ hη hz
  have hneg : (-matrixImaginaryPart M⁻¹).PosSemidef :=
    neg_matrixImaginaryPart_nonsing_inv_posSemidef M hMdet him
  have htrace := hneg.trace_nonneg
  rw [trace_neg_matrixImaginaryPart] at htrace
  have hre := (RCLike.nonneg_iff.mp htrace).1
  simpa [cauchyResolventTrace, M] using hre

omit [Fintype ι] in
/-- Boundary specialization: on the real axis the matrix pencil is the
Hermitian background `A + tQ` with regulator `iηI`. -/
theorem cauchyResolventPencil_ofReal
    (A Q : Matrix ι ι ℂ) (η t : ℝ) :
    cauchyResolventPencil A Q η (t : ℂ) =
      A + (t : ℂ) • Q + Complex.I • (η • (1 : Matrix ι ι ℂ)) := rfl

omit [Fintype ι] in
/-- Interior specialization at `i`: Cauchy dilation adds the absorber `Q` to
the regulator, exactly as in the PSSS normalization. -/
theorem cauchyResolventPencil_I
    (A Q : Matrix ι ι ℂ) (η : ℝ) :
    cauchyResolventPencil A Q η Complex.I =
      A + Complex.I • (Q + η • (1 : Matrix ι ι ℂ)) := by
  ext i j
  simp [cauchyResolventPencil]
  ring

end CEHNative.BlockBand
