module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhaseFixedHouseholderUnitarity
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairCoareaAssembly
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Fixed-frame smooth conjugation for eigenpair charts

This module supplies the exact smooth two-sided matrix-conjugation component of
an eigenpair chart once its phase-fixed eigenline has been chosen.  Conjugation
by the explicit Householder frame is packaged as a complex continuous linear
equivalence, so its inverse identities, injectivity, and Fréchet derivative are
available without any further geometric assumption.

The rest of the chart is not constructed here: the real coordinates that split
the conjugated Hermitian matrix into the selected energy, the `(d-1)`-dimensional
Hermitian complementary block, and the projective coordinate, and the derivative
of the *moving* Householder frame, are those of `coherentSelectedEigenpairDecode`
(`hasFDerivAt_coherentSelectedEigenpairDecode`,
`contDiff_coherentSelectedEigenpairDecode`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- Conjugation by a unitary matrix, as a complex-linear equivalence. -/
def unitaryConjugationLinearEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ * H = 1) :
    Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ where
  toFun A := Hᴴ * A * H
  invFun A := H * A * Hᴴ
  left_inv A := by
    have hH' : H * Hᴴ = 1 := mul_eq_one_comm.mp hH
    calc
      H * (Hᴴ * A * H) * Hᴴ = (H * Hᴴ) * A * (H * Hᴴ) := by
        noncomm_ring
      _ = A := by rw [hH']; simp
  right_inv A := by
    calc
      Hᴴ * (H * A * Hᴴ) * H = (Hᴴ * H) * A * (Hᴴ * H) := by
        noncomm_ring
      _ = A := by rw [hH]; simp
  map_add' A B := by simp [mul_add, add_mul]
  map_smul' c A := by
    ext a b
    simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    ring_nf

/-- The inverse map of unitary conjugation is conjugation in the opposite
order. -/
theorem unitaryConjugationLinearEquiv_symm_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ * H = 1) (A : Matrix ι ι ℂ) :
    (unitaryConjugationLinearEquiv H hH).symm A = H * A * Hᴴ :=
  rfl

/-- Finite-dimensional unitary conjugation is a continuous linear equivalence. -/
def unitaryConjugationContinuousLinearEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ * H = 1) :
    Matrix ι ι ℂ ≃L[ℂ] Matrix ι ι ℂ :=
  (unitaryConjugationLinearEquiv H hH).toContinuousLinearEquiv

/-- Its Fréchet derivative at every matrix is the same fixed conjugation map. -/
theorem hasFDerivAt_unitaryConjugation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ * H = 1) (A : Matrix ι ι ℂ) :
    HasFDerivAt (fun K : Matrix ι ι ℂ => Hᴴ * K * H)
      (unitaryConjugationContinuousLinearEquiv H hH).toContinuousLinearMap A := by
  exact (unitaryConjugationContinuousLinearEquiv H hH).toContinuousLinearMap.hasFDerivAt

/-- Unitary conjugation preserves Hermitian matrices. -/
theorem isHermitian_unitaryConjugation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (Hᴴ * A * H).IsHermitian := by
  change (Hᴴ * A * H)ᴴ = Hᴴ * A * H
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA.eq]
  noncomm_ring

/-- The explicit phase-fixed Householder frame gives a canonical smooth linear
coordinate change for every unit vector in its positive-real chart. -/
def phaseFixedHouseholderConjugation
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v i = ((v i).re : ℂ))
    (hpos : 0 < (v i).re) :
    Matrix ι ι ℂ ≃L[ℂ] Matrix ι ι ℂ :=
  unitaryConjugationContinuousLinearEquiv
    (phaseFixedHouseholderFrame i v)
    (phaseFixedHouseholderFrame_unitary i v hv hreal hpos)

/-- Explicit formula for the forward Householder coordinate map. -/
theorem phaseFixedHouseholderConjugation_apply
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v i = ((v i).re : ℂ))
    (hpos : 0 < (v i).re) (A : Matrix ι ι ℂ) :
    phaseFixedHouseholderConjugation i v hv hreal hpos A =
      (phaseFixedHouseholderFrame i v)ᴴ * A *
        phaseFixedHouseholderFrame i v :=
  rfl

/-- Explicit formula for decoding Householder coordinates. -/
theorem phaseFixedHouseholderConjugation_symm_apply
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v i = ((v i).re : ℂ))
    (hpos : 0 < (v i).re) (A : Matrix ι ι ℂ) :
    (phaseFixedHouseholderConjugation i v hv hreal hpos).symm A =
      phaseFixedHouseholderFrame i v * A *
        (phaseFixedHouseholderFrame i v)ᴴ :=
  rfl

/-- Encoding after decoding is exactly the identity. -/
theorem phaseFixedHouseholder_encode_decode
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v i = ((v i).re : ℂ))
    (hpos : 0 < (v i).re) (A : Matrix ι ι ℂ) :
    phaseFixedHouseholderConjugation i v hv hreal hpos
      ((phaseFixedHouseholderConjugation i v hv hreal hpos).symm A) = A :=
  (phaseFixedHouseholderConjugation i v hv hreal hpos).apply_symm_apply A

/-- Decoding after encoding is exactly the identity. -/
theorem phaseFixedHouseholder_decode_encode
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v i = ((v i).re : ℂ))
    (hpos : 0 < (v i).re) (A : Matrix ι ι ℂ) :
    (phaseFixedHouseholderConjugation i v hv hreal hpos).symm
      (phaseFixedHouseholderConjugation i v hv hreal hpos A) = A :=
  (phaseFixedHouseholderConjugation i v hv hreal hpos).symm_apply_apply A

/-- The fixed-frame decoding map is injective. -/
theorem injective_phaseFixedHouseholder_decode
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v i = ((v i).re : ℂ))
    (hpos : 0 < (v i).re) :
    Function.Injective
      (phaseFixedHouseholderConjugation i v hv hreal hpos).symm :=
  (phaseFixedHouseholderConjugation i v hv hreal hpos).symm.injective

/-- The ordered eigenline chart therefore has an unconditional fixed-frame
continuous linear equivalence on ambient matrices. -/
def orderedEigenlineHouseholderConjugation
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    Matrix (Fin d) (Fin d) ℂ ≃L[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  phaseFixedHouseholderConjugation (ofLex p).1
    (orderedEigenlineChartCandidate d r p x)
    (norm_projectiveUnitReconstruction _ _)
    (by
      apply Complex.ext
      · rfl
      · simpa using orderedEigenlineChartCandidate_selectedCoordinate_im r p x)
    (orderedEigenlineChartCandidate_selectedCoordinate_re_pos r p x)

/-- The selected chart's fixed-frame conjugation is Fréchet differentiable in
the matrix variable. -/
theorem hasFDerivAt_orderedEigenlineHouseholderConjugation
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    HasFDerivAt (orderedEigenlineHouseholderConjugation r p x)
      (orderedEigenlineHouseholderConjugation r p x).toContinuousLinearMap A := by
  exact (orderedEigenlineHouseholderConjugation r p x).toContinuousLinearMap.hasFDerivAt

end CoareaNative.BlockBand
