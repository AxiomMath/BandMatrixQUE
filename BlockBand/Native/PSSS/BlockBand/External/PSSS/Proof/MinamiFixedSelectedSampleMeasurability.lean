module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedPredecessorWeight

/-!
# Measurability of the fixed-target selected-block reconstruction

This small module isolates the dependent singleton selected-sample map used in
PSSS (2.13), avoiding elaboration of the subsequent spectral weight at the
same time.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 300000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- Hermitian totalization of a selected matrix is measurable as a value of
the singleton dependent selected-sample space. -/
theorem measurable_selectedSampleOfMatrix
    {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :
    Measurable (selectedSampleOfMatrix (dims := dims) j) := by
  rw [measurable_pi_iff]
  intro q
  rcases q with ⟨i, hi⟩
  have hij : i = j := not_ne_iff.mp hi
  subst i
  change Measurable (fun X : Matrix (Fin (dims j)) (Fin (dims j)) ℂ =>
    (⟨PSSSNative.BlockBand.matrixHermitianPart X,
      PSSSNative.BlockBand.matrixHermitianPart_isHermitian X⟩ :
      HermitianMatrix (Fin (dims j))))
  apply Measurable.subtype_mk
  exact PSSSNative.BlockBand.Measurable.matrixHermitianPart
    measurable_id

end PSSSNative.BlockBand.PSSS
