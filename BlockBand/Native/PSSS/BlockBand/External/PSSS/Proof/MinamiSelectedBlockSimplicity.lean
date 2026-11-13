module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiInductionBase
public import Mathlib.MeasureTheory.Function.Floor
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerSelectedBlockSchur
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.SingleBlockDOSFiniteGrid

/-!
# Almost-sure simplicity in a selected public block

Evaluation of the singleton selected-block product has exactly the normalized
public GUE law.  Therefore every deterministic Hermitian deformation of that
selected block has simple ordered spectrum almost surely.  This is the
simplicity input for the auxiliary Minami cell partition.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set

/-- A deterministically deformed selected block has simple ordered spectrum
almost surely under the selected singleton measure. -/
theorem ae_selectedBlock_addHermitian_orderedEigenvalue_injective
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A : HermitianMatrix (Fin (dims j))) :
    ∀ᵐ Gj ∂BlockProductDisintegration.selectedMeasure dims hd j,
      Function.Injective
        (orderedEigenvalue (addHermitian A (Gj ⟨j, by simp⟩))) := by
  have h := ae_publicGUE_addHermitian_orderedEigenvalue_injective (hd j) A
  exact (measurePreserving_selectedMeasure_eval dims hd j).quasiMeasurePreserving.ae h

end PSSSNative.BlockBand.PSSS
