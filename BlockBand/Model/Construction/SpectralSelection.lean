module

public import BlockBand.Model.Construction.OrderedSelection
public import BlockBand.Model.Construction.SpectralEigenvalues

/-!
# Raw-matrix measurable ordered eigenvector selection

The explicit first-positive-projector-column eigenvector selection, extended by zero to all raw
matrices outside the Hermitian locus. Its coordinates and site masses are Borel measurable, and it
agrees with the Hermitian-domain selection on Hermitian matrices.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit ordered column selection on raw matrices, with zero defaults. -/
def rawOrderedColumnSelection (i : Fin (Fintype.card ι))
    (A : Matrix ι ι ℂ) (x : ι) : ℂ :=
  rawHermitianExtension (fun B => orderedColumnSelection i B x) 0 A

/-- Every raw selected eigenvector coordinate is Borel measurable. -/
theorem measurable_rawOrderedColumnSelection (i : Fin (Fintype.card ι)) (x : ι) :
    Measurable (fun A : Matrix ι ι ℂ => rawOrderedColumnSelection i A x) :=
  measurable_rawHermitianExtension _ (measurable_orderedColumnSelection i x) 0

/-- Every raw selected site mass is Borel measurable. -/
theorem measurable_rawOrderedSiteMass (i : Fin (Fintype.card ι)) (x : ι) :
    Measurable (fun A : Matrix ι ι ℂ => ‖rawOrderedColumnSelection i A x‖ ^ 2) :=
  (measurable_rawOrderedColumnSelection i x).norm.pow_const 2

/-- The raw selection agrees pointwise with the Hermitian-domain selection. -/
theorem rawOrderedColumnSelection_eq (i : Fin (Fintype.card ι))
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (x : ι) :
    rawOrderedColumnSelection i A x = orderedColumnSelection i ⟨A, hA⟩ x :=
  rawHermitianExtension_eq _ _ A hA

end BlockBand.Model.Construction
