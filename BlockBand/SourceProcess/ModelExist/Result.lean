module

public import BlockBand.SourceProcess.ModelExist.Final
public import BlockBand.SourceProcess.ModelExist.SelectProp

/-!
# The positive finite source model exists

`modelExists_holds`: `ModelExists` holds, since the perpendicular selection exists for every
finite column type.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.ModelExist

/-- The perpendicular selection exists for every finite column type (`perpSelection_holds`). -/
theorem perpSelectionHolds : PerpSelectionHolds := fun _ _ _ _ cur _ => perpSelection_holds cur

/-- **`ModelExists` holds.** -/
theorem modelExists_holds : BlockBand.SourceProcess.SourceProcessLaw.ModelExists :=
  modelExists_of_perpSelection perpSelectionHolds

end BlockBand.SourceProcess.ModelExist
