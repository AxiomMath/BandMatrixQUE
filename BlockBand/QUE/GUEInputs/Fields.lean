module

public import BlockBand.External.CEH.SourceStatement

/-!
# GUE-inputs QUE chain: the two deterministic CEH field types

The QUE chain reads its input `inputs : NativeInputs.{0}` only as
`(inputs.ceh Wf).eigenpairs_exist` and `(inputs.ceh Wf).spacing_exists`. Both fields of
`External.CEH.SourceContract W` are independent of the Wigner family `W`. This file names their
types:
* `EigenpairsExist`: the type of the `eigenpairs_exist` field;
* `SpacingExists`: the type of the `spacing_exists` field.

The theorems `eigenpairsExist_of_sourceContract` and `spacingExists_of_sourceContract` check,
by elaboration, that each field has exactly this type.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.QUE.GUEInputs

open BlockBand.External.CEH

/-- The type of the field `eigenpairs_exist` of `External.CEH.SourceContract W`: a measurable
increasing orthonormal eigenpair selection in every dimension `N > 0`. -/
abbrev EigenpairsExist : Prop :=
  ∀ (N : ℕ), 0 < N → Nonempty (EigenpairSelection N)

/-- The type of the field `spacing_exists` of `External.CEH.SourceContract W`: a typical spacing
for every MDE branch, `N ≥ 4`, `λ > 0`. -/
abbrev SpacingExists : Prop :=
  ∀ {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N},
    4 ≤ N → 0 < lambda → ∀ M : MDEBranch lambda H0, Nonempty (TypicalSpacing M)

/-- The field `eigenpairs_exist` of any `External.CEH.SourceContract W` has type
`EigenpairsExist`. -/
theorem eigenpairsExist_of_sourceContract {W : WignerFamily} (c : SourceContract W) :
    EigenpairsExist :=
  c.eigenpairs_exist

/-- The field `spacing_exists` of any `External.CEH.SourceContract W` has type
`SpacingExists`. -/
theorem spacingExists_of_sourceContract {W : WignerFamily} (c : SourceContract W) :
    SpacingExists :=
  c.spacing_exists

end BlockBand.QUE.GUEInputs
