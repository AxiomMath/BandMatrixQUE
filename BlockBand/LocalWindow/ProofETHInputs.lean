module

public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.External.NativeInputs

/-!
# The typical spacing and the eigenpair selection

Existence of the two auxiliary objects used by the external ETH theorem in part (ii) of the
physical local-window lemma.

## Main results

* `exists_eigenpairSelection`: a measurable increasing orthonormal eigenpair selection in every
  dimension `N > 0`.
* `exists_typicalSpacing`: a typical spacing for every branch, `N ≥ 4`, `λ > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofETH

open BlockBand.External BlockBand.Internal.Contracts.Inputs

/-- **The eigenpairs of the external eigenstate thermalization (ETH) theorem**: in every dimension
`N > 0` a measurable increasing orthonormal eigenpair selection exists
(`CEH.SourceContract.eigenpairs_exist`, read at the GUE family of `GUEWignerFamilyAdapter`).
-/
theorem exists_eigenpairSelection (inputs : NativeInputs.{0})
    (hAd : GUEWignerFamilyAdapter) (N : ℕ) (hN : 0 < N) :
    Nonempty (CEH.EigenpairSelection N) := by
  obtain ⟨Wf, -⟩ := hAd
  exact (inputs.ceh Wf).eigenpairs_exist N hN

/-- **The typical spacing `η_f` of the external ETH theorem** (defined by
`N η_f ρ(E + iη_f) = 1`, measurable in `E`): it exists for every branch, `N ≥ 4`,
`λ > 0` (`CEH.SourceContract.spacing_exists`). -/
theorem exists_typicalSpacing (inputs : NativeInputs.{0}) (hAd : GUEWignerFamilyAdapter)
    {N : ℕ} {lambda : ℝ} {H0 : CEH.SourceHermitian N} (hN : 4 ≤ N) (hl : 0 < lambda)
    (M : CEH.MDEBranch lambda H0) : Nonempty (CEH.TypicalSpacing M) := by
  obtain ⟨Wf, -⟩ := hAd
  exact (inputs.ceh Wf).spacing_exists hN hl M

end BlockBand.LocalWindow.ProofETH
