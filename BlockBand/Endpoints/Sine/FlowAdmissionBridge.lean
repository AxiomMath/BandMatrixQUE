module

public import BlockBand.Endpoints.Sine.FlowAdmission
public import BlockBand.Endpoints.Sine.LocalMassFlat

/-!
# Flow admission from local mass flatness

The pair clause of `LocalMassFlatStatement` gives `FaLocalMassFlatPair`
(`faLocalMassFlatPair_of_localMassFlat`), and hence `FlowAdmissionStatement`
(`flowAdmission_of_localMassFlat`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.Inputs

/-- The pair clause of local mass flatness, in the form used by flow admission. -/
theorem faLocalMassFlatPair_of_localMassFlat (h : LocalMassFlatStatement) :
    FaLocalMassFlatPair := by
  intro b hb hb' E hE1 hE2 T₀ hT₀ w hw hwin
  obtain ⟨C, hC⟩ := h b hb hb' E hE1 hE2 T₀ hT₀
  refine ⟨C, fun τ hτ hτT s R i ε hε => ?_⟩
  filter_upwards [hC w hw hwin τ hτ hτT s R i ε hε] with j hj
  exact hj.1

/-- Flow admission with its local-mass-flat input supplied by `LocalMassFlatStatement`. -/
theorem flowAdmission_of_localMassFlat (hPalm : ExactPalmContract) (hCo : CoareaContract)
    (hShift : FaShiftedMassPalm) (hCount : PhysicalBlockConditionalCount)
    (hLMF : LocalMassFlatStatement) : FlowAdmissionStatement :=
  flowAdmission hPalm hCo hShift hCount (faLocalMassFlatPair_of_localMassFlat hLMF)

end BlockBand.Endpoints
