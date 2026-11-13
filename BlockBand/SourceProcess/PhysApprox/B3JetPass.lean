module

public import BlockBand.SourceProcess.PhysApprox.B3JetMain
public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm

/-!
# Passivity of the closed input `b3ClosedX`

* **`closedInputPassive_b3ClosedX`**: `ClosedInputPassive b3ClosedX` holds, by
  `ae_passive_b3ClosedX`, at every step, for `W ≥ 1`, with `h² < 1` from `FrameDomain`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Filter

/-- **`ClosedInputPassive b3ClosedX`**, from `ae_passive_b3ClosedX`. -/
theorem closedInputPassive_b3ClosedX : ClosedInputPassive b3ClosedX := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, -, -, hh0, hh1, -⟩ := id hF
  have hh : h ^ 2 < 1 := by nlinarith
  filter_upwards [eventually_ge_atTop 1] with W hW j _
  exact ae_passive_b3ClosedX hb0 hb hE1 hE2 s h hh τ m hW j

end BlockBand.SourceProcess.PhysApprox.B3.Jet
