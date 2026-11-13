module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2KStopFin
public import BlockBand.SourceProcess.PhysApprox.B3Ident2Entr

/-!
# `TargetCapIdentAll` from three estimates

`CapIdentKStop` is proved (`capIdentKStop_holds`). What is left of `TargetCapIdentAll` are the
estimates `CapIdentEntrance`, `CapIdentGram` and `CapIdentKDouble`.

* **`targetCapIdentAll_of_three`**: `CapIdentEntrance → CapIdentGram → CapIdentKDouble →
  TargetCapIdentAll`.
* **`targetCapCond'_of_three`**: the same three estimates give `TargetCapCond'` (with
  `Fdd.targetCapFddAll_holds`).
* **`targetCapCond'_of_entranceFdd`**: `CapIdentEntrance` replaced by its finite-dimensional core
  `CapIdentEntranceFdd` (`capIdentEntrance_of_fdd`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

/-- **`TargetCapIdentAll` from the three remaining estimates.** -/
theorem targetCapIdentAll_of_three (hEnt : CapIdentEntrance) (hGr : CapIdentGram)
    (hKD : CapIdentKDouble) : TargetCapIdentAll :=
  targetCapIdentAll_of_pins hEnt hGr hKD capIdentKStop_holds

/-- **`TargetCapCond'` from the three remaining estimates.** -/
theorem targetCapCond'_of_three (hEnt : CapIdentEntrance) (hGr : CapIdentGram)
    (hKD : CapIdentKDouble) : TargetCapCond' :=
  targetCapCond'_of_identPins hEnt hGr hKD capIdentKStop_holds

/-- **`TargetCapCond'` from `CapIdentEntranceFdd`, `CapIdentGram` and `CapIdentKDouble`.** -/
theorem targetCapCond'_of_entranceFdd (hEF : CapIdentEntranceFdd) (hGr : CapIdentGram)
    (hKD : CapIdentKDouble) : TargetCapCond' :=
  targetCapCond'_of_three (capIdentEntrance_of_fdd hEF) hGr hKD

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
