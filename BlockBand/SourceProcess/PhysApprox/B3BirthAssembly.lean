module

public import BlockBand.SourceProcess.PhysApprox.B3BirthOld
public import BlockBand.SourceProcess.PhysApprox.B3BirthFresh

/-!
# The birth estimate `GenReqBirth` from six birth estimates

**`genReqBirth_of_pins`**: the birth half `GenReqBirth` of the generator estimates follows from
the six birth estimates below, which are hypotheses here (stated in sibling modules):
* `ComplexBirthOldL2` (one-step `L²` size of the old coordinates at a birth step),
* `ComplexBirthGramDiag` (closed `M_ii`, `B_ii` of a newborn tag `→ d_* m_i`),
* `ComplexBirthKFreshTrace` (path only: newest block `W⁻¹ Tr B → a`, `W⁻¹‖B‖_HS → 0`),
* `ComplexBirthKFreshCross` (unclosed `𝒦` old/new and new/new entries `→ 0`),
* `ComplexBirthKClosing` (closing correction of newborn `𝒦` entries `→ 0`),
* `ComplexBirthCrossGram` (closed Gram overlaps of a newborn column `→ 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

/-- **The birth half of the generator estimates from the six birth estimates.** -/
theorem genReqBirth_of_pins (hO : ComplexBirthOldL2) (hG : ComplexBirthGramDiag)
    (hT : ComplexBirthKFreshTrace) (hKX : ComplexBirthKFreshCross) (hC : ComplexBirthKClosing)
    (hGX : ComplexBirthCrossGram) : GenReqBirth :=
  genReqBirth_of_parts (complexBirthOld_of_L2 hO) hG
    (complexBirthKDiag_of_parts (complexBirthKFresh_of_trace hT) hC)
    (complexBirthCross_of_parts hGX (complexBirthCrossK_of_parts hKX hC))

end BlockBand.SourceProcess.PhysApprox.B3
