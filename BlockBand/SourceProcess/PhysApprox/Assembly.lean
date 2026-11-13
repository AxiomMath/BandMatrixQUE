module

public import BlockBand.SourceProcess.PhysApprox.Pins
public import BlockBand.SourceProcess.PhysApprox.PinsIdent
public import BlockBand.SourceProcess.PhysApprox.Bridge

/-!
# Assembly of the frequent-`h` physical approximation

The physical approximation `ComplexPhysicalApproximationFreq` follows from the closing error (a)
`ComplexClosingError` and the closed identification (b) `ComplexClosedIdentification`. This file
states the intermediate implications as propositions `TargetT*` and proves that they compose.

## Main results

* `complexPhysicalApproximationFreq_of_pins`: (a) and (b) give `ComplexPhysicalApproximationFreq`.
* `complexPhysicalApproximationFreq_of_targets`: the propositions below compose to `TargetT9`,
  the implication from the hypotheses and `KolmogorovConjugate`, `ComplexClosedLimitLaw` to
  `ComplexPhysicalApproximationFreq`. It is conditional on the propositions and proves none of them.

The propositions:

* `TargetT1`: (a1) `KClosingFractional` and (a2) `GramClosingSmall` ⇒ (a) `ComplexClosingError`;
* `TargetT2`: `KolmogorovConjugate` and (L) `TagChannelLeakage` ⇒ (a1);
* `TargetT3`: (L) and (Lo) `TagChannelLeakageOut` ⇒ (a2);
* `TargetT4`: (L) ⇒ (Lo);
* `TargetTL`: the hypotheses ⇒ (L);
* `TargetT6`: (b1) `ComplexCappedClosedIdentification` ⇒ (b);
* `TargetT7`: (b2) `ComplexClosedLimitIdentification` ⇒ (b1);
* `TargetT8`: (b3) `ComplexClosedLimitLaw` ⇒ (b2), and `TargetT8Stopped`: the stopped law
  `ComplexClosedLimitLawStopped` ⇒ (b2).

Where they appear, "the hypotheses" are the five assumptions `MatchedTracesContract`,
`GaussianAbsorptionContract`, `ScalarRecursionContract`, `GaussianLpGradient`, `GaussianPoincare`,
in this order.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct

/-!
## The closing error and the identification give the physical approximation
-/

/-- The closing error (a), eventually in `h`, and the closed identification (b), frequently in
`h` and `K`, give `ComplexPhysicalApproximationFreq` (triangle inequality at `ε/2`). -/
theorem complexPhysicalApproximationFreq_of_pins (hA : ComplexClosingError)
    (hB : ComplexClosedIdentification) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq := by
  refine complexFreq_iff.1 ?_
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ ε hε
  have ha := hA b E np τ m T hD s hs hτ Φ (ε / 2) (by linarith)
  have hb := hB b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ (ε / 2) (by linarith)
  refine (ha.and_frequently hb).mono fun h ⟨hah, hbh⟩ => hbh.mono fun K hK v hv => ?_
  filter_upwards [hah, hK v hv] with W h1 h2
  calc |physExpectation b E T τ m Φ W - v|
      ≤ |physExpectation b E T τ m Φ W - closedPhysExpectation b E s T h τ m Φ W| +
        |closedPhysExpectation b E s T h τ m Φ W - v| := abs_sub_le _ _ _
    _ ≤ ε := by linarith

/-!
## The intermediate implications
-/

/-- The entrywise closing errors (a1), (a2) give the closing error (a) for bounded continuous
tests (tightness of the source data, Markov's inequality per entry, uniform continuity of `Φ` on a
compact set). -/
def TargetT1 : Prop :=
  Layers.MatchedTracesContract → Layers.GaussianAbsorptionContract →
    Layers.ScalarRecursionContract → Inputs.GaussianLpGradient → Inputs.GaussianPoincare →
    KClosingFractional → GramClosingSmall → ComplexClosingError

/-- Kolmogorov's conjugate inequality and the input leakage (L) give the fractional closing
error (a1) of `𝒦`. -/
def TargetT2 : Prop :=
  Layers.MatchedTracesContract → Layers.GaussianAbsorptionContract →
    Layers.ScalarRecursionContract → Inputs.GaussianLpGradient → Inputs.GaussianPoincare →
    KolmogorovConjugate → TagChannelLeakage → KClosingFractional

/-- The input and output leakages (L), (Lo) give the closing error (a2) of the Gram coordinates
and the current. -/
def TargetT3 : Prop :=
  Layers.MatchedTracesContract → Layers.GaussianAbsorptionContract →
    Layers.ScalarRecursionContract → Inputs.GaussianLpGradient → Inputs.GaussianPoincare →
    TagChannelLeakage → TagChannelLeakageOut → GramClosingSmall

/-- The output leakage (Lo) follows from the input leakage (L), by entrywise conjugation of the
path. -/
def TargetT4 : Prop :=
  TagChannelLeakage → TagChannelLeakageOut

/-- The input leakage (L) of one normalized tag holds under the hypotheses. -/
def TargetTL : Prop :=
  Layers.MatchedTracesContract → Layers.GaussianAbsorptionContract →
    Layers.ScalarRecursionContract → Inputs.GaussianLpGradient → Inputs.GaussianPoincare →
    TagChannelLeakage

/-- Cap removal on both sides (physical side: `P_W(physCapEventCᶜ)` is small; model side: the
entrance tail) turns the capped identification (b1) into (b). -/
def TargetT6 : Prop :=
  Layers.MatchedTracesContract → Layers.GaussianAbsorptionContract →
    Layers.ScalarRecursionContract → Inputs.GaussianLpGradient → Inputs.GaussianPoincare →
    ComplexCappedClosedIdentification → ComplexClosedIdentification

/-- Bounded sequences whose limit points are restricted model values converge to them
(restricted uniqueness), so (b2) gives (b1). -/
def TargetT7 : Prop :=
  ComplexClosedLimitIdentification → ComplexCappedClosedIdentification

/-- A tested complex model is a filtered complex finite model (natural filtration of
`complexObs`, optional stopping), so (b3) gives (b2). -/
def TargetT8 : Prop :=
  ComplexClosedLimitLaw → ComplexClosedLimitIdentification

/-- **T8, stopped fallback**: the stopped form of (b3)
gives (b2) without optional stopping.
-/
def TargetT8Stopped : Prop :=
  ComplexClosedLimitLawStopped → ComplexClosedLimitIdentification

/-- The hypotheses, `KolmogorovConjugate` and (b3) `ComplexClosedLimitLaw` give
`ComplexPhysicalApproximationFreq`; `complexPhysicalApproximationFreq_of_targets` proves it from
the other targets.
-/
def TargetT9 : Prop :=
  Layers.MatchedTracesContract → Layers.GaussianAbsorptionContract →
    Layers.ScalarRecursionContract → Inputs.GaussianLpGradient → Inputs.GaussianPoincare →
    KolmogorovConjugate → ComplexClosedLimitLaw →
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq

/-!
## The implications compose
-/

/-- **Composition**: `TargetTL`, `TargetT4`, `TargetT3`, `TargetT2`, `TargetT1` give (a);
`TargetT8`, `TargetT7`, `TargetT6` give (b); then `complexPhysicalApproximationFreq_of_pins`. -/
theorem complexPhysicalApproximationFreq_of_targets (t1 : TargetT1) (t2 : TargetT2)
    (t3 : TargetT3) (t4 : TargetT4) (tL : TargetTL) (t6 : TargetT6) (t7 : TargetT7)
    (t8 : TargetT8) : TargetT9 := by
  intro hMT hGA hSR hLp hP hK hLaw
  have hL := tL hMT hGA hSR hLp hP
  exact complexPhysicalApproximationFreq_of_pins
    (t1 hMT hGA hSR hLp hP (t2 hMT hGA hSR hLp hP hK hL) (t3 hMT hGA hSR hLp hP hL (t4 hL)))
    (t6 hMT hGA hSR hLp hP (t7 (t8 hLaw)))

end BlockBand.SourceProcess.PhysApprox
