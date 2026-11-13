module

public import BlockBand.SourceProcess.PhysApprox.Defs

/-!
# The intermediate statements of the physical approximation

Measures: `probedPathLaw W np b` (path ⊗ independent circular probes) times `phaseLaw` (uniform
phase on `[0, 2π)`), and `growthPathLaw W b`. Domain: `ComplexSourceLawDomain b E τ m T`, closing time
`0 < s < min τ_j`. Uniformity: every statement of the closing part (a) is
`∀ᶠ h in 𝓝[>] 0, ∀ᶠ W`, with no cap (uniform in `K`); every statement of the identification part
(b) is `∃ᶠ h in 𝓝[>] 0, ∃ᶠ K` (the frequent form of the target).

* (a) `ComplexClosingError` ⇐ (a1) `KClosingFractional` + (a2) `GramClosingSmall` (`TargetT1`).
* (a1) ⇐ `KolmogorovConjugate` + (L) `TagChannelLeakage` (`TargetT2`).
* (a2) ⇐ (L) + (Lo) `TagChannelLeakageOut` (`TargetT3`); (Lo) ⇐ (L) (`TargetT4`, conjugation
  symmetry).
* (b) `ComplexClosedIdentification` ⇐ (b1) `ComplexCappedClosedIdentification` (`TargetT6`)
  ⇐ (b2) `ComplexClosedLimitIdentification` (`TargetT7`) ⇐ (b3) `ComplexClosedLimitLaw`
  (`TargetT8`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open scoped NNReal

/-!
## (a) Closing error
-/

/-- **(a) Closing error** (uniformly in the source sample size): eventually as `h ↓ 0`, for all
large `W`, the physical expectation is within `ε` of the closed one. There is no cap, so this is
uniform in `K`. -/
def ComplexClosingError : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᶠ W in atTop,
    |physExpectation b E T τ m Φ W - closedPhysExpectation b E s T h τ m Φ W| ≤ ε

/-- **(a1) Fractional moments of the closing error of `𝒦`** (Kolmogorov for the real part,
`Im 𝒦_cl - Im 𝒦 = -η(M_cl - M)` for the imaginary part, polarization, `p < 1`), entrywise, as a
lower Lebesgue integral. -/
def KClosingFractional : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ p : ℝ, 0 < p → p < 1 → ∀ (i k : Fin np) (ε : ℝ), 0 < ε →
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᶠ W in atTop,
      ∫⁻ y, ENNReal.ofReal (‖closedK b E s T h τ m W (phase y.2) y.1 i k -
          complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m y.1 i k‖ ^ p)
        ∂((probedPathLaw W np b).prod phaseLaw) ≤ ENNReal.ofReal ε

/-- **(a2) Closing error of the Gram coordinates and the current** (for `M_pr` and `B_pr`,
`r = 1, 2`; for `J_pr`, `r = 3`, the output-side leakage (Lo) is also needed), entrywise in `L¹`,
as a lower Lebesgue integral. -/
def GramClosingSmall : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ r : Fin 4, r ≠ 0 → ∀ (i k : Fin np) (ε : ℝ), 0 < ε →
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᶠ W in atTop,
      ∫⁻ y, ENNReal.ofReal (‖closedSourceData b E s T h τ m W (phase y.2) y.1 r i k -
          complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m y.1 r i k‖)
        ∂((probedPathLaw W np b).prod phaseLaw) ≤ ENNReal.ofReal ε

/-- **(L) Input-side leakage of one normalized tag** (the small channel leakage, for one tag at
`τ`, uniform for finite positive source families): `E Tr(A_- Y_{⌊WT⌋;⌊Wτ⌋})/W` is eventually
small, `A_-` the omitted far input projection at `⌊Ws⌋`. Stated with `∫⁻ ofReal`, so that
consumers need no integrability. The integrand is pathwise nonnegative (`A_-` is a projection,
`Y ⪰ 0`), so this is the same statement as the bound on the mean.
-/
def TagChannelLeakage : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ T : ℝ, 0 < s → s < τ → τ < T →
  ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᶠ W in atTop,
    ∫⁻ ω, ENNReal.ofReal ((farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
        tagResponse b E W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ⌋₊ ω).trace.re / W)
      ∂growthPathLaw W b ≤ ENNReal.ofReal ε

/-- PLAN §1.8, the unwritten
step for `J_pr`): with `A_+ = Πᴴ Π`, `E Tr(A_+ 𝕊 Y 𝕊ᴴ)/W` is eventually small.
Pathwise equal to
the (L) integrand at the entrywise-conjugated path (`PK/csl04/evidence/closed_j_check.py`,
numerics;
As (L), stated with `∫⁻ ofReal` (m6); the integrand is
pathwise nonnegative.
-/
def TagChannelLeakageOut : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ T : ℝ, 0 < s → s < τ → τ < T →
  ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᶠ W in atTop,
    ∫⁻ ω, ENNReal.ofReal ((farEmbed ((closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)ᴴ *
          closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω) *
        scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω *
        tagResponse b E W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ⌋₊ ω *
        (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)ᴴ).trace.re / W)
      ∂growthPathLaw W b ≤ ENNReal.ofReal ε

/-!
## (b) Identification of the closed process with the complex model
-/

/-- **(b) Closed identification**: frequently as `h ↓ 0` and then frequently in `K`, every
complex model value at `(h, K)` is eventually within `ε` of the closed expectation. -/
def ComplexClosedIdentification : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ ε : ℝ, 0 < ε → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop, ∀ v : ℝ,
    ComplexModelValue b E s T τ m h K (entranceLaw P μ s) Φ v →
    ∀ᶠ W in atTop, |closedPhysExpectation b E s T h τ m Φ W - v| ≤ ε

/-- **(b1) Identification at a fixed cap** (complex analogue of `CappedClosedIdentification`):
the capped closed expectation is eventually within `ε` of the restricted value of every complex
finite model at `(h, K)`. -/
def ComplexCappedClosedIdentification : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ ε : ℝ, 0 < ε → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop,
    ∀ (Ω' : Type) (mΩ : MeasurableSpace Ω') (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω')
      (tseq : Ω' → ℕ → ℝ) (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
      (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
      IsFiniteComplexSourceModel b E s τ m h K (entranceLaw P μ s) 𝓖 Q tseq G Kc →
      ∀ᶠ W in atTop, |cappedClosedPhysExpectation b E s T h τ m Φ K W -
        restrictedModelExpectation K h s T Q tseq G Kc Φ| ≤ ε

/-- **(b2) Limit points of the capped closed expectation are restricted model values**
(existence half; complex analogue of `ClosedLimitIdentification`). -/
def ComplexClosedLimitIdentification : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop,
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ L : ℝ,
      Tendsto (fun n => cappedClosedPhysExpectation b E s T h τ m Φ K (φ n)) atTop (𝓝 L) →
      ∃ (Ω' : Type) (mΩ : MeasurableSpace Ω') (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω')
        (tseq : Ω' → ℕ → ℝ) (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
        (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
        IsFiniteComplexSourceModel b E s τ m h K (entranceLaw P μ s) 𝓖 Q tseq G Kc ∧
        restrictedModelExpectation K h s T Q tseq G Kc Φ = L

end BlockBand.SourceProcess.PhysApprox
