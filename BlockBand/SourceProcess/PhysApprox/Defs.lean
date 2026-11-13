module

public import BlockBand.SourceProcess.ComplexConstruct.Interface
public import BlockBand.SourceProcess.Closing.Defs
public import BlockBand.SourceProcess.CapLimit.Model

/-!
# The closed complex source data

Definitions only. Notation: `𝕊` is the scattering matrix at the final length `n = ⌊WT⌋`; the
omitted far channels (`t ≤ h²`) are chosen at `⌊Ws⌋`, with far input projection `A = farEmbed A_-`
and pairing `Π = farEmbed Π`; `N = Π𝕊A`; `C(z) = physClosingMap … z`; `V = probeFrame`
(`V_pr = 𝒰_n*𝒥`).

* `physClosingN`: `N = Π𝕊A`.
* `closedK`: `𝒦_cl(z) = 𝒦 - 2iηz V*(1 - zN)⁻¹Π𝕊V`.
* `closedFrame`: `V_cl(z) = C(z)ᴴV`.
* `closedSourceData`: `(𝒦_cl, V_clᴴV_cl, V_clᴴPV_cl, V_clᴴ(Cᴴ𝕊ᴴP𝕊C - P)V_cl)`.
* `closedPhysExpectation`: `E_{path, probes, z} Φ(closedSourceData)`, one uniform phase.
* `physCapEventC`, `cappedClosedPhysExpectation`, `restrictedModelExpectation`: the cap event at
  `s` and the two sides of the capped identification `ComplexCappedClosedIdentification`.

Facts proved elsewhere: `closedK … 0 = complexSourceK …` (`closedK_zero`; this is the `f(0) = 0`
of Kolmogorov) and `measurable_closedSourceData` (joint in path, probes and phase).
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
## The closed complex source data
-/

/-- `N = Π𝕊A` (`r = S_AA`): `𝕊` at the final length `⌊WT⌋`, omitted channels `t ≤ h²` chosen at
`⌊Ws⌋`. Equal to `closingN` of the data of `physClosingMap`. -/
def physClosingN (b E s T h : ℝ) (W : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  closingN (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)
    (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
    (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω))

/-- **Closed `𝒦`**: `𝒦_cl(z) = 𝒦 - 2iηz V_pr*(1 - zN)⁻¹ Π 𝕊 V_pr`, the omitted far channels
closed with phase `z`. It equals `𝒥*G_cl(z)𝒥` for the resolvent of the closed path. At `z = 0` it
is `complexSourceK` (`closedK_zero`). -/
def closedK (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W : ℕ) (z : ℂ)
    (x : ProbedPath W np) : Matrix (Fin np) (Fin np) ℂ :=
  complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x -
    ((2 * etaZ b E : ℝ) * Complex.I * z) •
      ((probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᴴ * (1 - z • physClosingN b E s T h W x.1)⁻¹ *
        farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1) *
        scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 * probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)

/-- **Closed probe frame** `V_cl(z) = C(z)ᴴ V_pr`: the probes' response to the retained inputs.
At `z = 0` it is `(1 - A)V_pr`, not `V_pr`. -/
def closedFrame (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W : ℕ) (z : ℂ)
    (x : ProbedPath W np) : Matrix (Fin 2 × Fin W) (Fin np) ℂ :=
  (physClosingMap b E s T h W x.1 z)ᴴ * probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x

/-- **Closed source data**:
`(𝒦_cl, V_clᴴV_cl, V_clᴴPV_cl, V_clᴴ(Cᴴ𝕊ᴴP𝕊C - P)V_cl)`, all at `⌊WT⌋`. -/
def closedSourceData (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W : ℕ) (z : ℂ)
    (x : ProbedPath W np) : SourceData np :=
  ![closedK b E s T h τ m W z x,
    (closedFrame b E s T h τ m W z x)ᴴ * closedFrame b E s T h τ m W z x,
    (closedFrame b E s T h τ m W z x)ᴴ * nearProjection W * closedFrame b E s T h τ m W z x,
    (closedFrame b E s T h τ m W z x)ᴴ *
      ((physClosingMap b E s T h W x.1 z)ᴴ * (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1)ᴴ *
        nearProjection W * scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 *
        physClosingMap b E s T h W x.1 z - nearProjection W) *
      closedFrame b E s T h τ m W z x]

/-- **The closed physical expectation**: one uniform phase `z = e^{iθ}`,
`θ ~ phaseLaw`, for all probes, independent of the path and the probes. -/
def closedPhysExpectation (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (W : ℕ) : ℝ :=
  ∫ y, Φ (closedSourceData b E s T h τ m W (phase y.2) y.1)
    ∂((probedPathLaw W np b).prod phaseLaw)

/-!
## Cap event and restricted model value
-/

/-- The physical cap event at `s`: the trace measure of the homogeneous path transmission at
`⌊Ws⌋` lies in `CapLimit.capSet K h` (`t_K ≤ h²`). It is the same set as
`ClosedIdent.physCapEvent` (restated to keep the statement imports light). -/
def physCapEventC (b E s h : ℝ) (K W : ℕ) : Set (GrowthPath W) :=
  {ω | ((transmissionProcess b E (fun _ => 0) W s ω : FiniteMeasure unitInterval) :
    Measure unitInterval) ∈ CapLimit.capSet K h}

/-- The closed expectation restricted to the physical cap event. -/
def cappedClosedPhysExpectation (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (K W : ℕ) : ℝ :=
  ∫ y, (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
      Φ (closedSourceData b E s T h τ m W (phase y.2) y.1)
    ∂((probedPathLaw W np b).prod phaseLaw)

/-- The model value restricted to the entrance event `{t_K ≤ h²}`, at model
time `T - s`. -/
def restrictedModelExpectation {np : ℕ} (K : ℕ) (h s T : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure Ω) (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) : ℝ :=
  ∫ ω in CapLimit.entEvent tseq (CapLimit.capSet K h),
    Φ (modelSourceData (srcSignature K (Fin np)) (Kc (T - s).toNNReal ω)
      (G (T - s).toNNReal ω)) ∂Q

end BlockBand.SourceProcess.PhysApprox
