module

public import BlockBand.Transmission.LawDuality.Determining
public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The transmission law: subsequential limits and the statements of the proof

The vocabulary for subsequential limits of the transmission measure process `μ_W` and the five
statements from which the transmission law is assembled.

Vocabulary:
* `IsTransmissionSubLimit b E κ φ P μ`: `(P, μ)` is an fdd limit of `μ_{φ(n)}` (positive times,
  bounded continuous tests), with measurable marginals and a.s. continuous paths on `(0,∞)`.
* `ratioDrift D₀ E κ u z ν = (𝒟_p F_·(ν))(z) - h(u) R(z) F_z(ν)`, the right side of
  ratio duality relation (`𝒢^κF = 𝒟_pF - h(t)RF`), `h = absorptionRate E κ`.
* `IsRatioMartingale`: `F_z(μ_t) - F_z(μ_s) - ∫_s^t ratioDrift(u, z, μ_u) du` are martingale
  increments for the natural filtration of `μ` (`IsMartingaleIncrements`), every interior `z`.
* `HasRatioEntrance`: `E F_z(μ_s) → 0` as `s ↓ 0` whenever a pair remains.
* `HasLocalMassBound`: `E μ_t[0,1]` is bounded on compact positive-time intervals.

Statements:
* `TransmissionSubLimitExists` (tightness and Prokhorov): every subsequence has a
  further subsequence with a subsequential limit.
* `TransmissionTraceModulus`: the finite-`W` modulus of continuity of `t ↦ μ_W(t)(f)`.
* `SubLimitRatioMP` (the `F_{x,y}` finite-`W` expansion, the generator, the forced extension and
  the entrance): every subsequential limit is a ratio martingale with entrance and local mass
  bound.
* `RatioDualityPrinciple` (duality with killing): a statement without `W`: a continuous
  random-measure process which is a ratio martingale with entrance and local mass bound
  satisfies the dual transmission law (proved as `ratioDualityPrinciple_holds`).
* `SubLimitFddUnique` (multi-time uniqueness): any two subsequential limits have the
  same finite-dimensional laws. Its one-time content is `subLimit_map_eq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal BoundedContinuousFunction

/-!
## Vocabulary
-/

/-- **`(P, μ)` is a subsequential (fdd) limit of `μ_W` along `φ`.** -/
structure IsTransmissionSubLimit (b E : ℝ) (κ : ℝ → ℝ) (φ : ℕ → ℕ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval) : Prop where
  prob : IsProbabilityMeasure P
  measurable : ∀ t, 0 < t → Measurable (μ t)
  continuous : ∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Set.Ioi 0)
  fdd : ∀ (k : ℕ) (τ : Fin k → ℝ), (∀ i, 0 < τ i) →
    ∀ Φ : BoundedContinuousFunction (Fin k → FiniteMeasure unitInterval) ℝ,
      Tendsto (fun n : ℕ => ∫ ω, Φ (fun i => transmissionProcess b E κ (φ n) (τ i) ω)
          ∂growthPathLaw (φ n) b) atTop (𝓝 (∫ ω, Φ (fun i => μ (τ i) ω) ∂P))

/-- `z ↦ F_z(ν)` on the dual coordinates. -/
def ratioOn {p : ℕ} (ν : FiniteMeasure unitInterval) : DualCoord p → ℝ :=
  fun z => transmissionRatio z.1 z.2 ν

/-- The right side of the ratio duality relation: `(𝒟_p F_·(ν))(z) - h(u) R(z) F_z(ν)`. -/
def ratioDrift (D0 E : ℝ) (κ : ℝ → ℝ) (u : ℝ) {p : ℕ} (z : DualCoord p)
    (ν : FiniteMeasure unitInterval) : ℝ :=
  dualGenerator D0 (ratioOn ν) z -
    absorptionRate E κ u * (∑ i, (z.1 i + z.2 i)) * transmissionRatio z.1 z.2 ν

/-- **The ratio martingale problem** (the ratio duality relation for the limit process). -/
def IsRatioMartingale (D0 E : ℝ) (κ : ℝ → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) : Prop :=
  ∀ (p : ℕ) (z : DualCoord p), z ∈ dualChamber p →
    IsMartingaleIncrements P (fun (_ : Unit) => μ) (Set.Ioi 0) fun s t ω =>
      transmissionRatio z.1 z.2 (μ t ω) - transmissionRatio z.1 z.2 (μ s ω) -
        ∫ u in s..t, ratioDrift D0 E κ u z (μ u ω)

/-- **Entrance**: zero initial value whenever a pair remains. -/
def HasRatioEntrance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∀ z : DualCoord p, z ∈ dualChamber p →
    Tendsto (fun s => ∫ ω, transmissionRatio z.1 z.2 (μ s ω) ∂P) (𝓝[>] 0) (𝓝 0)

/-- **Local mass bound**: `E μ_t[0,1]` is bounded on every `[ε, T]`, `ε > 0`. -/
def HasLocalMassBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) : Prop :=
  ∀ ε T : ℝ, 0 < ε → ∃ C : ℝ, ∀ t ∈ Set.Icc ε T,
    ∫⁻ ω, (μ t ω : Measure unitInterval) Set.univ ∂P ≤ ENNReal.ofReal C

/-!
## Statements
-/

/-- **Subsequential limits exist** (tightness from the polynomial tests and the conductance
moments): for `0 < b < 1/2`, bulk `E` and every admissible profile `κ`, every
subsequence `ns → ∞` has a strictly increasing refinement `ms` along which `μ_W` has a
subsequential limit. -/
def TransmissionSubLimitExists : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ, StrictMono ms ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionSubLimit b E κ (ns ∘ ms) P μ

/-- **The finite-`W` modulus** (the `modulus` clause of `IsTransmissionLimit`), for every
admissible profile: for `ε > 0`, `T`, a continuous `f` and `η, θ > 0` there are `δ > 0` and `W₀`
with `P(∃ t, t' ∈ [ε, T], |t - t'| ≤ δ, |μ_W(t)(f) - μ_W(t')(f)| > η) ≤ θ` for all `W ≥ W₀`. -/
def TransmissionTraceModulus : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ ε T : ℝ, 0 < ε → ∀ f : C(unitInterval, ℝ), ∀ η θ : ℝ, 0 < η → 0 < θ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
          η < |∫ x, f x ∂(transmissionProcess b E κ W t ω : Measure unitInterval) -
            ∫ x, f x ∂(transmissionProcess b E κ W t' ω : Measure unitInterval)|} ≤
          ENNReal.ofReal θ

/-- **The limit ratio martingale problem**. Every subsequential limit
(along `φ → ∞`) solves the ratio martingale problem with `D₀ = transportD0 b E` and
`h = 4πρ(E)κ`, has the entrance, and has locally bounded mean mass. Inputs in the paper: the
`F_{x,y}` finite-`W` expansion with summable errors (derivatives bounded by polynomials in `g`),
the transmission generator theorem (`TransmissionGeneratorContract`, `κ ≡ 0`), the forced
extension (`LawFinite.AbsorbedWardIdentity`, `InjectionNorms`, `InjectionMean`) and the entrance
bound (`LawFinite.TransmissionEntranceBulk`). -/
def SubLimitRatioMP : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionSubLimit b E κ φ P μ →
      IsRatioMartingale (transportD0 b E) E κ P μ ∧ HasRatioEntrance P μ ∧ HasLocalMassBound P μ

/-- **Duality with killing** (a statement about one process, without `W`).
A probability space carrying a random finite measure process on `[0,1]` with measurable
marginals and a.s. continuous paths on `(0,∞)`, which is a ratio martingale with entrance and
local mass bound, satisfies the dual transmission law at every `t > 0` and interior `(x, y)`:
every realization of the conservative deletion law (the dual boundary lemma) gives
`E_{x,y}[e^{-∫_0^t h(t-s)R_s ds} 1{ζ ≤ t}] = E F_{x,y}(μ_t)`. -/
def RatioDualityPrinciple : Prop :=
  ∀ D0 : ℝ, 0 < D0 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsProbabilityMeasure P →
      (∀ t, 0 < t → Measurable (μ t)) → (∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Set.Ioi 0)) →
      IsRatioMartingale D0 E κ P μ → HasRatioEntrance P μ → HasLocalMassBound P μ →
      ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
        DualLawValue E κ t D0 x y (∫ ω, transmissionRatio x y (μ t ω) ∂P)

/-- **Multi-time uniqueness** (the stopped backward calculation between two positive times,
conditionally on the earlier history, determines the transition law). Any
two subsequential limits have the same finite-dimensional distributions. -/
def SubLimitFddUnique : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ φ φ' : ℕ → ℕ, Tendsto φ atTop atTop → Tendsto φ' atTop atTop →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval) (Ω' : Type) (_ : MeasurableSpace Ω')
      (P' : Measure Ω') (μ' : ℝ → Ω' → FiniteMeasure unitInterval),
      IsTransmissionSubLimit b E κ φ P μ → IsTransmissionSubLimit b E κ φ' P' μ' →
      ∀ (k : ℕ) (τ : Fin k → ℝ), (∀ i, 0 < τ i) →
        ∀ Φ : BoundedContinuousFunction (Fin k → FiniteMeasure unitInterval) ℝ,
          ∫ ω, Φ (fun i => μ (τ i) ω) ∂P = ∫ ω, Φ (fun i => μ' (τ i) ω) ∂P'

end BlockBand.Transmission.LawDuality
