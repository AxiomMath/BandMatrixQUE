module

public import BlockBand.Internal.Contracts.Endpoints

/-!
# Window-uniform contracts: clock entrance and near-Schatten decay

| Contract | Statement | Fixed-energy original |
|---|---|---|
| `ClockFractionalEntranceWindowContract` | clock fractional entrance | `Endpoints.ClockFractionalEntranceContract` (`entrance`, `later`) |
| `NearSchattenDecayWindowContract` | near-Schatten decay | `Endpoints.NearSchattenDecayContract` (`limsupDecay`) |

## Window uniformity

The uniformity in deterministic energies includes every bounded unfolded window.

* Lengths. Path lengths `m_W` with `m_W/W → t` (`IsWindowLength`) in place of `⌊Wt⌋`.
  Clauses that are already uniform over a travel interval (`later`) are stated at every length
  of that interval.
* Constants. `C` is chosen after `b, E, p` (and `ε` or `s₁, s₂`) and the window constant `K`,
  and before the source, the preceding middle length `t₁`, the travel time, the energies and the
  lengths; the width threshold of `later` may depend on the source (as in the original).
* Restated unchanged. `ClockFractionalEntranceContract.smallChannels` is an inequality at
  every bulk energy, width and length, so it already covers each `e_W`;
  `NearSchattenDecayContract.limitDecay` concerns critical limits at the base energy (the window
  `limsup`s are bounded through these same limit objects). Both are repeated unchanged as fields so
  that each window contract contains its fixed-energy original.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Endpoints (nearClock travelLength IsUnitSource smallChannelPower
  ClockWord noTags IsClockMeasure limitFracTrace)
open BlockBand.Internal.Contracts.TransmissionStatements (IsWordLimit)
open scoped ENNReal

/-!
## Window vocabulary
-/

/-- Deterministic energies `e_W` in the window of constant `K` around `E`: eventually
`|e_W - E| ≤ K/W²`. -/
def IsWindowEnergy (E K : ℝ) (e : ℕ → ℝ) : Prop :=
  ∀ᶠ W : ℕ in atTop, |e W - E| ≤ K / (W : ℝ) ^ 2

/-- Path lengths `m_W` with `m_W/W → t`. -/
def IsWindowLength (t : ℝ) (m : ℕ → ℕ) : Prop :=
  Tendsto (fun W : ℕ => (m W : ℝ) / W) atTop (𝓝 t)

/-- `E H_p` of the near clock of the source `q` at energy `e` (blocks `A - e`, matched leads
`boundaryZ b e`) and path length `j`, as a lower integral of `Tr A^p ≥ 0`. -/
def windowFracMoment (b e p : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W j q ω)) ∂growthPathLaw W b

/-!
## Clock fractional entrance, window form
-/

/-- The clock fractional entrance, window form.
* `entrance`: for every `0 < p < 1`, `ε > 0` and window constant `K ≥ 0` there is `C`, chosen
  before the source, the preceding middle length, the energies and the lengths, such that
  `limsup_W E H_p ≤ C` at energies `e_W` in the window and lengths `m_W/W → t₁ + R + ε`.
* `later`: on each fixed travel interval `[s₁, s₂]`, `0 < s₁ ≤ s₂`, and for each `K ≥ 0` there is
  `C` (chosen before the source and the preceding middle length) such that for every source
  there is `W₀` with `E H_p ≤ C` for all `W ≥ W₀`, every energy `e'` with `|e' - E| ≤ K/W²` and
  every travel time `s ∈ [s₁, s₂]` (every length of the interval).
* `smallChannels`: the same statement as `Endpoints.ClockFractionalEntranceContract.smallChannels`. -/
structure ClockFractionalEntranceWindowContract : Prop where
  entrance : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ ε : ℝ, 0 < ε → ∀ K : ℝ, 0 ≤ K →
      ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
        ∀ (e : ℕ → ℝ) (m : ℕ → ℕ), IsWindowEnergy E K e → IsWindowLength (t₁ + R + ε) m →
          limsup (fun W : ℕ => windowFracMoment b (e W) p W (m W) q) atTop ≤ ENNReal.ofReal C
  later : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ → ∀ K : ℝ, 0 ≤ K →
      ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
        ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ e' : ℝ, |e' - E| ≤ K / (W : ℝ) ^ 2 →
          ∀ s ∈ Set.Icc s₁ s₂,
            windowFracMoment b e' p W (travelLength W t₁ R s) q ≤ ENNReal.ofReal C
  smallChannels : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < r → r < 1 → ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
      ∀ a : ℝ, 0 ≤ a → ∀ W j : ℕ,
        ∫⁻ ω, ENNReal.ofReal (smallChannelPower a r (nearClock b E W j q ω))
            ∂growthPathLaw W b ≤
          ENNReal.ofReal (a ^ (r - p)) *
            ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W j q ω)) ∂growthPathLaw W b

/-!
## Near-Schatten decay, window form
-/

/-- Near-Schatten decay, window form.
* `limsupDecay`: for every `0 < p < 1` and window constant `K ≥ 0` there is `C`, chosen before the
  source, the preceding middle length, the travel time, the energies and the lengths, with
  `limsup_W E H_p ≤ C e^{-Dp(1-p)s/2}` at every travel time `s ≥ 1`, energies `e_W` in the window
  and lengths `m_W/W → t₁ + R + s`.
* `limitDecay`: the same statement as `Endpoints.NearSchattenDecayContract.limitDecay`. -/
structure NearSchattenDecayWindowContract : Prop where
  limitDecay : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : ClockWord → ℝ → Ω → ℂ),
      IsWordLimit b E noTags (fun _ => q) (t₁ + R) P Z →
    ∀ μ : ℝ → Ω → Measure ℝ, (∀ t : ℝ, t₁ + R ≤ t → ∀ᵐ ω ∂P, IsClockMeasure Z t ω (μ t ω)) →
    ∀ s t : ℝ, 0 < s → 0 ≤ t →
      ∫⁻ ω, limitFracTrace p (μ (t₁ + R + s + t) ω) ∂P ≤
        ENNReal.ofReal (Real.exp (-(transportD0 b E * p * (1 - p) * t / 2))) *
          ∫⁻ ω, limitFracTrace p (μ (t₁ + R + s) ω) ∂P
  limsupDecay : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ K : ℝ, 0 ≤ K →
      ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q → ∀ s : ℝ, 1 ≤ s →
        ∀ (e : ℕ → ℝ) (m : ℕ → ℕ), IsWindowEnergy E K e → IsWindowLength (t₁ + R + s) m →
          limsup (fun W : ℕ => windowFracMoment b (e W) p W (m W) q) atTop ≤
            ENNReal.ofReal (C * Real.exp (-(transportD0 b E * p * (1 - p) * s / 2)))

end BlockBand.Endpoints
