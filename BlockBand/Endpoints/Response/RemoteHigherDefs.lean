module

public import BlockBand.Endpoints.Poisson.PoissonEndpointDefs

/-!
# The remote higher-order clock theorem: the uniform statement and its inputs

* `RemoteHigherUniformStatement`: the remote bound uniformly in moving energies, general lengths
  and indicator sources.
* `RhNearHigherLimsupDecay`, `RhNearHigherLimsupDecayUniform`, `RhHigherLimitDecay`: the three
  inputs from which the remote bound is derived.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements (IsWordLimit)
open BlockBand.Internal.Contracts.Endpoints (IsUnitSource ClockWord noTags IsClockMeasure
  limitFracTrace nearClock travelLength)
open scoped ENNReal

/-!
## The uniform statement
-/

/-- The remote bound, uniform form. Fix `0 < b < 1/2`, a bulk `E`, exponents `0 < p < 1`, `r ≥ 1`,
`pr < 1`, and a window constant `K ≥ 0`. There are `C` and `c > 0`, chosen before `τ`, `R`, the
energies, the lengths and the source, such that for every `τ > 0`, `R ≥ 2`, every sequence of
energies `e_W` with eventually `|e_W - E| ≤ K/W²`, every sequence of path lengths `n_W` with
`n_W/W → τ`, and every source `0 ≤ q ≤ 1` vanishing off `[R, τ - R]` (no continuity),
`limsup_W E (Tr Q_{e_W, n_W}(q)^p)^r ≤ C e^{-cR}`.

The three uniformities:
* (a) moving energies `e = E + x/Λ_W`, `Λ_W = n W ρ(E)`: for `x` in a bounded window
  `|x| ≤ X` and `n/W → τ ≥ 1`, eventually `|x/Λ_W| ≤ 2X/(ρ(E) W²)`, so `K = 2X/ρ(E)`; `K`
  depends only on the window of `supp f`. Because `C, c` do not depend on the sequence `e_W`,
  the bound also holds for `limsup_W sup_{|e - E| ≤ K/W²}` (choose near-maximizing `e_W`);
* (b) general lengths `n_W/W → τ`, not only `⌊Wτ⌋`;
* (c) indicator sources: `q` is any `[0,1]`-valued function vanishing off `[R, τ-R]`, e.g. the
  indicator of the blocks of a set `C`; unequal distances `R₁, R₂ ≥ R` to the two ends are the
  case `R = min(R₁, R₂)`.

The grid convention is that of `intervalSource`: block `k` carries `q((k+1)/W)`, so `x` is the
scaled distance from the far end and `n_W/W - x` the distance from the near end. -/
def RemoteHigherUniformStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 → ∀ K : ℝ, 0 ≤ K →
      ∃ C c : ℝ, 0 < c ∧ ∀ τ R : ℝ, 0 < τ → 2 ≤ R →
        ∀ (e : ℕ → ℝ) (n : ℕ → ℕ), (∀ᶠ W : ℕ in atTop, |e W - E| ≤ K / (W : ℝ) ^ 2) →
          Tendsto (fun W : ℕ => (n W : ℝ) / W) atTop (𝓝 τ) →
        ∀ q : ℝ → ℝ, (∀ x, 0 ≤ q x) → (∀ x, q x ≤ 1) → (∀ x, x ∉ Set.Icc R (τ - R) → q x = 0) →
          limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
              (fracTrace p (intervalSource b (e W) W (n W) q ω)) ^ r
              ∂growthPathLaw W b) atTop ≤
            ENNReal.ofReal (C * Real.exp (-(c * R)))

/-!
## The inputs
-/

/-- Higher fractional moments of a near clock decay along the travel (the `r`-th power analogue
of the limsup clause of near-Schatten decay).

Fixed `0 < b < 1/2`, bulk `E`, `0 < p < 1`, `r ≥ 1`, `pr < 1`. There are `C` and `c > 0`, chosen
before the source, the preceding middle length `t₁` and the travel time, such that the near clock
`A` of every unit source (`IsUnitSource t₁ R q`) satisfies, at every travel time `s ≥ 1` after
the injection, `limsup_W E (Tr A^p)^r ≤ C e^{-cs}` (path length
`travelLength W t₁ R s = ⌊W(t₁+R+s)⌋`).

This concerns one clock block (the near-near block) of one unit source at a time. The remote
bound needs in addition the path reversal for the far block, the pinching of the complete
two-input clock, subadditivity of `Tr ·^p`, the decomposition of a remote source into unit pieces
and the geometric summation with `L^r` weights; these are proved in `rh_core`. It also says
nothing about critical limits (`limitDecay`). -/
def RhNearHigherLimsupDecay : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 →
      ∃ C c : ℝ, 0 < c ∧ ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q → ∀ s : ℝ, 1 ≤ s →
        limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
            (fracTrace p (nearClock b E W (travelLength W t₁ R s) q ω)) ^ r
            ∂growthPathLaw W b) atTop ≤
          ENNReal.ofReal (C * Real.exp (-(c * s)))

/-- `RhNearHigherLimsupDecay` with in addition a window constant `K ≥ 0` fixed before `C, c`,
every sequence of energies `e_W` with eventually `|e_W - E| ≤ K/W²`, and every sequence of path
lengths `m_W` with `m_W/W → t₁ + R + s` (instead of `⌊W(t₁+R+s)⌋` at `E`). As for
`RhNearHigherLimsupDecay`, it concerns one block and unit sources. -/
def RhNearHigherLimsupDecayUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 → ∀ K : ℝ, 0 ≤ K →
      ∃ C c : ℝ, 0 < c ∧ ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q → ∀ s : ℝ, 1 ≤ s →
        ∀ (e : ℕ → ℝ) (m : ℕ → ℕ), (∀ᶠ W : ℕ in atTop, |e W - E| ≤ K / (W : ℝ) ^ 2) →
          Tendsto (fun W : ℕ => (m W : ℝ) / W) atTop (𝓝 (t₁ + R + s)) →
          limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
              (fracTrace p (nearClock b (e W) W (m W) q ω)) ^ r
              ∂growthPathLaw W b) atTop ≤
            ENNReal.ofReal (C * Real.exp (-(c * s)))

/-- Exponential decay of the higher fractional moments at critical limits: for a unit source and a
joint critical word limit with a.s. clock measures `μ_t`, for `s > 0`, `t ≥ 0`,
`E H_p(μ_{t₁+R+s+t})^r ≤ e^{-D₀ r p (1 - rp) t / 2} E H_p(μ_{t₁+R+s})^r`. This is the
`limitDecay` field of `RemoteHigherStatement`; it does not imply `limsupBound`. -/
def RhHigherLimitDecay : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 →
    ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : ClockWord → ℝ → Ω → ℂ),
      IsWordLimit b E noTags (fun _ => q) (t₁ + R) P Z →
    ∀ μ : ℝ → Ω → Measure ℝ, (∀ t : ℝ, t₁ + R ≤ t → ∀ᵐ w ∂P, IsClockMeasure Z t w (μ t w)) →
    ∀ s t : ℝ, 0 < s → 0 ≤ t →
      ∫⁻ w, limitFracTrace p (μ (t₁ + R + s + t) w) ^ r ∂P ≤
        ENNReal.ofReal (Real.exp (-(transportD0 b E * r * p * (1 - r * p) * t / 2))) *
          ∫⁻ w, limitFracTrace p (μ (t₁ + R + s) w) ^ r ∂P

end BlockBand.Endpoints
