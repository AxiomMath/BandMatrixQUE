module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# Fractional clock entrance and strict homogeneous Schatten decay

`ClockFractionalEntranceContract` states the fractional clock entrance lemma (including the
small-channel bound), and `NearSchattenDecayContract` the near Schatten decay theorem with its
homogeneous decay of fractional clock traces.

## Setting

* **Law.** The independent Gaussian path with its two matched leads at deterministic bulk
  energy, unabsorbed (the reference path has no physical absorption): the near-end-grown
  path `TransmissionPath.growthPathLaw W b`, the full inverse with two matched leads
  `TransmissionPath.fullInverse b E`, `0 < b < 1/2`, `-2 < E < 2`.
* **Sources and clocks.** "Sources are on physical blocks, normalized by `W²`": the interval
  source `Q(q) = Σ_k q((k+1)/W) Y_{n;k}/W²` (`TransmissionPath.intervalSource`) of a positive test
  `q` supported on an interval `[t₁, t₁ + R]` of scaled length `R ≤ 1`. Here `t₁` is the
  scaled length of the *preceding middle* path (blocks born before the injection) and
  `t₁ + R` is the end of the injection ("time zero denotes its last injection"). The *near-near
  clock block* `A` is the near-port block of `Q(q)` (`nearClock`); `H_p = Tr A^p`
  (`TransmissionPath.fracTrace`). Travel time `s ≥ 0` after the injection is the path length
  `⌊W(t₁ + R + s)⌋`. Travel is measured from the interval end `t₁ + R`, which is at or after the
  last time `q > 0`; this is harmless because the entrance constant `C(1 + ε⁻¹)` of the proof is
  monotone in the travel time.
* **Source class.** "A positive source on an interval of scaled length at most one" is a
  `TransmissionPath.IsSourceTest t₁ (t₁ + R) q` with `0 ≤ t₁`, `0 ≤ R ≤ 1` and `q ≤ 1`
  (`IsUnitSource`). The bound `q ≤ 1` is the normalization `0 ≤ q ≤ 1` of the sources of
  the remote higher-moment theorem that the decay results serve; it is no restriction for bounded sources,
  since `A` is linear and Loewner-monotone in `q ≥ 0` and `H_p(λA) = λ^p H_p(A)`, so a source with
  `q ≤ M` is controlled through `q/M`. Constants are uniform over this class (sums of travel
  bounds require uniformity in the source location).
* **Order of limits.** "`W → ∞` at each fixed finite path length in units of `W`, before
  increasing that length": every `limsup_W` is taken at fixed `t₁, R, q` and
  fixed travel time; the constant is chosen before `t₁, R, q` (independent of the length of the preceding
  middle). Expectations of the nonnegative `H_p` are lower Lebesgue integrals and
  the `limsup` is in `ℝ≥0∞` (no integrability loophole; the bound asserts finiteness).
* **Critical limits.** A critical limit of the clock is a joint critical limit of the trace
  words of the one-source family (`TransmissionStatements.IsWordLimit`, no tags, the single interval
  test `q`, start of homogeneity `t₀ = t₁ + R`). The moments `Tr A^k = Tr (Q P)^k` are the
  ordinary words `clockWord k`. The limiting clock at time `t` is the finite *trace measure*
  `μ_t` on `[0, ∞)` with `∫ x^{k-1} dμ_t = lim Tr A^k` for all `k ≥ 1` (`IsClockMeasure`; at
  finite `W` it is `Σ_i λ_i δ_{λ_i}`). Supported in `[0, Z_{clockWord 1}]`, it is unique (Hausdorff moment problem on a
  compact interval); its a.s. existence is not asserted here. Its fractional trace is `H_p(μ) = ∫ x^{p-1} dμ(x)` in
  `ℝ≥0∞` with `0^{p-1} = ∞` (`limitFracTrace`): at finite `W` this is `Σ_i λ_i^p`, and trace
  mass collapsing to zero eigenvalues ("trace dust") makes it infinite.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.Endpoints

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix

/-!
## 1. Clock vocabulary
-/

/-- The near-near clock block `A` of the positive source `q` on the two-input path of length
`j`: the near-port block of the interval source `Q(q) = Σ_k q((k+1)/W) Y_{j;k}/W²`. During
homogeneous propagation `A₊ = L*AL`. -/
def nearClock (b E : ℝ) (W j : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  portBlock (intervalSource b E W j q ω) 0 0

/-- The path length at travel time `s` after the end `t₁ + R` of the injection interval. -/
def travelLength (W : ℕ) (t₁ R s : ℝ) : ℕ := ⌊(W : ℝ) * (t₁ + R + s)⌋₊

/-- `E H_p` of the near clock at travel time `s` (lower integral of `Tr A^p ≥ 0`). -/
def clockFracMoment (b E p : ℝ) (W : ℕ) (t₁ R s : ℝ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W (travelLength W t₁ R s) q ω))
    ∂growthPathLaw W b

/-- The positive source class: a source test on
`[t₁, t₁ + R]`, `0 ≤ t₁`, `0 ≤ R ≤ 1`, with `q ≤ 1`. -/
def IsUnitSource (t₁ R : ℝ) (q : ℝ → ℝ) : Prop :=
  0 ≤ t₁ ∧ 0 ≤ R ∧ R ≤ 1 ∧ IsSourceTest t₁ (t₁ + R) q ∧ ∀ x, q x ≤ 1

open scoped Classical in
/-- `Σ_{λ_i(A) ≤ a} λ_i(A)^r`, eigenvalues through `charpoly.roots` as in
`TransmissionPath.fracTrace` (left side of the small-channel bound). -/
def smallChannelPower {n : Type*} [Fintype n] [DecidableEq n] (a r : ℝ) (A : Matrix n n ℂ) : ℝ :=
  ((A.charpoly.roots.filter fun z => z.re ≤ a).map fun z => (max z.re 0) ^ r).sum

/-- The one-source family: no tags, a single interval test. -/
abbrev ClockWord := TraceWord 0 1

/-- `Tr A^k = Tr (Q P)^k` as the ordinary word `(Q P)^k` (letter: the interval source, separator
`P`); `k ≥ 1`. -/
def clockWord (k : ℕ) : ClockWord := List.replicate k (TraceLetter.interval 0, Separator.proj)

/-- No tag birth indices (the family has `nT = 0` tags). -/
def noTags : ℕ → Fin 0 → ℕ := fun _ => Fin.elim0

/-- `μ` is the limiting clock trace measure of the word limit `Z` at time `t` along the sample
`ω`: a finite measure supported in `[0, Re Z_{QP}(t, ω)]` with
`∫ x^{k-1} dμ = Re Z_{(QP)^k}(t, ω)` for every `k ≥ 1` (finite `W`: `μ = Σ_i λ_i δ_{λ_i}`, supported
in `[0, Tr A]` since `0 ≤ λ_i ≤ Tr A`, and `∫ x^{k-1} dμ = Tr A^k`). The compact support makes the
moment problem determinate (it excludes heavy-tailed measures whose higher moments are not
integrable and that Lean's integral convention would otherwise admit). -/
def IsClockMeasure {Ω : Type*} (Z : ClockWord → ℝ → Ω → ℂ) (t : ℝ) (ω : Ω) (μ : Measure ℝ) :
    Prop :=
  IsFiniteMeasure μ ∧ μ (Set.Iio 0) = 0 ∧ μ (Set.Ioi (Z (clockWord 1) t ω).re) = 0 ∧
    ∀ k : ℕ, 1 ≤ k → ∫ x, x ^ (k - 1) ∂μ = (Z (clockWord k) t ω).re

/-- `H_p` of a limiting clock trace measure: `∫ x^{p-1} dμ(x)` with `0^{p-1} = ∞`
(finite `W`: `Σ_i λ_i^p`). -/
def limitFracTrace (p : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal x ^ (p - 1) ∂μ

/-!
## 2. The fractional clock entrance lemma
-/

/-- The fractional clock entrance lemma.
* `entrance`: for every `0 < p < 1` and `ε > 0` there is `C = C_{p,ε}`, chosen
  before the source and the preceding middle length `t₁`, with
  `limsup_W E H_p(ε) ≤ C` (`W → ∞` at fixed `t₁, R, q, ε`).
* `later`: on each subsequent fixed homogeneous travel interval `[s₁, s₂]`,
  `0 < s₁ ≤ s₂`, the expectations `E H_p(s)` are bounded uniformly in `W ≥ W₀` and `s ∈ [s₁,s₂]`
  by a constant `C = C_{p,s₁,s₂}` permitted to depend on that interval and on `p` only: it is
  chosen before the source and the preceding middle length `t₁`; the width threshold `W₀` may
  depend on the source.
* `smallChannels`: for `p < r < 1` (the exponent `q` of the paper)
  and every threshold `a ≥ 0`, at every width and every length `j` of the path,
  `E Σ_{λ_i(A) ≤ a} λ_i(A)^r ≤ a^{r-p} E H_p` (a pointwise inequality). -/
structure ClockFractionalEntranceContract : Prop where
  entrance : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
        limsup (fun W : ℕ => clockFracMoment b E p W t₁ R ε q) atTop ≤ ENNReal.ofReal C
  later : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
        ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ s ∈ Set.Icc s₁ s₂,
          clockFracMoment b E p W t₁ R s q ≤ ENNReal.ofReal C
  smallChannels : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < r → r < 1 → ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
      ∀ a : ℝ, 0 ≤ a → ∀ W j : ℕ,
        ∫⁻ ω, ENNReal.ofReal (smallChannelPower a r (nearClock b E W j q ω))
            ∂growthPathLaw W b ≤
          ENNReal.ofReal (a ^ (r - p)) *
            ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W j q ω)) ∂growthPathLaw W b

/-!
## 3. The near Schatten decay theorem
-/

/-- The near Schatten decay theorem.
* `limitDecay`: for every critical limit of the clock of a unit source — a joint
  critical word limit `(P, Z)` on `[t₁ + R, ∞)` (`IsWordLimit`, one interval test `q`, no tags)
  and limiting clock trace measures `μ_t` (`IsClockMeasure`, a.s. at each time
  `t ≥ t₁ + R`) — at every travel time `s > 0` after the last injection and every `t ≥ 0`,
  `E H_p(s+t) ≤ e^{-Dp(1-p)t/2} E H_p(s)`, `H_p = limitFracTrace p`. Every `0 < p < 1`.
* `limsupDecay`: for every `0 < p < 1` there is `C`, chosen before the source,
  the preceding middle length and the travel time (constants independent of the total length),
  with `limsup_W E H_p(s) ≤ C e^{-Dp(1-p)s/2}` for every travel time `s ≥ 1` ("at all later
  travel times" after the entrance at one unit of travel; `W → ∞` at fixed `s`). -/
structure NearSchattenDecayContract : Prop where
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
    ∀ p : ℝ, 0 < p → p < 1 →
      ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q → ∀ s : ℝ, 1 ≤ s →
        limsup (fun W : ℕ => clockFracMoment b E p W t₁ R s q) atTop ≤
          ENNReal.ofReal (C * Real.exp (-(transportD0 b E * p * (1 - p) * s / 2)))

end BlockBand.Internal.Contracts.Endpoints
