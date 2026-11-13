module

public import BlockBand.Statements
public import BlockBand.Endpoints.Poisson.FiniteLogRecoveryRing
public import BlockBand.Internal.Contracts.Endpoints
public import BlockBand.Internal.Contracts.Critical
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The Poisson endpoint theorem: statements and inputs

We state the Poisson endpoint theorem and the inputs from which it is derived.

* `RemoteHigherStatement`: the full statement of the remote-higher theorem, both clauses (the
  remote clock bound and the decay of higher clock moments). It is a hypothesis of
  `poissonEndpoint`.
* `PoissonEndpointLaplace`, `PoissonEndpointLimitClause`, `PoissonEndpointStatement`: the two
  clauses of the Poisson endpoint theorem.
* `PeSameVolumeLogError`: the same-volume log-error bound, as a hypothesis.
* `PeSameVolumeDerivation`: the derivation of the same-volume log-error bound from its inputs,
  as a hypothesis.

**Why the same-volume log-error bound is a hypothesis.** Its proof in the paper needs the
following steps, none of which is formalized here:
* the absorbed scattering matrix and the Ward bounds on the remote scattering source;
* the unitary dilation of the source, with subadditivity of `Tr|·|^p`;
* the step from the remote-higher theorem to fractional moments of the dilation (`p = 1/8`);
* the Cauchy-integral removal of exceptional sets (the passive-log lemma, the singular
  log-moments lemma), which gives the single-collar log-error bound;
* the identification of the stage matrices of the sequential-collars lemma
  (`sequentialCollars_full`, stated for fully matched models with ports) with the absorbed ring
  `H^ring` and the direct sum of rings `H^boxes`;
* the telescoping over the `≤ 2m` stages and the integration against `f`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements (IsWordLimit)
open BlockBand.Internal.Contracts.Endpoints (IsUnitSource ClockWord noTags IsClockMeasure
  limitFracTrace)
open BlockBand.Internal.Contracts.Inputs (blockProjector PassiveLog SingularLogMoments)
open BlockBand.Internal.Contracts.InputsRing (ringParameters toBlockCoords directSumBlockCoords)
open BlockBand.Internal.Contracts.Critical (CollarKernelContract)
open BlockBand.Internal.Contracts.Layers (MatchedTracesContract)
open BlockBand.Internal.Contracts.TransmissionUniform (TransmissionLengthUniformContract)
open scoped ENNReal ContDiff

/-!
## 1. The remote-higher theorem
-/

/-- **The remote-higher theorem.**
* `limsupBound` (remote clock bound). Fix `0 < p < 1`, `r ≥ 1`, `pr < 1`. There are
  `C = C_{p,r}` and `c = c_{p,r} > 0`, chosen before the fixed total critical length `τ`
  ("independent of the fixed total critical length") and before `R` and the source. Then for
  every `τ > 0`, every `R ≥ 2` and every source `0 ≤ q ≤ 1` at distance `≥ R` from both path
  endpoints (`IsSourceTest R (τ - R) q`, `q ≤ 1`):
  `limsup_W E (Tr Q(q)^p)^r ≤ C e^{-cR}`.
  Here `Q(q) = intervalSource b E W ⌊Wτ⌋ q` is the interval source on the path of length
  `⌊Wτ⌋` and `Tr Q^p = fracTrace p Q`. The expectation is a lower integral and the `limsup` is
  in `ℝ≥0∞`, so finiteness is part of the claim. The bound is for the `limsup_W` itself, at
  fixed `τ`.
* `limitDecay` (decay of higher clock moments). For every word limit with unit source `q` and
  clock measures `μ t`, the moment `E (Tr μ(t₁ + R + s + t)^p)^r` is at most
  `exp(-D₀ r p (1 - rp) t / 2)` times `E (Tr μ(t₁ + R + s)^p)^r`, with `D₀ = transportD0 b E`. -/
structure RemoteHigherStatement : Prop where
  limsupBound : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 →
      ∃ C c : ℝ, 0 < c ∧ ∀ τ R : ℝ, 0 < τ → 2 ≤ R → ∀ q : ℝ → ℝ,
        IsSourceTest R (τ - R) q → (∀ x, q x ≤ 1) →
          limsup (fun W : ℕ => ∫⁻ w, ENNReal.ofReal
              (fracTrace p (intervalSource b E W ⌊(W : ℝ) * τ⌋₊ q w)) ^ r
              ∂growthPathLaw W b) atTop ≤
            ENNReal.ofReal (C * Real.exp (-(c * R)))
  limitDecay : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 →
    ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : ClockWord → ℝ → Ω → ℂ),
      IsWordLimit b E noTags (fun _ => q) (t₁ + R) P Z →
    ∀ μ : ℝ → Ω → Measure ℝ, (∀ t : ℝ, t₁ + R ≤ t → ∀ᵐ w ∂P, IsClockMeasure Z t w (μ t w)) →
    ∀ s t : ℝ, 0 < s → 0 ≤ t →
      ∫⁻ w, limitFracTrace p (μ (t₁ + R + s + t) w) ^ r ∂P ≤
        ENNReal.ofReal (Real.exp (-(transportD0 b E * r * p * (1 - r * p) * t / 2))) *
          ∫⁻ w, limitFracTrace p (μ (t₁ + R + s) w) ^ r ∂P

/-!
## 2. The Poisson endpoint theorem
-/

/-- **The Poisson Laplace limit**. Fix `0 < b < 1/2`, a bulk energy
`-2 < E < 2` and a nonnegative `C^∞` compactly supported `f`. Then
`lim_{τ→∞} limsup_{W→∞, n/W→τ} |E exp(-Tr f(Λ(H - E))) - exp(-∫(1 - e^{-f}))| = 0`.

The law is the exact physical law of the original ring (`FiniteRealization`, every
ordered spectral realization), with `Λ = Nρ(E)` and `u_α = Nρ(E)(λ_α - E)`.
The limsup is over every critical sequence and every realization. The statement reads: for
every `η > 0` there is `τ₀` such that for every `τ ≥ τ₀`, every critical sequence
(`W → ∞`, `n/W → τ`) and all realizations, eventually `|…| ≤ η`. This is equivalent to the
double limit, because the limsup is nonnegative. -/
def PoissonEndpointLaplace : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ f : CompactlySupportedContinuousMap ℝ ℝ, ContDiff ℝ ∞ (f : ℝ → ℝ) → (∀ x, 0 ≤ f x) →
    ∀ η : ℝ, 0 < η → ∃ τ₀ : ℝ, ∀ τ : ℝ, τ₀ ≤ τ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
        ∀ᶠ j in atTop,
          |(∫ H, Real.exp (-∑ α, f ((R j).spectral.unfoldedEigenvalue E H α))
              ∂((R j).model.law : Measure (s.parameters b hb hb' j).SiteMatrix)) -
            Real.exp (-∫ x, (1 - Real.exp (-f x)))| ≤ η

/-- The limit clause of the Poisson endpoint theorem: `𝒳_{τ,b,E}` tends to
the unit-intensity Poisson process as `τ → ∞`, after the critical limit, for every fixed
`0 < b < 1/2` and bulk `E`. For every critical family (`IsCriticalFamily`, the critical limit of
`endpoints`) and every law satisfying `IsUnitPoissonLaw`,
`spectralProjectionLaw (family τ) → poissonLaw` as `τ → ∞` (`atTop` on `PositiveRatio`). This is
exactly the last conjunct of `HasCriticalEndpoints`. -/
def PoissonEndpointLimitClause : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family →
      ∀ poissonLaw : ProbabilityMeasure (VaguePointMeasure ℝ), IsUnitPoissonLaw poissonLaw →
        Tendsto (fun τ : PositiveRatio => spectralProjectionLaw (family τ)) atTop
          (𝓝 poissonLaw)

/-- **The Poisson endpoint theorem**: both clauses. -/
def PoissonEndpointStatement : Prop := PoissonEndpointLaplace ∧ PoissonEndpointLimitClause

/-!
## 3. The same-volume comparison
-/

/-- **The same-volume log-error bound**: the comparison of the positive
log statistics `𝓡_δ^C` of the original ring and of the independent rings of the same volume.

Setting. Fix `0 < b < 1/2`, a bulk `E`, `f ≥ 0` `C^∞` with
compact support, `ρ = ρ(E)`. There is `c > 0` (the decay rate of the remote-higher theorem). For
every `δ > 0` there is `C = C_{f,δ} ≥ 0`, uniform for `τ ≥ 1` ("the constants are uniform for
`τ ≥ 1`"). Now fix a partition: `m` boxes with fractions `a_i` (`Σ a_i = 1`), buffer length
`R ≥ 2` and ratio `τ ≥ 1`. The complementary paths have length at least `4R`, here in the
form `4R + 1 ≤ a_i τ`. Take
* a critical sequence (`W → ∞`, `n/W → τ`) with physical ring models;
* box block numbers `n_i ≥ 4` with `n_i/W → a_i τ` (the partition is fixed before `W → ∞`) and
  eventually `Σ n_i = n` (same total volume);
* physical models of the box rings (common `W`, `b`).

Then for every `ε > 0`, eventually in `j`, the following objects exist:
* a core `C` of ring blocks and a core of box blocks, each with complement (collars and
  buffers) of size `≤ m(3 + 2RW)`;
* a coupling `γ` of the ring law and the product of the box laws.

They satisfy `E_γ |𝓡_δ^C(H^ring; f) - 𝓡_δ^C(H^boxes; f)| ≤ C m³ e^{-cR} + ε`, with the global
unfolding `Λ = nWρ` on both sides (`positiveLogStatistic`, absorber the block projector of the
core; `H^boxes` in block coordinates `directSumBlockCoords`). This is the bound
`limsup_W ≤ C_{f,δ} m³ e^{-cR}` of the paper.

The paper proves this bound with one specific coupling (the rewiring of the collars) and the
same core on both sides. This statement asks only for some coupling and some cores with the
stated sizes, so it follows from the paper's bound. -/
def PeSameVolumeLogError : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → (∀ x, 0 ≤ f x) →
  ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
  ∀ (m : ℕ) (a : Fin m → ℝ) (R τ : ℝ), 2 ≤ R → 1 ≤ τ → ∑ i, a i = 1 →
    (∀ i, 4 * R + 1 ≤ a i * τ) →
  ∀ (s : CriticalSequence τ) (model : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
    (nb : ℕ → Fin m → ℕ) (hnb : ∀ j i, 4 ≤ nb j i),
    (∀ i, Tendsto (fun j => (nb j i : ℝ) / (s.W j : ℝ)) atTop (𝓝 (a i * τ))) →
    (∀ᶠ j in atTop, ∑ i, nb j i = s.n j) →
  ∀ boxes : ∀ j i,
      (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb').GaussianRingModel,
  ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
    ∃ (Cr : Finset (ZMod (s.parameters b hb hb' j).n)) (Cb : Finset (Fin (∑ i, nb j i))),
      (((Crᶜ).card : ℕ) : ℝ) ≤ m * (3 + 2 * R * s.W j) ∧
      (((Cbᶜ).card : ℕ) : ℝ) ≤ m * (3 + 2 * R * s.W j) ∧
      ∃ γ : Measure ((s.parameters b hb hb' j).SiteMatrix ×
          ∀ i, (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb').SiteMatrix),
        IsProbabilityMeasure γ ∧
        γ.map Prod.fst = ((model j).law : Measure (s.parameters b hb hb' j).SiteMatrix) ∧
        γ.map Prod.snd = Measure.pi (fun i => ((boxes j i).law :
          Measure (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb').SiteMatrix)) ∧
        ∫⁻ w, ENNReal.ofReal
            |positiveLogStatistic w.1 E (((s.parameters b hb hb' j).N : ℝ) *
                Parameters.semicircleDensity E) δ
                (physicalBlockProjector (s.parameters b hb hb' j) Cr) f -
              positiveLogStatistic (directSumBlockCoords (nb j)
                  (fun i => toBlockCoords
                    (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb') (w.2 i)))
                E ((((∑ i, nb j i) * s.W j : ℕ) : ℝ) * Parameters.semicircleDensity E) δ
                (blockProjector Cb) f| ∂γ ≤
          ENNReal.ofReal (C * (m : ℝ) ^ 3 * Real.exp (-(c * R)) + ε)

/-- **The derivation of the same-volume log-error bound**: `PeSameVolumeLogError` follows from
the collar-kernel, matched-traces and transmission-length inputs, the passive-log and singular
log-moments lemmas, and the remote-higher theorem. The steps it stands for are listed in the
module docstring. -/
def PeSameVolumeDerivation : Prop :=
  CollarKernelContract → MatchedTracesContract → TransmissionLengthUniformContract →
    PassiveLog → SingularLogMoments → RemoteHigherStatement → PeSameVolumeLogError

end BlockBand.Endpoints
