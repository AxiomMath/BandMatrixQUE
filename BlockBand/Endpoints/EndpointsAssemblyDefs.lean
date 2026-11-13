module

public import BlockBand.Statements
public import BlockBand.Internal.Contracts.WindowAngular
public import BlockBand.Endpoints.Response.ResponseVarianceLead
public import BlockBand.Endpoints.Response.PassDerivativeLimitResponse

/-!
# Hypotheses of the endpoints assembly

This file states the propositions used as hypotheses by `endpoints_of_inputs`:
* `EpNonzeroResponse`: for every `τ > 0` and integer `m ≠ 0`, the signed response `J_{τ,m}(x,0)`
  is positive at some finite `x > 0`; its body is that of `NonzeroResponseStatement`;
* `EpMarkStatisticLimit`: along every critical sequence, the bounded nonnegative one-mark
  statistics converge to their value under the limiting law, which is finite;
* `EpStationaryWeightFree`: for a spectrally stationary law with unit spectral intensity, the
  limiting one-mark statistic does not depend on the spectral weight;
* `EpRotationFourierDiagonal`: for a law invariant under rotation of the circle marks, the mark
  variance is diagonal in the Fourier basis.

The last two are statements about an abstract law on marked point measures, with no random-matrix
input.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Clocks (physicalOneMark)
open BlockBand.Internal.Contracts.TransmissionPath (transportD0)
open scoped ENNReal BoundedContinuousFunction

/-!
## 1. Nonzero response
-/

/-- **Nonzero response**: for every diffusion constant `D0 > 0`, every `τ > 0` and every integer
`m ≠ 0` there is a finite `x > 0` with `J_{τ,m}(x,0) > 0`, where `J` is the signed response to the
cosine test `rvCosineTest τ m`. The response variance uses `D0 = transportD0 b E > 0`. This is
definitionally the body of `NonzeroResponseStatement`. -/
def EpNonzeroResponse : Prop :=
  ∀ D0 : ℝ, 0 < D0 → ∀ τ : ℝ, 0 < τ → ∀ m : ℤ, m ≠ 0 →
    ∃ x : ℝ, 0 < x ∧ ∃ J : ℝ, 0 < J ∧ IsSignedResponse D0 τ (rvCosineTest τ m) x 0 J

/-!
## 2. Limiting one-mark statistics
-/

/-- The limiting one-mark statistic `E_𝖯 Σ_{(u,ν) ∈ ξ} w(u) Φ(ν)` of a law `𝖯` on marked point
measures, as a lower integral in `[0, ∞]` (the convention of `markVariance` and
`modeVariance`).
-/
def ep_limitOneMark (P : ProbabilityMeasure MarkedPointMeasure) (w : SpectralWeight)
    (Φ : MassProfile →ᵇ ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (w x.1 * Φ x.2) ∂ξ.marked.measure ∂(P : Measure MarkedPointMeasure)

/-- **Convergence of one-mark statistics**: for every critical family, every spectral weight `w`
and every nonnegative bounded continuous mark functional `Φ`, the limiting one-mark statistic is
finite and the physical one-mark statistics converge to it along every critical sequence. -/
def EpMarkStatisticLimit : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family →
      ∀ (τ : PositiveRatio) (w : SpectralWeight) (Φ : MassProfile →ᵇ ℝ), (∀ ν, 0 ≤ Φ ν) →
        ep_limitOneMark (family τ) w Φ ≠ ∞ ∧
        ∀ (s : CriticalSequence τ.1) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
          Tendsto (fun j => physicalOneMark (R j) E w Φ) atTop
            (𝓝 (ep_limitOneMark (family τ) w Φ).toReal)

/-- **Independence of the spectral weight**: for a spectrally stationary law
(`IsSpectrallyStationary`) with unit spectral intensity (so that the weighted intensity is locally
finite), the weighted intensity `A ↦ E_𝖯 Σ 1_A(u)Φ(ν)` of a nonnegative bounded continuous mark
functional is translation invariant, hence a constant multiple of Lebesgue measure; so every
weight `w` of integral one gives the same value. -/
def EpStationaryWeightFree : Prop :=
  ∀ P : ProbabilityMeasure MarkedPointMeasure, IsSpectrallyStationary P →
    HasUnitSpectralIntensity P →
    ∀ (Φ : MassProfile →ᵇ ℝ), (∀ ν, 0 ≤ Φ ν) → ∀ w w' : SpectralWeight,
      ep_limitOneMark P w Φ = ep_limitOneMark P w' Φ

/-- **The Fourier diagonalization**: for a law invariant under simultaneous rotation of the circle
marks (`IsMarkRotationInvariant`) with unit spectral intensity, every spectral weight `w` and every
smooth real test `φ` on `𝕋`, `V_𝖯(w,φ) = Σ_{m ≠ 0} |φ̂_m|² E_𝖯 Σ w(u)|ν(e^{2πim·})|²`. -/
def EpRotationFourierDiagonal : Prop :=
  ∀ P : ProbabilityMeasure MarkedPointMeasure, IsMarkRotationInvariant P →
    HasUnitSpectralIntensity P →
    ∀ (w : SpectralWeight) (φ : ProfileTest),
      BlockBand.Internal.Contracts.WindowAngular.markVariance P w φ =
        ∑' m : ℤ, if m = 0 then 0 else
          ENNReal.ofReal (‖fourierCoeff (fun r : Torus => ((φ r : ℝ) : ℂ)) m‖ ^ 2) *
            BlockBand.Internal.Contracts.WindowAngular.modeVariance P w (-m)

end BlockBand.Endpoints
