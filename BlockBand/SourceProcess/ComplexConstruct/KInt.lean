module

public import BlockBand.SourceProcess.ComplexUnique.Noise
public import BlockBand.SourceProcess.Stochastic.GramChar.Conditional
public import BlockBand.Internal.Contracts.TransmissionPath

/-!
# The ambient `𝒦` noise integral `𝒴 = ∫ kNoise(X) dW`

`AmbientKIntegral`: for a global solution `X` of the ambient finite source frame SDE
(constraint `TwoProjection` at time `0`), there is an Itô process `𝒴` in `Matrix c' c' ℂ`
with `𝒴₀ = 0`, zero drift and diffusion `a ↦ kNoise D₀ η P 𝖣' a (X_t)` (the ambient `𝒦`
coefficient, `η = etaZ b E`, `D₀ = transportD0 b E`). It is proved as `ambientKIntegral_holds`.

Proof outline: the joint SDE `(X, 𝒴)` with locally Lipschitz coefficients
(`sourceDrift`, `0`; `sourceDiffusion`, `kNoise`; `contDiff_kNoise`) has strong exit-time
solutions of every radius (`exists_solutionUntil_exitTime_strong`); their frame part is `X` before
the exit (pathwise uniqueness), and Doob's `L²` inequality with `‖kNoise(X)‖ ≤ C_M` before the
exit of `X` from the `M`-ball gives the escape property, so `exists_isSDESolution_of_family`
glues a global solution.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.ComplexUnique
open scoped NNReal Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  BlockBand.SourceProcess.Stochastic.SourceSDE.frobBorelSpace

/-- **The ambient `𝒦` noise integral.** -/
def AmbientKIntegral : Prop :=
  ∀ (b E : ℝ), 0 < b → b < 1 / 2 → -2 < E → E < 2 →
  ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (ι c' : Type) [Fintype ι] [DecidableEq ι] [Fintype c'] [DecidableEq c'] (Naux : ℕ)
    (P : Matrix ι ι ℂ) (D' : Matrix c' c' ℂ), IsNearProjection P Naux → IsSignature D' →
  ∀ ξ : DriverSample S (SourceNoise ι) → Matrix ι c' ℂ,
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D' (ξ x)) →
  ∀ X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c' ℂ,
    IsSDESolution μ (sourceDrift (transportD0 b E) Naux P)
      (sourceDiffusion (transportD0 b E) P D') ξ X →
    ∃ Y : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c' c' ℂ,
      IsNativeItoProcess μ Y (fun _ _ => 0)
        (fun a t x => kNoise (transportD0 b E) (etaZ b E) P D' a (X t x)) ∧ ∀ x, Y 0 x = 0

end BlockBand.SourceProcess.ComplexConstruct
