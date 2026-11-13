module

public import BlockBand.SourceProcess.ComplexConstruct.Interface
public import BlockBand.SourceProcess.ModelExist.TransMain

/-!
# The `𝒦` extension of a born ambient Gram process

Setting: the construction of the positive model (`ModelExist`). On the driver space, `X` solves
the finite source frame SDE in an ambient space `ι` with near projection `P` and
signature `𝖣'` on columns `c'`; `𝒢 = gramPair P X`. Target columns `SrcCol K π` are born at
`𝓖₀`-measurable times `θ_y` with `𝓕_{θ_y}`-measurable vectors `λ_y ∈ ℂ^{c'}`, `L_t 𝖣 L_tᴴ = 𝖣'`
(`L_t = bornL θ λ t`), and the continuous part of the born Gram process `G = L_tᴴ 𝒢_t L_t` is
the transformed increment of `𝒢` (`BornRepresents`). These are exactly the hypotheses of
`isBornGramSolution_bornG`. `BornKExtension` states that a `𝒦` extension exists in this setting.

Proof sketch (not formalized; `BornKExtension` is used only as a hypothesis).
`𝒴_t = ∫_0^t kNoise(X_s) dW_s` (`ComplexUnique.kNoise`, the
ambient coefficient `-2iη w̄_a XᴴPᴴE_{xy}P'ᴴX`), an Itô process (`IsNativeItoProcess`) with zero drift
(`ItoNative.exists_integralProcess` and localization). Set
`𝒦_ij(t) = J_𝒦(t)_ij + λ_iᴴ (𝒴_t - 𝒴_{t ∧ (θ_i ∨ θ_j)}) λ_j`. The brackets are the
frame-generic `sum_kNoise_mul`, `sum_kNoise_mul_star`, `sum_kNoise_mul_gram` at `V = X_t`,
identified with `B` and `C₀ = B + M𝖣M`, `C₁` of `𝒢` (`raw_B`, `raw_C0`, `raw_C1`
under `TwoProjection`), then transported to `G` by congruence (`L𝖣Lᴴ = 𝖣'`). The
martingale clauses follow as for the positive model (`CLocMart.shift`, `pair`,
`weight`), with one change: `𝒦` is not bounded before the Gram trace stop, so the localized
martingales are closed with the `L²` bound `E|𝒦^τ_t|² ≤ C_L t` (bracket bounded by the trace)
and Doob, instead of a uniform bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.ModelExist
open scoped NNReal Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- **The `𝒦` extension of a born ambient Gram process**: in the setting above, a `𝒦` extension
exists. The frame SDE is read with the Frobenius norm on matrices, as in `RankFreeCoupling`. -/
def BornKExtension : Prop :=
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
  ∀ (K : ℕ) (π F : Type) [Fintype π] [DecidableEq π] [Fintype F]
    (θ : SrcCol K π → DriverSample S (SourceNoise ι) → ℝ≥0)
    (lam : SrcCol K π → DriverSample S (SourceNoise ι) → c' → ℂ)
    (hθ : ∀ y, Measurable[driverAugmented (κ := SourceNoise ι) μ 0] (θ y)),
    (∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace] (lam y)) →
    (∀ t x, bornL θ lam t x * srcSignature K π * (bornL θ lam t x)ᴴ = D') →
  ∀ (j : F → GramState (SrcCol K π)) (β : F → DriverSample S (SourceNoise ι) → ℝ),
    (∀ f, Measurable[driverAugmented (κ := SourceNoise ι) μ 0] (β f)) →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      BornRepresents (fun t x => gramPair P (X t x)) θ lam j β x) →
  ∀ JK : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix π π ℂ,
    (∀ t, StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] (JK t)) →
    ∃ Kc : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix π π ℂ,
      IsComplexSourceExtension (driverLaw (κ := SourceNoise ι) μ)
        (driverAugmented (κ := SourceNoise ι) μ) b E (srcSignature K π) (bJ j β)
        (bornG (fun t x => gramPair P (X t x)) θ lam) JK Kc ∧ ∀ x, Kc 0 x = JK 0 x

end BlockBand.SourceProcess.ComplexConstruct
