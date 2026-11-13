module

public import BlockBand.Endpoints.Transmission.AlongUnique
public import BlockBand.Endpoints.Transmission.AlongTight
public import BlockBand.Endpoints.Transmission.AlongRatio
public import BlockBand.Transmission.LawForced.LawHolds
public import BlockBand.Transmission.LawDecay.ExpDecay
public import BlockBand.Transmission.LawFractional.Main
public import BlockBand.Transmission.EnergyUniform.Holds

/-!
# Transmission limits along moving energies and the energy-uniform transmission law

This file proves that a fixed-energy transmission limit `(P, μ)` is also the limit along every
moving energy (`isTransmissionLimitAlong_of_limit`), and assembles
`TransmissionLawEnergyUniformContract` (`transmissionLawEnergyUniform_holds`).

For the limit along a moving energy:
  - `prob`, `measurable` and `continuous` come from `(P, μ)`.
  - `modulus` is `modulus_along`.
  - For `fdd`, every subsequence of widths has a refinement with an along sub-limit
    (`subLimitExists_along`). That sub-limit solves the base-`E` ratio martingale problem,
    with entrance and local mass bound (`subLimitRatioMP_along`). So does `(P, μ)`,
    which is the constant-energy case of the same statement. The `W`-free uniqueness
    (`fddUnique_of_ratioMP_free`) then makes their fdd integrals equal, and
    `Filter.tendsto_of_subseq_tendsto` concludes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Transmission

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.LawDuality

/-- The constant energy is a moving energy. -/
theorem isMovingEnergy_const' (E : ℝ) : IsMovingEnergy E 0 (fun _ => E) := fun W _ => by
  simp [IsNearEnergy]

/-- A fixed-energy transmission limit is the limit along every moving energy. -/
theorem isTransmissionLimitAlong_of_limit (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {κ : ℝ → ℝ}
    (hκ : IsAbsorptionProfile κ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (hL : IsTransmissionLimit b E κ P μ)
    {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) :
    IsTransmissionLimitAlong b e κ P μ := by
  -- the base limit as a constant-energy along sub-limit along `id`
  have hL' : IsTransmissionSubLimitAlong b (fun _ => E) κ id P μ :=
    ⟨hL.prob, hL.measurable, hL.continuous, hL.fdd⟩
  obtain ⟨hM₀, hEnt₀, hMass₀⟩ := subLimitRatioMP_along hMT hGA hLp hP hb0 hb hE1 hE2
    (isMovingEnergy_const' E) hκ tendsto_id hL'
  have hF₀ : IsFiniteLimitProcess P μ := isFiniteLimitProcess_of_limit hL
  refine ⟨hL.prob, hL.measurable, hL.continuous, ?_,
    modulus_along hMT hGA hLp hb0 hb hE1 hE2 he hκ⟩
  intro k τ hτ Φ
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, hms, Ω', m', P', μ', hS⟩ := subLimitExists_along hMT hGA hLp hb0 hb hE1 hE2 he hκ
    ns hns
  have hφ : Tendsto (ns ∘ ms) atTop atTop := hns.comp hms.tendsto_atTop
  obtain ⟨hM, hEnt, hMass⟩ := subLimitRatioMP_along hMT hGA hLp hP hb0 hb hE1 hE2 he hκ hφ hS
  refine ⟨ms, ?_⟩
  have hlim := hS.fdd k τ hτ Φ
  have heq := fddUnique_of_ratioMP_free hb0 hb hE1 hE2 hκ hS.toFinite hM hEnt hMass hF₀ hM₀ hEnt₀
    hMass₀ k τ hτ Φ
  rw [heq] at hlim
  exact hlim

/-- **The `TransmissionLawEnergyUniformContract.law` field.** -/
theorem transmissionLawEnergyUniform_law (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        (∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e → IsTransmissionLimitAlong b e κ P μ) ∧
        ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
          HasDualDeletionProcess (transportD0 b E) x y ∧
          DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P) := by
  intro b hb0 hb E hE1 hE2 κ hκ
  obtain ⟨Ω, m, P, μ, hL, hD⟩ :=
    BlockBand.Transmission.LawForced.law_holds hMT hGA hLp hP b hb0 hb E hE1 hE2 κ hκ
  exact ⟨Ω, m, P, μ, fun Ce e he =>
    isTransmissionLimitAlong_of_limit hMT hGA hLp hP hb0 hb hE1 hE2 hκ hL he, hD⟩

/-- **The energy-uniform transmission law** `TransmissionLawEnergyUniformContract`, from
`MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient`, `GaussianPoincare` and
`ScalarRecursionContract`. -/
theorem transmissionLawEnergyUniform_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) : TransmissionLawEnergyUniformContract where
  law := transmissionLawEnergyUniform_law hMT hGA hLp hP
  fractional := BlockBand.Transmission.LawFractional.fractional_moving_holds hMT hGA hLp hP
  expDecay := BlockBand.Transmission.LawDecay.expDecay_moving_holds hMT hGA hLp hP
  moments := BlockBand.Transmission.EnergyUniform.fullSourceMomentsEnergyUniform_holds hGA hLp hSR

end BlockBand.Endpoints.Transmission
