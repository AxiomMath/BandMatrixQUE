module

public import BlockBand.SourceProcess.ComplexCutoff.KNoiseAlg

/-!
# `ExtendedRankFreeCoupling` from a generic stopped-bracket coupling

`StoppedBracketCoupling` is the tail bound for the increments of two driftless Itô processes whose
diffusion coefficients are bounded by `C(L)` and Lipschitz with constant `C(L)` in two born SDE
solutions with the same noise, on `{‖X₁‖² + ‖X₂‖² ≤ L}`.

* `extendedRankFreeCoupling_of`: the `𝒦` coefficient satisfies the bracket hypothesis with
  `C_L = kC D₀ η L`, so `StoppedBracketCoupling` gives `ExtendedRankFreeCoupling`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCutoff

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.ComplexUnique
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal ComplexConjugate

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- For `D₀` and any `C: ℝ → ℝ`: under every hypothesis of
`RankFreeCoupling`, for Itô processes `Y_i` (`IsNativeItoProcess`; zero drift, diffusions `σ_i`) with
`Σ_a ‖σ₁_a‖²_HS ≤ C_L` and `Σ_a ‖σ₁_a - σ₂_a‖²_HS ≤ C_L ‖X₁ - X₂‖²_HS` at every `(t, x)` with
`‖X₁‖² + ‖X₂‖² ≤ L`, the bounds of `ExtendedRankFreeCoupling` hold with `C_L`.
-/
def StoppedBracketCoupling : Prop :=
  ∀ (D0 : ℝ) (C : ℝ → ℝ),
  ∀ (ι c S : Type) [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (Naux : ℕ) (P : Matrix ι ι ℂ)
    (D : Matrix c c ℂ), 0 < D0 → IsNearProjection P Naux → IsSignature D →
  ∀ ξ₁ ξ₂ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ,
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ₁ →
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ₂ →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ₁ x)) →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ₂ x)) →
  ∀ (nb : ℕ) (tb : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0) (col : Fin nb → c)
    (w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ) (β : Fin nb → ℝ)
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (fun x => ((tb k x : ℝ≥0) : WithTop ℝ≥0))),
    (∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k)) →
    Function.Injective col → (∀ k j, D (col k) j = 0 ∧ D j (col k) = 0) →
    (∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ i, ξ₁ x i (col k) = 0 ∧ ξ₂ x i (col k) = 0) →
    (∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      P *ᵥ w k x = w k x ∧ ∑ i, ‖w k x i‖ ^ 2 = β k) →
  ∀ X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ,
    IsBornSDESolution μ D0 Naux P D ξ₁ (frameBirthJump tb col w) X₁ →
    IsBornSDESolution μ D0 Naux P D ξ₂ (frameBirthJump tb col w) X₂ →
    (∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ j, j ≠ col k →
      (∑ i, conj (X₁ (tb k x) x i j) * w k x i = 0) ∧
        ∑ i, conj (X₂ (tb k x) x i j) * w k x i = 0) →
  ∀ (Y₁ Y₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c c ℂ)
    (σ₁ σ₂ : SourceNoise ι → ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c c ℂ),
    IsNativeItoProcess μ Y₁ (fun _ _ => 0) σ₁ → IsNativeItoProcess μ Y₂ (fun _ _ => 0) σ₂ →
    (∀ (L : ℝ) (t : ℝ≥0) (x : DriverSample S (SourceNoise ι)),
      hsSq (X₁ t x) + hsSq (X₂ t x) ≤ L →
        ∑ a, hsSq (σ₁ a t x) ≤ C L ∧
          ∑ a, hsSq (σ₁ a t x - σ₂ a t x) ≤ C L * hsSq (X₁ t x - X₂ t x)) →
  ∀ (L u δ : ℝ) (t : ℝ≥0), 0 < L → 0 < u → 0 < δ →
    driverLaw (κ := SourceNoise ι) μ
        {x | δ < hsSq ((Y₁ t x - Y₁ 0 x) - (Y₂ t x - Y₂ 0 x))} ≤
      2 * ((∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x) + hsSq (ξ₂ x)) ∂driverLaw (κ := SourceNoise ι) μ) +
            ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal L +
        ENNReal.ofReal (Real.exp (D0 * L ^ 2 * t / 2)) *
          (∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x - ξ₂ x)) ∂driverLaw (κ := SourceNoise ι) μ) /
          ENNReal.ofReal u +
        ENNReal.ofReal (C L * u * t / δ) ∧
    driverLaw (κ := SourceNoise ι) μ {x | δ < hsSq (Y₁ t x - Y₁ 0 x)} ≤
      ((∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x) + hsSq (ξ₂ x)) ∂driverLaw (κ := SourceNoise ι) μ) +
            ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal L +
        ENNReal.ofReal (C L * t / δ)

/-- **`ExtendedRankFreeCoupling` from `StoppedBracketCoupling`**, with `C_L = kC D₀ η L`. -/
theorem extendedRankFreeCoupling_of (h : StoppedBracketCoupling) : ExtendedRankFreeCoupling := by
  intro D0 η
  refine ⟨kC D0 η, ?_⟩
  intro ι c S _ _ _ _ _ μ _ Naux P D hD0 hP hD ξ₁ ξ₂ hξ₁ hξ₂ hξ₁0 hξ₂0 nb tb col w β hτ hw hcol
    hDcol hξc hwP X₁ X₂ hX₁ hX₂ hperp Y₁ Y₂ hY₁ hY₂
  refine h D0 (kC D0 η) ι c S μ Naux P D hD0 hP hD ξ₁ ξ₂ hξ₁ hξ₂ hξ₁0 hξ₂0 nb tb col w β hτ hw
    hcol hDcol hξc hwP X₁ X₂ hX₁ hX₂ hperp Y₁ Y₂ _ _ hY₁ hY₂ fun L t x hL => ?_
  simp only [hsSq_eq] at hL ⊢
  exact ⟨kNoise_size_le hD0.le η hP hD (by nlinarith [sq_nonneg ‖X₂ t x‖]),
    kNoise_sub_le hD0.le η hP hD hL⟩

end BlockBand.SourceProcess.ComplexCutoff
