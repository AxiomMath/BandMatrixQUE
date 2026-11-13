module

public import BlockBand.SourceProcess.FullSourceCovariance.Level1
public import BlockBand.SourceProcess.FullSourceCovariance.Reduction

/-!
# The strict on-domain covariance statements from three estimates

The equal- and opposite-sign covariance bounds for `Δ` on the scalar domain, at strictly passive
inputs, follow from three estimates:

* `FirstTermBound`: `|E[Ω₀FΨ]|, |E[Ω₀FΨ̄]| ≤ C·covErr·∏‖v‖`, `Ψ = x'*Δ⁰y'`;
* `CrossedSameBound`: `|E[F(x',y)Φ] - (σ₋/W)(x*y')(x'*y)| ≤ C·covErr·∏‖v‖`;
* `CrossedOppBound`: `|E[Φ'·conj H] - (σ₊/W)(x*x')(y'*y)| ≤ C·covErr·∏‖v‖`.

* **`deltaCovarianceSameOnDomainStrict_of hA hGA hF hS`**,
  **`deltaCovarianceOppositeOnDomainStrict_of hA hGA hF hO`**: triangle inequality, radius
  `min d₁ d₂`, constant `C₁ + C₂`.
* **`fullSourceCovarianceEnergyUniform_of_bounds hGA hLp hF hS hO`**,
  **`fullSourceCovariance_of_bounds hGA hLp hF hS hO`**: both full-source covariance statements,
  via `deltaCovariance*OnDomain_of_strict` and the reduction to `Δ`
  (`hA = passiveBounds_holds hGA hLp`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Internal.Contracts.TransmissionUniform2
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The first terms** `E[Ω₀FΨ]`, `E[Ω₀FΨ̄]` are `O(covErr)` (from the self-energy centring and
`Ω̄ = O(δ₀ + W⁻²)`). -/
def FirstTermBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∃ d : ℝ, 0 < d ∧
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDist b E s X ≤ d →
      ∀ x y x' y' : Fin W → ℂ,
        ‖∫ ω, omega0 b E X ω * fForm b E X x y ω *
            bilinear x' (freshDelta b E X ω - matrixExpect (freshLaw W b) (freshDelta b E X)) y'
            ∂freshLaw W b‖ ≤ C * covErr b E s X * fourNorm x y x' y' ∧
        ‖∫ ω, omega0 b E X ω * fForm b E X x y ω *
            star (bilinear x' (freshDelta b E X ω -
              matrixExpect (freshLaw W b) (freshDelta b E X)) y') ∂freshLaw W b‖ ≤
          C * covErr b E s X * fourNorm x y x' y'

/-- **The equal-sign crossed product** `E[F(x',y)Φ(x,y')] = (σ₋/W)(x*y')(x'*y)`
up to `O(covErr)` (`β = α = +`). -/
def CrossedSameBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∃ d : ℝ, 0 < d ∧
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDist b E s X ≤ d →
      ∀ x y x' y' : Fin W → ℂ,
        ‖(∫ ω, fForm b E X x' y ω * phiSame b E X x y' ω ∂freshLaw W b) -
            sigmaMinus b E s / W * crossedTensor x y x' y' 1 1‖ ≤
          C * covErr b E s X * fourNorm x y x' y'

/-- **The opposite-sign crossed product** `E[Φ'(x,x')·conj H(y,y')] =
(σ₊/W)(x*x')(y'*y)` up to `O(covErr)` (`β = -`, `α = +`). -/
def CrossedOppBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∃ d : ℝ, 0 < d ∧
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDist b E s X ≤ d →
      ∀ x y x' y' : Fin W → ℂ,
        ‖(∫ ω, phiOpp b E X x x' ω * star (hForm b E X y y' ω) ∂freshLaw W b) -
            ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear x 1 x' * bilinear y' 1 y)‖ ≤
          C * covErr b E s X * fourNorm x y x' y'

/-- **The equal-sign strict statement** from the first-term and crossed bounds. -/
theorem deltaCovarianceSameOnDomainStrict_of (hA : PassiveBoundsStatement)
    (hGA : GaussianAbsorptionContract) (hF : FirstTermBound) (hS : CrossedSameBound) :
    DeltaCovarianceSameOnDomainStrict := by
  intro b hb0 hb κ hκ
  obtain ⟨d₁, hd₁, C₁, W₁, h₁⟩ := hF b hb0 hb κ hκ
  obtain ⟨d₂, hd₂, C₂, W₂, h₂⟩ := hS b hb0 hb κ hκ
  obtain ⟨W₃, h₃⟩ := cov_same_level1 hA hGA hb0 hb hκ
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, C₁ + C₂, max (max W₁ W₂) W₃,
    fun W hW E hE s hs X hY hd x y x' y' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW₂⟩, hW₃⟩ := hW
  rw [h₃ W hW₃ E hE X hY x y x' y', add_sub_assoc, add_mul, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (h₁ W hW₁ E hE s hs X hY (hd.trans (min_le_left _ _)) x y x' y').1
    (h₂ W hW₂ E hE s hs X hY (hd.trans (min_le_right _ _)) x y x' y'))

/-- **The opposite-sign strict statement** from the first-term and crossed bounds. -/
theorem deltaCovarianceOppositeOnDomainStrict_of (hA : PassiveBoundsStatement)
    (hGA : GaussianAbsorptionContract) (hF : FirstTermBound) (hO : CrossedOppBound) :
    DeltaCovarianceOppositeOnDomainStrict := by
  intro b hb0 hb κ hκ
  obtain ⟨d₁, hd₁, C₁, W₁, h₁⟩ := hF b hb0 hb κ hκ
  obtain ⟨d₂, hd₂, C₂, W₂, h₂⟩ := hO b hb0 hb κ hκ
  obtain ⟨W₃, h₃⟩ := cov_opp_level1 hA hGA hb0 hb hκ
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, C₁ + C₂, max (max W₁ W₂) W₃,
    fun W hW E hE s hs X hY hd x y x' y' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW₂⟩, hW₃⟩ := hW
  rw [h₃ W hW₃ E hE X hY x y x' y', add_sub_assoc, add_mul, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (h₁ W hW₁ E hE s hs X hY (hd.trans (min_le_left _ _)) x y x' y').2
    (h₂ W hW₂ E hE s hs X hY (hd.trans (min_le_right _ _)) x y x' y'))

/-- **The additive contract** from the three named estimates and input hypotheses. -/
theorem fullSourceCovarianceEnergyUniform_of_bounds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hF : FirstTermBound) (hS : CrossedSameBound)
    (hO : CrossedOppBound) : FullSourceCovarianceEnergyUniformContract :=
  fullSourceCovarianceEnergyUniform_of_onDomain hGA hLp
    (deltaCovarianceSameOnDomain_of_strict hGA
      (deltaCovarianceSameOnDomainStrict_of (passiveBounds_holds hGA hLp) hGA hF hS))
    (deltaCovarianceOppositeOnDomain_of_strict hGA
      (deltaCovarianceOppositeOnDomainStrict_of (passiveBounds_holds hGA hLp) hGA hF hO))

/-- **`FullSourceCovarianceContract`** from the three estimates `FirstTermBound`,
`CrossedSameBound`, `CrossedOppBound` and the input hypotheses. -/
theorem fullSourceCovariance_of_bounds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hF : FirstTermBound) (hS : CrossedSameBound)
    (hO : CrossedOppBound) : FullSourceCovarianceContract :=
  fullSourceCovariance_of_uniform (fullSourceCovarianceEnergyUniform_of_bounds hGA hLp hF hS hO)

end BlockBand.SourceProcess.FullSourceCovariance
