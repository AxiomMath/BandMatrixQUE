module

public import BlockBand.Transmission.PassiveCovariance.CovLevel0
public import BlockBand.Transmission.PassiveCovariance.Assembly

/-!
# Reduction of the passive covariance bound to the level-0 means

Named versions of the three level-0 quantities of `cov_level0` (`tauBar`, `srcX1`, `srcX2`),
and the reduction of the whole contract to one statement about **means only**:

* `MeansMatchMain` (the level-0 sources match `mainTensor`; a hypothesis here, derived from the
  mean bounds by `meansMatchMain_of_alp`):
  `|τ̄·conj X₂ + X₁ - mainTensor| ≤ C[W⁻² + W⁻¹(δ₀ + δ₁ + q/W)]` near the jet, strictly passive
  `X`, `‖v₁‖ ≤ ρ`, `‖v₂‖, ‖v₃‖, ‖v₄‖ ≤ 1`.
* `normalized_of_match (hP hA hM) : PassiveCovarianceNormalized` (from `cov_level0`).
* **`passiveCovariance_holds_of_match hGA hLp hP hM : PassiveCovarianceContract`**.

Hypotheses: `GaussianAbsorptionContract`, `GaussianLpGradient`, `GaussianPoincare` and
`MeansMatchMain`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `τ̄ = Σ_q s_q E⟨(𝒢Π𝒢ᴴ)_qq⟩`. -/
def tauBar (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  ∑ q : Fin 2, sRow b q * ∫ ω, SourceMixing.blkTr (gSide b E X false ω *
    wordAlpha (kHat b E X) (gRes b E X ω) 1 ![3] ![portProj, 1] 0) q ∂layerLaw W b .oneBlockOnePort

/-- The crossed source `X₁` of (C1). -/
def srcX1 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (v₁ v₂ v₃ v₄ : Fin W → ℂ) : ℂ :=
  ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
    ((∫ ω, star ((kHat b E X * mbarSide b E X false)ᴴ *ᵥ physVec v₁) ⬝ᵥ
        ((bProj p * wordGamma (kHat b E X) (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k) *ᵥ
        physVec v₄) ∂layerLaw W b .oneBlockOnePort) *
      ∫ ω, star (physVec v₃) ⬝ᵥ ((wordAlpha (kHat b E X) (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k *
        bProj p' * (gSide b E X false ω * wordVal (kHat b E X) (gRes b E X ω) ![3] ![portProj, 1])) *ᵥ
        physVec v₂) ∂layerLaw W b .oneBlockOnePort)

/-- The crossed source `X₂` of (C2). -/
def srcX2 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (v₁ v₂ v₃ v₄ : Fin W → ℂ) : ℂ :=
  ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
    ((∫ ω, star ((kHat b E X * mbarSide b E X false)ᴴ *ᵥ physVec v₂) ⬝ᵥ
        ((bProj p * wordGamma (kHat b E X) (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k) *ᵥ
        physVec v₃) ∂layerLaw W b .oneBlockOnePort) *
      ∫ ω, star (physVec v₄) ⬝ᵥ ((wordAlpha (kHat b E X) (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k *
        bProj p' * (gSide b E X false ω * wordVal (kHat b E X) (gRes b E X ω) ![] ![1])) *ᵥ
        ((kHat b E X * mbarSide b E X false)ᴴ *ᵥ physVec v₁)) ∂layerLaw W b .oneBlockOnePort)

/-- **The means statement**: the level-0 sources reproduce the leading tensor. -/
def MeansMatchMain : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℂ, IsStationaryJet b E s →
    ∃ (ρ d C : ℝ) (W₀ : ℕ), 0 < ρ ∧ 0 < d ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W ≤ d →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, vecNorm v₁ ≤ ρ → vecNorm v₂ ≤ 1 → vecNorm v₃ ≤ 1 →
        vecNorm v₄ ≤ 1 →
        ‖tauBar b E X * conj (srcX2 b E X v₁ v₂ v₃ v₄) + srcX1 b E X v₁ v₂ v₃ v₄ -
            mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W))

/-- `cov_level0` and `MeansMatchMain` give the normalized near-domain bound. -/
theorem normalized_of_match (hP : GaussianPoincare) (hA : PassiveLayer.PassiveBoundsStatement)
    (hM : MeansMatchMain) : PassiveCovarianceNormalized := by
  intro b hb0 hb E h1 h2 s hs
  obtain ⟨ρ₁, d, C₁, W₁, hρ₁, hd, hC₁, hM'⟩ := hM b hb0 hb E h1 h2 s hs
  obtain ⟨ρ₀, C₀, W₀, hρ₀, hC₀, hL⟩ := cov_level0 hP hA hb0 hb h1 h2
  refine ⟨min ρ₀ ρ₁, d, C₀ + C₁, max W₀ W₁, lt_min hρ₀ hρ₁, hd,
    fun W hW X hX hδ v₁ v₂ v₃ v₄ hv₁ hv₂ hv₃ hv₄ => ?_⟩
  have hL' : ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
      tauBar b E X * conj (srcX2 b E X v₁ v₂ v₃ v₄) - srcX1 b E X v₁ v₂ v₃ v₄‖ ≤ C₀ / (W : ℝ) ^ 2 :=
    hL W (le_trans (le_max_left _ _) hW) X hX v₁ v₂ v₃ v₄ (hv₁.trans (min_le_left _ _)) hv₂ hv₃ hv₄
  have hm := hM' W (le_trans (le_max_right _ _) hW) X hX hδ v₁ v₂ v₃ v₄
    (hv₁.trans (min_le_right _ _)) hv₂ hv₃ hv₄
  set δ := jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W
  have hδ0 : 0 ≤ δ := by
    have := passiveMass_nonneg b E hX.posSemidef
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    positivity
  have hW2 : C₀ / (W : ℝ) ^ 2 = C₀ * (W : ℝ)⁻¹ ^ 2 := by rw [inv_pow, div_eq_mul_inv]
  have e : bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ - mainTensor b E s X v₁ v₂ v₃ v₄ =
      (bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
        tauBar b E X * conj (srcX2 b E X v₁ v₂ v₃ v₄) - srcX1 b E X v₁ v₂ v₃ v₄) +
      (tauBar b E X * conj (srcX2 b E X v₁ v₂ v₃ v₄) + srcX1 b E X v₁ v₂ v₃ v₄ -
        mainTensor b E s X v₁ v₂ v₃ v₄) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1' : 0 ≤ (W : ℝ)⁻¹ * δ := by positivity
  calc _ ≤ C₀ * (W : ℝ)⁻¹ ^ 2 + C₁ * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ) := by
        rw [← hW2]; exact add_le_add hL' hm
    _ ≤ (C₀ + C₁) * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ) := by nlinarith

/-- **`PassiveCovarianceContract` from the means statement** (all other inputs are contract
hypotheses). -/
theorem passiveCovariance_holds_of_match (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hM : MeansMatchMain) :
    PassiveCovarianceContract :=
  passiveCovariance_holds_of_normalized hGA hLp
    (normalized_of_match hP (PassiveLayer.passiveBounds_holds hGA hLp) hM)

end BlockBand.Transmission.PassiveCovariance
