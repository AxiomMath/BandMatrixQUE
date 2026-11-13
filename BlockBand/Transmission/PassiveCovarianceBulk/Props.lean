module

public import BlockBand.Transmission.PassiveCovariance.MeansNear
public import BlockBand.Transmission.PassiveCovariance.LevelZeroMatch
public import BlockBand.Transmission.PassiveCovariance.Assembly
public import BlockBand.Transmission.PassiveCovariance.Continuity
public import BlockBand.Transmission.PassiveCovariance.Reduction
public import BlockBand.Transmission.PassiveCovariance.Fluctuation

/-!
# Bulk-uniform versions of the named `Prop`s of the passive-covariance chain

Each statement is the corresponding statement of the passive covariance argument with the
constants uniform on `bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

/-- Bulk-uniform `MeanNear`: the same bound with the constants uniform on `bulkInterval κ`. -/
def MeanNearBulk {ι : Type} (F : WordFam ι) (L : LeadFam ι) : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (d C : ℝ) (W₀ : ℕ), 0 < d ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
     
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDelta b E s X ≤ d →
      ∀ (i : ι) (u v : Fin W → ℂ),
        ‖(∫ ω, star (physVec u) ⬝ᵥ (F i b E W X ω *ᵥ physVec v) ∂layerLaw W b .oneBlockOnePort) -
            bilinear u (L i b E s W X) v‖ ≤
          C * (jetDelta b E s X + (W : ℝ)⁻¹) * (vecNorm u * vecNorm v)

/-- Bulk-uniform `TauNear`: the same bound with the constants uniform on `bulkInterval κ`. -/
def TauNearBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (d C : ℝ) (W₀ : ℕ), 0 < d ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
     
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDelta b E s X ≤ d →
        ‖tauBar b E X - 1‖ ≤ C * (jetDelta b E s X + (W : ℝ)⁻¹)

/-- Bulk-uniform `MeansMatchMain`: the same bound with the constants uniform on `bulkInterval κ`. -/
def MeansMatchMainBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (ρ d C : ℝ) (W₀ : ℕ), 0 < ρ ∧ 0 < d ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
     
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W ≤ d →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, vecNorm v₁ ≤ ρ → vecNorm v₂ ≤ 1 → vecNorm v₃ ≤ 1 →
        vecNorm v₄ ≤ 1 →
        ‖tauBar b E X * conj (srcX2 b E X v₁ v₂ v₃ v₄) + srcX1 b E X v₁ v₂ v₃ v₄ -
            mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W))

/-- Bulk-uniform `PassiveCovarianceNormalized`: the same bound with the constants uniform on
`bulkInterval κ`. -/
def PassiveCovarianceNormalizedBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (ρ d C : ℝ) (W₀ : ℕ), 0 < ρ ∧ 0 < d ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
      jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W ≤ d →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, vecNorm v₁ ≤ ρ → vecNorm v₂ ≤ 1 → vecNorm v₃ ≤ 1 →
        vecNorm v₄ ≤ 1 →
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W))

/-- Bulk-uniform `PassiveCovarianceOnDomainStrict`: the same bound with the constants uniform on
`bulkInterval κ`. -/
def PassiveCovarianceOnDomainStrictBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (d C : ℝ) (W₀ : ℕ), 0 < d ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
      jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W ≤ d →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
            fourNorm v₁ v₂ v₃ v₄

/-- Bulk-uniform `PassiveCovarianceOnDomain`: the same bound with the constants uniform on
`bulkInterval κ`. -/
def PassiveCovarianceOnDomainBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (d C : ℝ) (W₀ : ℕ), 0 < d ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W ≤ d →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
            fourNorm v₁ v₂ v₃ v₄

/-- Bulk-uniform `PassiveFluctuationL2`: the same bound with the constants uniform on
`bulkInterval κ`. -/
def PassiveFluctuationL2Bulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
     
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (freshU b E X ω -
            matrixExpect (freshLaw W b) (freshU b E X)) v) 2 (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v)

end BlockBand.Transmission.CovarianceBulk
