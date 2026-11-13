module

public import BlockBand.Palm.ReferenceFlowHolds
public import BlockBand.Palm.ReferenceFlowBackward

/-!
# Existence of the reference flow

The reference flow exists, with its mass identity, for deterministic coefficients and along the
eigenvalue paths of the matrix flow.

* `referenceFlowExistence_holds`: `ReferenceFlowExistence N` (deterministic coefficients).
* `referenceFlowStatement_holds`: `ReferenceFlowStatement` (every collision-free eigenvalue path,
  with the coefficients `shortRate`, `refDamping`).
* `referenceFlowAEStatement_holds`: `ReferenceFlowAEStatement` (`flowLaw`-a.e. path).

Hypotheses (no estimate is assumed): `LinearRotationFlowContract` (the rotation flow), Itô's
formula `ItoFormulaFor` and the Itô product rule `ItoProductRuleFor` on `N × N` matrices with the
Frobenius norm, `MultivariateGaussianIBP`, and for the a.e. form `DysonBrownianMotion`
(non-collision).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Set Filter Matrix BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow LinearRotationFlowContract)
open BlockBand.Internal.Contracts.Transmission (DysonBrownianMotion)
open BlockBand.Internal.Contracts.Inputs (MultivariateGaussianIBP)
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic
open BlockBand.Palm.RelativeLocalization.StochasticBridge
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobeniusBorelSpace

/-- Existence of the reference flow for deterministic coefficients. -/
theorem referenceFlowExistence_holds {N : ℕ} (hRF : LinearRotationFlowContract N)
    (hProd : ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      ItoProductRuleFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ)
        (Matrix (Fin N) (Fin N) ℂ) (Matrix (Fin N) (Fin N) ℂ))
    (hIto : ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      ItoFormulaFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ) ℝ)
    (hIBP : MultivariateGaussianIBP) : ReferenceFlowExistence N := by
  intro S _ μ _ r κ a c b hac hb0 hr hκ hrs hr0 hκ0 hfloor
  obtain ⟨𝓝, h𝓝⟩ := exists_reflectedFlow hRF μ hac hr hκ hrs hr0 hκ0
  have hcon := kernelContracts_of (hProd S μ) hac hr hκ hrs hr0 h𝓝
  exact ⟨refKernel c 𝓝, refFactor c 𝓝, isReferenceFlow_of hRF hac hb0 hr hκ hrs hr0 hκ0 hfloor
    h𝓝 hcon (backwardEquation_holds hIto hIBP hac hb0 hr hκ hrs hr0 hκ0 hfloor h𝓝 hcon)⟩

/-- Existence of the reference flow, with its mass identity, along every collision-free eigenvalue
path. -/
theorem referenceFlowStatement_holds (hRF : ∀ N, LinearRotationFlowContract N)
    (hProd : ∀ (N : ℕ) (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      ItoProductRuleFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ)
        (Matrix (Fin N) (Fin N) ℂ) (Matrix (Fin N) (Fin N) ℂ))
    (hIto : ∀ (N : ℕ) (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      ItoFormulaFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ) ℝ)
    (hIBP : MultivariateGaussianIBP) : ReferenceFlowStatement := by
  intro N F hF hN a c _ha hac b₀ hb₀ ℓ hℓ ω hω S _ μ _
  have hfl : 0 < b₀ * N / ℓ := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    positivity
  exact referenceFlowExistence_holds (hRF N) (hProd N) (hIto N) hIBP S μ
    (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c (b₀ * N / ℓ) hac hfl
    (continuousOn_shortRate hF hω ℓ) (continuousOn_refDamping hF hω b₀ ℓ)
    (shortRate_comm F a ω ℓ) (shortRate_nonneg F a ω ℓ) (refDamping_nonneg F a b₀ ω ℓ)
    (fun _ _ _ => le_max_right _ _)

/-- Existence of the reference flow, with its mass identity, for `flowLaw`-almost every eigenvalue
path. -/
theorem referenceFlowAEStatement_holds (hRF : ∀ N, LinearRotationFlowContract N)
    (hProd : ∀ (N : ℕ) (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      ItoProductRuleFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ)
        (Matrix (Fin N) (Fin N) ℂ) (Matrix (Fin N) (Fin N) ℂ))
    (hIto : ∀ (N : ℕ) (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      ItoFormulaFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ) ℝ)
    (hIBP : MultivariateGaussianIBP) (hDBM : ∀ N, DysonBrownianMotion N) :
    ReferenceFlowAEStatement := by
  intro N F hF hN a c ha hac b₀ hb₀ ℓ hℓ
  filter_upwards [ae_noCollision (hDBM N) hF ha c] with ω hω S _ μ _
  exact referenceFlowStatement_holds hRF hProd hIto hIBP N F hF hN a c ha hac b₀ hb₀ ℓ hℓ ω hω
    S μ

end BlockBand.Palm.ReferenceFlow
