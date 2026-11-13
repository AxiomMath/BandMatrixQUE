module

public import BlockBand.Palm.MomentFlow.EventLocal

/-!
# `NormBound` gives the operator-norm hypothesis of the external local law

* `l2opNorm_le_of_normBound`: `NormBound F A → ‖F‖ ≤ N^A`.
* `cehNormBound_of_freshClass`: for `σ > 0`, `(√σ)⁻¹ ‖F‖ ≤ (√σ)⁻¹ N^A` (so `ExternalLocalGUE`
  applies with `C = (√σ₀)⁻¹` uniformly in `σ ≥ σ₀`; `cehNormBound_uniform`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

theorem l2opNorm_le_of_normBound {F : Matrix (Fin N) (Fin N) ℂ} {A : ℝ} (hB : NormBound F A) :
    ‖F‖ ≤ (N : ℝ) ^ A := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    fun x => ?_
  have h := hB (WithLp.ofLp x)
  unfold l2Norm at h
  simpa [EuclideanSpace.norm_eq] using h

theorem cehNormBound_uniform {F : Matrix (Fin N) (Fin N) ℂ} {A : ℝ} (hB : NormBound F A)
    {σ₀ σ : ℝ} (hσ₀ : 0 < σ₀) (hσ : σ₀ ≤ σ) :
    (Real.sqrt σ)⁻¹ * ‖F‖ ≤ (Real.sqrt σ₀)⁻¹ * (N : ℝ) ^ A := by
  have h1 : (Real.sqrt σ)⁻¹ ≤ (Real.sqrt σ₀)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hσ₀) (Real.sqrt_le_sqrt hσ)
  exact mul_le_mul h1 (l2opNorm_le_of_normBound hB) (norm_nonneg _)
    (inv_nonneg.2 (Real.sqrt_nonneg _))

theorem cehNormBound_of_freshClass {F : Matrix (Fin N) (Fin N) ℂ} {A c₀ E r₀ s₀ v₀ : ℝ}
    (hC : FreshClass F A c₀ E r₀ s₀ v₀) {σ : ℝ} (hσ : 0 < σ) :
    (Real.sqrt σ)⁻¹ * ‖F‖ ≤ (Real.sqrt σ)⁻¹ * (N : ℝ) ^ A :=
  cehNormBound_uniform hC.2.1 hσ le_rfl

end BlockBand.Palm.MomentFlow
