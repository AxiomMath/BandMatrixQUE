module

public import BlockBand.SourceProcess.Closing.PhaseAvg

/-!
# The Hardy-series closing identity

The identities below are proved in the sibling modules `HardyAvg` and `HardyMain`:

* `phaseAvg_closingX`: `E_z X(z) = 0` (phase orthogonality, as `E_z z^k = 0`, `k ≥ 1`);
* `phaseAvg_closingX_mul`: `E_z X Xᴴ = A`, the Hardy-series identity
  `Σ_k r^k t t* (r*)^k = I` in the form `Y = TTᴴ + NYNᴴ`, `TTᴴ = A - NNᴴ`;
* `phaseAvg_closingDefect`: `E_z (C(z) - 1)(C(z) - 1)ᴴ = 2A`.

Hypotheses: `A` is an orthogonal projection, `ΠΠᴴ = A` (the pairing is a partial isometry onto
`A`), `𝕊𝕊ᴴ = 1` (unitarity at real energy), and `N^n → 0` (`‖r‖ < 1` a.s.). For a
source map `F` and an independent Gaussian `h`, `E_{z,h}‖F(C(z)-1)h‖² = Tr(F E_z[(C-1)(C-1)ᴴ] Fᴴ)
= 2 Tr(FAFᴴ)`, the Gaussian closing error.

This file defines the closing correction `closingX` and proves its basic properties
(`closingMap_sub_one`, `isUnit_det_of_tendsto`, `continuous_closingX`, `closingX_fixed`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Closing

open MeasureTheory Matrix Filter Topology
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The closing correction `X(θ) = (1 - zN)⁻¹ zT`, `z = e^{iθ}`. -/
def closingX (S A Pi : Matrix ι ι ℂ) (θ : ℝ) : Matrix ι ι ℂ :=
  (1 - phase θ • closingN S A Pi)⁻¹ * (phase θ • closingT S A Pi)

theorem closingMap_sub_one (S A Pi : Matrix ι ι ℂ) (θ : ℝ) :
    closingMap S A Pi (phase θ) - 1 = closingX S A Pi θ - A := by
  simp only [closingMap, closingX]
  abel

/-- `N^n → 0` makes `1 - zN` invertible on the unit circle. -/
theorem isUnit_det_of_tendsto {N : Matrix ι ι ℂ} (hN : Tendsto (fun n => N ^ n) atTop (𝓝 0))
    {z : ℂ} (hz : ‖z‖ = 1) : IsUnit (1 - z • N).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hfix : z • (N *ᵥ v) = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at hv0
    exact (sub_eq_zero.1 hv0).symm
  have hpow : ∀ n : ℕ, z ^ n • (N ^ n *ᵥ v) = v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc z ^ (n + 1) • (N ^ (n + 1) *ᵥ v) = z ^ n • (N ^ n *ᵥ (z • (N *ᵥ v))) := by
            rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, smul_smul]
        _ = v := by rw [hfix, ih]
  refine hv (funext fun i => ?_)
  have hc : Continuous fun P : Matrix ι ι ℂ => (P *ᵥ v) i :=
    (continuous_apply i).comp (continuous_id.matrix_mulVec continuous_const)
  have ht : Tendsto (fun n => ‖(N ^ n *ᵥ v) i‖) atTop (𝓝 0) := by
    have := ((hc.tendsto 0).comp hN).norm
    simpa using this
  have he : ∀ n, ‖(N ^ n *ᵥ v) i‖ = ‖v i‖ := by
    intro n
    have := congrFun (hpow n) i
    rw [Pi.smul_apply, smul_eq_mul] at this
    rw [← this, norm_mul, norm_pow, hz, one_pow, one_mul]
  simp_rw [he] at ht
  exact norm_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds ht)

section Fixed

variable {S A Pi : Matrix ι ι ℂ}
variable (hU : ∀ θ, IsUnit (1 - phase θ • closingN S A Pi).det)
include hU

theorem continuous_closingX : Continuous (closingX S A Pi) := by
  have hc : Continuous fun θ => (1 : Matrix ι ι ℂ) - phase θ • closingN S A Pi :=
    continuous_const.sub (continuous_phase.smul continuous_const)
  have hinv : Continuous fun θ => (1 - phase θ • closingN S A Pi)⁻¹ := by
    refine continuous_iff_continuousAt.2 fun θ => ?_
    refine (continuousAt_matrix_inv _ ?_).comp hc.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hU θ).ne_zero
  exact hinv.matrix_mul (continuous_phase.smul continuous_const)

/-- The fixed-point form `X = z(T + NX)` of `(1 - zN)X = zT`. -/
theorem closingX_fixed (θ : ℝ) :
    closingX S A Pi θ = phase θ • (closingT S A Pi + closingN S A Pi * closingX S A Pi θ) := by
  have h := Matrix.mul_nonsing_inv_cancel_left _ (phase θ • closingT S A Pi) (hU θ)
  rw [← closingX, Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at h
  rw [smul_add, ← smul_mul_assoc]
  exact h

end Fixed

end BlockBand.SourceProcess.Closing
