module

public import BlockBand.Transmission.PathJet.JetPathStep
public import BlockBand.Transmission.PathJet.Statement

/-!
# `PassiveJetMoments`: assembly

The first-jet path moments hold under the input hypotheses.

`passiveJetMoments_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
(hLp : GaussianLpGradient) : PassiveJetMoments`.

* `δ₀`: `PassiveInitialScalarContract.moment` (`passiveInitialScalar_moment hMT`).
* `δ₁`: the a.s. jet step (`ae_jet_step`) with the jet mean step
  (`passiveJetMeanStep_holds`, through `passiveBounds_holds hGA hLp`) and the generic
  `L^p` recursion `eLpNorm_linrec` with `ρ = max ρ₁ ½`, `‖δ_{1,1}‖_p ≤ M`, and per-step error
  `(C₂ + M/d₀)‖δ_{0,j}‖_p + C/W² + ‖ξ_{j+1}‖_p ≤ B/W` (`ξ` by `eLpNorm_stepFluctOf_le` and
  `passiveJetFluctuationStep_holds hGA hLp`). Then `ρ^{r-1} ≤ 2/W` once
  `r ≥ C₁ log W`, `C₁ = 1/log(1/ρ)` (`pow_le_two_div`), so `C₁` depends on `b, κ` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder

variable {W : ℕ}

theorem pow_le_two_div {ρ : ℝ} {r : ℕ} (hρ1 : 1 / 2 ≤ ρ) (hρ : ρ < 1) (hW : 1 ≤ W) (hr1 : 1 ≤ r)
    (hr : 1 / Real.log (1 / ρ) * Real.log W ≤ r) : ρ ^ (r - 1) ≤ 2 / W := by
  have hρ0 : 0 < ρ := by linarith
  have hL : 0 < Real.log (1 / ρ) := Real.log_pos (by rw [lt_div_iff₀ hρ0]; linarith)
  have hx : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : Real.log W ≤ r * Real.log (1 / ρ) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hL] at hr; exact hr
  have h2 : ρ ^ r ≤ 1 / W := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_div one_ne_zero
      hx.ne', Real.log_one, zero_sub]
    rw [Real.log_div one_ne_zero hρ0.ne', Real.log_one, zero_sub] at h1
    linarith
  have h3 : ρ ^ r = ρ ^ (r - 1) * ρ := by rw [← pow_succ]; congr 1; omega
  rw [h3] at h2
  have h4 : ρ ^ (r - 1) / 2 ≤ ρ ^ (r - 1) * ρ :=
    by have := pow_nonneg hρ0.le (r - 1); nlinarith
  rw [le_div_iff₀ hx] at h2 ⊢
  nlinarith

theorem eLpNorm_err_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 1 ≤ p) {f g : Ω → ℝ} {k c a₀ aξ : ℝ} (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hfa : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal a₀)
    (hga : eLpNorm g (ENNReal.ofReal p) μ ≤ ENNReal.ofReal aξ) (ha₀ : 0 ≤ a₀) (haξ : 0 ≤ aξ) :
    eLpNorm (fun ω => k * f ω + c + g ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (k * a₀ + c + aξ) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have h1 := eLpNorm_add_le (f := fun ω => k * f ω + c) (g := g) (μ := μ) hp1
  have h2 := eLpNorm_add_le (f := fun ω => k * f ω) (g := fun _ => c) (μ := μ) hp1
  have hsm : eLpNorm (fun ω => k * f ω) (ENNReal.ofReal p) μ =
      ENNReal.ofReal k * eLpNorm f (ENNReal.ofReal p) μ := by
    have := eLpNorm_const_smul k f (ENNReal.ofReal p) μ
    rw [show (k • f) = fun ω => k * f ω from rfl, Real.enorm_eq_ofReal hk] at this
    exact this
  have hc' : eLpNorm (fun _ : Ω => c) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal c := by
    refine (eLpNorm_le_of_ae_bound (C := c) aestronglyMeasurable_const (ae_of_all _ fun _ => by
      rw [Real.norm_of_nonneg hc])).trans (le_of_eq ?_)
    simp
  calc eLpNorm (fun ω => k * f ω + c + g ω) (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun ω => k * f ω + c) (ENNReal.ofReal p) μ + eLpNorm g (ENNReal.ofReal p) μ := h1
    _ ≤ (ENNReal.ofReal k * ENNReal.ofReal a₀ + ENNReal.ofReal c) + ENNReal.ofReal aξ := by
        gcongr
        refine h2.trans (add_le_add ?_ hc')
        rw [hsm]; exact mul_le_mul' le_rfl hfa
    _ = ENNReal.ofReal (k * a₀ + c + aξ) := by
        rw [← ENNReal.ofReal_mul hk, ← ENNReal.ofReal_add (by positivity) hc,
          ← ENNReal.ofReal_add (by positivity) haξ]

end BlockBand.Transmission.PathJet
