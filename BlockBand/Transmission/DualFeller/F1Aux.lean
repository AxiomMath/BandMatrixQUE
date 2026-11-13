module

public import BlockBand.Transmission.DualFeller.Pathwise

/-!
# Constants for start continuity: modulus of `π`, start bounds, a sum rule

Deterministic.
* `exists_proj_mod`: on the sup-norm `n`-ball of `ℝ⁶`, `pairDist(u, v) < r` moves `π` by less
  than any given `ρ > 0` for a suitable `r > 0` (`π` is `C¹`, hence Lipschitz on the ball).
* `liftLyap_le_of_norm`: on `liftM`, `‖ξ‖ ≤ R` gives `g(π ξ) ≤ (2R² + 1)(1 + 2R²)` for the lift
  Lyapunov function `g = S(1 + log(1 + x))`.
* `add_ofReal_le`: `x ≤ a`, `y ≤ b` give `x + y ≤ a + b` in `ℝ≥0∞` for reals `a, b ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open MeasureTheory Real
open BlockBand.Transmission.DualLift
open scoped NNReal ENNReal

theorem exists_proj_lip (m : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ u v : Fin 6 → ℝ, ‖u‖ ≤ m → ‖v‖ ≤ m →
    ‖liftProj u - liftProj v‖ ≤ K * ‖u - v‖ := by
  have hf : ContDiff ℝ 1 liftProj := contDiff_liftProj.of_le le_top
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin 6 → ℝ) m).exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  have hL := (convex_closedBall (0 : Fin 6 → ℝ) m).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    (C := (max C 0).toNNReal) (fun x _ => hf.differentiable one_ne_zero x)
    (fun x hx => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
      exact (hC x hx).trans (le_max_left _ _))
  refine ⟨max C 0, le_max_right _ _, fun u v hu hv => ?_⟩
  have h := hL.dist_le_mul u (mem_closedBall_zero_iff.2 hu) v (mem_closedBall_zero_iff.2 hv)
  rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _)] at h

theorem exists_proj_mod (m : ℝ) {ρ : ℝ} (hρ : 0 < ρ) : ∃ r : ℝ, 0 < r ∧
    ∀ u v : Fin 6 → ℝ, ‖u‖ ≤ m → ‖v‖ ≤ m → pairDist (u, v) < r →
      ‖liftProj u - liftProj v‖ < ρ := by
  obtain ⟨K, hK0, hK⟩ := exists_proj_lip m
  refine ⟨(ρ / (K + 1)) ^ 2, by positivity, fun u v hu hv h => ?_⟩
  have h1 : ‖u - v‖ < ρ / (K + 1) := by
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    exact (sq_norm_le_pairDist (u, v)).trans_lt h
  have h2 : (K + 1) * ‖u - v‖ < ρ := by
    rw [lt_div_iff₀ (by positivity)] at h1; linarith
  nlinarith [hK u v hu hv, norm_nonneg (u - v)]

theorem liftLyap_le_of_norm {ξ : Fin 6 → ℝ} (h : ξ ∈ liftM) {R : ℝ} (hR : ‖ξ‖ ≤ R) :
    liftLyap (liftProj ξ) ≤ (2 * R ^ 2 + 1) * (1 + 2 * R ^ 2) := by
  have hc : ∀ i, |ξ i| ≤ R := fun i => by
    have := norm_le_pi_norm ξ i; rw [Real.norm_eq_abs] at this; linarith
  have hx : lx ξ ≤ 2 * R ^ 2 := by
    unfold lx
    nlinarith [abs_mul_abs_self (ξ 0), abs_mul_abs_self (ξ 1), hc 0, hc 1, abs_nonneg (ξ 0),
      abs_nonneg (ξ 1)]
  have hx0 := lx_nonneg ξ
  have hy := ly_mem_of_mem h
  have hlog : Real.log (1 + lx ξ) ≤ lx ξ := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + lx ξ); linarith
  have hlog0 : 0 ≤ Real.log (1 + lx ξ) := Real.log_nonneg (by linarith)
  simp only [liftLyap, liftProj_zero, liftProj_one]
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)

theorem add_ofReal_le {x y : ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x ≤ ENNReal.ofReal a) (hy : y ≤ ENNReal.ofReal b) : x + y ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_add ha hb]; exact add_le_add hx hy

end BlockBand.Transmission.DualFeller
