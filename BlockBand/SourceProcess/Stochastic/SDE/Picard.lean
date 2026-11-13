module

public import BlockBand.SourceProcess.Stochastic.SDE.Gronwall
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Abstract Picard iteration with a Volterra-type contraction

The deterministic skeleton of strong existence and uniqueness for globally Lipschitz SDEs.
`α` is a complete metric space (in the application: classes of adapted continuous processes
with `dist(X,Y)² = E sup_{t≤T} |X_t - Y_t|²`), `Γ : α → α` the Picard map, and
`δ t x y` a time-indexed squared discrepancy (in the application `E sup_{s≤t} |X_s - Y_s|²`)
with `δ T = dist²`, `δ ≥ 0` and `δ` monotone in `t ∈ [0,T]`. The key hypothesis is
`δ t (Γ x) (Γ y) ≤ L ∫₀ᵗ δ s x y ds` on `[0,T]` (Lebesgue measure, `L ≥ 0`).

* `dist_iterate_succ_sq_le`: `dist(Γⁿ⁺¹x₀, Γⁿx₀)² ≤ dist(Γx₀, x₀)² (L T)ⁿ / n!`.
* `summable_sqrt_volterra_bound`: `∑ₙ √(C xⁿ/n!) < ∞` (`C, x ≥ 0`).
* `picard_fixedPoint`: `Γ` has a unique fixed point and every Picard sequence converges to it.
* `eq_of_isFixedPt_volterra`: uniqueness alone (no completeness needed).
-/

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.SDE
open MeasureTheory Filter Topology Set intervalIntegral
open scoped Nat NNReal

/-- `√(C xⁿ / n!)` is summable for `C, x ≥ 0` (AM-GM against `(2x)ⁿ/n!` and `2⁻ⁿ`). -/
theorem summable_sqrt_volterra_bound {C x : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) :
    Summable fun n : ℕ => Real.sqrt (C * x ^ n / n !) := by
  refine Summable.of_nonneg_of_le (fun n => Real.sqrt_nonneg _) (fun n => ?_)
    ((summable_volterra_bound C (2 * x)).add (summable_geometric_two))
  set a := C * x ^ n / n ! with ha
  have ha0 : 0 ≤ a := by positivity
  set b := Real.sqrt a
  have hb2 : b ^ 2 = a := Real.sq_sqrt ha0
  have hr : (0 : ℝ) < 2 ^ n := by positivity
  have hkey : b * 2 ^ n ≤ b ^ 2 * (2 ^ n) ^ 2 + 1 := by
    nlinarith [sq_nonneg (b * 2 ^ n - 1)]
  have h2 : C * (2 * x) ^ n / n ! = a * 2 ^ n := by rw [ha, mul_pow]; ring
  rw [h2, ← hb2, one_div, inv_pow]
  rw [← sub_nonneg]
  have : b ^ 2 * 2 ^ n + (2 ^ n)⁻¹ - b = (b ^ 2 * (2 ^ n) ^ 2 + 1 - b * 2 ^ n) / 2 ^ n := by
    field_simp
  rw [this]
  exact div_nonneg (by linarith) hr.le

/-- A function monotone on `[0,T]` is interval integrable on `[0,T]`. -/
theorem intervalIntegrable_of_monotoneOn {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (h : MonotoneOn f (Icc 0 T)) : IntervalIntegrable f volume 0 T :=
  MonotoneOn.intervalIntegrable (by rw [uIcc_of_le hT]; exact h)

variable {α : Type*} [MetricSpace α]

/-- The Picard map is Lipschitz with constant `√(L T)`. -/
theorem dist_map_le_of_volterra {Γ : α → α} {δ : ℝ → α → α → ℝ} {L T : ℝ} (hL : 0 ≤ L)
    (hT : 0 ≤ T) (hmono : ∀ x y, MonotoneOn (fun t => δ t x y) (Icc 0 T))
    (hδT : ∀ x y, δ T x y = dist x y ^ 2)
    (hΓ : ∀ x y, ∀ t ∈ Icc 0 T, δ t (Γ x) (Γ y) ≤ L * ∫ s in (0 : ℝ)..t, δ s x y) (x y : α) :
    dist (Γ x) (Γ y) ≤ Real.sqrt (L * T) * dist x y := by
  have hTm : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hint : ∫ s in (0 : ℝ)..T, δ s x y ≤ ∫ s in (0 : ℝ)..T, δ T x y :=
    integral_mono_on hT (intervalIntegrable_of_monotoneOn hT (hmono x y))
      intervalIntegrable_const fun s hs => hmono x y hs hTm hs.2
  have hsq : dist (Γ x) (Γ y) ^ 2 ≤ (L * T) * dist x y ^ 2 := by
    rw [← hδT, ← hδT]
    refine (hΓ x y T hTm).trans ?_
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hint hL
  rw [← Real.sqrt_sq dist_nonneg, ← Real.sqrt_sq (dist_nonneg (x := x) (y := y)),
    ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hsq

/-- Geometric-factorial decay of successive Picard increments. -/
theorem dist_iterate_succ_sq_le {Γ : α → α} {δ : ℝ → α → α → ℝ} {L T : ℝ} (hL : 0 ≤ L)
    (hT : 0 ≤ T) (hmono : ∀ x y, MonotoneOn (fun t => δ t x y) (Icc 0 T))
    (hδT : ∀ x y, δ T x y = dist x y ^ 2)
    (hΓ : ∀ x y, ∀ t ∈ Icc 0 T, δ t (Γ x) (Γ y) ≤ L * ∫ s in (0 : ℝ)..t, δ s x y)
    (x₀ : α) (n : ℕ) :
    dist (Γ^[n + 1] x₀) (Γ^[n] x₀) ^ 2 ≤ dist (Γ x₀) x₀ ^ 2 * (L * T) ^ n / n ! := by
  have hTm : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have key := volterra_iterate_le (v := fun n t => δ t (Γ^[n + 1] x₀) (Γ^[n] x₀))
    (C := dist (Γ x₀) x₀ ^ 2) hL
    (fun n => intervalIntegrable_of_monotoneOn hT (hmono _ _))
    (fun t ht => by
      simp only [Function.iterate_zero, id]
      rw [← hδT]; exact hmono _ _ ht hTm ht.2)
    (fun n t ht => by
      rw [Function.iterate_succ_apply' Γ (n + 1), Function.iterate_succ_apply' Γ n]
      exact hΓ _ _ t ht) n T hTm
  rwa [hδT] at key

/-- **Uniqueness of fixed points** under the Volterra contraction (no completeness). -/
theorem eq_of_isFixedPt_volterra {Γ : α → α} {δ : ℝ → α → α → ℝ} {L T : ℝ} (hL : 0 ≤ L)
    (hT : 0 ≤ T) (hδ0 : ∀ x y, ∀ t ∈ Icc 0 T, 0 ≤ δ t x y)
    (hmono : ∀ x y, MonotoneOn (fun t => δ t x y) (Icc 0 T))
    (hδT : ∀ x y, δ T x y = dist x y ^ 2)
    (hΓ : ∀ x y, ∀ t ∈ Icc 0 T, δ t (Γ x) (Γ y) ≤ L * ∫ s in (0 : ℝ)..t, δ s x y)
    {x y : α} (hx : Γ x = x) (hy : Γ y = y) : x = y := by
  have h0 := eq_zero_of_le_volterra (w := fun t => δ t x y) hL (hδ0 x y)
    (intervalIntegrable_of_monotoneOn hT (hmono x y))
    (fun t ht => by simpa only [hx, hy] using hΓ x y t ht) T ⟨hT, le_rfl⟩
  simp only [hδT, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    dist_eq_zero] at h0
  exact h0

/-- **Picard fixed point theorem under a Volterra-type contraction.** In a nonempty complete
metric space, `Γ` has a unique fixed point `x`, and `Γⁿ x₀ → x` for every starting point. -/
theorem picard_fixedPoint [CompleteSpace α] [Nonempty α] {Γ : α → α} {δ : ℝ → α → α → ℝ}
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (hδ0 : ∀ x y, ∀ t ∈ Icc 0 T, 0 ≤ δ t x y)
    (hmono : ∀ x y, MonotoneOn (fun t => δ t x y) (Icc 0 T))
    (hδT : ∀ x y, δ T x y = dist x y ^ 2)
    (hΓ : ∀ x y, ∀ t ∈ Icc 0 T, δ t (Γ x) (Γ y) ≤ L * ∫ s in (0 : ℝ)..t, δ s x y) :
    ∃ x, Γ x = x ∧ (∀ y, Γ y = y → y = x) ∧
      ∀ x₀, Tendsto (fun n => Γ^[n] x₀) atTop (𝓝 x) := by
  have hcont : Continuous Γ := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (Real.sqrt (L * T)))
      fun x y => ?_).continuous
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    exact dist_map_le_of_volterra hL hT hmono hδT hΓ x y
  -- every Picard sequence converges to a fixed point
  have hconv : ∀ x₀, ∃ x, Γ x = x ∧ Tendsto (fun n => Γ^[n] x₀) atTop (𝓝 x) := by
    intro x₀
    have hsum : Summable fun n => dist (Γ^[n] x₀) (Γ^[n.succ] x₀) := by
      refine Summable.of_nonneg_of_le (fun _ => dist_nonneg) (fun n => ?_)
        (summable_sqrt_volterra_bound (sq_nonneg (dist (Γ x₀) x₀)) (mul_nonneg hL hT))
      rw [dist_comm, ← Real.sqrt_sq dist_nonneg]
      exact Real.sqrt_le_sqrt (dist_iterate_succ_sq_le hL hT hmono hδT hΓ x₀ n)
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
    refine ⟨x, tendsto_nhds_unique ?_ ((tendsto_add_atTop_iff_nat 1).2 hx), hx⟩
    have := (hcont.tendsto x).comp hx
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, Function.iterate_succ_apply']
  obtain ⟨x, hx, -⟩ := hconv (Classical.arbitrary α)
  have huniq : ∀ y, Γ y = y → y = x := fun y hy =>
    eq_of_isFixedPt_volterra hL hT hδ0 hmono hδT hΓ hy hx
  refine ⟨x, hx, huniq, fun x₀ => ?_⟩
  obtain ⟨y, hy, hlim⟩ := hconv x₀
  rwa [huniq y hy] at hlim

end BlockBand.SourceProcess.Stochastic.SDE
