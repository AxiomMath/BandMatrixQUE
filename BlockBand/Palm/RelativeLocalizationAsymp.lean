module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Relative localization: elementary asymptotics in `N`

Eventually-in-`N` statements (`N : ℕ`, `N → ∞`): powers grow (`ev_rpow_ge`), negative powers
vanish (`ev_rpow_neg_le`), `K (1 + log N) ≤ N^r` (`ev_log_le`), `N^β e^{-cN^ε} ≤ K`
(`ev_poly_exp_le`), and the floor bounds `N^p/2 ≤ ⌊N^p⌋ ≤ N^p` (`ev_floor_ge_half`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Filter Topology Real

theorem ev_rpow_ge {p : ℝ} (hp : 0 < p) (K : ℝ) : ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ p :=
  ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K

theorem ev_rpow_neg_le {p : ℝ} (hp : 0 < p) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-p) ≤ K :=
  (((tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop).eventually
    (Iio_mem_nhds hK)).mono fun _ h => le_of_lt h

theorem ev_natCast_ge (K : ℝ) : ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually_ge_atTop K

theorem ev_log_le {r : ℝ} (hr : 0 < r) (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K * (1 + Real.log N) ≤ (N : ℝ) ^ r := by
  set K' := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hlo := (isLittleO_log_rpow_atTop hr).def (c := 1 / (2 * K')) (by positivity)
  have hreal : ∀ᶠ x : ℝ in atTop, K' * (1 + Real.log x) ≤ x ^ r := by
    filter_upwards [hlo, (tendsto_rpow_atTop hr).eventually_ge_atTop (2 * K'),
      eventually_ge_atTop (1 : ℝ)] with x h1 h2 h3
    have hlog : 0 ≤ Real.log x := Real.log_nonneg h3
    have hxr : 0 ≤ x ^ r := Real.rpow_nonneg (by linarith) r
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hxr] at h1
    have : K' * Real.log x ≤ x ^ r / 2 := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ K')
      calc K' * Real.log x ≤ K' * (1 / (2 * K') * x ^ r) := this
        _ = x ^ r / 2 := by field_simp
    nlinarith
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hreal, ev_natCast_ge 1] with N hN h1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg h1
  calc K * (1 + Real.log N) ≤ K' * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    _ ≤ _ := hN

theorem ev_poly_exp_le (β : ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ β * Real.exp (-(c * (N : ℝ) ^ ε)) ≤ K := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (β / ε) c hc).comp
    (tendsto_rpow_atTop hε)
  have hreal : ∀ᶠ x : ℝ in atTop, x ^ β * Real.exp (-(c * x ^ ε)) ≤ K := by
    filter_upwards [h.eventually (Iio_mem_nhds hK), eventually_ge_atTop (0 : ℝ)] with x hx hx0
    simp only [Function.comp] at hx
    rw [← Real.rpow_mul hx0, mul_div_cancel₀ _ hε.ne', neg_mul] at hx
    exact hx.le
  exact tendsto_natCast_atTop_atTop.eventually hreal

theorem floor_ge_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  linarith

theorem ev_floor_ge_half {p : ℝ} (hp : 0 < p) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ p / 2 ≤ (⌊(N : ℝ) ^ p⌋₊ : ℝ) :=
  (ev_rpow_ge hp 2).mono fun _ h => floor_ge_half h

end BlockBand.Palm.RelativeLocalization
