module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The mean-conductance comparison `y' ≤ -(D/2)y²` in integral form

`ode_compare`: if `y(b) - y(a) = -(D/2)∫_a^b q` on `[s,t]`, `0 ≤ y`, `y² ≤ q ≤ C`, then
`y(t) ≤ 2/(D(t-s))` (discretize: `1/y_{j+1} - 1/y_j ≥ c - c²C/y(t)`, `c = Dh/2`; let `h → 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology

/-- One step: `z - x ≥ cx²`, `z - x ≤ cC`, `0 < Y ≤ x ≤ z` give `1/x ≥ 1/z + c - c²C/Y`. -/
theorem inv_step {x z c C Y : ℝ} (hY : 0 < Y) (hYx : Y ≤ x) (hxz : x ≤ z) (hc : 0 ≤ c)
    (h1 : c * x ^ 2 ≤ z - x) (h2 : z - x ≤ c * C) : 1 / z + (c - c ^ 2 * C / Y) ≤ 1 / x := by
  have hx : 0 < x := lt_of_lt_of_le hY hYx
  have hz : 0 < z := lt_of_lt_of_le hx hxz
  have key : c * x / z ≥ c - c ^ 2 * C / Y := by
    have e1 : c * x / z = c - c * (z - x) / z := by field_simp; ring
    rw [e1]
    have : c * (z - x) / z ≤ c ^ 2 * C / Y := by
      rw [div_le_div_iff₀ hz hY]
      have hcz : c * (z - x) ≤ c * (c * C) := mul_le_mul_of_nonneg_left h2 hc
      have hCc : 0 ≤ c * (c * C) := le_trans (mul_nonneg hc (by nlinarith)) hcz
      calc c * (z - x) * Y ≤ c * (c * C) * Y := mul_le_mul_of_nonneg_right hcz hY.le
        _ ≤ c * (c * C) * z := mul_le_mul_of_nonneg_left (hYx.trans hxz) hCc
        _ = c ^ 2 * C * z := by ring
    linarith
  have e2 : 1 / x - 1 / z = (z - x) / (x * z) := by field_simp
  have : c * x / z ≤ 1 / x - 1 / z := by
    rw [e2, div_le_div_iff₀ hz (mul_pos hx hz)]
    nlinarith [mul_le_mul_of_nonneg_right h1 hz.le]
  linarith

theorem ode_compare {y q : ℝ → ℝ} {D C s t : ℝ} (hD : 0 < D) (hst : s < t)
    (hy0 : ∀ u ∈ Set.Icc s t, 0 ≤ y u)
    (hid : ∀ a b, s ≤ a → a ≤ b → b ≤ t → y b - y a = -(D / 2) * ∫ u in a..b, q u)
    (hint : ∀ a b, s ≤ a → a ≤ b → b ≤ t → IntervalIntegrable q volume a b)
    (hq : ∀ u ∈ Set.Icc s t, y u ^ 2 ≤ q u) (hqC : ∀ u ∈ Set.Icc s t, q u ≤ C) :
    y t ≤ 2 / (D * (t - s)) := by
  have hts : 0 < t - s := by linarith
  have hanti : ∀ a b, s ≤ a → a ≤ b → b ≤ t → y b ≤ y a := by
    intro a b ha hab hb
    have h := hid a b ha hab hb
    have : 0 ≤ ∫ u in a..b, q u := intervalIntegral.integral_nonneg hab fun u hu =>
      le_trans (sq_nonneg _) (hq u ⟨ha.trans hu.1, hu.2.trans hb⟩)
    nlinarith
  rcases le_or_gt (y t) 0 with hY | hY
  · exact hY.trans (by positivity)
  set Y := y t
  -- for every `N ≥ 1`: `1/Y ≥ A - B/N`
  set A := D / 2 * (t - s)
  set B := (D / 2) ^ 2 * (t - s) ^ 2 * C / Y
  have hNb : ∀ N : ℕ, 0 < N → A - B / N ≤ 1 / Y := by
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    set h := (t - s) / N
    have hh : 0 < h := by positivity
    set c := D / 2 * h
    have hc : 0 ≤ c := by positivity
    set u : ℕ → ℝ := fun j => s + j * h
    have hu_mem : ∀ j, j ≤ N → u j ∈ Set.Icc s t := by
      intro j hj
      have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
      refine ⟨by simp only [u]; exact le_add_of_nonneg_right (by positivity), ?_⟩
      simp only [u, h]
      have : (j : ℝ) * ((t - s) / N) ≤ t - s := by
        rw [mul_div_assoc', div_le_iff₀ hNr]; nlinarith
      linarith
    have huN : u N = t := by simp only [u, h]; field_simp; ring
    have hstep : ∀ j, j < N → 1 / y (u j) + (c - c ^ 2 * C / Y) ≤ 1 / y (u (j + 1)) := by
      intro j hj
      have hj1 := hu_mem j hj.le
      have hj2 := hu_mem (j + 1) hj
      have hle : u j ≤ u (j + 1) := by simp only [u]; push_cast; nlinarith
      have hlen : u (j + 1) - u j = h := by simp only [u]; push_cast; ring
      have hid' := hid _ _ hj1.1 hle hj2.2
      have hi := hint _ _ hj1.1 hle hj2.2
      have hYx : Y ≤ y (u (j + 1)) := hanti _ _ hj2.1 hj2.2 le_rfl
      have hxz : y (u (j + 1)) ≤ y (u j) := hanti _ _ hj1.1 hle hj2.2
      have hlow : (u (j + 1) - u j) * y (u (j + 1)) ^ 2 ≤ ∫ v in u j..u (j + 1), q v := by
        have := intervalIntegral.integral_mono_on hle intervalIntegrable_const hi
          (f := fun _ => y (u (j + 1)) ^ 2) fun v hv => by
            have hv' : v ∈ Set.Icc s t := ⟨hj1.1.trans hv.1, hv.2.trans hj2.2⟩
            have hy1 : 0 ≤ y (u (j + 1)) := hy0 _ hj2
            have hmono : y (u (j + 1)) ≤ y v := hanti _ _ hv'.1 hv.2 hj2.2
            exact (pow_le_pow_left₀ hy1 hmono 2).trans (hq v hv')
        simpa [intervalIntegral.integral_const, smul_eq_mul] using this
      have hup : ∫ v in u j..u (j + 1), q v ≤ (u (j + 1) - u j) * C := by
        have := intervalIntegral.integral_mono_on hle hi intervalIntegrable_const
          (g := fun _ => C) fun v hv => hqC v ⟨hj1.1.trans hv.1, hv.2.trans hj2.2⟩
        simpa [intervalIntegral.integral_const, smul_eq_mul] using this
      rw [hlen] at hlow hup
      refine inv_step hY hYx hxz hc ?_ ?_
      · simp only [c]; nlinarith
      · simp only [c]; nlinarith
    have hind : ∀ j, j ≤ N → 1 / y s + j * (c - c ^ 2 * C / Y) ≤ 1 / y (u j) := by
      intro j hj
      induction j with
      | zero => simp [u]
      | succ j ih =>
        have := hstep j (by omega)
        have := ih (by omega)
        push_cast; linarith
    have hfin := hind N le_rfl
    rw [huN] at hfin
    have hys : 0 ≤ 1 / y s := by
      have := hy0 s ⟨le_rfl, hst.le⟩; positivity
    have : (N : ℝ) * (c - c ^ 2 * C / Y) = A - B / N := by
      simp only [c, h, A, B]; field_simp
    linarith
  have hlim : Tendsto (fun N : ℕ => A - B / N) atTop (𝓝 A) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat B)
  have hA : A ≤ 1 / Y := le_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun N hN1 => hNb N hN1⟩)
  have hApos : 0 < A := by positivity
  rw [le_div_iff₀ hY] at hA
  rw [le_div_iff₀ (by positivity)]
  simp only [A] at hA
  nlinarith

end BlockBand.Transmission.Generator
