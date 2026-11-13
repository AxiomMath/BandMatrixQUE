module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Gronwall comparison for an integrated dissipation inequality

`ns_gronwall`: let `Y, X : ℝ → ℝ≥0∞` satisfy, on `[a, b]`, the integrated inequality
`Y(u₂) + κ ∫_{[u₁,u₂]} X ≤ Y(u₁)` (`a ≤ u₁ ≤ u₂ ≤ b`, lower Lebesgue integral, no measurability
assumed) and the comparison `Y ≤ X + c` with `c < ∞`. Then
`Y(b) ≤ e^{-κ(b-a)} Y(a) + c`.

Proof: `Y` is nonincreasing (the integral is `≥ 0`), so on `[u₁, u₂]`, `X ≥ Y - c ≥ Y(u₂) - c`
and `(Y(u₂) - c)₊ (1 + κ(u₂ - u₁)) ≤ (Y(u₁) - c)₊`; iterate on `N` equal steps and let
`(1 + κ(b-a)/N)^N → e^{κ(b-a)}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Real-valued one-step contraction iterated: if `z ≥ 0` satisfies
`z(u + h) (1 + κh) ≤ z(u)` along the grid `u_i = a + i h`, then
`z(a + N h) (1 + κh)^N ≤ z(a)`. -/
theorem ns_grid_contraction {z : ℝ → ℝ} {a h κ : ℝ} (hκh : 0 ≤ κ * h)
    (N : ℕ) (hstep : ∀ i : ℕ, i < N → z (a + (i + 1) * h) * (1 + κ * h) ≤ z (a + i * h)) :
    z (a + N * h) * (1 + κ * h) ^ N ≤ z a := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ih' := ih fun i hi => hstep i (Nat.lt_succ_of_lt hi)
    have h1 := hstep N (Nat.lt_succ_self N)
    push_cast
    calc z (a + (N + 1) * h) * (1 + κ * h) ^ (N + 1)
        = (z (a + (N + 1) * h) * (1 + κ * h)) * (1 + κ * h) ^ N := by ring
      _ ≤ z (a + N * h) * (1 + κ * h) ^ N := by
          gcongr
      _ ≤ z a := ih'

/-- **Gronwall comparison**. See the module docstring. -/
theorem ns_gronwall {Y X : ℝ → ℝ≥0∞} {a b κ : ℝ} {c : ℝ≥0∞} (hab : a ≤ b) (hκ : 0 ≤ κ)
    (hc : c ≠ ⊤)
    (hstep : ∀ u₁ u₂ : ℝ, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b →
      Y u₂ + ENNReal.ofReal κ * ∫⁻ u in Icc u₁ u₂, X u ≤ Y u₁)
    (hcomp : ∀ u ∈ Icc a b, Y u ≤ X u + c) :
    Y b ≤ ENNReal.ofReal (Real.exp (-(κ * (b - a)))) * Y a + c := by
  have hexp : 0 < Real.exp (-(κ * (b - a))) := Real.exp_pos _
  by_cases hYa : Y a = ⊤
  · rw [hYa, ENNReal.mul_top (ENNReal.ofReal_pos.2 hexp).ne', top_add]; exact le_top
  -- `Y` is nonincreasing on `[a, b]`
  have hmono : ∀ u₁ u₂ : ℝ, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b → Y u₂ ≤ Y u₁ := fun u₁ u₂ h1 h2 h3 =>
    le_trans le_self_add (hstep u₁ u₂ h1 h2 h3)
  have hfin : ∀ u ∈ Icc a b, Y u ≠ ⊤ := fun u hu =>
    ne_top_of_le_ne_top hYa (hmono a u le_rfl hu.1 hu.2)
  set c' := c.toReal with hc'
  set z : ℝ → ℝ := fun u => max ((Y u).toReal - c') 0 with hz
  have hz0 : ∀ u, 0 ≤ z u := fun u => le_max_right _ _
  -- one-step contraction of `z`
  have hone : ∀ u₁ u₂ : ℝ, a ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ b →
      z u₂ * (1 + κ * (u₂ - u₁)) ≤ z u₁ := by
    intro u₁ u₂ h1 h2 h3
    have hInt : (Y u₂ - c) * ENNReal.ofReal (u₂ - u₁) ≤ ∫⁻ u in Icc u₁ u₂, X u := by
      have hconst : ∫⁻ _ in Icc u₁ u₂, (Y u₂ - c) = (Y u₂ - c) * ENNReal.ofReal (u₂ - u₁) := by
        rw [setLIntegral_const, Real.volume_Icc]
      rw [← hconst]
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall ?_))
      intro u hu
      have hYu : Y u₂ ≤ Y u := hmono u u₂ (h1.trans hu.1) hu.2 h3
      exact (tsub_le_tsub_right hYu c).trans
        (tsub_le_iff_right.2 (hcomp u ⟨h1.trans hu.1, hu.2.trans h3⟩))
    have hY := hstep u₁ u₂ h1 h2 h3
    have hYle : Y u₂ + ENNReal.ofReal κ * ((Y u₂ - c) * ENNReal.ofReal (u₂ - u₁)) ≤ Y u₁ :=
      le_trans (by gcongr) hY
    have hf1 := hfin u₁ ⟨h1, h2.trans h3⟩
    have hf2 := hfin u₂ ⟨h1.trans h2, h3⟩
    rcases le_or_gt (Y u₂) c with hle | hlt
    · have : z u₂ = 0 := by
        simp only [hz]
        refine max_eq_right (sub_nonpos.2 ?_)
        exact ENNReal.toReal_mono hc hle
      rw [this, zero_mul]; exact hz0 _
    · have hD : (Y u₂ - c).toReal = (Y u₂).toReal - c' := ENNReal.toReal_sub_of_le hlt.le hf2
      have hR := ENNReal.toReal_mono hf1 hYle
      rw [ENNReal.toReal_add hf2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top (ne_top_of_le_ne_top hf2 tsub_le_self) ENNReal.ofReal_ne_top)),
        ENNReal.toReal_mul, ENNReal.toReal_mul, hD, ENNReal.toReal_ofReal hκ,
        ENNReal.toReal_ofReal (by linarith)] at hR
      have hpos : c' ≤ (Y u₂).toReal := by
        rw [hc']; exact ENNReal.toReal_mono hf2 hlt.le
      have hz2 : z u₂ = (Y u₂).toReal - c' := by simp only [hz]; exact max_eq_left (by linarith)
      have hz1 : (Y u₁).toReal - c' ≤ z u₁ := le_max_left _ _
      rw [hz2]
      nlinarith
  -- iterate on `N` equal steps and pass to the limit
  have hgrid : ∀ N : ℕ, 1 ≤ N → z b * (1 + κ * (b - a) / N) ^ N ≤ z a := by
    intro N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    set h := (b - a) / N with hh
    have hh0 : 0 ≤ h := div_nonneg (by linarith) hN0.le
    have hNh : a + N * h = b := by rw [hh]; field_simp; ring
    have := ns_grid_contraction (z := z) (a := a) (h := h) (κ := κ) (mul_nonneg hκ hh0) N
      (fun i hi => by
        have hi' : ((i : ℝ) + 1) ≤ N := by exact_mod_cast hi
        have h1 := hone (a + i * h) (a + (i + 1) * h) (by nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)])
          (by nlinarith) (by rw [← hNh]; nlinarith)
        have : a + (↑i + 1) * h - (a + ↑i * h) = h := by ring
        rwa [this] at h1)
    rw [hNh, ← mul_div_assoc] at this
    exact this
  have hlim : Tendsto (fun N : ℕ => z b * (1 + κ * (b - a) / N) ^ N) atTop
      (𝓝 (z b * Real.exp (κ * (b - a)))) :=
    (Real.tendsto_one_add_div_pow_exp (κ * (b - a))).const_mul _
  have hzb : z b * Real.exp (κ * (b - a)) ≤ z a :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨1, hgrid⟩)
  have hzb' : z b ≤ Real.exp (-(κ * (b - a))) * z a := by
    rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _)]; exact hzb
  have hc0 : 0 ≤ c' := ENNReal.toReal_nonneg
  have hya : z a ≤ (Y a).toReal := max_le (by linarith) ENNReal.toReal_nonneg
  have hyb : (Y b).toReal ≤ Real.exp (-(κ * (b - a))) * (Y a).toReal + c' := by
    have : (Y b).toReal - c' ≤ z b := le_max_left _ _
    have := mul_le_mul_of_nonneg_left hya hexp.le
    linarith
  calc Y b = ENNReal.ofReal (Y b).toReal := (ENNReal.ofReal_toReal (hfin b ⟨hab, le_rfl⟩)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(κ * (b - a))) * (Y a).toReal + c') := ENNReal.ofReal_le_ofReal hyb
    _ = ENNReal.ofReal (Real.exp (-(κ * (b - a)))) * Y a + c := by
        rw [ENNReal.ofReal_add (by positivity) hc0, ENNReal.ofReal_mul hexp.le,
          ENNReal.ofReal_toReal hYa, hc', ENNReal.ofReal_toReal hc]

end BlockBand.Endpoints
