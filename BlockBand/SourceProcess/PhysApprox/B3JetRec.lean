module

public import BlockBand.Transmission.PathScalar.StoppedRecursion

/-!
# The stopped scalar recursion with geometric memory of the start

The passive jet moments are reached after `C_p log W` layers, and fixed high moments pay for the
exits. This file uses the abstract setting of `PathScalar.StoppedRecursion` (good event `G_r`,
stopped scalar `1_{G_r}δ_r`). There `eLpNorm_stopped_le` bounds `‖1_{G_r}δ_r‖_p` by
`s₁ + (c + s_ξ)/(1-ρ)`, where `s₁ = ‖δ_1‖_p`; it does not forget the start. Here the start
only has to lie in the half-domain `δ_1 ≤ d/2` (on `G_r` it does), and the memory of it decays
geometrically:

* `eLpNorm_stopped_geom_le`: `‖1_{G_r}δ_r‖_p ≤ ρ^{r-1} d/2 + (c + s_ξ)/(1-ρ)`;
* `lintegral_delta_four_geom_le`: with the a.s. bound `δ_r ≤ M`,
  `E δ_r⁴ ≤ (ρ^{r-1} d/2 + (c + s_ξ)/(1-ρ))⁴ + M⁴ μ(G_rᶜ)`;
* `pow_le_inv_mul`: `ρ^n ≤ (n(1-ρ))⁻¹` for `0 < ρ < 1`, `n ≥ 1` (Bernoulli).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory
open BlockBand.Transmission.PathScalar
open scoped ENNReal

section Abstract

variable {Ω : Type*} {δ ξ : ℕ → Ω → ℝ} {d t ρ c : ℝ} {n : ℕ}

/-- The stopped scalar at the start lies in the half-domain. -/
theorem stopped_one_le (hd : 0 < d) (ω : Ω) :
    stopped δ ξ d t 1 ω ≤ d / 2 := by
  unfold stopped
  by_cases h : ω ∈ goodEvent δ ξ d t 1
  · rw [Set.indicator_of_mem h]; exact h.1
  · rw [Set.indicator_of_notMem h]; positivity

variable [MeasurableSpace Ω]

/-- **The stopped scalar forgets its start geometrically**:
`‖1_{G_r}δ_r‖_p ≤ ρ^{r-1} d/2 + (c + s_ξ)/(1-ρ)`. -/
theorem eLpNorm_stopped_geom_le (μ : Measure Ω) [IsProbabilityMeasure μ] {p sξ : ℝ} (hp : 1 ≤ p)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hd : 0 < d) (hc : 0 ≤ c) (hct : c + t ≤ (1 - ρ) * d)
    (hsξ : 0 ≤ sξ) (hδ0 : ∀ j ω, 0 ≤ δ j ω) (hξ0 : ∀ j ω, 0 ≤ ξ j ω)
    (hδm : ∀ j, Measurable (δ j)) (hξm : ∀ j, Measurable (ξ j))
    (hstep : ∀ᵐ ω ∂μ, ∀ j, 1 ≤ j → j < n → δ j ω ≤ d →
      δ (j + 1) ω ≤ ρ * δ j ω + c + ξ (j + 1) ω)
    (hξ : ∀ j, 2 ≤ j → j ≤ n → eLpNorm (ξ j) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal sξ) :
    ∀ r, 1 ≤ r → r ≤ n → eLpNorm (stopped δ ξ d t r) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (ρ ^ (r - 1) * (d / 2) + (c + sξ) / (1 - ρ)) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  set B := (c + sξ) / (1 - ρ) with hB
  have hB0 : 0 ≤ B := div_nonneg (by linarith) h1ρ.le
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hSm : ∀ r, Measurable (stopped δ ξ d t r) := fun r =>
    (hδm r).indicator (measurableSet_goodEvent δ ξ d t (hδm 1) hξm r)
  intro r hr
  induction r with
  | zero => omega
  | succ r ih =>
    intro hrn
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · have hb : ∀ᵐ ω ∂μ, ‖stopped δ ξ d t 1 ω‖ ≤ d / 2 := Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (stopped_nonneg δ ξ d t hδ0 1 ω)]
        exact stopped_one_le hd ω
      refine (eLpNorm_le_of_ae_bound (hSm 1).aestronglyMeasurable hb).trans ?_
      rw [measure_univ, ENNReal.one_rpow, one_mul]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [zero_add, Nat.sub_self, pow_zero, one_mul]
      linarith
    · have hIH := ih hr0 (by omega)
      have hmono : eLpNorm (stopped δ ξ d t (r + 1)) (ENNReal.ofReal p) μ ≤
          eLpNorm ((ρ • stopped δ ξ d t r + fun _ => c) + ξ (r + 1)) (ENNReal.ofReal p) μ := by
        refine eLpNorm_mono_ae_real (hSm _).aestronglyMeasurable (hstep.mono fun ω hω => ?_)
        rw [Real.norm_of_nonneg (stopped_nonneg δ ξ d t hδ0 _ ω)]
        simpa [smul_eq_mul] using stopped_succ_le hρ0 hd hc hct hδ0 hξ0 hω hr0 (by omega)
      refine hmono.trans ((eLpNorm_add_le hp1).trans ?_)
      refine (add_le_add (eLpNorm_add_le hp1) (hξ (r + 1) (by omega) hrn)).trans ?_
      rw [eLpNorm_const_smul, eLpNorm_const _ (by simpa using (by linarith : (0 : ℝ) < p))
        (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow, mul_one,
        Real.enorm_eq_ofReal hρ0, Real.enorm_eq_ofReal hc]
      have hA0 : 0 ≤ ρ ^ (r - 1) * (d / 2) + B := by positivity
      calc ENNReal.ofReal ρ * eLpNorm (stopped δ ξ d t r) (ENNReal.ofReal p) μ +
            ENNReal.ofReal c + ENNReal.ofReal sξ
          ≤ ENNReal.ofReal ρ * ENNReal.ofReal (ρ ^ (r - 1) * (d / 2) + B) + ENNReal.ofReal c +
              ENNReal.ofReal sξ := by gcongr
        _ = ENNReal.ofReal (ρ * (ρ ^ (r - 1) * (d / 2) + B) + c + sξ) := by
            rw [← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_add (by positivity) hc,
              ← ENNReal.ofReal_add (by positivity) hsξ]
        _ = ENNReal.ofReal (ρ ^ (r + 1 - 1) * (d / 2) + B) := by
            congr 1
            have hcs : c + sξ = (1 - ρ) * B := by rw [hB]; field_simp
            have hpw : ρ ^ (r + 1 - 1) = ρ * ρ ^ (r - 1) := by
              rw [show r + 1 - 1 = (r - 1) + 1 by omega, pow_succ, mul_comm]
            rw [hpw]
            linarith

/-- `∫ f⁴ ≤ a⁴` from `‖f‖₄ ≤ a`, for `f ≥ 0`. -/
theorem lintegral_ofReal_pow_four_le (μ : Measure Ω) {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hfm : Measurable f) {a : ℝ} (ha : 0 ≤ a)
    (h : eLpNorm f (ENNReal.ofReal 4) μ ≤ ENNReal.ofReal a) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ 4) ∂μ ≤ ENNReal.ofReal (a ^ 4) := by
  have h4 : ENNReal.ofReal 4 ≠ 0 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h4 ENNReal.ofReal_ne_top hfm.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)] at h
  have e : ∀ ω, ‖f ω‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (f ω ^ 4) := fun ω => by
    rw [Real.enorm_eq_ofReal (hf0 ω), ENNReal.rpow_ofNat, ENNReal.ofReal_pow (hf0 ω)]
  simp_rw [e] at h
  have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 4)
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num), ENNReal.rpow_one,
    ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow ha] at h'

/-- **The fourth moment of the recursion with geometric memory and exits**:
`E δ_r⁴ ≤ (ρ^{r-1} d/2 + (c + s_ξ)/(1-ρ))⁴ + M⁴ μ(G_rᶜ)`. -/
theorem lintegral_delta_four_geom_le (μ : Measure Ω) [IsProbabilityMeasure μ] {sξ M : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hd : 0 < d) (hc : 0 ≤ c) (hct : c + t ≤ (1 - ρ) * d)
    (hsξ : 0 ≤ sξ) (hδ0 : ∀ j ω, 0 ≤ δ j ω) (hξ0 : ∀ j ω, 0 ≤ ξ j ω)
    (hδm : ∀ j, Measurable (δ j)) (hξm : ∀ j, Measurable (ξ j))
    (hstep : ∀ᵐ ω ∂μ, ∀ j, 1 ≤ j → j < n → δ j ω ≤ d →
      δ (j + 1) ω ≤ ρ * δ j ω + c + ξ (j + 1) ω)
    (hξ : ∀ j, 2 ≤ j → j ≤ n → eLpNorm (ξ j) (ENNReal.ofReal 4) μ ≤ ENNReal.ofReal sξ)
    (hn : 1 ≤ n) (hM : ∀ᵐ ω ∂μ, δ n ω ≤ M) :
    ∫⁻ ω, ENNReal.ofReal (δ n ω ^ 4) ∂μ ≤
      ENNReal.ofReal ((ρ ^ (n - 1) * (d / 2) + (c + sξ) / (1 - ρ)) ^ 4) +
        ENNReal.ofReal (M ^ 4) * μ (goodEvent δ ξ d t n)ᶜ := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have hG := measurableSet_goodEvent δ ξ d t (hδm 1) hξm n
  have hSm : Measurable (stopped δ ξ d t n) :=
    (hδm n).indicator hG
  have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal (δ n ω ^ 4) ≤
      ENNReal.ofReal (stopped δ ξ d t n ω ^ 4) +
        (goodEvent δ ξ d t n)ᶜ.indicator (fun _ => ENNReal.ofReal (M ^ 4)) ω := by
    filter_upwards [hM] with ω hω
    by_cases h : ω ∈ goodEvent δ ξ d t n
    · rw [stopped, Set.indicator_of_mem h, Set.indicator_of_notMem (by simpa using h)]
      simp
    · rw [Set.indicator_of_mem (by simpa using h)]
      refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
      exact pow_le_pow_left₀ (hδ0 n ω) hω 4
  have hS := eLpNorm_stopped_geom_le μ (p := 4) (by norm_num) hρ0 hρ1 hd hc hct hsξ hδ0 hξ0 hδm
    hξm hstep hξ n hn le_rfl
  have hS4 := lintegral_ofReal_pow_four_le μ (stopped_nonneg δ ξ d t hδ0 n) hSm
    (by have := div_nonneg (by linarith : 0 ≤ c + sξ) h1ρ.le; positivity) hS
  calc ∫⁻ ω, ENNReal.ofReal (δ n ω ^ 4) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (stopped δ ξ d t n ω ^ 4) +
          (goodEvent δ ξ d t n)ᶜ.indicator (fun _ => ENNReal.ofReal (M ^ 4)) ω) ∂μ :=
        lintegral_mono_ae hpt
    _ = ∫⁻ ω, ENNReal.ofReal (stopped δ ξ d t n ω ^ 4) ∂μ +
          ENNReal.ofReal (M ^ 4) * μ (goodEvent δ ξ d t n)ᶜ := by
        rw [lintegral_add_left (hSm.pow_const 4).ennreal_ofReal,
          lintegral_indicator_const hG.compl]
    _ ≤ _ := by gcongr

end Abstract

/-- **Bernoulli**: `ρ^n ≤ (n(1-ρ))⁻¹` for `0 < ρ < 1` and `n ≥ 1`. -/
theorem pow_le_inv_mul {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {n : ℕ} (hn : 1 ≤ n) :
    ρ ^ n ≤ ((n : ℝ) * (1 - ρ))⁻¹ := by
  have ha : 0 ≤ ρ⁻¹ - 1 := by
    have : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ0 |>.2 hρ1.le
    linarith
  have hB := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ ρ⁻¹ - 1) n
  rw [add_sub_cancel] at hB
  have h1 : 1 - ρ ≤ ρ⁻¹ - 1 := by
    have e : ρ⁻¹ - 1 - (1 - ρ) = (1 - ρ) ^ 2 / ρ := by field_simp
    have : 0 ≤ (1 - ρ) ^ 2 / ρ := div_nonneg (sq_nonneg _) hρ0.le
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) * (1 - ρ) := mul_pos hn0 (by linarith)
  have hle : (n : ℝ) * (1 - ρ) ≤ ρ⁻¹ ^ n := by
    have : (n : ℝ) * (1 - ρ) ≤ (n : ℝ) * (ρ⁻¹ - 1) := mul_le_mul_of_nonneg_left h1 hn0.le
    nlinarith
  rw [inv_pow] at hle
  rw [le_inv_comm₀ (pow_pos hρ0 n) hpos]
  exact hle

end BlockBand.SourceProcess.PhysApprox.B3.Jet
