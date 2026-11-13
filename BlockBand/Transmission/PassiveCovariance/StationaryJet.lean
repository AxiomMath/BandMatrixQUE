module

public import BlockBand.Transmission.PassiveCovariance.Scalars

/-!
# Existence of the stationary jet

The stationary jet equation has a solution (`stationaryJet_exists`). Proof: the first-derivative
update
`φ(s) = -a²(1+cs)/(1+k₋s)` maps the closed disk `|s| ≤ d_*` into itself and is a strict
contraction there:
* `|1+k₋s| ≥ m := 1 - |k₋|d_* > b` (since `|k₋| < (1-b)²`, `PassiveCovariance.norm_kMinus_lt`);
* `1+cs = (1+k₋s) - b²a²s`, so `|φ(s)| ≤ 1 + b²d_*/|1+k₋s| ≤ 1 + bd_* = d_*`;
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal

/-- The first-derivative update map `s ↦ -a²(1+cs)/(1+k₋s)`. -/
def jetMap (b E : ℝ) (s : ℂ) : ℂ :=
  -(matchedA E ^ 2) * (1 + ((1 - 2 * b : ℝ) : ℂ) * s) / (1 + kMinus b E * s)

section

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
include hb0 hb h1 h2

/-- The margin `m = 1 - |k₋|d_*` exceeds `b`. -/
theorem jet_margin_gt : b < 1 - ‖kMinus b E‖ * dStar b := by
  have hk := norm_kMinus_lt b E hb0 hb h1 h2
  have h1b : 0 < 1 - b := by linarith
  rw [dStar]
  have : ‖kMinus b E‖ * (1 / (1 - b)) < 1 - b := by
    rw [mul_one_div, div_lt_iff₀ h1b]; nlinarith
  linarith

omit hb0 hb h1 h2 in
theorem jet_denom_lower (s : ℂ) (hs : ‖s‖ ≤ dStar b) :
    1 - ‖kMinus b E‖ * dStar b ≤ ‖1 + kMinus b E * s‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (-(kMinus b E * s))
  rw [norm_one, norm_neg, sub_neg_eq_add, norm_mul] at h
  have : ‖kMinus b E‖ * ‖s‖ ≤ ‖kMinus b E‖ * dStar b :=
    mul_le_mul_of_nonneg_left hs (norm_nonneg _)
  linarith

theorem jet_denom_pos (s : ℂ) (hs : ‖s‖ ≤ dStar b) : b < ‖1 + kMinus b E * s‖ :=
  lt_of_lt_of_le (jet_margin_gt hb0 hb h1 h2) (jet_denom_lower (b := b) (E := E) s hs)

theorem jetMap_mapsTo (s : ℂ) (hs : ‖s‖ ≤ dStar b) : ‖jetMap b E s‖ ≤ dStar b := by
  have hD := jet_denom_pos hb0 hb h1 h2 s hs
  have hDpos : 0 < ‖1 + kMinus b E * s‖ := lt_trans hb0 hD
  have ha := norm_matchedA E h1 h2
  have h1b : 0 < 1 - b := by linarith
  have hsplit : 1 + ((1 - 2 * b : ℝ) : ℂ) * s =
      (1 + kMinus b E * s) - ((b : ℂ) ^ 2 * matchedA E ^ 2) * s := by
    rw [kMinus]; ring
  have hnum : ‖1 + ((1 - 2 * b : ℝ) : ℂ) * s‖ ≤ ‖1 + kMinus b E * s‖ + b ^ 2 * dStar b := by
    rw [hsplit]
    have hterm : ‖((b : ℂ) ^ 2 * matchedA E ^ 2) * s‖ ≤ b ^ 2 * dStar b := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, ha, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hb0, one_pow, mul_one]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    linarith [norm_sub_le (1 + kMinus b E * s) (((b : ℂ) ^ 2 * matchedA E ^ 2) * s)]
  rw [jetMap, norm_div, norm_mul, norm_neg, norm_pow, ha, one_pow, one_mul,
    div_le_iff₀ hDpos]
  refine hnum.trans ?_
  have hd : dStar b = 1 + b * dStar b := by rw [dStar]; field_simp; ring
  have : b ^ 2 * dStar b ≤ b * dStar b * ‖1 + kMinus b E * s‖ := by
    have hdpos : 0 < dStar b := by rw [dStar]; positivity
    have := mul_le_mul_of_nonneg_left hD.le (mul_nonneg hb0.le hdpos.le)
    nlinarith
  nlinarith

theorem jetMap_sub (s t : ℂ) (hs : ‖s‖ ≤ dStar b) (ht : ‖t‖ ≤ dStar b) :
    jetMap b E s - jetMap b E t =
      matchedA E ^ 4 * (b : ℂ) ^ 2 * (s - t) / ((1 + kMinus b E * s) * (1 + kMinus b E * t)) := by
  have hs0 : 1 + kMinus b E * s ≠ 0 := by
    intro h; have := jet_denom_pos hb0 hb h1 h2 s hs; rw [h, norm_zero] at this; linarith
  have ht0 : 1 + kMinus b E * t ≠ 0 := by
    intro h; have := jet_denom_pos hb0 hb h1 h2 t ht; rw [h, norm_zero] at this; linarith
  rw [jetMap, jetMap, div_sub_div _ _ hs0 ht0]
  congr 1
  rw [kMinus]; push_cast; ring

theorem jetMap_lipschitz (s t : ℂ) (hs : ‖s‖ ≤ dStar b) (ht : ‖t‖ ≤ dStar b) :
    ‖jetMap b E s - jetMap b E t‖ ≤
      b ^ 2 / (1 - ‖kMinus b E‖ * dStar b) ^ 2 * ‖s - t‖ := by
  have hm := jet_margin_gt hb0 hb h1 h2
  have hmpos : 0 < 1 - ‖kMinus b E‖ * dStar b := lt_trans hb0 hm
  have hls := jet_denom_lower (b := b) (E := E) s hs
  have hlt := jet_denom_lower (b := b) (E := E) t ht
  rw [jetMap_sub hb0 hb h1 h2 s t hs ht, norm_div, norm_mul, norm_mul, norm_mul, norm_pow,
    norm_pow, norm_matchedA E h1 h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0,
    one_pow, one_mul]
  have hprod : (1 - ‖kMinus b E‖ * dStar b) ^ 2 ≤
      ‖1 + kMinus b E * s‖ * ‖1 + kMinus b E * t‖ := by
    rw [pow_two]; exact mul_le_mul hls hlt hmpos.le (le_trans hmpos.le hls)
  have hppos : 0 < (1 - ‖kMinus b E‖ * dStar b) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (lt_of_lt_of_le hppos hprod) hppos]
  have := mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg b) (norm_nonneg (s - t)))
  nlinarith

/-- **Existence of the stationary jet.** -/
theorem stationaryJet_exists : ∃ s : ℂ, IsStationaryJet b E s := by
  set d := dStar b
  set m := 1 - ‖kMinus b E‖ * d
  have hm := jet_margin_gt hb0 hb h1 h2
  have hmpos : 0 < m := lt_trans hb0 hm
  have hd0 : 0 ≤ d := by simp only [d, dStar]; have : 0 < 1 - b := by linarith
                         positivity
  let D := Metric.closedBall (0 : ℂ) d
  have : CompleteSpace D := Metric.isClosed_closedBall.completeSpace_coe
  have : Nonempty D := ⟨⟨0, Metric.mem_closedBall_self hd0⟩⟩
  have hmem : ∀ x : D, ‖(x : ℂ)‖ ≤ d := fun x => by
    have := x.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
  let f : D → D := fun x => ⟨jetMap b E x, by
    rw [Metric.mem_closedBall, dist_zero_right]; exact jetMap_mapsTo hb0 hb h1 h2 x (hmem x)⟩
  have hK : b ^ 2 / m ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hc : ContractingWith (Real.toNNReal (b ^ 2 / m ^ 2)) f := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by positivity)]; simpa using hK
    · rw [Real.coe_toNNReal _ (by positivity), Subtype.dist_eq, Subtype.dist_eq,
        dist_eq_norm, dist_eq_norm]
      exact jetMap_lipschitz hb0 hb h1 h2 x y (hmem x) (hmem y)
  set s := ContractingWith.fixedPoint f hc
  have hfix : jetMap b E (s : ℂ) = s := congrArg Subtype.val (ContractingWith.fixedPoint_isFixedPt hc)
  refine ⟨s, ?_, hmem s⟩
  have hden : 1 + kMinus b E * s ≠ 0 := by
    intro h; have := jet_denom_pos hb0 hb h1 h2 s (hmem s); rw [h, norm_zero] at this; linarith
  rw [jetMap, div_eq_iff hden] at hfix
  linear_combination -hfix

end

end BlockBand.Transmission.PassiveCovariance
