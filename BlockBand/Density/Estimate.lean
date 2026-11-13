module

public import BlockBand.Density.Stieltjes
public import BlockBand.Density.Unsmoothing
public import BlockBand.Density.SemicircleSmoothing
public import BlockBand.Density.UnitIntensity

/-!
# The critical density estimate from a uniform diagonal-resolvent mean bound

The single probabilistic input of the critical density theorem is the uniform bound on diagonal
resolvent means at `η_W = W^{-7/4}` (`MeanResolventBound`, proved as `meanResolventBound_holds`);
this file proves everything else.

* `criticalDensityEstimate_of_meanResolventBound`: `MeanResolventBound` and the PSSS hypothesis
  imply `Internal.Contracts.Inputs.CriticalDensityEstimate` (clause 1 is
  `criticalDensity_smooth`; clause 2 combines averaging (`abs_poissonSmoothTest_sub_le`),
  semicircle smoothing (`abs_im_semicircleM_div_pi_sub_le`) and unsmoothing
  (`meanDensity_unsmoothing`, split scale `h = W^{-13/8}`), all `O(W^{-1/8})` or
  `O(W^{-1/32})`; small `W < W₀` use `0 ≤ ρ_{n,W} ≤ K_b`, `0 ≤ ρ ≤ 1/π`);
* `criticalDensity_of_meanResolventBound`: the full `Internal.Contracts.Inputs.CriticalDensity`
  (with `criticalUnitIntensity_of_estimate`).
Constants depend only on `b, κ, T` and the PSSS constant.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory Set Filter BlockBand.Counting BlockBand.External
open scoped ENNReal NNReal Topology

/-- The spectral scale `η_W = W^{-7/4}` of the proof. -/
def resolventScale (W : ℕ) : ℝ := (W : ℝ) ^ (-(7 : ℝ) / 4)

/-- **The probabilistic input of the critical density theorem**: for fixed `b, κ, T` there are
`C, W₀` such that for every admissible `p` with bond `b`, `4⌈W^{15/16}⌉ ≤ n ≤ TW`, `W ≥ W₀`, every
realization of the physical law, every bulk `|e| ≤ 2-κ` and every site `x`,
`|E G_xx(e + iη_W) - m_sc(e + iη_W)| ≤ C W^{-1/32}` (`G = (H - z)⁻¹`, `m_sc` the semicircle
Stieltjes transform). Proved as `meanResolventBound_holds`. -/
def MeanResolventBound : Prop :=
  ∀ (b κ T : ℝ), 0 < b → b < 1 / 2 → 0 < κ → 0 < T → ∃ C W₀ : ℝ, 0 ≤ C ∧
    ∀ p : Parameters, p.b = b →
      4 * ⌈(p.W : ℝ) ^ ((15 : ℝ) / 16)⌉₊ ≤ p.n → (p.n : ℝ) ≤ T * (p.W : ℝ) → W₀ ≤ (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (e : ℝ), |e| ≤ 2 - κ → ∀ x : p.Site,
        ‖(∫ H, (H - ((e : ℂ) + (resolventScale p.W : ℂ) * Complex.I) • (1 : p.SiteMatrix))⁻¹ x x
            ∂(model.law : Measure p.SiteMatrix)) -
          ErdosRiabov.semicircleM ((e : ℂ) + (resolventScale p.W : ℂ) * Complex.I)‖ ≤
          C * (p.W : ℝ) ^ (-(1 : ℝ) / 32)

theorem semicircleDensity_nonneg (e : ℝ) : 0 ≤ Parameters.semicircleDensity e := by
  unfold Parameters.semicircleDensity; positivity

theorem semicircleDensity_le (e : ℝ) : Parameters.semicircleDensity e ≤ 1 / Real.pi := by
  unfold Parameters.semicircleDensity
  have h : Real.sqrt (4 - e ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg e])
  rw [div_le_div_iff₀ (by positivity [Real.pi_pos]) Real.pi_pos]
  nlinarith [Real.pi_pos]

/-- Real-power bookkeeping for `W ≥ 1`. -/
theorem rpow_le_rpow_neg_one_div_32 {w a : ℝ} (hw : 1 ≤ w) (ha : a ≤ -(1 : ℝ) / 32) :
    w ^ a ≤ w ^ (-(1 : ℝ) / 32) :=
  Real.rpow_le_rpow_of_exponent_le hw ha

theorem rpow_ratio_eq {w : ℝ} (hw0 : 0 < w) :
    w ^ (-(7 : ℝ) / 4) / w ^ (-(13 : ℝ) / 8) = w ^ (-(1 : ℝ) / 8) := by
  rw [div_eq_iff (Real.rpow_pos_of_pos hw0 _).ne', ← Real.rpow_add hw0]
  norm_num

theorem sqrt_scale_bound {w N T c : ℝ} (hw0 : 0 < w) (hc : 0 < c) (hN : 0 < N)
    (hNW : N * w ≤ T * w ^ 3) :
    1 / Real.sqrt (c / (N * w)) * w ^ (-(13 : ℝ) / 8) ≤ Real.sqrt (T / c) * w ^ (-(1 : ℝ) / 8) := by
  have hT : 0 ≤ T := by
    have : 0 < T * w ^ 3 := lt_of_lt_of_le (by positivity) hNW
    by_contra hneg
    push Not at hneg
    nlinarith [pow_pos hw0 3]
  have hh : 0 < w ^ (-(13 : ℝ) / 8) := Real.rpow_pos_of_pos hw0 _
  have hl : 1 / Real.sqrt (c / (N * w)) * w ^ (-(13 : ℝ) / 8) =
      Real.sqrt (N * w / c * (w ^ (-(13 : ℝ) / 8)) ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hh.le, Real.sqrt_div' _ (by positivity),
      Real.sqrt_div (by positivity)]
    field_simp
  have hr : Real.sqrt (T / c) * w ^ (-(1 : ℝ) / 8) =
      Real.sqrt (T / c * (w ^ (-(1 : ℝ) / 8)) ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.rpow_pos_of_pos hw0 _).le]
  rw [hl, hr]
  apply Real.sqrt_le_sqrt
  have hh2 : (w ^ (-(13 : ℝ) / 8)) ^ 2 = w ^ (-(13 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le]; norm_num
  have hw8 : (w ^ (-(1 : ℝ) / 8)) ^ 2 = w ^ (-(1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le]; norm_num
  have e3 : w ^ 3 = w ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hw3 : w ^ 3 * w ^ (-(13 : ℝ) / 4) = w ^ (-(1 : ℝ) / 4) := by
    rw [e3, ← Real.rpow_add hw0]; norm_num
  rw [hh2, hw8, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc, ← hw3]
  have : 0 < w ^ (-(13 : ℝ) / 4) := Real.rpow_pos_of_pos hw0 _
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The critical density estimate** from `MeanResolventBound`. Uses `PSSS.SourceContract`. See
`criticalDensity_holds` for the unconditional constructor. -/
theorem criticalDensityEstimate_of_meanResolventBound (source : PSSS.SourceContract.{0})
    (hML : MeanResolventBound) : Internal.Contracts.Inputs.CriticalDensityEstimate := by
  refine ⟨criticalDensity_smooth, ?_⟩
  intro b κ T hb hb' hκ hT
  obtain ⟨C₁, W₀, hC₁, hML'⟩ := hML b κ T hb hb' hκ hT
  have hK : 0 < densityBound source b := densityBound_pos source hb'
  have hc : 0 < 1 - 2 * b := by linarith
  have hκ' : 0 < min κ 1 := lt_min hκ one_pos
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hs₀ : 0 < Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2 := by
    have : 0 < 4 - (2 - min κ 1) ^ 2 := by nlinarith
    positivity
  have hW₁ : 1 ≤ max W₀ 1 := le_max_right _ _
  refine ⟨max ((densityBound source b + 1 / Real.pi) * (max W₀ 1) ^ ((1 : ℝ) / 32))
    (2 * densityBound source b * Real.sqrt (T / (1 - 2 * b)) + 4 * densityBound source b / Real.pi +
      C₁ / Real.pi + 1 / (Real.pi * (Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2))),
    le_max_of_le_left (by positivity), ?_⟩
  intro n W hn hW hceil hnT p model ρ hρc hρeq e he
  have hρ : ρ = meanDensity p model := eq_meanDensity_of_withDensity p model hρc hρeq
  subst hρ
  have hw1 : (1 : ℝ) ≤ W := by
    have : 1 ≤ W := hW
    exact_mod_cast this
  have hw0 : (0 : ℝ) < W := by linarith
  have hρ0 := (meanDensity_pos p model e).le
  have hρK : meanDensity p model e ≤ densityBound source b := meanDensity_le source p model e
  have hsc0 := semicircleDensity_nonneg e
  have hsc1 := semicircleDensity_le e
  have hpos32 : 0 < (W : ℝ) ^ (-(1 : ℝ) / 32) := Real.rpow_pos_of_pos hw0 _
  by_cases hsmall : (W : ℝ) < max W₀ 1
  · -- small `W`: crude bound
    have hcrude : |meanDensity p model e - Parameters.semicircleDensity e| ≤
        densityBound source b + 1 / Real.pi := by
      rw [abs_le]; constructor <;> linarith
    have hscale : 1 ≤ (max W₀ 1) ^ ((1 : ℝ) / 32) * (W : ℝ) ^ (-(1 : ℝ) / 32) := by
      rw [show (-(1 : ℝ) / 32) = -((1 : ℝ) / 32) by ring, Real.rpow_neg hw0.le,
        ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hw0 _), one_mul]
      exact Real.rpow_le_rpow hw0.le hsmall.le (by norm_num)
    have h0 : 0 ≤ densityBound source b + 1 / Real.pi := by positivity
    refine hcrude.trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos32.le)
    nlinarith
  · -- large `W`
    push Not at hsmall
    have hW₀ : W₀ ≤ (W : ℝ) := (le_max_left _ _).trans hsmall
    have hη : 0 < resolventScale W := Real.rpow_pos_of_pos hw0 _
    have hh : 0 < (W : ℝ) ^ (-(13 : ℝ) / 8) := Real.rpow_pos_of_pos hw0 _
    have he2 : |e| < 2 := by linarith
    have h1 := abs_poissonSmoothTest_sub_le p model e hη
      (ErdosRiabov.semicircleM ((e : ℂ) + (resolventScale W : ℂ) * Complex.I))
      (hML' p rfl hceil hnT hW₀ model e he)
    have h2 := abs_im_semicircleM_div_pi_sub_le he2 hη
    have h3 := meanDensity_unsmoothing source p model hη hh e
    have hs : Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2 ≤ Real.sqrt (4 - e ^ 2) / 2 := by
      have : e ^ 2 ≤ (2 - min κ 1) ^ 2 := by
        have h' : |e| ≤ 2 - min κ 1 := by linarith [min_le_left κ 1]
        have := sq_abs e
        nlinarith [abs_nonneg e]
      have := Real.sqrt_le_sqrt (show 4 - (2 - min κ 1) ^ 2 ≤ 4 - e ^ 2 by linarith)
      linarith
    have hηle : resolventScale W ≤ (W : ℝ) ^ (-(1 : ℝ) / 32) :=
      rpow_le_rpow_neg_one_div_32 hw1 (by norm_num)
    have hratio : resolventScale W / (W : ℝ) ^ (-(13 : ℝ) / 8) = (W : ℝ) ^ (-(1 : ℝ) / 8) :=
      rpow_ratio_eq hw0
    have h18 : (W : ℝ) ^ (-(1 : ℝ) / 8) ≤ (W : ℝ) ^ (-(1 : ℝ) / 32) :=
      rpow_le_rpow_neg_one_div_32 hw1 (by norm_num)
    have hNW : (p.N : ℝ) * W ≤ T * (W : ℝ) ^ 3 := by
      have hN : (p.N : ℝ) = (n : ℝ) * W := by
        change ((n * W : ℕ) : ℝ) = _
        push_cast; ring
      rw [hN]
      have := mul_le_mul_of_nonneg_right hnT (by positivity : (0 : ℝ) ≤ (W : ℝ) * W)
      nlinarith
    have hsqrt : 1 / Real.sqrt (p.scalarTraceVariance : ℝ) * (W : ℝ) ^ (-(13 : ℝ) / 8) ≤
        Real.sqrt (T / (1 - 2 * b)) * (W : ℝ) ^ (-(1 : ℝ) / 8) :=
      sqrt_scale_bound hw0 hc (by exact_mod_cast p.N_pos) hNW
    have hA : |meanDensity p model e - poissonSmoothTest (resolventScale W) (meanDensity p model) e| ≤
        (2 * densityBound source b * Real.sqrt (T / (1 - 2 * b)) + 4 * densityBound source b / Real.pi) *
          (W : ℝ) ^ (-(1 : ℝ) / 32) := by
      refine h3.trans ?_
      have e1 : 2 * densityBound source p.b / Real.sqrt (p.scalarTraceVariance : ℝ) *
          (W : ℝ) ^ (-(13 : ℝ) / 8) = 2 * densityBound source b *
            (1 / Real.sqrt (p.scalarTraceVariance : ℝ) * (W : ℝ) ^ (-(13 : ℝ) / 8)) := by
        change 2 * densityBound source b / _ * _ = _
        ring
      have e2 : 2 * densityBound source p.b * (2 * resolventScale W /
          (Real.pi * (W : ℝ) ^ (-(13 : ℝ) / 8))) = 4 * densityBound source b / Real.pi *
            (resolventScale W / (W : ℝ) ^ (-(13 : ℝ) / 8)) := by
        change 2 * densityBound source b * _ = _
        field_simp
        norm_num
      rw [e1, e2, hratio]
      have h4 : 0 ≤ 4 * densityBound source b / Real.pi := by positivity
      have := mul_le_mul_of_nonneg_left hsqrt (by positivity : (0 : ℝ) ≤ 2 * densityBound source b)
      nlinarith [mul_le_mul_of_nonneg_left h18 h4,
        mul_le_mul_of_nonneg_left h18
          (by positivity : (0 : ℝ) ≤ 2 * densityBound source b * Real.sqrt (T / (1 - 2 * b)))]
    have hB : |poissonSmoothTest (resolventScale W) (meanDensity p model) e -
        (ErdosRiabov.semicircleM ((e : ℂ) + (resolventScale W : ℂ) * Complex.I)).im / Real.pi| ≤
        C₁ / Real.pi * (W : ℝ) ^ (-(1 : ℝ) / 32) := by
      refine h1.trans (le_of_eq ?_); ring
    have hC : |(ErdosRiabov.semicircleM ((e : ℂ) + (resolventScale W : ℂ) * Complex.I)).im /
        Real.pi - Parameters.semicircleDensity e| ≤
        1 / (Real.pi * (Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2)) * (W : ℝ) ^ (-(1 : ℝ) / 32) := by
      refine h2.trans ?_
      have hse : 0 < Real.sqrt (4 - e ^ 2) / 2 := by
        have h' := sq_lt_sq' (abs_lt.mp he2).1 (abs_lt.mp he2).2
        have : 0 < 4 - e ^ 2 := by linarith
        positivity
      have hsq : 0 < Real.sqrt (4 - (2 - min κ 1) ^ 2) := by linarith
      rw [div_le_iff₀ (mul_pos Real.pi_pos hse)]
      have hden : Real.pi * (Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2) ≤
          Real.pi * (Real.sqrt (4 - e ^ 2) / 2) := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
      have hq : 1 / (Real.pi * (Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2)) *
          (W : ℝ) ^ (-(1 : ℝ) / 32) * (Real.pi * (Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2)) =
          (W : ℝ) ^ (-(1 : ℝ) / 32) := by
        field_simp
      calc resolventScale W ≤ (W : ℝ) ^ (-(1 : ℝ) / 32) := hηle
        _ = 1 / (Real.pi * (Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2)) *
          (W : ℝ) ^ (-(1 : ℝ) / 32) * (Real.pi * (Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2)) := hq.symm
        _ ≤ 1 / (Real.pi * (Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2)) *
          (W : ℝ) ^ (-(1 : ℝ) / 32) * (Real.pi * (Real.sqrt (4 - e ^ 2) / 2)) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
    have htri := abs_sub_le (meanDensity p model e)
      (poissonSmoothTest (resolventScale W) (meanDensity p model) e) (Parameters.semicircleDensity e)
    have htri2 := abs_sub_le (poissonSmoothTest (resolventScale W) (meanDensity p model) e)
      ((ErdosRiabov.semicircleM ((e : ℂ) + (resolventScale W : ℂ) * Complex.I)).im / Real.pi)
      (Parameters.semicircleDensity e)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos32.le)
    have : (2 * densityBound source b * Real.sqrt (T / (1 - 2 * b)) +
        4 * densityBound source b / Real.pi + C₁ / Real.pi +
        1 / (Real.pi * (Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2))) * (W : ℝ) ^ (-(1 : ℝ) / 32) =
        (2 * densityBound source b * Real.sqrt (T / (1 - 2 * b)) +
          4 * densityBound source b / Real.pi) * (W : ℝ) ^ (-(1 : ℝ) / 32) +
        C₁ / Real.pi * (W : ℝ) ^ (-(1 : ℝ) / 32) +
        1 / (Real.pi * (Real.sqrt (4 - (2 - min κ 1) ^ 2) / 2)) * (W : ℝ) ^ (-(1 : ℝ) / 32) := by
      ring
    linarith

/-- **The critical density theorem** (both the estimate and the unit-intensity consequence) from
the single probabilistic input `MeanResolventBound`. Uses `PSSS.SourceContract`. The constructor
from the inputs is `criticalDensity_holds`. -/
theorem criticalDensity_of_meanResolventBound (source : PSSS.SourceContract.{0})
    (hML : MeanResolventBound) : Internal.Contracts.Inputs.CriticalDensity :=
  ⟨criticalDensityEstimate_of_meanResolventBound source hML,
    criticalUnitIntensity_of_estimate source
      (criticalDensityEstimate_of_meanResolventBound source hML)⟩

end BlockBand.Density
