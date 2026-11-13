module

public import BlockBand.Transmission.LawClauses.HessianSpectral

/-!
# Scalar integrals for the fractional concavity gap

* `rpow_eq_integral'`: `λ^p = c_p ∫ s^{p-1} λ/(λ+s) ds` for `λ ≥ 0` (the standard integral
  identity, with `λ = 0` allowed);
* `integral_lin`: `∫ s^p t/(t+s)² ds = t^p J_p`, `J_p = ∫ u^p/(1+u)² du ≥ 0`, `t ≥ 0`;
* `gap_lower`: `∫ s^p t t'/((t+s)²(t'+s)) ds ≥ t^p t'^p/27` for `0 ≤ t ≤ t' ≤ 1` (restrict to
  `s ∈ [t, 2t]`), the scalar input of the concavity gap.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Set Real
open BlockBand.Transmission.LawClauses

/-- `c_p = sin(πp)/π`. -/
def cP (p : ℝ) : ℝ := Real.sin (π * p) / π

theorem cP_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < cP p := by
  have hsin : 0 < Real.sin (π * p) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  exact div_pos hsin Real.pi_pos

/-- `λ^p = c_p ∫ s^{p-1} λ/(λ+s)` for `λ ≥ 0`. -/
theorem rpow_eq_integral' {p l : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hl : 0 ≤ l) :
    l ^ p = cP p * ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * (l / (l + s)) := by
  rcases hl.lt_or_eq with hl | hl
  · exact rpow_eq_integral hp0 hp1 hl
  · subst hl
    simp [zero_rpow hp0.ne']

theorem integrableOn_rpow_mul_div_add' {p l : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hl : 0 ≤ l) :
    IntegrableOn (fun s : ℝ => s ^ (p - 1) * (l / (l + s))) (Ioi 0) := by
  rcases hl.lt_or_eq with hl | hl
  · exact integrableOn_rpow_mul_div_add hp0 hp1 hl
  · subst hl
    simp

/-- `J_p = ∫_0^∞ u^p/(1+u)² du`. -/
def jP (p : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), u ^ p / (1 + u) ^ 2

theorem jP_nonneg (p : ℝ) : 0 ≤ jP p :=
  setIntegral_nonneg measurableSet_Ioi fun u hu => by
    have : (0 : ℝ) < u := hu
    positivity

theorem integrableOn_lin {p t : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => s ^ p * (t / (t + s) ^ 2)) (Ioi 0) := by
  rcases ht.lt_or_eq with ht | ht
  · have h := (integrableOn_rpow_div_pow (q := p) (k := 2) (m := t) (by linarith)
      (by push_cast; linarith) ht).const_mul t
    refine IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
    ring
  · subst ht
    simp

/-- **`∫ s^p t/(t+s)² = t^p J_p`**, `t ≥ 0`. -/
theorem integral_lin {p t : ℝ} (hp0 : 0 < p) (ht : 0 ≤ t) :
    ∫ s in Ioi (0 : ℝ), s ^ p * (t / (t + s) ^ 2) = t ^ p * jP p := by
  rcases ht.lt_or_eq with ht | ht
  · have h := integral_comp_mul_left_Ioi (fun s => s ^ p * (t / (t + s) ^ 2)) 0 ht
    rw [mul_zero] at h
    have hc : ∫ x in Ioi (0 : ℝ), (t * x) ^ p * (t / (t + t * x) ^ 2) =
        t ^ (p - 1) * jP p := by
      rw [jP, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : 0 < x := hx
      rw [mul_rpow ht.le hx0.le]
      have : t + t * x = t * (1 + x) := by ring
      rw [this]
      have h1 : (0 : ℝ) < 1 + x := by linarith
      have e : t ^ p = t ^ (p - 1) * t := by
        rw [← rpow_add_one ht.ne']; ring_nf
      rw [e]
      field_simp
    rw [hc, smul_eq_mul] at h
    have e : t ^ p = t * t ^ (p - 1) := by
      rw [← rpow_one_add' ht.le (by linarith)]; ring_nf
    rw [e, mul_assoc, h, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  · subst ht
    simp [zero_rpow hp0.ne']

/-- The gap integrand `s^p t t'/((t+s)²(t'+s))`. -/
def gapIntegrand (p t t' s : ℝ) : ℝ := s ^ p * (t * t' / ((t + s) ^ 2 * (t' + s)))

theorem gapIntegrand_nonneg {p t t' s : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (hs : 0 < s) :
    0 ≤ gapIntegrand p t t' s := by
  unfold gapIntegrand
  have : 0 < t + s := by linarith
  have : 0 < t' + s := by linarith
  positivity

theorem integrableOn_gap {p t t' : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    IntegrableOn (gapIntegrand p t t') (Ioi 0) := by
  have hb := integrableOn_lin hp0 hp1 ht
  have hcont : ContinuousOn (gapIntegrand p t t') (Ioi 0) := by
    unfold gapIntegrand
    refine ContinuousOn.mul (fun s hs => (continuousAt_rpow_const _ _
      (Or.inl (ne_of_gt hs))).continuousWithinAt) (ContinuousOn.div continuousOn_const
        (by fun_prop) fun s hs => ?_)
    have : (0 : ℝ) < s := hs
    have : 0 < t + s := by linarith
    have : 0 < t' + s := by linarith
    positivity
  refine hb.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  have hs0 : (0 : ℝ) < s := hs
  rw [Real.norm_of_nonneg (gapIntegrand_nonneg ht ht' hs0)]
  unfold gapIntegrand
  have h1 : 0 < t + s := by linarith
  have h2 : 0 < t' + s := by linarith
  have hr : t' / (t' + s) ≤ 1 := (div_le_one h2).mpr (by linarith)
  have e : t * t' / ((t + s) ^ 2 * (t' + s)) = t / (t + s) ^ 2 * (t' / (t' + s)) := by
    field_simp
  rw [e]
  have : 0 ≤ s ^ p * (t / (t + s) ^ 2) := by positivity
  calc s ^ p * (t / (t + s) ^ 2 * (t' / (t' + s))) = s ^ p * (t / (t + s) ^ 2) * (t' / (t' + s)) := by
        ring
    _ ≤ s ^ p * (t / (t + s) ^ 2) * 1 := mul_le_mul_of_nonneg_left hr this
    _ = _ := mul_one _

/-- **The scalar gap**: `∫ s^p t t'/((t+s)²(t'+s)) ≥ t^p t'^p/27` for `0 ≤ t ≤ t' ≤ 1`. -/
theorem gap_lower {p t t' : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ht : 0 ≤ t) (htt : t ≤ t')
    (ht1 : t' ≤ 1) :
    t ^ p * t' ^ p / 27 ≤ ∫ s in Ioi (0 : ℝ), gapIntegrand p t t' s := by
  have ht' : 0 ≤ t' := ht.trans htt
  rcases ht.lt_or_eq with ht | ht
  swap
  · subst ht
    rw [zero_rpow hp0.ne', zero_mul, zero_div]
    exact setIntegral_nonneg measurableSet_Ioi fun s hs => gapIntegrand_nonneg le_rfl ht' hs
  have ht'0 : 0 < t' := ht.trans_le htt
  have hsub : Icc t (2 * t) ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le ht hs.1
  have hmono : ∫ s in Icc t (2 * t), gapIntegrand p t t' s ≤
      ∫ s in Ioi (0 : ℝ), gapIntegrand p t t' s :=
    setIntegral_mono_set (integrableOn_gap hp0 hp1 ht.le ht')
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs =>
        gapIntegrand_nonneg ht.le ht' hs)) (Filter.Eventually.of_forall hsub)
  refine le_trans ?_ hmono
  have hconst : ∀ s ∈ Icc t (2 * t), t ^ p / (27 * t) ≤ gapIntegrand p t t' s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ht hs.1
    have hsp : t ^ p ≤ s ^ p := rpow_le_rpow ht.le hs.1 hp0.le
    have h1 : (t + s) ^ 2 ≤ 9 * t ^ 2 := by nlinarith [hs.1, hs.2]
    have h2 : t' + s ≤ 3 * t' := by linarith [hs.2]
    have hden : 0 < (t + s) ^ 2 * (t' + s) := by positivity
    have hq : t * t' / (9 * t ^ 2 * (3 * t')) ≤ t * t' / ((t + s) ^ 2 * (t' + s)) :=
      div_le_div_of_nonneg_left (by positivity) hden
        (mul_le_mul h1 h2 (by linarith) (by positivity))
    have e : t * t' / (9 * t ^ 2 * (3 * t')) = 1 / (27 * t) := by field_simp; ring
    rw [e] at hq
    unfold gapIntegrand
    calc t ^ p / (27 * t) = t ^ p * (1 / (27 * t)) := by ring
      _ ≤ s ^ p * (t * t' / ((t + s) ^ 2 * (t' + s))) :=
          mul_le_mul hsp hq (by positivity) (by positivity)
  have hI : ∫ s in Icc t (2 * t), t ^ p / (27 * t) ≤ ∫ s in Icc t (2 * t), gapIntegrand p t t' s :=
    setIntegral_mono_on (by simp)
      ((integrableOn_gap hp0 hp1 ht.le ht').mono_set hsub) measurableSet_Icc hconst
  refine le_trans ?_ hI
  rw [setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul]
  have htp : t' ^ p ≤ 1 := rpow_le_one ht'0.le ht1 hp0.le
  have : t ^ p * t' ^ p / 27 ≤ t ^ p / 27 := by
    have : 0 ≤ t ^ p := by positivity
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    exact mul_le_of_le_one_right this htp
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

end BlockBand.Transmission.FractionalBulk
