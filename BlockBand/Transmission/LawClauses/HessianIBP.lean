module

public import BlockBand.Transmission.LawClauses.HessianDeriv

/-!
# Integration by parts in `s` for the fractional Hessian

`∫_0^∞ s^{p-1} · s Re Tr[R_s H R_s] ds = p ∫_0^∞ s^{p-1} Re Tr[R_s H] ds`, with
`R_s = (A + s)⁻¹`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open MeasureTheory Set Real Matrix Filter Topology
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integrability on `(0,∞)` from a pointwise bound by an integrable function. -/
theorem integrableOn_Ioi_of_abs_le {f g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0))
    (hf : Measurable f) (h : ∀ s : ℝ, 0 < s → |f s| ≤ g s) : IntegrableOn f (Ioi 0) :=
  hg.mono' hf.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun s hs => by rw [Real.norm_eq_abs]; exact h s hs))

/-- **Integration by parts in `s`.** -/
theorem integral_ibp_resolvent {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {m : ℝ} (hm : 0 < m)
    (hXm : (X - (m : ℂ) • 1).PosSemidef) (H : Matrix ι ι ℂ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * (s * ((X + (s : ℂ) • 1)⁻¹ * H *
        (X + (s : ℂ) • 1)⁻¹).trace.re) =
      p * ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * ((X + (s : ℂ) • 1)⁻¹ * H).trace.re := by
  set n := (Fintype.card ι : ℝ)
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hH0 := norm_nonneg H
  set R : ℝ → Matrix ι ι ℂ := fun s => (X + (s : ℂ) • 1)⁻¹ with hRdef
  have hRm := measurable_resolvent X
  have hb := fun s (hs : 0 < s) => resolvent_norm_bounds hX hm hs.le hXm H
  set u : ℝ → ℝ := fun s => s ^ p
  set u' : ℝ → ℝ := fun s => p * s ^ (p - 1)
  set v : ℝ → ℝ := fun s => -(R s * H).trace.re
  set v' : ℝ → ℝ := fun s => (R s * R s * H).trace.re
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x := fun x hx =>
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hux : IsUnit (X + (x : ℂ) • (1 : Matrix ι ι ℂ)) :=
      (posDef_add_smul hm (le_of_lt hx) hXm).isUnit
    have h := ((trRe.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_inv_real_line X 1 x hux).mul_const H)).neg)
    convert h using 1
    · funext y; simp only [v, hRdef, Pi.neg_apply, Function.comp_apply, trRe_apply]
    · simp only [v', hRdef, trRe_apply, Matrix.mul_one, Matrix.neg_mul, trace_neg,
        Complex.neg_re, neg_neg]
  have hsp : ∀ s : ℝ, 0 < s → 0 < s ^ p := fun s hs => rpow_pos_of_pos hs p
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    refine integrableOn_Ioi_of_abs_le ((integrableOn_rpow_div_pow (q := p) (k := 2)
      (by linarith) (by push_cast; linarith) hm).const_mul (n * ‖H‖))
      ((measurable_id.pow_const _).mul (trRe.continuous.measurable.comp
        ((hRm.mul hRm).mul_const H))) fun s hs => ?_
    simp only [Pi.mul_apply, u, v', abs_mul, abs_of_pos (hsp s hs)]
    have := (abs_trace_re_le _).trans (mul_le_mul_of_nonneg_left (hb s hs).2.2.2 hn0)
    calc s ^ p * |(R s * R s * H).trace.re| ≤ s ^ p * (n * (‖H‖ / (m + s) ^ 2)) :=
          mul_le_mul_of_nonneg_left this (hsp s hs).le
      _ = _ := by ring
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    refine integrableOn_Ioi_of_abs_le ((integrableOn_rpow_div_pow (q := p - 1) (k := 1)
      (by linarith) (by push_cast; linarith) hm).const_mul (p * n * ‖H‖))
      ((measurable_const.mul (measurable_id.pow_const _)).mul
        (trRe.continuous.measurable.comp (hRm.mul_const H)).neg) fun s hs => ?_
    have hs0 : 0 < s := hs
    simp only [Pi.mul_apply, u', v, abs_mul, abs_neg, abs_of_pos hp0,
      abs_of_pos (rpow_pos_of_pos hs0 (p - 1))]
    have := (abs_trace_re_le _).trans (mul_le_mul_of_nonneg_left (hb s hs).1 hn0)
    calc p * s ^ (p - 1) * |(R s * H).trace.re| ≤ p * s ^ (p - 1) * (n * (‖H‖ / (m + s))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by simp only [pow_one]; ring
  -- boundary terms
  have hbd : ∀ s : ℝ, 0 < s → ‖(u * v) s‖ ≤ n * ‖H‖ * (s ^ p / (m + s)) := by
    intro s hs
    simp only [Pi.mul_apply, u, v, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (hsp s hs)]
    have := (abs_trace_re_le _).trans (mul_le_mul_of_nonneg_left (hb s hs).1 hn0)
    calc s ^ p * |(R s * H).trace.re| ≤ s ^ p * (n * (‖H‖ / (m + s))) :=
          mul_le_mul_of_nonneg_left this (hsp s hs).le
      _ = _ := by ring
  have h_zero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun s : ℝ => n * ‖H‖ / m * s ^ p) (𝓝[>] 0) (𝓝 0) := by
      have h := ((Real.continuousAt_rpow_const 0 p (Or.inr hp0.le)).tendsto).const_mul
        (n * ‖H‖ / m)
      rw [Real.zero_rpow hp0.ne', mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hc
    filter_upwards [self_mem_nhdsWithin] with s hs
    refine (hbd s hs).trans ?_
    have hs0 : 0 < s := hs
    have : s ^ p / (m + s) ≤ s ^ p / m :=
      div_le_div_of_nonneg_left (hsp s hs0).le hm (by linarith)
    calc n * ‖H‖ * (s ^ p / (m + s)) ≤ n * ‖H‖ * (s ^ p / m) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have h_infty : Tendsto (u * v) atTop (𝓝 0) := by
    have hc : Tendsto (fun s : ℝ => n * ‖H‖ * s ^ (p - 1)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - p)).const_mul (n * ‖H‖)
      rw [mul_zero, neg_sub] at h
      exact h
    refine squeeze_zero_norm' ?_ hc
    filter_upwards [eventually_gt_atTop 0] with s hs
    refine (hbd s hs).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [rpow_sub_one hs.ne', div_le_div_iff₀ (by linarith) hs]
    nlinarith [hsp s hs]
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  simp only [sub_zero, zero_sub] at hibp
  have hL : ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * (s * ((X + (s : ℂ) • 1)⁻¹ * H *
      (X + (s : ℂ) • 1)⁻¹).trace.re) = ∫ s in Ioi (0 : ℝ), u s * v' s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hs
    simp only [u, v', hRdef]
    rw [show ((X + (s : ℂ) • 1)⁻¹ * H * (X + (s : ℂ) • 1)⁻¹).trace =
        ((X + (s : ℂ) • 1)⁻¹ * (X + (s : ℂ) • 1)⁻¹ * H).trace by
      rw [trace_mul_comm, Matrix.mul_assoc]]
    rw [← mul_assoc, ← rpow_add_one hs0.ne']; ring_nf
  have hR : ∫ s in Ioi (0 : ℝ), u' s * v s =
      -(p * ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * ((X + (s : ℂ) • 1)⁻¹ * H).trace.re) := by
    rw [← integral_const_mul, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [u', v, hRdef]; ring
  rw [hL, hibp, hR, neg_neg]

end BlockBand.Transmission.LawClauses
