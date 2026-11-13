module

public import BlockBand.Transmission.LawClauses.HessianIBP

/-!
# `TransmissionLawContract.fractionalHessian`: the Hessian of `Tr A^p`

For `Φ(A) = Tr A^p`, `0 < p < 1`, the second derivative along `H` is the integral formula
`d²/dτ² Φ(A + τH)|_{τ=0} = -(p sin πp/π) ∫_0^∞ s^{p-1} Re Tr[(A+s)⁻¹H(A+s)⁻¹H] ds`, obtained by
differentiating twice under the integral sign.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open MeasureTheory Set Real Matrix Filter Topology
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Second derivative under the integral sign**, at `τ = 0`. -/
theorem hasDerivAt_trace_resolvent_line {A H : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hH : H.IsHermitian) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {m δ : ℝ} (hm : 0 < m)
    (hδ : 0 < δ) (hcoer : ∀ τ : ℝ, |τ| < δ → (A + (τ : ℂ) • H - (m : ℂ) • 1).PosSemidef) :
    HasDerivAt (fun τ : ℝ => ∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
        ((A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H).trace.re)
      (∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
        (-((A + (s : ℂ) • 1)⁻¹ * H * (A + (s : ℂ) • 1)⁻¹ * H).trace.re)) 0 := by
  set n := (Fintype.card ι : ℝ)
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hH0 := norm_nonneg H
  have hball : ∀ τ ∈ Metric.ball (0 : ℝ) δ, |τ| < δ := fun τ hτ => by
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hτ
  set F : ℝ → ℝ → ℝ := fun τ s => s ^ (p - 1) *
    ((A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H).trace.re with hF
  set F' : ℝ → ℝ → ℝ := fun τ s => s ^ (p - 1) *
    (-((A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H * (A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H).trace.re)
    with hF'
  have hmeasF : ∀ τ : ℝ, Measurable (F τ) := fun τ =>
    (measurable_id.pow_const _).mul (trRe.continuous.measurable.comp
      ((measurable_resolvent _).mul_const H))
  have hmeasF' : Measurable (F' 0) := by
    have hR := measurable_resolvent (A + ((0 : ℝ) : ℂ) • H)
    exact (measurable_id.pow_const _).mul (trRe.continuous.measurable.comp
      ((((hR.mul_const H).mul hR).mul_const H))).neg
  have hX0 := hcoer 0 (by simpa using hδ)
  have hint0 : Integrable (F 0) (volume.restrict (Ioi 0)) := by
    refine integrableOn_Ioi_of_abs_le ((integrableOn_rpow_div_pow (q := p - 1) (k := 1)
      (by linarith) (by push_cast; linarith) hm).const_mul (n * ‖H‖)) (hmeasF 0) fun s hs => ?_
    have hb := (resolvent_norm_bounds (isHermitian_add_real_smul hA 0 hH) hm hs.le hX0 H).1
    have htr := (abs_trace_re_le _).trans (mul_le_mul_of_nonneg_left hb hn0)
    simp only [hF, abs_mul, abs_of_pos (rpow_pos_of_pos hs (p - 1))]
    calc s ^ (p - 1) * |((A + ((0 : ℝ) : ℂ) • H + (s : ℂ) • 1)⁻¹ * H).trace.re| ≤
        s ^ (p - 1) * (n * (‖H‖ / (m + s))) :=
          mul_le_mul_of_nonneg_left htr (rpow_pos_of_pos hs _).le
      _ = _ := by simp only [pow_one]; ring
  have hInt := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := 0)
    (bound := fun s => n * ‖H‖ ^ 2 * (s ^ (p - 1) / (m + s) ^ 2)) (Metric.ball_mem_nhds 0 hδ)
    (Eventually.of_forall fun τ => (hmeasF τ).aestronglyMeasurable) hint0
    hmeasF'.aestronglyMeasurable ?bound
    ((integrableOn_rpow_div_pow (q := p - 1) (k := 2) (by linarith) (by push_cast; linarith)
      hm).const_mul _) ?diff
  case bound =>
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs τ hτ => ?_)
    have hs0 : 0 < s := hs
    have hb := (resolvent_norm_bounds (isHermitian_add_real_smul hA τ hH) hm hs0.le
      (hcoer τ (hball τ hτ)) H).2.2.1
    have htr := (abs_trace_re_le _).trans (mul_le_mul_of_nonneg_left hb hn0)
    simp only [hF', Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (rpow_pos_of_pos hs0 (p - 1))]
    calc s ^ (p - 1) * |((A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H *
          (A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H).trace.re| ≤
        s ^ (p - 1) * (n * (‖H‖ ^ 2 / (m + s) ^ 2)) :=
          mul_le_mul_of_nonneg_left htr (rpow_pos_of_pos hs0 _).le
      _ = _ := by ring
  case diff =>
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs τ hτ => ?_)
    have hs0 : 0 < s := hs
    have hu : IsUnit (A + (s : ℂ) • 1 + (τ : ℂ) • H) := by
      have := (posDef_add_smul hm hs0.le (hcoer τ (hball τ hτ))).isUnit
      rwa [add_right_comm] at this
    have hinv := hasDerivAt_inv_real_line (A + (s : ℂ) • 1) H τ hu
    have hd := (trRe.hasFDerivAt.comp_hasDerivAt τ (hinv.mul_const H)).const_mul (s ^ (p - 1))
    have hfun : (fun τ' : ℝ => F τ' s) = fun τ' : ℝ => s ^ (p - 1) *
        (trRe ∘ fun τ : ℝ => (A + (s : ℂ) • 1 + (τ : ℂ) • H)⁻¹ * H) τ' := by
      funext τ'; simp only [hF, Function.comp_apply, trRe_apply, add_right_comm]
    rw [hfun]
    convert hd using 1
    simp only [hF', trRe_apply, add_right_comm, Matrix.neg_mul, trace_neg, Complex.neg_re]
  have h2 := hInt.2
  have e0 : ∀ s : ℝ, F' 0 s = s ^ (p - 1) *
      (-((A + (s : ℂ) • 1)⁻¹ * H * (A + (s : ℂ) • 1)⁻¹ * H).trace.re) := fun s => by
    simp only [hF', Complex.ofReal_zero, zero_smul, add_zero]
  simp only [e0] at h2
  exact h2

/-- **`TransmissionLawContract.fractionalHessian`**, with exactly the field type. -/
theorem fractionalHessian : ∀ p : ℝ, 0 < p → p < 1 → ∀ (n : ℕ) (A H : Matrix (Fin n) (Fin n) ℂ),
    A.PosDef → H.IsHermitian →
      deriv (deriv (fun τ : ℝ => fracTrace p (A + (τ : ℂ) • H))) 0 =
        -(p * Real.sin (Real.pi * p) / Real.pi) *
          ∫ s in Set.Ioi (0 : ℝ), s ^ (p - 1) *
            ((A + (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ * H *
              (A + (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ * H).trace.re := by
  intro p hp0 hp1 n A H hA hH
  obtain ⟨m, δ, hm, hδ, hcoer⟩ := exists_coercive_line hA hH
  set c := Real.sin (π * p) / π
  set g : ℝ → ℝ := fun τ => ∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
    ((A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H).trace.re
  -- the first derivative on the window
  have hd1 : ∀ τ : ℝ, |τ| < δ →
      deriv (fun τ : ℝ => fracTrace p (A + (τ : ℂ) • H)) τ = c * p * g τ := by
    intro τ hτ
    rw [(hasDerivAt_fracTrace_line hA.1 hH hp0 hp1 hm hcoer hτ).deriv,
      integral_ibp_resolvent (isHermitian_add_real_smul hA.1 τ hH) hm (hcoer τ hτ) H hp0 hp1]
    ring
  have hev : deriv (fun τ : ℝ => fracTrace p (A + (τ : ℂ) • H)) =ᶠ[𝓝 0]
      fun τ => c * p * g τ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with τ hτ
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hτ
    exact hd1 τ hτ
  have hg := (hasDerivAt_trace_resolvent_line hA.1 hH hp0 hp1 hm hδ hcoer).const_mul (c * p)
  rw [hev.deriv_eq, hg.deriv]
  have hneg : ∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
      (-((A + (s : ℂ) • 1)⁻¹ * H * (A + (s : ℂ) • 1)⁻¹ * H).trace.re) =
      -∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
        ((A + (s : ℂ) • 1)⁻¹ * H * (A + (s : ℂ) • 1)⁻¹ * H).trace.re := by
    rw [← integral_neg]; simp only [mul_neg]
  rw [hneg]
  simp only [c]
  ring

end BlockBand.Transmission.LawClauses
