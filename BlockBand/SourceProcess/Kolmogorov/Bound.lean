module

public import BlockBand.SourceProcess.Kolmogorov.MeanValue
public import BlockBand.SourceProcess.Kolmogorov.HerglotzAbsIm

/-!
# Kolmogorov conjugate bound: the normalized bound on the unit circle

For `f` holomorphic on `ball 0 R`, `1 < R`, `f 0 = 0`, `0 < p < 1`:
`cos (p π / 2) · circleAverage ‖f‖ ^ p 0 1 ≤ 2 · (circleAverage |Im f| 0 1) ^ p`
(`cos_mul_circleAverage_norm_rpow_le_one`).

Route: for `1 < ρ < R` and `ε > 0`, with `H = herglotzAbsIm f ρ`, the functions
`K± = H + ε ± (-I f)` are holomorphic on `ball 0 ρ` with `re K± ≥ ε` (Poisson domination),
`K± 0 = avg_ρ |Im f| + ε` and `2 f = I (K₊ - K₋)`, so `‖f‖ ^ p ≤ ‖K₊‖ ^ p + ‖K₋‖ ^ p`; the mean
value bound (`cos_mul_circleAverage_le`) on the unit circle gives the bound with
`avg_ρ |Im f| + ε`; then `ε → 0` and `ρ → 1` (continuity of circle averages in the radius).
`integral_Ioc_eq_circleAverage` converts circle averages to `∫ θ in Ioc 0 (2π)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Kolmogorov

open Complex Real Metric Set Filter Topology

variable {f : ℂ → ℂ} {ρ : ℝ}

/-- `2 x ≤ a + b` implies `x ^ p ≤ a ^ p + b ^ p` for nonnegative reals and `p > 0`. -/
theorem rpow_le_add_of_norm_le {p : ℝ} (hp0 : 0 < p) {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h : 2 * x ≤ a + b) : x ^ p ≤ a ^ p + b ^ p := by
  rcases le_total a b with hab | hab
  · have : x ^ p ≤ b ^ p := Real.rpow_le_rpow hx (by linarith) hp0.le
    linarith [Real.rpow_nonneg ha p]
  · have : x ^ p ≤ a ^ p := Real.rpow_le_rpow hx (by linarith) hp0.le
    linarith [Real.rpow_nonneg hb p]

/-- `cos (p π / 2) > 0` for `0 < p < 1`. -/
theorem cos_pos_of_lt_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < Real.cos (p * π / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

/-- The fixed-radius, fixed-`ε` bound. -/
theorem cos_mul_circleAverage_norm_rpow_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hf0 : f 0 = 0) (hρ : 1 < ρ) (hρR : ρ < R)
    {ε : ℝ} (hε : 0 < ε) :
    Real.cos (p * π / 2) * circleAverage (fun z ↦ ‖f z‖ ^ p) 0 1 ≤
      2 * (circleAverage (fun ζ ↦ |(f ζ).im|) 0 ρ + ε) ^ p := by
  have hρ0 : 0 < ρ := by linarith
  have hfc : DiffContOnCl ℂ f (ball 0 ρ) := hf.diffContOnCl_ball (closedBall_subset_ball hρR)
  have hfd : DifferentiableOn ℂ f (ball 0 ρ) := hf.mono (ball_subset_ball hρR.le)
  set H := herglotzAbsIm f ρ with hH
  have hHd : DifferentiableOn ℂ H (ball 0 ρ) := differentiableOn_herglotzAbsIm hρ0 hfc
  set A := circleAverage (fun ζ ↦ |(f ζ).im|) 0 ρ with hA
  have hA0 : 0 ≤ A := circleAverage_nonneg_of_nonneg (fun _ _ ↦ abs_nonneg _)
  set Kp : ℂ → ℂ := fun z ↦ H z + ε + (-I * f z) with hKp
  set Km : ℂ → ℂ := fun z ↦ H z + ε - (-I * f z) with hKm
  have hre_mul (z : ℂ) : (-I * f z).re = (f z).im := by simp
  have hKpd : DifferentiableOn ℂ Kp (ball 0 ρ) :=
    ((hHd.add_const _).add ((differentiableOn_const _).mul hfd))
  have hKmd : DifferentiableOn ℂ Km (ball 0 ρ) :=
    ((hHd.add_const _).sub ((differentiableOn_const _).mul hfd))
  have hKpre : ∀ z ∈ ball (0 : ℂ) ρ, 0 < (Kp z).re := by
    intro z hz
    have := abs_im_le_re_herglotzAbsIm hρ0 hfc hz
    simp only [hKp, add_re, hre_mul, ofReal_re]
    linarith [neg_abs_le (f z).im]
  have hKmre : ∀ z ∈ ball (0 : ℂ) ρ, 0 < (Km z).re := by
    intro z hz
    have := abs_im_le_re_herglotzAbsIm hρ0 hfc hz
    simp only [hKm, add_re, sub_re, hre_mul, ofReal_re]
    linarith [le_abs_self (f z).im]
  have hH0 : H 0 = (A : ℂ) := herglotzAbsIm_zero hρ0 hfc
  have hKp0 : ‖Kp 0‖ = A + ε := by
    simp only [hKp, hH0, hf0, mul_zero, add_zero]
    rw [← ofReal_add, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hKm0 : ‖Km 0‖ = A + ε := by
    simp only [hKm, hH0, hf0, mul_zero, sub_zero]
    rw [← ofReal_add, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hp := cos_mul_circleAverage_le hp0 hp1.le hρ hKpd hKpre
  have hm := cos_mul_circleAverage_le hp0 hp1.le hρ hKmd hKmre
  rw [hKp0] at hp
  rw [hKm0] at hm
  -- continuity on the unit circle
  have hsub : sphere (0 : ℂ) |1| ⊆ ball 0 ρ := by
    intro z hz
    simp only [abs_one, mem_sphere_iff_norm, sub_zero] at hz
    simpa [hz] using hρ
  have hint {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 ρ)) :
      CircleIntegrable (fun z ↦ ‖g z‖ ^ p) 0 1 :=
    ContinuousOn.circleIntegrable'
      (((hg.continuousOn.mono hsub).norm).rpow_const (fun _ _ ↦ Or.inr hp0.le))
  have hmono : circleAverage (fun z ↦ ‖f z‖ ^ p) 0 1 ≤
      circleAverage (fun z ↦ ‖Kp z‖ ^ p) 0 1 + circleAverage (fun z ↦ ‖Km z‖ ^ p) 0 1 := by
    rw [← circleAverage_fun_add (hint hKpd) (hint hKmd)]
    apply circleAverage_mono (hint hfd) ((hint hKpd).add (hint hKmd))
    intro z _
    apply rpow_le_add_of_norm_le hp0 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    have h2 : (2 : ℂ) * f z = I * (Kp z - Km z) := by
      simp only [hKp, hKm]
      ring_nf
      rw [I_sq]
      ring
    have := congrArg (‖·‖) h2
    simp only [norm_mul, norm_I, one_mul] at this
    rw [show ‖(2 : ℂ)‖ = 2 by simp] at this
    rw [this]
    exact norm_sub_le _ _
  have hc := cos_pos_of_lt_one hp0 hp1
  calc Real.cos (p * π / 2) * circleAverage (fun z ↦ ‖f z‖ ^ p) 0 1
      ≤ Real.cos (p * π / 2) * (circleAverage (fun z ↦ ‖Kp z‖ ^ p) 0 1 +
          circleAverage (fun z ↦ ‖Km z‖ ^ p) 0 1) := by gcongr
    _ ≤ 2 * (A + ε) ^ p := by linarith

/-- The normalized Kolmogorov bound on the unit circle. -/
theorem cos_mul_circleAverage_norm_rpow_le_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {R : ℝ}
    (hR : 1 < R) (hf : DifferentiableOn ℂ f (ball 0 R)) (hf0 : f 0 = 0) :
    Real.cos (p * π / 2) * circleAverage (fun z ↦ ‖f z‖ ^ p) 0 1 ≤
      2 * (circleAverage (fun ζ ↦ |(f ζ).im|) 0 1) ^ p := by
  set A : ℝ → ℝ := fun r ↦ circleAverage (fun ζ ↦ |(f ζ).im|) 0 r with hA
  have hA0 (r : ℝ) : 0 ≤ A r := circleAverage_nonneg_of_nonneg (fun _ _ ↦ abs_nonneg _)
  -- first `ε → 0`
  have step1 : ∀ r, 1 < r → r < R →
      Real.cos (p * π / 2) * circleAverage (fun z ↦ ‖f z‖ ^ p) 0 1 ≤ 2 * (A r) ^ p := by
    intro r hr hrR
    have hcont : Continuous (fun ε : ℝ ↦ 2 * (A r + ε) ^ p) :=
      continuous_const.mul ((continuous_const.add continuous_id).rpow_const
        (fun _ ↦ Or.inr hp0.le))
    have ht : Tendsto (fun ε : ℝ ↦ 2 * (A r + ε) ^ p) (𝓝[>] 0) (𝓝 (2 * (A r) ^ p)) := by
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε ↦
      cos_mul_circleAverage_norm_rpow_le hp0 hp1 hf hf0 hr hrR hε)
  -- then `r → 1`
  have hcA : ContinuousOn A (Ioo 0 R) := by
    apply ContinuousOn.circleAverage _ (fun r hr ↦ hr.1.le)
    refine continuous_abs.comp_continuousOn (continuous_im.comp_continuousOn
      (hf.continuousOn.mono ?_))
    intro z hz
    simp only [sub_zero, mem_ofPred_eq, mem_Ioo] at hz
    simpa using hz.2
  have hcA1 : ContinuousAt A 1 := hcA.continuousAt (Ioo_mem_nhds one_pos hR)
  have ht : Tendsto (fun r ↦ 2 * (A r) ^ p) (𝓝[>] 1) (𝓝 (2 * (A 1) ^ p)) := by
    have : ContinuousAt (fun r ↦ 2 * (A r) ^ p) 1 :=
      continuousAt_const.mul (hcA1.rpow_const (Or.inr hp0.le))
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  exact step1 r hr.1 hr.2

/-- `∫ θ in Ioc 0 (2π), F (exp (θ I)) = 2π · circleAverage F 0 1`. -/
theorem integral_Ioc_eq_circleAverage (F : ℂ → ℝ) :
    ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), F (Complex.exp (θ * Complex.I)) =
      2 * π * circleAverage F 0 1 := by
  rw [circleAverage_def, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne', one_mul,
    intervalIntegral.integral_of_le two_pi_pos.le]
  simp [circleMap]

end BlockBand.SourceProcess.Kolmogorov
