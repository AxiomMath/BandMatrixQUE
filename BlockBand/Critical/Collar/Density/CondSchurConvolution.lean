module

public import BlockBand.Critical.WeightedDensity.Poisson
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Conditional Schur identity: Convolution

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

The Gaussian–Cauchy convolution `cauchyConv σ η θ = ∫ φ_σ(t) P_η(θ - t) dt`: uniform bound
`≤ K_σ P_1(θ)` for `0 < η ≤ 1`, and pointwise convergence to `φ_σ(θ)` as `η ↓ 0`. Pure real analysis.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory Filter Topology ProbabilityTheory
open BlockBand.Critical.WeightedDensity (cauchyKernel cauchyKernel_nonneg continuous_cauchyKernel
  measurable_cauchyKernel)
open scoped ENNReal NNReal

/-- The Gaussian–Cauchy convolution `(P_η ∗ φ_σ)(θ) = ∫ φ_σ(t) P_η(θ - t) dt` (extended reals). -/
def cauchyConv (σ : ℝ≥0) (η θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (gaussianPDFReal 0 σ t * cauchyKernel η (θ - t))

theorem cauchyKernel_eq_cauchyPDFReal {η : ℝ} (hη : 0 < η) (θ t : ℝ) :
    cauchyKernel η (θ - t) = cauchyPDFReal θ (Real.toNNReal η) t := by
  rw [cauchyPDFReal_def, Real.coe_toNNReal _ hη.le]
  unfold cauchyKernel
  have : 0 < (θ - t) ^ 2 + η ^ 2 := by positivity
  rw [show (t - θ) ^ 2 = (θ - t) ^ 2 by ring]
  field_simp

theorem lintegral_ofReal_cauchyKernel_shift {η : ℝ} (hη : 0 < η) (θ : ℝ) :
    ∫⁻ t, ENNReal.ofReal (cauchyKernel η (θ - t)) = 1 := by
  have h := lintegral_cauchyPDF_eq_one θ (γ := Real.toNNReal η) (Real.toNNReal_pos.2 hη).ne'
  rw [← h]
  refine lintegral_congr fun t => ?_
  rw [cauchyKernel_eq_cauchyPDFReal hη]
  rfl

theorem measurable_cauchyConv (σ : ℝ≥0) (η : ℝ) : Measurable (cauchyConv σ η) := by
  unfold cauchyConv
  have h : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal 0 σ p.2 *
      cauchyKernel η (p.1 - p.2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_gaussianPDFReal 0 σ).comp measurable_snd).mul
      ((measurable_cauchyKernel η).comp (measurable_fst.sub measurable_snd)))
  exact h.lintegral_prod_right'

theorem gaussianPDFReal_le_const (σ : ℝ≥0) (t : ℝ) :
    gaussianPDFReal 0 σ t ≤ (Real.sqrt (2 * Real.pi * σ))⁻¹ := by
  rw [gaussianPDFReal_def]
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 ?_) (by positivity)).trans_eq
    (mul_one _)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

theorem continuous_gaussianPDFReal' (σ : ℝ≥0) : Continuous (gaussianPDFReal 0 σ) := by
  rw [gaussianPDFReal_def]
  fun_prop

/-- Weighted Gaussian bound: `φ_σ(t)(1 + t²) ≤ c M₀ e^{-a t²}`, `a = 1/(4σ)`, `M₀ = max 1 (4σ)`. -/
theorem gaussianPDFReal_mul_le {σ : ℝ≥0} (hσ : σ ≠ 0) (t : ℝ) :
    gaussianPDFReal 0 σ t * (1 + t ^ 2) ≤ (Real.sqrt (2 * Real.pi * σ))⁻¹ * max 1 (4 * (σ : ℝ)) *
      Real.exp (-(1 / (4 * σ)) * t ^ 2) := by
  have hs : (0 : ℝ) < σ := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg σ) with h | h
    · exact absurd (NNReal.coe_eq_zero.1 h.symm) hσ
    · exact h
  set a : ℝ := 1 / (4 * σ) with ha
  have ha0 : 0 < a := by positivity
  rw [gaussianPDFReal_def]
  simp only [sub_zero]
  have hexp : Real.exp (-t ^ 2 / (2 * σ)) = Real.exp (-a * t ^ 2) * Real.exp (-a * t ^ 2) := by
    rw [← Real.exp_add]; congr 1; rw [ha]; field_simp; ring
  have hM : (1 + t ^ 2) * Real.exp (-a * t ^ 2) ≤ max 1 (4 * (σ : ℝ)) := by
    have h1 : 1 + a * t ^ 2 ≤ Real.exp (a * t ^ 2) := by
      have := Real.add_one_le_exp (a * t ^ 2); linarith
    have h2 : Real.exp (-a * t ^ 2) = (Real.exp (a * t ^ 2))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    have hpos : 0 < Real.exp (a * t ^ 2) := Real.exp_pos _
    rw [h2, ← div_eq_mul_inv, div_le_iff₀ hpos]
    have hm1 : 1 ≤ max 1 (4 * (σ : ℝ)) := le_max_left _ _
    have hm2 : 4 * (σ : ℝ) ≤ max 1 (4 * (σ : ℝ)) := le_max_right _ _
    have hma : 1 ≤ max 1 (4 * (σ : ℝ)) * a := by
      rw [ha]
      calc (1 : ℝ) = 4 * σ * (1 / (4 * σ)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hm2 (by positivity)
    nlinarith [sq_nonneg t, mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one hm1),
      mul_nonneg (sub_nonneg.2 hma) (sq_nonneg t)]
  rw [hexp]
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi * σ))⁻¹ := by positivity
  have he : 0 ≤ Real.exp (-a * t ^ 2) := (Real.exp_pos _).le
  calc (Real.sqrt (2 * Real.pi * σ))⁻¹ * (Real.exp (-a * t ^ 2) * Real.exp (-a * t ^ 2)) *
        (1 + t ^ 2) = (Real.sqrt (2 * Real.pi * σ))⁻¹ * ((1 + t ^ 2) * Real.exp (-a * t ^ 2)) *
          Real.exp (-a * t ^ 2) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi * σ))⁻¹ * max 1 (4 * (σ : ℝ)) * Real.exp (-a * t ^ 2) := by
        gcongr

theorem one_add_sq_le (θ t : ℝ) : 1 + θ ^ 2 ≤ 2 * ((1 + t ^ 2) * (1 + (θ - t) ^ 2)) := by
  nlinarith [sq_nonneg (θ - 2 * t), sq_nonneg (t * (θ - t)), sq_nonneg t, sq_nonneg (θ - t)]

theorem cauchyKernel_mul_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (u : ℝ) :
    cauchyKernel η u * (1 + u ^ 2) ≤ 1 / Real.pi + cauchyKernel η u := by
  unfold cauchyKernel
  have hp := Real.pi_pos
  have hd : 0 < u ^ 2 + η ^ 2 := by positivity
  have e1 : η / (Real.pi * (u ^ 2 + η ^ 2)) * (1 + u ^ 2) =
      (η + η * u ^ 2) / (Real.pi * (u ^ 2 + η ^ 2)) := by ring
  have e2 : 1 / Real.pi + η / (Real.pi * (u ^ 2 + η ^ 2)) =
      (u ^ 2 + η ^ 2 + η) / (Real.pi * (u ^ 2 + η ^ 2)) := by
    field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg u, sq_nonneg η]) (by positivity)

/-- **Uniform Cauchy bound** for `0 < η ≤ 1`: `(P_η ∗ φ_σ)(θ) ≤ K_σ P_1(θ)`. -/
theorem cauchyConv_le {σ : ℝ≥0} (hσ : σ ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ θ : ℝ,
      cauchyConv σ η θ ≤ ENNReal.ofReal (K * cauchyKernel 1 θ) := by
  have hs : (0 : ℝ) < σ := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg σ) with h | h
    · exact absurd (NNReal.coe_eq_zero.1 h.symm) hσ
    · exact h
  set c : ℝ := (Real.sqrt (2 * Real.pi * σ))⁻¹ * max 1 (4 * (σ : ℝ))
  set a : ℝ := 1 / (4 * σ)
  have ha : 0 < a := by positivity
  have hc : 0 ≤ c := by positivity
  set J : ℝ := ∫ t, Real.exp (-a * t ^ 2)
  have hJ : 0 ≤ J := integral_nonneg fun t => (Real.exp_pos _).le
  have hJl : ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t ^ 2)) = ENNReal.ofReal J :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq ha)
      (Eventually.of_forall fun t => (Real.exp_pos _).le)).symm
  refine ⟨2 * c * (J / Real.pi + 1) * Real.pi, by positivity, fun η hη hη1 θ => ?_⟩
  have hθ : 0 < 1 + θ ^ 2 := by positivity
  have hpt : ∀ t, gaussianPDFReal 0 σ t * cauchyKernel η (θ - t) ≤
      (1 + θ ^ 2)⁻¹ * (2 * c) * (Real.exp (-a * t ^ 2) * (1 / Real.pi) +
        Real.exp (-a * t ^ 2) * cauchyKernel η (θ - t)) := by
    intro t
    have h1 := gaussianPDFReal_mul_le hσ t
    have h2 := cauchyKernel_mul_le hη hη1 (θ - t)
    have h3 := one_add_sq_le θ t
    have hφ : 0 ≤ gaussianPDFReal 0 σ t := gaussianPDFReal_nonneg _ _ _
    have hP : 0 ≤ cauchyKernel η (θ - t) := cauchyKernel_nonneg hη.le _
    have he : 0 ≤ Real.exp (-a * t ^ 2) := (Real.exp_pos _).le
    have key : gaussianPDFReal 0 σ t * cauchyKernel η (θ - t) * (1 + θ ^ 2) ≤
        2 * c * (Real.exp (-a * t ^ 2) * (1 / Real.pi) +
          Real.exp (-a * t ^ 2) * cauchyKernel η (θ - t)) := by
     calc gaussianPDFReal 0 σ t * cauchyKernel η (θ - t) * (1 + θ ^ 2)
        ≤ gaussianPDFReal 0 σ t * cauchyKernel η (θ - t) *
            (2 * ((1 + t ^ 2) * (1 + (θ - t) ^ 2))) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hφ hP)
      _ = 2 * ((gaussianPDFReal 0 σ t * (1 + t ^ 2)) *
            (cauchyKernel η (θ - t) * (1 + (θ - t) ^ 2))) := by ring
      _ ≤ 2 * ((c * Real.exp (-a * t ^ 2)) * (1 / Real.pi + cauchyKernel η (θ - t))) := by
          have h1' : gaussianPDFReal 0 σ t * (1 + t ^ 2) ≤ c * Real.exp (-a * t ^ 2) := h1
          have := mul_le_mul h1' h2 (mul_nonneg hP (by positivity)) (by positivity)
          linarith
      _ = _ := by ring
    calc gaussianPDFReal 0 σ t * cauchyKernel η (θ - t) =
        (1 + θ ^ 2)⁻¹ * (gaussianPDFReal 0 σ t * cauchyKernel η (θ - t) * (1 + θ ^ 2)) := by
          field_simp
      _ ≤ (1 + θ ^ 2)⁻¹ * (2 * c * (Real.exp (-a * t ^ 2) * (1 / Real.pi) +
          Real.exp (-a * t ^ 2) * cauchyKernel η (θ - t))) :=
          mul_le_mul_of_nonneg_left key (inv_nonneg.2 hθ.le)
      _ = _ := by ring
  have hmeas1 : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-a * t ^ 2) * (1 / Real.pi)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hmeas2 : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-a * t ^ 2) *
      cauchyKernel η (θ - t)) :=
    ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun t : ℝ =>
      Real.exp (-a * t ^ 2)).mul ((measurable_cauchyKernel η).comp (measurable_const.sub
        measurable_id)))
  calc cauchyConv σ η θ
      ≤ ∫⁻ t, ENNReal.ofReal ((1 + θ ^ 2)⁻¹ * (2 * c)) *
          (ENNReal.ofReal (Real.exp (-a * t ^ 2) * (1 / Real.pi)) +
            ENNReal.ofReal (Real.exp (-a * t ^ 2) * cauchyKernel η (θ - t))) := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg (Real.exp_pos _).le
          (cauchyKernel_nonneg hη.le _)), ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt t)
    _ = ENNReal.ofReal ((1 + θ ^ 2)⁻¹ * (2 * c)) *
          (ENNReal.ofReal (J / Real.pi) +
            ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t ^ 2) * cauchyKernel η (θ - t))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmeas1]
        congr 2
        have : (fun t : ℝ => ENNReal.ofReal (Real.exp (-a * t ^ 2) * (1 / Real.pi))) =
            fun t => ENNReal.ofReal (Real.exp (-a * t ^ 2)) * ENNReal.ofReal (1 / Real.pi) := by
          funext t; rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        rw [this, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hJl,
          ← ENNReal.ofReal_mul hJ, div_eq_mul_one_div]
        congr 1; ring
    _ ≤ ENNReal.ofReal ((1 + θ ^ 2)⁻¹ * (2 * c)) * (ENNReal.ofReal (J / Real.pi) + 1) := by
        gcongr
        calc ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t ^ 2) * cauchyKernel η (θ - t))
            ≤ ∫⁻ t, ENNReal.ofReal (cauchyKernel η (θ - t)) := by
              refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
              exact mul_le_of_le_one_left (cauchyKernel_nonneg hη.le _)
                (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t]))
          _ = 1 := lintegral_ofReal_cauchyKernel_shift hη θ
    _ = ENNReal.ofReal (2 * c * (J / Real.pi + 1) * Real.pi * cauchyKernel 1 θ) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) zero_le_one,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold cauchyKernel
        have hp := Real.pi_pos
        field_simp
        ring

/-- Scaling: `(P_η ∗ φ)(θ) = ∫ φ(θ - ηc) P_1(c) dc`. -/
theorem cauchyConv_eq_scaled (σ : ℝ≥0) {η : ℝ} (hη : 0 < η) (θ : ℝ) :
    cauchyConv σ η θ = ∫⁻ c, ENNReal.ofReal (gaussianPDFReal 0 σ (θ - η * c) *
      cauchyKernel 1 c) := by
  unfold cauchyConv
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (gaussianPDFReal 0 σ t * cauchyKernel η (θ - t))
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    ((measurable_gaussianPDFReal 0 σ).mul ((measurable_cauchyKernel η).comp
      (measurable_const.sub measurable_id)))
  have hmap := Real.map_volume_mul_left (a := -η) (by linarith)
  have h1 : ∫⁻ c, F (θ + -η * c) = ENNReal.ofReal |(-η)⁻¹| * ∫⁻ t, F t := by
    have := lintegral_map (μ := volume) (g := fun c : ℝ => -η * c)
      (f := fun y => F (θ + y)) (hF.comp (measurable_const.add measurable_id))
      (measurable_const.mul measurable_id)
    rw [hmap, lintegral_smul_measure] at this
    rw [← this, lintegral_add_left_eq_self F θ]
    rfl
  have habs : |(-η)⁻¹| = η⁻¹ := by
    rw [abs_inv, abs_neg, abs_of_pos hη]
  rw [habs] at h1
  have hη' : ENNReal.ofReal η * ENNReal.ofReal η⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hη.le, mul_inv_cancel₀ hη.ne', ENNReal.ofReal_one]
  calc ∫⁻ t, F t = ENNReal.ofReal η * (ENNReal.ofReal η⁻¹ * ∫⁻ t, F t) := by
        rw [← mul_assoc, hη', one_mul]
    _ = ENNReal.ofReal η * ∫⁻ c, F (θ + -η * c) := by rw [h1]
    _ = ∫⁻ c, ENNReal.ofReal η * F (θ + -η * c) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        refine lintegral_congr fun c => ?_
        simp only [F]
        rw [← ENNReal.ofReal_mul hη.le]
        congr 1
        have hsub : θ - (θ + -η * c) = η * c := by ring
        rw [hsub, show θ + -η * c = θ - η * c by ring]
        unfold cauchyKernel
        have hp := Real.pi_pos
        have : 0 < (η * c) ^ 2 + η ^ 2 := by positivity
        field_simp

theorem lintegral_ofReal_cauchyKernel_one :
    ∫⁻ c, ENNReal.ofReal (cauchyKernel 1 c) = 1 := by
  have h := lintegral_ofReal_cauchyKernel_shift (η := 1) one_pos 0
  rw [← lintegral_neg_eq_self] at h
  simpa using h

/-- `(P_η ∗ φ_σ)(θ) → φ_σ(θ)` along `η_k = 1/(k+1)`. -/
theorem tendsto_cauchyConv (σ : ℝ≥0) (θ : ℝ) :
    Tendsto (fun k : ℕ => cauchyConv σ (1 / ((k : ℝ) + 1)) θ) atTop
      (𝓝 (ENNReal.ofReal (gaussianPDFReal 0 σ θ))) := by
  have hη : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  simp_rw [cauchyConv_eq_scaled σ (hη _) θ]
  set M := (Real.sqrt (2 * Real.pi * σ))⁻¹
  have hlim : ∫⁻ c, ENNReal.ofReal (gaussianPDFReal 0 σ θ * cauchyKernel 1 c) =
      ENNReal.ofReal (gaussianPDFReal 0 σ θ) := by
    simp_rw [ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_ofReal_cauchyKernel_one, mul_one]
  rw [← hlim]
  refine tendsto_lintegral_of_dominated_convergence (fun c => ENNReal.ofReal (M * cauchyKernel 1 c))
    (fun k => ?_) (fun k => Eventually.of_forall fun c => ?_) ?_ (Eventually.of_forall fun c => ?_)
  · exact ENNReal.measurable_ofReal.comp (((measurable_gaussianPDFReal 0 σ).comp
      (measurable_const.sub (measurable_const.mul measurable_id))).mul (measurable_cauchyKernel 1))
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (gaussianPDFReal_le_const σ _)
      (cauchyKernel_nonneg zero_le_one _))
  · simp_rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ M by positivity)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_ofReal_cauchyKernel_one, mul_one]
    exact ENNReal.ofReal_ne_top
  · refine ENNReal.tendsto_ofReal (Tendsto.mul_const _ ?_)
    have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun k : ℕ => θ - 1 / ((k : ℝ) + 1) * c) atTop (𝓝 θ) := by
      have := (h0.mul_const c).const_sub θ
      simpa using this
    exact ((continuous_gaussianPDFReal' σ).tendsto θ).comp h1

end BlockBand.Critical.Collar.Density
