module

public import BlockBand.PointProcess.LawProperties
public import BlockBand.Model.Construction.MarkedRotation
public import BlockBand.Counting.SimpleSpectralLimitsTopology

/-!
# Mean spatial intensity from unit spectral intensity and rotation invariance

* `HasUnitSpectralIntensity ν` (mean spectral counting measure is Lebesgue) and
* `IsMarkRotationInvariant ν` (Laplace functional invariant under simultaneous rotation)

imply `HasUniformSpatialIntensity ν` (mean mark-weighted intensity is `du dr`).

Proof. For `f ∈ C_c(ℝ × T)` the profile test `F_f(u, P) = ∫ f(u, r) dP(r)` is in
`C_c(ℝ × P(T))`, and the rotated profile test is `F_{f(·, a + ·)}`. For `f ≥ 0`, Fatou with
`(1 - e^{-cx})/c ↑ x` turns Laplace invariance into invariance of the mean
`E ∫ F_f dξ` (as a lintegral). Averaging over `a ∈ T` (Tonelli, twice) and translation
invariance of Haar measure gives `E ∫ F_f dξ = E ∫ g dξ_spec` with `g(u) = ∫_T f(u, r) dr`,
which is `∫ g du` by unit intensity. General `f` splits into positive and negative parts.
No other input is used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Stationarity

open MeasureTheory Set Filter Topology
open BlockBand.Model.Construction
open scoped ENNReal

/-- The Haar measure `volume` on the unit torus `AddCircle 1` has total mass one. -/
instance torus_volume_isProbabilityMeasure : IsProbabilityMeasure (volume : Measure Torus) :=
  ⟨by simp [AddCircle.measure_univ]⟩

/-- The Haar probability on the torus, as a mass profile. -/
def haarProfile : MassProfile := ⟨volume, inferInstance⟩

/-- The (compact) projection of the support of a test on `ℝ × T` to `ℝ`. -/
def spectralShadow (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) : Set ℝ :=
  Prod.fst '' tsupport f

theorem isCompact_spectralShadow (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) :
    IsCompact (spectralShadow f) :=
  f.hasCompactSupport.image continuous_fst

theorem apply_eq_zero_of_not_mem_spectralShadow
    (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) {u : ℝ} (hu : u ∉ spectralShadow f)
    (r : Torus) : f (u, r) = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hu ⟨(u, r), h, rfl⟩)

/-- Integration of a jointly continuous family against a mass profile is jointly continuous. -/
theorem continuous_profile_integral {Y : Type*} [TopologicalSpace Y] (φ : Y × Torus → ℝ)
    (hφ : Continuous φ) :
    Continuous (fun p : Y × MassProfile => ∫ r, φ (p.1, r) ∂(p.2 : Measure Torus)) := by
  let g : C(Y, C(Torus, ℝ)) := (⟨φ, hφ⟩ : C(Y × Torus, ℝ)).curry
  exact continuous_massProfile_integral.comp ((g.continuous.comp continuous_fst).prodMk
    continuous_snd)

/-- The profile test `F_f(u, P) = ∫ f(u, r) dP(r)`, a compactly supported continuous test on
the marked space `ℝ × P(T)` (compactness of `P(T)` gives the compact support). -/
def profileTest (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) :
    CompactlySupportedContinuousMap MarkedSpectralSpace ℝ where
  toFun := fun z => ∫ r, f (z.1, r) ∂(z.2 : Measure Torus)
  continuous_toFun := continuous_profile_integral (fun p => f p) f.continuous
  hasCompactSupport' := by
    refine HasCompactSupport.intro ((isCompact_spectralShadow f).prod isCompact_univ) ?_
    intro z hz
    have hz1 : z.1 ∉ spectralShadow f := fun h => hz ⟨h, mem_univ _⟩
    simp [apply_eq_zero_of_not_mem_spectralShadow f hz1]

theorem profileTest_apply (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (z : MarkedSpectralSpace) :
    profileTest f z = ∫ r, f (z.1, r) ∂(z.2 : Measure Torus) := rfl

theorem profileTest_nonneg (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (hf : ∀ p, 0 ≤ f p) (z : MarkedSpectralSpace) : 0 ≤ profileTest f z :=
  integral_nonneg (fun _ => hf _)

/-- The rotated test `f(u, a + r)`. -/
def rotateTest (a : Torus) (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) :
    CompactlySupportedContinuousMap (ℝ × Torus) ℝ where
  toFun := fun p => f (p.1, a + p.2)
  continuous_toFun := f.continuous.comp (continuous_fst.prodMk (continuous_const.add continuous_snd))
  hasCompactSupport' := by
    refine HasCompactSupport.intro ((isCompact_spectralShadow f).prod isCompact_univ) ?_
    intro p hp
    exact apply_eq_zero_of_not_mem_spectralShadow f (fun h => hp ⟨h, mem_univ _⟩) _

theorem rotateTest_apply (a : Torus) (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (p : ℝ × Torus) : rotateTest a f p = f (p.1, a + p.2) := rfl

/-- The rotated profile test is the profile test of the rotated test. -/
theorem profileTest_rotate (a : Torus) (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (z : MarkedSpectralSpace) :
    profileTest f (z.1, z.2.map (Homeomorph.addLeft a)) = profileTest (rotateTest a f) z := by
  rw [profileTest_apply, profileTest_apply, ProbabilityMeasure.toMeasure_map]
  exact integral_map (Homeomorph.addLeft a).continuous.measurable.aemeasurable
    (f.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

/-- The Haar average `g_f(u) = ∫_T f(u, r) dr`, a compactly supported continuous test on `ℝ`. -/
def haarTest (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) :
    CompactlySupportedContinuousMap ℝ ℝ where
  toFun := fun u => ∫ r, f (u, r)
  continuous_toFun := (profileTest f).continuous.comp
    (continuous_id.prodMk continuous_const : Continuous fun u : ℝ => (u, haarProfile))
  hasCompactSupport' := by
    refine HasCompactSupport.intro (isCompact_spectralShadow f) ?_
    intro u hu
    simp [apply_eq_zero_of_not_mem_spectralShadow f hu]

theorem haarTest_apply (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) (u : ℝ) :
    haarTest f u = ∫ r, f (u, r) := rfl

theorem haarTest_nonneg (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (hf : ∀ p, 0 ≤ f p) (u : ℝ) : 0 ≤ haarTest f u :=
  integral_nonneg (fun _ => hf _)

/-- The mark-weighted mean functional `X_f(ξ) = ∫ F_f dξ`. -/
def markedMean (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) (ξ : MarkedPointMeasure) :
    ℝ :=
  ∫ z, profileTest f z ∂ξ.marked.measure

theorem continuous_markedMean (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) :
    Continuous (markedMean f) :=
  (continuous_vaguePointMeasure_coordinate (profileTest f)).comp continuous_induced_dom

theorem markedMean_nonneg (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (hf : ∀ p, 0 ≤ f p) (ξ : MarkedPointMeasure) : 0 ≤ markedMean f ξ :=
  integral_nonneg (profileTest_nonneg f hf)

theorem integrable_profileTest (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (ξ : MarkedPointMeasure) : Integrable (profileTest f) ξ.marked.measure := by
  have := massProfile_borelSpace
  exact (profileTest f).continuous.integrable_of_hasCompactSupport (profileTest f).hasCompactSupport

theorem integrable_slice (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) (u : ℝ)
    (P : Measure Torus) [IsFiniteMeasure P] : Integrable (fun r => f (u, r)) P :=
  (f.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-!
## Laplace invariance gives invariance of means
-/

/-- The scale `1/(n+1)`. -/
def laplaceScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem laplaceScale_pos (n : ℕ) : 0 < laplaceScale n := by
  unfold laplaceScale
  positivity

/-- `(1 - e^{-ct})/c` at `c = 1/(n+1)`; it increases to `t`. -/
def laplaceApprox (n : ℕ) (t : ℝ) : ℝ :=
  (1 - Real.exp (-(laplaceScale n * t))) / laplaceScale n

theorem continuous_laplaceApprox (n : ℕ) : Continuous (laplaceApprox n) := by
  unfold laplaceApprox
  fun_prop

theorem laplaceApprox_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ laplaceApprox n t := by
  apply div_nonneg _ (laplaceScale_pos n).le
  have : Real.exp (-(laplaceScale n * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (laplaceScale_pos n).le ht))
  linarith

theorem laplaceApprox_le (n : ℕ) (t : ℝ) : laplaceApprox n t ≤ t := by
  rw [laplaceApprox, div_le_iff₀ (laplaceScale_pos n)]
  have := Real.add_one_le_exp (-(laplaceScale n * t))
  linarith

theorem tendsto_laplaceApprox {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => laplaceApprox n t) atTop (𝓝 t) := by
  have hc0 : Tendsto laplaceScale atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlow : Tendsto (fun n => t - laplaceScale n * t ^ 2) atTop (𝓝 t) := by
    simpa using (hc0.mul_const (t ^ 2)).const_sub t
  have hev : ∀ᶠ n in atTop, laplaceScale n * t ≤ 1 := by
    have h1 : Tendsto (fun n => laplaceScale n * t) atTop (𝓝 0) := by
      simpa using hc0.mul_const t
    exact h1.eventually (ge_mem_nhds zero_lt_one)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun n => laplaceApprox_le n t)
  filter_upwards [hev] with n hn
  have hcpos := laplaceScale_pos n
  have hct : 0 ≤ laplaceScale n * t := mul_nonneg hcpos.le ht
  have habs := Real.abs_exp_sub_one_sub_id_le (x := -(laplaceScale n * t))
    (by rw [abs_neg, abs_of_nonneg hct]; exact hn)
  have hle := (le_abs_self _).trans habs
  rw [laplaceApprox, le_div_iff₀ hcpos]
  nlinarith [hle]

/-- Equal Laplace transforms at all nonnegative arguments give ordered (hence equal)
lintegral means, by Fatou; no integrability is assumed. -/
theorem lintegral_ofReal_le_of_laplace_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (x y : Ω → ℝ) (hx : Measurable x) (hy : Measurable y)
    (hx0 : ∀ w, 0 ≤ x w) (hy0 : ∀ w, 0 ≤ y w)
    (h : ∀ c : ℝ, 0 ≤ c → ∫ w, Real.exp (-(c * x w)) ∂μ = ∫ w, Real.exp (-(c * y w)) ∂μ) :
    ∫⁻ w, ENNReal.ofReal (x w) ∂μ ≤ ∫⁻ w, ENNReal.ofReal (y w) ∂μ := by
  have hint : ∀ (z : Ω → ℝ), Measurable z → (∀ w, 0 ≤ z w) → ∀ n : ℕ,
      ∫⁻ w, ENNReal.ofReal (laplaceApprox n (z w)) ∂μ =
        ENNReal.ofReal ((1 - ∫ w, Real.exp (-(laplaceScale n * z w)) ∂μ) / laplaceScale n) := by
    intro z hz hz0 n
    have hexp : Integrable (fun w => Real.exp (-(laplaceScale n * z w))) μ := by
      refine Integrable.of_bound (by fun_prop : Measurable fun w =>
        Real.exp (-(laplaceScale n * z w))).aestronglyMeasurable 1 (Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (laplaceScale_pos n).le (hz0 w)))
    have hint2 : Integrable (fun w => laplaceApprox n (z w)) μ :=
      ((integrable_const (1 : ℝ)).sub hexp).div_const _
    rw [← ofReal_integral_eq_lintegral_ofReal hint2
      (Eventually.of_forall fun w => laplaceApprox_nonneg n (hz0 w))]
    congr 1
    simp only [laplaceApprox]
    rw [integral_div, integral_sub (integrable_const 1) hexp]
    simp
  have happrox : ∀ n : ℕ, ∫⁻ w, ENNReal.ofReal (laplaceApprox n (x w)) ∂μ =
      ∫⁻ w, ENNReal.ofReal (laplaceApprox n (y w)) ∂μ := by
    intro n
    rw [hint x hx hx0, hint y hy hy0, h _ (laplaceScale_pos n).le]
  have hmeas : ∀ n : ℕ, Measurable (fun w => ENNReal.ofReal (laplaceApprox n (x w))) :=
    fun n => ENNReal.measurable_ofReal.comp ((continuous_laplaceApprox n).measurable.comp hx)
  calc ∫⁻ w, ENNReal.ofReal (x w) ∂μ
      = ∫⁻ w, liminf (fun n : ℕ => ENNReal.ofReal (laplaceApprox n (x w))) atTop ∂μ := by
        refine lintegral_congr fun w => ?_
        exact ((ENNReal.tendsto_ofReal (tendsto_laplaceApprox (hx0 w))).liminf_eq).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ w, ENNReal.ofReal (laplaceApprox n (x w)) ∂μ) atTop :=
        lintegral_liminf_le hmeas
    _ = liminf (fun n : ℕ => ∫⁻ w, ENNReal.ofReal (laplaceApprox n (y w)) ∂μ) atTop := by
        simp only [happrox]
    _ ≤ ∫⁻ w, ENNReal.ofReal (y w) ∂μ := by
        refine (liminf_le_liminf (Eventually.of_forall fun n => lintegral_mono fun w =>
          ENNReal.ofReal_le_ofReal (laplaceApprox_le n (y w)))).trans (le_of_eq (liminf_const _))

/-- Rotation invariance of the Laplace functional, applied to `c • F_f`, in mean form. -/
theorem laplace_markedMean_rotate (ν : ProbabilityMeasure MarkedPointMeasure)
    (hR : IsMarkRotationInvariant ν) (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (hf : ∀ p, 0 ≤ f p) (a : Torus) (c : ℝ) (hc : 0 ≤ c) :
    ∫ ξ, Real.exp (-(c * markedMean (rotateTest a f) ξ)) ∂(ν : Measure MarkedPointMeasure) =
      ∫ ξ, Real.exp (-(c * markedMean f ξ)) ∂(ν : Measure MarkedPointMeasure) := by
  have h := hR a (c • profileTest f) (fun z => by
    rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hc (profileTest_nonneg f hf z))
  have e1 : ∀ ξ : MarkedPointMeasure,
      (∫ z, (c • profileTest f) (z.1, z.2.map (Homeomorph.addLeft a)) ∂ξ.marked.measure) =
        c * markedMean (rotateTest a f) ξ := by
    intro ξ
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, profileTest_rotate]
    exact integral_const_mul c _
  have e2 : ∀ ξ : MarkedPointMeasure,
      (∫ z, (c • profileTest f) z ∂ξ.marked.measure) = c * markedMean f ξ := by
    intro ξ
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  simp only [e1, e2] at h
  exact h

/-- For nonnegative `f`, the lintegral mean of `X_f` is rotation invariant. -/
theorem lintegral_markedMean_rotate (ν : ProbabilityMeasure MarkedPointMeasure)
    (hR : IsMarkRotationInvariant ν) (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (hf : ∀ p, 0 ≤ f p) (a : Torus) :
    ∫⁻ ξ, ENNReal.ofReal (markedMean (rotateTest a f) ξ) ∂(ν : Measure MarkedPointMeasure) =
      ∫⁻ ξ, ENNReal.ofReal (markedMean f ξ) ∂(ν : Measure MarkedPointMeasure) := by
  have hrf : ∀ p, 0 ≤ rotateTest a f p := fun _ => hf _
  apply le_antisymm
  · exact lintegral_ofReal_le_of_laplace_eq _ _ _ (continuous_markedMean _).measurable
      (continuous_markedMean _).measurable (markedMean_nonneg _ hrf) (markedMean_nonneg _ hf)
      (fun c hc => laplace_markedMean_rotate ν hR f hf a c hc)
  · exact lintegral_ofReal_le_of_laplace_eq _ _ _ (continuous_markedMean _).measurable
      (continuous_markedMean _).measurable (markedMean_nonneg _ hf) (markedMean_nonneg _ hrf)
      (fun c hc => (laplace_markedMean_rotate ν hR f hf a c hc).symm)

/-!
## Averaging over rotations
-/

theorem ofReal_integral_torus (P : Measure Torus) [IsFiniteMeasure P] (h : Torus → ℝ)
    (hc : Continuous h) (h0 : ∀ r, 0 ≤ h r) :
    ENNReal.ofReal (∫ r, h r ∂P) = ∫⁻ r, ENNReal.ofReal (h r) ∂P :=
  ofReal_integral_eq_lintegral_ofReal
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h))
    (Eventually.of_forall h0)

/-- Haar average of the rotated profile test at one marked point: mass one of the profile and
translation invariance of Haar measure. -/
theorem lintegral_rotate_profileTest (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (hf : ∀ p, 0 ≤ f p) (z : MarkedSpectralSpace) :
    ∫⁻ a : Torus, ENNReal.ofReal (profileTest (rotateTest a f) z) =
      ENNReal.ofReal (haarTest f z.1) := by
  have hcont : Continuous (fun q : Torus × Torus => f (z.1, q.1 + q.2)) :=
    f.continuous.comp (continuous_const.prodMk (continuous_fst.add continuous_snd))
  calc ∫⁻ a : Torus, ENNReal.ofReal (profileTest (rotateTest a f) z)
      = ∫⁻ a : Torus, (∫⁻ r, ENNReal.ofReal (f (z.1, a + r)) ∂(z.2 : Measure Torus)) := by
        refine lintegral_congr fun a => ?_
        exact ofReal_integral_torus _ (fun r => f (z.1, a + r))
          (f.continuous.comp (continuous_const.prodMk (continuous_const.add continuous_id)))
          (fun _ => hf _)
    _ = ∫⁻ r, (∫⁻ a : Torus, ENNReal.ofReal (f (z.1, a + r))) ∂(z.2 : Measure Torus) :=
        lintegral_lintegral_swap
          (ENNReal.measurable_ofReal.comp hcont.measurable).aemeasurable
    _ = ∫⁻ r, (∫⁻ a : Torus, ENNReal.ofReal (f (z.1, a))) ∂(z.2 : Measure Torus) :=
        lintegral_congr fun r => lintegral_add_right_eq_self (fun a => ENNReal.ofReal (f (z.1, a))) r
    _ = ∫⁻ a : Torus, ENNReal.ofReal (f (z.1, a)) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ = ENNReal.ofReal (haarTest f z.1) :=
        (ofReal_integral_torus volume _
          (f.continuous.comp (continuous_const.prodMk continuous_id)) (fun _ => hf _)).symm

theorem continuous_rotate_profileTest (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (z : MarkedSpectralSpace) : Continuous (fun a : Torus => profileTest (rotateTest a f) z) := by
  have h := continuous_profile_integral (Y := Torus) (fun q : Torus × Torus => f (z.1, q.1 + q.2))
    (f.continuous.comp (continuous_const.prodMk (continuous_fst.add continuous_snd)))
  exact h.comp (continuous_id.prodMk continuous_const : Continuous fun a : Torus => (a, z.2))

theorem measurable_rotate_profileTest (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) :
    Measurable (Function.uncurry fun (a : Torus) (z : MarkedSpectralSpace) =>
      ENNReal.ofReal (profileTest (rotateTest a f) z)) := by
  have := massProfile_borelSpace
  apply measurable_uncurry_of_continuous_of_measurable
  · intro z
    exact ENNReal.continuous_ofReal.comp (continuous_rotate_profileTest f z)
  · intro a
    exact ENNReal.measurable_ofReal.comp (profileTest (rotateTest a f)).continuous.measurable

/-- Rotation continuity of the marked mean, by dominated convergence against the compact
spectral shadow (finite mass for a locally finite measure). -/
theorem continuous_rotate_markedMean (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (ξ : MarkedPointMeasure) : Continuous (fun a : Torus => markedMean (rotateTest a f) ξ) := by
  have := massProfile_borelSpace
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  let K : Set MarkedSpectralSpace := spectralShadow f ×ˢ univ
  have hK : IsCompact K := (isCompact_spectralShadow f).prod isCompact_univ
  have hbound : ∀ (a : Torus) (z : MarkedSpectralSpace),
      ‖profileTest (rotateTest a f) z‖ ≤ K.indicator (fun _ => C) z := by
    intro a z
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
      have h := norm_integral_le_of_norm_le_const (μ := (z.2 : Measure Torus))
        (f := fun r => f (z.1, a + r)) (Eventually.of_forall fun _ => hC _)
      simpa [profileTest_apply, rotateTest_apply] using h
    · rw [indicator_of_notMem hz]
      have hz1 : z.1 ∉ spectralShadow f := fun h => hz ⟨h, mem_univ _⟩
      simp [profileTest_apply, rotateTest_apply, apply_eq_zero_of_not_mem_spectralShadow f hz1]
  apply continuous_of_dominated (bound := K.indicator (fun _ => C))
  · intro a
    exact (profileTest (rotateTest a f)).continuous.aestronglyMeasurable
  · intro a
    exact Eventually.of_forall (hbound a)
  · exact (integrable_indicator_iff hK.isClosed.measurableSet).2
      (integrableOn_const (ξ.marked.finite_on_compact K hK).ne)
  · exact Eventually.of_forall fun z => continuous_rotate_profileTest f z

theorem measurable_rotate_markedMean (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) :
    Measurable (Function.uncurry fun (a : Torus) (ξ : MarkedPointMeasure) =>
      ENNReal.ofReal (markedMean (rotateTest a f) ξ)) := by
  apply measurable_uncurry_of_continuous_of_measurable
  · intro ξ
    exact ENNReal.continuous_ofReal.comp (continuous_rotate_markedMean f ξ)
  · intro a
    exact ENNReal.measurable_ofReal.comp (continuous_markedMean _).measurable

/-- Per configuration: the Haar average over rotations of the marked mean is the spectral
integral of the Haar average `g_f`. -/
theorem lintegral_rotate_markedMean (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ)
    (hf : ∀ p, 0 ≤ f p) (ξ : MarkedPointMeasure) :
    ∫⁻ a : Torus, ENNReal.ofReal (markedMean (rotateTest a f) ξ) =
      ∫⁻ x, ENNReal.ofReal (haarTest f x) ∂ξ.spectral.measure := by
  calc ∫⁻ a : Torus, ENNReal.ofReal (markedMean (rotateTest a f) ξ)
      = ∫⁻ a : Torus, (∫⁻ z, ENNReal.ofReal (profileTest (rotateTest a f) z)
          ∂ξ.marked.measure) := by
        refine lintegral_congr fun a => ?_
        exact ofReal_integral_eq_lintegral_ofReal (integrable_profileTest _ ξ)
          (Eventually.of_forall (profileTest_nonneg _ (fun _ => hf _)))
    _ = ∫⁻ z, (∫⁻ a : Torus, ENNReal.ofReal (profileTest (rotateTest a f) z))
          ∂ξ.marked.measure :=
        lintegral_lintegral_swap (measurable_rotate_profileTest f).aemeasurable
    _ = ∫⁻ z, ENNReal.ofReal (haarTest f z.1) ∂ξ.marked.measure :=
        lintegral_congr fun z => lintegral_rotate_profileTest f hf z
    _ = ∫⁻ x, ENNReal.ofReal (haarTest f x) ∂ξ.spectral.measure := by
        have hm : Measurable fun x : ℝ => ENNReal.ofReal (haarTest f x) :=
          ENNReal.measurable_ofReal.comp (haarTest f).continuous.measurable
        rw [ξ.spectral_eq, lintegral_map hm measurable_fst]

/-- Unit spectral intensity in lintegral form for a nonnegative test. -/
theorem lintegral_spectral_of_unit (ν : ProbabilityMeasure MarkedPointMeasure)
    (hU : HasUnitSpectralIntensity ν) (g : CompactlySupportedContinuousMap ℝ ℝ)
    (hg : ∀ u, 0 ≤ g u) :
    ∫⁻ ξ, ENNReal.ofReal (∫ x, g x ∂ξ.spectral.measure) ∂(ν : Measure MarkedPointMeasure) =
      ENNReal.ofReal (∫ u, g u) := by
  have hY0 : ∀ ξ : MarkedPointMeasure, 0 ≤ ∫ x, g x ∂ξ.spectral.measure :=
    fun _ => integral_nonneg hg
  have hYint : Integrable (fun ξ : MarkedPointMeasure => ∫ x, g x ∂ξ.spectral.measure)
      (ν : Measure MarkedPointMeasure) := by
    by_cases h0 : ∫ u, g u = 0
    · have hgi : Integrable g := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
      have hae : (g : ℝ → ℝ) =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hg hgi).1 h0
      have hzero : (g : ℝ → ℝ) = 0 :=
        (Continuous.ae_eq_iff_eq volume g.continuous continuous_const).1 hae
      have hY : (fun ξ : MarkedPointMeasure => ∫ x, g x ∂ξ.spectral.measure) = 0 := by
        funext ξ
        simp [hzero]
      rw [hY]
      exact integrable_zero _ _ _
    · exact Integrable.of_integral_ne_zero (by rw [hU g]; exact h0)
  rw [← ofReal_integral_eq_lintegral_ofReal hYint (Eventually.of_forall hY0), hU g]

/-- Nonnegative tests: the lintegral mean of `X_f` is `∫ g_f du`. -/
theorem lintegral_markedMean_of_nonneg (ν : ProbabilityMeasure MarkedPointMeasure)
    (hU : HasUnitSpectralIntensity ν) (hR : IsMarkRotationInvariant ν)
    (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∫⁻ ξ, ENNReal.ofReal (markedMean f ξ) ∂(ν : Measure MarkedPointMeasure) =
      ENNReal.ofReal (∫ u, haarTest f u) := by
  calc ∫⁻ ξ, ENNReal.ofReal (markedMean f ξ) ∂(ν : Measure MarkedPointMeasure)
      = ∫⁻ a : Torus, (∫⁻ ξ, ENNReal.ofReal (markedMean (rotateTest a f) ξ)
          ∂(ν : Measure MarkedPointMeasure)) := by
        simp_rw [lintegral_markedMean_rotate ν hR f hf]
        rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ ξ, (∫⁻ a : Torus, ENNReal.ofReal (markedMean (rotateTest a f) ξ))
          ∂(ν : Measure MarkedPointMeasure) :=
        lintegral_lintegral_swap (measurable_rotate_markedMean f).aemeasurable
    _ = ∫⁻ ξ, ENNReal.ofReal (∫ x, haarTest f x ∂ξ.spectral.measure)
          ∂(ν : Measure MarkedPointMeasure) := by
        refine lintegral_congr fun ξ => ?_
        rw [lintegral_rotate_markedMean f hf ξ]
        exact (ofReal_integral_eq_lintegral_ofReal
          ((haarTest f).continuous.integrable_of_hasCompactSupport (haarTest f).hasCompactSupport)
          (Eventually.of_forall (haarTest_nonneg f hf))).symm
    _ = ENNReal.ofReal (∫ u, haarTest f u) :=
        lintegral_spectral_of_unit ν hU (haarTest f) (haarTest_nonneg f hf)

/-- Nonnegative tests: `X_f` is `ν`-integrable with mean `∫ g_f du`. -/
theorem integral_markedMean_of_nonneg (ν : ProbabilityMeasure MarkedPointMeasure)
    (hU : HasUnitSpectralIntensity ν) (hR : IsMarkRotationInvariant ν)
    (f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) (hf : ∀ p, 0 ≤ f p) :
    Integrable (markedMean f) (ν : Measure MarkedPointMeasure) ∧
      ∫ ξ, markedMean f ξ ∂(ν : Measure MarkedPointMeasure) = ∫ u, haarTest f u := by
  have hl := lintegral_markedMean_of_nonneg ν hU hR f hf
  have hmeas : AEStronglyMeasurable (markedMean f) (ν : Measure MarkedPointMeasure) :=
    (continuous_markedMean f).aestronglyMeasurable
  have h0 : 0 ≤ᵐ[(ν : Measure MarkedPointMeasure)] markedMean f :=
    Eventually.of_forall (markedMean_nonneg f hf)
  refine ⟨⟨hmeas, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal h0, hl]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae h0 hmeas, hl,
      ENNReal.toReal_ofReal (integral_nonneg (haarTest_nonneg f hf))]

/-- Linear splitting `f = f₊ - f₋` with nonnegative parts. -/
theorem integral_markedMean_of_split (ν : ProbabilityMeasure MarkedPointMeasure)
    (hU : HasUnitSpectralIntensity ν) (hR : IsMarkRotationInvariant ν)
    (f fp fm : CompactlySupportedContinuousMap (ℝ × Torus) ℝ) (hsplit : ∀ p, f p = fp p - fm p)
    (hfp : ∀ p, 0 ≤ fp p) (hfm : ∀ p, 0 ≤ fm p) :
    ∫ ξ, markedMean f ξ ∂(ν : Measure MarkedPointMeasure) = ∫ u, haarTest f u := by
  have hprof : ∀ z, profileTest f z = profileTest fp z - profileTest fm z := by
    intro z
    simp only [profileTest_apply, hsplit]
    exact integral_sub (integrable_slice fp z.1 _) (integrable_slice fm z.1 _)
  have hmean : ∀ ξ, markedMean f ξ = markedMean fp ξ - markedMean fm ξ := by
    intro ξ
    simp only [markedMean, hprof]
    exact integral_sub (integrable_profileTest fp ξ) (integrable_profileTest fm ξ)
  have hhaar : ∀ u, haarTest f u = haarTest fp u - haarTest fm u := by
    intro u
    simp only [haarTest_apply, hsplit]
    exact integral_sub (integrable_slice fp u _) (integrable_slice fm u _)
  obtain ⟨hip, hp⟩ := integral_markedMean_of_nonneg ν hU hR fp hfp
  obtain ⟨him, hm⟩ := integral_markedMean_of_nonneg ν hU hR fm hfm
  have hgp : Integrable (fun u => haarTest fp u) :=
    (haarTest fp).continuous.integrable_of_hasCompactSupport (haarTest fp).hasCompactSupport
  have hgm : Integrable (fun u => haarTest fm u) :=
    (haarTest fm).continuous.integrable_of_hasCompactSupport (haarTest fm).hasCompactSupport
  simp only [hmean, hhaar]
  rw [integral_sub hip him, hp, hm]
  exact (integral_sub hgp hgm).symm

/-- Stationarity, mean-intensity clause, abstract form. Law: any
probability law `ν` on marked point measures `MarkedPointMeasure` (spectral locations in `ℝ`,
marks in `P(T)`, `T = AddCircle 1` with Haar probability). Hypotheses: unit spectral
intensity (`E ∫ g dξ_spec = ∫ g du` for all `g ∈ C_c(ℝ)`) and simultaneous mark-rotation
invariance of the Laplace functional (all rotations `a ∈ T`, all nonnegative
`F ∈ C_c(ℝ × P(T))`). Conclusion: for every `f ∈ C_c(ℝ × T)`,
`E ∫∫ f(u, r) dP(r) dξ(u, P) = ∫∫ f(u, r) dr du` (Bochner integrals; integrability is
proved). No further hypothesis is used. -/
theorem hasUniformSpatialIntensity_of_unit_of_rotation
    (ν : ProbabilityMeasure MarkedPointMeasure)
    (hU : HasUnitSpectralIntensity ν) (hR : IsMarkRotationInvariant ν) :
    HasUniformSpatialIntensity ν := by
  intro f
  have hsplit : ∀ p, f p = f.nnrealPart.toReal p - (-f).nnrealPart.toReal p := by
    intro p
    simp
  have h := integral_markedMean_of_split ν hU hR f f.nnrealPart.toReal (-f).nnrealPart.toReal
    hsplit (fun p => by simp) (fun p => by simp)
  exact h

end BlockBand.Stationarity
