module

public import BlockBand.SourceProcess.Stochastic.Ito

/-!
# Mean zero of the Itô integral and the Itô expectation identity

Measure: `driverLaw μ = μ ⊗ Wiener^κ` on `DriverSample S κ`, for an arbitrary probability law
`μ` of the old state `S` and a finite set `κ` of independent standard Brownian coordinates.

* `integral_fullNativeIntegral`, `integral_nativeIntegralOf`: the terminal Itô
  integral (the isometry `fullNativeIntegral` into `L²(driverLaw μ)`) has mean zero, for
  every horizon `T` and every integrand. Proof: the mean is the continuous functional
  `⟪1, ·⟫` on `L²`; it vanishes on grid presentations (each term is an `F_s`-measurable `L²`
  coefficient times a future Brownian increment), and these are dense
  (`nativeClosedPredictable_eq_top`).
* `integral_sub_integral_of_isNativeItoProcess`: for a real Itô process `X` with `|X| ≤ C_X`
  and drift `|b| ≤ C_B` (uniformly in time and sample), `E X_t - E X_0 = ∫_{(0,t]} E b_s ds` for
  every `t ≥ 0`. Proof: the identity of `IsNativeItoProcess` along the localizing sequence `τ_n`,
  mean zero of the integral, dominated convergence in `n` (the stopped quantities are eventually
  unstopped since `τ_n → ⊤` a.s.), and Fubini on `(0,t] × DriverSample` using progressive
  measurability of `b`.
* `ae_eq_add_drift_of_zero_diffusion`: for an Itô process with zero diffusion in a
  finite-dimensional `E`, `X_t = X_0 + ∫_0^t b_s ds` almost surely, for each fixed `t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]

/-- A grid stochastic sum has mean zero under `driverLaw μ`. -/
theorem integral_gridPresentation_integralLp {T : ℝ≥0} (d : GridPresentation (κ := κ) μ T) :
    ∫ x, (d.integralLp : DriverSample S κ → ℝ) x ∂driverLaw (κ := κ) μ = 0 := by
  rw [GridPresentation.integralLp, integral_congr_ae d.integral_memLp.coeFn_toLp]
  unfold GridPresentation.integral
  rw [integral_finsetSum _ (fun ka _ => (d.term_memLp ka.1 ka.2).integrable (by norm_num))]
  apply Finset.sum_eq_zero
  intro ka _
  have h := driverStep_temporal_orthogonality μ (d.grid.time ka.1.castSucc) (d.grid.step ka.1)
    ka.2 (A := fun _ => (1 : ℝ)) measurable_const (memLp_const 1) (d.adapted ka.1 ka.2)
    (d.coeffL2 ka.1 ka.2)
  simpa [GridPresentation.term] using h

/-- On a probability space the mean of an `L²` class is `⟪1, f⟫`. -/
theorem integral_eq_inner_one (f : Lp ℝ 2 (driverLaw (κ := κ) μ)) :
    ∫ x, (f : DriverSample S κ → ℝ) x ∂driverLaw (κ := κ) μ =
      inner ℝ (indicatorConstLp 2 MeasurableSet.univ
        (measure_ne_top (driverLaw (κ := κ) μ) Set.univ) (1 : ℝ)) f := by
  rw [L2.inner_indicatorConstLp_one, Measure.restrict_univ]

/-- The terminal Itô integral of every predictable `L²` family
has mean zero under `driverLaw μ`. -/
theorem integral_fullNativeIntegral {T : ℝ≥0}
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    ∫ x, (fullNativeIntegral (κ := κ) μ T f : DriverSample S κ → ℝ) x
      ∂driverLaw (κ := κ) μ = 0 := by
  classical
  rw [integral_eq_inner_one]
  set one : Lp ℝ 2 (driverLaw (κ := κ) μ) := indicatorConstLp 2 MeasurableSet.univ
    (measure_ne_top (driverLaw (κ := κ) μ) Set.univ) (1 : ℝ)
  have hc : IsClosed {g : PredictableFamily (S := S) (κ := κ) (μ := μ) T |
      inner ℝ one (fullNativeIntegral (κ := κ) μ T g) = 0} :=
    isClosed_eq (continuous_const.inner (fullNativeIntegral (κ := κ) μ T).continuous)
      continuous_const
  have hsub : ((nativeFinitePredictable (κ := κ) μ T :
      Submodule ℝ (PredictableFamily (S := S) (κ := κ) (μ := μ) T)) :
        Set (PredictableFamily (S := S) (κ := κ) (μ := μ) T)) ⊆
      {g | inner ℝ one (fullNativeIntegral (κ := κ) μ T g) = 0} := by
    rintro g ⟨z, hz, rfl⟩
    rcases nativeGraph_zero_or_presentation μ T hz with rfl | ⟨d, rfl⟩
    · simp
    · change inner ℝ one (fullNativeIntegral (κ := κ) μ T d.predictableFamily) = 0
      rw [fullNativeIntegral_presentation, ← integral_eq_inner_one]
      exact integral_gridPresentation_integralLp d
  have hcl := hc.closure_subset_iff.mpr hsub
  have hf : f ∈ nativeClosedPredictable (κ := κ) μ T := by
    rw [nativeClosedPredictable_eq_top]
    trivial
  exact hcl hf

/-- Mean zero of the Itô integral: for every horizon `T` and every native
integrand `g` on `(0,T]`, `E ∑_a ∫_0^T g_a dW^a = 0` under `driverLaw μ`. -/
theorem integral_nativeIntegralOf {T : ℝ≥0} {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) :
    ∫ x, (nativeIntegralOf hg : DriverSample S κ → ℝ) x ∂driverLaw (κ := κ) μ = 0 :=
  integral_fullNativeIntegral hg.family

omit [MeasurableSpace S] [Fintype κ] in
/-- Uniform bound on the stopped drift: `|∫_0^{t∧τ} b ds| ≤ max C_B 0 · t`. -/
theorem abs_stoppedDrift_le {b : ℝ≥0 → DriverSample S κ → ℝ} {CB : ℝ}
    (hbb : ∀ t x, |b t x| ≤ CB) (τ : DriverSample S κ → WithTop ℝ≥0) (t : ℝ≥0)
    (x : DriverSample S κ) : |stoppedDrift τ b t x| ≤ max CB 0 * t := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc (0 : ℝ) t)
    (f := fun s : ℝ => if ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x then b s.toNNReal x else 0)
    (C := max CB 0) measure_Ioc_lt_top (fun s _ => by
      split_ifs
      · exact (hbb _ _).trans (le_max_left _ _)
      · simp)
  rw [Real.volume_real_Ioc_of_le (NNReal.coe_nonneg t), sub_zero] at h
  exact h

omit [IsProbabilityMeasure μ] in
/-- The drift `(x, s) ↦ b_{min(s⁺, t)}(x)` is jointly strongly measurable (progressive
measurability of `b` at time `t`). -/
theorem stronglyMeasurable_drift_min {b : ℝ≥0 → DriverSample S κ → ℝ}
    (hb : IsStronglyProgressive (driverAugmented (κ := κ) μ) b) (t : ℝ≥0) :
    StronglyMeasurable fun p : DriverSample S κ × ℝ => b (min p.2.toNNReal t) p.1 := by
  have hprog := hb t
  let φ : DriverSample S κ × ℝ → Set.Iic t × DriverSample S κ :=
    fun p => (⟨min p.2.toNNReal t, min_le_right _ _⟩, p.1)
  have h1 : Measurable fun p : DriverSample S κ × ℝ =>
      (⟨min p.2.toNNReal t, min_le_right _ _⟩ : Set.Iic t) :=
    (measurable_real_toNNReal.comp measurable_snd).min measurable_const |>.subtype_mk
  have h2 : Measurable[_, driverAugmented (κ := κ) μ t] fun p : DriverSample S κ × ℝ => p.1 :=
    measurable_fst.mono le_rfl ((driverAugmented (κ := κ) μ).le t)
  have hφ : Measurable[_, Subtype.instMeasurableSpace.prod (driverAugmented (κ := κ) μ t)] φ :=
    @Measurable.prodMk _ _ _ _ Subtype.instMeasurableSpace (driverAugmented (κ := κ) μ t) _ _ h1 h2
  exact hprog.comp_measurable hφ

/-- **Itô expectation identity.** Let `X` be a real Itô process on
`driverLaw μ` with drift `b` and diffusion `σ`, with `|X_t(x)| ≤ C_X` and `|b_t(x)| ≤ C_B` for
all times and samples. Then for every `t ≥ 0`,
`E X_t - E X_0 = ∫_{(0,t]} E b_s ds` (times read through `Real.toNNReal`). -/
theorem integral_sub_integral_of_isNativeItoProcess {X : ℝ≥0 → DriverSample S κ → ℝ}
    {b : ℝ≥0 → DriverSample S κ → ℝ} {σ : κ → ℝ≥0 → DriverSample S κ → ℝ}
    (hX : IsNativeItoProcess μ X b σ) {CX CB : ℝ} (hXb : ∀ t x, |X t x| ≤ CX)
    (hbb : ∀ t x, |b t x| ≤ CB) (t : ℝ≥0) :
    ∫ x, X t x ∂driverLaw (κ := κ) μ - ∫ x, X 0 x ∂driverLaw (κ := κ) μ =
      ∫ s in Set.Ioc (0 : ℝ) t, ∫ x, b s.toNNReal x ∂driverLaw (κ := κ) μ := by
  obtain ⟨τ, hτ, hτlim, hτint⟩ := hX.localizing
  set P := driverLaw (κ := κ) μ with hP
  let D : DriverSample S κ → ℝ := fun x => ∫ s in Set.Ioc (0 : ℝ) t, b s.toNNReal x
  let F : ℕ → DriverSample S κ → ℝ := fun n x =>
    stoppedProcess X (τ n) t x - X 0 x - stoppedDrift (τ n) b t x
  have hFae : ∀ n, ∃ hs : NativeIntegrand μ t
      (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ n x))
        (functionalIntegrand (ContinuousLinearMap.id ℝ ℝ) σ)),
      F n =ᵐ[P] (nativeIntegralOf hs : DriverSample S κ → ℝ) := fun n =>
    hX.identity (ContinuousLinearMap.id ℝ ℝ) (τ n) (hτ n) t
      (hτint n (ContinuousLinearMap.id ℝ ℝ) t) t le_rfl
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) P := fun n => by
    obtain ⟨hs, he⟩ := hFae n
    exact (Lp.aestronglyMeasurable _).congr he.symm
  have hFint : ∀ n, ∫ x, F n x ∂P = 0 := fun n => by
    obtain ⟨hs, he⟩ := hFae n
    rw [integral_congr_ae he]
    exact integral_nativeIntegralOf hs
  have hbound : ∀ n, ∀ᵐ x ∂P, ‖F n x‖ ≤ CX + CX + max CB 0 * t := fun n =>
    Eventually.of_forall fun x => by
      have h1 : |stoppedProcess X (τ n) t x| ≤ CX := hXb _ _
      have h2 := hXb 0 x
      have h3 := abs_stoppedDrift_le hbb (τ n) t x
      rw [Real.norm_eq_abs]
      calc |F n x| ≤ |stoppedProcess X (τ n) t x - X 0 x| + |stoppedDrift (τ n) b t x| :=
            abs_sub _ _
        _ ≤ |stoppedProcess X (τ n) t x| + |X 0 x| + |stoppedDrift (τ n) b t x| := by
            gcongr; exact abs_sub _ _
        _ ≤ CX + CX + max CB 0 * t := by gcongr
  have hlim : ∀ᵐ x ∂P, Tendsto (fun n => F n x) atTop (𝓝 (X t x - X 0 x - D x)) := by
    filter_upwards [hτlim] with x hx
    have hev : ∀ᶠ n in atTop, (t : WithTop ℝ≥0) < τ n x :=
      hx.eventually_const_lt (WithTop.coe_lt_top t)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    simp only [F, D, stoppedDrift]
    rw [stoppedProcess_eq_of_le hn.le]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hst : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ n x :=
      (WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hs.2)).trans hn.le
    beta_reduce
    split_ifs
    rfl
  have hlimint := tendsto_integral_of_dominated_convergence _ hFmeas (integrable_const _)
    hbound hlim
  have hzero : ∫ x, (X t x - X 0 x - D x) ∂P = 0 := by
    simp only [hFint] at hlimint
    exact tendsto_nhds_unique hlimint tendsto_const_nhds
  have hLmeas : AEStronglyMeasurable (fun x => X t x - X 0 x - D x) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hFmeas hlim
  have hXmeas : ∀ u, StronglyMeasurable (X u) := fun u =>
    (hX.adapted u).mono ((driverAugmented (κ := κ) μ).le u)
  have hXint : ∀ u, Integrable (X u) P := fun u =>
    Integrable.of_bound (hXmeas u).aestronglyMeasurable CX
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hXb u x)
  have hDmeas : AEStronglyMeasurable D P := by
    have h := ((hXmeas t).aestronglyMeasurable.sub (hXmeas 0).aestronglyMeasurable).sub hLmeas
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hDint : Integrable D P :=
    Integrable.of_bound hDmeas (max CB 0 * t) (Eventually.of_forall fun x => by
      have h := abs_stoppedDrift_le hbb (fun _ => ⊤) t x
      simp only [stoppedDrift, le_top, ite_true] at h
      rw [Real.norm_eq_abs]
      exact h)
  have e1 : ∫ x, (X t x - X 0 x - D x) ∂P = ∫ x, (X t x - X 0 x) ∂P - ∫ x, D x ∂P :=
    integral_sub ((hXint t).sub (hXint 0)) hDint
  have e2 : ∫ x, (X t x - X 0 x) ∂P = ∫ x, X t x ∂P - ∫ x, X 0 x ∂P :=
    integral_sub (hXint t) (hXint 0)
  rw [e1, e2] at hzero
  have hmain : ∫ x, X t x ∂P - ∫ x, X 0 x ∂P = ∫ x, D x ∂P := by linarith
  rw [hmain]
  -- Fubini on `(0,t] × DriverSample`.
  let g : DriverSample S κ → ℝ → ℝ := fun x s => b (min s.toNNReal t) x
  have hgmeas : StronglyMeasurable (Function.uncurry g) :=
    stronglyMeasurable_drift_min hX.drift_progressive t
  have hgint : Integrable (Function.uncurry g) (P.prod (volume.restrict (Set.Ioc (0 : ℝ) t))) :=
    Integrable.of_bound hgmeas.aestronglyMeasurable CB
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hbb _ _)
  have hcongr : ∀ x, ∀ s ∈ Set.Ioc (0 : ℝ) t, b s.toNNReal x = g x s := fun x s hs => by
    simp only [g, min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]
  calc ∫ x, D x ∂P = ∫ x, (∫ s in Set.Ioc (0 : ℝ) t, g x s) ∂P := by
        apply integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact setIntegral_congr_fun measurableSet_Ioc (fun s hs => hcongr x s hs)
    _ = ∫ s in Set.Ioc (0 : ℝ) t, ∫ x, g x s ∂P := integral_integral_swap hgint
    _ = ∫ s in Set.Ioc (0 : ℝ) t, ∫ x, b s.toNNReal x ∂P := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs
        exact integral_congr_ae (Eventually.of_forall fun x => (hcongr x s hs).symm)

/-- The integral of an integrand that vanishes identically is the zero class. -/
theorem nativeIntegralOf_eq_zero {T : ℝ≥0} {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (h0 : ∀ a p, g a p = 0) : nativeIntegralOf hg = 0 := by
  have hf : hg.family = 0 := by
    apply PiLp.ext
    intro a
    apply (predictableL2_eq_iff_ae_eq _ _).2
    filter_upwards [(hg a).2.coeFn_toLp,
      Lp.coeFn_zero ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))] with p hp hz
    change ((hg a).2.toLp (g a) : ℝ × DriverSample S κ → ℝ) p =
      ((0 : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ) p
    rw [hp, hz, h0]
    rfl
  rw [nativeIntegralOf, hf, map_zero]

omit [IsProbabilityMeasure μ] in
/-- The constant stopping time `⊤` of the augmented driver filtration. -/
theorem isStoppingTime_top_driver :
    IsStoppingTime (driverAugmented (κ := κ) μ) (fun _ => (⊤ : WithTop ℝ≥0)) := fun i => by
  simp

section ZeroDiffusion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Zero diffusion.** If `X` is an Itô process in a finite-dimensional `E` with
drift `b` and zero diffusion, then for every fixed `t`,
`X_t = X_0 + ∫_0^t b_s ds` for `driverLaw μ`-almost every sample. -/
theorem ae_eq_add_drift_of_zero_diffusion {X b : ℝ≥0 → DriverSample S κ → E}
    (hX : IsNativeItoProcess μ X b (fun _ _ _ => 0)) (t : ℝ≥0) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, X t x = X 0 x + stoppedDrift (fun _ => ⊤) b t x := by
  obtain ⟨τ, -, -, hτint⟩ := hX.localizing
  have hℓ : ∀ ℓ : E →L[ℝ] ℝ, ∀ᵐ x ∂driverLaw (κ := κ) μ,
      ℓ (X t x - X 0 x - stoppedDrift (fun _ => ⊤) b t x) = 0 := by
    intro ℓ
    have hfun : stopIntegrand (fun _ => (⊤ : WithTop ℝ≥0))
        (functionalIntegrand ℓ (fun (_ : κ) (_ : ℝ≥0) (_ : DriverSample S κ) => (0 : E))) =
        stopIntegrand (τ 0)
          (functionalIntegrand ℓ (fun (_ : κ) (_ : ℝ≥0) (_ : DriverSample S κ) => (0 : E))) := by
      funext a p
      unfold stopIntegrand functionalIntegrand
      split_ifs <;> simp
    have hint : NativeIntegrand μ t (stopIntegrand (fun _ => (⊤ : WithTop ℝ≥0))
        (functionalIntegrand ℓ (fun (_ : κ) (_ : ℝ≥0) (_ : DriverSample S κ) => (0 : E)))) :=
      hfun ▸ hτint 0 ℓ t
    obtain ⟨hs, he⟩ := hX.identity ℓ (fun _ => ⊤) isStoppingTime_top_driver t hint t le_rfl
    rw [nativeIntegralOf_eq_zero hs (fun a p => by
      unfold stopIntegrand functionalIntegrand
      split_ifs <;> simp)]
      at he
    filter_upwards [he, Lp.coeFn_zero ℝ 2 (driverLaw (κ := κ) μ)] with x hx hz
    rw [stoppedProcess_const_top] at hx
    rw [map_sub, map_sub, hx, hz]
    rfl
  let B := Module.finBasis ℝ E
  have hall : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ i,
      (B.coord i).toContinuousLinearMap (X t x - X 0 x - stoppedDrift (fun _ => ⊤) b t x) = 0 :=
    ae_all_iff.2 fun i => hℓ _
  filter_upwards [hall] with x hx
  have h0 : X t x - X 0 x - stoppedDrift (fun _ => ⊤) b t x = 0 := by
    apply B.ext_elem
    intro i
    simpa using hx i
  rw [sub_sub, sub_eq_zero] at h0
  exact h0

end ZeroDiffusion

end BlockBand.Palm.ReferenceFlow
