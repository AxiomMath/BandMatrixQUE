module
public import BlockBand.SourceProcess.Stochastic.Integral.Bracket
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Bracket martingales, unstopped and stopped

Measure `P = driverLaw μ`, raw filtration `F = commonWienerFiltration S κ`, augmented stopping
times for `F_t ∨ N`. For integrands `g, h` on `(0,T]` with `X = nativeAdaptedLimit μ T
hg.family`, `Y = nativeAdaptedLimit μ T hh.family`:

* `bracket_martingale`: `∃ N`, a raw-filtration martingale with
  `N_t = X_t Y_t − ∫_{(0,t∧T]} ∑_a g_a h_a ds` a.s. for every `t ≥ 0`;
* `bracket_martingale_stopped`: for an augmented stopping time `τ`, `∃ N` martingale with
  `N_t = X_{t∧τ} Y_{t∧τ} − ∫_{(0,t∧T]} 1{s ≤ τ} ∑_a g_a h_a ds` a.s.
  (`bracketDrift_stopIntegrand` identifies the drift of the stopped integrands).

Taking `g = h` gives the isometry process `X_t² − ∫_0^t ∑_a g_a² ds`.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverCompletion

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

/-- `X_t Y_t − ∫_{(0,t∧T]} ∑_a g_a h_a ds` has a raw-filtration martingale
modification (measure `driverLaw μ`). -/
theorem bracket_martingale {g h : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) :
    ∃ N : ℝ≥0 → DriverSample S κ → ℝ,
      Martingale N (commonWienerFiltration S κ) (driverLaw (κ := κ) μ) ∧
      ∀ t, N t =ᵐ[driverLaw (κ := κ) μ] fun x =>
        nativeAdaptedLimit μ T hg.family t x * nativeAdaptedLimit μ T hh.family t x -
          bracketDrift T g h t x := by
  set X := nativeAdaptedLimit μ T hg.family with hXdef
  set Y := nativeAdaptedLimit μ T hh.family with hYdef
  choose D hDm hD using fun t => exists_adapted_bracketDrift hg hh t
  have hXm (t : ℝ≥0) : StronglyMeasurable[commonWienerFiltration S κ t] (X t) :=
    (nativeAdaptedLimit_adapted μ T hg.family t).stronglyMeasurable
  have hYm (t : ℝ≥0) : StronglyMeasurable[commonWienerFiltration S κ t] (Y t) :=
    (nativeAdaptedLimit_adapted μ T hh.family t).stronglyMeasurable
  have hXL2 := nativeAdaptedLimit_memLp_all μ T hg.family
  have hYL2 := nativeAdaptedLimit_memLp_all μ T hh.family
  have hXmart := nativeAdaptedLimit_martingale μ T hg.family
  have hYmart := nativeAdaptedLimit_martingale μ T hh.family
  let N : ℝ≥0 → DriverSample S κ → ℝ := fun t x => X t x * Y t x - D t x
  have hNm (t : ℝ≥0) : StronglyMeasurable[commonWienerFiltration S κ t] (N t) :=
    ((hXm t).mul (hYm t)).sub ((hDm t).mono ((commonWienerFiltration S κ).mono (min_le_left t T)))
  have hDint (t : ℝ≥0) : Integrable (D t) (driverLaw (κ := κ) μ) :=
    (integrable_bracketDrift hg hh t).congr (hD t)
  have hNint (t : ℝ≥0) : Integrable (N t) (driverLaw (κ := κ) μ) :=
    ((hXL2 t).integrable_mul (hYL2 t)).sub (hDint t)
  refine ⟨N, ⟨hNm, fun r t hrt => ?_⟩, fun t => ?_⟩
  swap
  · filter_upwards [hD t] with x hx
    simp only [N, hx]
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((commonWienerFiltration S κ).le r) (hNint t)
    (fun s _ _ => (hNint r).integrableOn) (fun B hB _ => ?_) (hNm r).aestronglyMeasurable).symm
  have hBm : MeasurableSet B := (commonWienerFiltration S κ).le r B hB
  have hsplit : (fun x => N t x - N r x) =ᵐ[driverLaw (κ := κ) μ] fun x =>
      ((X t x - X r x) * (Y t x - Y r x) - (bracketDrift T g h t x - bracketDrift T g h r x)) +
        (X r x * (Y t x - Y r x) + Y r x * (X t x - X r x)) := by
    filter_upwards [hD t, hD r] with x h1 h2
    simp only [N]
    rw [h1, h2]
    ring
  have hI1 : Integrable (fun x => (X t x - X r x) * (Y t x - Y r x)) (driverLaw (κ := κ) μ) :=
    ((hXL2 t).sub (hXL2 r)).integrable_mul ((hYL2 t).sub (hYL2 r))
  have hI2 : Integrable (fun x => bracketDrift T g h t x - bracketDrift T g h r x)
      (driverLaw (κ := κ) μ) :=
    (integrable_bracketDrift hg hh t).sub (integrable_bracketDrift hg hh r)
  have hI3 : Integrable (fun x => X r x * (Y t x - Y r x)) (driverLaw (κ := κ) μ) :=
    (hXL2 r).integrable_mul ((hYL2 t).sub (hYL2 r))
  have hI4 : Integrable (fun x => Y r x * (X t x - X r x)) (driverLaw (κ := κ) μ) :=
    (hYL2 r).integrable_mul ((hXL2 t).sub (hXL2 r))
  have hcross (Z W : ℝ≥0 → DriverSample S κ → ℝ)
      (hZm : ∀ t, StronglyMeasurable[commonWienerFiltration S κ t] (Z t))
      (hZL2 : ∀ t, MemLp (Z t) 2 (driverLaw (κ := κ) μ))
      (hW : Martingale W (commonWienerFiltration S κ) (driverLaw (κ := κ) μ))
      (hWL2 : ∀ t, MemLp (W t) 2 (driverLaw (κ := κ) μ)) :
      ∫ x in B, Z r x * (W t x - W r x) ∂driverLaw (κ := κ) μ = 0 := by
    rw [← integral_indicator hBm]
    have he : B.indicator (fun x => Z r x * (W t x - W r x)) =
        fun x => B.indicator (Z r) x * (W t x - W r x) := by
      funext x
      exact Set.indicator_mul_left B (Z r) (fun x => W t x - W r x)
    rw [he]
    exact integral_mul_martingale_increment hW hWL2 hrt ((hZm r).indicator hB)
      ((hZL2 r).indicator hBm.nullMeasurableSet)
  have hI12 : Integrable (fun x => (X t x - X r x) * (Y t x - Y r x) -
      (bracketDrift T g h t x - bracketDrift T g h r x)) (driverLaw (κ := κ) μ) := hI1.sub hI2
  have hI34 : Integrable (fun x => X r x * (Y t x - Y r x) + Y r x * (X t x - X r x))
      (driverLaw (κ := κ) μ) := hI3.add hI4
  have key : ∫ x in B, (N t x - N r x) ∂driverLaw (κ := κ) μ = 0 := by
    rw [integral_congr_ae (ae_restrict_of_ae hsplit),
      integral_add hI12.integrableOn hI34.integrableOn,
      integral_sub hI1.integrableOn hI2.integrableOn, setIntegral_increment_mul hg hh hrt hB,
      sub_self, zero_add, integral_add hI3.integrableOn hI4.integrableOn,
      hcross X Y hXm hXL2 hYmart hYL2, hcross Y X hYm hYL2 hXmart hXL2, add_zero]
  rw [integral_sub (hNint t).integrableOn (hNint r).integrableOn] at key
  linarith

omit [MeasurableSpace S] [IsProbabilityMeasure μ] in
theorem bracketDensity_stopIntegrand (τ : DriverSample S κ → WithTop ℝ≥0)
    (g h : κ → ℝ × DriverSample S κ → ℝ) (p : ℝ × DriverSample S κ) :
    bracketDensity (stopIntegrand τ g) (stopIntegrand τ h) p =
      if ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2 then bracketDensity g h p else 0 := by
  unfold bracketDensity stopIntegrand
  split_ifs <;> simp

omit [MeasurableSpace S] [IsProbabilityMeasure μ] in
/-- The drift of the stopped integrands is the stopped drift `∫_{(0,t∧T]} 1{s ≤ τ} ∑ g h ds`. -/
theorem bracketDrift_stopIntegrand (τ : DriverSample S κ → WithTop ℝ≥0)
    (g h : κ → ℝ × DriverSample S κ → ℝ) (t : ℝ≥0) (x : DriverSample S κ) :
    bracketDrift T (stopIntegrand τ g) (stopIntegrand τ h) t x =
      ∫ s in Set.Ioc (0 : ℝ) ((min t T : ℝ≥0) : ℝ),
        if ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x then ∑ c, g c (s, x) * h c (s, x) else 0 := by
  simp only [bracketDrift, bracketDensity_stopIntegrand]
  rfl

/-- For an augmented stopping time `τ`,
`X_{t∧τ} Y_{t∧τ} − ∫_{(0,t∧T]} 1{s ≤ τ} ∑_a g_a h_a ds` has a raw martingale modification. -/
theorem bracket_martingale_stopped {g h : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h)
    {τ : DriverSample S κ → WithTop ℝ≥0} (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ) :
    ∃ N : ℝ≥0 → DriverSample S κ → ℝ,
      Martingale N (commonWienerFiltration S κ) (driverLaw (κ := κ) μ) ∧
      ∀ t, N t =ᵐ[driverLaw (κ := κ) μ] fun x =>
        stoppedProcess (nativeAdaptedLimit μ T hg.family) τ t x *
          stoppedProcess (nativeAdaptedLimit μ T hh.family) τ t x -
          bracketDrift T (stopIntegrand τ g) (stopIntegrand τ h) t x := by
  have hgτ := stopIntegrand_nativeIntegrand hg hτ
  have hhτ := stopIntegrand_nativeIntegrand hh hτ
  obtain ⟨N, hN, hNe⟩ := bracket_martingale hgτ hhτ
  refine ⟨N, hN, fun t => ?_⟩
  filter_upwards [hNe t, nativeAdaptedLimit_stopIntegrand hg hτ hgτ t,
    nativeAdaptedLimit_stopIntegrand hh hτ hhτ t] with x h1 h2 h3
  rw [h1, h2, h3]

end BlockBand.SourceProcess.Stochastic.Integral
