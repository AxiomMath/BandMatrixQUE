module
public import BlockBand.SourceProcess.Stochastic.Integral.BracketAdapted
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The bracket / isometry martingale

Measure `P = driverLaw μ`, raw filtration `F = commonWienerFiltration S κ`, integrands on
`(0,T]` (`L²(dt ⊗ P)`, a.e. raw predictable). For native `g, h` with draft continuous
representatives `X = nativeAdaptedLimit μ T hg.family`, `Y = nativeAdaptedLimit μ T hh.family`
and the pathwise drift `A_t = bracketDrift T g h t = ∫_{(0,t∧T]} ∑_a g_a h_a ds`:

* `setIntegral_increment_mul` (**conditional isometry**): for `r ≤ t`, `B ∈ F_r`,
  `∫_B (X_t − X_r)(Y_t − Y_r) dP = ∫_B (A_t − A_r) dP`.

It gives, in the sibling module:
* `bracket_martingale`: `X_t Y_t − A_t` has a raw-filtration martingale modification;
* `bracket_martingale_stopped`: for an augmented stopping time `τ`,
  `X_{t∧τ} Y_{t∧τ} − ∫_{(0,t∧T]} 1{s ≤ τ} ∑_a g_a h_a ds` has a raw martingale modification.

Route: `1_B (X_t − X_r) = I_T(1_{(r,t]×B} g)` (`fullNativeIntegral_indicator_rectangle`), the
isometry `⟪I a, I b⟫ = ⟪a, b⟫`, Fubini (`setIntegral_bracketDrift_sub`); cross terms vanish by
the martingale property; adaptedness of `A_t` up to null sets from `exists_adapted_bracketDrift`.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology InnerProductSpace
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

omit [Fintype κ] in
/-- On `(0,T]`, `(r,t]` and `(r ∧ T, t ∧ T]` coincide. -/
theorem mem_Ioc_min_iff {r t : ℝ≥0} {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) (T : ℝ)) :
    s ∈ Set.Ioc ((min r T : ℝ≥0) : ℝ) ((min t T : ℝ≥0) : ℝ) ↔ s ∈ Set.Ioc (r : ℝ) (t : ℝ) := by
  simp only [Set.mem_Ioc, NNReal.coe_min, min_lt_iff, le_min_iff]
  have hT : ¬ (T : ℝ) < s := not_lt.2 hs.2
  constructor
  · rintro ⟨h1 | h1, h2, -⟩
    · exact ⟨h1, h2⟩
    · exact absurd h1 hT
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inl h1, h2, hs.2⟩

/-- The isometry on a predictable rectangle `R`: `E[I(1_R g) I(1_R h)] = ∫ 1_R ∑_a g_a h_a`. -/
theorem integral_mul_indicatorFamily {g h : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) (R : Set (ℝ × DriverSample S κ))
    (hR : MeasurableSet[rawPredictable S κ] R) :
    ∫ x, (fullNativeIntegral (κ := κ) μ T (indicatorFamily R hR hg.family) : DriverSample S κ → ℝ) x *
      (fullNativeIntegral (κ := κ) μ T (indicatorFamily R hR hh.family) : DriverSample S κ → ℝ) x
        ∂driverLaw (κ := κ) μ =
      ∫ p, R.indicator (bracketDensity g h) p ∂timeProbMeasure T (driverLaw (κ := κ) μ) := by
  have hRm : MeasurableSet R := predictableSpace_le _ R hR
  have h1 := LinearIsometry.inner_map_map (𝕜 := ℝ) (fullNativeIntegral (κ := κ) μ T)
    (indicatorFamily R hR hg.family) (indicatorFamily R hR hh.family)
  rw [L2.inner_def, PiLp.inner_apply] at h1
  simp only [RCLike.inner_apply', conj_trivial] at h1
  rw [h1]
  have hterm (c : κ) : ⟪(indicatorFamily R hR hg.family).ofLp c,
      (indicatorFamily R hR hh.family).ofLp c⟫_ℝ =
      ∫ p, R.indicator (g c) p * R.indicator (h c) p
        ∂timeProbMeasure T (driverLaw (κ := κ) μ) := by
    change ⟪indicatorScalar R hR (hg.family c), indicatorScalar R hR (hh.family c)⟫_ℝ = _
    rw [Submodule.coe_inner, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [indicatorScalar_coeFn R hR (hg.family c),
      indicatorScalar_coeFn R hR (hh.family c), nativeIntegrand_family_coeFn hg c,
      nativeIntegrand_family_coeFn hh c] with p h1 h2 h3 h4
    rw [RCLike.inner_apply', conj_trivial, h1, h2]
    by_cases hp : p ∈ R
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp,
        Set.indicator_of_mem hp, h3, h4]
    · simp only [Set.indicator_of_notMem hp, mul_zero]
  simp_rw [hterm]
  have hsum := integral_finsetSum (μ := timeProbMeasure T (driverLaw (κ := κ) μ))
    (Finset.univ : Finset κ) (f := fun c p => R.indicator (g c) p * R.indicator (h c) p)
    fun c _ => ((hg c).2.indicator hRm.nullMeasurableSet).integrable_mul
      ((hh c).2.indicator hRm.nullMeasurableSet)
  beta_reduce at hsum
  rw [← hsum]
  congr 1
  funext p
  by_cases hp : p ∈ R
  · simp only [Set.indicator_of_mem hp, bracketDensity]
  · simp only [Set.indicator_of_notMem hp, mul_zero, Finset.sum_const_zero]

/-- **Conditional isometry.** For `r ≤ t` and a raw `B ∈ F_r`,
`∫_B (X_t − X_r)(Y_t − Y_r) dP = ∫_B (A_t − A_r) dP`. -/
theorem setIntegral_increment_mul {g h : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) {r t : ℝ≥0} (hrt : r ≤ t)
    {B : Set (DriverSample S κ)} (hB : MeasurableSet[commonWienerFiltration S κ r] B) :
    ∫ x in B, (nativeAdaptedLimit μ T hg.family t x - nativeAdaptedLimit μ T hg.family r x) *
      (nativeAdaptedLimit μ T hh.family t x - nativeAdaptedLimit μ T hh.family r x)
        ∂driverLaw (κ := κ) μ =
      ∫ x in B, (bracketDrift T g h t x - bracketDrift T g h r x) ∂driverLaw (κ := κ) μ := by
  classical
  have hBm : MeasurableSet B := (commonWienerFiltration S κ).le r B hB
  have hR := measurableSet_predictableRectangle enlargedPredictableFiltration (t := t) hB
  rw [setIntegral_bracketDrift_sub hg hh hrt hBm, ← integral_indicator hBm]
  have hl := integral_mul_indicatorFamily hg hh (Set.Ioc (r : ℝ) (t : ℝ) ×ˢ B) hR
  have hcongr : (fun x => B.indicator (fun x =>
      (nativeAdaptedLimit μ T hg.family t x - nativeAdaptedLimit μ T hg.family r x) *
      (nativeAdaptedLimit μ T hh.family t x - nativeAdaptedLimit μ T hh.family r x)) x) =ᵐ[driverLaw (κ := κ) μ]
      fun x => (fullNativeIntegral (κ := κ) μ T (indicatorFamily _ hR hg.family) :
        DriverSample S κ → ℝ) x *
        (fullNativeIntegral (κ := κ) μ T (indicatorFamily _ hR hh.family) :
          DriverSample S κ → ℝ) x := by
    filter_upwards [fullNativeIntegral_indicator_rectangle μ T hg.family hrt hB,
      fullNativeIntegral_indicator_rectangle μ T hh.family hrt hB] with x h1 h2
    rw [h1, h2]
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, mul_zero]
  rw [integral_congr_ae hcongr, hl]
  apply integral_congr_ae
  filter_upwards [timeProbMeasure_horizon (κ := κ) μ T] with p hp
  have hiff : p ∈ Set.Ioc (r : ℝ) (t : ℝ) ×ˢ B ↔
      p ∈ Set.Ioc ((min r T : ℝ≥0) : ℝ) ((min t T : ℝ≥0) : ℝ) ×ˢ B := by
    simp only [Set.mem_prod, mem_Ioc_min_iff hp]
  by_cases hpR : p ∈ Set.Ioc (r : ℝ) (t : ℝ) ×ˢ B
  · rw [Set.indicator_of_mem hpR, Set.indicator_of_mem (hiff.1 hpR)]
  · rw [Set.indicator_of_notMem hpR, Set.indicator_of_notMem (fun h => hpR (hiff.2 h))]

omit [MeasurableSpace S] [Fintype κ] in
/-- Cross terms vanish: `E[Z (Y_t − Y_r)] = 0` for an `F_r`-measurable `Z ∈ L²` and an `L²`
martingale `Y`. -/
theorem integral_mul_martingale_increment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Y : ℝ≥0 → Ω → ℝ} (hY : Martingale Y 𝓕 P) (hYL2 : ∀ t, MemLp (Y t) 2 P) {r t : ℝ≥0}
    (hrt : r ≤ t) {Z : Ω → ℝ} (hZm : StronglyMeasurable[𝓕 r] Z) (hZ : MemLp Z 2 P) :
    ∫ x, Z x * (Y t x - Y r x) ∂P = 0 := by
  have hInc : MemLp (Y t - Y r) 2 P := (hYL2 t).sub (hYL2 r)
  have hint : Integrable (Z * (Y t - Y r)) P := hZ.integrable_mul hInc
  have hc : P[Y t - Y r | 𝓕 r] =ᵐ[P] 0 := by
    filter_upwards [condExp_sub ((hYL2 t).integrable one_le_two) ((hYL2 r).integrable one_le_two)
      (𝓕 r), hY.condExp_ae_eq hrt] with x h1 h2
    rw [h1, Pi.sub_apply, h2, condExp_of_stronglyMeasurable (𝓕.le r) (hY.1 r)
      ((hYL2 r).integrable one_le_two), sub_self, Pi.zero_apply]
  calc ∫ x, Z x * (Y t x - Y r x) ∂P = ∫ x, (Z * (Y t - Y r)) x ∂P := rfl
    _ = ∫ x, P[Z * (Y t - Y r) | 𝓕 r] x ∂P := (integral_condExp (𝓕.le r)).symm
    _ = ∫ x, (Z * P[Y t - Y r | 𝓕 r]) x ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hZm hint
          (hInc.integrable one_le_two))
    _ = 0 := by
        rw [integral_congr_ae (hc.mono fun x hx => by
          rw [Pi.mul_apply, hx, Pi.zero_apply, mul_zero])]
        exact integral_zero _ _

end BlockBand.SourceProcess.Stochastic.Integral
