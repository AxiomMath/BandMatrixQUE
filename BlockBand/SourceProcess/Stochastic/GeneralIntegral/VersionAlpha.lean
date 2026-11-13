module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.PredSample
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Setting
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Jointly measurable versions of bracket densities

Setting: an arbitrary measurable space `(Ω, m₀)`, raw filtration `𝓖`, a `𝓖`-adapted process
`Y : ℝ≥0 → Ω → E` with `Q`-a.s. continuous paths (`Y` itself need not be jointly
measurable), `φ : E → ℝ` continuous (e.g. `y ↦ a(y) i j` for a continuous covariance `a`),
and a raw `𝓖`-stopping time `τ`. The intended density is `α_s(ω) = φ(Y_s ω) 1{s ≤ τ ω}`
(`stoppedComposite`), which need not be jointly measurable off the null set of
discontinuous paths.

* `compositeVersion τ φ Y = lim_n leftSample n (φ(Y) 1{· < τ})` (a `limUnder`), raw
  predictable everywhere (`stronglyMeasurable_compositeVersion`), `0` for `s ≤ 0`.
* `alphaVersion τ φ Y t ω = compositeVersion τ φ Y (t, ω)`; `alphaVersionPos` its positive
  part. Read through `s ↦ s.toNNReal` they are jointly measurable and raw predictable
  (`measurable_alphaVersion`, `stronglyMeasurable_alphaVersion`), exactly the form of
  `IsL2Integrator.alpha_measurable`.
* On **every** continuous path and every `t > 0`, `alphaVersion t ω = φ(Y_t ω) 1{t ≤ τ ω}`
  (`alphaVersion_eq`; for `alphaVersionPos` when `φ ≥ 0`), hence equality `dt ⊗ Q`-a.e.
  (and `μ`-a.e. for `μ ≪ dt ⊗ Q`) and equality of all pathwise integrals `∫_{(0,t]}` a.s.
* `IsL2Integrator.congr_alpha`: an integrator for `α` is one for any measurable nonnegative
  `α'` with `α'_t = α_t` for all `t > 0`, a.s.; `bracketMeasure_congr`: then `ν_T` is
  unchanged.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {E : Type*} [TopologicalSpace E]

omit mΩ [TopologicalSpace E] in
/-- The left-sampling limit version of the stopped composite. -/
def compositeVersion (τ : Ω → WithTop ℝ≥0) (φ : E → ℝ) (Y : ℝ≥0 → Ω → E) (p : ℝ × Ω) : ℝ :=
  limUnder atTop fun n => leftSample n (preComposite τ φ Y) p

omit mΩ [TopologicalSpace E] in
/-- The version as a time-indexed density. -/
def alphaVersion (τ : Ω → WithTop ℝ≥0) (φ : E → ℝ) (Y : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : ℝ :=
  compositeVersion τ φ Y ((t : ℝ), ω)

omit mΩ [TopologicalSpace E] in
/-- The positive part of the version (for nonnegative densities). -/
def alphaVersionPos (τ : Ω → WithTop ℝ≥0) (φ : E → ℝ) (Y : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) :
    ℝ :=
  max (alphaVersion τ φ Y t ω) 0

theorem stronglyMeasurable_compositeVersion (𝓖 : Filtration ℝ≥0 mΩ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {φ : E → ℝ} (hφ : Continuous φ) {Y : ℝ≥0 → Ω → E}
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) :
    StronglyMeasurable[predictableSpace (toCF 𝓖)] (compositeVersion τ φ Y) :=
  @StronglyMeasurable.limUnder ℕ (ℝ × Ω) ℝ (predictableSpace (toCF 𝓖)) _ _ atTop _ _ _ _
    fun n => stronglyMeasurable_leftSample 𝓖 n (stronglyMeasurable_preComposite 𝓖 hτ hφ hY)

omit mΩ [TopologicalSpace E] in
theorem compositeVersion_of_nonpos (τ : Ω → WithTop ℝ≥0) (φ : E → ℝ) (Y : ℝ≥0 → Ω → E)
    {p : ℝ × Ω} (hp : p.1 ≤ 0) : compositeVersion τ φ Y p = 0 := by
  have he : (fun n => leftSample n (preComposite τ φ Y) p) = fun _ => 0 := by
    funext n; simp [leftSample, not_lt.2 hp]
  rw [compositeVersion, he]
  exact tendsto_const_nhds.limUnder_eq

omit mΩ in
/-- On a continuous path, the version is the stopped composite at every `s > 0`. -/
theorem compositeVersion_eq (τ : Ω → WithTop ℝ≥0) {φ : E → ℝ} (hφ : Continuous φ)
    {Y : ℝ≥0 → Ω → E} {p : ℝ × Ω} (hp : Continuous fun t => Y t p.2) (hs : 0 < p.1) :
    compositeVersion τ φ Y p = stoppedComposite τ φ Y p :=
  (tendsto_leftSample_stoppedComposite τ hφ hp hs).limUnder_eq

omit mΩ [TopologicalSpace E] in
theorem alphaVersion_toNNReal (τ : Ω → WithTop ℝ≥0) (φ : E → ℝ) (Y : ℝ≥0 → Ω → E) :
    (fun p : ℝ × Ω => alphaVersion τ φ Y p.1.toNNReal p.2) = compositeVersion τ φ Y := by
  funext p
  by_cases hp : 0 < p.1
  · simp only [alphaVersion, Real.coe_toNNReal _ hp.le]
  · have hp' : p.1 ≤ 0 := not_lt.1 hp
    rw [alphaVersion, compositeVersion_of_nonpos τ φ Y hp', compositeVersion_of_nonpos τ φ Y]
    simp [Real.toNNReal_of_nonpos hp']

variable (𝓖 : Filtration ℝ≥0 mΩ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) {φ : E → ℝ}
  (hφ : Continuous φ) {Y : ℝ≥0 → Ω → E} (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t))
include hτ hφ hY

/-- **Predictable version** (read through `s ↦ s.toNNReal`). -/
theorem stronglyMeasurable_alphaVersion :
    StronglyMeasurable[predictableSpace (toCF 𝓖)]
      fun p : ℝ × Ω => alphaVersion τ φ Y p.1.toNNReal p.2 := by
  rw [alphaVersion_toNNReal]
  exact stronglyMeasurable_compositeVersion 𝓖 hτ hφ hY

/-- **Jointly measurable version**, in the form of `IsL2Integrator.alpha_measurable`. -/
theorem measurable_alphaVersion :
    Measurable fun p : ℝ × Ω => alphaVersion τ φ Y p.1.toNNReal p.2 :=
  ((stronglyMeasurable_alphaVersion 𝓖 hτ hφ hY).mono (predictableSpace_le _)).measurable

theorem stronglyMeasurable_alphaVersionPos :
    StronglyMeasurable[predictableSpace (toCF 𝓖)]
      fun p : ℝ × Ω => alphaVersionPos τ φ Y p.1.toNNReal p.2 :=
  (continuous_id.max continuous_const).comp_stronglyMeasurable
    (stronglyMeasurable_alphaVersion 𝓖 hτ hφ hY)

theorem measurable_alphaVersionPos :
    Measurable fun p : ℝ × Ω => alphaVersionPos τ φ Y p.1.toNNReal p.2 :=
  ((stronglyMeasurable_alphaVersionPos 𝓖 hτ hφ hY).mono (predictableSpace_le _)).measurable

omit mΩ hτ hY in
/-- On every continuous path and every `t > 0`, `alphaVersion t ω = φ(Y_t ω) 1{t ≤ τ ω}`. -/
theorem alphaVersion_eq {ω : Ω} (hω : Continuous fun t => Y t ω) {t : ℝ≥0} (ht : 0 < t) :
    alphaVersion τ φ Y t ω = if (t : WithTop ℝ≥0) ≤ τ ω then φ (Y t ω) else 0 := by
  rw [alphaVersion, compositeVersion_eq τ hφ (p := ((t : ℝ), ω)) hω (by exact_mod_cast ht)]
  simp only [stoppedComposite, Real.toNNReal_coe]

omit mΩ hτ hY in
theorem alphaVersionPos_eq (hφ0 : ∀ y, 0 ≤ φ y) {ω : Ω} (hω : Continuous fun t => Y t ω)
    {t : ℝ≥0} (ht : 0 < t) :
    alphaVersionPos τ φ Y t ω = if (t : WithTop ℝ≥0) ≤ τ ω then φ (Y t ω) else 0 := by
  rw [alphaVersionPos, alphaVersion_eq hφ hω ht]
  refine max_eq_left ?_
  split_ifs
  · exact hφ0 _
  · exact le_rfl

omit mΩ hτ hY in
/-- Pathwise integrals of the version agree with those of the stopped composite. -/
theorem setIntegral_alphaVersion {ω : Ω} (hω : Continuous fun t => Y t ω) (a b : ℝ) (ha : 0 ≤ a) :
    ∫ r in Ioc a b, alphaVersion τ φ Y r.toNNReal ω =
      ∫ r in Ioc a b, stoppedComposite τ φ Y (r, ω) := by
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hr0 : 0 < r := ha.trans_lt hr.1
  rw [alphaVersion, Real.coe_toNNReal _ hr0.le]
  exact compositeVersion_eq τ hφ (p := (r, ω)) hω hr0

omit hτ hY in
theorem ae_alphaVersion_eq {Q : Measure Ω} (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t →
      alphaVersion τ φ Y t ω = if (t : WithTop ℝ≥0) ≤ τ ω then φ (Y t ω) else 0 := by
  filter_upwards [hYc] with ω hω t ht using alphaVersion_eq hφ hω ht

omit hτ hY in
/-- The version agrees `μ`-a.e. with the stopped composite, for every `μ ≪ dt ⊗ Q`. -/
theorem alphaVersion_ae_eq {Q : Measure Ω} [SFinite Q] {T : ℝ≥0} {μ : Measure (ℝ × Ω)}
    (hμ : μ ≪ timeProbMeasure T Q) (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω) :
    (fun p : ℝ × Ω => alphaVersion τ φ Y p.1.toNNReal p.2) =ᵐ[μ] stoppedComposite τ φ Y := by
  filter_upwards [hμ.ae_le (ae_timeProb_snd (T := T) hYc), hμ.ae_le (ae_timeProb_mem Q T)]
    with p hp hpos
  change (fun p : ℝ × Ω => alphaVersion τ φ Y p.1.toNNReal p.2) p = _
  rw [alphaVersion_toNNReal]
  exact compositeVersion_eq τ hφ hp hpos.1

end BlockBand.SourceProcess.Stochastic.GeneralIntegral

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral.IsL2Integrator
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {N α α' : ℝ≥0 → Ω → ℝ}

/-- **Changing the density on null sets**: the bracket only sees `α` through `∫_{(0,t]} α`. -/
theorem congr_alpha (h : IsL2Integrator Q 𝓖 N α) (h0 : ∀ t ω, 0 ≤ α' t ω)
    (hm : Measurable fun p : ℝ × Ω => α' p.1.toNNReal p.2)
    (heq : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → α' t ω = α t ω) : IsL2Integrator Q 𝓖 N α' where
  continuous := h.continuous
  memLp := h.memLp
  martingale := h.martingale
  alpha_nonneg := h0
  alpha_measurable := hm
  alpha_integrable := by
    filter_upwards [h.alpha_integrable, heq] with ω hω he t
    exact (hω t).congr_fun (fun r hr => (he _ (Real.toNNReal_pos.2 hr.1)).symm) measurableSet_Ioc
  bracket := by
    obtain ⟨K, hK, hKe⟩ := h.bracket
    refine ⟨K, hK, fun t => ?_⟩
    filter_upwards [hKe t, heq] with ω h1 he
    rw [h1, setIntegral_congr_fun measurableSet_Ioc
      (fun r hr => (he _ (Real.toNNReal_pos.2 hr.1)).symm)]

theorem bracketMeasure_congr [SFinite Q] (T : ℝ≥0)
    (heq : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → α' t ω = α t ω) :
    bracketMeasure Q α' T = bracketMeasure Q α T := by
  refine withDensity_congr_ae ?_
  filter_upwards [ae_timeProb_snd (T := T) heq, ae_timeProb_mem Q T] with p hp hpos
  rw [hp _ (Real.toNNReal_pos.2 hpos.1)]

end BlockBand.SourceProcess.Stochastic.GeneralIntegral.IsL2Integrator
