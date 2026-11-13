module
public import BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Tools
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Square-integrable continuous integrators on arbitrary filtered spaces

Setting for the general stochastic integral (used for the Gram martingale problem): an arbitrary
measurable space `(Ω, m₀)` with a measure `Q` (finite where stated), a raw filtration
`𝓖 : Filtration ℝ≥0 m₀` (no completeness, no usual conditions), a real process `N` and a
density `α ≥ 0`. `IsL2Integrator Q 𝓖 N α` asserts:

* the process `N` has `Q`-a.s. continuous paths, `N t ∈ L²(Q)` for all `t`, and `N` has a
  `𝓖`-martingale modification `M` (`M t = N t` a.s. for every `t`);
* `α` is jointly measurable in `(s, ω)` on `ℝ × Ω` (through `s ↦ s.toNNReal`), nonnegative,
  and a.s. integrable on every `(0, t]`;
* `N_t² - ∫_{(0,t]} α_s ds` has a `𝓖`-martingale modification (bracket `d⟨N⟩ = α dt`).

No progressive measurability of `α` is required: a.e. `𝓖_t`-measurability of
`∫_{(0,t]} α` follows from the bracket hypothesis.

The integrand measure on `ℝ × Ω` for the horizon `T` is
`bracketMeasure Q α T = (dt|_{(0,T]} ⊗ Q).withDensity α`, i.e. `ν_T = α(s,ω) ds ⊗ Q` on
`(0,T] × Ω`. `Rect 𝓖 T` are the predictable rectangles `(s,t] × A` with `s ≤ t ≤ T` and
`A ∈ 𝓖_s`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The raw filtration seen as a `ContinuousFiltration` (for the predictable σ-algebra). -/
def toCF (𝓖 : Filtration ℝ≥0 mΩ) : ContinuousFiltration Ω :=
  ⟨fun t => 𝓖 t, fun _ _ h => 𝓖.mono h, 𝓖.le⟩

/-- Pathwise bracket increment `∫_{(a,b]} α_r dr`. -/
def bracketIntegral (α : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in Ioc (a : ℝ) b, α r.toNNReal ω

/-- Continuous square-integrable martingale integrator with absolutely continuous bracket
`d⟨N⟩_t = α_t dt`, in modification form on a raw filtration. -/
structure IsL2Integrator (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) (N α : ℝ≥0 → Ω → ℝ) :
    Prop where
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => N t ω
  memLp : ∀ t, MemLp (N t) 2 Q
  martingale : ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 Q ∧ ∀ t, M t =ᵐ[Q] N t
  alpha_nonneg : ∀ t ω, 0 ≤ α t ω
  alpha_measurable : Measurable fun p : ℝ × Ω => α p.1.toNNReal p.2
  alpha_integrable : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun r : ℝ => α r.toNNReal ω) (Ioc 0 t)
  bracket : ∃ K : ℝ≥0 → Ω → ℝ, Martingale K 𝓖 Q ∧
    ∀ t, K t =ᵐ[Q] fun ω => N t ω ^ 2 - ∫ r in Ioc (0 : ℝ) t, α r.toNNReal ω

/-- The integrand measure `ν_T = α(s,ω) ds ⊗ Q` on `(0,T] × Ω`. -/
def bracketMeasure (Q : Measure Ω) (α : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Measure (ℝ × Ω) :=
  (timeProbMeasure T Q).withDensity fun p => ENNReal.ofReal (α p.1.toNNReal p.2)

/-- Predictable rectangles `(s,t] × A`, `s ≤ t ≤ T`, `A ∈ 𝓖_s`. -/
structure Rect (𝓖 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) where
  s : ℝ≥0
  t : ℝ≥0
  A : Set Ω
  hst : s ≤ t
  htT : t ≤ T
  hA : MeasurableSet[𝓖 s] A

/-- The subset `(s,t] × A` of `ℝ × Ω`. -/
def Rect.set {𝓖 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} (r : Rect 𝓖 T) : Set (ℝ × Ω) :=
  Ioc (r.s : ℝ) r.t ×ˢ r.A

theorem Rect.measurableSet_pred {𝓖 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} (r : Rect 𝓖 T) :
    MeasurableSet[predictableSpace (toCF 𝓖)] r.set :=
  measurableSet_predictableRectangle (toCF 𝓖) (t := r.t) r.hA

theorem Rect.measurableSet {𝓖 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} (r : Rect 𝓖 T) :
    MeasurableSet r.set :=
  predictableSpace_le _ _ r.measurableSet_pred

namespace IsL2Integrator

variable {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {N α : ℝ≥0 → Ω → ℝ}

/-- The chosen martingale modification of `N`. -/
def mart (h : IsL2Integrator Q 𝓖 N α) : ℝ≥0 → Ω → ℝ := h.martingale.choose

theorem mart_martingale (h : IsL2Integrator Q 𝓖 N α) : Martingale h.mart 𝓖 Q :=
  h.martingale.choose_spec.1

theorem mart_ae (h : IsL2Integrator Q 𝓖 N α) (t : ℝ≥0) : h.mart t =ᵐ[Q] N t :=
  h.martingale.choose_spec.2 t

theorem mart_memLp (h : IsL2Integrator Q 𝓖 N α) (t : ℝ≥0) : MemLp (h.mart t) 2 Q :=
  (h.memLp t).ae_eq (h.mart_ae t).symm

theorem mart_sm (h : IsL2Integrator Q 𝓖 N α) (t : ℝ≥0) :
    StronglyMeasurable[𝓖 t] (h.mart t) :=
  h.mart_martingale.stronglyMeasurable t

/-- The chosen martingale modification of `N² - ∫α`. -/
def comp (h : IsL2Integrator Q 𝓖 N α) : ℝ≥0 → Ω → ℝ := h.bracket.choose

theorem comp_martingale (h : IsL2Integrator Q 𝓖 N α) : Martingale h.comp 𝓖 Q :=
  h.bracket.choose_spec.1

/-- `∫_{(0,t]} α = M_t² - K_t` a.s. -/
theorem bracketIntegral_zero_ae (h : IsL2Integrator Q 𝓖 N α) (t : ℝ≥0) :
    bracketIntegral α 0 t =ᵐ[Q] fun ω => h.mart t ω ^ 2 - h.comp t ω := by
  filter_upwards [h.bracket.choose_spec.2 t, h.mart_ae t] with ω h1 h2
  change h.comp t ω = _ at h1
  rw [h1, h2]
  simp [bracketIntegral]

theorem integrable_bracketIntegral_zero (h : IsL2Integrator Q 𝓖 N α) (t : ℝ≥0) :
    Integrable (bracketIntegral α 0 t) Q :=
  (((h.mart_memLp t).integrable_sq).sub (h.comp_martingale.integrable t)).congr
    (h.bracketIntegral_zero_ae t).symm

theorem aesm_bracketIntegral_zero (h : IsL2Integrator Q 𝓖 N α) (t : ℝ≥0) :
    AEStronglyMeasurable[𝓖 t] (bracketIntegral α 0 t) Q :=
  (((h.mart_sm t).pow 2).sub (h.comp_martingale.stronglyMeasurable t)).aestronglyMeasurable.congr
    (h.bracketIntegral_zero_ae t).symm

/-- Additivity of the bracket integral: `∫_{(a,b]} α = ∫_{(0,b]} α - ∫_{(0,a]} α` a.s. -/
theorem bracketIntegral_sub (h : IsL2Integrator Q 𝓖 N α) {a b : ℝ≥0} (hab : a ≤ b) :
    bracketIntegral α a b =ᵐ[Q] fun ω => bracketIntegral α 0 b ω - bracketIntegral α 0 a ω := by
  filter_upwards [h.alpha_integrable] with ω hω
  have hu : Ioc (0 : ℝ) a ∪ Ioc (a : ℝ) b = Ioc (0 : ℝ) b :=
    Ioc_union_Ioc_eq_Ioc a.coe_nonneg (NNReal.coe_le_coe.2 hab)
  have hint : ∫ r in Ioc (0 : ℝ) b, α r.toNNReal ω =
      (∫ r in Ioc (0 : ℝ) a, α r.toNNReal ω) + ∫ r in Ioc (a : ℝ) b, α r.toNNReal ω := by
    rw [← hu]
    refine setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      ((hω a)) ((hω b).mono_set ?_)
    rw [← hu]; exact subset_union_right
  simp only [bracketIntegral, NNReal.coe_zero] at hint ⊢
  linarith

theorem integrable_bracketIntegral (h : IsL2Integrator Q 𝓖 N α) {a b : ℝ≥0} (hab : a ≤ b) :
    Integrable (bracketIntegral α a b) Q :=
  ((h.integrable_bracketIntegral_zero b).sub (h.integrable_bracketIntegral_zero a)).congr
    (h.bracketIntegral_sub hab).symm

theorem aesm_bracketIntegral (h : IsL2Integrator Q 𝓖 N α) {a b : ℝ≥0} (hab : a ≤ b) :
    AEStronglyMeasurable[𝓖 b] (bracketIntegral α a b) Q :=
  ((h.aesm_bracketIntegral_zero b).sub
    ((h.aesm_bracketIntegral_zero a).mono (𝓖.mono hab))).congr (h.bracketIntegral_sub hab).symm

theorem bracketIntegral_nonneg (h : IsL2Integrator Q 𝓖 N α) (a b : ℝ≥0) (ω : Ω) :
    0 ≤ bracketIntegral α a b ω :=
  setIntegral_nonneg measurableSet_Ioc fun _ _ => h.alpha_nonneg _ _

/-- The bracket measure of a rectangle: `ν_T((a,b] × D) = E[1_D ∫_{(a,b]} α]`. -/
theorem bracketMeasure_rect (h : IsL2Integrator Q 𝓖 N α) {T a b : ℝ≥0} (hab : a ≤ b)
    (hbT : b ≤ T) {D : Set Ω} (hD : MeasurableSet D) [SFinite Q] :
    bracketMeasure Q α T (Ioc (a : ℝ) b ×ˢ D) =
      ENNReal.ofReal (∫ ω in D, bracketIntegral α a b ω ∂Q) := by
  have hm : Measurable fun p : ℝ × Ω => ENNReal.ofReal (α p.1.toNNReal p.2) :=
    ENNReal.measurable_ofReal.comp h.alpha_measurable
  rw [bracketMeasure, withDensity_apply _ (measurableSet_Ioc.prod hD), timeProbMeasure,
    ← Measure.prod_restrict, lintegral_prod_symm _ hm.aemeasurable,
    Measure.restrict_restrict measurableSet_Ioc,
    Ioc_inter_Ioc, max_eq_left a.coe_nonneg, min_eq_left (NNReal.coe_le_coe.2 hbT)]
  have hin : ∀ᵐ ω ∂Q.restrict D, ∫⁻ r in Ioc (a : ℝ) b, ENNReal.ofReal (α r.toNNReal ω) =
      ENNReal.ofReal (bracketIntegral α a b ω) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [h.alpha_integrable] with ω hω
    rw [bracketIntegral, ofReal_integral_eq_lintegral_ofReal
      ((hω b).mono_set (Ioc_subset_Ioc_left a.coe_nonneg))
      (Eventually.of_forall fun r => h.alpha_nonneg _ _)]
  rw [lintegral_congr_ae hin, ← ofReal_integral_eq_lintegral_ofReal
    (h.integrable_bracketIntegral hab).integrableOn
    (Eventually.of_forall fun ω => h.bracketIntegral_nonneg a b ω)]

theorem bracketMeasure_compl_null (Q : Measure Ω) [SFinite Q] (α : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    bracketMeasure Q α T (Ioc (0 : ℝ) T ×ˢ (univ : Set Ω))ᶜ = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [timeProbMeasure, Measure.measure_prod_null (measurableSet_Ioc.prod MeasurableSet.univ).compl]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have h0 : Prod.mk x ⁻¹' (Ioc (0 : ℝ) T ×ˢ (univ : Set Ω))ᶜ = ∅ := by
    ext ω; simp [hx]
  simp [h0]

/-- `ν_T` is concentrated on times in `(0,T]`. -/
theorem bracketMeasure_ae_mem (Q : Measure Ω) [SFinite Q] (α : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    ∀ᵐ x ∂bracketMeasure Q α T, x.1 ∈ Ioc (0 : ℝ) T := by
  have := bracketMeasure_compl_null Q α T
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) this
  simp_all

theorem isFiniteMeasure_bracketMeasure (h : IsL2Integrator Q 𝓖 N α) [SFinite Q] (T : ℝ≥0) :
    IsFiniteMeasure (bracketMeasure Q α T) := by
  refine ⟨?_⟩
  have h1 := h.bracketMeasure_rect (zero_le : (0 : ℝ≥0) ≤ T) le_rfl MeasurableSet.univ
  have h2 := bracketMeasure_compl_null Q α T
  calc bracketMeasure Q α T univ
      ≤ bracketMeasure Q α T (Ioc (0 : ℝ) T ×ˢ (univ : Set Ω)) +
        bracketMeasure Q α T (Ioc (0 : ℝ) T ×ˢ (univ : Set Ω))ᶜ := by
        rw [← union_compl_self (Ioc (0 : ℝ) T ×ˢ (univ : Set Ω))]
        exact measure_union_le _ _
    _ < ⊤ := by
        rw [h2, add_zero]
        push_cast at h1
        rw [h1]; exact ENNReal.ofReal_lt_top

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
