module
public import BlockBand.Model.Construction.MarkedStateTopologyConsequences
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Rotation of marked configurations

Rotation of the torus marks of a marked point configuration: the rotation of a mass profile is
jointly continuous in the angle and the profile, and induces a global rotation of marked point
measures that leaves the spectral projection unchanged.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Set TopologicalSpace Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

def massProfileRotation (a : Torus) (μ : MassProfile) : MassProfile :=
  μ.map (Homeomorph.addLeft a)

theorem massProfileRotation_zero (μ : MassProfile) : massProfileRotation 0 μ = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (Homeomorph.addLeft (0 : Torus)) (μ : Measure Torus) = _
  have he : (Homeomorph.addLeft (0 : Torus) : Torus → Torus) = id := by funext r; simp
  rw [he, Measure.map_id]

theorem massProfileRotation_add (a b : Torus) (μ : MassProfile) :
    massProfileRotation a (massProfileRotation b μ) = massProfileRotation (a+b) μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (Homeomorph.addLeft a) (Measure.map (Homeomorph.addLeft b) (μ : Measure Torus)) = _
  rw [Measure.map_map (Homeomorph.addLeft a).continuous.measurable
    (Homeomorph.addLeft b).continuous.measurable]
  congr 1
  funext r
  simp [add_assoc]

theorem continuous_massProfileRotation (a : Torus) : Continuous (massProfileRotation a) :=
  ProbabilityMeasure.continuous_map (Homeomorph.addLeft a).continuous

theorem measurable_massProfileRotation (a : Torus) : Measurable (massProfileRotation a) := by
  have := massProfile_borelSpace
  exact (continuous_massProfileRotation a).measurable

/-- Uniform compact-test error for a single probability profile. -/
theorem massProfile_integral_dist_le (μ : MassProfile) (f g : C(Torus, ℝ)) :
    |(∫ r, f r ∂(μ : Measure Torus)) - ∫ r, g r ∂(μ : Measure Torus)| ≤ dist f g := by
  rw [← integral_sub (f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace f)) (g.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace g))]
  have h := norm_integral_le_of_norm_le_const
    (μ := (μ : Measure Torus)) (f := fun r => f r-g r)
    (ae_of_all _ (fun r => by
      simpa only [Real.norm_eq_abs, Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) r))
  simpa [Real.norm_eq_abs] using h

/-- Joint integration is continuous because profile masses are exactly one. -/
theorem continuous_massProfile_integral : Continuous (fun q : C(Torus, ℝ) × MassProfile =>
    ∫ r, q.1 r ∂(q.2 : Measure Torus)) := by
  rw [continuous_iff_continuousAt]
  intro q
  rw [Metric.continuousAt_iff']
  intro ε hε
  have h1 : ∀ᶠ p : C(Torus, ℝ) × MassProfile in 𝓝 q, dist p.1 q.1 < ε/2 :=
    (continuous_fst.tendsto q).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have h2 : ∀ᶠ p : C(Torus, ℝ) × MassProfile in 𝓝 q,
      |(∫ r, q.1 r ∂(p.2 : Measure Torus)) - ∫ r, q.1 r ∂(q.2 : Measure Torus)| < ε/2 := by
    have h := ((ProbabilityMeasure.continuous_integral_continuousMap q.1).comp continuous_snd).tendsto q
    have hn := h.eventually (Metric.ball_mem_nhds _ (half_pos hε))
    simpa only [Metric.mem_ball, Real.dist_eq, Function.comp_apply] using hn
  filter_upwards [h1,h2] with p hp hnear
  have he := massProfile_integral_dist_le p.2 p.1 q.1
  have hs := abs_add_le
    ((∫ r, p.1 r ∂(p.2 : Measure Torus)) - ∫ r, q.1 r ∂(p.2 : Measure Torus))
    ((∫ r, q.1 r ∂(p.2 : Measure Torus)) - ∫ r, q.1 r ∂(q.2 : Measure Torus))
  rw [Real.dist_eq]
  have hid : (∫ r, p.1 r ∂(p.2 : Measure Torus)) - ∫ r, q.1 r ∂(q.2 : Measure Torus) =
      ((∫ r, p.1 r ∂(p.2 : Measure Torus)) - ∫ r, q.1 r ∂(p.2 : Measure Torus)) +
      ((∫ r, q.1 r ∂(p.2 : Measure Torus)) - ∫ r, q.1 r ∂(q.2 : Measure Torus)) := by ring
  rw [hid]
  linarith

/-- Joint continuity of the rotation in the angle and the profile. -/
theorem continuous_massProfileRotation_joint :
    Continuous (fun q : Torus × MassProfile => massProfileRotation q.1 q.2) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral]
  intro f
  let g : C(Torus, C(Torus, ℝ)) :=
    (⟨fun ar : Torus × Torus => f (ar.1+ar.2),
      f.continuous.comp (continuous_fst.add continuous_snd)⟩ : C(Torus × Torus, ℝ)).curry
  have h := continuous_massProfile_integral.comp ((g.continuous.comp continuous_fst).prodMk continuous_snd)
  convert h using 1
  funext q
  exact integral_map (Homeomorph.addLeft q.1).continuous.measurable.aemeasurable
    f.continuous.aestronglyMeasurable

theorem measurable_massProfileRotation_joint :
    Measurable (fun q : Torus × MassProfile => massProfileRotation q.1 q.2) := by
  have := massProfile_borelSpace
  exact continuous_massProfileRotation_joint.measurable

def massProfileRotationHomeomorph (a : Torus) : MassProfile ≃ₜ MassProfile where
  toFun := massProfileRotation a
  invFun := massProfileRotation (-a)
  left_inv μ := by rw [massProfileRotation_add, neg_add_cancel, massProfileRotation_zero]
  right_inv μ := by rw [massProfileRotation_add, add_neg_cancel, massProfileRotation_zero]
  continuous_toFun := continuous_massProfileRotation a
  continuous_invFun := continuous_massProfileRotation (-a)

def markedLocationRotation (a : Torus) (z : MarkedSpectralSpace) : MarkedSpectralSpace :=
  (z.1, massProfileRotation a z.2)

theorem continuous_markedLocationRotation_joint :
    Continuous (fun q : Torus × MarkedSpectralSpace => markedLocationRotation q.1 q.2) :=
  continuous_snd.fst.prodMk (continuous_massProfileRotation_joint.comp
    (continuous_fst.prodMk continuous_snd.snd))

def markedLocationRotationHomeomorph (a : Torus) : MarkedSpectralSpace ≃ₜ MarkedSpectralSpace :=
  Homeomorph.prodCongr (Homeomorph.refl ℝ) (massProfileRotationHomeomorph a)

theorem measurable_markedLocationRotation (a : Torus) : Measurable (markedLocationRotation a) :=
  measurable_fst.prodMk ((measurable_massProfileRotation a).comp measurable_snd)

theorem measurable_markedLocationRotationHomeomorph_symm (a : Torus) :
    Measurable (markedLocationRotationHomeomorph a).symm :=
  measurable_fst.prodMk ((measurable_massProfileRotation (-a)).comp measurable_snd)

/-- Full-measure rotation, with its unchanged spectral projection proved. -/
def globalMarkedRotation (a : Torus) (ξ : MarkedPointMeasure) : MarkedPointMeasure where
  marked := vagueHomeomorphPushforward (markedLocationRotationHomeomorph a)
    (measurable_markedLocationRotation a) (measurable_markedLocationRotationHomeomorph_symm a) ξ.marked
  spectral := ξ.spectral
  spectral_eq := by
    rw [ξ.spectral_eq]
    change Measure.map Prod.fst ξ.marked.measure = Measure.map Prod.fst
      (Measure.map (markedLocationRotation a) ξ.marked.measure)
    rw [Measure.map_map measurable_fst (measurable_markedLocationRotation a)]
    rfl

theorem globalMarkedRotation_measure (a : Torus) (ξ : MarkedPointMeasure) :
    (globalMarkedRotation a ξ).marked.measure = Measure.map (markedLocationRotation a) ξ.marked.measure := rfl

theorem globalMarkedRotation_apply (a : Torus) (ξ : MarkedPointMeasure) (A : Set MarkedSpectralSpace) :
    (globalMarkedRotation a ξ).marked.measure A = ξ.marked.measure ((markedLocationRotation a) ⁻¹' A) :=
  vagueHomeomorphPushforward_apply _ _ _ ξ.marked A

theorem globalMarkedRotation_zero (ξ : MarkedPointMeasure) : globalMarkedRotation 0 ξ = ξ := by
  apply markedPointMeasure_eq_of_marked_measure_eq
  rw [globalMarkedRotation_measure]
  have he : markedLocationRotation 0 = id := by
    funext z
    exact Prod.ext rfl (massProfileRotation_zero z.2)
  rw [he, Measure.map_id]

theorem globalMarkedRotation_add (a b : Torus) (ξ : MarkedPointMeasure) :
    globalMarkedRotation a (globalMarkedRotation b ξ) = globalMarkedRotation (a+b) ξ := by
  apply markedPointMeasure_eq_of_marked_measure_eq
  simp only [globalMarkedRotation_measure]
  rw [Measure.map_map (measurable_markedLocationRotation a) (measurable_markedLocationRotation b)]
  congr 1
  funext z
  exact Prod.ext rfl (massProfileRotation_add a b z.2)

theorem globalMarkedRotation_inverse (a : Torus) (ξ : MarkedPointMeasure) :
    globalMarkedRotation (-a) (globalMarkedRotation a ξ) = ξ := by
  rw [globalMarkedRotation_add, neg_add_cancel, globalMarkedRotation_zero]

theorem globalMarkedRotation_spectral (a : Torus) (ξ : MarkedPointMeasure) :
    (globalMarkedRotation a ξ).spectral = ξ.spectral := rfl

theorem continuous_globalMarkedRotation (a : Torus) : Continuous (globalMarkedRotation a) := by
  rw [continuous_induced_rng]
  exact (continuous_vagueHomeomorphPushforward (markedLocationRotationHomeomorph a)
    (measurable_markedLocationRotation a) (measurable_markedLocationRotationHomeomorph_symm a)).comp continuous_induced_dom

theorem measurable_globalMarkedRotation (a : Torus) : Measurable (globalMarkedRotation a) :=
  (continuous_globalMarkedRotation a).measurable

theorem globalMarkedRotation_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (a : Torus) (ξ : MarkedPointMeasure) (f : MarkedSpectralSpace → E) :
    (∫ z, f z ∂(globalMarkedRotation a ξ).marked.measure) =
      ∫ z, f (markedLocationRotation a z) ∂ξ.marked.measure :=
  vagueHomeomorphPushforward_integral _ _ _ ξ.marked f

def globalMarkedRotationHomeomorph (a : Torus) : MarkedPointMeasure ≃ₜ MarkedPointMeasure where
  toFun := globalMarkedRotation a
  invFun := globalMarkedRotation (-a)
  left_inv := globalMarkedRotation_inverse a
  right_inv ξ := by simpa only [neg_neg] using globalMarkedRotation_inverse (-a) ξ
  continuous_toFun := continuous_globalMarkedRotation a
  continuous_invFun := continuous_globalMarkedRotation (-a)

def globalMarkedRotationLaw (a : Torus) (ν : ProbabilityMeasure MarkedPointMeasure) :
    ProbabilityMeasure MarkedPointMeasure := ν.map (globalMarkedRotation a)

theorem continuous_globalMarkedRotationLaw (a : Torus) : Continuous (globalMarkedRotationLaw a) :=
  ProbabilityMeasure.continuous_map (continuous_globalMarkedRotation a)

end BlockBand.Model.Construction
