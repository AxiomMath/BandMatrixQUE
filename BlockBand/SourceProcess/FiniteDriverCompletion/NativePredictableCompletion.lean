module
public import BlockBand.SourceProcess.FiniteDriverCompletion.PredictableGridRelations

/-!
# The finite-grid Itô integral and its completion

The graph of the finite-grid stochastic sums, viewed as pairs (predictable class, `L²` integral),
is a linear relation on which the two norms agree. Its projection onto predictable classes is a
linear isomorphism onto the finite-grid classes `nativeFinitePredictable`, so the integral descends
to an isometry `nativeFiniteIntegral`, which extends to the closure `nativeClosedPredictable`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)

abbrev NativeRandomL2 := Lp ℝ 2 (driverLaw (κ := κ) μ)

/-- The graph of the finite-grid stochastic sums and their predictable classes. -/
def nativeGraph : Submodule ℝ
    (NativeRandomL2 (κ := κ) μ × PredictableFamily (S := S) (κ := κ) (μ := μ) T) :=
  Submodule.span ℝ {z | ∃ d : GridPresentation (κ := κ) μ T,
    z = (d.integralLp, d.predictableFamily)}

/-- Every element of the graph is zero or comes from a grid presentation. -/
theorem nativeGraph_zero_or_presentation {z : NativeRandomL2 (κ := κ) μ ×
    PredictableFamily (S := S) (κ := κ) (μ := μ) T} (hz : z ∈ nativeGraph (κ := κ) μ T) :
    z = 0 ∨ ∃ d : GridPresentation (κ := κ) μ T, z = (d.integralLp, d.predictableFamily) := by
  refine Submodule.span_induction (p := fun z _ =>
    z = 0 ∨ ∃ d : GridPresentation (κ := κ) μ T, z = (d.integralLp, d.predictableFamily))
    ?_ ?_ ?_ ?_ hz
  · intro z hz
    exact Or.inr hz
  · exact Or.inl rfl
  · intro x y _hx _hy hxr hyr
    rcases hxr with rfl | ⟨d, rfl⟩
    · simpa only [zero_add] using hyr
    rcases hyr with rfl | ⟨e, rfl⟩
    · exact Or.inr ⟨d, by simp⟩
    · exact Or.inr ⟨d.add e, by
        rw [d.integralLp_add e, d.predictableFamily_add e]
        rfl⟩
  · intro c x _hx hxr
    rcases hxr with rfl | ⟨d, rfl⟩
    · exact Or.inl (smul_zero c)
    · exact Or.inr ⟨d.smul c, by
        rw [d.integralLp_smul c, d.predictableFamily_smul c]
        rfl⟩

/-- On the graph, the `L²` norm of the integral equals the predictable energy norm. -/
theorem nativeGraph_norm (z : nativeGraph (κ := κ) μ T) : ‖z.1.1‖ = ‖z.1.2‖ := by
  rcases nativeGraph_zero_or_presentation μ T z.2 with hz | ⟨d, hd⟩
  · simp [hz]
  · rw [hd]
    exact d.predictableFamily_norm_eq_integralLp.symm

/-- The submodule of finite-grid predictable classes. -/
def nativeFinitePredictable : Submodule ℝ (PredictableFamily (S := S) (κ := κ) (μ := μ) T) :=
  (nativeGraph (κ := κ) μ T).map (LinearMap.snd ℝ
    (NativeRandomL2 (κ := κ) μ) (PredictableFamily (S := S) (κ := κ) (μ := μ) T))

def nativeGraphOutput : nativeGraph (κ := κ) μ T →ₗ[ℝ] NativeRandomL2 (κ := κ) μ where
  toFun z := z.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def nativeGraphPredictable : nativeGraph (κ := κ) μ T →ₗ[ℝ] nativeFinitePredictable (κ := κ) μ T where
  toFun z := ⟨z.1.2, ⟨z.1, z.2, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem nativeGraphPredictable_injective : Function.Injective (nativeGraphPredictable (κ := κ) μ T) := by
  intro u v huv
  have hp : u.1.2 = v.1.2 := congrArg Subtype.val huv
  apply Subtype.ext
  apply Prod.ext
  · apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hn := nativeGraph_norm μ T (u - v)
    change ‖u.1.1 - v.1.1‖ = ‖u.1.2 - v.1.2‖ at hn
    rw [hp, sub_self, norm_zero] at hn
    exact hn
  · exact hp

theorem nativeGraphPredictable_surjective : Function.Surjective (nativeGraphPredictable (κ := κ) μ T) := by
  intro f
  rcases f.2 with ⟨z, hz, he⟩
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  exact he

/-- The graph is linearly isomorphic to the finite-grid predictable classes. -/
def nativeGraphPredictableEquiv : nativeGraph (κ := κ) μ T ≃ₗ[ℝ] nativeFinitePredictable (κ := κ) μ T :=
  LinearEquiv.ofBijective (nativeGraphPredictable (κ := κ) μ T)
    ⟨nativeGraphPredictable_injective μ T, nativeGraphPredictable_surjective μ T⟩

/-- The finite-grid integral as a linear map on predictable classes. -/
def nativeFiniteIntegralLinear : nativeFinitePredictable (κ := κ) μ T →ₗ[ℝ] NativeRandomL2 (κ := κ) μ :=
  (nativeGraphOutput (κ := κ) μ T).comp (nativeGraphPredictableEquiv (κ := κ) μ T).symm.toLinearMap

theorem nativeFiniteIntegral_norm (f : nativeFinitePredictable (κ := κ) μ T) :
    ‖nativeFiniteIntegralLinear (κ := κ) μ T f‖ = ‖f‖ := by
  let z := (nativeGraphPredictableEquiv (κ := κ) μ T).symm f
  have hp : z.1.2 = f.1 := congrArg Subtype.val
    ((nativeGraphPredictableEquiv (κ := κ) μ T).apply_symm_apply f)
  change ‖z.1.1‖ = ‖f‖
  rw [nativeGraph_norm μ T z, hp]
  rfl

/-- The Itô isometry on finite-grid predictable classes. -/
def nativeFiniteIntegral : nativeFinitePredictable (κ := κ) μ T →ₗᵢ[ℝ] NativeRandomL2 (κ := κ) μ where
  toLinearMap := nativeFiniteIntegralLinear (κ := κ) μ T
  norm_map' := nativeFiniteIntegral_norm μ T

def nativePresentationClass (d : GridPresentation (κ := κ) μ T) : nativeFinitePredictable (κ := κ) μ T :=
  ⟨d.predictableFamily, ⟨(d.integralLp, d.predictableFamily), Submodule.subset_span ⟨d, rfl⟩, rfl⟩⟩

theorem nativeFiniteIntegral_presentation (d : GridPresentation (κ := κ) μ T) :
    nativeFiniteIntegral (κ := κ) μ T (nativePresentationClass μ T d) = d.integralLp := by
  let z : nativeGraph (κ := κ) μ T :=
    ⟨(d.integralLp, d.predictableFamily), Submodule.subset_span ⟨d, rfl⟩⟩
  have he : nativePresentationClass μ T d = nativeGraphPredictable (κ := κ) μ T z := rfl
  rw [he]
  change nativeGraphOutput μ T
    ((nativeGraphPredictableEquiv (κ := κ) μ T).symm
      ((nativeGraphPredictableEquiv (κ := κ) μ T) z)) = d.integralLp
  rw [(nativeGraphPredictableEquiv (κ := κ) μ T).symm_apply_apply]
  rfl

/-- The closure of the finite-grid predictable classes. -/
def nativeClosedPredictable := (nativeFinitePredictable (κ := κ) μ T).topologicalClosure

/-- The finite-grid classes embed isometrically into their closure. -/
def nativeClosureEmbedding : nativeFinitePredictable (κ := κ) μ T →ₗᵢ[ℝ] nativeClosedPredictable (κ := κ) μ T where
  toLinearMap := Submodule.inclusion (nativeFinitePredictable (κ := κ) μ T).le_topologicalClosure
  norm_map' _ := rfl

/-- The finite-grid classes are dense in their closure. -/
theorem nativeClosureEmbedding_dense : DenseRange (nativeClosureEmbedding (κ := κ) μ T) := by
  apply Metric.denseRange_iff.2
  intro f ε hε
  have hf : f.1 ∈ closure (nativeFinitePredictable (κ := κ) μ T :
      Set (PredictableFamily (S := S) (κ := κ) (μ := μ) T)) := f.2
  rcases Metric.mem_closure_iff.1 hf ε hε with ⟨g, hg, hd⟩
  exact ⟨⟨g, hg⟩, hd⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The terminal Itô integral on the closure of the finite-grid predictable classes. -/
def nativeClosedIntegral : nativeClosedPredictable (κ := κ) μ T →ₗᵢ[ℝ] NativeRandomL2 (κ := κ) μ :=
  @extendIntegralAlongDense
    (nativeFinitePredictable (κ := κ) μ T)
    (nativeFinitePredictable (κ := κ) μ T).seminormedAddCommGroup
    (nativeFinitePredictable (κ := κ) μ T).normedSpace
    (nativeClosedPredictable (κ := κ) μ T) (NativeRandomL2 (κ := κ) μ)
    (nativeClosedPredictable (κ := κ) μ T).normedAddCommGroup
    (nativeClosedPredictable (κ := κ) μ T).normedSpace
    inferInstance inferInstance inferInstance
    (nativeClosureEmbedding (κ := κ) μ T)
    (nativeClosureEmbedding_dense (κ := κ) μ T) (nativeFiniteIntegral (κ := κ) μ T)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem nativeClosedIntegral_finite (f : nativeFinitePredictable (κ := κ) μ T) :
    nativeClosedIntegral (κ := κ) μ T (nativeClosureEmbedding (κ := κ) μ T f) =
      nativeFiniteIntegral (κ := κ) μ T f :=
  by
    unfold nativeClosedIntegral
    exact @extendIntegralAlongDense_apply
      (nativeFinitePredictable (κ := κ) μ T)
      (nativeFinitePredictable (κ := κ) μ T).seminormedAddCommGroup
      (nativeFinitePredictable (κ := κ) μ T).normedSpace
      (nativeClosedPredictable (κ := κ) μ T) (NativeRandomL2 (κ := κ) μ)
      (nativeClosedPredictable (κ := κ) μ T).normedAddCommGroup
      (nativeClosedPredictable (κ := κ) μ T).normedSpace
      inferInstance inferInstance inferInstance
      (nativeClosureEmbedding (κ := κ) μ T)
      (nativeClosureEmbedding_dense (κ := κ) μ T) (nativeFiniteIntegral (κ := κ) μ T) f

theorem nativeClosedIntegral_presentation (d : GridPresentation (κ := κ) μ T) :
    nativeClosedIntegral (κ := κ) μ T
      (nativeClosureEmbedding (κ := κ) μ T (nativePresentationClass μ T d)) = d.integralLp := by
  rw [nativeClosedIntegral_finite, nativeFiniteIntegral_presentation]

end BlockBand.SourceProcess.FiniteDriverCompletion
