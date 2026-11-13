module
public import BlockBand.SourceProcess.FiniteDriverCompletion.FullPredictableIntegral

/-!
# Density of the finite-grid predictable families

Elementary predictable rectangles, and hence all predictable `L²` functions, lie in the closure of
the finite-grid classes; the closure `nativeClosedPredictable` is the whole space.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open PredictableRectangle
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)
variable [DecidableEq κ]

omit [DecidableEq κ] in

/-- The class of an elementary predictable integrand `elementaryPredictable s t A c` in
`NativeScalarPredictable` has `elementaryPredictable s t A c` as an a.e. representative. -/
theorem nativeElementary_coeFn {s t : ℝ≥0} {A : Set (DriverSample S κ)}
    (hA : MeasurableSet[commonWienerFiltration S κ s] A) (c : ℝ) :
    (((elementaryPredictableL2 enlargedPredictableFiltration T (driverLaw (κ := κ) μ)
      (t := t) hA c : NativeScalarPredictable (κ := κ) μ T) :
      Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) :
      ℝ × DriverSample S κ → ℝ) =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)]
      elementaryPredictable s t A c := by
  have hm : MemLp (elementaryPredictable s t A c) 2
      (timeProbMeasure T (driverLaw (κ := κ) μ)) := by
    apply MemLp.of_bound
      ((stronglyMeasurable_elementaryPredictable enlargedPredictableFiltration hA c).mono
        (predictableSpace_le enlargedPredictableFiltration)).aestronglyMeasurable ‖c‖
    exact Eventually.of_forall (fun x => by
      by_cases hx : x ∈ Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A <;>
        simp [elementaryPredictable, hx])
  exact hm.coeFn_toLp

/-- Every elementary predictable rectangle, clipped to the horizon, lies in the closure. -/
theorem elementary_single_mem_nativeClosed {s t : ℝ≥0} {A : Set (DriverSample S κ)}
    (hA : MeasurableSet[commonWienerFiltration S κ s] A) (c : ℝ) (a : κ) :
    nativeCoordinateEmbedding μ T a
      (elementaryPredictableL2 enlargedPredictableFiltration T (driverLaw (κ := κ) μ)
        (t := t) hA c) ∈ nativeClosedPredictable (κ := κ) μ T := by
  classical
  let H : DriverSample S κ → ℝ := A.indicator (fun _ => c)
  have hH : Measurable[commonWienerFiltration S κ s] H :=
    measurable_const.indicator hA
  have hHL2 : MemLp H 2 (driverLaw (κ := κ) μ) := by
    apply MemLp.of_bound (hH.mono ((commonWienerFiltration S κ).le s) le_rfl).aestronglyMeasurable ‖c‖
    exact Eventually.of_forall (fun x => by by_cases hx : x ∈ A <;> simp [H, hx])
  by_cases hst : s < min t T
  · let r := coefficientRectanglePredictableL2 enlargedPredictableFiltration T
      (driverLaw (κ := κ) μ) (s := s) (t := min t T) H hH hHL2
    have he : elementaryPredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (t := t) hA c = r := by
      apply (predictableL2_eq_iff_ae_eq _ _).2
      filter_upwards [nativeElementary_coeFn μ T (t := t) hA c,
        coefficientRectangle_class_coeFn μ T (s := s) (t := min t T) H hH hHL2,
        timeProbMeasure_horizon (κ := κ) μ T] with x hx hy hz
      rw [hx, hy]
      have hi : x.1 ∈ Set.Ioc (s : ℝ) ((min t T : ℝ≥0) : ℝ) ↔
          x.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) := by
        simp only [Set.mem_Ioc, NNReal.coe_min, le_min_iff]
        exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hz.2⟩⟩
      have hi' : x.1 ∈ Set.Ioc (s : ℝ) (min (t : ℝ) (T : ℝ)) ↔
          x.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) := by
        simpa only [NNReal.coe_min] using hi
      by_cases ht : x.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) <;>
        by_cases ha : x.2 ∈ A <;>
        simp [elementaryPredictable, coefficientRectangle, H, Set.mem_prod, hi', ht, ha]
    rw [he]
    exact (nativeFinitePredictable (κ := κ) μ T).le_topologicalClosure
      (rectangle_single_mem_nativeFinite μ T s (min t T) hst (min_le_right _ _) a H hH hHL2)
  · have he : elementaryPredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (t := t) hA c = 0 := by
      apply (predictableL2_eq_iff_ae_eq _ _).2
      filter_upwards [nativeElementary_coeFn μ T (t := t) hA c,
        timeProbMeasure_horizon (κ := κ) μ T,
        Lp.coeFn_zero ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))] with x hx hz hzero
      have hi : x.1 ∉ Set.Ioc (s : ℝ) (t : ℝ) := by
        intro hi
        apply hst
        exact_mod_cast (hi.1.trans_le (le_min hi.2 hz.2))
      rw [hx]
      change elementaryPredictable s t A c x =
        ((0 : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ) x
      rw [hzero]
      simp [elementaryPredictable, Set.mem_prod, hi]
    rw [he, map_zero]
    exact (nativeClosedPredictable (κ := κ) μ T).zero_mem

/-- Every predictable function in one noise direction lies in the closure. -/
theorem coordinate_mem_nativeClosed (a : κ) (f : NativeScalarPredictable (κ := κ) μ T) :
    nativeCoordinateEmbedding μ T a f ∈ nativeClosedPredictable (κ := κ) μ T := by
  let e := nativeCoordinateEmbedding μ T a
  have hc : IsClosed {g : NativeScalarPredictable (κ := κ) μ T |
      e g ∈ nativeClosedPredictable (κ := κ) μ T} :=
    (nativeFinitePredictable (κ := κ) μ T).isClosed_topologicalClosure.preimage e.continuous
  have hsub : (elementaryPredictableSubmodule enlargedPredictableFiltration T
      (driverLaw (κ := κ) μ) : Set (NativeScalarPredictable (κ := κ) μ T)) ⊆
      {g | e g ∈ nativeClosedPredictable (κ := κ) μ T} := by
    intro g hg
    refine Submodule.span_induction (p := fun g _ => e g ∈ nativeClosedPredictable (κ := κ) μ T)
      ?_ ?_ ?_ ?_ hg
    · intro g hg
      rcases hg with ⟨s, t, A, hA, c, rfl⟩
      exact elementary_single_mem_nativeClosed μ T hA c a
    · simpa only [map_zero] using (nativeClosedPredictable (κ := κ) μ T).zero_mem
    · intro g h _ _ hg hh
      simpa only [map_add] using (nativeClosedPredictable (κ := κ) μ T).add_mem hg hh
    · intro c g _ hg
      simpa only [map_smul] using (nativeClosedPredictable (κ := κ) μ T).smul_mem c hg
  have hcl := hc.closure_subset_iff.mpr hsub
  rw [(enlargedPredictable_dense (κ := κ) μ T).closure_eq] at hcl
  exact hcl (Set.mem_univ f)

/-- The predictable closure is the whole space of predictable families. -/
theorem nativeClosedPredictable_eq_top : nativeClosedPredictable (κ := κ) μ T = ⊤ := by
  classical
  apply top_unique
  intro f _
  have hs : (∑ a : κ, nativeCoordinateEmbedding μ T a (f a)) = f := by
    apply PiLp.ext
    intro b
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : κ => NativeScalarPredictable (κ := κ) μ T) b) (∑ a : κ, nativeCoordinateEmbedding μ T a (f a)) = f b
    rw [map_sum]
    rw [Finset.sum_eq_single b]
    · simp [nativeCoordinateEmbedding, PiLp.projₗ]
    · intro a _ hab
      simp [nativeCoordinateEmbedding, PiLp.projₗ, hab]
    · simp
  rw [← hs]
  exact (nativeClosedPredictable (κ := κ) μ T).sum_mem
    (fun a _ => coordinate_mem_nativeClosed μ T a (f a))

end BlockBand.SourceProcess.FiniteDriverCompletion
