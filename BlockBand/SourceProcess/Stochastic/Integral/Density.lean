module
public import BlockBand.SourceProcess.Stochastic.Integral.Rectangle
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Rectangle density for continuous linear maps

Two continuous linear maps out of the predictable family `PredictableFamily T`
(`L²(dt ⊗ driverLaw μ)` on `(0,T]`, raw enlarged predictable σ-algebra, `κ` coordinates)
agree as soon as they agree on every single-direction bounded-horizon rectangle
`1_{(s,t]} H e_a` with `s < t ≤ T` and `H` an `F_s`-measurable `L²` coefficient.
This uses only the adopted density `enlargedPredictable_dense` of elementary rectangles.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open PredictableRectangle

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)
variable [DecidableEq κ]

/-- The single-direction rectangle class `1_{(s,t]} H e_a` in the predictable family. -/
abbrev rectFamily {s : ℝ≥0} (t : ℝ≥0) (a : κ) (H : DriverSample S κ → ℝ)
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    PredictableFamily (S := S) (κ := κ) (μ := μ) T :=
  PiLp.single 2 a (coefficientRectanglePredictableL2 enlargedPredictableFiltration T
    (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2)

omit [DecidableEq κ] in
/-- An elementary generator in one direction is either a bounded-horizon rectangle or zero. -/
theorem elementary_rectangle_or_zero {s t : ℝ≥0} {A : Set (DriverSample S κ)}
    (hA : MeasurableSet[commonWienerFiltration S κ s] A) (c : ℝ) :
    ∃ H : DriverSample S κ → ℝ, ∃ hH : Measurable[commonWienerFiltration S κ s] H,
      ∃ hHL2 : MemLp H 2 (driverLaw (κ := κ) μ),
      (s < min t T ∧ elementaryPredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (t := t) hA c = coefficientRectanglePredictableL2
          enlargedPredictableFiltration T (driverLaw (κ := κ) μ) (s := s) (t := min t T)
          H hH hHL2) ∨
      elementaryPredictableL2 enlargedPredictableFiltration T (driverLaw (κ := κ) μ)
        (t := t) hA c = 0 := by
  classical
  let H : DriverSample S κ → ℝ := A.indicator (fun _ => c)
  have hH : Measurable[commonWienerFiltration S κ s] H :=
    measurable_const.indicator hA
  have hHL2 : MemLp H 2 (driverLaw (κ := κ) μ) := by
    apply MemLp.of_bound (hH.mono ((commonWienerFiltration S κ).le s) le_rfl).aestronglyMeasurable ‖c‖
    exact Eventually.of_forall (fun x => by by_cases hx : x ∈ A <;> simp [H, hx])
  refine ⟨H, hH, hHL2, ?_⟩
  by_cases hst : s < min t T
  · left
    refine ⟨hst, ?_⟩
    apply (predictableL2_eq_iff_ae_eq _ _).2
    filter_upwards [nativeElementary_coeFn μ T (t := t) hA c,
      coefficientRectangle_class_coeFn μ T (s := s) (t := min t T) H hH hHL2,
      timeProbMeasure_horizon (κ := κ) μ T] with x hx hy hz
    rw [hx, hy]
    have hi' : x.1 ∈ Set.Ioc (s : ℝ) (min (t : ℝ) (T : ℝ)) ↔
        x.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) := by
      simp only [Set.mem_Ioc, le_min_iff]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hz.2⟩⟩
    by_cases ht : x.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) <;>
      by_cases ha : x.2 ∈ A <;>
      simp [elementaryPredictable, coefficientRectangle, H, Set.mem_prod, hi', ht, ha]
  · right
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

/-- **Rectangle extensionality.** Continuous linear maps on the predictable family that agree
on all single-direction rectangles `1_{(s,t]} H e_a` (`s < t ≤ T`) are equal. -/
theorem family_clm_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L R : PredictableFamily (S := S) (κ := κ) (μ := μ) T →L[ℝ] E)
    (h : ∀ (a : κ) (s t : ℝ≥0), s < t → t ≤ T → ∀ (H : DriverSample S κ → ℝ)
      (hH : Measurable[commonWienerFiltration S κ s] H)
      (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)),
      L (rectFamily μ T t a H hH hHL2) = R (rectFamily μ T t a H hH hHL2)) :
    L = R := by
  classical
  let D := L - R
  have hcoord (a : κ) (g : NativeScalarPredictable (κ := κ) μ T) :
      D (nativeCoordinateEmbedding μ T a g) = 0 := by
    let Da := D.comp (nativeCoordinateEmbedding μ T a).toContinuousLinearMap
    have hsub : (elementaryPredictableSubmodule enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) : Set (NativeScalarPredictable (κ := κ) μ T)) ⊆
        ((LinearMap.ker (Da : NativeScalarPredictable (κ := κ) μ T →ₗ[ℝ] E)) :
          Set (NativeScalarPredictable (κ := κ) μ T)) := by
      intro g hg
      refine Submodule.span_induction (p := fun g _ =>
        g ∈ LinearMap.ker (Da : NativeScalarPredictable (κ := κ) μ T →ₗ[ℝ] E)) ?_ ?_ ?_ ?_ hg
      · intro g hg
        rcases hg with ⟨s, t, A, hA, c, rfl⟩
        rcases elementary_rectangle_or_zero μ T (t := t) hA c with
          ⟨H, hH, hHL2, ⟨hst, he⟩ | he⟩
        · rw [LinearMap.mem_ker, he]
          change L (rectFamily μ T (min t T) a H hH hHL2) -
            R (rectFamily μ T (min t T) a H hH hHL2) = 0
          rw [h a s (min t T) hst (min_le_right _ _) H hH hHL2, sub_self]
        · rw [LinearMap.mem_ker, he, map_zero]
      · exact Submodule.zero_mem _
      · intro g g' _ _ hg hg'
        exact Submodule.add_mem _ hg hg'
      · intro c g _ hg
        exact Submodule.smul_mem _ c hg
    have hcl := closure_minimal hsub (ContinuousLinearMap.isClosed_ker Da)
    rw [(enlargedPredictable_dense (κ := κ) μ T).closure_eq] at hcl
    exact hcl (Set.mem_univ g)
  have hs (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
      (∑ a : κ, nativeCoordinateEmbedding μ T a (f a)) = f := by
    apply PiLp.ext
    intro b
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : κ => NativeScalarPredictable (κ := κ) μ T) b)
      (∑ a : κ, nativeCoordinateEmbedding μ T a (f a)) = f b
    rw [map_sum]
    rw [Finset.sum_eq_single b]
    · simp [nativeCoordinateEmbedding, PiLp.projₗ]
    · intro a _ hab
      simp [nativeCoordinateEmbedding, PiLp.projₗ, hab]
    · simp
  ext f
  have hD : D f = 0 := by
    rw [← hs f, map_sum]
    exact Finset.sum_eq_zero fun a _ => hcoord a (f a)
  exact sub_eq_zero.1 hD

end BlockBand.SourceProcess.Stochastic.Integral
