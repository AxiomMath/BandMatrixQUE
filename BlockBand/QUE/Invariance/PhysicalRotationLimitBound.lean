module
public import BlockBand.QUE.Invariance.PhysicalRotationLimitCompact
public import BlockBand.Counting.PhysicalMarkedTightness

/-!
# Laplace rotation error of the canonical marked law

For a grid approximation of a rotation, the Laplace functional of the canonical physical marked
law changes by at most the rotation error of the test times the expected local count, and the
local count has a finite first moment by the PSSS source contract
(`canonicalPhysicalMarkedLaw_laplace_rotation_error`).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Invariance
open MeasureTheory Filter BlockBand.Model.Construction BlockBand.Counting
open scoped Topology ENNReal

/-- Finite canonical sample integrals, with all multiplicities. -/
theorem canonicalMarked_integral (p : Parameters) (E : ℝ) (H : p.SiteMatrix)
    (f : MarkedSpectralSpace → ℝ) :
    (∫ z, f z ∂(physicalOrderedMarkedConfig p E H).marked.measure) =
      ∑ α : Fin p.N, f (physicalCanonicalMarkedLocations p E H α) := by
  let : MeasurableSingletonClass MassProfile := massProfile_measurableSingletonClass
  change (∫ z, f z ∂finiteAtomicMeasure (physicalCanonicalMarkedLocations p E H)) = _
  rw [finiteAtomicMeasure_eq_sum_dirac,
    integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp only [integral_dirac]

theorem canonicalMarked_laplace_rotation_error (p : Parameters) (E R : ℝ)
    (F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (hf : ∀ z, 0≤F z)
    (hs : ∀ z, z.1 ∉ Set.Icc (-R) R → F z=0) (a b : Torus) (H : p.SiteMatrix) :
    |markedLaplaceTest F hf (globalMarkedRotation a (physicalOrderedMarkedConfig p E H))-
      markedLaplaceTest F hf (globalMarkedRotation b (physicalOrderedMarkedConfig p E H))| ≤
      markedRotationTestError F R a b * (physicalCanonicalLocalCount p E R H : ℝ) := by
  classical
  let z := physicalCanonicalMarkedLocations p E H
  have hcoords (t : Torus) :
      (globalMarkedRotation t (physicalOrderedMarkedConfig p E H)).marked.coordinate F =
        ∑ α, F (markedLocationRotation t (z α)) := by
    change (∫ w, F w ∂(globalMarkedRotation t (physicalOrderedMarkedConfig p E H)).marked.measure) = _
    rw [globalMarkedRotation_integral, canonicalMarked_integral]
  change |Real.exp (-(globalMarkedRotation a _).marked.coordinate F)-
    Real.exp (-(globalMarkedRotation b _).marked.coordinate F)| ≤ _
  rw [hcoords a,hcoords b]
  have hn (t : Torus) : 0≤∑ α, F (markedLocationRotation t (z α)) :=
    Finset.sum_nonneg (fun _ _=>hf _)
  apply (abs_exp_neg_sub_le (hn a) (hn b)).trans
  rw [← Finset.sum_sub_distrib]
  have hc : (physicalCanonicalLocalCount p E R H : ℝ) =
      ∑ α : Fin p.N, if (z α).1 ∈ Set.Icc (-R) R then (1 : ℝ) else 0 := by
    have hn' : physicalCanonicalLocalCount p E R H =
        ∑ α : Fin p.N, if (z α).1 ∈ Set.Icc (-R) R then (1 : ℕ) else 0 := by
      simp [physicalCanonicalLocalCount,finiteSpectralCount,z,Finset.sum_boole]
    exact_mod_cast hn'
  rw [hc,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro α _
  by_cases hz : (z α).1 ∈ Set.Icc (-R) R
  · simpa only [ite_eq_left hz,mul_one] using markedRotationTestError_pointwise F R a b (z α) hz
  · have hza : F (markedLocationRotation a (z α))=0 := hs _ hz
    have hzb : F (markedLocationRotation b (z α))=0 := hs _ hz
    have hnot : ¬(-R ≤ (z α).1 ∧ (z α).1 ≤ R) := hz
    simp only [hza,hzb,sub_self,abs_zero,Set.mem_Icc,ite_eq_right hnot,mul_zero,le_refl]

/-- The canonical local counts are integrable. -/
theorem integrable_canonicalLocalCount (p : Parameters) (model : p.GaussianRingModel) (E R : ℝ) :
    Integrable (fun H => (physicalCanonicalLocalCount p E R H : ℝ))
      (model.law : Measure p.SiteMatrix) := by
  apply (integrable_const (p.N : ℝ)).mono'
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_physicalCanonicalLocalCount p E R)).aestronglyMeasurable
  filter_upwards [] with H
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  change (physicalCanonicalLocalCount p E R H : ℝ) ≤ (p.N : ℝ)
  exact_mod_cast (show physicalCanonicalLocalCount p E R H ≤ p.N from by
    simpa [physicalCanonicalLocalCount,finiteSpectralCount] using
      Finset.card_filter_le (s := (Finset.univ : Finset (Fin p.N)))
        (p := fun α => (physicalCanonicalMarkedLocations p E H α).1 ∈ Set.Icc (-R) R))

/-- First moment bound for the local count, from the PSSS source contract. -/
theorem integral_canonicalLocalCount_le (p : Parameters) (model : p.GaussianRingModel)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (E R : ℝ)
    (hrho : 0<Parameters.semicircleDensity E) (hR : 0≤R) :
    (∫ H, (physicalCanonicalLocalCount p E R H : ℝ) ∂(model.law : Measure p.SiteMatrix)) ≤
      p.physicalUnfoldedConstant source (Parameters.semicircleDensity E)*(2*R) := by
  have h := physicalCanonicalLocalCount_firstMoment_le p model source E R hrho hR
  have he : ENNReal.ofReal (∫ H, (physicalCanonicalLocalCount p E R H : ℝ)
      ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ H, (physicalCanonicalLocalCount p E R H : ℝ≥0∞)
        ∂(model.law : Measure p.SiteMatrix) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_canonicalLocalCount p model E R)
      (ae_of_all _ (fun _=>Nat.cast_nonneg _))]
    simp
  rw [← he] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (p.physicalUnfoldedConstant_pos source hrho).le (by positivity))).mp h

theorem canonicalPhysicalMarkedLaw_laplace_rotation_error (p : Parameters)
    (model : p.GaussianRingModel) (source : BlockBand.External.PSSS.SourceContract.{0})
    (E R : ℝ) (hrho : 0<Parameters.semicircleDensity E) (hR : 0≤R)
    (F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (hf : ∀ z, 0≤F z)
    (hs : ∀ z, z.1 ∉ Set.Icc (-R) R → F z=0) (a b : Torus) :
    |(∫ ξ, markedLaplaceTest F hf ξ ∂(globalMarkedRotationLaw a (model.canonicalPhysicalMarkedLaw E) :
      Measure MarkedPointMeasure))-
      ∫ ξ, markedLaplaceTest F hf ξ ∂(globalMarkedRotationLaw b (model.canonicalPhysicalMarkedLaw E) :
        Measure MarkedPointMeasure)| ≤
      markedRotationTestError F R a b *
        (p.physicalUnfoldedConstant source (Parameters.semicircleDensity E)*(2*R)) := by
  let g := markedLaplaceTest F hf
  have hm (t : Torus) :
      (∫ ξ, g ξ ∂(globalMarkedRotationLaw t (model.canonicalPhysicalMarkedLaw E) : Measure MarkedPointMeasure)) =
      ∫ H, g (globalMarkedRotation t (physicalOrderedMarkedConfig p E H))
        ∂(model.law : Measure p.SiteMatrix) := by
    change (∫ ξ, g ξ ∂Measure.map (globalMarkedRotation t)
      (model.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure)) = _
    rw [integral_map (measurable_globalMarkedRotation t).aemeasurable g.continuous.aestronglyMeasurable]
    change (∫ ξ, g (globalMarkedRotation t ξ) ∂Measure.map (physicalOrderedMarkedConfig p E)
      (model.law : Measure p.SiteMatrix)) = _
    exact integral_map (measurable_physicalOrderedMarkedConfig p E).aemeasurable
      (g.continuous.comp (continuous_globalMarkedRotation t)).aestronglyMeasurable
  have hi (t : Torus) : Integrable (fun H => g (globalMarkedRotation t
      (physicalOrderedMarkedConfig p E H))) (model.law : Measure p.SiteMatrix) :=
    (integrable_const ‖g‖).mono'
      ((g.continuous.comp (continuous_globalMarkedRotation t)).measurable.comp
        (measurable_physicalOrderedMarkedConfig p E)).aestronglyMeasurable
      (ae_of_all _ (fun H=>g.norm_coe_le_norm _))
  rw [hm a,hm b,← integral_sub (hi a) (hi b)]
  calc
    _ ≤ ∫ H, |g (globalMarkedRotation a (physicalOrderedMarkedConfig p E H))-
        g (globalMarkedRotation b (physicalOrderedMarkedConfig p E H))|
        ∂(model.law : Measure p.SiteMatrix) := abs_integral_le_integral_abs
    _ ≤ ∫ H, markedRotationTestError F R a b*(physicalCanonicalLocalCount p E R H : ℝ)
        ∂(model.law : Measure p.SiteMatrix) :=
      integral_mono ((hi a).sub (hi b)).abs
        ((integrable_canonicalLocalCount p model E R).const_mul _)
        (canonicalMarked_laplace_rotation_error p E R F hf hs a b)
    _ = markedRotationTestError F R a b*
        ∫ H, (physicalCanonicalLocalCount p E R H : ℝ) ∂(model.law : Measure p.SiteMatrix) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_canonicalLocalCount_le p model source E R hrho hR)
      (markedRotationTestError_nonneg F R a b)

end BlockBand.QUE.Invariance
