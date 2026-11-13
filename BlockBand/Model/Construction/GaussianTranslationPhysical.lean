module

public import BlockBand.Model.Construction.GaussianTranslationProduct
public import BlockBand.Model.Construction.GaussianTranslationSpectral
public import BlockBand.Model.Construction.SpectralFiniteRealization
public import BlockBand.Counting.TraceDecomposition

/-!
# Translation total variation of the finite physical marked law

For every finite physical Gaussian model, the canonical marked spectral law and its translate by
`s` in the spectral locations are within an explicit total variation distance, obtained by
splitting the matrix into its scalar trace part and a traceless background.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory Set
open BlockBand.Model.Construction
open scoped NNReal

/-- Measurability of the raw traceless matrix, on the full matrix domain. -/
theorem measurable_tracelessGaussianMatrix (p : BlockBand.Parameters) :
    Measurable p.tracelessGaussianMatrix := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  change Measurable (fun H : p.SiteMatrix => H x y -
    (p.scalarTrace H : ℂ) * (1 : p.SiteMatrix) x y)
  have hm : Measurable (fun H : p.SiteMatrix => H x y) :=
    (measurable_pi_apply y).comp (measurable_pi_apply x)
  have ht : Measurable (fun H : p.SiteMatrix => (p.scalarTrace H : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp p.measurable_scalarTrace
  exact hm.sub (ht.mul_const _)

/-- The probability law of the traceless background. -/
def GaussianRingModel.tracelessMatrixLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) : ProbabilityMeasure p.SiteMatrix :=
  model.law.map p.tracelessGaussianMatrix

/-- Microscopic scalar trace and traceless background, with a displayed scalar shift. -/
def microscopicTraceBackgroundPair (p : BlockBand.Parameters) (E s : ℝ)
    (H : p.SiteMatrix) : ℝ × p.SiteMatrix :=
  ((p.N * semicircleDensity E) * p.scalarTrace H + s, p.tracelessGaussianMatrix H)

theorem measurable_microscopicTraceBackgroundPair (p : BlockBand.Parameters) (E s : ℝ) :
    Measurable (p.microscopicTraceBackgroundPair E s) :=
  ((p.measurable_scalarTrace.const_mul _).add_const s).prodMk
    p.measurable_tracelessGaussianMatrix

/-- Exact product law of the microscopic scalar `N ρ(E) Tr_s H + s` and the traceless matrix:
under the model law the scalar trace is independent of the traceless part, so the joint law is
the product of the two marginals. -/
theorem GaussianRingModel.microscopicTraceBackgroundPair_map {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (E s : ℝ) :
    Measure.map (p.microscopicTraceBackgroundPair E s) (model.law : Measure p.SiteMatrix) =
      (Measure.map (fun H => (p.N * semicircleDensity E) * p.scalarTrace H + s)
        (model.law : Measure p.SiteMatrix)).prod
        (model.tracelessMatrixLaw : Measure p.SiteMatrix) := by
  have hI := model.scalarTrace_independent_tracelessMatrix.comp
    (show Measurable (fun t : ℝ => (p.N * semicircleDensity E) * t + s) by fun_prop)
    measurable_id
  exact hI.map_prod_eq_prod_map_map
    (((p.measurable_scalarTrace.const_mul _).add_const s).aemeasurable)
    p.measurable_tracelessGaussianMatrix.aemeasurable

/-- The canonical physical marked law for any realization of the physical matrix law. -/
def GaussianRingModel.canonicalPhysicalMarkedLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (E : ℝ) : ProbabilityMeasure BlockBand.MarkedPointMeasure :=
  model.law.map (physicalOrderedMarkedConfig p E)

/-- Law of the finite canonical atoms with only their spectral locations translated.
The underlying marked measure is exactly the pushforward by `(u, mark) ↦ (u + s, mark)`. -/
def GaussianRingModel.translatedCanonicalPhysicalMarkedLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (E s : ℝ) : ProbabilityMeasure BlockBand.MarkedPointMeasure :=
  model.law.map (gaussianTranslatedCanonicalMarkedConfig p E s)

/-- Scalar/traceless reconstruction gives exact microscopic marked translation,
on every raw matrix, before any almost-sure spectral statement is used. -/
theorem microscopicTraceBackgroundPair_markedMap (p : BlockBand.Parameters) (E s : ℝ)
    (hρ : semicircleDensity E ≠ 0) (H : p.SiteMatrix) :
    gaussianMicroscopicSpectralMarkedMap p E (p.microscopicTraceBackgroundPair E s H) =
      gaussianMicroscopicSpectralMarkedMap p E (s,H) := by
  have hN : (p.N : ℝ) ≠ 0 := by exact_mod_cast p.N_pos.ne'
  have hdiv : ((p.N * semicircleDensity E) * p.scalarTrace H + s) /
      (p.N * semicircleDensity E) = p.scalarTrace H + s / (p.N * semicircleDensity E) := by
    field_simp
  unfold gaussianMicroscopicSpectralMarkedMap gaussianSpectralMarkedMap
  change physicalOrderedMarkedConfig p E
    (p.tracelessGaussianMatrix H +
      ((((p.N * semicircleDensity E) * p.scalarTrace H + s) /
        (p.N * semicircleDensity E) : ℝ) : ℂ) • (1 : p.SiteMatrix)) =
    physicalOrderedMarkedConfig p E
      (H + ((s / (p.N * semicircleDensity E) : ℝ) : ℂ) • (1 : p.SiteMatrix))
  apply congrArg (physicalOrderedMarkedConfig p E)
  rw [hdiv, Complex.ofReal_add, add_smul]
  unfold tracelessGaussianMatrix
  abel

/-- Unshifted product reconstruction is the canonical marked configuration on all raw matrices. -/
theorem microscopicTraceBackgroundPair_markedMap_zero (p : BlockBand.Parameters) (E : ℝ)
    (hρ : semicircleDensity E ≠ 0) (H : p.SiteMatrix) :
    gaussianMicroscopicSpectralMarkedMap p E (p.microscopicTraceBackgroundPair E 0 H) =
      physicalOrderedMarkedConfig p E H := by
  rw [p.microscopicTraceBackgroundPair_markedMap E 0 hρ H]
  simp [gaussianMicroscopicSpectralMarkedMap, gaussianSpectralMarkedMap, gaussianSpectralTranslate]

/-- Shifted marked reconstruction is the translated canonical finite measure almost surely. -/
theorem GaussianRingModel.ae_microscopicTraceBackgroundPair_markedMap {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (E s : ℝ) (hρ : semicircleDensity E ≠ 0) :
    (fun H => gaussianMicroscopicSpectralMarkedMap p E
      (p.microscopicTraceBackgroundPair E s H)) =ᵐ[(model.law : Measure p.SiteMatrix)]
      gaussianTranslatedCanonicalMarkedConfig p E s := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  rw [p.microscopicTraceBackgroundPair_markedMap E s hρ H]
  exact gaussianMicroscopicSpectralMarkedMap_eq p E s hρ H ⟨hH,hsep⟩

/-- The canonical marked law is the image of the product law of the microscopic scalar and the
traceless matrix under the measurable microscopic map. -/
theorem GaussianRingModel.canonicalPhysicalMarkedLaw_eq_product {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (E : ℝ) (hρ : semicircleDensity E ≠ 0) :
    (model.canonicalPhysicalMarkedLaw E : Measure BlockBand.MarkedPointMeasure) =
      Measure.map (gaussianMicroscopicSpectralMarkedMap p E)
        ((Measure.map (fun H => (p.N * semicircleDensity E) * p.scalarTrace H)
          (model.law : Measure p.SiteMatrix)).prod
          (model.tracelessMatrixLaw : Measure p.SiteMatrix)) := by
  have hj := model.microscopicTraceBackgroundPair_map E 0
  simp only [add_zero] at hj
  symm
  rw [← hj, Measure.map_map (measurable_gaussianMicroscopicSpectralMarkedMap p E)
    (p.measurable_microscopicTraceBackgroundPair E 0)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall (p.microscopicTraceBackgroundPair_markedMap_zero E hρ)

/-- The translated canonical marked law is exactly the same map of the shifted scalar product. -/
theorem GaussianRingModel.translatedCanonicalPhysicalMarkedLaw_eq_product {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (E s : ℝ) (hρ : semicircleDensity E ≠ 0) :
    (model.translatedCanonicalPhysicalMarkedLaw E s : Measure BlockBand.MarkedPointMeasure) =
      Measure.map (gaussianMicroscopicSpectralMarkedMap p E)
        ((Measure.map (fun t : ℝ => t + s) (Measure.map
          (fun H => (p.N * semicircleDensity E) * p.scalarTrace H)
          (model.law : Measure p.SiteMatrix))).prod
          (model.tracelessMatrixLaw : Measure p.SiteMatrix)) := by
  rw [Measure.map_map (show Measurable (fun t : ℝ => t + s) by fun_prop)
    (p.measurable_scalarTrace.const_mul _)]
  simp only [Function.comp_def]
  symm
  rw [← model.microscopicTraceBackgroundPair_map E s,
    Measure.map_map (measurable_gaussianMicroscopicSpectralMarkedMap p E)
      (p.measurable_microscopicTraceBackgroundPair E s)]
  exact Measure.map_congr (model.ae_microscopicTraceBackgroundPair_markedMap E s hρ)

/-- Finite physical marked-law event bound, with no independence or marked-map
hypothesis. -/
theorem GaussianRingModel.canonicalPhysicalMarkedLaw_translation_event_le
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (E : ℝ)
    (hρ : 0 < semicircleDensity E) (s : ℝ) (B : Set BlockBand.MarkedPointMeasure)
    (hB : MeasurableSet B) :
    |(model.canonicalPhysicalMarkedLaw E : Measure BlockBand.MarkedPointMeasure).real B -
      (model.translatedCanonicalPhysicalMarkedLaw E s : Measure BlockBand.MarkedPointMeasure).real B| ≤
      min 1 (|s| / (semicircleDensity E * Real.sqrt (2 * Real.pi * p.c * (p.n : ℝ)))) := by
  rw [model.canonicalPhysicalMarkedLaw_eq_product E hρ.ne',
    model.translatedCanonicalPhysicalMarkedLaw_eq_product E s hρ.ne']
  exact model.spectralScalarTrace_product_map_event_le (semicircleDensity E) hρ s
    (model.tracelessMatrixLaw : Measure p.SiteMatrix)
    (gaussianMicroscopicSpectralMarkedMap p E)
    (measurable_gaussianMicroscopicSpectralMarkedMap p E) B hB

/-- Event-supremum total variation between the canonical and the spectrally translated finite
physical marked laws. -/
def GaussianRingModel.canonicalPhysicalMarkedTranslationTV {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (E s : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ B : Set BlockBand.MarkedPointMeasure, MeasurableSet B ∧
    r = |(model.canonicalPhysicalMarkedLaw E : Measure BlockBand.MarkedPointMeasure).real B -
      (model.translatedCanonicalPhysicalMarkedLaw E s : Measure BlockBand.MarkedPointMeasure).real B|}

/-- Translation total variation bound of the finite physical marked law (stationarity). -/
theorem GaussianRingModel.canonicalPhysicalMarkedLaw_translation_tv_le
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (E : ℝ)
    (hρ : 0 < semicircleDensity E) (s : ℝ) :
    model.canonicalPhysicalMarkedTranslationTV E s ≤
      min 1 (|s| / (semicircleDensity E * Real.sqrt (2 * Real.pi * p.c * (p.n : ℝ)))) := by
  unfold GaussianRingModel.canonicalPhysicalMarkedTranslationTV
  apply csSup_le
  · refine ⟨0, ∅, MeasurableSet.empty, ?_⟩
    simp
  · rintro r ⟨B,hB,rfl⟩
    exact model.canonicalPhysicalMarkedLaw_translation_event_le E hρ s B hB

/-- The fixed bulk energy condition implies exactly the positive density used above. -/
theorem semicircleDensity_pos_of_sq_lt_four (E : ℝ) (hE : E ^ 2 < 4) :
    0 < semicircleDensity E := by
  unfold semicircleDensity
  exact div_pos (Real.sqrt_pos.mpr (sub_pos.mpr hE)) (by positivity [Real.pi_pos])

/-- Bulk-energy form, all finite physical parameters and all translations. -/
theorem GaussianRingModel.canonicalPhysicalMarkedLaw_bulk_translation_tv_le
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (E : ℝ)
    (hE : E ^ 2 < 4) (s : ℝ) :
    model.canonicalPhysicalMarkedTranslationTV E s ≤
      min 1 (|s| / (semicircleDensity E * Real.sqrt (2 * Real.pi * p.c * (p.n : ℝ)))) :=
  model.canonicalPhysicalMarkedLaw_translation_tv_le E (semicircleDensity_pos_of_sq_lt_four E hE) s

end BlockBand.Parameters

namespace BlockBand.Model.Construction
open MeasureTheory

/-- The marked law of `constructFiniteRealization` is exactly the canonical law used above. -/
theorem constructFiniteRealization_markedLaw_eq_canonical (p : Parameters) (E : ℝ) :
    (constructFiniteRealization p).markedLaw E = p.constructGaussianRingModel.canonicalPhysicalMarkedLaw E := rfl

/-- Finite physical marked-law event bound for the constructed realization. -/
theorem constructFiniteRealization_markedLaw_translation_event_le (p : Parameters) (E : ℝ)
    (hE : E ^ 2 < 4) (s : ℝ) (B : Set MarkedPointMeasure) (hB : MeasurableSet B) :
    |((constructFiniteRealization p).markedLaw E : Measure MarkedPointMeasure).real B -
      (p.constructGaussianRingModel.translatedCanonicalPhysicalMarkedLaw E s :
        Measure MarkedPointMeasure).real B| ≤
      min 1 (|s| / (Parameters.semicircleDensity E * Real.sqrt (2 * Real.pi * p.c * (p.n : ℝ)))) := by
  rw [constructFiniteRealization_markedLaw_eq_canonical]
  exact p.constructGaussianRingModel.canonicalPhysicalMarkedLaw_translation_event_le E
    (Parameters.semicircleDensity_pos_of_sq_lt_four E hE) s B hB

end BlockBand.Model.Construction
