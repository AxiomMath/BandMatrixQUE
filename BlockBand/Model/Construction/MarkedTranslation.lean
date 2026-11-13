module

public import BlockBand.Model.Construction.VagueTranslation
public import BlockBand.Model.Construction.GaussianTranslationSpectral

/-!
# Global spectral translation of marked configurations

Translation by `s` of the spectral locations of a marked point measure, as a homeomorphism of the
space of marked point measures that transports counts, integrals and coordinates, and agrees
with the scalar translation of the matrix on the canonical spectrum.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Set
open scoped Topology

/-- Full marked point measures are determined by their marked measures. -/
theorem markedPointMeasure_eq_of_marked_measure_eq (ξ η : MarkedPointMeasure)
    (h : ξ.marked.measure = η.marked.measure) : ξ = η := by
  have hm : ξ.marked = η.marked := vaguePointMeasure_eq_of_measure_eq _ _ h
  have hs : ξ.spectral = η.spectral := by
    apply vaguePointMeasure_eq_of_measure_eq
    rw [ξ.spectral_eq, η.spectral_eq, h]
  cases ξ
  cases η
  cases hm
  cases hs
  rfl

/-- The translation homeomorphism of the real/profile product. -/
def markedSpectralTranslationHomeomorph (s : ℝ) : MarkedSpectralSpace ≃ₜ MarkedSpectralSpace where
  toFun := fun z => (z.1 + s, z.2)
  invFun := fun z => (z.1 - s, z.2)
  left_inv := by intro z; ext <;> simp
  right_inv := by intro z; ext <;> simp
  continuous_toFun := (continuous_fst.add continuous_const).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub continuous_const).prodMk continuous_snd

/-- Location translations are measurable for the product/Giry measurable space. -/
theorem measurable_markedSpectralTranslationHomeomorph (s : ℝ) :
    Measurable (markedSpectralTranslationHomeomorph s) :=
  (measurable_fst.add_const s).prodMk measurable_snd

theorem measurable_markedSpectralTranslationHomeomorph_symm (s : ℝ) :
    Measurable (markedSpectralTranslationHomeomorph s).symm :=
  (measurable_fst.sub_const s).prodMk measurable_snd

/-- Transport of the underlying marked vague measure. -/
def markedVagueTranslation (s : ℝ) (ξ : VaguePointMeasure MarkedSpectralSpace) :
    VaguePointMeasure MarkedSpectralSpace :=
  vagueHomeomorphPushforward (markedSpectralTranslationHomeomorph s)
    (measurable_markedSpectralTranslationHomeomorph s)
    (measurable_markedSpectralTranslationHomeomorph_symm s) ξ

theorem markedVagueTranslation_measure (s : ℝ) (ξ : VaguePointMeasure MarkedSpectralSpace) :
    (markedVagueTranslation s ξ).measure = Measure.map (gaussianMarkedLocationTranslate s) ξ.measure := rfl

theorem markedVagueTranslation_apply (s : ℝ) (ξ : VaguePointMeasure MarkedSpectralSpace)
    (A : Set MarkedSpectralSpace) :
    (markedVagueTranslation s ξ).measure A = ξ.measure ((gaussianMarkedLocationTranslate s) ⁻¹' A) :=
  vagueHomeomorphPushforward_apply _ _ _ ξ A

/-- Both full measure pushforwards agree with the redundant spectral projection. -/
theorem markedVagueTranslation_spectral_eq (s : ℝ) (ξ : MarkedPointMeasure) :
    (realVagueTranslation s ξ.spectral).measure =
      Measure.map Prod.fst (markedVagueTranslation s ξ.marked).measure := by
  change Measure.map (fun x : ℝ => x+s) ξ.spectral.measure = _
  rw [ξ.spectral_eq, markedVagueTranslation_measure]
  have hm : Measurable (fun x : ℝ => x+s) := measurable_id.add_const s
  calc
    Measure.map (fun x : ℝ => x+s) (Measure.map Prod.fst ξ.marked.measure) =
        Measure.map ((fun x : ℝ => x+s) ∘ Prod.fst) ξ.marked.measure :=
      Measure.map_map hm measurable_fst
    _ = Measure.map (Prod.fst ∘ gaussianMarkedLocationTranslate s) ξ.marked.measure := rfl
    _ = Measure.map Prod.fst (Measure.map (gaussianMarkedLocationTranslate s) ξ.marked.measure) :=
      (Measure.map_map measurable_fst (measurable_gaussianMarkedLocationTranslate s)).symm

/-- Global translation on the marked configuration type. -/
def globalMarkedTranslation (s : ℝ) (ξ : MarkedPointMeasure) : MarkedPointMeasure where
  marked := markedVagueTranslation s ξ.marked
  spectral := realVagueTranslation s ξ.spectral
  spectral_eq := markedVagueTranslation_spectral_eq s ξ

theorem globalMarkedTranslation_marked_measure (s : ℝ) (ξ : MarkedPointMeasure) :
    (globalMarkedTranslation s ξ).marked.measure =
      Measure.map (gaussianMarkedLocationTranslate s) ξ.marked.measure := rfl

theorem globalMarkedTranslation_apply (s : ℝ) (ξ : MarkedPointMeasure)
    (A : Set MarkedSpectralSpace) :
    (globalMarkedTranslation s ξ).marked.measure A =
      ξ.marked.measure ((gaussianMarkedLocationTranslate s) ⁻¹' A) :=
  markedVagueTranslation_apply s ξ.marked A

theorem globalMarkedTranslation_spectral (s : ℝ) (ξ : MarkedPointMeasure) :
    (globalMarkedTranslation s ξ).spectral = realVagueTranslation s ξ.spectral := rfl

theorem globalMarkedTranslation_zero (ξ : MarkedPointMeasure) : globalMarkedTranslation 0 ξ = ξ := by
  apply markedPointMeasure_eq_of_marked_measure_eq
  ext A hA
  rw [globalMarkedTranslation_apply]
  have he : gaussianMarkedLocationTranslate 0 = id := by
    funext z
    exact Prod.ext (add_zero z.1) rfl
  rw [he]
  rfl

theorem globalMarkedTranslation_add (s t : ℝ) (ξ : MarkedPointMeasure) :
    globalMarkedTranslation s (globalMarkedTranslation t ξ) = globalMarkedTranslation (s+t) ξ := by
  apply markedPointMeasure_eq_of_marked_measure_eq
  ext A hA
  simp only [globalMarkedTranslation_apply, Set.preimage_preimage]
  congr 1
  ext z
  change ((z.1+t+s, z.2) ∈ A) ↔ ((z.1+(s+t),z.2) ∈ A)
  rw [show z.1+t+s = z.1+(s+t) by ring]

theorem globalMarkedTranslation_inverse (s : ℝ) (ξ : MarkedPointMeasure) :
    globalMarkedTranslation (-s) (globalMarkedTranslation s ξ) = ξ := by
  rw [globalMarkedTranslation_add, neg_add_cancel, globalMarkedTranslation_zero]

/-- Transport of every stored compact-window count, derived from the full pushforward. -/
theorem globalMarkedTranslation_count (s : ℝ) (ξ : MarkedPointMeasure)
    (A : RelativelyCompactBorelSet MarkedSpectralSpace) :
    (globalMarkedTranslation s ξ).marked.count A = ξ.marked.count
      (vagueHomeomorphPullback (markedSpectralTranslationHomeomorph s)
        (measurable_markedSpectralTranslationHomeomorph s) A) := rfl

/-- Arbitrary complete real-vector Bochner integrals obey the global marked transport. -/
theorem globalMarkedTranslation_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : ℝ) (ξ : MarkedPointMeasure) (f : MarkedSpectralSpace → E) :
    (∫ z, f z ∂(globalMarkedTranslation s ξ).marked.measure) =
      ∫ z, f (gaussianMarkedLocationTranslate s z) ∂ξ.marked.measure :=
  vagueHomeomorphPushforward_integral _ _ _ ξ.marked f

/-- Exact defining marked vague coordinate transport by proper compact-test pullback. -/
theorem globalMarkedTranslation_coordinate (s : ℝ) (ξ : MarkedPointMeasure)
    (f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) :
    (globalMarkedTranslation s ξ).marked.coordinate f =
      ξ.marked.coordinate (vagueHomeomorphTestPullback (markedSpectralTranslationHomeomorph s) f) :=
  vagueHomeomorphPushforward_coordinate _ _ _ ξ.marked f

/-- For fixed `s`, the global translation is continuous in the induced vague topology. -/
theorem continuous_globalMarkedTranslation (s : ℝ) : Continuous (globalMarkedTranslation s) := by
  rw [continuous_induced_rng]
  exact (continuous_vagueHomeomorphPushforward (markedSpectralTranslationHomeomorph s)
    (measurable_markedSpectralTranslationHomeomorph s)
    (measurable_markedSpectralTranslationHomeomorph_symm s)).comp continuous_induced_dom

theorem measurable_globalMarkedTranslation (s : ℝ) : Measurable (globalMarkedTranslation s) :=
  (continuous_globalMarkedTranslation s).measurable

/-- On the ordered marked configuration of a site matrix, the global translation agrees with the
finite canonical translation `gaussianTranslatedCanonicalMarkedConfig`. -/
theorem globalMarkedTranslation_canonical (p : Parameters) (E s : ℝ) (H : p.SiteMatrix) :
    globalMarkedTranslation s (physicalOrderedMarkedConfig p E H) =
      gaussianTranslatedCanonicalMarkedConfig p E s H := by
  apply markedPointMeasure_eq_of_marked_measure_eq
  rw [globalMarkedTranslation_marked_measure, gaussianTranslatedCanonicalMarkedConfig_measure]

/-- Exact global action on the canonical spectrum of a raw scalar-translated matrix. -/
theorem physicalOrderedMarkedConfig_eq_globalMarkedTranslation (p : Parameters) (E t : ℝ)
    (H : p.SiteMatrix) (h : physicalProfileGood p H) :
    physicalOrderedMarkedConfig p E (gaussianSpectralTranslate t H) =
      globalMarkedTranslation (p.N * Parameters.semicircleDensity E * t)
        (physicalOrderedMarkedConfig p E H) := by
  rw [physicalOrderedMarkedConfig_gaussianSpectralTranslate p E t H h,
    globalMarkedTranslation_canonical]

/-- The fixed marked point-configuration translation is itself a homeomorphism. -/
def globalMarkedTranslationHomeomorph (s : ℝ) : MarkedPointMeasure ≃ₜ MarkedPointMeasure where
  toFun := globalMarkedTranslation s
  invFun := globalMarkedTranslation (-s)
  left_inv := globalMarkedTranslation_inverse s
  right_inv := by
    intro ξ
    simpa only [neg_neg] using globalMarkedTranslation_inverse (-s) ξ
  continuous_toFun := continuous_globalMarkedTranslation s
  continuous_invFun := continuous_globalMarkedTranslation (-s)

end BlockBand.Model.Construction
