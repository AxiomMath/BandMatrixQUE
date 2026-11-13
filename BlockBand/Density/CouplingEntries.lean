module

public import BlockBand.Model.Construction.GaussianCompatibility
public import BlockBand.QUE.Invariance.CyclicLaw

/-!
# First absolute moments of physical matrix entries

Law: the physical law `model.law` of any admissible `p` (any realization; it equals
`p.gaussianMatrixLaw`). For all sites `x, y`:
* `integrable_norm_entry`: `H ↦ ‖H x y‖` is integrable;
* `integral_norm_entry_le`: `E ‖H_xy‖ ≤ 2 √(E|H_xy|²)` with `E|H_xy|² = entryVariance x y`
  (so `E ‖H_xy‖ = 0` outside the band);
* `integral_norm_entry_le_two`: `E ‖H_xy‖ ≤ 2`.
Scalar input: `E|Z| ≤ √v` for `Z ~ N(0, v)`. No hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- `E|Z| ≤ √v` for a centred real Gaussian of variance `v`. -/
theorem integral_abs_gaussianReal_le (v : ℝ≥0) :
    ∫ t, |t| ∂(gaussianReal 0 v) ≤ Real.sqrt v := by
  have : IsProbabilityMeasure (gaussianReal 0 v) := instIsProbabilityMeasureGaussianReal 0 v
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    simp [gaussianReal_zero_var]
  have hv0 : (0 : ℝ) < v := by positivity
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have hsq : ∫ t, t ^ 2 ∂(gaussianReal 0 v) = v := by
    have h := @variance_id_gaussianReal 0 v
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    simpa [integral_id_gaussianReal] using h
  have hi2 : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hi1 : Integrable (fun t : ℝ => |t|) (gaussianReal 0 v) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  have hle : ∀ t : ℝ, |t| ≤ (Real.sqrt v + t ^ 2 / Real.sqrt v) / 2 := by
    intro t
    have e : (Real.sqrt v + t ^ 2 / Real.sqrt v) / 2 - |t| =
        (|t| - Real.sqrt v) ^ 2 / (2 * Real.sqrt v) := by
      rw [← sq_abs t]
      field_simp
      ring
    have := div_nonneg (sq_nonneg (|t| - Real.sqrt v)) (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt v)
    linarith
  calc ∫ t, |t| ∂(gaussianReal 0 v)
      ≤ ∫ t, (Real.sqrt v + t ^ 2 / Real.sqrt v) / 2 ∂(gaussianReal 0 v) :=
        integral_mono hi1 (((integrable_const _).add (hi2.div_const _)).div_const _) hle
    _ = Real.sqrt v := by
        rw [integral_div, integral_add (integrable_const _) (hi2.div_const _), integral_div, hsq,
          integral_const]
        simp only [probReal_univ, one_smul]
        rw [show (v : ℝ) / Real.sqrt v = Real.sqrt v by
          rw [div_eq_iff hs.ne', Real.mul_self_sqrt hv0.le]]
        ring

/-- Each coordinate of the product Gaussian law has an integrable absolute value with
`E|z_i| ≤ √(v_i)`. -/
theorem gaussianCoordinate_abs (p : Parameters) (i : p.GaussianCoordinate) :
    Integrable (fun z : p.GaussianCoordinate → ℝ => |z i|)
        (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) ∧
      ∫ z, |z i| ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) ≤
        Real.sqrt (p.gaussianCoordinateVariance i) := by
  have hP : ∀ j, IsProbabilityMeasure (gaussianReal 0 (p.gaussianCoordinateVariance j)) :=
    fun j => instIsProbabilityMeasureGaussianReal 0 _
  have hmp := measurePreserving_eval (fun j => gaussianReal 0 (p.gaussianCoordinateVariance j)) i
  have hmap : Measure.map (Function.eval i)
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) =
      gaussianReal 0 (p.gaussianCoordinateVariance i) := hmp.map_eq
  have hint : Integrable (fun t : ℝ => |t|) (gaussianReal 0 (p.gaussianCoordinateVariance i)) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  constructor
  · rw [← hmap] at hint
    exact hint.comp_measurable (measurable_pi_apply i)
  · have h2 : ∫ z, |z i| ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) =
        ∫ t, |t| ∂(Measure.map (Function.eval i)
          (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))) :=
      (integral_map (μ := (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)))
        (φ := Function.eval i) (f := fun t : ℝ => |t|) (measurable_pi_apply i).aemeasurable
        continuous_abs.aestronglyMeasurable).symm
    rw [h2, hmap]
    exact integral_abs_gaussianReal_le (p.gaussianCoordinateVariance i)

/-- Every reconstructed entry is dominated by two coordinates whose variances are at most the
entry variance. -/
theorem exists_coordinates_entry (p : Parameters) (x y : p.Site) :
    ∃ a c : p.GaussianCoordinate,
      ((p.gaussianCoordinateVariance a : ℝ) ≤ p.entryVariance x y) ∧
      ((p.gaussianCoordinateVariance c : ℝ) ≤ p.entryVariance x y) ∧
      ∀ z, ‖p.gaussianReconstruction z x y‖ ≤ |z a| + |z c| := by
  have hnn := p.entryVariance_nonneg x y
  by_cases hxy : x = y
  · subst hxy
    refine ⟨.inl x, .inr (x, x, false), le_rfl, ?_, ?_⟩
    · simp [Parameters.gaussianCoordinateVariance, hnn]
    · intro z
      simp [Parameters.gaussianReconstruction]
  · by_cases hlt : p.siteIndex x < p.siteIndex y
    · have hv : ∀ t : Bool, ((p.gaussianCoordinateVariance (.inr (x, y, t)) : ℝ)) =
          p.entryVariance x y / 2 := fun t => by simp [Parameters.gaussianCoordinateVariance, hlt]; rfl
      refine ⟨.inr (x, y, false), .inr (x, y, true), ?_, ?_, ?_⟩
      · rw [hv]; linarith
      · rw [hv]; linarith
      · intro z
        simp only [Parameters.gaussianReconstruction, hxy, hlt, ite_false, ite_true]
        refine (norm_add_le _ _).trans ?_
        simp [Complex.norm_real]
    · have hne : p.siteIndex x ≠ p.siteIndex y := fun h => hxy (p.siteIndex_injective h)
      have hylt : p.siteIndex y < p.siteIndex x := by omega
      have hsym := p.entryVariance_symm x y
      have hv : ∀ t : Bool, ((p.gaussianCoordinateVariance (.inr (y, x, t)) : ℝ)) =
          p.entryVariance y x / 2 := fun t => by simp [Parameters.gaussianCoordinateVariance, hylt]; rfl
      refine ⟨.inr (y, x, false), .inr (y, x, true), ?_, ?_, ?_⟩
      · rw [hv]; linarith
      · rw [hv]; linarith
      · intro z
        simp only [Parameters.gaussianReconstruction, hxy, hlt, ite_false]
        refine (norm_sub_le _ _).trans ?_
        simp [Complex.norm_real]

/-- Entries of the physical law are integrable in norm. -/
theorem integrable_norm_entry (p : Parameters) (model : p.GaussianRingModel) (x y : p.Site) :
    Integrable (fun H : p.SiteMatrix => ‖H x y‖) (model.law : Measure p.SiteMatrix) := by
  rw [model.law_eq_gaussianMatrixLaw]
  change Integrable _ (Measure.map p.gaussianReconstruction
    (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)))
  have hm : AEStronglyMeasurable (fun H : p.SiteMatrix => ‖H x y‖)
      (Measure.map p.gaussianReconstruction
        (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))) :=
    (by fun_prop : Continuous fun H : p.SiteMatrix => ‖H x y‖).aestronglyMeasurable
  rw [integrable_map_measure hm p.measurable_gaussianReconstruction.aemeasurable]
  obtain ⟨a, c, -, -, hdom⟩ := exists_coordinates_entry p x y
  refine (((gaussianCoordinate_abs p a).1.add (gaussianCoordinate_abs p c).1)).mono'
    (hm.comp_measurable p.measurable_gaussianReconstruction) ?_
  filter_upwards with z
  rw [Function.comp_apply, norm_norm]
  exact hdom z

/-- `E ‖H_xy‖ ≤ 2 √(entryVariance x y)` under the physical law. -/
theorem integral_norm_entry_le (p : Parameters) (model : p.GaussianRingModel) (x y : p.Site) :
    ∫ H, ‖H x y‖ ∂(model.law : Measure p.SiteMatrix) ≤ 2 * Real.sqrt (p.entryVariance x y) := by
  rw [model.law_eq_gaussianMatrixLaw]
  change ∫ H, ‖H x y‖ ∂(Measure.map p.gaussianReconstruction
    (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))) ≤ _
  rw [integral_map p.measurable_gaussianReconstruction.aemeasurable
    (by fun_prop : Continuous fun H : p.SiteMatrix => ‖H x y‖).aestronglyMeasurable]
  obtain ⟨a, c, ha, hc, hdom⟩ := exists_coordinates_entry p x y
  obtain ⟨ia, la⟩ := gaussianCoordinate_abs p a
  obtain ⟨ic, lc⟩ := gaussianCoordinate_abs p c
  have hmeas : AEStronglyMeasurable (fun z => ‖p.gaussianReconstruction z x y‖)
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) :=
    ((by fun_prop : Continuous fun H : p.SiteMatrix => ‖H x y‖).measurable.comp
      p.measurable_gaussianReconstruction).aestronglyMeasurable
  calc ∫ z, ‖p.gaussianReconstruction z x y‖
        ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))
      ≤ ∫ z, (|z a| + |z c|) ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (ia.add ic) (Filter.Eventually.of_forall hdom)
    _ = ∫ z, |z a| ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) +
          ∫ z, |z c| ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) :=
        integral_add ia ic
    _ ≤ Real.sqrt (p.entryVariance x y) + Real.sqrt (p.entryVariance x y) :=
        add_le_add (la.trans (Real.sqrt_le_sqrt ha)) (lc.trans (Real.sqrt_le_sqrt hc))
    _ = 2 * Real.sqrt (p.entryVariance x y) := by ring

/-- The physical entry variance is at most `1`. -/
theorem entryVariance_le_one (p : Parameters) (x y : p.Site) : p.entryVariance x y ≤ 1 := by
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hc : p.c ≤ 1 := by unfold Parameters.c; linarith [p.b_pos]
  unfold Parameters.entryVariance
  split_ifs
  · exact (div_le_one (by linarith)).mpr (hc.trans hW)
  · exact (div_le_one (by linarith)).mpr ((by linarith [p.b_lt_half] : p.b ≤ 1).trans hW)
  · norm_num

/-- `E ‖H_xy‖ ≤ 2` under the physical law. -/
theorem integral_norm_entry_le_two (p : Parameters) (model : p.GaussianRingModel)
    (x y : p.Site) : ∫ H, ‖H x y‖ ∂(model.law : Measure p.SiteMatrix) ≤ 2 := by
  refine (integral_norm_entry_le p model x y).trans ?_
  have : Real.sqrt (p.entryVariance x y) ≤ 1 :=
    Real.sqrt_le_one.mpr (entryVariance_le_one p x y)
  linarith

/-- `E ‖H_xy‖ = 0` outside the band. -/
theorem integral_norm_entry_eq_zero (p : Parameters) (model : p.GaussianRingModel)
    {x y : p.Site} (h : p.entryVariance x y = 0) :
    ∫ H, ‖H x y‖ ∂(model.law : Measure p.SiteMatrix) = 0 := by
  refine le_antisymm ?_ (integral_nonneg fun _ => norm_nonneg _)
  simpa [h] using integral_norm_entry_le p model x y

end BlockBand.Density
