module

public import BlockBand.PointProcess.Vague
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Global pushforward of vague point measures

Pushforward of vague point measures under a bimeasurable homeomorphism, which transports counts,
integrals and vague coordinates and is continuous and measurable; in particular, global
translation of point measures on `ℝ`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Set
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The count field is determined by the underlying measure. -/
theorem vaguePointMeasure_eq_of_measure_eq (ξ η : VaguePointMeasure X)
    (h : ξ.measure = η.measure) : ξ = η := by
  rcases ξ with ⟨μ, hf, hi, c, hc⟩
  rcases η with ⟨ν, hg, hj, d, hd⟩
  change μ = ν at h
  cases h
  have hcd : c = d := by
    funext A
    have he : (c A : ENNReal) = (d A : ENNReal) := (hc A).symm.trans (hd A)
    exact_mod_cast he
  cases hcd
  rfl

omit [MeasurableSpace X] in
/-- A homeomorphism preserves compactness of arbitrary inverse images. -/
theorem isCompact_preimage_vagueHomeomorph (e : X ≃ₜ X) (K : Set X)
    (hK : IsCompact K) : IsCompact (e ⁻¹' K) := by
  have hs : e ⁻¹' K = e.symm '' K := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [Set.mem_preimage, e.apply_symm_apply] using hy
  rw [hs]
  exact hK.image e.symm.continuous

/-- Pullback of a relatively compact measurable set. -/
def vagueHomeomorphPullback (e : X ≃ₜ X) (he : Measurable e)
    (A : RelativelyCompactBorelSet X) : RelativelyCompactBorelSet X where
  carrier := e ⁻¹' A.carrier
  measurable := A.measurable.preimage he
  compact_closure := by
    apply (isCompact_preimage_vagueHomeomorph e (closure A.carrier) A.compact_closure).of_isClosed_subset
      isClosed_closure
    exact closure_minimal (Set.preimage_mono subset_closure)
      (isClosed_closure.preimage e.continuous)

/-- The measurable equivalence associated to a bimeasurable homeomorphism. -/
def vagueMeasurableEquiv (e : X ≃ₜ X) (he : Measurable e) (hi : Measurable e.symm) : X ≃ᵐ X where
  toEquiv := e.toEquiv
  measurable_toFun := he
  measurable_invFun := hi

/-- Pushforward of a point measure, including infinite total mass. -/
def vagueHomeomorphPushforward (e : X ≃ₜ X) (he : Measurable e) (hi : Measurable e.symm)
    (ξ : VaguePointMeasure X) : VaguePointMeasure X where
  measure := Measure.map (vagueMeasurableEquiv e he hi) ξ.measure
  finite_on_compact := by
    intro K hK
    rw [(vagueMeasurableEquiv e he hi).map_apply]
    exact ξ.finite_on_compact _ (isCompact_preimage_vagueHomeomorph e K hK)
  integer_valued := by
    intro A hA
    rw [(vagueMeasurableEquiv e he hi).map_apply]
    exact ξ.integer_valued _ (hA.preimage he)
  count := fun A => ξ.count (vagueHomeomorphPullback e he A)
  measure_eq_count := by
    intro A
    rw [(vagueMeasurableEquiv e he hi).map_apply]
    exact ξ.measure_eq_count (vagueHomeomorphPullback e he A)

/-- Full measure transport, on all sets rather than just stored windows. -/
theorem vagueHomeomorphPushforward_apply (e : X ≃ₜ X) (he : Measurable e)
    (hi : Measurable e.symm) (ξ : VaguePointMeasure X) (A : Set X) :
    (vagueHomeomorphPushforward e he hi ξ).measure A = ξ.measure (e ⁻¹' A) :=
  (vagueMeasurableEquiv e he hi).map_apply A

/-- Exact count transport on every relatively compact measurable set. -/
theorem vagueHomeomorphPushforward_count (e : X ≃ₜ X) (he : Measurable e)
    (hi : Measurable e.symm) (ξ : VaguePointMeasure X) (A : RelativelyCompactBorelSet X) :
    (vagueHomeomorphPushforward e he hi ξ).count A = ξ.count (vagueHomeomorphPullback e he A) := rfl

/-- Bochner integral transport for arbitrary functions. -/
theorem vagueHomeomorphPushforward_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (e : X ≃ₜ X) (he : Measurable e) (hi : Measurable e.symm)
    (ξ : VaguePointMeasure X) (f : X → E) :
    (∫ x, f x ∂(vagueHomeomorphPushforward e he hi ξ).measure) = ∫ x, f (e x) ∂ξ.measure :=
  integral_map_equiv (vagueMeasurableEquiv e he hi) f

/-- Proper pullback of every compact continuous real test. -/
def vagueHomeomorphTestPullback (e : X ≃ₜ X) (f : CompactlySupportedContinuousMap X ℝ) :
    CompactlySupportedContinuousMap X ℝ where
  toFun := fun x => f (e x)
  continuous_toFun := f.continuous.comp e.continuous
  hasCompactSupport' := by
    apply (isCompact_preimage_vagueHomeomorph e (tsupport f) f.hasCompactSupport).of_isClosed_subset
      (isClosed_tsupport _)
    apply closure_minimal
    · intro x hx
      exact subset_tsupport f hx
    · exact (isClosed_tsupport f).preimage e.continuous

/-- Exact vague coordinate transport by compact-test precomposition. -/
theorem vagueHomeomorphPushforward_coordinate (e : X ≃ₜ X) (he : Measurable e)
    (hi : Measurable e.symm) (ξ : VaguePointMeasure X)
    (f : CompactlySupportedContinuousMap X ℝ) :
    (vagueHomeomorphPushforward e he hi ξ).coordinate f =
      ξ.coordinate (vagueHomeomorphTestPullback e f) :=
  vagueHomeomorphPushforward_integral e he hi ξ f

/-- Each defining coordinate is continuous in the induced vague topology. -/
theorem continuous_vaguePointMeasure_coordinate (f : CompactlySupportedContinuousMap X ℝ) :
    Continuous (fun ξ : VaguePointMeasure X => ξ.coordinate f) := by
  have hc : Continuous (fun ξ : VaguePointMeasure X =>
      fun g : CompactlySupportedContinuousMap X ℝ => ξ.coordinate g) := continuous_induced_dom
  exact (continuous_apply f).comp hc

/-- Global fixed-homeomorphism continuity on all point configurations. -/
theorem continuous_vagueHomeomorphPushforward (e : X ≃ₜ X) (he : Measurable e)
    (hi : Measurable e.symm) : Continuous (vagueHomeomorphPushforward e he hi) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro f
  simp_rw [Function.comp_apply, vagueHomeomorphPushforward_coordinate]
  exact continuous_vaguePointMeasure_coordinate (vagueHomeomorphTestPullback e f)

/-- The action of a fixed homeomorphism is Borel measurable. -/
theorem measurable_vagueHomeomorphPushforward (e : X ≃ₜ X) (he : Measurable e)
    (hi : Measurable e.symm) : Measurable (vagueHomeomorphPushforward e he hi) :=
  (continuous_vagueHomeomorphPushforward e he hi).measurable

/-- Real spectral translation as a proper homeomorphism. -/
def realSpectralTranslationHomeomorph (s : ℝ) : ℝ ≃ₜ ℝ where
  toFun := fun x => x + s
  invFun := fun x => x - s
  left_inv := by intro x; dsimp; ring
  right_inv := by intro x; dsimp; ring
  continuous_toFun := continuous_id.add continuous_const
  continuous_invFun := continuous_id.sub continuous_const

/-- Global spectral translation of a real point measure. -/
def realVagueTranslation (s : ℝ) (ξ : VaguePointMeasure ℝ) : VaguePointMeasure ℝ :=
  vagueHomeomorphPushforward (realSpectralTranslationHomeomorph s)
    (measurable_id.add_const s) (measurable_id.sub_const s) ξ

theorem realVagueTranslation_apply (s : ℝ) (ξ : VaguePointMeasure ℝ) (A : Set ℝ) :
    (realVagueTranslation s ξ).measure A = ξ.measure ((fun x => x+s) ⁻¹' A) :=
  vagueHomeomorphPushforward_apply _ _ _ ξ A

theorem realVagueTranslation_zero (ξ : VaguePointMeasure ℝ) : realVagueTranslation 0 ξ = ξ := by
  apply vaguePointMeasure_eq_of_measure_eq
  ext A hA
  rw [realVagueTranslation_apply]
  simp

theorem realVagueTranslation_add (s t : ℝ) (ξ : VaguePointMeasure ℝ) :
    realVagueTranslation s (realVagueTranslation t ξ) = realVagueTranslation (s+t) ξ := by
  apply vaguePointMeasure_eq_of_measure_eq
  ext A hA
  simp only [realVagueTranslation_apply, Set.preimage_preimage]
  congr 1
  ext x
  change (x+t+s ∈ A) ↔ (x+(s+t) ∈ A)
  rw [show x+t+s = x+(s+t) by ring]

theorem realVagueTranslation_inverse (s : ℝ) (ξ : VaguePointMeasure ℝ) :
    realVagueTranslation (-s) (realVagueTranslation s ξ) = ξ := by
  rw [realVagueTranslation_add, neg_add_cancel, realVagueTranslation_zero]

theorem continuous_realVagueTranslation (s : ℝ) : Continuous (realVagueTranslation s) :=
  continuous_vagueHomeomorphPushforward _ _ _

theorem measurable_realVagueTranslation (s : ℝ) : Measurable (realVagueTranslation s) :=
  (continuous_realVagueTranslation s).measurable

/-- Exact real-line compact-window count transport. -/
theorem realVagueTranslation_count (s : ℝ) (ξ : VaguePointMeasure ℝ)
    (A : RelativelyCompactBorelSet ℝ) :
    (realVagueTranslation s ξ).count A = ξ.count
      (vagueHomeomorphPullback (realSpectralTranslationHomeomorph s) (measurable_id.add_const s) A) := rfl

/-- Exact real-line complete-vector Bochner change of variables. -/
theorem realVagueTranslation_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (s : ℝ) (ξ : VaguePointMeasure ℝ) (f : ℝ → E) :
    (∫ x, f x ∂(realVagueTranslation s ξ).measure) = ∫ x, f (x+s) ∂ξ.measure :=
  vagueHomeomorphPushforward_integral _ _ _ ξ f

/-- Exact real-line defining vague coordinate transport. -/
theorem realVagueTranslation_coordinate (s : ℝ) (ξ : VaguePointMeasure ℝ)
    (f : CompactlySupportedContinuousMap ℝ ℝ) :
    (realVagueTranslation s ξ).coordinate f = ξ.coordinate
      (vagueHomeomorphTestPullback (realSpectralTranslationHomeomorph s) f) :=
  vagueHomeomorphPushforward_coordinate _ _ _ ξ f

/-- The fixed real point-configuration translation is itself a homeomorphism. -/
def realVagueTranslationHomeomorph (s : ℝ) : VaguePointMeasure ℝ ≃ₜ VaguePointMeasure ℝ where
  toFun := realVagueTranslation s
  invFun := realVagueTranslation (-s)
  left_inv := realVagueTranslation_inverse s
  right_inv := by
    intro ξ
    simpa only [neg_neg] using realVagueTranslation_inverse (-s) ξ
  continuous_toFun := continuous_realVagueTranslation s
  continuous_invFun := continuous_realVagueTranslation (-s)

end BlockBand.Model.Construction
