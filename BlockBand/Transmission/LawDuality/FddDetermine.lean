module

public import BlockBand.Transmission.LawDuality.FddTilt
public import BlockBand.Transmission.LawDuality.FddReduce

/-!
# Tilted ratio transforms determine a joint law

A `k`-time version of `map_eq_of_sameRatioTransforms`, proved by tilting rather than by a
new Stone–Weierstrass argument. Let `Y : Ω → α` (`α` Borel, with outer approximations of
closed sets, e.g. `Fin k → FM[0,1]`) and `V : Ω → FM[0,1]`, and the same on `Ω'`. Assume
`P.map Y = P'.map Y'` and, for every bounded continuous `ψ ≥ 0` on `α` and every interior
`(x, y)` (`SameTiltedRatioTransforms`):
`E[ψ(Y) F_{x,y}(V)] = E'[ψ(Y') F_{x,y}(V')]`. Then (**`map_prod_eq_of_sameTilted`**)
`P.map (Y, V) = P'.map (Y', V')`.

Proof: tilting both sides by `ψ(Y)/Eψ(Y)` and applying `map_eq_of_sameRatioTransforms` gives
`E[ψ(Y)1_B(V)] = E'[ψ(Y')1_B(V')]` for measurable `B` (`integral_mul_indicator_eq`); hence the
finite measures `A ↦ P(Y ∈ A, V ∈ B)` agree (`map_restrict_eq`, nonnegative bounded continuous
tests); hence the two laws agree on measurable rectangles.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal BoundedContinuousFunction

/-- **Tilted ratio transforms agree.** -/
def SameTiltedRatioTransforms {α Ω Ω' : Type*} [TopologicalSpace α] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (Y : Ω → α) (V : Ω → FiniteMeasure unitInterval)
    (P' : Measure Ω') (Y' : Ω' → α) (V' : Ω' → FiniteMeasure unitInterval) : Prop :=
  ∀ ψ : α →ᵇ ℝ, (∀ a, 0 ≤ ψ a) → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
    ∫ ω, ψ (Y ω) * transmissionRatio x y (V ω) ∂P =
      ∫ ω, ψ (Y' ω) * transmissionRatio x y (V' ω) ∂P'

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [HasOuterApproxClosed α]
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω → α} {Y' : Ω' → α}
  {V : Ω → FiniteMeasure unitInterval} {V' : Ω' → FiniteMeasure unitInterval}

omit [HasOuterApproxClosed α] in
theorem integrable_bcf_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Y : Ω → α} (hY : Measurable Y) (ψ : α →ᵇ ℝ) : Integrable (fun ω => ψ (Y ω)) P :=
  Integrable.of_bound (ψ.continuous.measurable.comp hY).aestronglyMeasurable ‖ψ‖
    (ae_of_all _ fun _ => ψ.norm_coe_le_norm _)

omit [HasOuterApproxClosed α] in
theorem integral_mul_eq_zero_of_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {Y : Ω → α} (hY : Measurable Y) (ψ : α →ᵇ ℝ) (h0 : ∀ ω, 0 ≤ ψ (Y ω))
    (hz : ∫ ω, ψ (Y ω) ∂P = 0) (g : Ω → ℝ) : ∫ ω, ψ (Y ω) * g ω ∂P = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg h0 (integrable_bcf_comp hY ψ)).1 hz
  exact integral_eq_zero_of_ae (hae.mono fun ω hω => by
    simp only [Pi.zero_apply] at hω; simp only [hω, zero_mul, Pi.zero_apply])

omit [HasOuterApproxClosed α] in
/-- **Tilted indicator integrals agree.** -/
theorem integral_mul_indicator_eq (hY : Measurable Y) (hY' : Measurable Y') (hV : Measurable V)
    (hV' : Measurable V') (hmap : P.map Y = P'.map Y')
    (h : SameTiltedRatioTransforms P Y V P' Y' V') (ψ : α →ᵇ ℝ) (hψ : ∀ a, 0 ≤ ψ a)
    {B : Set (FiniteMeasure unitInterval)} (hB : MeasurableSet B) :
    ∫ ω, ψ (Y ω) * B.indicator (fun _ => (1 : ℝ)) (V ω) ∂P =
      ∫ ω, ψ (Y' ω) * B.indicator (fun _ => (1 : ℝ)) (V' ω) ∂P' := by
  have hm : Measurable fun ω => ψ (Y ω) := ψ.continuous.measurable.comp hY
  have hm' : Measurable fun ω => ψ (Y' ω) := ψ.continuous.measurable.comp hY'
  have h0 : ∀ ω, 0 ≤ ψ (Y ω) := fun ω => hψ _
  have h0' : ∀ ω, 0 ≤ ψ (Y' ω) := fun ω => hψ _
  have hb : ∀ a, ψ a ≤ ‖ψ‖ := fun a =>
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ψ.norm_coe_le_norm _)
  have hc : ∫ ω, ψ (Y ω) ∂P = ∫ ω, ψ (Y' ω) ∂P' := by
    rw [← integral_map hY.aemeasurable ψ.continuous.aestronglyMeasurable, hmap,
      integral_map hY'.aemeasurable ψ.continuous.aestronglyMeasurable]
  obtain ⟨c, hcdef⟩ : ∃ c, ∫ ω, ψ (Y ω) ∂P = c := ⟨_, rfl⟩
  have hcdef' : ∫ ω, ψ (Y' ω) ∂P' = c := hc.symm.trans hcdef
  rcases (hcdef ▸ integral_nonneg h0 : 0 ≤ c).eq_or_lt with hc0 | hcpos
  · rw [integral_mul_eq_zero_of_integral_eq_zero hY ψ h0 (hcdef.trans hc0.symm),
      integral_mul_eq_zero_of_integral_eq_zero hY' ψ h0' (hcdef'.trans hc0.symm)]
  · have := isProbabilityMeasure_tilt hm h0 (fun ω => hb _) hcpos hcdef
    have := isProbabilityMeasure_tilt hm' h0' (fun ω => hb _) hcpos hcdef'
    have hQ := map_eq_of_sameRatioTransforms (P := tiltMeasure P (fun ω => ψ (Y ω)) c) hV
      (P' := tiltMeasure P' (fun ω => ψ (Y' ω)) c) hV' fun p x y hxy => by
        rw [integral_tiltMeasure hm h0 hcpos, integral_tiltMeasure hm' h0' hcpos,
          h ψ hψ p x y hxy]
    have hi : ∫ ω, B.indicator (fun _ => (1 : ℝ)) (V ω) ∂tiltMeasure P (fun ω => ψ (Y ω)) c =
        ∫ ω, B.indicator (fun _ => (1 : ℝ)) (V' ω) ∂tiltMeasure P' (fun ω => ψ (Y' ω)) c := by
      rw [← integral_map hV.aemeasurable (measurable_const.indicator hB).aestronglyMeasurable, hQ,
        integral_map hV'.aemeasurable (measurable_const.indicator hB).aestronglyMeasurable]
    rw [integral_tiltMeasure hm h0 hcpos, integral_tiltMeasure hm' h0' hcpos] at hi
    exact mul_left_cancel₀ (inv_ne_zero hcpos.ne') hi

/-- `f : α →ᵇ ℝ≥0` as a real bounded continuous function. -/
def bcfToReal (f : α →ᵇ ℝ≥0) : α →ᵇ ℝ :=
  ⟨⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩, f.map_bounded'⟩

omit [HasOuterApproxClosed α] in
theorem lintegral_map_restrict {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Y : Ω → α} (hY : Measurable Y) {V : Ω → FiniteMeasure unitInterval} (hV : Measurable V)
    {B : Set (FiniteMeasure unitInterval)} (hB : MeasurableSet B) (f : α →ᵇ ℝ≥0) :
    ∫⁻ a, f a ∂(P.restrict (V ⁻¹' B)).map Y =
      ENNReal.ofReal (∫ ω, bcfToReal f (Y ω) * B.indicator (fun _ => (1 : ℝ)) (V ω) ∂P) := by
  have hi : Integrable (fun ω => ((f (Y ω) : ℝ≥0) : ℝ)) (P.restrict (V ⁻¹' B)) :=
    (integrable_bcf_comp hY (bcfToReal f)).restrict
  have hfm : Measurable fun a => (f a : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp f.continuous).measurable
  rw [lintegral_map hfm hY,
    lintegral_coe_eq_integral _ hi, ← integral_indicator (hV hB)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  beta_reduce
  by_cases hω : V ω ∈ B
  · rw [indicator_of_mem (show ω ∈ V ⁻¹' B from hω), indicator_of_mem hω, mul_one]; rfl
  · rw [indicator_of_notMem (show ω ∉ V ⁻¹' B from hω), indicator_of_notMem hω, mul_zero]

/-- **The finite measures `A ↦ P(Y ∈ A, V ∈ B)` agree.** -/
theorem map_restrict_eq (hY : Measurable Y) (hY' : Measurable Y') (hV : Measurable V)
    (hV' : Measurable V') (hmap : P.map Y = P'.map Y')
    (h : SameTiltedRatioTransforms P Y V P' Y' V') {B : Set (FiniteMeasure unitInterval)}
    (hB : MeasurableSet B) : (P.restrict (V ⁻¹' B)).map Y = (P'.restrict (V' ⁻¹' B)).map Y' := by
  refine ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun f => ?_
  rw [lintegral_map_restrict hY hV hB, lintegral_map_restrict hY' hV' hB,
    integral_mul_indicator_eq hY hY' hV hV' hmap h (bcfToReal f) (fun a => NNReal.coe_nonneg _) hB]

/-- **Tilted ratio transforms determine the joint law of `(Y, V)`.** -/
theorem map_prod_eq_of_sameTilted (hY : Measurable Y) (hY' : Measurable Y') (hV : Measurable V)
    (hV' : Measurable V') (hmap : P.map Y = P'.map Y')
    (h : SameTiltedRatioTransforms P Y V P' Y' V') :
    P.map (fun ω => (Y ω, V ω)) = P'.map (fun ω => (Y' ω, V' ω)) := by
  have hm := hY.prodMk hV
  have hm' := hY'.prodMk hV'
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    have e := congrArg (fun m : Measure α => m A) (map_restrict_eq hY hY' hV hV' hmap h hB)
    rw [Measure.map_apply hY hA, Measure.map_apply hY' hA, Measure.restrict_apply (hY hA),
      Measure.restrict_apply (hY' hA)] at e
    rw [Measure.map_apply hm (hA.prod hB), Measure.map_apply hm' (hA.prod hB), mk_preimage_prod,
      mk_preimage_prod, e]
  · rw [Measure.map_apply hm MeasurableSet.univ, Measure.map_apply hm' MeasurableSet.univ,
      preimage_univ, preimage_univ, measure_univ, measure_univ]

end BlockBand.Transmission.LawDuality
