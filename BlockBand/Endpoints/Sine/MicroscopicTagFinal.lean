module

public import BlockBand.Endpoints.Sine.MicroscopicTagFinalCore

/-!
# The microscopic tag comparison from the contracts

* `microscopicTagLeadComparison_of_contracts`: `MicroscopicTagLeadComparison`, from `mts_core` by
  linearity: a signed bounded Lipschitz `Φ` is `(Φ + ‖Φ‖) - ‖Φ‖` (both nonnegative and
  Lipschitz), and a nonnegative weight `w` with `∫ w > 0` is `(∫ w)` times a window (if `∫ w = 0`
  then `w = 0` and both sides vanish).
* The final theorems combine it with `microscopicTagComparison`.

The hypotheses are `RingRotationInvariance`, `VanishingBlockAtom`, `FreshEigenpairDensityContract`,
`MatchedTracesContract`, `OneBlockPalmContract`, `OneBlockNormalizerContract`,
`UniformClockTagsPalmContract`, `ClockCovarianceStabilityContract`, `NegativeClockContract`,
`BlockRegularEventContract`, `UniformClockTagsCommonPortContract` and
`LeadFieldIdentificationContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.RingSymmetry
open scoped ENNReal NNReal BoundedContinuousFunction

/-!
## Linearity of the two sides
-/

section Linear

variable (p : Parameters) (E : ℝ)

theorem mts_integrable_physicalTag (model : p.GaussianRingModel) {w : ℝ → ℝ}
    (hwc : Continuous w) (hws : HasCompactSupport w) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (k : ZMod p.n) :
    Integrable (fun H => ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      Φ (Set.projIci 0 ((p.n : ℝ) * physicalOrderedBlockMass p H α k)))
      (model.law : Measure p.SiteMatrix) := by
  obtain ⟨C, hC⟩ := hwc.bounded_above_of_compact_support hws
  refine Integrable.of_bound (Finset.measurable_sum _ fun α _ =>
    (hwc.measurable.comp ((mts_measurable_microCoord p E).comp
      (mts_measurable_physicalOrderedEigenvalue p α))).mul (Φ.continuous.measurable.comp
      (continuous_projIci_zero.measurable.comp (measurable_const.mul
        (measurable_physicalOrderedBlockMass p α k))))).aestronglyMeasurable
    (p.N * (C * ‖Φ‖)) (ae_of_all _ fun H => ?_)
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _α : Fin p.N, C * ‖Φ‖ := Finset.sum_le_sum fun α _ => by
        rw [norm_mul]; exact mul_le_mul (hC _) (Φ.norm_coe_le_norm _) (norm_nonneg _)
          ((norm_nonneg _).trans (hC 0))
    _ = p.N * (C * ‖Φ‖) := by simp

theorem mts_physicalTagSide_add (model : p.GaussianRingModel) {w : ℝ → ℝ}
    (hwc : Continuous w) (hws : HasCompactSupport w) (Φ₁ Φ₂ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (k : ZMod p.n) :
    physicalTagSide p model E w (Φ₁ + Φ₂) k =
      physicalTagSide p model E w Φ₁ k + physicalTagSide p model E w Φ₂ k := by
  unfold physicalTagSide
  rw [← integral_add (mts_integrable_physicalTag p E model hwc hws Φ₁ k)
    (mts_integrable_physicalTag p E model hwc hws Φ₂ k)]
  congr 1; funext H
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [BoundedContinuousFunction.add_apply, mul_add]

theorem mts_leadTagSide_add {w : ℝ → ℝ} (hwc : Continuous w) (hws : HasCompactSupport w)
    (Φ₁ Φ₂ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    leadTagSide p E w (Φ₁ + Φ₂) = leadTagSide p E w Φ₁ + leadTagSide p E w Φ₂ := by
  have hPc := isProbabilityMeasure_probedClockLaw p.W p.b
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport hws
  have hpt : ∀ e x, leadAveragedTest p.b e p.n p.W (Φ₁ + Φ₂) x =
      leadAveragedTest p.b e p.n p.W Φ₁ x + leadAveragedTest p.b e p.n p.W Φ₂ x := by
    intro e x
    unfold leadAveragedTest
    simp only [BoundedContinuousFunction.add_apply, Finset.sum_add_distrib]
    ring
  have hi : ∀ (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (e : ℝ), Integrable
      (fun x => leadAveragedTest p.b e p.n p.W Φ x) (probedClockLaw p.W p.b) := fun Φ e =>
    Integrable.of_bound (measurable_leadAveragedTest_of p.b p.n p.W Φ measurable_const
      measurable_id).aestronglyMeasurable ‖Φ‖ (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact abs_leadAveragedTest_le _ _ p.n_ge_four _ Φ _)
  have hu : ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ, Integrable (fun u => w u *
      ∫ x, leadAveragedTest p.b (microEnergy p E u) p.n p.W Φ x ∂probedClockLaw p.W p.b) := by
    intro Φ
    have hb : ∀ u, ‖∫ x, leadAveragedTest p.b (microEnergy p E u) p.n p.W Φ x
        ∂probedClockLaw p.W p.b‖ ≤ ‖Φ‖ := fun u => by
      have h := norm_integral_le_of_norm_le_const (μ := probedClockLaw p.W p.b) (C := ‖Φ‖)
        (f := fun x => leadAveragedTest p.b (microEnergy p E u) p.n p.W Φ x)
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs]; exact abs_leadAveragedTest_le _ _ p.n_ge_four _ Φ _)
      simpa [probReal_univ] using h
    exact hwi.mul_bdd (measurable_leadAveragedTest_of p.b p.n p.W Φ
      ((mts_measurable_microEnergy p E).comp measurable_fst)
      measurable_snd).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (ae_of_all _ hb)
  unfold leadTagSide
  rw [← integral_add (hu Φ₁) (hu Φ₂)]
  congr 1; funext u
  simp only [hpt]
  rw [integral_add (hi Φ₁ _) (hi Φ₂ _), mul_add]

theorem mts_physicalTagSide_smul (model : p.GaussianRingModel) (c : ℝ) (w : ℝ → ℝ)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (k : ZMod p.n) :
    physicalTagSide p model E (fun u => c * w u) Φ k = c * physicalTagSide p model E w Φ k := by
  unfold physicalTagSide
  rw [← integral_const_mul]
  congr 1; funext H
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by ring

theorem mts_leadTagSide_smul (c : ℝ) (w : ℝ → ℝ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    leadTagSide p E (fun u => c * w u) Φ = c * leadTagSide p E w Φ := by
  unfold leadTagSide
  rw [← integral_const_mul]
  congr 1; funext u
  ring

end Linear

/-!
## Signed tests on a window
-/

/-- The lead comparison for a window and a signed bounded Lipschitz `Φ`. -/
theorem mts_window_signed (hRot : RingRotationInvariance) (hAtom : VanishingBlockAtom)
    (hPalm : OneBlockPalmContract) (hNorm : OneBlockNormalizerContract)
    (hFED : FreshEigenpairDensityContract) (hUCT : UniformClockTagsPalmContract)
    (hCS : ClockCovarianceStabilityContract) (hReg : BlockRegularEventContract)
    (hL : LeadFieldIdentificationContract) (hCP : UniformClockTagsCommonPortContract)
    (hMT : MatchedTracesContract) (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ)
    (hE1 : -2 < E) (hE2 : E < 2) {w : ℝ → ℝ} (hw : IsWindow w) {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ}
    {L : NNReal} (hLip : LipschitzWith L Φ) (τ : ℝ) (hτ : 0 < τ)
    (s : CriticalSequence τ) (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ k : ZMod (s.parameters b hb hb' j).n,
      |physicalTagSide (s.parameters b hb hb' j) (R j) E w Φ k -
          leadTagSide (s.parameters b hb hb' j) E w Φ| ≤ ε := by
  set Φc : Set.Ici (0 : ℝ) →ᵇ ℝ := BoundedContinuousFunction.const _ ‖Φ‖ with hΦcdef
  have hΦc0 : ∀ x, 0 ≤ Φc x := fun x => norm_nonneg Φ
  have hΦ0 : ∀ x, 0 ≤ (Φ + Φc) x := fun x => by
    rw [BoundedContinuousFunction.add_apply]
    have h := Φ.norm_coe_le_norm x
    rw [Real.norm_eq_abs] at h
    have : Φc x = ‖Φ‖ := rfl
    linarith [neg_abs_le (Φ x)]
  have hLc : LipschitzWith 0 Φc := LipschitzWith.of_dist_le_mul fun x y => by
    rw [show Φc x = Φc y from rfl, dist_self]; simp
  have hLp : LipschitzWith L (Φ + Φc) := LipschitzWith.of_dist_le_mul fun x y => by
    rw [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.add_apply,
      show Φc x = Φc y from rfl, dist_add_right]
    exact hLip.dist_le_mul x y
  have h1 := mts_core hRot hAtom hPalm hNorm hFED hUCT hCS hReg hL hCP hMT b hb hb' E hE1 hE2
    hw hΦ0 hLp τ hτ s R (ε / 2) (by positivity)
  have h2 := mts_core hRot hAtom hPalm hNorm hFED hUCT hCS hReg hL hCP hMT b hb hb' E hE1 hE2
    hw hΦc0 hLc τ hτ s R (ε / 2) (by positivity)
  filter_upwards [h1, h2] with j h1j h2j k
  have ep := mts_physicalTagSide_add (s.parameters b hb hb' j) E (R j) hw.1 hw.2.1 Φ Φc k
  have el := mts_leadTagSide_add (s.parameters b hb hb' j) E hw.1 hw.2.1 Φ Φc
  have a1 := abs_le.1 (h1j k)
  have a2 := abs_le.1 (h2j k)
  rw [ep, el] at a1
  exact abs_le.2 ⟨by linarith [a1.1, a2.2], by linarith [a1.2, a2.1]⟩

/-!
## The final theorems
-/

/-- **`MicroscopicTagLeadComparison`** (steps (1)–(4) of the microscopic tag comparison) from
the contracts in the signature.
-/
theorem microscopicTagLeadComparison_of_contracts (hRot : RingRotationInvariance)
    (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract) :
    MicroscopicTagLeadComparison := by
  intro b hb hb' E hE1 hE2 w hws hwc hw0 Φ hLip τ hτ s R ε hε
  obtain ⟨L, hLip⟩ := hLip
  have hwcont := hws.continuous
  have hwi : Integrable w := hwcont.integrable_of_hasCompactSupport hwc
  set I := ∫ u, w u with hIdef
  rcases (integral_nonneg hw0 : 0 ≤ I).lt_or_eq with hI | hI
  · set w' := fun u => I⁻¹ * w u with hw'def
    have hw' : IsWindow w' := by
      refine ⟨continuous_const.mul hwcont, ?_, fun u => mul_nonneg (inv_nonneg.2 hI.le) (hw0 u),
        ?_⟩
      · exact HasCompactSupport.mul_left (f := fun _ => I⁻¹) hwc
      · rw [hw'def, integral_const_mul, ← hIdef, inv_mul_cancel₀ hI.ne']
    have h := mts_window_signed hRot hAtom hPalm hNorm hFED hUCT hCS hReg hL hCP hMT b hb hb' E
      hE1 hE2 hw' hLip τ hτ s R (ε / I) (div_pos hε hI)
    filter_upwards [h] with j hj k
    have hw_eq : w = fun u => I * w' u := by
      funext u; rw [hw'def, ← mul_assoc, mul_inv_cancel₀ hI.ne', one_mul]
    rw [hw_eq, mts_physicalTagSide_smul, mts_leadTagSide_smul, ← mul_sub, abs_mul,
      abs_of_pos hI]
    calc I * |_| ≤ I * (ε / I) := mul_le_mul_of_nonneg_left (hj k) hI.le
      _ = ε := by rw [mul_div_assoc', mul_comm I ε, mul_div_assoc, div_self hI.ne', mul_one]
  · have hae := (integral_eq_zero_iff_of_nonneg hw0 hwi).1 hI.symm
    have hw00 : w = 0 := (Continuous.ae_eq_iff_eq volume hwcont continuous_zero).1 hae
    refine Eventually.of_forall fun j k => ?_
    have hp : physicalTagSide (s.parameters b hb hb' j) (R j) E w Φ k = 0 := by
      unfold physicalTagSide; rw [hw00]; simp
    have hl : leadTagSide (s.parameters b hb hb' j) E w Φ = 0 := by
      unfold leadTagSide; rw [hw00]; simp
    rw [hp, hl, sub_zero, abs_zero]
    exact hε.le

/-- **The microscopic tag comparison** from the contracts:
`microscopicTagLeadComparison_of_contracts` composed with `microscopicTagComparison`
(which uses `NegativeClockContract`).
-/
theorem microscopicTagComparison_of_contracts (hRot : RingRotationInvariance)
    (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hNeg : NegativeClockContract) : MicroscopicTagComparisonStatement :=
  microscopicTagComparison (microscopicTagLeadComparison_of_contracts hRot hAtom hPalm hNorm hFED
    hUCT hCS hReg hL hCP hMT) hNeg

end BlockBand.Endpoints
