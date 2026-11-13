module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalGaussianRingCountingSequence

/-!
# Measurability of the physical Gaussian-ring vague state

The physical unfolded ordered spectrum is already a measurable finite product.
This module records the remaining bridge from a measurable finite configuration
to its sequence of sharply restricted finite counting measures.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory
open scoped Topology

/-- Restriction to a fixed measurable set is measurable for the Giry
measurable structure on finite measures.  Continuity is false for sharp
closed windows in general, but measurability is all that pushforward laws
require. -/
theorem measurable_finiteMeasure_restrict
    {X : Type*} [MeasurableSpace X] (S : Set X) (hS : MeasurableSet S) :
    Measurable (fun μ : FiniteMeasure X => μ.restrict S) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro T hT
  simp_rw [Measure.restrict_apply hT]
  exact (Measure.measurable_coe (hT.inter hS)).comp measurable_subtype_coe

/-- A finite labeled configuration has a measurable finite counting measure.
This is a finite sum of measurable bundled Dirac maps. -/
theorem measurable_finiteMarkedCountingMeasure
    {Mark : Type*} [MeasurableSpace Mark] (N : ℕ) :
    Measurable (finiteMarkedCountingMeasure :
      FiniteMarkedConfiguration N Mark →
        FiniteMeasure (MarkedSpectralSpace Mark)) := by
  unfold finiteMarkedCountingMeasure
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.measurable_sum
  intro i _hi
  have hi : Measurable (fun x : FiniteMarkedConfiguration N Mark =>
      Measure.dirac (x i) s) := by
    simp_rw [Measure.dirac_apply' _ hs]
    exact (measurable_one.indicator hs).comp (measurable_pi_apply i)
  exact hi

/-- The common sharp-window encoding of a finite configuration is measurable
coordinate by coordinate. -/
theorem measurable_finiteMarkedLocalWindowEncoding
    {Mark : Type*} [MeasurableSpace Mark] (N : ℕ) :
    Measurable (finiteMarkedLocalWindowEncoding :
      FiniteMarkedConfiguration N Mark → LocalWindowMeasureEncoding Mark) := by
  rw [measurable_pi_iff]
  intro n
  exact (measurable_finiteMeasure_restrict
      (markedSpectralWindow Mark n)
      (measurableSet_markedSpectralWindow Mark n)).comp
    (measurable_finiteMarkedCountingMeasure (Mark := Mark) N)

namespace GaussianRing

/-- The physical unfolded vague-state map is measurable.  Ordered
spectrum measurability supplies the finite configuration, while
`measurable_finiteMarkedLocalWindowEncoding` supplies every sharp-window
finite-measure coordinate and the product bridge. -/
theorem Law.measurable_physicalUnfoldedVagueState
    {p : Params} (M : Law p) (e L ρ : ℝ) :
    Measurable (M.physicalUnfoldedVagueState e L ρ) := by
  unfold Law.physicalUnfoldedVagueState
  exact (measurable_finiteMarkedLocalWindowEncoding
      (Fintype.card (BlockGUE.Index (physicalBlockSizes p)))).comp
    (M.measurable_physicalUnfoldedFiniteConfiguration e L ρ)

/-- Canonical physical vague law; its measurability is proved, not assumed. -/
def Law.physicalUnfoldedVagueLawCanonical
    {p : Params} (M : Law p) (e L ρ : ℝ) :
    ProbabilityMeasure VagueRationalWindowState :=
  M.physicalUnfoldedVagueLaw e L ρ
    (M.measurable_physicalUnfoldedVagueState e L ρ)

/-- Constructor for a physical counting sequence which derives, rather than
requests, measurability of every unfolded vague-state map.  The analytic
normalization and uniform lower-bound fields are unchanged. -/
def PhysicalGaussianRingCountingSequence.ofModels
    (input : PSSSInput.{0})
    (params : ℕ → Params)
    (model : ∀ i, Law.{0} (params i))
    (energy scale density : ℕ → ℝ)
    (scale_pos : ∀ i, 0 < scale i)
    (density_pos : ∀ i, 0 < density i)
    (dimension_le_scale : ∀ i,
      ((params i).n * (params i).W : ℝ) ≤ scale i)
    (sqrtCoupling_lower : ℝ)
    (sqrtCoupling_lower_pos : 0 < sqrtCoupling_lower)
    (sqrtCoupling_lower_le : ∀ i,
      sqrtCoupling_lower ≤ Real.sqrt (params i).c)
    (density_lower : ℝ)
    (density_lower_pos : 0 < density_lower)
    (density_lower_le : ∀ i, density_lower ≤ density i) :
    PhysicalGaussianRingCountingSequence input where
  params := params
  model := model
  energy := energy
  scale := scale
  density := density
  scale_pos := scale_pos
  density_pos := density_pos
  dimension_le_scale := dimension_le_scale
  state_measurable := fun i =>
    (model i).measurable_physicalUnfoldedVagueState
      (energy i) (scale i) (density i)
  sqrtCoupling_lower := sqrtCoupling_lower
  sqrtCoupling_lower_pos := sqrtCoupling_lower_pos
  sqrtCoupling_lower_le := sqrtCoupling_lower_le
  density_lower := density_lower
  density_lower_pos := density_lower_pos
  density_lower_le := density_lower_le

/-- The `state_measurable` field of any existing physical sequence is
mathematically redundant: the physical model APIs prove it directly. -/
theorem PhysicalGaussianRingCountingSequence.measurable_state_auto
    {input : PSSSInput.{0}} (seq : PhysicalGaussianRingCountingSequence input)
    (i : ℕ) : Measurable (seq.state i) := by
  exact (seq.model i).measurable_physicalUnfoldedVagueState
    (seq.energy i) (seq.scale i) (seq.density i)

end GaussianRing

end CoareaNative.BlockBand
