module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeFiniteSetTail
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Maximal inequality for continuous grid sums

Sampling along a dense sequence of times in `[0, T]` identifies the event `{sup_{u ≤ T} |X_u| > ε}`
for a continuous grid sum, which therefore satisfies the maximal bound by its predictable energy.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration

/-- A dense sequence in the time horizon `[0, T]`. -/
def horizonDensePoints (T : ℝ≥0) : ℕ → Set.Icc (0 : ℝ≥0) T := by
  letI : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨⟨0, zero_le, zero_le⟩⟩
  exact denseSeq (Set.Icc (0 : ℝ≥0) T)

theorem horizonDensePoints_dense (T : ℝ≥0) : DenseRange (horizonDensePoints T) := by
  let : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨⟨0, zero_le, zero_le⟩⟩
  exact denseRange_denseSeq (Set.Icc (0 : ℝ≥0) T)

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}
namespace GridPresentation

omit [IsProbabilityMeasure μ] in
/-- The supremum event of a continuous grid sum is the union over the dense times. -/
theorem continuousIntegral_tail_eq_iUnion (d : GridPresentation (κ := κ) μ T) (ε : ℝ≥0) :
    {x : DriverSample S κ | ∃ u ≤ T, ((ε^2 : ℝ≥0) : ℝ) < (d.continuousIntegral u x)^2} =
    ⋃ n : ℕ, {x | ∃ i < n, ((ε^2 : ℝ≥0) : ℝ) <
      (d.continuousIntegral (horizonDensePoints T i).val x)^2} := by
  ext x
  constructor
  · rintro ⟨u, hu, hε⟩
    have hc : Continuous (fun v : Set.Icc (0 : ℝ≥0) T =>
        (d.continuousIntegral v.val x)^2) :=
      ((d.continuousIntegral_continuous x).comp continuous_subtype_val).pow 2
    have ho : IsOpen {v : Set.Icc (0 : ℝ≥0) T |
        ((ε^2 : ℝ≥0) : ℝ) < (d.continuousIntegral v.val x)^2} :=
      isOpen_lt continuous_const hc
    rcases (horizonDensePoints_dense T).exists_mem_open ho ⟨⟨u, zero_le, hu⟩, hε⟩ with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i + 1, i, Nat.lt_succ_self i, hi⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, i, hi, hε⟩
    exact ⟨(horizonDensePoints T i).val, (horizonDensePoints T i).property.2, hε⟩

/-- The maximal tail of a continuous grid sum is bounded by its predictable energy, uniformly in
the grid presentation. -/
theorem continuousIntegral_maximal_tail (d : GridPresentation (κ := κ) μ T) (ε : ℝ≥0) :
    (ε^2 : ℝ≥0) * (driverLaw (κ := κ) μ)
      {x | ∃ u ≤ T, ((ε^2 : ℝ≥0) : ℝ) < (d.continuousIntegral u x)^2} ≤
      ENNReal.ofReal (‖d.predictableFamily‖^2) := by
  let E : ℕ → Set (DriverSample S κ) := fun n => {x | ∃ i < n,
    ((ε^2 : ℝ≥0) : ℝ) < (d.continuousIntegral (horizonDensePoints T i).val x)^2}
  have hmono : Monotone E := by
    intro n m hnm x hx
    rcases hx with ⟨i, hi, hε⟩
    exact ⟨i, hi.trans_le hnm, hε⟩
  have hb (n : ℕ) : (ε^2 : ℝ≥0) * (driverLaw (κ := κ) μ) (E n) ≤
      ENNReal.ofReal (‖d.predictableFamily‖^2) := by
    let F : Finset ℝ≥0 := (Finset.range n).image (fun i => (horizonDensePoints T i).val)
    have hFT : ∀ t ∈ F, t ≤ T := by
      intro t ht
      rcases Finset.mem_image.mp ht with ⟨i, _, rfl⟩
      exact (horizonDensePoints T i).property.2
    refine (mul_le_mul_right (measure_mono ?_) (↑(ε^2) : ℝ≥0∞)).trans
      (d.continuousIntegral_finiteSet_tail F hFT ε)
    intro x hx
    rcases hx with ⟨i, hi, hε⟩
    exact ⟨(horizonDensePoints T i).val,
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩, hε.le⟩
  rw [d.continuousIntegral_tail_eq_iUnion ε]
  change (ε^2 : ℝ≥0) * (driverLaw (κ := κ) μ) (⋃ n, E n) ≤ _
  rw [hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le hb

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
