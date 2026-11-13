module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeMaximalTail

/-!
# Maximal inequality over finite sets of times

Sorting a finite set of times into a monotone sampling sequence, the discrete maximal inequality
gives the maximal tail bound of a continuous grid sum over every finite set of times in `[0, T]`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration

/-- The monotone sampling sequence of a nonempty finite set of times, constant after its largest
element. -/
def sortedFiniteSampling (F : Finset ℝ≥0) (hF : F.Nonempty) (n : ℕ) : ℝ≥0 :=
  (F.orderIsoOfFin rfl) ⟨min n (F.card - 1), by have := Finset.card_pos.mpr hF; omega⟩

theorem sortedFiniteSampling_monotone (F : Finset ℝ≥0) (hF : F.Nonempty) :
    Monotone (sortedFiniteSampling F hF) := by
  intro i j hij
  apply (F.orderIsoOfFin rfl).monotone
  change min i (F.card - 1) ≤ min j (F.card - 1)
  exact min_le_min_right _ hij

theorem sortedFiniteSampling_mem (F : Finset ℝ≥0) (hF : F.Nonempty) (n : ℕ) :
    sortedFiniteSampling F hF n ∈ F := (F.orderIsoOfFin rfl _).property

/-- Every time of the set occurs in the sampling sequence. -/
theorem sortedFiniteSampling_covers (F : Finset ℝ≥0) (hF : F.Nonempty)
    (t : ℝ≥0) (ht : t ∈ F) :
    ∃ i < F.card, sortedFiniteSampling F hF i = t := by
  let i := (F.orderIsoOfFin rfl).symm ⟨t, ht⟩
  refine ⟨i.val, i.isLt, ?_⟩
  have hi : i.val ≤ F.card - 1 := by have := i.isLt; omega
  unfold sortedFiniteSampling
  simp only [min_eq_left hi]
  exact congrArg Subtype.val ((F.orderIsoOfFin rfl).apply_symm_apply ⟨t, ht⟩)

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}
namespace GridPresentation

/-- The maximal energy bound over every finite set of times in the horizon. -/
theorem continuousIntegral_finiteSet_tail (d : GridPresentation (κ := κ) μ T)
    (F : Finset ℝ≥0) (hFT : ∀ t ∈ F, t ≤ T) (ε : ℝ≥0) :
    (ε^2 : ℝ≥0) * (driverLaw (κ := κ) μ)
      {x | ∃ t ∈ F, ((ε^2 : ℝ≥0) : ℝ) ≤ (d.continuousIntegral t x)^2} ≤
      ENNReal.ofReal (‖d.predictableFamily‖^2) := by
  by_cases hF : F.Nonempty
  · let q := sortedFiniteSampling F hF
    have hq := sortedFiniteSampling_monotone F hF
    have htail := d.continuousIntegral_finite_maximal_tail q hq (F.card - 1)
      (hFT _ (sortedFiniteSampling_mem F hF _)) ε
    refine (mul_le_mul_right (measure_mono ?_) (ε^2 : ℝ≥0∞)).trans htail
    intro x hx
    rcases hx with ⟨t, ht, hε⟩
    rcases sortedFiniteSampling_covers F hF t ht with ⟨i, hi, hit⟩
    change ((ε^2 : ℝ≥0) : ℝ) ≤ (Finset.range (F.card - 1 + 1)).sup'
      Finset.nonempty_range_add_one (fun k => (d.continuousIntegral (q k) x)^2)
    apply (Finset.le_sup'_iff Finset.nonempty_range_add_one).mpr
    refine ⟨i, Finset.mem_range.mpr (by have := Finset.card_pos.mpr hF; omega), ?_⟩
    simpa only [q, hit] using hε
  · have he : {x : DriverSample S κ | ∃ t ∈ F,
        ((ε^2 : ℝ≥0) : ℝ) ≤ (d.continuousIntegral t x)^2} = ∅ := by
      ext x
      simp [Finset.not_nonempty_iff_eq_empty.mp hF]
    rw [he, measure_empty, mul_zero]
    exact zero_le

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
