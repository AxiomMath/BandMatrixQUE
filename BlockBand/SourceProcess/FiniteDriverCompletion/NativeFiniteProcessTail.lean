module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeFiniteProcess
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeContinuousTail

/-!
# Maximal inequality for finite processes

The finite process of a finite-grid class satisfies the maximal tail bound on `[0, T]` by its
predictable energy.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)

/-- The maximal tail of a finite process is bounded by its predictable energy. -/
theorem nativeFiniteProcess_maximal_tail (f : nativeFinitePredictable (κ := κ) μ T) (ε : ℝ≥0) :
    (ε^2 : ℝ≥0) * (driverLaw (κ := κ) μ)
      {x | ∃ u ≤ T, ((ε^2 : ℝ≥0) : ℝ) < (nativeFiniteProcess μ T f u x)^2} ≤
      ENNReal.ofReal (‖f.val‖^2) := by
  classical
  by_cases h : ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d
  · have hp : nativeFiniteProcess μ T f = h.choose.continuousIntegral := by
      simp only [nativeFiniteProcess, dite_eq_left h]
    have hf : h.choose.predictableFamily = f.val := (congrArg Subtype.val h.choose_spec).symm
    rw [hp]
    have ht := h.choose.continuousIntegral_maximal_tail ε
    rw [hf] at ht
    exact ht
  · have hp : nativeFiniteProcess μ T f = 0 := by
      simp only [nativeFiniteProcess, dite_eq_right h]
    have hn : ‖f.val‖ = 0 := by
      have hf := (nativeFinite_zero_or_presentation μ T f).resolve_right h
      rw [hf]
      simp only [Submodule.coe_zero, norm_zero]
    rw [hp, hn]
    have he : {x : DriverSample S κ | ∃ u ≤ T, ((ε^2 : ℝ≥0) : ℝ) < (0 : ℝ≥0 → DriverSample S κ → ℝ) u x ^ 2} = ∅ := by
      ext x
      simp only [Pi.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      constructor
      · rintro ⟨u, _, hu⟩
        exact not_lt_of_ge (NNReal.coe_nonneg (ε^2)) hu
      · exact False.elim
    rw [he, measure_empty, mul_zero]
    exact zero_le

end BlockBand.SourceProcess.FiniteDriverCompletion
