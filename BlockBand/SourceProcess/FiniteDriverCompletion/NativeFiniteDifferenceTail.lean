module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeFiniteProcessTail

/-!
# Maximal inequality for differences of finite processes

The difference of the finite processes of two finite-grid classes satisfies the maximal tail bound
by the predictable energy of the difference.
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

/-- The maximal tail of the difference of two finite processes is bounded by the predictable
energy of the difference. -/
theorem nativeFiniteProcess_difference_tail
    (f g : nativeFinitePredictable (κ := κ) μ T) (ε : ℝ≥0) :
    (ε^2 : ℝ≥0) * (driverLaw (κ := κ) μ)
      {x | ∃ u ≤ T, ((ε^2 : ℝ≥0) : ℝ) <
        (nativeFiniteProcess μ T f u x - nativeFiniteProcess μ T g u x)^2} ≤
      ENNReal.ofReal (‖f.val - g.val‖^2) := by
  classical
  by_cases hg : ∃ e : GridPresentation (κ := κ) μ T, g = nativePresentationClass μ T e
  · by_cases hf : ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d
    · let D := hf.choose.add (hg.choose.smul (-1))
      have hD : D.continuousIntegral = nativeFiniteProcess μ T f - nativeFiniteProcess μ T g := by
        rw [GridPresentation.continuousIntegral_add, GridPresentation.continuousIntegral_smul]
        simp only [nativeFiniteProcess, dite_eq_left hf, dite_eq_left hg,
          neg_one_smul, sub_eq_add_neg]
      have hpred : D.predictableFamily = f.val - g.val := by
        rw [GridPresentation.predictableFamily_add, GridPresentation.predictableFamily_smul]
        have hpf : hf.choose.predictableFamily = f.val := (congrArg Subtype.val hf.choose_spec).symm
        have hpg : hg.choose.predictableFamily = g.val := (congrArg Subtype.val hg.choose_spec).symm
        rw [hpf, hpg]
        apply PiLp.ext
        intro a
        simp only [PiLp.add_apply, sub_eq_add_neg]
        change f.val a + (-1 : ℝ) • g.val a = f.val a + -g.val a
        exact congrArg (fun z => f.val a + z) (neg_one_smul ℝ (g.val a))
      have ht := D.continuousIntegral_maximal_tail ε
      rw [hpred, hD] at ht
      simpa only [Pi.sub_apply] using ht
    · have hzero : f = 0 := (nativeFinite_zero_or_presentation μ T f).resolve_right hf
      have hp : nativeFiniteProcess μ T f = 0 := by
        simp only [nativeFiniteProcess, dite_eq_right hf]
      have hval : f.val = 0 := by simpa only [Submodule.coe_zero] using congrArg Subtype.val hzero
      have ht := nativeFiniteProcess_maximal_tail μ T g ε
      simpa only [hp, hval, Pi.zero_apply, zero_sub, neg_sq, norm_neg] using ht
  · have hzero : g = 0 := (nativeFinite_zero_or_presentation μ T g).resolve_right hg
    have hp : nativeFiniteProcess μ T g = 0 := by
      simp only [nativeFiniteProcess, dite_eq_right hg]
    have hval : g.val = 0 := by simpa only [Submodule.coe_zero] using congrArg Subtype.val hzero
    have ht := nativeFiniteProcess_maximal_tail μ T f ε
    simpa only [hp, hval, Pi.zero_apply, sub_zero] using ht

end BlockBand.SourceProcess.FiniteDriverCompletion
