module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEProjectedCompressionTail

/-!
# Weighted event transport through an exact product law

This module isolates the measure-theoretic transport used by the weighted
fixed-vector proof.  An almost-everywhere event implication is transported
through a measurable map with an exact pushforward law, while retaining an
arbitrary nonnegative measurable weight on the target coordinate.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory Set Filter
open scoped ENNReal

/-- Weighted event domination under an exact measurable pushforward. -/
theorem lintegral_indicator_weight_comp_le_of_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (M : Measure Y) (f : X → Y) (hf : Measurable f)
    (B : Set X) (E : Set Y) (hE : MeasurableSet E)
    (W : Y → ℝ≥0∞) (hW : Measurable W)
    (hmap : Measure.map f P = M)
    (hsub : ∀ᵐ x ∂P, x ∈ B → f x ∈ E) :
    (∫⁻ x, Set.indicator B (fun _ => (1 : ℝ≥0∞)) x * W (f x) ∂P) ≤
      ∫⁻ y, Set.indicator E (fun _ => (1 : ℝ≥0∞)) y * W y ∂M := by
  have hmono :
      (fun x => Set.indicator B (fun _ => (1 : ℝ≥0∞)) x * W (f x)) ≤ᵐ[P]
        (fun x => Set.indicator E (fun _ => (1 : ℝ≥0∞)) (f x) * W (f x)) := by
    filter_upwards [hsub] with x hx
    by_cases hxB : x ∈ B
    · have hxE := hx hxB
      simp [Set.indicator, hxB, hxE]
    · simp [Set.indicator, hxB]
  calc
    (∫⁻ x, Set.indicator B (fun _ => (1 : ℝ≥0∞)) x * W (f x) ∂P) ≤
        ∫⁻ x, Set.indicator E (fun _ => (1 : ℝ≥0∞)) (f x) * W (f x) ∂P :=
      lintegral_mono_ae hmono
    _ = ∫⁻ y, Set.indicator E (fun _ => (1 : ℝ≥0∞)) y * W y ∂M := by
      rw [← hmap]
      exact (lintegral_map'
        ((measurable_const.indicator hE).mul hW).aemeasurable
        hf.aemeasurable).symm

/-- The same transport with a source weight known pointwise to be the pullback
of the target weight. -/
theorem lintegral_indicator_weight_le_of_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (M : Measure Y) (f : X → Y) (hf : Measurable f)
    (B : Set X) (E : Set Y) (hE : MeasurableSet E)
    (U : X → ℝ≥0∞) (W : Y → ℝ≥0∞) (hW : Measurable W)
    (hUW : ∀ x, U x = W (f x))
    (hmap : Measure.map f P = M)
    (hsub : ∀ᵐ x ∂P, x ∈ B → f x ∈ E) :
    (∫⁻ x, Set.indicator B (fun _ => (1 : ℝ≥0∞)) x * U x ∂P) ≤
      ∫⁻ y, Set.indicator E (fun _ => (1 : ℝ≥0∞)) y * W y ∂M := by
  simp_rw [hUW]
  exact lintegral_indicator_weight_comp_le_of_map P M f hf B E hE W hW hmap hsub

end PSSSNative.BlockBand.PSSS
