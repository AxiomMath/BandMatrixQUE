module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECanonicalWegner

/-!
# Tonelli interval assembly for the canonical GUE Wegner passage

This module isolates the exact nonnegative energy/sample Tonelli estimate used
after the Ward bound.  It keeps all measurability assumptions explicit and
uses the half-open interval whose volume is exactly its length.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

/-- A pointwise sample-average bound integrates over a finite energy interval
with precisely the interval-length factor.  This is the nonnegative Tonelli
step, so neither integrability nor a hidden Fubini hypothesis is required. -/
theorem lintegral_lintegral_Ioc_le_length_mul
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (f : Ω → ℝ → ℝ≥0∞) {a b : ℝ} (_hab : a ≤ b) (K : ℝ≥0∞)
    (hf : Measurable (Function.uncurry f))
    (havg : ∀ x ∈ Set.Ioc a b, (∫⁻ ω, f ω x ∂μ) ≤ K) :
    (∫⁻ ω, ∫⁻ x in Set.Ioc a b, f ω x ∂volume ∂μ) ≤
      ENNReal.ofReal (b - a) * K := by
  rw [MeasureTheory.lintegral_lintegral_swap hf.aemeasurable]
  calc
    (∫⁻ x, ∫⁻ ω, f ω x ∂μ ∂volume.restrict (Set.Ioc a b)) ≤
        ∫⁻ _x, K ∂volume.restrict (Set.Ioc a b) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact havg x hx
    _ = ENNReal.ofReal (b - a) * K := by
      rw [lintegral_const]
      simp [Real.volume_Ioc, mul_comm]

end PSSSNative.BlockBand.PSSS
