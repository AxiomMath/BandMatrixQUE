module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerEndpointLimit
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.RankOneCompression
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorOperatorCorollary

/-!
# Positive rank-one conditioning core for factorial-count induction

This module fixes the order-indexed factorial-count proposition in the
public block-product representation and proves that its induction hypothesis is
stable under every deterministic positive rank-one deformation.  The interval
remains closed and unchanged.  These are the exact deterministic and integral
inputs used after the uniform-direction conditioning in the Minami step of PSSS
(Peled–Schenker–Shamis–Sodin).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- Order-`r` factorial-count estimate for the independent public GUE
block product.  The constant is chosen before the order and every dimension,
deformation, and closed interval. -/
def PublicFactorialAtOrder (C : ℝ) (r : ℕ) : Prop :=
  ∀ ⦃k : ℕ⦄ (dims : Fin k → ℕ), ∀ (hd : ∀ j, 0 < dims j),
  ∀ (A₀ : HermitianMatrix (BlockGUE.Index dims)) (a b : ℝ), a ≤ b →
  (∫⁻ G, ((eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b)).descFactorial r :
      ℝ≥0∞) ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
    ENNReal.ofReal (C * (∑ j, (dims j : ℝ)) * (b - a)) ^ r

/-- Rank-one shifting the deterministic deformation commutes exactly with
adding the sampled public block diagonal. -/
theorem rankOneShift_publicBlockDeformation {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (G : BlockGUE.PublicBlockSample dims)
    (u : EuclideanSpace ℂ (BlockGUE.Index dims)) (τ : ℝ) :
    rankOneShift (publicBlockDeformation A₀ G) u τ =
      publicBlockDeformation (rankOneShift A₀ u τ) G := by
  apply Subtype.ext
  simp only [rankOneShift, publicBlockDeformation]
  abel

/-- The Wegner estimate is exactly the order-one public factorial estimate. -/
theorem publicFactorialAtOrder_one_of_wegnerBound {C : ℝ}
    (hW : WegnerBound C) : PublicFactorialAtOrder C 1 := by
  intro k dims hd A₀ a b hab
  simpa only [Nat.descFactorial_one, pow_one] using hW dims hd A₀ a b hab

/-- Enlarging a nonnegative factorial-count constant preserves a fixed-order
estimate. -/
theorem PublicFactorialAtOrder.mono_constant {C C' : ℝ} {r : ℕ}
    (h : PublicFactorialAtOrder C r) (hCC' : C ≤ C') :
    PublicFactorialAtOrder C' r := by
  intro k dims hd A₀ a b hab
  refine (h dims hd A₀ a b hab).trans ?_
  apply pow_le_pow_left₀
  · exact bot_le
  · apply ENNReal.ofReal_le_ofReal
    have hdim : 0 ≤ ∑ j, (dims j : ℝ) := by positivity
    have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC' hdim) hlen

/-- The small-parameter branch in the weighted conditioning step is
completely deterministic: when `0 < t < 1` and `C ≥ 1`, the factor `C/t`
dominates one, so no inverse-tail estimate is needed. -/
theorem lintegral_indicator_mul_le_scaled_of_lt_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) (F : Ω → ℝ≥0∞) {C t : ℝ}
    (hC : 1 ≤ C) (ht : 0 < t) (ht1 : t < 1) :
    (∫⁻ ω, Set.indicator E (fun _ => (1 : ℝ≥0∞)) ω * F ω ∂μ) ≤
      ENNReal.ofReal (C / t) * ∫⁻ ω, F ω ∂μ := by
  have hcoef : 1 ≤ ENNReal.ofReal (C / t) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ ht).2
    nlinarith
  calc
    _ ≤ ∫⁻ ω, F ω ∂μ := by
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ E <;> simp [Set.indicator, hω]
    _ = 1 * ∫⁻ ω, F ω ∂μ := (one_mul _).symm
    _ ≤ ENNReal.ofReal (C / t) * ∫⁻ ω, F ω ∂μ :=
      mul_le_mul_of_nonneg_right hcoef bot_le

end PSSSNative.BlockBand.PSSS
