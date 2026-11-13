module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiAbsorbedCountFormula
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerFrozenSchurAverage
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEBlockExpectedCountPoisson
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerPerronPassage

/-!
# Factorial-weighted Perron limit for the first Minami reduction

This module records the endpoint-sensitive regulator limit after multiplication
by a fixed natural weight.  In the induction this weight is the predecessor
compression factorial count.  Endpoint atoms are not discarded: their
vanishing is an explicit hypothesis, to be supplied almost surely by the
proved sharp Wegner theorem.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- Perron–Stieltjes inversion remains exact after multiplication by a fixed
natural (hence finite) factorial weight.  Both endpoint exclusions are kept
explicit. -/
theorem tendsto_weighted_integral_negImTrace_resolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : HermitianMatrix ι) {a b : ℝ} (hab : a < b)
    (ha : eigenCount H {a} = 0) (hb : eigenCount H {b} = 0)
    (q : ℕ) :
    Tendsto (fun eta : ℝ =>
      (q : ℝ≥0∞) * ENNReal.ofReal
        ((1 / Real.pi) * ∫ x : ℝ in a..b,
          -(((((H : Matrix ι ι ℂ) -
            (x : ℂ) • (1 : Matrix ι ι ℂ) +
            Complex.I • (eta • (1 : Matrix ι ι ℂ)))⁻¹).trace).im)))
      (𝓝[>] 0)
      (𝓝 ((q : ℝ≥0∞) * (eigenCount H (Icc a b) : ℝ≥0∞))) := by
  have hreal := tendsto_integral_neg_im_trace_resolvent H hab ha hb
  have hof := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hmul :=
    (ENNReal.continuous_const_mul (ENNReal.natCast_ne_top q)).continuousAt.tendsto.comp hof
  simpa only [Function.comp_def, ENNReal.ofReal_natCast] using hmul

/-- Sequential version along the repository's canonical positive regulators.
This is the form used under Fatou/Tonelli in the public block product. -/
theorem tendsto_weighted_canonicalEta_integral_negImTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : HermitianMatrix ι) {a b : ℝ} (hab : a < b)
    (ha : eigenCount H {a} = 0) (hb : eigenCount H {b} = 0)
    (q : ℕ) :
    Tendsto (fun n : ℕ =>
      (q : ℝ≥0∞) * ENNReal.ofReal
        ((1 / Real.pi) * ∫ x : ℝ in a..b,
          -(((((H : Matrix ι ι ℂ) -
            (x : ℂ) • (1 : Matrix ι ι ℂ) +
            Complex.I • (canonicalWegnerEta n •
              (1 : Matrix ι ι ℂ)))⁻¹).trace).im)))
      atTop
      (𝓝 ((q : ℝ≥0∞) * (eigenCount H (Icc a b) : ℝ≥0∞))) := by
  exact (tendsto_weighted_integral_negImTrace_resolvent H hab ha hb q).comp
    tendsto_canonicalWegnerEta_nhdsGT_zero

end PSSSNative.BlockBand.PSSS
