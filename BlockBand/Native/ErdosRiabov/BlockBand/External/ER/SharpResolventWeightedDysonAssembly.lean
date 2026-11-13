module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpResolventWeightedDiagonalIBP
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpCoordinateIndexReorganization

/-!
# Exact assembly of the resolvent-weighted Dyson coordinate expansion

This module combines the separately proved strict-upper and real-diagonal
Gaussian integration-by-parts identities.  It retains every profile factor,
variance half, resolvent order, and circular orientation before any Ward or
MDE-stability estimate is applied.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSharpCoordinateIBP

open Matrix MeasureTheory ProbabilityTheory
open ERGaussianCoordinate ERResolventMomentIBP ERProfile
open ERComplementBackgroundReconstruction ERConcrete
open scoped BigOperators NNReal Matrix.Norms.L2Operator

local instance (p : Params) : NeZero p.n := p.nNeZero
local instance (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance (p : Params) : Fintype (UpperPair p) := Fintype.ofFinite _
local instance (p : Params) : DecidableEq (UpperPair p) := Classical.decEq _

/-- The circular coordinate-weighted product test is integrable. -/
theorem Law.integrable_circularWeightedCoordinateResolventLowerTest_product
    {p : Params} (M : Law p) (q : UpperPair p)
    (hne : q.1.1 ≠ q.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun v => ((v.1.1 : ℂ) + Complex.I * (v.1.2 : ℂ)) *
      coordinateResolventLowerTest p v.2 q.1.1 q.1.2
        x y i j z m v.1.1 v.1.2)
      (strictCoordinateProductMeasure M q) := by
  have hr := Law.integrable_realWeightedCoordinateResolventLowerTest_product
    M q hne x y i j z hz m
  have hi := Law.integrable_imaginaryWeightedCoordinateResolventLowerTest_product
    M q hne x y i j z hz m
  refine (hr.add (hi.const_mul Complex.I)).congr ?_
  filter_upwards [] with v
  simp only [Pi.add_apply]
  ring

/-- Conjugate-circular coordinate-weighted product integrability. -/
theorem Law.integrable_conjugateCircularWeightedCoordinateResolventLowerTest_product
    {p : Params} (M : Law p) (q : UpperPair p)
    (hne : q.1.1 ≠ q.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun v => ((v.1.1 : ℂ) - Complex.I * (v.1.2 : ℂ)) *
      coordinateResolventLowerTest p v.2 q.1.1 q.1.2
        x y i j z m v.1.1 v.1.2)
      (strictCoordinateProductMeasure M q) := by
  have hr := Law.integrable_realWeightedCoordinateResolventLowerTest_product
    M q hne x y i j z hz m
  have hi := Law.integrable_imaginaryWeightedCoordinateResolventLowerTest_product
    M q hne x y i j z hz m
  refine (hr.sub (hi.const_mul Complex.I)).congr ?_
  filter_upwards [] with v
  simp only [Pi.sub_apply]
  ring

/-- Actual `H_ab G_ij` integrability transferred from the exact strict
coordinate/background product. -/
theorem Law.integrable_entryWeightedResolventLowerTest_actual
    {p : Params} (M : Law p) (q : UpperPair p)
    (hne : q.1.1 ≠ q.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun ω => M.H ω q.1.1 q.1.2 * green M z ω i j *
      lowerConjugateMomentTest m
        (ERFluctuationMoments.signedResolventError M z x y ω)) M.P := by
  let f := fun ω : M.Ω =>
    (((M.H ω q.1.1 q.1.2).re, (M.H ω q.1.1 q.1.2).im),
      offdiagBackground (M.H ω) q.1.1 q.1.2)
  let g := fun v : (ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
    ((v.1.1 : ℂ) + Complex.I * (v.1.2 : ℂ)) *
      coordinateResolventLowerTest p v.2 q.1.1 q.1.2
        x y i j z m v.1.1 v.1.2
  have hg : Integrable g (strictCoordinateProductMeasure M q) := by
    exact Law.integrable_circularWeightedCoordinateResolventLowerTest_product
      M q hne x y i j z hz m
  have hmap := Law.offdiagGaussian_background_productLaw M q hne
  have hmap' : Measure.map f M.P = strictCoordinateProductMeasure M q := by
    unfold strictCoordinateProductMeasure circularGaussianMeasure
      strictBackgroundMeasure
    rw [show (⟨siteCovariance p q.1.1 q.1.2,
        (siteCovariance_flat p q.1.1 q.1.2).1⟩ / 2 : NNReal) =
        ⟨siteCovariance p q.1.1 q.1.2 / 2,
          div_nonneg (siteCovariance_flat p q.1.1 q.1.2).1
            (by norm_num)⟩ by ext; rfl]
    exact hmap
  have hf : Measurable f := by
    exact (((Complex.measurable_re.comp
      (M.measurable_entry q.1.1 q.1.2)).prodMk
      (Complex.measurable_im.comp
        (M.measurable_entry q.1.1 q.1.2))).prodMk
      (Law.measurable_offdiagBackground_via_complement M q hne))
  have hc : Integrable (g ∘ f) M.P := by
    apply (integrable_map_measure
      (by rw [hmap']; exact hg.aestronglyMeasurable) hf.aemeasurable).mp
    rw [hmap']
    exact hg
  convert hc using 1
  funext ω
  simp only [Function.comp_apply, f, g]
  rw [coordinateResolventLowerTest_actual M q.1.1 q.1.2
    x y i j q.2 z hz.ne' m ω]
  have hreim : M.H ω q.1.1 q.1.2 =
      ((M.H ω q.1.1 q.1.2).re : ℂ) +
        Complex.I * (M.H ω q.1.1 q.1.2).im := by
    apply Complex.ext <;> simp
  nth_rewrite 1 [hreim]
  ring

/-- The reversed Hermitian orientation is integrable as well. -/
theorem Law.integrable_starEntryWeightedResolventLowerTest_actual
    {p : Params} (M : Law p) (q : UpperPair p)
    (hne : q.1.1 ≠ q.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun ω => M.H ω q.1.2 q.1.1 * green M z ω i j *
      lowerConjugateMomentTest m
        (ERFluctuationMoments.signedResolventError M z x y ω)) M.P := by
  let f := fun ω : M.Ω =>
    (((M.H ω q.1.1 q.1.2).re, (M.H ω q.1.1 q.1.2).im),
      offdiagBackground (M.H ω) q.1.1 q.1.2)
  let g := fun v : (ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
    ((v.1.1 : ℂ) - Complex.I * (v.1.2 : ℂ)) *
      coordinateResolventLowerTest p v.2 q.1.1 q.1.2
        x y i j z m v.1.1 v.1.2
  have hg : Integrable g (strictCoordinateProductMeasure M q) :=
    Law.integrable_conjugateCircularWeightedCoordinateResolventLowerTest_product
      M q hne x y i j z hz m
  have hmap := Law.offdiagGaussian_background_productLaw M q hne
  have hmap' : Measure.map f M.P = strictCoordinateProductMeasure M q := by
    unfold strictCoordinateProductMeasure circularGaussianMeasure
      strictBackgroundMeasure
    rw [show (⟨siteCovariance p q.1.1 q.1.2,
        (siteCovariance_flat p q.1.1 q.1.2).1⟩ / 2 : NNReal) =
        ⟨siteCovariance p q.1.1 q.1.2 / 2,
          div_nonneg (siteCovariance_flat p q.1.1 q.1.2).1
            (by norm_num)⟩ by ext; rfl]
    exact hmap
  have hf : Measurable f := by
    exact (((Complex.measurable_re.comp
      (M.measurable_entry q.1.1 q.1.2)).prodMk
      (Complex.measurable_im.comp
        (M.measurable_entry q.1.1 q.1.2))).prodMk
      (Law.measurable_offdiagBackground_via_complement M q hne))
  have hc : Integrable (g ∘ f) M.P := by
    apply (integrable_map_measure
      (by rw [hmap']; exact hg.aestronglyMeasurable) hf.aemeasurable).mp
    rw [hmap']
    exact hg
  convert hc using 1
  funext ω
  simp only [Function.comp_apply, f, g]
  rw [coordinateResolventLowerTest_actual M q.1.1 q.1.2
    x y i j q.2 z hz.ne' m ω]
  have hstar := (M.H_hermitian ω).apply q.1.2 q.1.1
  rw [← hstar]
  have hconj : star (M.H ω q.1.1 q.1.2) =
      ((M.H ω q.1.1 q.1.2).re : ℂ) -
        Complex.I * (M.H ω q.1.1 q.1.2).im := by
    apply Complex.ext <;> simp
  nth_rewrite 1 [hconj]
  ring

/-- Diagonal weighted-test integrability follows from the exact
diagonal product law. -/
theorem Law.integrable_diagonalEntryWeightedResolventLowerTest_actual
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun ω => M.H ω a a * green M z ω i j *
      lowerConjugateMomentTest m
        (ERFluctuationMoments.signedResolventError M z x y ω)) M.P := by
  let f := fun ω : M.Ω =>
    ((M.H ω a a).re, diagonalRealBackground (M.H ω) a)
  let g := fun v : ℝ × Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
    (v.1 : ℂ) * diagonalResolventLowerTest p v.2
      a x y i j z m v.1
  have hg : Integrable g (diagonalCoordinateProductMeasure M a) :=
    Law.integrable_realWeightedDiagonalResolventLowerTest_product
      M a x y i j z hz m
  have hmap : Measure.map f M.P = diagonalCoordinateProductMeasure M a := by
    exact Law.diagonalReal_background_productLaw M a
  have hf : Measurable f :=
    (Complex.measurable_re.comp (M.measurable_entry a a)).prodMk
      (Law.measurable_diagonalRealBackground M a)
  have hc : Integrable (g ∘ f) M.P := by
    apply (integrable_map_measure
      (by rw [hmap]; exact hg.aestronglyMeasurable) hf.aemeasurable).mp
    rw [hmap]
    exact hg
  convert hc using 1
  funext ω
  simp only [Function.comp_apply, f, g]
  rw [diagonalResolventLowerTest_actual M a x y i j z hz.ne' m ω]
  rw [hermitian_diag_eq_re (M.H ω) (M.isHermitian ω) a]
  ring

end ERSharpCoordinateIBP
end GaussianRing
end ERNative.BlockBand
