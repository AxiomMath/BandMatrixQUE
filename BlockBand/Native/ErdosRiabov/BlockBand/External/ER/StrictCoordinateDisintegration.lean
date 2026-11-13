module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ActualWardBound

/-!
# Strict-coordinate product disintegration for the Gaussian ring

This module upgrades upper-entry independence to the concrete real-coordinate
product laws used by Gaussian integration by parts.  A strict upper entry is
split into its real and imaginary coordinates and the complementary upper
array; a diagonal entry is split into its real coordinate and complement.
The resulting pushforward measures are products, so arbitrary joint
resolvent tests may be treated by Fubini.  We also prove entrywise
measurability of the coordinate-removed Hermitian background.

No local law, stochastic domination, moment recursion, or Ward
estimate is assumed.

Source: Erdős–Riabov, arXiv:2506.06441v1, coordinate conditioning in the
fluctuation-averaging proof of Theorem 3.3.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERStrictCoordinateDisintegration

open Matrix MeasureTheory ProbabilityTheory
open ERProductCoordinateAnalysis ERGaussianCoordinate

local instance (p : Params) : NeZero p.n := p.nNeZero
local instance (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance (p : Params) : Fintype (UpperPair p) := Fintype.ofFinite _
local instance (p : Params) : DecidableEq (UpperPair p) := Classical.decEq _

/-- Evaluation of the singleton tuple at its unique coordinate. -/
def selectedUpperEntry {p : Params} (q : UpperPair p)
    (u : (r : ({q} : Finset (UpperPair p))) → ℂ) : ℂ :=
  u ⟨q, Finset.mem_singleton_self q⟩

/-- Singleton evaluation is measurable. -/
theorem measurable_selectedUpperEntry {p : Params} (q : UpperPair p) :
    Measurable (selectedUpperEntry q) := by
  exact measurable_pi_apply _

@[simp] theorem selectedUpperEntry_singletonTuple
    {p : Params} (M : Law p) (q : UpperPair p) (ω : M.Ω) :
    selectedUpperEntry q (singletonTuple (upperEntryFamily M) q ω) =
      M.H ω q.1.1 q.1.2 := rfl

/-- A strict upper coordinate pair `(Re H_xy, Im H_xy)` is independent of all
other upper entries. -/
theorem Law.offdiagPair_indep_complement
    {p : Params} (M : Law p) (q : UpperPair p) :
    IndepFun
      (fun ω => ((M.H ω q.1.1 q.1.2).re, (M.H ω q.1.1 q.1.2).im))
      (complementTuple (upperEntryFamily M) q) M.P := by
  have h := (ERProductCoordinateAnalysis.Law.upperEntry_indep_complement M q).comp
    (show Measurable (fun u =>
      ((selectedUpperEntry q u).re, (selectedUpperEntry q u).im)) by
        exact
          (Complex.measurable_re.comp (measurable_selectedUpperEntry q)).prodMk
            (Complex.measurable_im.comp (measurable_selectedUpperEntry q)))
    measurable_id
  simpa [Function.comp_def] using h

/-- A diagonal real coordinate is independent of all other upper entries. -/
theorem Law.diagonalReal_indep_complement
    {p : Params} (M : Law p) (x : Site p.n p.W)
    (q : UpperPair p) (hq : q.1 = (x, x)) :
    IndepFun (fun ω => (M.H ω x x).re)
      (complementTuple (upperEntryFamily M) q) M.P := by
  have h := (ERProductCoordinateAnalysis.Law.upperEntry_indep_complement M q).comp
    (Complex.measurable_re.comp (measurable_selectedUpperEntry q))
    measurable_id
  have hx : q.1.1 = x := congrArg Prod.fst hq
  have hy : q.1.2 = x := congrArg Prod.snd hq
  simpa [Function.comp_def, hx, hy] using h

/-- For a strict upper coordinate, the coordinate-pair marginal is exactly the
product of its two normalized real Gaussian laws. -/
theorem Law.offdiagPair_gaussian_productLaw
    {p : Params} (M : Law p) (x y : Site p.n p.W)
    (hxy : siteLE p x y) (hne : x ≠ y) :
    M.P.map (fun ω => ((M.H ω x y).re, (M.H ω x y).im)) =
      (gaussianReal 0
        ⟨ERProfile.siteCovariance p x y / 2,
          div_nonneg (varianceProfile_nonneg p x y) (by norm_num)⟩).prod
      (gaussianReal 0
        ⟨ERProfile.siteCovariance p x y / 2,
          div_nonneg (varianceProfile_nonneg p x y) (by norm_num)⟩) := by
  have hlaws := actual_coordinate_laws M x y hxy hne
  have hprod := IndepFun.map_prod_eq_prod_map_map
    (Complex.measurable_re.comp (M.measurable_entry x y)).aemeasurable
    (Complex.measurable_im.comp (M.measurable_entry x y)).aemeasurable hlaws.2.2
  have hprod' :
      M.P.map (fun ω => ((M.H ω x y).re, (M.H ω x y).im)) =
        (M.P.map (fun ω => (M.H ω x y).re)).prod
          (M.P.map (fun ω => (M.H ω x y).im)) := by
    simpa only [Function.comp_def] using hprod
  rw [hlaws.1.map_eq, hlaws.2.1.map_eq] at hprod'
  exact hprod'

/-!
## One-dimensional IBP for arbitrary background-dependent tests
-/

/-- Conditional real-coordinate Gaussian IBP for an arbitrary test depending
jointly on the second coordinate and on a background parameter.  No separated
product representation of the test is required. -/
theorem gaussianIBP_jointTest_real
    {γ : Type*} (v : NNReal) (hv : v ≠ 0)
    (Φ dΦ : ℝ → ℝ → γ → ℂ)
    (hderiv : ∀ r s b, HasDerivAt (fun t => Φ t s b) (dΦ r s b) r)
    (s : ℝ) (b : γ)
    (hcoord : Integrable (fun r : ℝ =>
      ((r * gaussianPDFReal 0 v r : ℝ) : ℂ) * Φ r s b))
    (hderivInt : Integrable (fun r : ℝ =>
      ((gaussianPDFReal 0 v r : ℝ) : ℂ) * dΦ r s b))
    (htest : Integrable (fun r : ℝ =>
      ((gaussianPDFReal 0 v r : ℝ) : ℂ) * Φ r s b)) :
    (∫ r : ℝ, (r : ℂ) * Φ r s b ∂gaussianReal 0 v) =
      ((v : ℝ) : ℂ) * ∫ r : ℝ, dΦ r s b ∂gaussianReal 0 v := by
  exact ERLocalLaw.gaussian_ibp v hv (fun r => Φ r s b)
    (fun r => dΦ r s b) (fun r => hderiv r s b)
    hcoord hderivInt htest

/-- Conditional imaginary-coordinate Gaussian IBP for an arbitrary test
depending jointly on the real coordinate and background parameter. -/
theorem gaussianIBP_jointTest_imaginary
    {γ : Type*} (v : NNReal) (hv : v ≠ 0)
    (Φ dΦ : ℝ → ℝ → γ → ℂ)
    (hderiv : ∀ r s b, HasDerivAt (fun t => Φ r t b) (dΦ r s b) s)
    (r : ℝ) (b : γ)
    (hcoord : Integrable (fun s : ℝ =>
      ((s * gaussianPDFReal 0 v s : ℝ) : ℂ) * Φ r s b))
    (hderivInt : Integrable (fun s : ℝ =>
      ((gaussianPDFReal 0 v s : ℝ) : ℂ) * dΦ r s b))
    (htest : Integrable (fun s : ℝ =>
      ((gaussianPDFReal 0 v s : ℝ) : ℂ) * Φ r s b)) :
    (∫ s : ℝ, (s : ℂ) * Φ r s b ∂gaussianReal 0 v) =
      ((v : ℝ) : ℂ) * ∫ s : ℝ, dΦ r s b ∂gaussianReal 0 v := by
  exact ERLocalLaw.gaussian_ibp v hv (fun s => Φ r s b)
    (fun s => dΦ r s b) (fun s => hderiv r s b)
    hcoord hderivInt htest

end ERStrictCoordinateDisintegration
end GaussianRing
end ERNative.BlockBand
