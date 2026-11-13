module

public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ERAdmissibility
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Erdős–Riabov control-kernel ingredients

Scalar and site-level ingredients of the Erdős–Riabov admissible-control-function contract
(Definitions 2.4–2.5 of Erdős–Riabov, *The zigzag strategy for random band matrices*), with the
source normalization `N = p.L = p.n * p.W`.

* `erSemicircleStieltjes`: the semicircle Stieltjes transform, given in the upper half-plane by
  ER's principal-square-root formula and in the lower half-plane by its Schwarz reflection. It
  solves the Dyson equation `m² + z m + 1 = 0` (`erSemicircleStieltjes_dyson`), satisfies
  `Im m · Im z > 0` (`erSemicircleStieltjes_same_sign`) and `|m| < 1`
  (`norm_erSemicircleStieltjes_lt_one`) at every nonreal `z`.
* `erComplexVarianceProfile`, `erLocalizationLength` (`ℓ(η) = min (W/√η, N)`, ER (2.15)) and
  `erSiteDistance` (the circular distance `|x-y|_N` of ER (2.25)).
* `ERControlFamily`: the data of a control family, a real matrix indexed by the height.

The seven-clause contract itself is cited: `ERDefinition24Control` and its variant with the
logarithmic loss permitted in ER Example 2.7, `ERDefinition24ControlWithConvolutionLoss`, are
declared in `BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing

open scoped BigOperators

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The explicit algebraic formula used by ER in the upper half-plane.  The
principal square root is selected according to the sign of the real part. -/
def erSemicircleStieltjesUpperFormula (z : ℂ) : ℂ :=
  if z.re < 0 then
    (-z - Complex.sqrt (z ^ 2 - 4)) / 2
  else
    (-z + Complex.sqrt (z ^ 2 - 4)) / 2

/-- The source-faithful semicircle Stieltjes transform.  In the upper half-plane
this is ER's displayed principal-square-root formula; in the lower half-plane it is
its Schwarz reflection.  Thus `(Im m(z)) (Im z) > 0` for every nonreal `z`. -/
def erSemicircleStieltjes (z : ℂ) : ℂ :=
  if z.im < 0 then
    starRingEnd ℂ (erSemicircleStieltjesUpperFormula (starRingEnd ℂ z))
  else
    erSemicircleStieltjesUpperFormula z

/-- Exact compatibility with the upper-half-plane formula throughout the closed upper half-plane. -/
theorem erSemicircleStieltjes_eq_upperFormula_of_im_nonneg {z : ℂ}
    (hz : 0 ≤ z.im) :
    erSemicircleStieltjes z = erSemicircleStieltjesUpperFormula z := by
  unfold erSemicircleStieltjes
  split
  · rename_i h
    linarith
  · rfl

/-- Exact reflected formula throughout the open lower half-plane. -/
theorem erSemicircleStieltjes_eq_conj_upperFormula_conj_of_im_neg {z : ℂ}
    (hz : z.im < 0) :
    erSemicircleStieltjes z =
      starRingEnd ℂ (erSemicircleStieltjesUpperFormula (starRingEnd ℂ z)) := by
  unfold erSemicircleStieltjes
  split
  · rfl
  · rename_i h
    exact False.elim (h hz)

/-- Schwarz reflection symmetry away from the real axis. -/
theorem erSemicircleStieltjes_conj {z : ℂ} (hz : z.im ≠ 0) :
    erSemicircleStieltjes (starRingEnd ℂ z) =
      starRingEnd ℂ (erSemicircleStieltjes z) := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · rw [erSemicircleStieltjes_eq_conj_upperFormula_conj_of_im_neg hzneg]
    have hconj : 0 ≤ (starRingEnd ℂ z).im := by simp; linarith
    rw [erSemicircleStieltjes_eq_upperFormula_of_im_nonneg hconj]
    simp
  · rw [erSemicircleStieltjes_eq_upperFormula_of_im_nonneg hzpos.le]
    have hconj : (starRingEnd ℂ z).im < 0 := by simp; linarith
    rw [erSemicircleStieltjes_eq_conj_upperFormula_conj_of_im_neg hconj]
    simp

/-- Upper-half-plane sign control transfers exactly to the sign-dependent lower branch. -/
theorem herglotz_sign_of_lower_reflection {z : ℂ} (hz : z.im < 0)
    (hupper : 0 <
      (erSemicircleStieltjesUpperFormula (starRingEnd ℂ z)).im *
        (starRingEnd ℂ z).im) :
    0 < (erSemicircleStieltjes z).im * z.im := by
  rw [erSemicircleStieltjes_eq_conj_upperFormula_conj_of_im_neg hz]
  rw [Complex.conj_im]
  rw [Complex.conj_im] at hupper
  nlinarith

/-- On the upper half-plane, the sign statement for `erSemicircleStieltjes` is definitionally the one for
`erSemicircleStieltjesUpperFormula`. -/
theorem herglotz_sign_of_upper {z : ℂ} (hz : 0 < z.im)
    (hupper : 0 < (erSemicircleStieltjesUpperFormula z).im * z.im) :
    0 < (erSemicircleStieltjes z).im * z.im := by
  rw [erSemicircleStieltjes_eq_upperFormula_of_im_nonneg hz.le]
  exact hupper

/-- `erSemicircleStieltjesUpperFormula` solves the semicircle Dyson equation `m² + z m + 1 = 0`. -/
theorem erSemicircleStieltjesUpperFormula_dyson (z : ℂ) :
    erSemicircleStieltjesUpperFormula z ^ 2 + z * erSemicircleStieltjesUpperFormula z + 1 = 0 := by
  unfold erSemicircleStieltjesUpperFormula
  split <;> rename_i h
  · have hs : (Complex.sqrt (z ^ 2 - 4)) ^ 2 = z ^ 2 - 4 := by
      simp [Complex.sqrt]
    field_simp
    linear_combination hs
  · have hs : (Complex.sqrt (z ^ 2 - 4)) ^ 2 = z ^ 2 - 4 := by
      simp [Complex.sqrt]
    field_simp
    linear_combination hs

/-- The sign-dependent branch preserves the exact Dyson equation in both half-planes. -/
theorem erSemicircleStieltjes_dyson (z : ℂ) :
    erSemicircleStieltjes z ^ 2 +
      z * erSemicircleStieltjes z + 1 = 0 := by
  by_cases hz : z.im < 0
  · rw [erSemicircleStieltjes_eq_conj_upperFormula_conj_of_im_neg hz]
    have h := erSemicircleStieltjesUpperFormula_dyson (starRingEnd ℂ z)
    have hc := congrArg (starRingEnd ℂ) h
    simpa [map_add, map_mul, map_pow] using hc
  · rw [erSemicircleStieltjes_eq_upperFormula_of_im_nonneg (le_of_not_gt hz)]
    exact erSemicircleStieltjesUpperFormula_dyson z

/-- The imaginary part of the principal square root of the semicircle
discriminant dominates the spectral height in absolute value. -/
theorem spectral_discriminant_sqrt_im_gap {z : ℂ} (hz : 0 < z.im) :
    z.im < |(Complex.sqrt (z ^ 2 - 4)).im| := by
  let d : ℂ := z ^ 2 - 4
  let R : ℝ := z.re ^ 2 + z.im ^ 2 - 4
  have hdre : d.re = z.re ^ 2 - z.im ^ 2 - 4 := by
    simp [d, pow_two]
  have hdim : d.im = 2 * z.re * z.im := by
    simp [d, pow_two]
    ring
  have hnormsq : ‖d‖ ^ 2 = R ^ 2 + 16 * z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    rw [hdre, hdim]
    simp only [R]
    ring
  have hnorm_gt : R < ‖d‖ := by
    by_cases hR : R < 0
    · exact lt_of_lt_of_le hR (norm_nonneg d)
    · have hR0 : 0 ≤ R := le_of_not_gt hR
      have hy2 : 0 < z.im ^ 2 := sq_pos_of_pos hz
      nlinarith [sq_nonneg (‖d‖ - R), norm_nonneg d]
  have hsq : z.im ^ 2 < (‖d‖ - d.re) / 2 := by
    rw [hdre]
    simp only [R] at hnorm_gt
    nlinarith
  have hrad : 0 ≤ (‖d‖ - d.re) / 2 := by
    have := Complex.re_le_norm d
    linarith
  have hsqrt_gap : z.im < Real.sqrt ((‖d‖ - d.re) / 2) := by
    exact (Real.lt_sqrt hz.le).2 hsq
  by_cases hx : 0 ≤ z.re
  · have hd_im : 0 ≤ d.im := by rw [hdim]; positivity
    have hsqrt_im :
        (Complex.sqrt d).im = Real.sqrt ((‖d‖ - d.re) / 2) := by
      simpa [Complex.sqrt] using Complex.cpow_inv_two_im_eq_sqrt hd_im
    rw [show z ^ 2 - 4 = d by rfl, hsqrt_im, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hsqrt_gap
  · have hd_im : d.im < 0 := by
      rw [hdim]
      have hx' : z.re < 0 := lt_of_not_ge hx
      nlinarith
    have hsqrt_im :
        (Complex.sqrt d).im = -Real.sqrt ((‖d‖ - d.re) / 2) := by
      simpa [Complex.sqrt] using Complex.cpow_inv_two_im_eq_neg_sqrt hd_im
    rw [show z ^ 2 - 4 = d by rfl, hsqrt_im, abs_neg,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hsqrt_gap

/-- The checked-in principal-square-root formula is the Herglotz root throughout
the open upper half-plane. -/
theorem erSemicircleStieltjesUpperFormula_upper_sign {z : ℂ} (hz : 0 < z.im) :
    0 < (erSemicircleStieltjesUpperFormula z).im * z.im := by
  have hgap := spectral_discriminant_sqrt_im_gap hz
  unfold erSemicircleStieltjesUpperFormula
  split <;> rename_i hx
  · have hsqrt_nonpos : (Complex.sqrt (z ^ 2 - 4)).im ≤ 0 := by
      have hd : (z ^ 2 - 4).im < 0 := by
        simp [pow_two]
        nlinarith
      rw [show Complex.sqrt (z ^ 2 - 4) =
        (z ^ 2 - 4) ^ (2⁻¹ : ℂ) by rfl,
        Complex.cpow_inv_two_im_eq_neg_sqrt hd]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    rw [abs_of_nonpos hsqrt_nonpos] at hgap
    simp
    nlinarith
  · have hx' : 0 ≤ z.re := le_of_not_gt hx
    have hsqrt_nonneg : 0 ≤ (Complex.sqrt (z ^ 2 - 4)).im := by
      have hd : 0 ≤ (z ^ 2 - 4).im := by
        simp [pow_two]
        nlinarith
      rw [show Complex.sqrt (z ^ 2 - 4) =
        (z ^ 2 - 4) ^ (2⁻¹ : ℂ) by rfl,
        Complex.cpow_inv_two_im_eq_sqrt hd]
      exact Real.sqrt_nonneg _
    rw [abs_of_nonneg hsqrt_nonneg] at hgap
    simp
    nlinarith

/-- The sign-dependent branch has the Herglotz sign on both open half-planes. -/
theorem erSemicircleStieltjes_same_sign {z : ℂ} (hz : z.im ≠ 0) :
    0 < (erSemicircleStieltjes z).im * z.im := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · apply herglotz_sign_of_lower_reflection hzneg
    apply erSemicircleStieltjesUpperFormula_upper_sign
    simpa using neg_pos.mpr hzneg
  · exact herglotz_sign_of_upper hzpos
      (erSemicircleStieltjesUpperFormula_upper_sign hzpos)

/-- Pure algebraic Herglotz criterion: a solution of the semicircle Dyson equation
whose imaginary part has the sign of the spectral parameter necessarily lies strictly
inside the unit disk. -/
theorem norm_lt_one_of_dyson_and_same_sign {z m : ℂ}
    (hroot : m ^ 2 + z * m + 1 = 0)
    (hsign : 0 < m.im * z.im) : ‖m‖ < 1 := by
  have hm : m ≠ 0 := by
    intro hm
    subst m
    norm_num at hroot
  have hz : z = -(m + m⁻¹) := by
    apply (mul_right_cancel₀ hm)
    field_simp
    linear_combination hroot
  have him : z.im = m.im * (1 / Complex.normSq m - 1) := by
    rw [hz]
    simp only [Complex.neg_im, Complex.add_im, Complex.inv_im]
    field_simp [ne_of_gt (Complex.normSq_pos.mpr hm)]
    ring
  have hmim : m.im ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsign
    exact (lt_irrefl 0 hsign)
  have hfactor : 0 < 1 / Complex.normSq m - 1 := by
    rw [him] at hsign
    have hsquare : 0 < m.im ^ 2 := sq_pos_of_ne_zero hmim
    nlinarith
  have hnormsq : Complex.normSq m < 1 := by
    have hsqpos : 0 < Complex.normSq m := Complex.normSq_pos.mpr hm
    have hone : 1 < (Complex.normSq m)⁻¹ := by
      rw [← one_div]
      linarith
    exact (one_lt_inv₀ hsqpos).mp hone
  rw [Complex.normSq_eq_norm_sq] at hnormsq
  nlinarith [norm_nonneg m]

/-- Sharp unit-disc bound for the sign-dependent explicit branch, assuming the Herglotz sign
condition `Im m · Im z > 0`. -/
theorem norm_erSemicircleStieltjes_lt_one_of_same_sign {z : ℂ}
    (hsign : 0 < (erSemicircleStieltjes z).im * z.im) :
    ‖erSemicircleStieltjes z‖ < 1 :=
  norm_lt_one_of_dyson_and_same_sign
    (erSemicircleStieltjes_dyson z) hsign

/-- Sharp unit-disc bound for the sign-dependent branch at every nonreal spectral
parameter, with no half-plane restriction. -/
theorem norm_erSemicircleStieltjes_lt_one {z : ℂ} (hz : z.im ≠ 0) :
    ‖erSemicircleStieltjes z‖ < 1 :=
  norm_erSemicircleStieltjes_lt_one_of_same_sign
    (erSemicircleStieltjes_same_sign hz)

/-- The site variance profile, coerced entrywise to `ℂ`. -/
def erComplexVarianceProfile (p : Params) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  fun x y => varianceProfile p x y

/-- ER (2.15)'s localization length `ℓ(η) = min {W/√η, N}`. -/
def erLocalizationLength (p : Params) (η : ℝ) : ℝ :=
  min ((p.W : ℝ) / Real.sqrt η) (p.L : ℝ)

/-- Circular site distance `|x-y|_N` in ER (2.25), using the row-major
identification of the `nW` product sites with a cycle of length `N = p.L`. -/
def erSiteDistance (p : Params) (x y : Site p.n p.W) : ℕ :=
  let _ := p.nNeZero
  let i := (p.siteIndexEquiv x).val
  let j := (p.siteIndexEquiv y).val
  let d := max i j - min i j
  min d (p.L - d)

/-- An ER control family is an explicitly indexed real matrix family.  Positivity,
symmetry, its height range, and every analytic requirement live in
`ERDefinition24Control`; they are not built into this data alias. -/
abbrev ERControlFamily (p : Params) :=
  ℝ → Matrix (Site p.n p.W) (Site p.n p.W) ℝ

end GaussianRing
end ERNative.BlockBand
