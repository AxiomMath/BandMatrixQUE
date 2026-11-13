module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib

/-!
# Erdős–Riabov control-kernel contract

No omitted estimate is asserted here.  In particular, the seven analytic clauses are
fields of an explicit `Prop` structure.  The proved specialization at the end says
only that the already verified cyclic profile supplies Definition 2.5's deterministic
profile component; a value of the seven-clause contract is still required explicitly.

Source fidelity notes:

* the spectral domain is exactly ER (2.9): the lower height, norm cutoff, and
  semicircle-phase separation are all retained;
* `Θ` and `Ξ` use ER (2.10), with the matrix fraction read as right multiplication by
  the nonsingular inverse;
* the fields `clause1` through `clause7` encode ER (2.18)--(2.27), including both
  choices `i ∈ {1,2}` in (2.25), the localized threshold, and the row-average
  subtraction in (2.26);
* `ERDefinition24ControlWithConvolutionLoss` exposes the logarithmic loss which
  ER Example 2.7 explicitly permits in (2.24)--(2.25), while
  `ERDefinition24Control` is the exact loss-one specialization.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
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

/-- A quantitative form of the algebraic Herglotz criterion.  The deliberately
coarse constant `1/4` is uniform in the real part of the spectral parameter and
is sufficient to expose the height-dependent radial margin needed by Green
kernel estimates. -/
theorem min_abs_im_div_four_le_one_sub_norm_of_dyson_and_same_sign
    {z m : ℂ}
    (hroot : m ^ 2 + z * m + 1 = 0)
    (hsign : 0 < m.im * z.im) :
    min (1 / 2 : ℝ) (|z.im| / 4) ≤ 1 - ‖m‖ := by
  have hm : m ≠ 0 := by
    intro hm
    subst m
    norm_num at hroot
  have htpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have htlt : ‖m‖ < 1 :=
    norm_lt_one_of_dyson_and_same_sign hroot hsign
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
    nlinarith [sq_pos_of_ne_zero hmim]
  have hyabs :
      |z.im| = |m.im| * (1 / ‖m‖ ^ 2 - 1) := by
    rw [him, abs_mul, abs_of_pos hfactor, Complex.normSq_eq_norm_sq]
  have hidentity :
      |z.im| * ‖m‖ ^ 2 = |m.im| * (1 - ‖m‖ ^ 2) := by
    rw [hyabs]
    field_simp [ne_of_gt htpos]
  have hone_minus_sq : 0 ≤ 1 - ‖m‖ ^ 2 := by
    nlinarith [norm_nonneg m]
  have him_le : |m.im| ≤ ‖m‖ := Complex.abs_im_le_norm m
  have hprod :
      |m.im| * (1 - ‖m‖ ^ 2) ≤ ‖m‖ * (1 - ‖m‖ ^ 2) :=
    mul_le_mul_of_nonneg_right him_le hone_minus_sq
  have hheight : |z.im| * ‖m‖ ≤ 1 - ‖m‖ ^ 2 := by
    nlinarith
  by_cases ht : ‖m‖ ≤ 1 / 2
  · exact le_trans (min_le_left _ _) (by linarith)
  · have hzabs : 0 < |z.im| := by
      rw [abs_pos]
      intro h
      rw [h, mul_zero] at hsign
      exact (lt_irrefl 0 hsign)
    have hquarter : |z.im| / 4 ≤ 1 - ‖m‖ := by
      nlinarith [sq_nonneg (1 - ‖m‖)]
    exact le_trans (min_le_right _ _) hquarter

/-- For the sign-dependent explicit branch, the Herglotz sign condition gives the sharp
unit-disk bound. -/
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

/-- Explicit height-dependent radial separation of the sign-dependent branch. -/
theorem min_abs_im_div_four_le_one_sub_norm_erSemicircleStieltjes
    {z : ℂ} (hz : z.im ≠ 0) :
    min (1 / 2 : ℝ) (|z.im| / 4) ≤
      1 - ‖erSemicircleStieltjes z‖ :=
  min_abs_im_div_four_le_one_sub_norm_of_dyson_and_same_sign
    (erSemicircleStieltjes_dyson z)
    (erSemicircleStieltjes_same_sign hz)

/-- ER (2.9), for the cyclic model of total size `N = p.L`.

The source fixes `κ, δ, C₀` (its `δ` is called `ηExp` here) before choosing spectral
parameters.  The norm cutoff is `|z| ≤ C₀`, not merely a bound on the real part. -/
def ERSpectralDomain (p : Params) (κ ηExp C₀ : ℝ) (z : ℂ) : Prop :=
  Real.rpow (p.L : ℝ) (-1 + ηExp) ≤ |z.im| ∧
    ‖z‖ ≤ C₀ ∧
    κ ≤ ‖(erSemicircleStieltjes z / ‖erSemicircleStieltjes z‖) ^ 2 - 1‖

/-- The site variance profile, coerced entrywise to `ℂ`. -/
def erComplexVarianceProfile (p : Params) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  fun x y => varianceProfile p x y

/-- ER (2.10)'s `Θ(z₁,z₂) = aS(I-aS)⁻¹`, where
`a = m(z₁) * conj (m(z₂))`.

The contract below only applies this definition to spectral parameters in the same
open half-plane, exactly as in the paragraph introducing ER (2.10). -/
def erTheta (p : Params) (z₁ z₂ : ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  let a := erSemicircleStieltjes z₁ * starRingEnd ℂ (erSemicircleStieltjes z₂)
  let A := a • erComplexVarianceProfile p
  A * (1 - A)⁻¹

/-- ER (2.10)'s `Ξ(z₁,z₂) = aS(I-aS)⁻¹`, where
`a = m(z₁) * m(z₂)`. -/
def erXi (p : Params) (z₁ z₂ : ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  let a := erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂
  let A := a • erComplexVarianceProfile p
  A * (1 - A)⁻¹

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

/-- The height interval `[N⁻¹⁺δ, C₀]` on which Definition 2.4 indexes `Υ_η`. -/
def ERControlHeight (p : Params) (ηExp C₀ η : ℝ) : Prop :=
  Real.rpow (p.L : ℝ) (-1 + ηExp) ≤ η ∧ η ≤ C₀

/-- The fixed source convention that the two arguments of `Θ` and `Ξ` lie in the same
open half-plane. -/
def ERSameHalfPlane (z₁ z₂ : ℂ) : Prop := 0 < z₁.im * z₂.im

/-- An ER control family is an explicitly indexed real matrix family.  Positivity,
symmetry, its height range, and every analytic requirement live in
`ERDefinition24Control`; they are not built into this data alias. -/
abbrev ERControlFamily (p : Params) :=
  ℝ → Matrix (Site p.n p.W) (Site p.n p.W) ℝ

/-- Erdős–Riabov Definition 2.4, with its exact seven top-level clauses.

`C₁`, `C₂`, and `c₂` are the constants quantified immediately before the seven
clauses in the source.  Although `C₂` appears only in the explanatory effectiveness
remark following clause (vii), it is retained so that the source quantifier list is not
silently shortened.  `DPrime` is the exponent quantified in clause (ii).

The structure records the estimates for a given family `Upsilon`; it does not assert
that the control function displayed in the paper satisfies them. -/
structure ERDefinition24ControlWithConvolutionLoss (p : Params)
    (κ ηExp C₀ C₁ C₂ c₂ DPrime : ℝ)
    (convolutionLoss : ℝ)
    (Upsilon : ERControlFamily p) : Prop where
  κ_pos : 0 < κ
  ηExp_pos : 0 < ηExp
  C₀_ge_one : 1 ≤ C₀
  C₁_pos : 0 < C₁
  C₂_pos : 0 < C₂
  c₂_pos : 0 < c₂
  DPrime_pos : 0 < DPrime
  convolutionLoss_ge_one : 1 ≤ convolutionLoss
  entrywisePositive : ∀ η, ERControlHeight p ηExp C₀ η →
    ∀ x y, 0 < Upsilon η x y
  symmetric : ∀ η, ERControlHeight p ηExp C₀ η →
    ∀ x y, Upsilon η x y = Upsilon η y x
  /-- Clause (i), ER (2.18): simultaneous majoration of `Θ` at the minimum
  height and of `Ξ` at height one. -/
  clause1 : ∀ z₁ z₂, ERSpectralDomain p κ ηExp C₀ z₁ →
    ERSpectralDomain p κ ηExp C₀ z₂ → ERSameHalfPlane z₁ z₂ →
    ∀ x y,
      ‖erTheta p z₁ z₂ x y‖ ≤ C₁ * Upsilon (min |z₁.im| |z₂.im|) x y ∧
      ‖erXi p z₁ z₂ x y‖ ≤ C₁ * Upsilon 1 x y
  /-- Clause (ii), ER (2.19)--(2.21): pointwise and row-sum upper bounds, the polynomial
  floor, and the two-sided delocalized comparison. -/
  clause2 : ∀ η, ERControlHeight p ηExp C₀ η →
    (∀ x y, Upsilon η x y ≤ C₁ / (erLocalizationLength p η * η)) ∧
    (∀ x, ∑ a, Upsilon η x a ≤ C₁ / η) ∧
    (∀ x y, Real.rpow (p.L : ℝ) (-2 * DPrime) ≤ Upsilon η x y) ∧
    (η ≤ ((p.W : ℝ) / (p.L : ℝ)) ^ 2 →
      ∀ x y,
        (1 / C₁) * (1 / ((p.L : ℝ) * η)) ≤ Upsilon η x y ∧
        Upsilon η x y ≤ C₁ * (1 / ((p.L : ℝ) * η)))
  /-- Clause (iii), ER (2.22): monotonicity up to the same fixed constant `C₁`. -/
  clause3 : ∀ η₁ η₂, ERControlHeight p ηExp C₀ η₁ →
    ERControlHeight p ηExp C₀ η₂ → η₁ ≤ η₂ →
    ∀ x y, Upsilon η₂ x y ≤ C₁ * Upsilon η₁ x y
  /-- Clause (iv), ER (2.23)--(2.24): both the pointwise triangle/product estimate and
  the square-root convolution estimate. -/
  clause4 : ∀ η₁ η₂, ERControlHeight p ηExp C₀ η₁ →
    ERControlHeight p ηExp C₀ η₂ → η₁ ≤ η₂ →
    ∀ x y,
      (∀ a, Upsilon η₂ x a * Upsilon η₁ a y ≤
        C₁ / (erLocalizationLength p η₂ * η₂) * Upsilon η₁ x y) ∧
      (∑ a, Real.sqrt (Upsilon η₂ x a * Upsilon η₁ a y)) ≤
        (C₁ * convolutionLoss) / η₂ *
          Real.sqrt (erLocalizationLength p η₂ * η₂ * Upsilon η₁ x y)
  /-- Clause (v), ER (2.25): weighted convolution for each of the two source
  choices `ηᵢ ∈ {η₁,η₂}`. -/
  clause5 : ∀ η₁ η₂, ERControlHeight p ηExp C₀ η₁ →
    ERControlHeight p ηExp C₀ η₂ → η₁ ≤ η₂ →
    ∀ ηi, (ηi = η₁ ∨ ηi = η₂) → ∀ x y,
      (∑ a,
        (min ((erSiteDistance p a x : ℝ) + p.W)
            (erLocalizationLength p η₁) / erLocalizationLength p η₁) *
          Real.sqrt (Upsilon η₂ x a * Upsilon ηi a y)) ≤
        (C₁ * convolutionLoss) / η₂ *
          (erLocalizationLength p η₂ / erLocalizationLength p η₁) *
          Real.sqrt
            ((erLocalizationLength p η₂ * η₂) /
              (erLocalizationLength p ηi * ηi)) *
          Real.sqrt
            (erLocalizationLength p η₁ * η₁ * Upsilon η₁ x y)
  /-- Clause (vi), ER (2.26): localized regularity of `Θ`, including the source's `+W`
  allowance and the threshold `η ≥ c₂(W/N)²`. -/
  clause6 : ∀ z₁ z₂, ERSpectralDomain p κ ηExp C₀ z₁ →
    ERSpectralDomain p κ ηExp C₀ z₂ → ERSameHalfPlane z₁ z₂ →
    let η := min |z₁.im| |z₂.im|
    c₂ * ((p.W : ℝ) / (p.L : ℝ)) ^ 2 ≤ η →
      ∀ a b c,
        ‖erTheta p z₁ z₂ a b - erTheta p z₁ z₂ a c‖ ≤
          C₁ *
            (min ((erSiteDistance p b c : ℝ) + p.W)
                (erLocalizationLength p η) / erLocalizationLength p η) *
            (Upsilon η a b + Upsilon η a c)
  /-- Clause (vii), ER (2.27): delocalized regularity after subtracting the
  exact constant row Fourier mode.  The clause is stated on the whole spectral
  domain, as in Definition 2.4; `C₂` occurs only in the subsequent remark. -/
  clause7 : ∀ z₁ z₂, ERSpectralDomain p κ ηExp C₀ z₁ →
    ERSpectralDomain p κ ηExp C₀ z₂ → ERSameHalfPlane z₁ z₂ →
    ∀ a b,
      ‖erTheta p z₁ z₂ a b -
          (1 / (p.L : ℂ)) * ∑ c, erTheta p z₁ z₂ a c‖ ≤
        C₁ * (p.L : ℝ) / (p.W : ℝ) ^ 2

/-- ER Definition 2.4, with no dimension-dependent loss in
the two convolution clauses.  This is the loss-one specialization of the
generalized structure above. -/
abbrev ERDefinition24Control (p : Params)
    (κ ηExp C₀ C₁ C₂ c₂ DPrime : ℝ)
    (Upsilon : ERControlFamily p) : Prop :=
  ERDefinition24ControlWithConvolutionLoss p κ ηExp C₀ C₁ C₂ c₂ DPrime
    1 Upsilon

end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
