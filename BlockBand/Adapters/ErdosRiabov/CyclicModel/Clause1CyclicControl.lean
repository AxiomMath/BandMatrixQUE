module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ScalarProfileControl
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.DeterministicMDECore
public import Mathlib

/-!
# Fixed-bond cyclic control for ER clause (i)

The paper fixes the bond weight `b ∈ (0,1/2)` before choosing its analytic
constants.  This module proves the deterministic phase and cyclic-resolvent estimates
needed to discharge clause (i) with constants depending on that fixed `b` but not on
the ring length, block width, or parity.

The dependence on `b` is essential.  In particular, as `b ↑ 1/2`, the `Ξ` multiplier
approaches the negative cyclic Fourier edge; consequently neither decay rate `a = 1`
nor the comparison constant `6e` can be uniform in `b`.  The common constant below
therefore takes the maximum with the already proved scalar-control constant `6e`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause1

open scoped BigOperators
open ERProfile ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERCharacterAngle ERNearestNeighbor ERCyclicDecay ERJumpNormalization ERCyclicSummation ERHerglotz ERPhysicalBridge ERScalarProfileControl

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The common fixed-bond exponential rate. -/
def clause1Decay (b : ℝ) : ℝ := min (1 / 2) (1 - 2 * b)

/-- A fixed-bond lower bound for the noncritical factor of the `Ξ` jump. -/
def xiJumpMargin (b : ℝ) : ℝ := min 1 (2 - 4 * b)

/-- The fixed-bond decay rate is strictly positive. -/
theorem clause1Decay_pos {b : ℝ} (_hb0 : 0 < b) (hb : b < 1 / 2) :
    0 < clause1Decay b := by
  unfold clause1Decay
  exact lt_min (by norm_num) (by linarith)

/-- The negative-edge jump margin is strictly positive at every fixed
`b < 1/2`. -/
theorem xiJumpMargin_pos {b : ℝ} (hb : b < 1 / 2) :
    0 < xiJumpMargin b := by
  unfold xiJumpMargin
  exact lt_min (by norm_num) (by linarith)

/-- At height one the ER localization length is exactly one block width. -/
theorem erLocalizationLength_one (p : Params) :
    erLocalizationLength p 1 = p.W := by
  unfold erLocalizationLength
  rw [Real.sqrt_one, div_one, min_eq_left]
  exact_mod_cast
    (show p.W ≤ p.n * p.W by
      calc
        p.W = 1 * p.W := by simp
        _ ≤ p.n * p.W := Nat.mul_le_mul_right p.W p.n_pos)

/-- The exponential branch is a lower bound for the fixed-bond control. -/
theorem exp_branch_le_erManuscriptCyclicControl_one
    (p : Params) (a : ℝ) (x y : Site p.n p.W) :
    (1 / (p.W : ℝ)) *
        Real.exp (-a * (erSiteDistance p x y : ℝ) / p.W) ≤
      erManuscriptCyclicControl p a 8 1 x y := by
  show _ ≤ (1 / (erLocalizationLength p 1 * 1)) *
    Real.exp (-a * (erSiteDistance p x y : ℝ) / erLocalizationLength p 1)
  rw [erLocalizationLength_one, mul_one]

/-- A convenient numerical lower bound for the saturated wrap denominator. -/
theorem one_fourth_le_one_sub_exp_neg_one :
    (1 / 4 : ℝ) ≤ 1 - Real.exp (-1) := by
  rw [Real.exp_neg]
  have he : 2 ≤ Real.exp (1 : ℝ) := by
    convert Real.add_one_le_exp (1 : ℝ) using 1
    all_goals norm_num
  have hinv : (Real.exp (1 : ℝ))⁻¹ ≤ 1 / 2 := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he)
  linarith

/-- On the unit height range, the root-gap rate is at least half the
square-root height. -/
theorem sqrt_height_div_two_le_rootGapRate
    (p : Params) {α : ℂ} {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hmargin : η / 4 ≤ 1 - ‖α‖) :
    Real.sqrt η / 2 ≤ rootGapRate p α := by
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1
    all_goals norm_num
  unfold rootGapRate
  apply le_min
  · have hsqrt : Real.sqrt η ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hη1
    linarith
  · rw [show Real.sqrt η / 2 = Real.sqrt (η / 4) by
      rw [Real.sqrt_div hη0.le]
      rw [hsqrt4]]
    apply Real.sqrt_le_sqrt
    have hb : 2 * p.b ≤ 1 := by linarith [p.b_lt_half]
    have hden : 0 < 2 * p.b := by nlinarith [p.b_pos]
    apply (le_div_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ η / 4)]

/-- The jump scale inherits the height margin with the exact fixed-bond
factor. -/
theorem sqrt_height_mul_bondMargin_div_two_le_jumpLowerScale
    (p : Params) {α : ℂ} {η : ℝ}
    (hη0 : 0 < η) (hmargin : η / 4 ≤ 1 - ‖α‖) :
    Real.sqrt η / 2 * Real.sqrt (jumpBondMargin p) ≤
      jumpLowerScale p α := by
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1
    all_goals norm_num
  unfold jumpLowerScale
  have hg : 0 ≤ jumpBondMargin p := (jumpBondMargin_pos p).le
  have hη : 0 ≤ η := hη0.le
  have hprod :
      η / 4 * jumpBondMargin p ≤
        (1 - ‖α‖) * jumpBondMargin p :=
    mul_le_mul_of_nonneg_right hmargin hg
  calc
    Real.sqrt η / 2 * Real.sqrt (jumpBondMargin p) =
        Real.sqrt (η / 4 * jumpBondMargin p) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ η / 4),
        Real.sqrt_div hη]
      rw [hsqrt4]
    _ ≤ Real.sqrt ((1 - ‖α‖) * jumpBondMargin p) :=
      Real.sqrt_le_sqrt hprod

/-- Pointwise cyclic Green estimate at spectral height `η`.  The factor
`min 1 (n√η)` is exactly the finite-cycle wrap gain needed when the
localization length saturates at the system size. -/
theorem norm_fourierGreenKernel_le_theta_height
    (p : Params) {α : ℂ} {η : ℝ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hmargin : η / 4 ≤ 1 - ‖α‖)
    (x y : ZMod p.n) :
    ‖fourierGreenKernel p α x y‖ ≤
      16 * Real.exp (-(Real.sqrt η / 2) *
          cyclicBlockDistance p x y) /
        (min 1 ((p.n : ℝ) * Real.sqrt η) *
          Real.sqrt η * Real.sqrt (jumpBondMargin p)) := by
  let ρ := contractingRecurrenceRoot p α
  let γ := rootGapRate p α
  let J := jumpLowerScale p α
  have hbase := norm_fourierGreenKernel_le_twoPath p hα0 hα x y
  have hρ := norm_contractingRecurrenceRoot_lt_one p hα0 hα
  have hγ0 : 0 < γ := rootGapRate_pos p hα
  have hJ0 : 0 < J := jumpLowerScale_pos p hα
  have hγ : Real.sqrt η / 2 ≤ γ :=
    sqrt_height_div_two_le_rootGapRate p hη0 hη1 hmargin
  have hJ : Real.sqrt η / 2 * Real.sqrt (jumpBondMargin p) ≤ J :=
    sqrt_height_mul_bondMargin_div_two_le_jumpLowerScale p hη0 hmargin
  have hwrap := min_rootGap_wrapScale_le_contracting_denominator p hα0 hα
  have hsat : (1 / 4 : ℝ) ≤ 1 - Real.exp (-1) :=
    one_fourth_le_one_sub_exp_neg_one
  have hsmall :
      ((p.n : ℝ) * Real.sqrt η) / 4 ≤
        ((p.n : ℝ) * γ) / 2 := by
    have hn : 0 ≤ (p.n : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hγ hn]
  have hwrap' :
      (1 / 4) * min 1 ((p.n : ℝ) * Real.sqrt η) ≤
        ‖1 - ρ ^ p.n‖ := by
    have hmin :
        min (1 / 4 : ℝ) (((p.n : ℝ) * Real.sqrt η) / 4) ≤
          min (1 - Real.exp (-1)) (((p.n : ℝ) * γ) / 2) :=
      min_le_min hsat hsmall
    have heq :
        (1 / 4) * min 1 ((p.n : ℝ) * Real.sqrt η) =
          min (1 / 4) (((p.n : ℝ) * Real.sqrt η) / 4) := by
      rcases le_total 1 ((p.n : ℝ) * Real.sqrt η) with ht | ht
      · rw [min_eq_left ht, min_eq_left]
        · ring
        · nlinarith
      · rw [min_eq_right ht, min_eq_right]
        · ring
        · nlinarith
    rw [heq]
    exact hmin.trans hwrap
  have hpowers := twoPathPowers_le_twice_shorter
    (r := ‖ρ‖) (n := p.n) (d := orientedBlockDistance p x y)
    (norm_nonneg ρ) hρ.le
  have hpowexp :=
    pow_le_exp_neg_gap (norm_nonneg ρ)
      (cyclicBlockDistance p x y)
  have hrootgap :
      1 - ‖ρ‖ ≥ γ :=
    min_half_sqrt_radialMargin_le_root_gap p hα0 hα
  have hexp :
      ‖ρ‖ ^ cyclicBlockDistance p x y ≤
        Real.exp (-(Real.sqrt η / 2) *
          cyclicBlockDistance p x y) := by
    exact hpowexp.trans (Real.exp_le_exp.mpr (by
      have hd : 0 ≤ (cyclicBlockDistance p x y : ℝ) := by positivity
      nlinarith))
  have hminpos : 0 < min 1 ((p.n : ℝ) * Real.sqrt η) := by
    exact lt_min (by norm_num)
      (mul_pos (by exact_mod_cast p.n_pos) (Real.sqrt_pos.2 hη0))
  have hsqrtη : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
  have hsqrtg : 0 < Real.sqrt (jumpBondMargin p) :=
    Real.sqrt_pos.2 (jumpBondMargin_pos p)
  dsimp only [ρ] at hbase hpowers hwrap'
  dsimp only [γ, J] at hγ hJ hrootgap
  calc
    ‖fourierGreenKernel p α x y‖ ≤
        (‖ρ‖ ^ orientedBlockDistance p x y +
          ‖ρ‖ ^ (p.n - orientedBlockDistance p x y)) /
          (‖1 - ρ ^ p.n‖ *
            ‖recurrenceJump p α ρ‖) := hbase
    _ ≤ (2 * ‖ρ‖ ^ cyclicBlockDistance p x y) /
          (‖1 - ρ ^ p.n‖ *
            ‖recurrenceJump p α ρ‖) :=
      div_le_div_of_nonneg_right hpowers (by positivity)
    _ ≤ (2 * Real.exp (-(Real.sqrt η / 2) *
          cyclicBlockDistance p x y)) /
          (‖1 - ρ ^ p.n‖ *
            ‖recurrenceJump p α ρ‖) := by
      gcongr
    _ ≤ (2 * Real.exp (-(Real.sqrt η / 2) *
          cyclicBlockDistance p x y)) /
          (((1 / 4) * min 1 ((p.n : ℝ) * Real.sqrt η)) *
            (Real.sqrt η / 2 * Real.sqrt (jumpBondMargin p))) := by
      apply div_le_div_of_nonneg_left (by positivity)
      · positivity
      · exact mul_le_mul hwrap'
          (sqrt_margin_le_contractingRecurrenceJump p hα0 hα |>.trans' hJ)
          (by positivity) (norm_nonneg _)
    _ = 16 * Real.exp (-(Real.sqrt η / 2) *
          cyclicBlockDistance p x y) /
        (min 1 ((p.n : ℝ) * Real.sqrt η) *
          Real.sqrt η * Real.sqrt (jumpBondMargin p)) := by ring

/-- The finite-cycle wrap factor is exactly the branch selector in the
localization normalization of the paper. -/
theorem width_mul_wrap_sqrt_eq_localization_mul
    (p : Params) {η : ℝ} (hη : 0 < η) :
    (p.W : ℝ) *
        (min 1 ((p.n : ℝ) * Real.sqrt η) * Real.sqrt η) =
      erLocalizationLength p η * η := by
  have hs : 0 ≤ Real.sqrt η := Real.sqrt_nonneg _
  rw [erLocalizationLength_mul p hη]
  rw [min_mul_of_nonneg _ _ hs]
  rw [mul_min_of_nonneg _ _ p.real_W_pos.le]
  apply congrArg₂ min
  · ring
  · have hsquare : Real.sqrt η * Real.sqrt η = η := by
      nlinarith [Real.sq_sqrt hη.le]
    calc
      (p.W : ℝ) * ((p.n : ℝ) * Real.sqrt η * Real.sqrt η) =
          (p.W : ℝ) * (p.n : ℝ) *
            (Real.sqrt η * Real.sqrt η) := by ring
      _ = (p.W : ℝ) * (p.n : ℝ) * η := by rw [hsquare]
      _ = (p.L : ℝ) * η := by
        rw [show (p.L : ℝ) = (p.n : ℝ) * (p.W : ℝ) by
          simp [Conventions.ModelParameters.L, Conventions.dimension]]
        ring

/-- Every flattened cyclic distance is bounded by the total dimension. -/
theorem erSiteDistance_le_dimension
    (p : Params) (x y : Site p.n p.W) :
    erSiteDistance p x y ≤ p.L := by
  unfold erSiteDistance
  exact (min_le_right _ _).trans (Nat.sub_le _ _)

/-- Block-scale square-root decay dominates the site-scale
exponential on both branches of the localization minimum. -/
theorem theta_block_exp_le_site_exp
    (p : Params) {η a : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (ha1 : a ≤ 1 / 2)
    (x y : Site p.n p.W) :
    Real.exp (-(Real.sqrt η / 2) *
        cyclicBlockDistance p x.1 y.1) ≤
      Real.exp (1 / 2) *
        Real.exp (-a * (erSiteDistance p x y : ℝ) /
          erLocalizationLength p η) := by
  have hs0 : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
  have hs1 : Real.sqrt η ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hη1
  have hsite :
      (erSiteDistance p x y : ℝ) ≤
        (p.W : ℝ) * cyclicBlockDistance p x.1 y.1 + p.W := by
    exact_mod_cast
      siteDistance_le_width_mul_cyclicBlockDistance_add_width p x y
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  by_cases hbranch :
      (p.W : ℝ) / Real.sqrt η ≤ (p.L : ℝ)
  · have hell :
        erLocalizationLength p η = (p.W : ℝ) / Real.sqrt η := by
      unfold erLocalizationLength
      exact min_eq_left hbranch
    rw [hell]
    have hhalf :
        a * (erSiteDistance p x y : ℝ) ≤
          (1 / 2) *
            ((p.W : ℝ) * cyclicBlockDistance p x.1 y.1 + p.W) := by
      calc
        a * (erSiteDistance p x y : ℝ) ≤
            (1 / 2) * (erSiteDistance p x y : ℝ) :=
          mul_le_mul_of_nonneg_right ha1 (by positivity)
        _ ≤ (1 / 2) *
            ((p.W : ℝ) * cyclicBlockDistance p x.1 y.1 + p.W) :=
          mul_le_mul_of_nonneg_left hsite (by norm_num)
    have hscaled :
        (a * (erSiteDistance p x y : ℝ)) *
            (Real.sqrt η / (p.W : ℝ)) ≤
          ((1 / 2) *
            ((p.W : ℝ) * cyclicBlockDistance p x.1 y.1 + p.W)) *
            (Real.sqrt η / (p.W : ℝ)) :=
      mul_le_mul_of_nonneg_right hhalf (by positivity)
    have hrewrite :
        a * (erSiteDistance p x y : ℝ) /
            ((p.W : ℝ) / Real.sqrt η) =
          (a * (erSiteDistance p x y : ℝ)) *
            (Real.sqrt η / (p.W : ℝ)) := by
      field_simp
    have hrewrite_neg :
        -a * (erSiteDistance p x y : ℝ) /
            ((p.W : ℝ) / Real.sqrt η) =
          -(a * (erSiteDistance p x y : ℝ) /
            ((p.W : ℝ) / Real.sqrt η)) := by ring
    rw [hrewrite_neg, hrewrite]
    have hd : 0 ≤ (cyclicBlockDistance p x.1 y.1 : ℝ) := by positivity
    have hw : 0 < (p.W : ℝ) := p.real_W_pos
    have hscaled' :
        (a * (erSiteDistance p x y : ℝ)) *
            (Real.sqrt η / (p.W : ℝ)) ≤
          (Real.sqrt η / 2) *
            ((cyclicBlockDistance p x.1 y.1 : ℝ) + 1) := by
      exact hscaled.trans_eq (by field_simp [ne_of_gt hw])
    nlinarith [mul_nonneg hs0.le hd]
  · have hrev :
        (p.L : ℝ) ≤ (p.W : ℝ) / Real.sqrt η :=
      le_of_not_ge hbranch
    have hell : erLocalizationLength p η = (p.L : ℝ) := by
      unfold erLocalizationLength
      exact min_eq_right hrev
    rw [hell]
    have hdim :
        (erSiteDistance p x y : ℝ) ≤ (p.L : ℝ) := by
      exact_mod_cast erSiteDistance_le_dimension p x y
    have hhalf :
        a * (erSiteDistance p x y : ℝ) ≤
          (1 / 2) * (p.L : ℝ) := by
      calc
        a * (erSiteDistance p x y : ℝ) ≤
            (1 / 2) * (erSiteDistance p x y : ℝ) :=
          mul_le_mul_of_nonneg_right ha1 (by positivity)
        _ ≤ (1 / 2) * (p.L : ℝ) :=
          mul_le_mul_of_nonneg_left hdim (by norm_num)
    have hL : 0 < (p.L : ℝ) := p.real_L_pos
    have hquot :
        a * (erSiteDistance p x y : ℝ) / (p.L : ℝ) ≤ 1 / 2 := by
      exact (div_le_iff₀ hL).2 (by simpa [mul_comm] using hhalf)
    have hd : 0 ≤ (cyclicBlockDistance p x.1 y.1 : ℝ) := by positivity
    have hneg :
        -a * (erSiteDistance p x y : ℝ) / (p.L : ℝ) =
          -(a * (erSiteDistance p x y : ℝ) / (p.L : ℝ)) := by ring
    rw [hneg]
    have hleft :
        -(Real.sqrt η / 2) *
            (cyclicBlockDistance p x.1 y.1 : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (div_nonneg hs0.le (by norm_num))) hd
    exact hleft.trans (by linarith)

/-- The exponential branch alone is a lower bound for the cyclic control
`erManuscriptCyclicControl` at every positive height. -/
theorem exp_branch_le_erManuscriptCyclicControl
    (p : Params) {η : ℝ} (hη : 0 < η) (a : ℝ)
    (x y : Site p.n p.W) :
    (1 / (erLocalizationLength p η * η)) *
        Real.exp (-a * (erSiteDistance p x y : ℝ) /
          erLocalizationLength p η) ≤
      erManuscriptCyclicControl p a 8 η x y := by
  have hell : 0 < erLocalizationLength p η := by
    unfold erLocalizationLength
    exact lt_min (div_pos p.real_W_pos (Real.sqrt_pos.2 hη))
      p.real_L_pos
  have := hell
  exact le_rfl

/-- Sitewise corrected-`Θ` bound in the cyclic-control
normalization `erManuscriptCyclicControl`. -/
theorem norm_erTheta_le_fixedBond_control
    (p : Params) {κ ηExp : ℝ} {z₁ z₂ : ℂ}
    (h₁ : ERSpectralDomain p κ ηExp 1 z₁)
    (h₂ : ERSpectralDomain p κ ηExp 1 z₂)
    (x y : Site p.n p.W) :
    ‖erTheta p z₁ z₂ x y‖ ≤
      (32 * Real.exp (1 / 2) /
        Real.sqrt (jumpBondMargin p)) *
      erManuscriptCyclicControl p (clause1Decay p.b) 8
        (min |z₁.im| |z₂.im|) x y := by
  let η : ℝ := min |z₁.im| |z₂.im|
  let α : ℂ := erSemicircleStieltjes z₁ *
    starRingEnd ℂ (erSemicircleStieltjes z₂)
  have hz₁ : z₁.im ≠ 0 :=
    ERDeterministicMDECore.spectralDomain_im_ne_zero h₁
  have hz₂ : z₂.im ≠ 0 :=
    ERDeterministicMDECore.spectralDomain_im_ne_zero h₂
  have hη0 : 0 < η := by
    dsimp only [η]
    exact lt_min (abs_pos.mpr hz₁) (abs_pos.mpr hz₂)
  have hη1 : η ≤ 1 := by
    dsimp only [η]
    exact (min_le_left _ _).trans
      ((Complex.abs_im_le_norm z₁).trans h₁.2.1)
  have hm₁0 : erSemicircleStieltjes z₁ ≠ 0 := by
    intro hm
    have h := erSemicircleStieltjes_dyson z₁
    simp [hm] at h
  have hm₂0 : erSemicircleStieltjes z₂ ≠ 0 := by
    intro hm
    have h := erSemicircleStieltjes_dyson z₂
    simp [hm] at h
  have hα0 : α ≠ 0 :=
    mul_ne_zero hm₁0 ((map_ne_zero (starRingEnd ℂ)).2 hm₂0)
  have hα : ‖α‖ < 1 := by
    dsimp only [α]
    exact norm_thetaMultiplier_lt_one
      (norm_erSemicircleStieltjes_lt_one hz₁)
      (norm_erSemicircleStieltjes_lt_one hz₂)
  have hmargin : η / 4 ≤ 1 - ‖α‖ := by
    have h := thetaMultiplier_height_margin hz₁ hz₂
    dsimp only [η, α]
    rw [min_eq_right (by nlinarith)] at h
    exact h
  have hgreen :=
    norm_fourierGreenKernel_le_theta_height p hα0 hα hη0 hη1
      hmargin x.1 y.1
  have hbridge :=
    erTheta_apply_eq_siteGreenKernel_sub_identity p hz₁ hz₂ x y
  have hsite := norm_siteGreenKernel_sub_identity p α x y
  have hmpos :
      0 < min 1 ((p.n : ℝ) * Real.sqrt η) := by
    exact lt_min (by norm_num)
      (mul_pos (by exact_mod_cast p.n_pos) (Real.sqrt_pos.2 hη0))
  have hspos : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
  have hgpos : 0 < Real.sqrt (jumpBondMargin p) :=
    Real.sqrt_pos.2 (jumpBondMargin_pos p)
  let den : ℝ :=
    min 1 ((p.n : ℝ) * Real.sqrt η) *
      Real.sqrt η * Real.sqrt (jumpBondMargin p)
  have hdenpos : 0 < den := by
    dsimp only [den]
    positivity
  have hdelta :
      ‖fourierGreenKernel p α x.1 y.1 -
          (if x.1 = y.1 then 1 else 0)‖ ≤
        32 * Real.exp (-(Real.sqrt η / 2) *
          cyclicBlockDistance p x.1 y.1) / den := by
    by_cases hb : x.1 = y.1
    · have hd0 : cyclicBlockDistance p x.1 y.1 = 0 := by
        rw [hb]
        simp [cyclicBlockDistance, orientedBlockDistance]
      have hdenle : den ≤ 1 := by
        have hmle : min 1 ((p.n : ℝ) * Real.sqrt η) ≤ 1 :=
          min_le_left _ _
        have hsle : Real.sqrt η ≤ 1 := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt hη1
        have hgle : Real.sqrt (jumpBondMargin p) ≤ 1 := by
          rw [← Real.sqrt_one]
          apply Real.sqrt_le_sqrt
          unfold jumpBondMargin
          exact sub_le_self _ (abs_nonneg _)
        dsimp only [den]
        nlinarith [hmpos.le, hspos.le, hgpos.le,
          mul_nonneg hmpos.le hspos.le,
          mul_le_mul hmle hsle hspos.le (by norm_num : (0 : ℝ) ≤ 1)]
      have hone : 1 ≤ 16 / den := by
        apply (le_div_iff₀ hdenpos).2
        nlinarith
      have hgreen' :
          ‖fourierGreenKernel p α x.1 y.1‖ ≤ 16 / den := by
        change ‖fourierGreenKernel p α x.1 y.1‖ ≤
          16 * Real.exp (-(Real.sqrt η / 2) *
            cyclicBlockDistance p x.1 y.1) / den at hgreen
        rw [hd0] at hgreen
        norm_num at hgreen
        exact hgreen
      have hite :
          (if x.1 = y.1 then (1 : ℂ) else 0) = 1 := by
        simp [hb]
      rw [hite, hd0]
      norm_num
      calc
        ‖fourierGreenKernel p α x.1 y.1 - 1‖ ≤
            ‖fourierGreenKernel p α x.1 y.1‖ + 1 := by
          simpa using norm_sub_le
            (fourierGreenKernel p α x.1 y.1) (1 : ℂ)
        _ ≤ 16 / den + 1 := by
          simpa [add_comm] using add_le_add_right hgreen' 1
        _ ≤ 32 / den := by
          calc
            16 / den + 1 ≤ 16 / den + 16 / den :=
              (by simpa [add_comm] using
                add_le_add_left hone (16 / den))
            _ = 32 / den := by ring
    · simp only [hb, ite_false, sub_zero]
      exact hgreen.trans (by
        apply div_le_div_of_nonneg_right _ hdenpos.le
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (Real.exp_pos _).le)
  have hnorm :
      (p.W : ℝ) *
          (min 1 ((p.n : ℝ) * Real.sqrt η) * Real.sqrt η) =
        erLocalizationLength p η * η :=
    width_mul_wrap_sqrt_eq_localization_mul p hη0
  have hellηpos : 0 < erLocalizationLength p η * η := by
    rw [← hnorm]
    exact mul_pos p.real_W_pos (mul_pos hmpos hspos)
  have hdennorm :
      den * (p.W : ℝ) =
        (erLocalizationLength p η * η) *
          Real.sqrt (jumpBondMargin p) := by
    dsimp only [den]
    calc
      (min 1 ((p.n : ℝ) * Real.sqrt η) *
          Real.sqrt η * Real.sqrt (jumpBondMargin p)) * (p.W : ℝ) =
        ((p.W : ℝ) *
          (min 1 ((p.n : ℝ) * Real.sqrt η) * Real.sqrt η)) *
            Real.sqrt (jumpBondMargin p) := by ring
      _ = (erLocalizationLength p η * η) *
            Real.sqrt (jumpBondMargin p) := by rw [hnorm]
  have hexp := theta_block_exp_le_site_exp p
    (a := clause1Decay p.b) hη0 hη1
    (min_le_left _ _) x y
  have hcontrol := exp_branch_le_erManuscriptCyclicControl p hη0
    (clause1Decay p.b) x y
  rw [hbridge, hsite]
  change ‖fourierGreenKernel p α x.1 y.1 -
      (if x.1 = y.1 then 1 else 0)‖ / (p.W : ℝ) ≤ _
  calc
    ‖fourierGreenKernel p α x.1 y.1 -
        (if x.1 = y.1 then 1 else 0)‖ / (p.W : ℝ) ≤
      (32 * Real.exp (-(Real.sqrt η / 2) *
        cyclicBlockDistance p x.1 y.1) / den) / (p.W : ℝ) := by
          gcongr
    _ = (32 / Real.sqrt (jumpBondMargin p)) *
        ((1 / (erLocalizationLength p η * η)) *
          Real.exp (-(Real.sqrt η / 2) *
            cyclicBlockDistance p x.1 y.1)) := by
      rw [div_div, hdennorm]
      field_simp [ne_of_gt hellηpos, ne_of_gt hgpos]
    _ ≤ (32 / Real.sqrt (jumpBondMargin p)) *
        ((1 / (erLocalizationLength p η * η)) *
          (Real.exp (1 / 2) *
            Real.exp (-clause1Decay p.b *
              (erSiteDistance p x y : ℝ) /
                erLocalizationLength p η))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp
          (one_div_nonneg.mpr hellηpos.le))
        (by positivity)
    _ = (32 * Real.exp (1 / 2) /
          Real.sqrt (jumpBondMargin p)) *
        ((1 / (erLocalizationLength p η * η)) *
          Real.exp (-clause1Decay p.b *
            (erSiteDistance p x y : ℝ) /
              erLocalizationLength p η)) := by ring
    _ ≤ (32 * Real.exp (1 / 2) /
          Real.sqrt (jumpBondMargin p)) *
        erManuscriptCyclicControl p (clause1Decay p.b) 8 η x y :=
      mul_le_mul_of_nonneg_left hcontrol (by positivity)

/-- The jump margin written only in terms of the fixed bond weight. -/
theorem jumpBondMargin_eq_fixedBond (p : Params) :
    jumpBondMargin p = 1 - |1 - 4 * p.b| := by
  unfold jumpBondMargin
  congr 2
  linarith [p.c_add_two_b]

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause1
