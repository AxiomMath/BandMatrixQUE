module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.GeneralVectorMDEXiKappa
public import Mathlib

/-!
# Domain-dependent deterministic control of the ER Theta kernel

This module closes the high-height part of ER Definition 2.4(i) for the concrete
cyclic profile without asking for a decay rate uniform in the spectral cutoff.
For a fixed domain cutoff `C₀`, the explicit rate is
`1 / (2 * sqrt (max 1 C₀))`.  Thus the quantifier order agrees with ER
Definition 2.9 and Proposition 2.8: the cutoff is fixed before the decay.

The proof uses the all-height recurrence bound for `erTheta`.  At
height above one the localization length is `W / sqrt η`; the norm cutoff gives
`sqrt η ≤ sqrt (max 1 C₀)`, which converts the fixed block rate `1/2` into the
stated site-scale rate.  No admissibility certificate or target estimate is an
input.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERGeneralVectorMDEThetaDomain

open ERGeneralVectorMDESpectralDomain ERGeneralVectorMDEXiKappa ERClause1 ERScalarProfileControl ERPhysicalBridge ERDeterministicMDECore ERCyclicDecay ERJumpNormalization

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The source-faithful `Theta` decay after fixing the spectral cutoff `C₀`. -/
def thetaDomainDecay (C₀ : ℝ) : ℝ :=
  1 / (2 * Real.sqrt (max 1 C₀))

/-- A comparison constant for the domain-dependent `Theta` estimate. -/
def thetaDomainControlConstant (p : Params) (C₀ : ℝ) : ℝ :=
  max (32 * Real.exp (1 / 2) / Real.sqrt (jumpBondMargin p))
    (17 * Real.exp (1 / 2) * Real.sqrt (max 1 C₀) /
      Real.sqrt (jumpBondMargin p))

theorem thetaDomainDecay_pos (C₀ : ℝ) : 0 < thetaDomainDecay C₀ := by
  unfold thetaDomainDecay
  have : 0 < Real.sqrt (max 1 C₀) := Real.sqrt_pos.2 (lt_max_of_lt_left one_pos)
  positivity

theorem thetaDomainDecay_le_half (C₀ : ℝ) : thetaDomainDecay C₀ ≤ 1 / 2 := by
  unfold thetaDomainDecay
  have hs : 1 ≤ Real.sqrt (max 1 C₀) :=
    Real.one_le_sqrt.mpr (le_max_left _ _)
  have hs0 : 0 < Real.sqrt (max 1 C₀) := lt_of_lt_of_le one_pos hs
  apply (div_le_iff₀ (mul_pos (by norm_num) hs0)).2
  nlinarith

theorem thetaDomainControlConstant_pos (p : Params) (C₀ : ℝ) :
    0 < thetaDomainControlConstant p C₀ := by
  unfold thetaDomainControlConstant
  apply lt_max_of_lt_left
  have hj : 0 < Real.sqrt (jumpBondMargin p) :=
    Real.sqrt_pos.2 (jumpBondMargin_pos p)
  exact div_pos (mul_pos (by positivity) (Real.exp_pos _)) hj

/-- Above height one the localization-length branch is exactly `W / sqrt η`. -/
theorem erLocalizationLength_eq_width_div_sqrt_of_one_lt
    (p : Params) {η : ℝ} (hη : 1 < η) :
    erLocalizationLength p η = (p.W : ℝ) / Real.sqrt η := by
  unfold erLocalizationLength
  apply min_eq_left
  have hs : 1 < Real.sqrt η := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hη
  have hdiv : (p.W : ℝ) / Real.sqrt η ≤ (p.W : ℝ) := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (lt_trans one_pos hη))]
    nlinarith [p.real_W_pos]
  exact hdiv.trans (by
    exact_mod_cast (show p.W ≤ p.n * p.W from
      Nat.le_mul_of_pos_left p.W p.n_pos))

/-- Domain norm control bounds the spectral height by the cutoff. -/
theorem spectralDomain_min_abs_im_le {p : Params} {κ ηExp C₀ : ℝ} {z₁ z₂ : ℂ}
    (h₁ : ERSpectralDomain p κ ηExp C₀ z₁) :
    min |z₁.im| |z₂.im| ≤ C₀ :=
  (min_le_left _ _).trans ((Complex.abs_im_le_norm z₁).trans h₁.2.1)

/-- High-height block decay converts to site decay at the domain-dependent rate. -/
theorem half_block_exp_le_domain_site_exp
    (p : Params) {C₀ η : ℝ} (hη : 1 < η) (hηC : η ≤ C₀)
    (x y : Site p.n p.W) :
    Real.exp (-(1 / 2 : ℝ) * cyclicBlockDistance p x.1 y.1) ≤
      Real.exp (1 / 2) *
        Real.exp (-thetaDomainDecay C₀ * (erSiteDistance p x y : ℝ) /
          erLocalizationLength p η) := by
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.2 (lt_trans one_pos hη)
  have hsC : 0 < Real.sqrt (max 1 C₀) :=
    Real.sqrt_pos.2 (lt_max_of_lt_left one_pos)
  have hηmax : η ≤ max 1 C₀ := hηC.trans (le_max_right _ _)
  have hsle : Real.sqrt η ≤ Real.sqrt (max 1 C₀) := Real.sqrt_le_sqrt hηmax
  have hsite : (erSiteDistance p x y : ℝ) ≤
      (p.W : ℝ) * cyclicBlockDistance p x.1 y.1 + p.W := by
    exact_mod_cast siteDistance_le_width_mul_cyclicBlockDistance_add_width p x y
  rw [erLocalizationLength_eq_width_div_sqrt_of_one_lt p hη, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hW : 0 < (p.W : ℝ) := p.real_W_pos
  have hrate : thetaDomainDecay C₀ * Real.sqrt η ≤ 1 / 2 := by
    unfold thetaDomainDecay
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ (mul_pos (by norm_num) hsC)).2
    nlinarith
  have hmul : thetaDomainDecay C₀ * (erSiteDistance p x y : ℝ) *
      Real.sqrt η / (p.W : ℝ) ≤
      (1 / 2) * ((cyclicBlockDistance p x.1 y.1 : ℝ) + 1) := by
    have hnonneg : 0 ≤ thetaDomainDecay C₀ * Real.sqrt η :=
      mul_nonneg (thetaDomainDecay_pos C₀).le hsη.le
    calc
      thetaDomainDecay C₀ * (erSiteDistance p x y : ℝ) * Real.sqrt η /
          (p.W : ℝ) =
        (thetaDomainDecay C₀ * Real.sqrt η) *
          ((erSiteDistance p x y : ℝ) / (p.W : ℝ)) := by ring
      _ ≤ (thetaDomainDecay C₀ * Real.sqrt η) *
          ((cyclicBlockDistance p x.1 y.1 : ℝ) + 1) := by
        gcongr
        exact (div_le_iff₀ hW).2 (by
          convert hsite using 1
          ring)
      _ ≤ (1 / 2) * ((cyclicBlockDistance p x.1 y.1 : ℝ) + 1) := by
        gcongr
  have hre : -thetaDomainDecay C₀ * (erSiteDistance p x y : ℝ) /
      ((p.W : ℝ) / Real.sqrt η) =
      -(thetaDomainDecay C₀ * (erSiteDistance p x y : ℝ) *
        Real.sqrt η / (p.W : ℝ)) := by
    field_simp
  rw [hre]
  linarith

/-- The recurrence bound gives the `Theta` clause-(i) estimate at
heights above one, with constants allowed to depend on the already fixed cutoff. -/
theorem norm_erTheta_le_domain_control_of_one_lt
    (p : Params) {κ ηExp C₀ : ℝ} {z₁ z₂ : ℂ}
    (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂)
    (hη : 1 < min |z₁.im| |z₂.im|) (x y : Site p.n p.W) :
    ‖erTheta p z₁ z₂ x y‖ ≤
      thetaDomainControlConstant p C₀ *
        erManuscriptCyclicControl p (thetaDomainDecay C₀) 8
          (min |z₁.im| |z₂.im|) x y := by
  let η : ℝ := min |z₁.im| |z₂.im|
  let M : ℝ := Real.sqrt (max 1 C₀)
  have hz₁ : z₁.im ≠ 0 := spectralDomain_im_ne_zero h₁
  have hz₂ : z₂.im ≠ 0 := spectralDomain_im_ne_zero h₂
  have hη0 : 0 < η := lt_trans one_pos hη
  have hηC : η ≤ C₀ := spectralDomain_min_abs_im_le h₁
  have hηmax : η ≤ max 1 C₀ := hηC.trans (le_max_right _ _)
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
  have hM0 : 0 < M := Real.sqrt_pos.2 (lt_max_of_lt_left one_pos)
  have hsle : Real.sqrt η ≤ M := Real.sqrt_le_sqrt hηmax
  have hbase := norm_erTheta_le_sqrt_height p hz₁ hz₂ x y
  have htrunc : truncatedHeight z₁ z₂ = 1 := by
    unfold truncatedHeight η at *
    exact min_eq_left hη.le
  rw [htrunc, Real.sqrt_one, mul_one] at hbase
  have hn : min 1 ((p.n : ℝ) * 1) = 1 := by
    apply min_eq_left
    norm_num
    exact_mod_cast p.n_pos
  rw [hn, one_mul] at hbase
  have hexp := half_block_exp_le_domain_site_exp p hη hηC x y
  have hell : erLocalizationLength p η = (p.W : ℝ) / Real.sqrt η :=
    erLocalizationLength_eq_width_div_sqrt_of_one_lt p hη
  have hbranch := exp_branch_le_erManuscriptCyclicControl p hη0
    (thetaDomainDecay C₀) x y
  have hW : 0 < (p.W : ℝ) := p.real_W_pos
  have hj : 0 < Real.sqrt (jumpBondMargin p) :=
    Real.sqrt_pos.2 (jumpBondMargin_pos p)
  let E : ℝ := Real.exp (-thetaDomainDecay C₀ *
    (erSiteDistance p x y : ℝ) / erLocalizationLength p η)
  have hE0 : 0 < E := Real.exp_pos _
  have hnorm : 1 / (erLocalizationLength p η * η) =
      1 / ((p.W : ℝ) * Real.sqrt η) := by
    rw [hell]
    field_simp
    nlinarith [Real.sq_sqrt hη0.le]
  have hsame : (if x.1 = y.1 then (1 : ℝ) else 0) ≤
      Real.exp (1 / 2) * M / Real.sqrt η * E := by
    by_cases hxy : x.1 = y.1
    · simp only [hxy, ite_true]
      have hd0 : cyclicBlockDistance p x.1 y.1 = 0 := by simp [hxy]
      have hElow : 1 ≤ Real.exp (1 / 2) * E := by
        simpa only [hd0, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, E, η]
          using hexp
      have hsratio : 1 ≤ M / Real.sqrt η := by
        apply (le_div_iff₀ hsη).2
        simpa using hsle
      calc
        1 ≤ Real.exp (1 / 2) * E := hElow
        _ ≤ (Real.exp (1 / 2) * E) * (M / Real.sqrt η) := by
          exact le_mul_of_one_le_right (by positivity) hsratio
        _ = Real.exp (1 / 2) * M / Real.sqrt η * E := by ring
    · simp [hxy]
      positivity
  have hpoint :
      (16 * Real.exp (-(1 / 2 : ℝ) * cyclicBlockDistance p x.1 y.1) /
          Real.sqrt (jumpBondMargin p) +
        (if x.1 = y.1 then 1 else 0)) / (p.W : ℝ) ≤
      (17 * Real.exp (1 / 2) * M / Real.sqrt (jumpBondMargin p)) *
        ((1 / ((p.W : ℝ) * Real.sqrt η)) * E) := by
    have hjle : Real.sqrt (jumpBondMargin p) ≤ 1 := by
      rw [← Real.sqrt_one]
      apply Real.sqrt_le_sqrt
      unfold jumpBondMargin
      exact sub_le_self _ (abs_nonneg _)
    have hM : 0 ≤ M := hM0.le
    calc
      (16 * Real.exp (-(1 / 2 : ℝ) * cyclicBlockDistance p x.1 y.1) /
          Real.sqrt (jumpBondMargin p) +
        (if x.1 = y.1 then 1 else 0)) / (p.W : ℝ) ≤
        (16 * (Real.exp (1 / 2) * E) / Real.sqrt (jumpBondMargin p) +
          (Real.exp (1 / 2) * M / Real.sqrt η * E)) / (p.W : ℝ) := by
            gcongr
      _ ≤ (17 * Real.exp (1 / 2) * M / Real.sqrt (jumpBondMargin p)) *
          ((1 / ((p.W : ℝ) * Real.sqrt η)) * E) := by
            field_simp
            nlinarith [hsle, hjle, hM, hE0.le, Real.exp_pos (1 / 2)]
  refine hbase.trans (hpoint.trans ?_)
  rw [← hnorm]
  apply mul_le_mul
  · unfold thetaDomainControlConstant
    dsimp only [M]
    exact le_max_right _ _
  · simpa only [E, η] using hbranch
  · have hell0 : 0 < erLocalizationLength p η := by
      unfold erLocalizationLength
      exact lt_min (div_pos p.real_W_pos hsη) p.real_L_pos
    exact mul_nonneg (one_div_nonneg.mpr (mul_nonneg hell0.le hη0.le)) hE0.le
  · exact (thetaDomainControlConstant_pos p C₀).le

/-- The `Theta` clause-(i) estimate for an arbitrary fixed domain
cutoff.  The decay and comparison constant are chosen after `C₀`, and the
conclusion is uniform in both spectral points, the ring size, width and sites. -/
theorem norm_erTheta_le_domain_control
    (p : Params) {κ ηExp C₀ : ℝ} {z₁ z₂ : ℂ}
    (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂)
    (x y : Site p.n p.W) :
    ‖erTheta p z₁ z₂ x y‖ ≤
      thetaDomainControlConstant p C₀ *
        erManuscriptCyclicControl p (thetaDomainDecay C₀) 8
          (min |z₁.im| |z₂.im|) x y := by
  rcases le_or_gt (min |z₁.im| |z₂.im|) 1 with hη | hη
  · have hz₁ := spectralDomain_im_ne_zero h₁
    have hz₂ := spectralDomain_im_ne_zero h₂
    refine (norm_erTheta_le_control_of_height_le_one p
      (thetaDomainDecay_le_half C₀) hz₁ hz₂ hη x y).trans ?_
    unfold thetaDomainControlConstant
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
    exact erManuscriptCyclicControl_nonneg p _ _ _
      (lt_min (abs_pos.mpr hz₁) (abs_pos.mpr hz₂)) x y
  · exact norm_erTheta_le_domain_control_of_one_lt p h₁ h₂ hη x y

/-- Common clause-(i) decay after the domain parameters `κ,C₀` have been fixed. -/
def domainKappaClause1Decay (κ C₀ b : ℝ) : ℝ :=
  min (thetaDomainDecay C₀) (xiKappaRate κ b)

theorem domainKappaClause1Decay_pos {κ C₀ b : ℝ} (hκ : 0 < κ)
    (hb0 : 0 < b) (hb : b < 1 / 2) :
    0 < domainKappaClause1Decay κ C₀ b :=
  lt_min (thetaDomainDecay_pos C₀) (xiKappaRate_pos hκ hb0 hb)

end ERGeneralVectorMDEThetaDomain
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
