module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Clause6SiteAssembly
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.GeneralVectorMDEThetaDomain
public import Mathlib

/-!
# ER clause (vi) on a fixed arbitrary spectral domain

This module extends the concrete cyclic-profile site-difference estimate of
ER Definition 2.4(vi) from cutoff one to an arbitrary fixed cutoff `C₀ ≥ 1`.
The decay is selected after `κ,C₀`, consistently with ER Definition 2.9.
No full admissibility package is asserted here.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause6DomainControl

open ERFourierInverse ERFourierAlgebra ERNearestNeighbor ERCyclicDecay ERJumpNormalization ERClause1 ERHerglotz ERScalarProfileControl ERScalarProfileSourceFaithfulNormalization ERPhysicalBridge ERClause6CyclicDifference ERClause6EndpointControl ERClause6SiteAssembly ERGeneralVectorMDEThetaDomain ERGeneralVectorMDEXiKappa

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Common decay for clause (vi), no larger than either the fixed-bond decay or
arbitrary-domain clause-(i) decay. -/
def clause6DomainDecay (p : Params) (κ C₀ : ℝ) : ℝ :=
  min (sourceFaithfulDecay p) (domainKappaClause1Decay κ C₀ p.b)

/-- Explicit comparison constant for arbitrary-domain clause (vi). -/
def clause6DomainConstant (p : Params) (_κ C₀ : ℝ) : ℝ :=
  max (2 * (1 + C₀) ^ 2 * Real.exp (5 / 2) /
      (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor) + Real.exp (1 / 2))
    (2 * thetaDomainControlConstant p C₀)

theorem clause6DomainDecay_pos (p : Params) {κ C₀ : ℝ} (hκ : 0 < κ) :
    0 < clause6DomainDecay p κ C₀ :=
  lt_min (sourceFaithfulDecay_pos p)
    (domainKappaClause1Decay_pos hκ p.b_pos p.b_lt_half)

theorem clause6DomainDecay_le_half (p : Params) (κ C₀ : ℝ) :
    clause6DomainDecay p κ C₀ ≤ 1 / 2 :=
  (min_le_left _ _).trans (sourceFaithfulDecay_le_half p)

theorem near_implies_height_le_one (p : Params) {η : ℝ}
    (hη0 : 0 < η) {b c : Site p.n p.W}
    (hnear : (erSiteDistance p b c : ℝ) + p.W < erLocalizationLength p η) :
    η ≤ 1 := by
  by_contra h
  have hη : 1 < η := lt_of_not_ge h
  have hs : 1 < Real.sqrt η := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hη
  have hell := erLocalizationLength_eq_width_div_sqrt_of_one_lt p hη
  have hdiv : (p.W : ℝ) / Real.sqrt η < p.W := by
    rw [div_lt_iff₀ (Real.sqrt_pos.2 hη0)]
    nlinarith [p.real_W_pos]
  rw [hell] at hnear
  have hw : (p.W : ℝ) ≤ (erSiteDistance p b c : ℝ) + p.W := by
    linarith [Nat.cast_nonneg (α := ℝ) (erSiteDistance p b c)]
  linarith

/-- Green part of the near branch at arbitrary cutoff.  The only new loss is
`(1+C₀)^2`, from the explicit lower bound on the Theta multiplier. -/
theorem greenDifference_div_width_near_domain
    (p : Params) {κ ηExp C₀ : ℝ} (hC₀ : 1 ≤ C₀) {z₁ z₂ : ℂ}
    (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂)
    (hthreshold : ((p.W : ℝ) / (p.L : ℝ)) ^ 2 ≤ min |z₁.im| |z₂.im|)
    (a b c : Site p.n p.W)
    (hnear : (erSiteDistance p b c : ℝ) + p.W <
      erLocalizationLength p (min |z₁.im| |z₂.im|)) :
    ‖fourierGreenKernel p
          (erSemicircleStieltjes z₁ * starRingEnd ℂ (erSemicircleStieltjes z₂)) a.1 b.1 -
        fourierGreenKernel p
          (erSemicircleStieltjes z₁ * starRingEnd ℂ (erSemicircleStieltjes z₂)) a.1 c.1‖ /
        (p.W : ℝ) ≤
      (2 * (1 + C₀) ^ 2 * Real.exp (5 / 2) /
        (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) *
        (((erSiteDistance p b c : ℝ) + p.W) /
          erLocalizationLength p (min |z₁.im| |z₂.im|)) *
        (erManuscriptCyclicControl p (clause6DomainDecay p κ C₀) 8
            (min |z₁.im| |z₂.im|) a b +
          erManuscriptCyclicControl p (clause6DomainDecay p κ C₀) 8
            (min |z₁.im| |z₂.im|) a c) := by
  let η := min |z₁.im| |z₂.im|
  let ell := erLocalizationLength p η
  let α := erSemicircleStieltjes z₁ * starRingEnd ℂ (erSemicircleStieltjes z₂)
  let D := Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor
  let B := (1 + C₀) ^ 2
  let δ := clause6DomainDecay p κ C₀
  have hz₁ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₁
  have hz₂ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₂
  have hη0 : 0 < η := by
    dsimp [η]
    exact lt_min (abs_pos.mpr hz₁) (abs_pos.mpr hz₂)
  have hη1 : η ≤ 1 := near_implies_height_le_one p hη0 hnear
  have hthreshold' : (1 / (p.n : ℝ)) ^ 2 ≤ η := by
    have hratio : (p.W : ℝ) / (p.L : ℝ) = 1 / (p.n : ℝ) := by
      rw [show (p.L : ℝ) = (p.n : ℝ) * (p.W : ℝ) by
        simp [Conventions.ModelParameters.L, Conventions.dimension]]
      field_simp [ne_of_gt p.real_W_pos]
    rw [hratio] at hthreshold
    exact hthreshold
  have hm₁0 : erSemicircleStieltjes z₁ ≠ 0 := by
    intro hm
    have h := erSemicircleStieltjes_dyson z₁
    simp [hm] at h
  have hm₂0 : erSemicircleStieltjes z₂ ≠ 0 := by
    intro hm
    have h := erSemicircleStieltjes_dyson z₂
    simp [hm] at h
  have hα0 : α ≠ 0 := mul_ne_zero hm₁0 ((map_ne_zero (starRingEnd ℂ)).2 hm₂0)
  have hα : ‖α‖ < 1 := by
    dsimp [α]
    exact norm_thetaMultiplier_lt_one
      (norm_erSemicircleStieltjes_lt_one hz₁) (norm_erSemicircleStieltjes_lt_one hz₂)
  have hmargin : η / 4 ≤ 1 - ‖α‖ := by
    have h := thetaMultiplier_height_margin hz₁ hz₂
    dsimp [η, α]
    rw [min_eq_right (by nlinarith)] at h
    exact h
  have hshort := shorter_path_is_scalar_short p hη0 hthreshold' b c hnear
  have hscalar := norm_alpha_mul_fourierGreenKernel_sub_le_shorter_endpoints
    p hα0 hα hη0 hη1 hthreshold' hmargin a.1 b.1 c.1 hshort
  have hαlower : 1 / B ≤ ‖α‖ := by
    have hlower := one_div_one_add_sq_le_norm_thetaMultiplier
      hz₁ hz₂ (zero_le_one.trans hC₀) h₁.2.1 h₂.2.1
    simpa [B, α] using hlower
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hgreenAlpha :
      ‖fourierGreenKernel p α a.1 b.1 - fourierGreenKernel p α a.1 c.1‖ ≤
        B * ‖α * (fourierGreenKernel p α a.1 b.1 -
          fourierGreenKernel p α a.1 c.1)‖ := by
    rw [norm_mul]
    have hone : 1 ≤ B * ‖α‖ := by
      have hh := (div_le_iff₀ hB0).mp hαlower
      simpa [mul_comm] using hh
    calc
      _ = 1 * ‖fourierGreenKernel p α a.1 b.1 -
          fourierGreenKernel p α a.1 c.1‖ := by ring
      _ ≤ (B * ‖α‖) * ‖fourierGreenKernel p α a.1 b.1 -
          fourierGreenKernel p α a.1 c.1‖ := by gcongr
      _ = B * (‖α‖ * ‖fourierGreenKernel p α a.1 b.1 -
          fourierGreenKernel p α a.1 c.1‖) := by ring
  have hblockScale := blockDistance_div_width_le_siteFactor p hη0 hthreshold' b c
  have hδhalf : δ ≤ 1 / 2 := clause6DomainDecay_le_half p κ C₀
  have hexpb := theta_block_exp_le_site_exp p hη0 hη1 hδhalf a b
  have hexpc := theta_block_exp_le_site_exp p hη0 hη1 hδhalf a c
  have hcontrolb := exp_branch_le_erManuscriptCyclicControl p hη0 δ a b
  have hcontrolc := exp_branch_le_erManuscriptCyclicControl p hη0 δ a c
  have hell0 : 0 < ell := by
    dsimp [ell]
    unfold erLocalizationLength
    exact lt_min (div_pos p.real_W_pos (Real.sqrt_pos.2 hη0)) p.real_L_pos
  have hD0 : 0 < D := by
    dsimp [D]
    exact mul_pos (Real.sqrt_pos.2 (mul_pos p.b_pos (jumpBondMargin_pos p)))
      fixedWrapFloor_pos
  have hsiteExp :
      (1 / (ell * η)) *
          (Real.exp (-δ * (erSiteDistance p a b : ℝ) / ell) +
            Real.exp (-δ * (erSiteDistance p a c : ℝ) / ell)) ≤
        erManuscriptCyclicControl p δ 8 η a b +
          erManuscriptCyclicControl p δ 8 η a c := by
    rw [mul_add]
    exact add_le_add (by simpa [ell, η, δ] using hcontrolb)
      (by simpa [ell, η, δ] using hcontrolc)
  change ‖fourierGreenKernel p α a.1 b.1 - fourierGreenKernel p α a.1 c.1‖ /
      (p.W : ℝ) ≤ _
  calc
    _ ≤ (B * ‖α * (fourierGreenKernel p α a.1 b.1 -
          fourierGreenKernel p α a.1 c.1)‖) / (p.W : ℝ) := by gcongr
    _ ≤ (B * ((2 * Real.exp 2 / D) * cyclicBlockDistance p b.1 c.1 *
        (Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p a.1 b.1) +
          Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p a.1 c.1)))) /
        (p.W : ℝ) := by gcongr
    _ = (2 * B * Real.exp 2 / D) *
        ((cyclicBlockDistance p b.1 c.1 : ℝ) / p.W) *
        (Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p a.1 b.1) +
          Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p a.1 c.1)) := by ring
    _ ≤ (2 * B * Real.exp 2 / D) *
        (((erSiteDistance p b c : ℝ) + p.W) / (ell ^ 2 * η)) *
        (Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p a.1 b.1) +
          Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p a.1 c.1)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hblockScale (by positivity)) (by positivity)
    _ ≤ (2 * B * Real.exp 2 / D) *
        (((erSiteDistance p b c : ℝ) + p.W) / (ell ^ 2 * η)) *
        (Real.exp (1 / 2) *
          (Real.exp (-δ * (erSiteDistance p a b : ℝ) / ell) +
            Real.exp (-δ * (erSiteDistance p a c : ℝ) / ell))) := by
      have hexpsum : Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p a.1 b.1) +
          Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p a.1 c.1) ≤
          Real.exp (1 / 2) *
            (Real.exp (-δ * (erSiteDistance p a b : ℝ) / ell) +
              Real.exp (-δ * (erSiteDistance p a c : ℝ) / ell)) := by
        calc
          _ ≤ Real.exp (1 / 2) * Real.exp (-δ * (erSiteDistance p a b : ℝ) / ell) +
            Real.exp (1 / 2) * Real.exp (-δ * (erSiteDistance p a c : ℝ) / ell) :=
              add_le_add hexpb hexpc
          _ = _ := by ring
      exact mul_le_mul_of_nonneg_left hexpsum (by positivity)
    _ = (2 * B * Real.exp (5 / 2) / D) *
        (((erSiteDistance p b c : ℝ) + p.W) / ell) *
        ((1 / (ell * η)) *
          (Real.exp (-δ * (erSiteDistance p a b : ℝ) / ell) +
            Real.exp (-δ * (erSiteDistance p a c : ℝ) / ell))) := by
      rw [show Real.exp (5 / 2) = Real.exp 2 * Real.exp (1 / 2) by
        rw [← Real.exp_add]; norm_num]
      field_simp [ne_of_gt hell0, ne_of_gt hη0]
    _ ≤ (2 * B * Real.exp (5 / 2) / D) *
        (((erSiteDistance p b c : ℝ) + p.W) / ell) *
        (erManuscriptCyclicControl p δ 8 η a b +
          erManuscriptCyclicControl p δ 8 η a c) := by
      exact mul_le_mul_of_nonneg_left hsiteExp (by positivity)
    _ = _ := by rfl

/-- The supported tensor correction with the smaller domain-dependent decay. -/
theorem blockCorrection_div_width_le_domain
    (p : Params) {κ C₀ η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η) (a b c : Site p.n p.W) :
    ‖(if a.1 = b.1 then (1 : ℂ) else 0) -
        (if a.1 = c.1 then (1 : ℂ) else 0)‖ / (p.W : ℝ) ≤
      Real.exp (1 / 2) *
        (((erSiteDistance p b c : ℝ) + p.W) / erLocalizationLength p η) *
        (erManuscriptCyclicControl p (clause6DomainDecay p κ C₀) 8 η a b +
          erManuscriptCyclicControl p (clause6DomainDecay p κ C₀) 8 η a c) := by
  refine (blockCorrection_div_width_le_sourceFaithful p hη0 hη1 hthreshold a b c).trans ?_
  have hdec : clause6DomainDecay p κ C₀ ≤ sourceFaithfulDecay p := min_le_left _ _
  have hb := erManuscriptCyclicControl_anti_decay p hdec 8 hη0 a b
  have hc := erManuscriptCyclicControl_anti_decay p hdec 8 hη0 a c
  have hell0 : 0 < erLocalizationLength p η := by
    unfold erLocalizationLength
    exact lt_min (div_pos p.real_W_pos (Real.sqrt_pos.2 hη0)) p.real_L_pos
  apply mul_le_mul_of_nonneg_left (add_le_add hb hc)
  positivity

/-- Far branch at arbitrary cutoff, using the arbitrary-height pointwise Theta
control. -/
theorem erTheta_difference_far_domain
    (p : Params) {κ ηExp C₀ : ℝ} {z₁ z₂ : ℂ}
    (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂)
    (a b c : Site p.n p.W)
    (hfar : erLocalizationLength p (min |z₁.im| |z₂.im|) ≤
      (erSiteDistance p b c : ℝ) + p.W) :
    ‖erTheta p z₁ z₂ a b - erTheta p z₁ z₂ a c‖ ≤
      clause6DomainConstant p κ C₀ *
        (min ((erSiteDistance p b c : ℝ) + p.W)
            (erLocalizationLength p (min |z₁.im| |z₂.im|)) /
          erLocalizationLength p (min |z₁.im| |z₂.im|)) *
        (erManuscriptCyclicControl p (clause6DomainDecay p κ C₀) 8
            (min |z₁.im| |z₂.im|) a b +
          erManuscriptCyclicControl p (clause6DomainDecay p κ C₀) 8
            (min |z₁.im| |z₂.im|) a c) := by
  let η := min |z₁.im| |z₂.im|
  let ell := erLocalizationLength p η
  let K := thetaDomainControlConstant p C₀
  let δ := clause6DomainDecay p κ C₀
  have hz₁ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₁
  have hz₂ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₂
  have hη0 : 0 < η := by
    dsimp [η]
    exact lt_min (abs_pos.mpr hz₁) (abs_pos.mpr hz₂)
  have hell0 : 0 < ell := by
    dsimp [ell]
    unfold erLocalizationLength
    exact lt_min (div_pos p.real_W_pos (Real.sqrt_pos.2 hη0)) p.real_L_pos
  have hb := norm_erTheta_le_domain_control p h₁ h₂ a b
  have hc := norm_erTheta_le_domain_control p h₁ h₂ a c
  have hdec : δ ≤ thetaDomainDecay C₀ := by
    dsimp [δ, clause6DomainDecay, domainKappaClause1Decay]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcb := erManuscriptCyclicControl_anti_decay p hdec 8 hη0 a b
  have hcc := erManuscriptCyclicControl_anti_decay p hdec 8 hη0 a c
  have hcontrols :
      ‖erTheta p z₁ z₂ a b - erTheta p z₁ z₂ a c‖ ≤
        K * (erManuscriptCyclicControl p δ 8 η a b +
          erManuscriptCyclicControl p δ 8 η a c) := by
    calc
      _ ≤ ‖erTheta p z₁ z₂ a b‖ + ‖erTheta p z₁ z₂ a c‖ := norm_sub_le _ _
      _ ≤ K * erManuscriptCyclicControl p (thetaDomainDecay C₀) 8 η a b +
          K * erManuscriptCyclicControl p (thetaDomainDecay C₀) 8 η a c :=
        add_le_add (by simpa [K, η] using hb) (by simpa [K, η] using hc)
      _ ≤ K * erManuscriptCyclicControl p δ 8 η a b +
          K * erManuscriptCyclicControl p δ 8 η a c := by
        have hK0 : 0 ≤ K := by
          dsimp [K]
          exact (thetaDomainControlConstant_pos p C₀).le
        exact add_le_add (mul_le_mul_of_nonneg_left hcb hK0)
          (mul_le_mul_of_nonneg_left hcc hK0)
      _ = K * (erManuscriptCyclicControl p δ 8 η a b +
          erManuscriptCyclicControl p δ 8 η a c) := by ring
  have hmin : min ((erSiteDistance p b c : ℝ) + p.W) ell = ell := min_eq_right hfar
  rw [show min |z₁.im| |z₂.im| = η by rfl]
  change _ ≤ clause6DomainConstant p κ C₀ *
    (min ((erSiteDistance p b c : ℝ) + p.W) ell / ell) * _
  rw [hmin, div_self (ne_of_gt hell0), mul_one]
  refine hcontrols.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · unfold K clause6DomainConstant
    exact (le_mul_of_one_le_left (thetaDomainControlConstant_pos p C₀).le
      (by norm_num : (1 : ℝ) ≤ 2)).trans (le_max_right _ _)
  · exact add_nonneg
      (erManuscriptCyclicControl_nonneg p _ _ _ hη0 a b)
      (erManuscriptCyclicControl_nonneg p _ _ _ hη0 a c)

/-- Near branch at arbitrary cutoff. -/
theorem erTheta_difference_near_domain
    (p : Params) {κ ηExp C₀ : ℝ} (hC₀ : 1 ≤ C₀) {z₁ z₂ : ℂ}
    (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂)
    (hthreshold : ((p.W : ℝ) / (p.L : ℝ)) ^ 2 ≤ min |z₁.im| |z₂.im|)
    (a b c : Site p.n p.W)
    (hnear : (erSiteDistance p b c : ℝ) + p.W <
      erLocalizationLength p (min |z₁.im| |z₂.im|)) :
    ‖erTheta p z₁ z₂ a b - erTheta p z₁ z₂ a c‖ ≤
      clause6DomainConstant p κ C₀ *
        (min ((erSiteDistance p b c : ℝ) + p.W)
            (erLocalizationLength p (min |z₁.im| |z₂.im|)) /
          erLocalizationLength p (min |z₁.im| |z₂.im|)) *
        (erManuscriptCyclicControl p (clause6DomainDecay p κ C₀) 8
            (min |z₁.im| |z₂.im|) a b +
          erManuscriptCyclicControl p (clause6DomainDecay p κ C₀) 8
            (min |z₁.im| |z₂.im|) a c) := by
  let η := min |z₁.im| |z₂.im|
  let ell := erLocalizationLength p η
  let α := erSemicircleStieltjes z₁ * starRingEnd ℂ (erSemicircleStieltjes z₂)
  let Kg := 2 * (1 + C₀) ^ 2 * Real.exp (5 / 2) /
    (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)
  let Kc := Real.exp (1 / 2)
  let δ := clause6DomainDecay p κ C₀
  let F := (((erSiteDistance p b c : ℝ) + p.W) / ell) *
    (erManuscriptCyclicControl p δ 8 η a b +
      erManuscriptCyclicControl p δ 8 η a c)
  have hz₁ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₁
  have hz₂ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₂
  have hη0 : 0 < η := by
    dsimp [η]
    exact lt_min (abs_pos.mpr hz₁) (abs_pos.mpr hz₂)
  have hη1 : η ≤ 1 := near_implies_height_le_one p hη0 hnear
  have hthreshold' : (1 / (p.n : ℝ)) ^ 2 ≤ η := by
    have hratio : (p.W : ℝ) / (p.L : ℝ) = 1 / (p.n : ℝ) := by
      rw [show (p.L : ℝ) = (p.n : ℝ) * (p.W : ℝ) by
        simp [Conventions.ModelParameters.L, Conventions.dimension]]
      field_simp [ne_of_gt p.real_W_pos]
    rw [hratio] at hthreshold
    exact hthreshold
  have hgreen := greenDifference_div_width_near_domain
    p hC₀ h₁ h₂ hthreshold a b c hnear
  have hcorr := blockCorrection_div_width_le_domain
    p (κ := κ) (C₀ := C₀) hη0 hη1 hthreshold' a b c
  have hF0 : 0 ≤ F := by
    have hell0 : 0 < ell := by
      dsimp [ell]
      unfold erLocalizationLength
      exact lt_min (div_pos p.real_W_pos (Real.sqrt_pos.2 hη0)) p.real_L_pos
    dsimp [F]
    exact mul_nonneg (div_nonneg (by positivity) hell0.le)
      (add_nonneg
        (erManuscriptCyclicControl_nonneg p _ _ _ hη0 a b)
        (erManuscriptCyclicControl_nonneg p _ _ _ hη0 a c))
  have hK : Kg + Kc ≤ clause6DomainConstant p κ C₀ := by
    unfold clause6DomainConstant
    exact le_max_left _ _
  have htensor :
      ‖erTheta p z₁ z₂ a b - erTheta p z₁ z₂ a c‖ ≤ (Kg + Kc) * F := by
    rw [erTheta_sub_eq_green_sub_blockCorrection_div_width p hz₁ hz₂]
    rw [norm_div, show ‖(p.W : ℂ)‖ = (p.W : ℝ) by simp]
    have hsplit :
        ‖(fourierGreenKernel p α a.1 b.1 - (if a.1 = b.1 then 1 else 0)) -
            (fourierGreenKernel p α a.1 c.1 - (if a.1 = c.1 then 1 else 0))‖ ≤
          ‖fourierGreenKernel p α a.1 b.1 - fourierGreenKernel p α a.1 c.1‖ +
            ‖(if a.1 = b.1 then (1 : ℂ) else 0) -
              (if a.1 = c.1 then (1 : ℂ) else 0)‖ := by
      have heq :
          (fourierGreenKernel p α a.1 b.1 - (if a.1 = b.1 then 1 else 0)) -
            (fourierGreenKernel p α a.1 c.1 - (if a.1 = c.1 then 1 else 0)) =
          (fourierGreenKernel p α a.1 b.1 - fourierGreenKernel p α a.1 c.1) -
            ((if a.1 = b.1 then (1 : ℂ) else 0) -
              (if a.1 = c.1 then (1 : ℂ) else 0)) := by ring
      rw [heq]
      exact norm_sub_le _ _
    calc
      _ ≤ (‖fourierGreenKernel p α a.1 b.1 - fourierGreenKernel p α a.1 c.1‖ +
            ‖(if a.1 = b.1 then (1 : ℂ) else 0) -
              (if a.1 = c.1 then (1 : ℂ) else 0)‖) / (p.W : ℝ) := by
        exact div_le_div_of_nonneg_right hsplit (by positivity)
      _ = ‖fourierGreenKernel p α a.1 b.1 - fourierGreenKernel p α a.1 c.1‖ /
            (p.W : ℝ) +
          ‖(if a.1 = b.1 then (1 : ℂ) else 0) -
              (if a.1 = c.1 then (1 : ℂ) else 0)‖ / (p.W : ℝ) := by ring
      _ ≤ Kg * F + Kc * F := add_le_add
        (by simpa [Kg, F, ell, η, α, δ, mul_assoc] using hgreen)
        (by simpa [Kc, F, ell, η, δ, mul_assoc] using hcorr)
      _ = (Kg + Kc) * F := by ring
  have hmin : min ((erSiteDistance p b c : ℝ) + p.W) ell =
      (erSiteDistance p b c : ℝ) + p.W := min_eq_left hnear.le
  rw [show min |z₁.im| |z₂.im| = η by rfl]
  change _ ≤ clause6DomainConstant p κ C₀ *
    (min ((erSiteDistance p b c : ℝ) + p.W) ell / ell) * _
  rw [hmin]
  exact htensor.trans (by
    dsimp [F]
    nlinarith [mul_le_mul_of_nonneg_right hK hF0])

/-- Source-faithful ER Definition 2.4(vi) for the concrete cyclic profile on
an arbitrary fixed domain cutoff `C₀ ≥ 1`. -/
theorem clause6_domain
    (p : Params) {κ ηExp C₀ : ℝ} (hC₀ : 1 ≤ C₀) {z₁ z₂ : ℂ}
    (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂)
    (_hsame : ERSameHalfPlane z₁ z₂)
    (hthreshold : ((p.W : ℝ) / (p.L : ℝ)) ^ 2 ≤ min |z₁.im| |z₂.im|)
    (a b c : Site p.n p.W) :
    ‖erTheta p z₁ z₂ a b - erTheta p z₁ z₂ a c‖ ≤
      clause6DomainConstant p κ C₀ *
        (min ((erSiteDistance p b c : ℝ) + p.W)
            (erLocalizationLength p (min |z₁.im| |z₂.im|)) /
          erLocalizationLength p (min |z₁.im| |z₂.im|)) *
        (erManuscriptCyclicControl p (clause6DomainDecay p κ C₀) 8
            (min |z₁.im| |z₂.im|) a b +
          erManuscriptCyclicControl p (clause6DomainDecay p κ C₀) 8
            (min |z₁.im| |z₂.im|) a c) := by
  by_cases hfar : erLocalizationLength p (min |z₁.im| |z₂.im|) ≤
      (erSiteDistance p b c : ℝ) + p.W
  · exact erTheta_difference_far_domain p h₁ h₂ a b c hfar
  · exact erTheta_difference_near_domain p hC₀ h₁ h₂ hthreshold a b c
      (lt_of_not_ge hfar)

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause6DomainControl
