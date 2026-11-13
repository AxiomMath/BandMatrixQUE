module

public import BlockBand.Adapters.ErdosRiabov.ShortRingBridge
public import BlockBand.Adapters.ErdosRiabov.Clause23
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.GeneralVectorMDEThetaDomain
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Clause7DomainControl

/-!
# Clauses (i), (vi), (vii) of Erdős–Riabov admissibility from the Green-function bounds

The polynomial control `Υ_η` satisfies the majoration clause (i) for both `Θ` and `Ξ`, and
clauses (vi) and (vii) of Erdős–Riabov Definition 2.4, derived from the exponential
Green-function bounds of the cyclic ring.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open BlockBand.External
open scoped BigOperators

local instance (p : CyclicModel.Params) : NeZero p.n := p.nNeZero

/-- The exponential cyclic control `erManuscriptCyclicControl p a 8 η` is dominated by
`(1 + D/a)^D` times the polynomial control `Υ_η` with exponent `D`. -/
theorem cyclicControl_le_poly (p : CyclicModel.Params) {a D : ℝ} (ha : 0 < a) (hD : 0 < D) {η : ℝ}
    (hη : 0 < η) (x y : CyclicModel.Conventions.Site p.n p.W) :
    CyclicModel.GaussianRing.erManuscriptCyclicControl p a 8 η x y ≤
      (1 + D / a) ^ D *
        Internal.Contracts.Inputs.polynomialControl (p.n * p.W) p.W D η (siteEquiv p x)
          (siteEquiv p y) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos p.n_pos p.W_pos
  have hl := loc_pos hN p.W_pos hη
  rw [polynomialControl_eq hN p.W_pos D hη, cyclicDistance_siteEquiv]
  show (1 / (CyclicModel.GaussianRing.erLocalizationLength p η * η)) *
      Real.exp (-a * (CyclicModel.GaussianRing.erSiteDistance p x y : ℝ) /
        CyclicModel.GaussianRing.erLocalizationLength p η) ≤ _
  rw [← localizationLength_eq_erLocalizationLength]
  set l := ErdosRiabov.localizationLength (p.n * p.W) p.W η
  set d : ℝ := (CyclicModel.GaussianRing.erSiteDistance p x y : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have he := exp_neg_le_decay ha hD (div_nonneg hd hl.le)
  rw [show -a * d / l = -(a * (d / l)) by ring]
  unfold decayF
  rw [one_div]
  have : 0 < (l * η)⁻¹ := by positivity
  calc (l * η)⁻¹ * Real.exp (-(a * (d / l))) ≤ (l * η)⁻¹ * ((1 + D / a) ^ D * ((1 + d / l) ^ D)⁻¹) := by
        gcongr
    _ = _ := by ring

/-- `thetaDomainControlConstant p C₀` depends on `p` only through the bond weight `b`. -/
theorem thetaDomainControlConstant_congr (p q : CyclicModel.Params) (h : p.b = q.b) (C₀ : ℝ) :
    CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainControlConstant p C₀ =
      CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainControlConstant q C₀ := by
  simp only [CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainControlConstant,
    CyclicModel.GaussianRing.ERJumpNormalization.jumpBondMargin, CyclicModel.Params.c, h]

theorem clause6DomainConstant_congr (p q : CyclicModel.Params) (h : p.b = q.b) (κ C₀ : ℝ) :
    CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainConstant p κ C₀ =
      CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainConstant q κ C₀ := by
  simp only [CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainConstant,
    thetaDomainControlConstant_congr p q h,
    CyclicModel.GaussianRing.ERJumpNormalization.jumpBondMargin, CyclicModel.Params.c, h]

theorem clause6DomainDecay_congr (p q : CyclicModel.Params) (h : p.b = q.b) (κ C₀ : ℝ) :
    CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainDecay p κ C₀ =
      CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainDecay q κ C₀ := by
  simp only [CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainDecay,
    CyclicModel.GaussianRing.ERScalarProfileSourceFaithfulNormalization.sourceFaithfulDecay, h]

theorem clause67DomainConstant_congr (p q : CyclicModel.Params) (h : p.b = q.b) (κ C₀ : ℝ) :
    CyclicModel.GaussianRing.ERClause7DomainControl.clause67DomainConstant p κ C₀ =
      CyclicModel.GaussianRing.ERClause7DomainControl.clause67DomainConstant q κ C₀ := by
  simp only [CyclicModel.GaussianRing.ERClause7DomainControl.clause67DomainConstant,
    clause6DomainConstant_congr p q h, h]

/-- The Erdős–Riabov spectral domain at `N = nW` is contained in the cyclic-model domain
`ERSpectralDomain`. -/
theorem erSpectralDomain_of_spectralDomain (q : ErdosRiabov.ModelParameters) (p : CyclicModel.Params) {z : ℂ}
    (hz : ErdosRiabov.SpectralDomain q (p.n * p.W) z) :
    CyclicModel.GaussianRing.ERSpectralDomain p q.kappa q.delta0 q.C0 z :=
  (spectralDomain_iff_erSpectralDomain q p z).1 hz

/-- Clause (i), `Θ` half: `‖Θ_xy‖ ≤ K Υ_{min|Im z|}(x,y)`. -/
theorem clause1_theta (q : ErdosRiabov.ModelParameters) (p : CyclicModel.Params) {D : ℝ} (hD : 0 < D)
    {z₁ z₂ : ℂ} (h₁ : ErdosRiabov.SpectralDomain q (p.n * p.W) z₁)
    (h₂ : ErdosRiabov.SpectralDomain q (p.n * p.W) z₂) (x y : Fin (p.n * p.W)) :
    ‖ErdosRiabov.theta (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) z₁ z₂ x y‖ ≤
      CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainControlConstant p q.C0 *
          (1 + D / CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainDecay q.C0) ^ D *
        Internal.Contracts.Inputs.polynomialControl (p.n * p.W) p.W D (min |z₁.im| |z₂.im|)
          x y := by
  have l₁ := erSpectralDomain_of_spectralDomain q p h₁
  have l₂ := erSpectralDomain_of_spectralDomain q p h₂
  have hη : 0 < min |z₁.im| |z₂.im| :=
    lt_min (abs_pos.2 (CyclicModel.GaussianRing.ERDeterministicMDECore.spectralDomain_im_ne_zero l₁))
      (abs_pos.2 (CyclicModel.GaussianRing.ERDeterministicMDECore.spectralDomain_im_ne_zero l₂))
  obtain ⟨x, rfl⟩ := (siteEquiv p).surjective x
  obtain ⟨y, rfl⟩ := (siteEquiv p).surjective y
  rw [theta_siteEquiv]
  refine (CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.norm_erTheta_le_domain_control
    p l₁ l₂ x y).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (cyclicControl_le_poly p
    (CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainDecay_pos q.C0) hD hη x y)
    (CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainControlConstant_pos p q.C0).le

/-- Clause (i), `Ξ` half: `‖Ξ_xy‖ ≤ K Υ_1(x,y)`. -/
theorem clause1_xi (q : ErdosRiabov.ModelParameters) (p : CyclicModel.Params) {D : ℝ} (hD : 0 < D)
    {z₁ z₂ : ℂ} (h₁ : ErdosRiabov.SpectralDomain q (p.n * p.W) z₁)
    (h₂ : ErdosRiabov.SpectralDomain q (p.n * p.W) z₂) (hs : ErdosRiabov.SameHalfPlane z₁ z₂)
    (x y : Fin (p.n * p.W)) :
    ‖ErdosRiabov.xi (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) z₁ z₂ x y‖ ≤
      CyclicModel.GaussianRing.ERGeneralVectorMDEXiKappa.xiKappaControlConstant q.kappa p.b *
          (1 + D / CyclicModel.GaussianRing.ERGeneralVectorMDEXiKappa.xiKappaRate q.kappa p.b) ^ D *
        Internal.Contracts.Inputs.polynomialControl (p.n * p.W) p.W D 1 x y := by
  have l₁ := erSpectralDomain_of_spectralDomain q p h₁
  have l₂ := erSpectralDomain_of_spectralDomain q p h₂
  obtain ⟨x, rfl⟩ := (siteEquiv p).surjective x
  obtain ⟨y, rfl⟩ := (siteEquiv p).surjective y
  rw [xi_siteEquiv]
  refine (CyclicModel.GaussianRing.ERGeneralVectorMDEXiKappa.norm_erXi_le_xi_kappa_control
    p q.kappa_pos l₁ l₂ hs x y).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (cyclicControl_le_poly p
    (CyclicModel.GaussianRing.ERGeneralVectorMDEXiKappa.xiKappaRate_pos q.kappa_pos p.b_pos
      p.b_lt_half) hD one_pos x y)
    (CyclicModel.GaussianRing.ERGeneralVectorMDEXiKappa.xiKappaControlConstant_pos q.kappa_pos p.b_pos
      p.b_lt_half).le

/-- Clause (vi), with threshold `(W/N)² ≤ η`. -/
theorem clause6_poly (q : ErdosRiabov.ModelParameters) (p : CyclicModel.Params) {D : ℝ} (hD : 0 < D)
    {z₁ z₂ : ℂ} (h₁ : ErdosRiabov.SpectralDomain q (p.n * p.W) z₁)
    (h₂ : ErdosRiabov.SpectralDomain q (p.n * p.W) z₂) (hs : ErdosRiabov.SameHalfPlane z₁ z₂)
    (hthr : ((p.W : ℝ) / ((p.n * p.W : ℕ) : ℝ)) ^ 2 ≤ min |z₁.im| |z₂.im|)
    (a b c : Fin (p.n * p.W)) :
    ‖ErdosRiabov.theta (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) z₁ z₂ a b -
        ErdosRiabov.theta (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) z₁ z₂ a c‖ ≤
      CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainConstant p q.kappa q.C0 *
          (1 + D / CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainDecay p q.kappa
            q.C0) ^ D *
        (min ((ErdosRiabov.cyclicDistance (p.n * p.W) b c : ℝ) + p.W)
            (ErdosRiabov.localizationLength (p.n * p.W) p.W (min |z₁.im| |z₂.im|)) /
          ErdosRiabov.localizationLength (p.n * p.W) p.W (min |z₁.im| |z₂.im|)) *
        (Internal.Contracts.Inputs.polynomialControl (p.n * p.W) p.W D (min |z₁.im| |z₂.im|) a b +
          Internal.Contracts.Inputs.polynomialControl (p.n * p.W) p.W D (min |z₁.im| |z₂.im|)
            a c) := by
  have l₁ := erSpectralDomain_of_spectralDomain q p h₁
  have l₂ := erSpectralDomain_of_spectralDomain q p h₂
  have hη : 0 < min |z₁.im| |z₂.im| :=
    lt_min (abs_pos.2 (CyclicModel.GaussianRing.ERDeterministicMDECore.spectralDomain_im_ne_zero l₁))
      (abs_pos.2 (CyclicModel.GaussianRing.ERDeterministicMDECore.spectralDomain_im_ne_zero l₂))
  have hC₀ : 1 ≤ q.C0 := q.C0_ge_one
  have hdec := CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainDecay_pos p
    (C₀ := q.C0) q.kappa_pos
  have hθ := CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainControlConstant_pos p q.C0
  have hK : 0 ≤ CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainConstant p q.kappa q.C0 :=
    le_trans (by linarith) (le_max_right _ _)
  obtain ⟨a, rfl⟩ := (siteEquiv p).surjective a
  obtain ⟨b, rfl⟩ := (siteEquiv p).surjective b
  obtain ⟨c, rfl⟩ := (siteEquiv p).surjective c
  rw [theta_siteEquiv, theta_siteEquiv, cyclicDistance_siteEquiv, localizationLength_eq_erLocalizationLength]
  refine (CyclicModel.GaussianRing.ERClause6DomainControl.clause6_domain p hC₀ l₁ l₂ hs hthr
    a b c).trans ?_
  have hl := loc_pos (Nat.mul_pos p.n_pos p.W_pos) p.W_pos hη
  rw [localizationLength_eq_erLocalizationLength] at hl
  have hwt : 0 ≤ min ((CyclicModel.GaussianRing.erSiteDistance p b c : ℝ) + p.W)
      (CyclicModel.GaussianRing.erLocalizationLength p (min |z₁.im| |z₂.im|)) /
        CyclicModel.GaussianRing.erLocalizationLength p (min |z₁.im| |z₂.im|) :=
    div_nonneg (le_min (by positivity) hl.le) hl.le
  have e1 := cyclicControl_le_poly p hdec hD hη a b
  have e2 := cyclicControl_le_poly p hdec hD hη a c
  calc _ ≤ CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainConstant p q.kappa q.C0 *
        (min ((CyclicModel.GaussianRing.erSiteDistance p b c : ℝ) + p.W)
            (CyclicModel.GaussianRing.erLocalizationLength p (min |z₁.im| |z₂.im|)) /
          CyclicModel.GaussianRing.erLocalizationLength p (min |z₁.im| |z₂.im|)) *
        ((1 + D / CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainDecay p q.kappa
            q.C0) ^ D *
          (Internal.Contracts.Inputs.polynomialControl (p.n * p.W) p.W D (min |z₁.im| |z₂.im|)
              (siteEquiv p a) (siteEquiv p b) +
            Internal.Contracts.Inputs.polynomialControl (p.n * p.W) p.W D
              (min |z₁.im| |z₂.im|) (siteEquiv p a) (siteEquiv p c))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hwt)
        rw [mul_add]
        exact add_le_add e1 e2
    _ = _ := by ring

/-- Clause (vii). -/
theorem clause7_poly (q : ErdosRiabov.ModelParameters) (p : CyclicModel.Params)
    {z₁ z₂ : ℂ} (h₁ : ErdosRiabov.SpectralDomain q (p.n * p.W) z₁)
    (h₂ : ErdosRiabov.SpectralDomain q (p.n * p.W) z₂) (hs : ErdosRiabov.SameHalfPlane z₁ z₂)
    (a b : Fin (p.n * p.W)) :
    ‖ErdosRiabov.theta (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) z₁ z₂ a b -
        (1 / ((p.n * p.W : ℕ) : ℂ)) *
          ∑ c, ErdosRiabov.theta (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W)
            z₁ z₂ a c‖ ≤
      CyclicModel.GaussianRing.ERClause7DomainControl.clause67DomainConstant p q.kappa q.C0 *
        ((p.n * p.W : ℕ) : ℝ) / (p.W : ℝ) ^ 2 := by
  have l₁ := erSpectralDomain_of_spectralDomain q p h₁
  have l₂ := erSpectralDomain_of_spectralDomain q p h₂
  obtain ⟨a, rfl⟩ := (siteEquiv p).surjective a
  obtain ⟨b, rfl⟩ := (siteEquiv p).surjective b
  rw [theta_siteEquiv, ← Equiv.sum_comp (siteEquiv p)]
  simp only [theta_siteEquiv]
  exact CyclicModel.GaussianRing.ERClause7DomainControl.erTheta_zeroModeSubtracted_le_domain p l₁ l₂
    hs a b

end BlockBand.Adapters.ErdosRiabov
