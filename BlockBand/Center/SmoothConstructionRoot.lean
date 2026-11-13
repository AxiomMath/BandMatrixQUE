module

public import BlockBand.Center.SmoothConstructionLinear

/-!
# The Dyson root as a smooth function on the shift lines

* §1 `scnLine H₀ x = H₀ + Σ_g x_g P_{S_g}` keeps Hermitian, ring-banded and invertible exterior
  bonds; the full matrix `scnPsi` is affine, hence `C^∞`, in `(ξ, E, ζ)`, and its inverse is `C^∞`
  wherever `Im ζ ≠ 0`.
* §2 `scnRoot`: the (globally unique, `ctr_root_unique`) upper-half-plane Dyson root, `0` if none;
  **`scn_root_contDiffAt`**: along a shift line through Hermitian, ring-banded, exterior-bond-
  invertible `H₀`, the root is `C^∞` jointly in `(ξ, E)` at every point where it exists (implicit
  function theorem; the Jacobian `1 - (s/N_aux) Tr ℛ²` is nonzero by `scn_stability`), and it
  exists nearby.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate Matrix.Norms.L2Operator ContDiff

/-!
## 1. Shift lines
-/

section Line

variable {p : Parameters} {e : ZMod p.n}

/-- The shift line `H₀ + Σ_g x_g P_{S_g}` (`x = (ξ, E)`; only `ξ` enters). -/
def scnLine (H₀ : p.SiteMatrix) (x : (ZMod p.n → ℝ) × ℝ) : p.SiteMatrix :=
  H₀ + ∑ g, ((x.1 g : ℝ) : ℂ) • pairProjector p g

theorem scn_sum_projector_offdiag (c : ZMod p.n → ℝ) {x y : p.Site} (h : x ≠ y) :
    (∑ g, ((c g : ℝ) : ℂ) • pairProjector p g) x y = 0 := by
  rw [Matrix.sum_apply]
  refine Finset.sum_eq_zero fun g _ => ?_
  simp [pairProjector, Matrix.diagonal_apply_ne _ h]

theorem scn_sum_projector_isHermitian (c : ZMod p.n → ℝ) :
    (∑ g, ((c g : ℝ) : ℂ) • pairProjector p g).IsHermitian := by
  ext x y
  by_cases h : x = y
  · subst h
    simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply, pairProjector,
      Matrix.diagonal_apply_eq, smul_eq_mul, star_sum, star_mul', Complex.star_def,
      Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp
  · rw [Matrix.conjTranspose_apply, scn_sum_projector_offdiag c h,
      scn_sum_projector_offdiag c (Ne.symm h), star_zero]

theorem scn_line_isHermitian {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (x : (ZMod p.n → ℝ) × ℝ) :
    (scnLine H₀ x).IsHermitian :=
  hH.add (scn_sum_projector_isHermitian x.1)

theorem scn_line_apply_ne (H₀ : p.SiteMatrix) (x : (ZMod p.n → ℝ) × ℝ) {a b : p.Site}
    (h : a ≠ b) : scnLine H₀ x a b = H₀ a b := by
  unfold scnLine
  rw [Matrix.add_apply, scn_sum_projector_offdiag x.1 h, add_zero]

theorem scn_line_banded {H₀ : p.SiteMatrix} (hb : IsRingBanded p H₀) (x : (ZMod p.n → ℝ) × ℝ) :
    IsRingBanded p (scnLine H₀ x) := by
  intro a b hab
  have hne : a ≠ b := by
    intro h; subst h; exact hab (Or.inl rfl)
  rw [scn_line_apply_ne H₀ x hne]
  exact hb a b hab

theorem scn_line_bonds {H₀ : p.SiteMatrix} (hb : ExteriorBondsInvertible p e H₀)
    (x : (ZMod p.n → ℝ) × ℝ) : ExteriorBondsInvertible p e (scnLine H₀ x) := by
  intro k hk
  have heq : (Matrix.of fun a c : Fin p.W => scnLine H₀ x (k, a) (k + 1, c)) =
      Matrix.of fun a c : Fin p.W => H₀ (k, a) (k + 1, c) := by
    ext a c
    simp only [Matrix.of_apply]
    refine scn_line_apply_ne H₀ x ?_
    intro h
    exact BlockBand.Layers.rng_add_one_ne p k (congrArg Prod.fst h).symm
  rw [heq]
  exact hb k hk

theorem scn_line_single (H₀ : p.SiteMatrix) (g : ZMod p.n) (t E : ℝ) :
    scnLine H₀ ((Pi.single g t : ZMod p.n → ℝ), E) = H₀ + (t : ℂ) • pairProjector p g := by
  unfold scnLine
  rw [sc_sum_single]

/-- The full matrix along the shift line, as a function of `((ξ, E), ζ)`. -/
def scnPsi (p : Parameters) (e : ZMod p.n) (H₀ : p.SiteMatrix)
    (v : ((ZMod p.n → ℝ) × ℝ) × ℂ) : p.SiteMatrix :=
  ctrFull p e (scnLine H₀ v.1) v.1.2 v.2

theorem scn_psi_det_ne {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) (v : ((ZMod p.n → ℝ) × ℝ) × ℂ) (hv : v.2.im ≠ 0) :
    (scnPsi p e H₀ v).det ≠ 0 :=
  scn_ctrFull_det_ne (scn_line_isHermitian hH v.1) (scn_line_banded hb v.1)
    (scn_line_bonds hbd v.1) v.1.2 hv

theorem scn_contDiff_psi (H₀ : p.SiteMatrix) : ContDiff ℝ ∞ (scnPsi p e H₀) := by
  unfold scnPsi ctrFull scnLine
  have h1 : ContDiff ℝ ∞ (fun v : ((ZMod p.n → ℝ) × ℝ) × ℂ =>
      ∑ g, ((v.1.1 g : ℝ) : ℂ) • pairProjector p g) := by
    refine ContDiff.sum fun g _ => ?_
    have : (fun v : ((ZMod p.n → ℝ) × ℝ) × ℂ => ((v.1.1 g : ℝ) : ℂ) • pairProjector p g) =
        fun v => (v.1.1 g) • pairProjector p g := by
      funext v; rw [Complex.coe_smul]
    rw [this]
    exact ((contDiff_apply ℝ ℝ g).comp (contDiff_fst.comp contDiff_fst)).smul contDiff_const
  have h2 : ContDiff ℝ ∞ (fun v : ((ZMod p.n → ℝ) × ℝ) × ℂ =>
      ((v.1.2 : ℝ) : ℂ) • (1 : p.SiteMatrix)) := by
    have : (fun v : ((ZMod p.n → ℝ) × ℝ) × ℂ => ((v.1.2 : ℝ) : ℂ) • (1 : p.SiteMatrix)) =
        fun v => (v.1.2) • (1 : p.SiteMatrix) := by
      funext v; rw [Complex.coe_smul]
    rw [this]
    exact (contDiff_snd.comp contDiff_fst).smul contDiff_const
  have h3 : ContDiff ℝ ∞ (fun v : ((ZMod p.n → ℝ) × ℝ) × ℂ => v.2 • pairProjector p e) :=
    contDiff_snd.smul contDiff_const
  exact ((contDiff_const.add h1).sub h2).sub h3

theorem scn_contDiffAt_psi_inv (H₀ : p.SiteMatrix) {v : ((ZMod p.n → ℝ) × ℝ) × ℂ}
    (hv : (scnPsi p e H₀ v).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun w => (scnPsi p e H₀ w)⁻¹) v := by
  have hU : IsUnit (scnPsi p e H₀ v) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv)
  have e1 : (fun w => (scnPsi p e H₀ w)⁻¹) = fun w => Ring.inverse (scnPsi p e H₀ w) := by
    funext w; rw [Matrix.nonsing_inv_eq_ringInverse]
  rw [e1]
  have hinv := contDiffAt_ringInverse ℝ (n := ∞) hU.unit
  rw [IsUnit.unit_spec] at hinv
  exact hinv.comp v (scn_contDiff_psi H₀).contDiffAt

end Line

/-!
## 2. The root function and the implicit-function theorem
-/

section Root

variable {p : Parameters} {e : ZMod p.n}

/-- The trace over the pair `S_e` of a site matrix, `Σ_{z ∈ S_e} M_zz`, as a real-linear map. -/
def scnTrS (p : Parameters) (e : ZMod p.n) : p.SiteMatrix →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => ∑ z : PairSite p e, M z.1 z.1
      map_add' := fun A B => by simp only [Matrix.add_apply, Finset.sum_add_distrib]
      map_smul' := fun r A => by
        simp only [Matrix.smul_apply, RingHom.id_apply, Finset.smul_sum] }

theorem scn_trS_apply (A : p.SiteMatrix) : scnTrS p e A = (scnBlk A e e).trace := rfl

/-- The Dyson equation `F(ξ, E, ζ) = ζ - (s/N_aux) Tr ℛ(ζ)` along the shift line. -/
def scnF (p : Parameters) (e : ZMod p.n) (H₀ : p.SiteMatrix)
    (v : ((ZMod p.n → ℝ) × ℝ) × ℂ) : ℂ :=
  v.2 - (ctrK p : ℂ) * scnTrS p e (scnPsi p e H₀ v)⁻¹

theorem scn_isDysonRoot_iff (H₀ : p.SiteMatrix) (v : ((ZMod p.n → ℝ) × ℝ) × ℂ) :
    IsDysonRoot p e (scnLine H₀ v.1) v.1.2 v.2 ↔ 0 < v.2.im ∧ scnF p e H₀ v = 0 := by
  unfold IsDysonRoot scnF
  rw [← ctrK_coe, sub_eq_zero]
  rfl

/-- The upper-half-plane Dyson root (unique for Hermitian `H`), `0` if there is none. -/
def scnRoot (p : Parameters) (e : ZMod p.n) (H : p.SiteMatrix) (E : ℝ) : ℂ := by
  classical
  exact if h : ∃ ζ, IsDysonRoot p e H E ζ then Classical.choose h else 0

theorem scn_root_spec {H : p.SiteMatrix} {E : ℝ} (h : ∃ ζ, IsDysonRoot p e H E ζ) :
    IsDysonRoot p e H E (scnRoot p e H E) := by
  unfold scnRoot
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem scn_root_eq {H : p.SiteMatrix} (hH : H.IsHermitian) {E : ℝ} {ζ : ℂ}
    (h : IsDysonRoot p e H E ζ) : scnRoot p e H E = ζ :=
  ctr_root_unique hH (scn_root_spec ⟨ζ, h⟩) h

theorem scn_contDiffAt_F {H₀ : p.SiteMatrix} {v : ((ZMod p.n → ℝ) × ℝ) × ℂ}
    (hv : (scnPsi p e H₀ v).det ≠ 0) : ContDiffAt ℝ ∞ (scnF p e H₀) v := by
  unfold scnF
  refine contDiffAt_snd.sub (contDiffAt_const.mul ?_)
  exact (scnTrS p e).contDiff.contDiffAt.comp v (scn_contDiffAt_psi_inv H₀ hv)

/-- The partial derivative of the Dyson equation in `ζ` is multiplication by the Jacobian
`J = 1 - (s/N_aux) Tr_S (A P_S A)`, `A = (H - E - ζP_S)⁻¹`. -/
theorem scn_hasFDerivAt_F_zeta (H₀ : p.SiteMatrix) (v : ((ZMod p.n → ℝ) × ℝ) × ℂ)
    (hv : (scnPsi p e H₀ v).det ≠ 0) :
    HasFDerivAt (fun ζ : ℂ => scnF p e H₀ (v.1, ζ))
      ((1 - (ctrK p : ℂ) * scnTrS p e ((scnPsi p e H₀ v)⁻¹ * pairProjector p e *
        (scnPsi p e H₀ v)⁻¹)) • ContinuousLinearMap.id ℝ ℂ) v.2 := by
  set A := (scnPsi p e H₀ v)⁻¹ with hA
  have hU : IsUnit (scnPsi p e H₀ v) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv)
  have hG : HasFDerivAt (fun ζ : ℂ => scnPsi p e H₀ (v.1, ζ))
      (-((ContinuousLinearMap.id ℝ ℂ).smulRight (pairProjector p e))) v.2 := by
    have h1 := ((hasFDerivAt_id (𝕜 := ℝ) v.2).smul_const (pairProjector p e)).const_sub
      (scnLine H₀ v.1 - ((v.1.2 : ℝ) : ℂ) • (1 : p.SiteMatrix))
    convert h1 using 1
    funext ζ; rfl
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit
  rw [IsUnit.unit_spec] at hinv
  have hv' : scnPsi p e H₀ (v.1, v.2) = scnPsi p e H₀ v := rfl
  have hinv' : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ p.SiteMatrix A A) (scnPsi p e H₀ (v.1, v.2)) := by
    rw [hv']
    have hinvN : (↑hU.unit⁻¹ : p.SiteMatrix) = A := by
      rw [← Ring.inverse_unit, IsUnit.unit_spec, hA, Matrix.nonsing_inv_eq_ringInverse]
    rw [hinvN] at hinv
    exact hinv
  have hcomp := hinv'.comp v.2 hG
  have hcomp' : HasFDerivAt (fun ζ : ℂ => (scnPsi p e H₀ (v.1, ζ))⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ p.SiteMatrix A A).comp
        (-((ContinuousLinearMap.id ℝ ℂ).smulRight (pairProjector p e)))) v.2 := by
    refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [Function.comp_apply]
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have htr := (scnTrS p e).hasFDerivAt.comp v.2 hcomp'
  have hF := (hasFDerivAt_id (𝕜 := ℝ) v.2).sub (htr.const_mul (ctrK p : ℂ))
  convert hF using 1
  · funext ζ; rfl
  · ext1 dζ
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, _root_.sub_apply,
      ContinuousLinearMap.comp_apply, _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      ContinuousLinearMap.smulRight_apply, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
      Matrix.mul_smul, Matrix.smul_mul]
    have hl : scnTrS p e (dζ • (A * pairProjector p e * A)) =
        dζ * scnTrS p e (A * pairProjector p e * A) := by
      rw [scn_trS_apply, scn_trS_apply]
      unfold Matrix.trace scnBlk
      rw [Finset.mul_sum]
      rfl
    rw [hl]
    ring

theorem scn_trS_projector_eq (A : p.SiteMatrix) :
    scnTrS p e (A * pairProjector p e * A) = (scnBlk A e e * scnBlk A e e).trace := by
  rw [scn_trS_apply]
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Matrix.mul_apply]
  change (A * pairProjector p e * A) z.1 z.1 = _
  rw [ctr_mul_projector_mul_apply]
  rfl

/-- **The root is smooth on the shift lines** (implicit-function theorem): along
the shift line through Hermitian, ring-banded `H₀` with invertible exterior bonds, at every
`x₀ = (ξ₀, E₀)` where a Dyson root exists, `x ↦ scnRoot(H₀ + Σ x_g P_g, E)` is `C^∞` at `x₀`, and
roots exist on a neighbourhood of `x₀`. -/
theorem scn_root_contDiffAt {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {x₀ : (ZMod p.n → ℝ) × ℝ} {ζ₀ : ℂ}
    (hroot : IsDysonRoot p e (scnLine H₀ x₀) x₀.2 ζ₀) :
    ContDiffAt ℝ ∞ (fun x => scnRoot p e (scnLine H₀ x) x.2) x₀ ∧
      ∀ᶠ x in 𝓝 x₀, IsDysonRoot p e (scnLine H₀ x) x.2 (scnRoot p e (scnLine H₀ x) x.2) := by
  set u : ((ZMod p.n → ℝ) × ℝ) × ℂ := (x₀, ζ₀) with hu
  have hdet : (scnPsi p e H₀ u).det ≠ 0 := scn_psi_det_ne hH hb hbd u hroot.1.ne'
  have cdf := scn_contDiffAt_F (p := p) (e := e) hdet
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set A := (scnPsi p e H₀ u)⁻¹
  set J : ℂ := 1 - (ctrK p : ℂ) * scnTrS p e (A * pairProjector p e * A) with hJdef
  have hJ : J ≠ 0 := by
    have hst := scn_stability (scn_line_isHermitian hH x₀) hroot
    have hJR : J = 1 - (ctrK p : ℂ) * (compressedResolvent p e (scnLine H₀ x₀) x₀.2 ζ₀ *
        compressedResolvent p e (scnLine H₀ x₀) x₀.2 ζ₀).trace := by
      rw [hJdef, scn_trS_projector_eq]; rfl
    intro h0
    rw [← hJR, h0, Complex.zero_re] at hst
    have : 0 < 2 * ζ₀.im ^ 2 / splitS p := by
      have := hroot.1; have := ctr_splitS_pos (p := p); positivity
    linarith
  have hderiv : (fderiv ℝ (scnF p e H₀) u).comp
      (ContinuousLinearMap.inr ℝ ((ZMod p.n → ℝ) × ℝ) ℂ) = J • ContinuousLinearMap.id ℝ ℂ := by
    have hfd : HasFDerivAt (scnF p e H₀) (fderiv ℝ (scnF p e H₀) u) u :=
      (cdf.differentiableAt (by simp)).hasFDerivAt
    have h1 := hfd.comp u.2 (hasFDerivAt_prodMk_right u.1 u.2)
    exact h1.unique (scn_hasFDerivAt_F_zeta H₀ u hdet)
  have if₂ : ((fderiv ℝ (scnF p e H₀) u).comp
      (ContinuousLinearMap.inr ℝ ((ZMod p.n → ℝ) × ℝ) ℂ)).IsInvertible := by
    rw [hderiv]
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := J⁻¹ • ContinuousLinearMap.id ℝ ℂ)
      ?_ ?_
    · ext1 z
      simp [smul_smul, mul_inv_cancel₀ hJ]
    · ext1 z
      simp [smul_smul, inv_mul_cancel₀ hJ]
  set ψ := cdf.implicitFunction pn if₂
  have hψ0 : ψ x₀ = ζ₀ := cdf.implicitFunction_apply_self pn if₂
  have hψ : ContDiffAt ℝ ∞ ψ x₀ := cdf.contDiffAt_implicitFunction pn if₂
  have hev := cdf.eventually_apply_implicitFunction pn if₂
  have hF0 : scnF p e H₀ u = 0 := ((scn_isDysonRoot_iff H₀ u).mp hroot).2
  have him : ∀ᶠ x in 𝓝 x₀, 0 < (ψ x).im := by
    have hc : ContinuousAt (fun x => (ψ x).im) x₀ :=
      Complex.continuous_im.continuousAt.comp hψ.continuousAt
    have h0 : 0 < (ψ x₀).im := by rw [hψ0]; exact hroot.1
    exact hc.eventually (lt_mem_nhds h0)
  have hroots : ∀ᶠ x in 𝓝 x₀, IsDysonRoot p e (scnLine H₀ x) x.2 (ψ x) := by
    filter_upwards [hev, him] with x hx hxi
    exact (scn_isDysonRoot_iff H₀ (x, ψ x)).mpr ⟨hxi, by rw [hx, hF0]⟩
  have heq : (fun x => scnRoot p e (scnLine H₀ x) x.2) =ᶠ[𝓝 x₀] ψ := by
    filter_upwards [hroots] with x hx
    exact scn_root_eq (scn_line_isHermitian hH x) hx
  refine ⟨hψ.congr_of_eventuallyEq heq, ?_⟩
  filter_upwards [hroots, heq] with x hx hxe
  rw [hxe]; exact hx

end Root

/-!
## 3. Smoothness of the residuals along the shift lines
-/

section Residual

variable {p : Parameters} {e : ZMod p.n}

open BlockBand.Layers

theorem scn_tgtMu_eq (E : ℝ) :
    tgtMu E = ((-E / 2 : ℝ) : ℂ) + ((Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [tgtMu, matchedA]; ring

theorem scn_continuous_tgtMu : Continuous tgtMu := by
  have h : tgtMu = fun E : ℝ =>
      ((-E / 2 : ℝ) : ℂ) + ((Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I := funext scn_tgtMu_eq
  rw [h]; fun_prop

theorem scn_contDiffAt_tgtMu {E : ℝ} (hE : |E| < 2) : ContDiffAt ℝ ∞ tgtMu E := by
  have h : tgtMu = fun E : ℝ =>
      ((-E / 2 : ℝ) : ℂ) + ((Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I := funext scn_tgtMu_eq
  rw [h]
  have h4 : 4 - E ^ 2 ≠ 0 := by nlinarith [abs_lt.mp hE, sq_abs E]
  have hs : ContDiffAt ℝ ∞ (fun E : ℝ => Real.sqrt (4 - E ^ 2) / 2) E :=
    ((contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt h4).div_const 2
  have hl : ContDiffAt ℝ ∞ (fun E : ℝ => -E / 2) E := (contDiffAt_id.neg).div_const 2
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp E hl).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp E hs).mul contDiffAt_const)

theorem scn_tgtZeta_im_pos {E : ℝ} (hE : |E| < 2) : 0 < ((splitS p : ℂ) * tgtMu E).im :=
  tgt_zeta_im_pos (p := p) hE

/-- The residual `ε_{e,k}` along the shift line, in full-inverse form. -/
theorem scn_eps_line_eq (H₀ : p.SiteMatrix) (x : (ZMod p.n → ℝ) × ℝ) (k : ZMod p.n) :
    tgtEps p e (scnLine H₀ x) x.2 k =
      tgtTraceCLM e k (scnPsi p e H₀ (x, (splitS p : ℂ) * tgtMu x.2))⁻¹ - tgtMu x.2 := rfl

theorem scn_contDiffAt_eps {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {x : (ZMod p.n → ℝ) × ℝ} (hE : |x.2| < 2)
    (k : ZMod p.n) :
    ContDiffAt ℝ ∞ (fun y => tgtEps p e (scnLine H₀ y) y.2 k) x := by
  have hz : ContDiffAt ℝ ∞ (fun y : (ZMod p.n → ℝ) × ℝ => (y, (splitS p : ℂ) * tgtMu y.2)) x :=
    contDiffAt_id.prodMk (contDiffAt_const.mul ((scn_contDiffAt_tgtMu hE).comp x contDiffAt_snd))
  have hdet : (scnPsi p e H₀ (x, (splitS p : ℂ) * tgtMu x.2)).det ≠ 0 :=
    scn_psi_det_ne hH hb hbd _ (scn_tgtZeta_im_pos (p := p) hE).ne'
  have hinv := (scn_contDiffAt_psi_inv (e := e) H₀ hdet).comp x hz
  exact ((tgtTraceCLM e k).contDiff.contDiffAt.comp x hinv).sub
    ((scn_contDiffAt_tgtMu hE).comp x contDiffAt_snd)

/-- The squared residual `ε_e² = |ε_{e,e}|² + |ε_{e,e+1}|²` (smooth, unlike `ε_e`). -/
def scnEps2 (p : Parameters) (e : ZMod p.n) (H : p.SiteMatrix) (E : ℝ) : ℝ :=
  ‖tgtEps p e H E e‖ ^ 2 + ‖tgtEps p e H E (e + 1)‖ ^ 2

theorem scn_centerResidual_eq (H : p.SiteMatrix) (E : ℝ) :
    centerResidual p e H E = Real.sqrt (scnEps2 p e H E) := rfl

theorem scn_contDiffAt_eps2 {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {x : (ZMod p.n → ℝ) × ℝ} (hE : |x.2| < 2) :
    ContDiffAt ℝ ∞ (fun y => scnEps2 p e (scnLine H₀ y) y.2) x :=
  (scn_contDiffAt_eps hH hb hbd hE e).norm_sq ℂ |>.add
    ((scn_contDiffAt_eps hH hb hbd hE (e + 1)).norm_sq ℂ)

end Residual

/-!
## 4. Exterior poles are isolated; roots pass to limits
-/

section Limit

variable {p : Parameters} {e : ZMod p.n}

theorem scn_eventually_det_ne {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (E₀ : ℝ) : ∀ᶠ E : ℝ in 𝓝[≠] E₀, (B - (E : ℂ) • 1).det ≠ 0 := by
  have hfin : Set.Finite {E : ℝ | (B - (E : ℂ) • 1).det = 0} := by
    have hp : B.charpoly ≠ 0 := B.charpoly_monic.ne_zero
    have hr := Polynomial.finite_setOfPred_isRoot hp
    refine (hr.preimage (f := fun E : ℝ => (E : ℂ))
      (Complex.ofReal_injective.injOn)).subset fun E hE => ?_
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly]
    have h1 : Matrix.scalar ι (E : ℂ) - B = -(B - (E : ℂ) • 1) := by
      rw [Matrix.scalar_apply, neg_sub, Matrix.smul_one_eq_diagonal]
    rw [h1, Matrix.det_neg, hE, mul_zero]
  have hop : IsOpen ({E : ℝ | (B - (E : ℂ) • 1).det = 0} \ {E₀})ᶜ :=
    (hfin.sdiff).isClosed.isOpen_compl
  have hmem : E₀ ∈ ({E : ℝ | (B - (E : ℂ) • 1).det = 0} \ {E₀})ᶜ := by simp
  have h1 : ∀ᶠ E : ℝ in 𝓝[≠] E₀, E ∈ ({E : ℝ | (B - (E : ℂ) • 1).det = 0} \ {E₀})ᶜ :=
    nhdsWithin_le_nhds (hop.mem_nhds hmem)
  filter_upwards [h1, self_mem_nhdsWithin] with E hE hne
  intro h0
  exact hE ⟨h0, hne⟩

theorem scn_continuousAt_F {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {v : ((ZMod p.n → ℝ) × ℝ) × ℂ} (hv : v.2.im ≠ 0) :
    ContinuousAt (scnF p e H₀) v :=
  (scn_contDiffAt_F (scn_psi_det_ne hH hb hbd v hv)).continuousAt

/-- **Roots pass to limits along `E`** (uniform height `y₀ > 0`; `|ζ| ≤ 1` at every root). -/
theorem scn_root_of_frequently {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) (ξ : ZMod p.n → ℝ) {E₀ y₀ : ℝ} (hy : 0 < y₀)
    (hfreq : ∃ᶠ E in 𝓝[≠] E₀, ∃ ζ, IsDysonRoot p e (scnLine H₀ (ξ, E)) E ζ ∧ y₀ ≤ ζ.im) :
    ∃ ζ, IsDysonRoot p e (scnLine H₀ (ξ, E₀)) E₀ ζ ∧ y₀ ≤ ζ.im := by
  obtain ⟨Es, hEs, hEp⟩ := Filter.exists_seq_forall_of_frequently hfreq
  choose ζs hζs hζy using hEp
  set K : Set ℂ := Metric.closedBall 0 1 ∩ {ζ | y₀ ≤ ζ.im}
  have hK : IsCompact K := (isCompact_closedBall 0 1).inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  have hmem : ∀ n, ζs n ∈ K := fun n => ⟨by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact scn_root_norm_le (scn_line_isHermitian hH _) (hζs n), hζy n⟩
  obtain ⟨ζ, hζK, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hEφ : Tendsto (Es ∘ φ) atTop (𝓝 E₀) :=
    (tendsto_nhdsWithin_iff.mp hEs).1.comp hφ.tendsto_atTop
  have hy₀ : y₀ ≤ ζ.im := hζK.2
  have hv : ((ξ, E₀), ζ).2.im ≠ 0 := (lt_of_lt_of_le hy hy₀).ne'
  have hc := scn_continuousAt_F hH hb hbd hv
  have hseq : Tendsto (fun n => (((ξ, (Es ∘ φ) n), (ζs ∘ φ) n) : ((ZMod p.n → ℝ) × ℝ) × ℂ))
      atTop (𝓝 ((ξ, E₀), ζ)) :=
    (tendsto_const_nhds.prodMk_nhds hEφ).prodMk_nhds hlim
  have hF := hc.tendsto.comp hseq
  have hzero : ∀ n, scnF p e H₀ (((ξ, (Es ∘ φ) n), (ζs ∘ φ) n)) = 0 := fun n =>
    ((scn_isDysonRoot_iff (e := e) H₀ ((ξ, Es (φ n)), ζs (φ n))).mp (hζs (φ n))).2
  have hF0 : scnF p e H₀ ((ξ, E₀), ζ) = 0 := by
    have : Tendsto (fun n => scnF p e H₀ (((ξ, (Es ∘ φ) n), (ζs ∘ φ) n))) atTop (𝓝 0) := by
      simp only [hzero]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (f := fun n => scnF p e H₀ (((ξ, (Es ∘ φ) n), (ζs ∘ φ) n))) hF this
  exact ⟨ζ, (scn_isDysonRoot_iff H₀ ((ξ, E₀), ζ)).mpr ⟨lt_of_lt_of_le hy hy₀, hF0⟩, hy₀⟩

end Limit

/-!
## 5. Roots from the regularity certificate (off the exterior poles)
-/

section Cert

open BlockBand.Palm BlockBand.Layers

variable {p : Parameters} {e : ZMod p.n}

/-- A Dyson root in matrix form: `m = ζ/s` solves `m = N⁻¹ Tr (F - E - s m)⁻¹`,
`F = K_e(E) + E`, hence `m = freshDyson F s E` (off the exterior poles). -/
theorem scn_root_freshDyson {H : p.SiteMatrix} (hH : H.IsHermitian) {E : ℝ}
    (hdet : (exteriorBlock p e H - (E : ℂ) • 1).det ≠ 0) {ζ : ℂ} (hroot : IsDysonRoot p e H E ζ) :
    freshDyson (pairToFin (edgeSchur p e H E + (E : ℂ) • 1)) (splitS p) E = ζ / (splitS p : ℂ) ∧
      ζ / (splitS p : ℂ) = ((Fintype.card (PairSite p e) : ℕ) : ℂ)⁻¹ *
        (pairToFin (edgeSchur p e H E + (E : ℂ) • 1) -
          ((E : ℂ) + (splitS p : ℂ) * (ζ / (splitS p : ℂ))) • 1)⁻¹.trace := by
  set K := edgeSchur p e H E
  set F := pairToFin (K + (E : ℂ) • 1)
  have hs : 0 < splitS p := ctr_splitS_pos
  have hF : F.IsHermitian := ctr_pairToFin_isHermitian (ctr_edgeSchur_add_isHermitian hH E)
  have hN : 0 < Fintype.card (PairSite p e) := ctr_card_pairSite_pos
  have hR : compressedResolvent p e H E ζ = (K - ζ • 1)⁻¹ := ctr_compressed_eq_schur hH hdet ζ
  set m : ℂ := ζ / (splitS p : ℂ)
  have hsC : (splitS p : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hζm : ζ = (splitS p : ℂ) * m := by simp only [m]; field_simp
  have hm : 0 < m.im := by
    have : m.im = ζ.im / splitS p := by simp only [m]; rw [Complex.div_ofReal_im]
    rw [this]; exact div_pos hroot.1 hs
  have heq : m = ((Fintype.card (PairSite p e) : ℕ) : ℂ)⁻¹ *
      (F - ((E : ℂ) + (splitS p : ℂ) * m) • 1)⁻¹.trace := by
    rw [ctr_pairToFin_shift_trace, ← hζm, ctr_card_pairSite_coe]
    have hK : K + (E : ℂ) • 1 - ((E : ℂ) + ζ) • 1 = K - ζ • 1 := by rw [add_smul]; abel
    rw [hK, ← hR]
    have h2 := hroot.2
    simp only [m]
    rw [div_eq_iff hsC]
    nth_rewrite 1 [h2]
    ring
  have hz0 : (0 : ℝ) ≤ ((E : ℂ)).im := by simp
  exact ⟨ctr_freshDyson_eq F hF hN hs hz0 hm heq, heq⟩

/-- **Roots from the certificate** (as in `cst0_inCenterDomain_iff`, at the full certificate
threshold): for Hermitian `H^{(e)}` off the exterior poles, `|E| ≤ 2 - θ_k` and
`ε_e ≤ ε_cert(s, θ_k)`, there is a Dyson root with `Im ζ ≥ s v₀(k)`. -/
theorem scn_cert_root {H : p.SiteMatrix} (hH : H.IsHermitian) {E : ℝ}
    (hdet : (exteriorBlock p e H - (E : ℂ) • 1).det ≠ 0) {k : ℕ} (hE : |E| ≤ 2 - ctrTheta k)
    (hε : centerResidual p e H E ≤ (ctrCert (splitS p) (ctrTheta k)).1) :
    ∃ ζ, IsDysonRoot p e H E ζ ∧ splitS p * (ctrCert (splitS p) (ctrTheta k)).2.2.2 ≤ ζ.im := by
  set c := splitS p
  have hc : 0 < c := ctr_splitS_pos
  have hc1 : c < 1 := by
    have : c ≤ p.b := min_le_right _ _
    linarith [p.b_lt_half]
  set K := edgeSchur p e H E
  set F := pairToFin (K + (E : ℂ) • 1)
  have hF : F.IsHermitian := ctr_pairToFin_isHermitian (ctr_edgeSchur_add_isHermitian hH E)
  have hN : 0 < Fintype.card (PairSite p e) := ctr_card_pairSite_pos
  have hspec := ctrCert_spec hc hc1 (ctrTheta_pos k) (ctrTheta_le_two k)
  have hχ : ‖certificateChi F c E (certificateSemicircleReference E)‖ ≤
      (ctrCert c (ctrTheta k)).1 := (ctr_chi_le hH hdet).trans hε
  have hreg := hspec.2.2 _ F hN hF E hE hχ
  have hv := hspec.2.1.2.2.2.2.2
  have hr₀ := hspec.2.1.2.2.1
  have h1 := (hreg c ⟨by linarith [hspec.2.1.2.2.2.1], le_refl _⟩ E (by simp [hr₀.le]) 0
    ⟨le_refl _, zero_le_one⟩).1
  have h0 : (⟨E, 0⟩ : ℂ) = (E : ℂ) := rfl
  rw [h0] at h1
  set m := freshDyson F c E
  have hm : 0 < m.im := hv.trans_le h1
  have heq : m = ((Fintype.card (PairSite p e) : ℕ) : ℂ)⁻¹ *
      (F - ((E : ℂ) + (c : ℂ) * m) • 1)⁻¹.trace := ctr_freshDyson_spec F c E hm
  refine ⟨(c : ℂ) * m, ⟨?_, ?_⟩, ?_⟩
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos hc hm
  · rw [ctr_compressed_eq_schur hH hdet]
    have htr : (F - ((E : ℂ) + (c : ℂ) * m) • 1)⁻¹.trace =
        (K + (E : ℂ) • 1 - ((E : ℂ) + (c : ℂ) * m) • 1)⁻¹.trace :=
      ctr_pairToFin_shift_trace (K + (E : ℂ) • 1) ((E : ℂ) + (c : ℂ) * m)
    have hK : K + (E : ℂ) • 1 - ((E : ℂ) + (c : ℂ) * m) • 1 = K - ((c : ℂ) * m) • 1 := by
      rw [add_smul]; abel
    rw [hK] at htr
    rw [← htr, ← ctr_card_pairSite_coe (i := e)]
    change (c : ℂ) * m = (c : ℂ) * _ * _
    nth_rewrite 1 [heq]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_le_mul_of_nonneg_left h1 hc.le

/-- **Lipschitz dependence of the root on the residual** (`certificate_semicircle_full`,
its constant `C`; trivial bound `|ζ - sμ| ≤ 2` above its threshold): for `0 < c < 1`, `0 < θ ≤ 2`
there is `L ≥ 0` with `|ζ - s μ| ≤ L ε_e` for every Dyson root, Hermitian `H^{(e)}` off the exterior
poles, `s = c` and `|E| ≤ 2 - θ`. -/
theorem scn_root_lipschitz {c θ : ℝ} (hc : 0 < c) (hc1 : c < 1) (hθ : 0 < θ) (hθ2 : θ ≤ 2) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (p : Parameters), splitS p = c → ∀ (e : ZMod p.n) (H : p.SiteMatrix),
      H.IsHermitian → ∀ E : ℝ, (exteriorBlock p e H - (E : ℂ) • 1).det ≠ 0 → |E| ≤ 2 - θ →
      ∀ ζ, IsDysonRoot p e H E ζ → ‖ζ - (c : ℂ) * tgtMu E‖ ≤ L * centerResidual p e H E := by
  obtain ⟨ε, r, s₀, v₀, C, hε, hr, hs₀, hs₀c, hv₀, hC, hall⟩ :=
    certificate_semicircle_full.{0} hc hc1 hθ hθ2
  refine ⟨max (c * C) (2 / ε), le_trans (by positivity) (le_max_right _ _), ?_⟩
  intro p hpc e H hH E hdet hE ζ hroot
  have hcR : 0 ≤ centerResidual p e H E := Real.sqrt_nonneg _
  have hE2 : |E| ≤ 2 := hE.trans (by linarith)
  have hμ : ‖tgtMu E‖ = 1 := by
    unfold tgtMu; rw [Complex.norm_conj]; exact ctr_norm_matchedA hE2
  by_cases hbig : ε ≤ centerResidual p e H E
  · have h2 : ‖ζ - (c : ℂ) * tgtMu E‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, hμ, mul_one]
      linarith [scn_root_norm_le hH hroot]
    calc ‖ζ - (c : ℂ) * tgtMu E‖ ≤ 2 := h2
      _ ≤ 2 / ε * centerResidual p e H E := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hε]; linarith
      _ ≤ max (c * C) (2 / ε) * centerResidual p e H E :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hcR
  · push Not at hbig
    set K := edgeSchur p e H E
    set F := pairToFin (K + (E : ℂ) • 1)
    have hF : F.IsHermitian := ctr_pairToFin_isHermitian (ctr_edgeSchur_add_isHermitian hH E)
    have hN : 0 < Fintype.card (PairSite p e) := ctr_card_pairSite_pos
    have : Nonempty (Fin (Fintype.card (PairSite p e))) := ⟨⟨0, hN⟩⟩
    have hχ0 := ctr_chi_le hH hdet
    rw [hpc] at hχ0
    have hχ : ‖certificateChi F c E (certificateSemicircleReference E)‖ ≤ ε :=
      hχ0.trans hbig.le
    obtain ⟨hrect, hlip, -, -⟩ := hall (Fin (Fintype.card (PairSite p e))) F hF E hE hχ
    obtain ⟨heqc, hlo, -⟩ := hrect c (by linarith) le_rfl E (by simp [hr.le]) 0 le_rfl zero_le_one
    have hz : ((E : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) = (E : ℂ) := by simp
    rw [hz] at heqc hlo
    set m₀ := certificateCanonicalDyson hF.eigenvalues c (E : ℂ)
    have hfd0 : freshDyson F c E = m₀ := by
      refine ctr_freshDyson_eq F hF hN hc (by simp) (hv₀.trans_le hlo) ?_
      rw [← ctr_matrixTrace_eq]; exact heqc
    obtain ⟨hfd, -⟩ := scn_root_freshDyson hH hdet hroot
    rw [hpc] at hfd
    have hm : ζ / (c : ℂ) = m₀ := hfd.symm.trans hfd0
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hζ : ζ = (c : ℂ) * m₀ := by rw [← hm]; field_simp
    have href : tgtMu E = certificateSemicircleReference E := by
      unfold tgtMu; exact ctr_conj_matchedA E
    rw [hζ, href, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    calc c * ‖m₀ - certificateSemicircleReference E‖
        ≤ c * (C * ‖certificateChi F c E (certificateSemicircleReference E)‖) :=
          mul_le_mul_of_nonneg_left hlip hc.le
      _ ≤ c * (C * centerResidual p e H E) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hχ0 hC.le) hc.le
      _ = c * C * centerResidual p e H E := by ring
      _ ≤ max (c * C) (2 / ε) * centerResidual p e H E :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hcR

end Cert

end BlockBand.Center
