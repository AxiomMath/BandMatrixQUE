module

public import BlockBand.Angular.RatioFields

/-!
# Derivatives along the field `ΓDv` for the angular ratio lemma

Exact derivatives at unit vectors of `cfun = Q_D^{-1/2}`, `qe = (Q_{B'} + ε²)^{1/2}`, the
regression exponent and the product `ffun = χ(b₂) qe e^{q} 𝔷`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Ratio

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.DegreeZero
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference BlockBand.Angular.Stein
open BlockBand.Angular.Stein.AngularData (reInner quadNum reInner_comm normSqSum_eq_reInner
  reInner_mulVec_herm quadNum_real_smul quadQuot_of_unit)
open scoped ComplexConjugate

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (D : AngularData ι) (L : Matrix κ ι ℂ)

theorem dAt {G : (ι → ℂ) → ℝ} (hG : ContDiffOn ℝ 1 G {z | z ≠ 0}) {v : ι → ℂ} (hv : v ≠ 0) :
    DifferentiableAt ℝ G v :=
  (hG.differentiableOn one_ne_zero).differentiableAt (isOpen_ne.mem_nhds hv)

theorem fderiv_cfun (hL : ∀ x, L *ᵥ x = 0 → x = 0) {v : ι → ℂ} (hv : v ≠ 0) (w : ι → ℂ) :
    fderiv ℝ (cfun L) v w = -((Real.sqrt (quadQuot (Dm L) v)) ^ 2)⁻¹ *
      ((1 / (2 * Real.sqrt (quadQuot (Dm L) v))) * fderiv ℝ (quadQuot (Dm L)) v w) := by
  have hQ := (dAt (contDiffOn_quadQuot (Dm L)) hv).hasFDerivAt
  have hpos := quadQuot_Dm_pos L hL hv
  have h1 : HasFDerivAt (fun y => Real.sqrt (quadQuot (Dm L) y))
      ((1 / (2 * Real.sqrt (quadQuot (Dm L) v))) • fderiv ℝ (quadQuot (Dm L)) v) v :=
    hQ.sqrt hpos.ne'
  have h := (hasDerivAt_inv (Real.sqrt_pos.2 hpos).ne').comp_hasFDerivAt v h1
  rw [show cfun L = (fun y : ℝ => y⁻¹) ∘ fun y => Real.sqrt (quadQuot (Dm L) y) from rfl,
    h.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, neg_mul]

theorem fderiv_qe (A : Matrix ι ι ℂ) {ε2 : ℝ} (hε : 0 < ε2) {v : ι → ℂ} (hv : v ≠ 0)
    (w : ι → ℂ) :
    fderiv ℝ (qe D L A ε2) v w =
      (1 / (2 * qe D L A ε2 v)) * fderiv ℝ (quadQuot (Bq D L A)) v w := by
  have hQ := ((dAt (contDiffOn_quadQuot (Bq D L A)) hv).hasFDerivAt).add_const ε2
  have h := hQ.sqrt (Real.sqrt_pos.1 (qe_pos D L A hε v)).ne'
  rw [show qe D L A ε2 = fun y => Real.sqrt (quadQuot (Bq D L A) y + ε2) from rfl, h.fderiv]
  rfl

theorem fderiv_expo {v : ι → ℂ} (hv : v ≠ 0) (w : ι → ℂ) :
    fderiv ℝ D.expo v w = (-(fderiv ℝ D.b₂ v w) + D.a v * fderiv ℝ D.a v w) / D.t := by
  have hb := (dAt (b₂_c1 D) hv).hasFDerivAt
  have ha := (dAt (a_c1 D) hv).hasFDerivAt
  have h1 : HasFDerivAt (fun y => -(D.b₂ y)) (-fderiv ℝ D.b₂ v) v := hb.neg
  have h2 : HasFDerivAt (fun y => D.a y ^ 2) ((2 * D.a v ^ (2 - 1) : ℝ) • fderiv ℝ D.a v) v := by
    simpa using ha.pow 2
  have h := (h1.mul_const D.t⁻¹).fun_add (h2.mul_const (2 * D.t)⁻¹)
  rw [show D.expo = fun y => -(D.b₂ y) * D.t⁻¹ + D.a y ^ 2 * (2 * D.t)⁻¹ from
    funext fun y => by simp only [AngularData.expo, div_eq_mul_inv], h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    _root_.neg_apply, div_eq_mul_inv]
  push_cast
  ring

theorem fderiv_ffun {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) {Zf : (ι → ℂ) → ℝ}
    (hZc : ContDiffOn ℝ 1 Zf {z | z ≠ 0}) (A : Matrix ι ι ℂ) {ε2 : ℝ} (hε : 0 < ε2)
    {v : ι → ℂ} (hv : v ≠ 0) (w : ι → ℂ) :
    fderiv ℝ (ffun D L χ Zf A ε2) v w =
      deriv χ (D.b₂ v) * fderiv ℝ D.b₂ v w * qe D L A ε2 v * (Real.exp (D.expo v) * Zf v) +
        χ (D.b₂ v) * fderiv ℝ (qe D L A ε2) v w * (Real.exp (D.expo v) * Zf v) +
        χ (D.b₂ v) * qe D L A ε2 v * (Real.exp (D.expo v) * fderiv ℝ D.expo v w * Zf v +
          Real.exp (D.expo v) * fderiv ℝ Zf v w) := by
  have hb := (dAt (b₂_c1 D) hv).hasFDerivAt
  have hχb := (hχ.differentiable one_ne_zero (D.b₂ v)).hasDerivAt.comp_hasFDerivAt v hb
  have hq := (dAt (qe_c1 D L A hε) hv).hasFDerivAt
  have hE := (dAt D.expo_c1 hv).hasFDerivAt.exp
  have hZ := (dAt hZc hv).hasFDerivAt
  have h := (hχb.mul hq).mul (hE.mul hZ)
  rw [show ffun D L χ Zf A ε2 = (χ ∘ D.b₂) * qe D L A ε2 *
    ((fun y => Real.exp (D.expo y)) * Zf) from rfl, h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp, Pi.mul_apply]
  ring

end BlockBand.Angular.Ratio
