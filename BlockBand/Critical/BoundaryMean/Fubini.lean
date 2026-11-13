module

public import BlockBand.Critical.BoundaryMean.Domination

/-!
# Fubini for the scalar Cauchy dilation of the collar form

A step of the proof of the exact boundary-mean theorem: a passive response is written as an
average of Hermitian ones over a Cauchy dilation.

`integral_regForm_eq`: for `Y = -Im X ⪰ 0` and a height `ν > 0`,
`E_collar f_ν = E_t h_ν(X_t, q)`, `X_t = X_h + tY`, `t ~ stdCauchy`, with
`f_ν = -Im⟨ρ*q, (ℋ_X + iν)⁻¹ρ*q⟩` (`regForm`) and the Hermitian form
`h_ν(X', q) = E_collar Im⟨ρ*q, (ℋ_{X'} - iν)⁻¹ρ*q⟩` (`hermitianCollarForm`). The integrand is
nonnegative and jointly integrable on `stdCauchy × collarLaw`: each section is bounded by the
fresh-row bound `C_{b,w}√W‖q‖²` (`Collar.Density.lintegral_im_resolvent_collarRow_le_sqrt`).
The pointwise identity is `Collar.Kernel.neg_im_collarResolvent_eq_integral`.

Law: `collarLaw W b`, `0 < b < 1/2`, `W ≥ 1`, deterministic `X`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Collar.Density (collarMatrix collarRowVec collarRowConst)
open BlockBand.Critical.Collar.Kernel (topLift rePart)
open BlockBand.Critical.Collar (stdCauchy)
open scoped ComplexOrder ENNReal

variable {W : ℕ}

/-- The dilated Hermitian old response `X_t = X_h + tY` (`X = X_h - iY`). -/
abbrev dilatedOld (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (t : ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  rePart X + (t : ℂ) • (-imPart X)

/-- The integrand `G(t, ω) = Im⟨ρ*q, (ℋ_{X_t} - iν)⁻¹ ρ*q⟩` of the dilation. -/
def dilForm (b e ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (q : Fin 2 × Fin W → ℂ)
    (p : ℝ × CollarSample W) : ℝ :=
  (star (collarRowVec (Collar.Kernel.rowCoeff b e 0) q p.2) ⬝ᵥ
    ((collarMatrix e (dilatedOld X p.1) p.2 - ((ν : ℂ) * Complex.I) • 1)⁻¹ *ᵥ
      collarRowVec (Collar.Kernel.rowCoeff b e 0) q p.2)).im

theorem measurable_dilForm (b e ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (q : Fin 2 × Fin W → ℂ) : Measurable (dilForm b e ν X q) := by
  have hM : Measurable fun p : ℝ × CollarSample W =>
      collarMatrix e (dilatedOld X p.1) p.2 - ((ν : ℂ) * Complex.I) • 1 := by
    have heq : (fun p : ℝ × CollarSample W =>
        collarMatrix e (dilatedOld X p.1) p.2 - ((ν : ℂ) * Complex.I) • 1) =
        fun p => collarMatrix e (rePart X) p.2 - (p.1 : ℂ) • topLift (-imPart X) -
          ((ν : ℂ) * Complex.I) • 1 := by
      funext p; rw [Collar.Kernel.collarMatrix_add_right, Collar.Kernel.topLift_smul]
    rw [heq]
    refine Measurable.of_eval_matrix _ fun i j => ?_
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    refine (((Matrix.measurable_apply).comp ((Collar.Density.measurable_collarMatrix e
      (rePart X)).comp measurable_snd)).sub ?_).sub measurable_const
    exact (Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const
  have hv : Measurable fun p : ℝ × CollarSample W =>
      collarRowVec (Collar.Kernel.rowCoeff b e 0) q p.2 :=
    (Collar.Density.measurable_collarRowVec (W := W) (Collar.Kernel.rowCoeff b e 0) q).comp
      measurable_snd
  have hinv := (BlockBand.Wegner.measurable_matrix_inv (n := LayerSite W .common)).comp hM
  have hcont : Continuous fun p : Matrix (LayerSite W .common) (LayerSite W .common) ℂ ×
      (LayerSite W .common → ℂ) => (star p.2 ⬝ᵥ (p.1 *ᵥ p.2)).im :=
    Complex.continuous_im.comp ((continuous_star.comp continuous_snd).dotProduct
      (continuous_fst.matrix_mulVec continuous_snd))
  exact (hcont.measurable.comp (hinv.prodMk hv) :)

/-- **Fubini for the dilation** (`Y = -Im X ⪰ 0`, `ν > 0`): the integrand is integrable on
`stdCauchy × collarLaw`, each `t`-section has `0 ≤ h_ν(X_t, q) ≤ C_{b,w}√W‖q‖²`, and
`E_collar f_ν = E_t h_ν(X_t, q)`. -/
theorem integral_regForm_eq {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 0 < W) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosSemidef) {ν : ℝ}
    (hν : 0 < ν) (q : Fin 2 × Fin W → ℂ) :
    Integrable (fun t => hermitianCollarForm W b e ν (dilatedOld X t) q) stdCauchy ∧
    (∀ t, 0 ≤ hermitianCollarForm W b e ν (dilatedOld X t) q ∧
      hermitianCollarForm W b e ν (dilatedOld X t) q ≤
        collarRowConst b (Collar.Kernel.rowCoeff b e 0) * Real.sqrt W * ∑ x, ‖q x‖ ^ 2) ∧
    ∫ ω, regForm b e ν X q ω ∂collarLaw W b =
      ∫ t, hermitianCollarForm W b e ν (dilatedOld X t) q ∂stdCauchy := by
  set w := Collar.Kernel.rowCoeff b e 0
  set B := collarRowConst b w * Real.sqrt W * ∑ x, ‖q x‖ ^ 2
  set G := dilForm b e ν X q
  have hGm := measurable_dilForm b e ν X q
  have hz : 0 < ((ν : ℂ) * Complex.I).im := by simp [hν]
  have hHerm := Collar.Density.ae_collarMatrix_isHermitian b e (Collar.Kernel.rePart_isHermitian X)
    (W := W)
  -- nonnegativity, a.e. in the collar, for all `t`
  have hnn_ω : ∀ᵐ ω ∂collarLaw W b, ∀ t, 0 ≤ G (t, ω) := by
    filter_upwards [hHerm] with ω hω t
    exact Collar.Density.im_dotProduct_inv_mulVec_nonneg'
      (Collar.Kernel.collarMatrix_isHermitian e hω.2.1 hω.2.2
        (Collar.Kernel.dilatedOld_isHermitian X t)) hz _
  have hnn : ∀ᵐ p ∂(stdCauchy.prod (collarLaw W b)), 0 ≤ G p := by
    have := (Measure.quasiMeasurePreserving_snd (μ := stdCauchy)
      (ν := collarLaw W b)).ae hnn_ω
    filter_upwards [this] with p hp using hp p.1
  -- each `t`-section
  have hsec : ∀ t, ∫⁻ ω, ENNReal.ofReal (G (t, ω)) ∂collarLaw W b ≤ ENNReal.ofReal B := fun t =>
    Collar.Density.lintegral_im_resolvent_collarRow_le_sqrt hb0 hb hW e
      (Collar.Kernel.dilatedOld_isHermitian X t) hz w q
  have hint : Integrable G (stdCauchy.prod (collarLaw W b)) := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn, lintegral_prod _
      (hGm.ennreal_ofReal.aemeasurable)]
    calc ∫⁻ t, ∫⁻ ω, ENNReal.ofReal (G (t, ω)) ∂collarLaw W b ∂stdCauchy
        ≤ ∫⁻ _ : ℝ, ENNReal.ofReal B ∂stdCauchy := lintegral_mono fun t => hsec t
      _ < ⊤ := by simp
  have hsecnn : ∀ t, 0 ≤ᵐ[collarLaw W b] fun ω => G (t, ω) := by
    intro t
    filter_upwards [hnn_ω] with ω hω using hω t
  have hform : ∀ t, hermitianCollarForm W b e ν (dilatedOld X t) q =
      ∫ ω, G (t, ω) ∂collarLaw W b := fun t => rfl
  refine ⟨?_, fun t => ⟨?_, ?_⟩, ?_⟩
  · simp_rw [hform]
    exact hint.integral_prod_left
  · rw [hform]; exact integral_nonneg_of_ae (hsecnn t)
  · rw [hform, integral_eq_lintegral_of_nonneg_ae (hsecnn t)
      (hGm.comp measurable_prodMk_left).aestronglyMeasurable]
    have hB : 0 ≤ B := by
      have := Collar.Density.collarRowConst_nonneg hb0.le w
      positivity
    exact ENNReal.toReal_le_of_le_ofReal hB (hsec t)
  · have hswap := integral_integral_swap (f := fun t ω => G (t, ω)) hint
    simp_rw [hform]
    rw [hswap]
    refine integral_congr_ae ?_
    filter_upwards [hHerm] with ω hω
    obtain ⟨-, heq⟩ := Collar.Kernel.neg_im_collarResolvent_eq_integral e hω.2.1 hω.2.2 hY hν
      (collarRowVec w q ω)
    exact heq.symm

end BlockBand.Critical.BoundaryMean
