module

public import BlockBand.SourceProcess.FullSourceCovariance.TauCov

/-!
# `FirstTermBound` holds

* **`tauCov_bulk hGA hLp`**: `‖E[τ⁰Ψ]‖, ‖E[τ⁰Ψ̄]‖ ≤ C(W⁻² + W⁻¹δ₀)‖x‖‖y‖` (`Ψ = x*Δ⁰y`), the
  instances `θ = τ⁰` and `θ = conj τ⁰` of `trace_test_bound` (`selfTau = τ_{S̃}`,
  `hasLayerDeriv_tauD`, `tauDer_single`, `starDeriv_tauDer_single`).
* **`firstTermBound_holds hGA hLp : FirstTermBound`**. With `Ω₀ = Ω̄ + τ⁰`, `F = EF + F⁰`,
  `first_split_bound` gives `‖E[Ω₀FΨ]‖ ≤ ‖Ω̄‖‖F⁰‖₄‖Ψ‖₂ + ‖EF‖‖E[τ⁰Ψ]‖ + ‖τ⁰‖₄‖F⁰‖₄‖Ψ‖₂`
  `≤ C(δ₀+W⁻²)W⁻¹ + C(W⁻² + W⁻¹δ₀) + CW⁻²` (`omegaBar_close`, `rightForms_bulk`,
  `deltaFluctuation_all`, `tauCov_bulk`, `selfTau_fluct_bulk`), and the same for `Ψ̄`.
  Radius `min(d₁, d₂)` of `omegaBar_close`/`tauCov_bulk` (`δ₀ ≤ jetDist`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **`E[τ⁰Ψ]`, `E[τ⁰Ψ̄]` are `O(W⁻² + W⁻¹δ₀)`** (strictly passive `X`, bulk-uniform). -/
theorem tauCov_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₁ C : ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDistance0 b E X ≤ d₁ →
      ∀ x y : Fin W → ℂ,
        ‖∫ ω, (selfTau b (gRes b E X ω) - ∫ ω', selfTau b (gRes b E X ω') ∂freshLaw W b) *
            bilinear x (freshDelta b E X ω - matrixExpect (freshLaw W b) (freshDelta b E X)) y
            ∂freshLaw W b‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDistance0 b E X) * (vecNorm x * vecNorm y) ∧
        ‖∫ ω, (selfTau b (gRes b E X ω) - ∫ ω', selfTau b (gRes b E X ω') ∂freshLaw W b) *
            star (bilinear x (freshDelta b E X ω -
              matrixExpect (freshLaw W b) (freshDelta b E X)) y) ∂freshLaw W b‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDistance0 b E X) * (vecNorm x * vecNorm y) := by
  obtain ⟨d₁, C, Cτ, W₀, hd₁, hC, -, h⟩ := trace_test_bound hGA hLp hb0 hb hκ
  refine ⟨d₁, C, max W₀ 1, hd₁, hC, fun W hW E hE X hY hδ x y => ?_⟩
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hW0 : W ≠ 0 := by have := le_of_max_le_right hW; omega
  obtain ⟨hτ4, hgen⟩ := h W (le_of_max_le_left hW) E hE X hY hδ
  set μ := freshLaw W b
  set S := sTilde W b
  have hS : ‖S‖ ≤ 1 := norm_sTilde_le hb0 hb
  set mτ := ∫ ω', selfTau b (gRes b E X ω') ∂μ
  set τ0 := fun ω => selfTau b (gRes b E X ω) - mτ
  have hτθ : τ0 = fun ω => tauD S (gRes b E X ω) + -mτ := by
    funext ω; simp only [τ0, selfTau_eq_tauD b hW0]; ring
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hB1 := fun ω => one_le_one_add_btFun b E X ω
  have hG1 := fun ω => norm_gRes_le_one_add b E X ω
  -- the test `τ⁰`
  have hD : HasLayerDeriv τ0 (fun ω => tauDer S (gRes b E X ω)) := by
    rw [hτθ]; exact hasLayerDeriv_tauD hη hY S (-mτ)
  have hτm : Measurable τ0 := by
    rw [hτθ]; exact ((continuous_tauD S).measurable.comp hGm).add_const _
  have hDc : ∀ N, Continuous fun G : LayerMat W => tauDer S G N := fun N =>
    ((continuous_tauD S).comp ((continuous_id.matrix_mul continuous_const).matrix_mul
      continuous_id)).neg
  have hDm : ∀ N, Measurable fun ω => tauDer S (gRes b E X ω) N := fun N =>
    (hDc N).measurable.comp hGm
  have hτB : ∀ ω, ‖τ0 ω‖ ≤ (2 + ‖mτ‖) * (1 + btFun b E X ω) ^ 1 := fun ω => by
    rw [hτθ, pow_one]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    have := norm_tauD_le hS (gRes b E X ω)
    nlinarith [hG1 ω, hB1 ω, norm_nonneg mτ]
  have hDB0 : ∀ G N : LayerMat W, ‖tauDer S G N‖ ≤ 2 * ‖N‖ * ‖G‖ ^ 2 := fun G N => by
    rw [tauDer_apply, norm_neg]
    refine (norm_tauD_le hS _).trans ?_
    have : ‖G * N * G‖ ≤ ‖G‖ * ‖N‖ * ‖G‖ := (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    nlinarith
  have hDB : ∀ ω N, ‖tauDer S (gRes b E X ω) N‖ ≤ (2 * ‖N‖) * (1 + btFun b E X ω) ^ 2 :=
    fun ω N => (hDB0 _ N).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hG1 ω) 2) (by positivity))
  have hAn : ∀ G : LayerMat W, ‖G * S * G‖ ≤ ‖G‖ ^ 2 := fun G => by
    have : ‖G * S * G‖ ≤ ‖G‖ * ‖S‖ * ‖G‖ := (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    nlinarith [norm_nonneg G, norm_nonneg S]
  have hAc : Continuous fun G : LayerMat W => G * S * G :=
    (continuous_id.matrix_mul continuous_const).matrix_mul continuous_id
  have hτ4m : MemLp τ0 4 μ := lt_of_le_of_lt hτ4 ENNReal.ofReal_lt_top
  have hτi : Integrable τ0 μ := hτ4m.integrable (by norm_num)
  have hτ0 : ∫ ω, τ0 ω ∂μ = 0 := by
    have hsi : Integrable (fun ω => selfTau b (gRes b E X ω)) μ := by
      have e : (fun ω => selfTau b (gRes b E X ω)) = fun ω => τ0 ω + mτ := by
        funext ω; simp only [τ0]; ring
      rw [e]; exact hτi.add (integrable_const _)
    simp only [τ0]
    rw [integral_sub hsi (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    exact sub_self _
  have r1 := hgen τ0 _ (fun G => G * S * G) (2 + ‖mτ‖) (by positivity) hD hτm hDm hτB hDB hAc
    hAn (fun ω β γ => tauDer_single S _ β γ) hτ0 hτ4 x y
  refine ⟨r1, ?_⟩
  -- the test `conj τ⁰`
  have hD' := hasLayerDeriv_star hD
  have hσm : Measurable fun ω => star (τ0 ω) := continuous_star.measurable.comp hτm
  have hDm' : ∀ N, Measurable fun ω => starDeriv (tauDer S (gRes b E X ω)) N := fun N =>
    continuous_star.measurable.comp (hDm Nᴴ)
  have hσB : ∀ ω, ‖star (τ0 ω)‖ ≤ (2 + ‖mτ‖) * (1 + btFun b E X ω) ^ 1 := fun ω => by
    rw [norm_star]; exact hτB ω
  have hDB' : ∀ ω N, ‖starDeriv (tauDer S (gRes b E X ω)) N‖ ≤
      (2 * ‖N‖) * (1 + btFun b E X ω) ^ 2 := fun ω N => by
    rw [starDeriv_apply, norm_star]
    have := hDB ω Nᴴ
    rwa [Matrix.l2_opNorm_conjTranspose] at this
  have hAn' : ∀ G : LayerMat W, ‖(G * S * G)ᴴ‖ ≤ ‖G‖ ^ 2 := fun G => by
    rw [Matrix.l2_opNorm_conjTranspose]; exact hAn G
  have hσ0 : ∫ ω, star (τ0 ω) ∂μ = 0 := by
    show ∫ ω, (starRingEnd ℂ) (τ0 ω) ∂μ = 0
    rw [integral_conj, hτ0, map_zero]
  have hσ4 : eLpNorm (fun ω => star (τ0 ω)) 4 μ ≤ ENNReal.ofReal (Cτ / W) := by
    have hs : eLpNorm (fun ω => star (τ0 ω)) 4 μ = eLpNorm τ0 4 μ := eLpNorm_star (f := τ0)
    rw [hs]; exact hτ4
  have r2 := hgen (fun ω => star (τ0 ω)) _ (fun G => (G * S * G)ᴴ) (2 + ‖mτ‖) (by positivity)
    hD' hσm hDm' hσB hDB' hAc.matrix_conjTranspose hAn'
    (fun ω β γ => starDeriv_tauDer_single S _ β γ) hσ0 hσ4 x y
  refine le_of_eq_of_le ?_ r2
  have e : ∫ ω, (selfTau b (gRes b E X ω) - mτ) *
      star (bilinear x (freshDelta b E X ω - matrixExpect μ (freshDelta b E X)) y) ∂μ =
      (starRingEnd ℂ) (∫ ω, star (τ0 ω) *
        bilinear x (freshDelta b E X ω - matrixExpect μ (freshDelta b E X)) y ∂μ) := by
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [τ0, Complex.star_def, map_mul, Complex.conj_conj]
  rw [e, Complex.norm_conj]

end BlockBand.SourceProcess.FullSourceCovariance
