module

public import BlockBand.SourceProcess.FullSourceCovariance.CovSameLevel0
public import BlockBand.SourceProcess.FullSourceCovariance.RightIBP

/-!
# Level 0 of the opposite-sign `Δ`-covariance: the exact identity

Strictly passive `X`, `E ∈ bulkInterval κ`,
`W ≥ W₀` (`W₀` uniform). Notation of `CovSameLevel0`: `a = ι₁x`, `c = ι₁y`, `a' = ι₁x'`,
`c' = ι₁y'`, `K̂ = diag(K, I)`, `F = a*K̂𝒢c = x*K𝒢₁₁y`, `Ψ = x'*(Δ - EΔ)y'`, `τ = selfTau`:

`CrossCov(x,y;x',y') = E[((z+E) + τ)F·conj Ψ]
   + Σ_{β,γ} c_β σ(β,γ) E[(a*K̂𝒢)_γ · conj((a'*K̂𝒢)_γ) · conj((𝒢K̂c')_β)]`
(`cov_opp_level0`).

This is `delta_ibp` with the test `conj Ψ` and derivative `starDeriv ∘ resFormDeriv`
(`hasLayerDeriv_star`); `starDeriv(resFormDeriv)(E_{βγ}) = -conj((a'*K̂𝒢)_γ (𝒢K̂c')_β)`.
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

/-- `CrossCov(P, Q) = E[P·conj Q⁰]` for the bilinear forms of `U` (`L¹` entries). -/
theorem crossCov_eq_integral_mul_centered {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hU : ∀ i j, Integrable (fun ω => U ω i j) μ) (x y x' y' : Fin W → ℂ)
    (hP : Integrable (fun ω => bilinear x (U ω) y *
      star (bilinear x' (U ω - matrixExpect μ U) y')) μ)
    (hQ : Integrable (fun ω => bilinear x' (U ω) y') μ) :
    bilinearCrossCovariance μ U x y x' y' =
      ∫ ω, bilinear x (U ω) y * star (bilinear x' (U ω - matrixExpect μ U) y') ∂μ := by
  have hQ' : Integrable (fun ω => star (bilinear x' (U ω - matrixExpect μ U) y')) μ := by
    simp only [PassiveLayer.bilinear_sub_matrixExpect U hU]
    exact integrable_star_fun (hQ.sub (integrable_const _))
  have h0 : ∫ ω, star (bilinear x' (U ω - matrixExpect μ U) y') ∂μ = 0 := by
    have e : ∫ ω, star (bilinear x' (U ω - matrixExpect μ U) y') ∂μ =
        star (∫ ω, bilinear x' (U ω - matrixExpect μ U) y' ∂μ) := integral_conj
    rw [e]
    simp only [PassiveLayer.bilinear_sub_matrixExpect U hU]
    rw [integral_sub hQ (integrable_const _), integral_const]
    simp
  rw [bilinearCrossCovariance]
  have e : (fun ω => bilinear x (U ω - matrixExpect μ U) y *
      star (bilinear x' (U ω - matrixExpect μ U) y')) =
      fun ω => bilinear x (U ω) y * star (bilinear x' (U ω - matrixExpect μ U) y') -
        bilinear x (matrixExpect μ U) y * star (bilinear x' (U ω - matrixExpect μ U) y') := by
    funext ω; rw [PassiveCovariance.bilinear_sub x (U ω), sub_mul]
  rw [e, integral_sub hP (hQ'.const_mul _), integral_const_mul, h0, mul_zero, sub_zero]

/-- `starDeriv (resFormDeriv G u v) (E_{βγ}) = -conj((u*G)_γ (Gv)_β)`. -/
theorem starDeriv_resFormDeriv_single (G : LayerMat W) (u v : LayerSite W .oneBlockOnePort → ℂ)
    (β γ : LayerSite W .oneBlockOnePort) :
    starDeriv (resFormDeriv G u v) (Matrix.single β γ 1) =
      -(star ((star u ᵥ* G) γ) * star ((G *ᵥ v) β)) := by
  rw [starDeriv_apply, Matrix.conjTranspose_single, star_one, resFormDeriv_single, star_neg,
    star_mul']

/-- **Level 0, opposite signs**: the exact cross-covariance identity. -/
theorem cov_opp_level0 (hA : PassiveBoundsStatement) (hGA : GaussianAbsorptionContract)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ x y x' y' : Fin W → ℂ,
      bilinearCrossCovariance (freshLaw W b) (freshDelta b E X) x y x' y' =
        ∫ ω, ((boundaryZ b E + E) + selfTau b (gRes b E X ω)) *
            (star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ physVec y)) *
            star (bilinear x' (freshDelta b E X ω -
              matrixExpect (freshLaw W b) (freshDelta b E X)) y') ∂freshLaw W b +
        ∑ β, ∑ γ, physVec y β * siteVar W b β γ *
          ∫ ω, (star (physVec x) ᵥ* (kHat b E X * gRes b E X ω)) γ *
            (star ((star (physVec x') ᵥ* (kHat b E X * gRes b E X ω)) γ) *
              star ((gRes b E X ω *ᵥ (kHat b E X *ᵥ physVec y')) β)) ∂freshLaw W b := by
  obtain ⟨W₁, hI⟩ := ibp_hyps_bulk hA hb0 hb hκ
  obtain ⟨C2, W₂, hC2, hmom⟩ := FullSource.delta_moments hGA b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨C1, W₃, -, hint⟩ := FullSource.delta_integrable hGA b hb0 hb κ hκ
  refine ⟨max W₁ (max W₂ W₃), fun W hW E hE X hY x y x' y' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨hW₁, hW₂, hW₃⟩ := hW
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  set μ := freshLaw W b
  set Kh := kHat b E X
  set u := Khᴴ *ᵥ physVec x'
  set v := Kh *ᵥ physVec y'
  set κ' : ℂ := -(bilinear x' (boundaryZ b E • 1 - X) y' +
    bilinear x' (matrixExpect μ (freshDelta b E X)) y')
  set Ψ : LayerSample W .oneBlockOnePort → ℂ := fun ω =>
    bilinear x' (freshDelta b E X ω - matrixExpect μ (freshDelta b E X)) y'
  have hΨe : ∀ ω, Ψ ω = star u ⬝ᵥ (gRes b E X ω *ᵥ v) + κ' := fun ω => by
    simp only [Ψ, PassiveCovariance.bilinear_sub, delta_eq_resForm, κ', u, v, Kh]; ring
  have hΨfun : Ψ = fun ω => star u ⬝ᵥ (gRes b E X ω *ᵥ v) + κ' := funext hΨe
  have hD : HasLayerDeriv Ψ (fun ω => resFormDeriv (gRes b E X ω) u v) := by
    intro ω hω Δ hΔ
    have := (hasLayerDeriv_resForm hη hY u v ω hω Δ hΔ).add_const κ'
    rw [hΨfun]; exact this
  have hDs := hasLayerDeriv_star hD
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hcf : Continuous fun G : LayerMat W => star u ⬝ᵥ (G *ᵥ v) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  have hΨm : Measurable Ψ := by rw [hΨfun]; exact (hcf.measurable.comp hGm).add_const _
  have hΨsm : Measurable fun ω => star (Ψ ω) := continuous_star.measurable.comp hΨm
  have hDm : ∀ N, Measurable fun ω => starDeriv (resFormDeriv (gRes b E X ω) u v) N := fun N => by
    have hc : Continuous fun G : LayerMat W => star (-(star u ⬝ᵥ ((G * Nᴴ * G) *ᵥ v))) :=
      continuous_star.comp (continuous_const.dotProduct (((continuous_id.matrix_mul
        continuous_const).matrix_mul continuous_id).matrix_mulVec continuous_const)).neg
    exact hc.measurable.comp hGm
  have hB1 : ∀ ω, ‖star (Ψ ω)‖ ≤ (vecNorm u * vecNorm v + ‖κ'‖) * (1 + btFun b E X ω) ^ 1 :=
    fun ω => by
    rw [norm_star, hΨe, pow_one]
    have hg := norm_gRes_le_one_add b E X ω
    have h1' := one_le_one_add_btFun b E X ω
    have := PassiveCovariance.vecNorm_nonneg u; have := PassiveCovariance.vecNorm_nonneg v
    calc ‖star u ⬝ᵥ (gRes b E X ω *ᵥ v) + κ'‖ ≤ vecNorm u * vecNorm v * ‖gRes b E X ω‖ + ‖κ'‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_form_le u v _)
      _ ≤ vecNorm u * vecNorm v * (1 + btFun b E X ω) + ‖κ'‖ * (1 + btFun b E X ω) := by
          gcongr; nlinarith [norm_nonneg κ']
      _ = _ := by ring
  have hB2 : ∀ ω N, ‖starDeriv (resFormDeriv (gRes b E X ω) u v) N‖ ≤
      (vecNorm u * vecNorm v * ‖N‖) * (1 + btFun b E X ω) ^ 2 := fun ω N => by
    rw [starDeriv_apply, norm_star, resFormDeriv_apply, norm_neg]
    have hg := norm_gRes_le_one_add b E X ω
    have := PassiveCovariance.vecNorm_nonneg u; have := PassiveCovariance.vecNorm_nonneg v
    refine (norm_form_le u v _).trans ?_
    have hGNG : ‖gRes b E X ω * Nᴴ * gRes b E X ω‖ ≤ ‖N‖ * (1 + btFun b E X ω) ^ 2 := by
      calc ‖gRes b E X ω * Nᴴ * gRes b E X ω‖ ≤ ‖gRes b E X ω‖ * ‖Nᴴ‖ * ‖gRes b E X ω‖ :=
            (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
              (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
        _ ≤ (1 + btFun b E X ω) * ‖N‖ * (1 + btFun b E X ω) := by
            rw [Matrix.l2_opNorm_conjTranspose]
            exact mul_le_mul (mul_le_mul_of_nonneg_right hg (norm_nonneg _)) hg (norm_nonneg _)
              (mul_nonneg (by linarith [btFun_nonneg b E X ω]) (norm_nonneg _))
        _ = _ := by ring
    calc vecNorm u * vecNorm v * ‖gRes b E X ω * Nᴴ * gRes b E X ω‖
        ≤ vecNorm u * vecNorm v * (‖N‖ * (1 + btFun b E X ω) ^ 2) := by gcongr
      _ = _ := by ring
  obtain ⟨hL2, hI1, hI2, hI3, hF⟩ := hI W hW₁ E hE X hY (physVec x) (physVec y) _ _
    (add_nonneg (mul_nonneg (PassiveCovariance.vecNorm_nonneg u)
      (PassiveCovariance.vecNorm_nonneg v)) (norm_nonneg _))
    (mul_nonneg (PassiveCovariance.vecNorm_nonneg u) (PassiveCovariance.vecNorm_nonneg v))
    (fun ω => star (Ψ ω)) _ hΨsm hDm hB1 hB2
  have hibp := delta_ibp hb h1 h2 hY hDs hΨsm x y hL2 hI1 hI2 hI3 hF
  have hmeasΔ : Measurable fun ω => freshDelta b E X ω :=
    FullSource.measurable_freshDelta_comp b E (X := fun _ => X) measurable_const measurable_id
  obtain ⟨hent, -⟩ := hint W hW₃ E hE X hY.posSemidef
  have hL2Δ : ∀ (p q : Fin W → ℂ) (M : Matrix (Fin W) (Fin W) ℂ),
      MemLp (fun ω => bilinear p (freshDelta b E X ω - M) q) 2 μ := fun p q M => by
    have hm := (hmom W hW₂ E hE X hY.posSemidef)
    have hb2 : MemLp (fun ω => vecNorm p * (‖freshDelta b E X ω‖ + ‖M‖) * vecNorm q) 2 μ := by
      have h0 : MemLp (fun ω => ‖freshDelta b E X ω‖) 2 μ :=
        lt_of_le_of_lt (by simpa using hm.2) ENNReal.ofReal_lt_top
      exact ((h0.add (memLp_const _)).const_mul _).mul_const _
    refine hb2.of_le (((PassiveCovariance.continuous_bilinear p q).measurable.comp
      (hmeasΔ.sub measurable_const)).aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
    refine (PassiveCovariance.norm_bilinear_le p _ q).trans ?_
    have := PassiveCovariance.vecNorm_nonneg p; have := PassiveCovariance.vecNorm_nonneg q
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr; exact norm_sub_le _ _
  have hcov := crossCov_eq_integral_mul_centered (μ := μ) (freshDelta b E X) hent x y x' y'
    (by
      have := (hL2Δ x y 0).integrable_mul (hL2Δ x' y' (matrixExpect μ (freshDelta b E X))).star
      simp only [Pi.mul_def, sub_zero] at this; exact this)
    (by
      have := (hL2Δ x' y' 0).integrable one_le_two
      simp only [sub_zero] at this; exact this)
  rw [hcov]
  change ∫ ω, bilinear x (freshDelta b E X ω) y * star (Ψ ω) ∂μ = _
  rw [hibp]
  have hu : ∀ G : LayerMat W, star u ᵥ* G = star (physVec x') ᵥ* (Kh * G) := fun G => by
    rw [star_mulVec, conjTranspose_conjTranspose, vecMul_vecMul]
  have hS : ∀ β γ, ∫ ω, (star (physVec x) ᵥ* (Kh * gRes b E X ω)) γ *
      starDeriv (resFormDeriv (gRes b E X ω) u v) (Matrix.single β γ 1)
        ∂layerLaw W b .oneBlockOnePort =
      -∫ ω, (star (physVec x) ᵥ* (Kh * gRes b E X ω)) γ *
        (star ((star (physVec x') ᵥ* (Kh * gRes b E X ω)) γ) *
          star ((gRes b E X ω *ᵥ v) β)) ∂μ := by
    intro β γ
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show _ * starDeriv (resFormDeriv (gRes b E X ω) u v) (Matrix.single β γ 1) = _
    rw [starDeriv_resFormDeriv_single, hu]; ring
  rw [Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ =>
    congrArg (fun t => physVec y β * siteVar W b β γ * t) (hS β γ)]
  simp only [mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  rfl

end BlockBand.SourceProcess.FullSourceCovariance
