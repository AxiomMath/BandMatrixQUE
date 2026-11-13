module

public import BlockBand.SourceProcess.FullSourceCovariance.CrossedSameCov
public import BlockBand.SourceProcess.FullSourceCovariance.PhiSameHolds
public import BlockBand.SourceProcess.FullSourceCovariance.FirstTermHolds
public import BlockBand.SourceProcess.FullSourceCovariance.Decomposition

/-!
# `CrossedSameBound` holds; both full-source covariance statements

The equal-sign crossed product bound holds, and with it the full-source covariance statements
(`fullSourceCovarianceEnergyUniform_holds`, `fullSourceCovariance_holds`).

* `integral_mul_eq`: `E[PH] = EP·EH + E[P⁰H⁰]` for `P, H ∈ L²`;
* **`crossedSameBound_holds hGA hLp : CrossedSameBound`**. With `Φ = phiSame x y'`, `F' = fForm x' y`:
  `E[F'Φ] - (σ₋/W)(x*y')(x'*y) = E[Φ⁰F'⁰] + (EF' - x'*y)·EΦ + (x'*y)(EΦ - σ₋/W·x*y')`, and
  - `|E[Φ⁰F'⁰]| ≤ C(W⁻² + W⁻¹δ₀)∏` (`phiCov_bulk`);
  - `|EF' - x'*y| = |x'*EΔ(Ry)| ≤ η⁻¹C(δ₀ + W⁻²)` (`rightForms_bulk`, `deltaMean_strict`);
  - `|EΦ| ≤ (σ₊ + C(d + 1))/W` and the last term are `PhiSameMean` (`phiSameMean_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Internal.Contracts.TransmissionUniform2
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `E[PH] = EP·EH + E[P⁰H⁰]` for `P, H ∈ L²`. -/
theorem integral_mul_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {P H : Ω → ℂ} (hP : MemLp P 2 μ) (hH : MemLp H 2 μ) :
    ∫ ω, P ω * H ω ∂μ = (∫ ω, P ω ∂μ) * (∫ ω, H ω ∂μ) +
      ∫ ω, (P ω - ∫ ω', P ω' ∂μ) * (H ω - ∫ ω', H ω' ∂μ) ∂μ := by
  set mP := ∫ ω, P ω ∂μ
  set mH := ∫ ω, H ω ∂μ
  have hPi := hP.integrable one_le_two
  have hHi := hH.integrable one_le_two
  have hPH : Integrable (fun ω => P ω * H ω) μ := hP.integrable_mul hH
  have e : (fun ω => (P ω - mP) * (H ω - mH)) =
      fun ω => P ω * H ω - mH * P ω - mP * H ω + mP * mH := by funext ω; ring
  have i1 : Integrable (fun ω => P ω * H ω - mH * P ω) μ := hPH.sub (hPi.const_mul _)
  have i2 : Integrable (fun ω => P ω * H ω - mH * P ω - mP * H ω) μ := i1.sub (hHi.const_mul _)
  rw [e, integral_add i2 (integrable_const _), integral_sub i1 (hHi.const_mul _),
    integral_sub hPH (hPi.const_mul _), integral_const_mul, integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-- **`CrossedSameBound`**, from `GaussianAbsorptionContract` and `GaussianLpGradient`. -/
theorem crossedSameBound_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    CrossedSameBound := by
  intro b hb0 hb κ hκ
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨dM, hdM, CM, WM, hMb⟩ := phiSameMean_holds hGA hLp b hb0 hb κ hκ
  obtain ⟨d₁, C₁, W₁, hd₁, hC₁, hC1⟩ := phiCov_bulk hGA hLp hb0 hb hκ
  obtain ⟨d₂, CΔ, WΔ, hd₂, hCΔ, hΔ⟩ := FullSource.deltaMean_strict hA hb0 hb hκ
  obtain ⟨Ch, Wh, hCh, hh⟩ := rightForms_bulk hGA hLp hb0 hb hκ 2 one_le_two
  have hσ0 : 0 ≤ sigmaPlus b := by
    rw [sigmaPlus, kPlus]; exact div_nonneg (by nlinarith) hb0.le
  have hηL := PathScalar.etaLow_pos (b := b) (by linarith) hκ
  set CM' := max CM 0
  set ηi := (PathScalar.etaLow b κ)⁻¹
  set Cσ := sigmaPlus b + CM' * (dM + 1)
  refine ⟨min dM (min d₁ d₂), lt_min hdM (lt_min hd₁ hd₂), C₁ + Cσ * ηi * CΔ + CM',
    max (max WM W₁) (max (max WΔ Wh) 1), fun W hW E hE s hs X hY hd x y x' y' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWM, hW₁⟩, ⟨hWΔ, hWh⟩, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWr : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hWi : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW1)
  have hWi0 : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr hWr.le
  -- the jet distance
  have hg := conductance_nonneg b E hη.le hY.posSemidef
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδ1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  have hJ : jetDistance0 b E X ≤ jetDist b E s X := by
    unfold jetDist; have := div_nonneg hg hWr.le; linarith
  have hJ0 : 0 ≤ jetDist b E s X := hδ0.trans hJ
  have hdM' : jetDist b E s X ≤ dM := hd.trans (min_le_left _ _)
  have hd₁' : jetDistance0 b E X ≤ d₁ :=
    hJ.trans (hd.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd₂' : jetDistance0 b E X ≤ d₂ :=
    hJ.trans (hd.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcov : covErr b E s X = (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDist b E s X := rfl
  set ε := covErr b E s X
  have hcA : (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDistance0 b E X ≤ ε := by
    rw [hcov]; nlinarith [mul_le_mul_of_nonneg_left hJ hWi0]
  have hcB : (W : ℝ)⁻¹ * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ≤ ε := by
    rw [hcov]; nlinarith [mul_le_mul_of_nonneg_left hJ hWi0]
  have hcC : (W : ℝ)⁻¹ * (jetDist b E s X + (W : ℝ)⁻¹) = ε := by rw [hcov]; ring
  -- the two factors
  obtain ⟨hΦ2, hA1⟩ := hC1 W hW₁ E hE X hY hd₁' x y x' y'
  obtain ⟨hF0, -, hmF, -⟩ := hh W hWh E hE X hY.posSemidef x' y
  rw [ENNReal.ofReal_ofNat] at hF0
  set mF := ∫ ω, fForm b E X x' y ω ∂freshLaw W b
  set mP := ∫ ω, phiSame b E X x y' ω ∂freshLaw W b
  have hF0m : MemLp (fun ω => fForm b E X x' y ω - mF) 2 (freshLaw W b) :=
    lt_of_le_of_lt hF0 ENNReal.ofReal_lt_top
  have hFm : MemLp (fForm b E X x' y) 2 (freshLaw W b) := by
    have h := hF0m.add (memLp_const mF)
    have e : ((fun ω => fForm b E X x' y ω - mF) + fun _ => mF) = fForm b E X x' y := by
      funext ω; simp
    rw [e] at h; exact h
  have eFP : ∫ ω, fForm b E X x' y ω * phiSame b E X x y' ω ∂freshLaw W b =
      ∫ ω, phiSame b E X x y' ω * fForm b E X x' y ω ∂freshLaw W b :=
    integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  rw [eFP, integral_mul_eq hΦ2 hFm]
  set A := ∫ ω, (phiSame b E X x y' ω - mP) * (fForm b E X x' y ω - mF) ∂freshLaw W b
  set B₁ := bilinear x 1 y'
  set B₂ := bilinear x' 1 y
  have hT : crossedTensor x y x' y' 1 1 = B₁ * B₂ := rfl
  rw [hT]
  have hsplit : mP * mF + A - sigmaMinus b E s / W * (B₁ * B₂) =
      A + (mF - B₂) * mP + B₂ * (mP - sigmaMinus b E s / W * B₁) := by ring
  rw [hsplit]
  have nx := vecNorm_nonneg x; have ny := vecNorm_nonneg y
  have nx' := vecNorm_nonneg x'; have ny' := vecNorm_nonneg y'
  set n₁ := vecNorm x * vecNorm y'
  set n₂ := vecNorm x' * vecNorm y
  have hN : fourNorm x y x' y' = n₁ * n₂ := by simp only [fourNorm, n₁, n₂]; ring
  have hN' : vecNorm x * vecNorm y * vecNorm x' * vecNorm y' = n₁ * n₂ := by
    simp only [n₁, n₂]; ring
  have hB : ∀ u v : Fin W → ℂ, ‖bilinear u 1 v‖ ≤ vecNorm u * vecNorm v := fun u v => by
    refine (norm_bilinear_le u 1 v).trans ?_
    have := norm_one_matrix_le (n := Fin W); have := vecNorm_nonneg u; have := vecNorm_nonneg v
    calc vecNorm u * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * vecNorm v ≤ vecNorm u * 1 * vecNorm v := by
          gcongr
      _ = _ := by ring
  -- (1) the centred product
  rw [hN'] at hA1
  -- (2) the right letter mean
  have hF2 : ‖mF - B₂‖ ≤ ηi * (CΔ * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) * n₂ := by
    rw [hmF, add_sub_cancel_left]
    refine (norm_bilinear_le _ _ _).trans ?_
    have hRy : vecNorm (passiveResolvent b E X *ᵥ y) ≤ ηi * vecNorm y :=
      (vecNorm_mulVec_le' _ _).trans (mul_le_mul_of_nonneg_right ((norm_passiveResolvent_le hb0 hb
        h1 h2 hY.posSemidef).trans (CovarianceBulk.inv_etaZ_le_bulk hb hκ hE)) ny)
    have hD := hΔ W hWΔ E hE X hY hd₂'
    have := vecNorm_nonneg (passiveResolvent b E X *ᵥ y)
    calc vecNorm x' * ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ *
          vecNorm (passiveResolvent b E X *ᵥ y) ≤
        vecNorm x' * (CΔ * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) * (ηi * vecNorm y) := by
          gcongr
      _ = _ := by simp only [n₂]; ring
  -- (3) the mean of `Φ`
  have hM0 := hMb W hWM E hE s hs X hY hdM' x y'
  have hσm : ‖sigmaMinus b E s‖ ≤ sigmaPlus b :=
    (BlockBand.Transmission.LawClauses.norm_sigmaMinus_lt_sigmaPlus hb0 hb h1 h2 hs).le
  have hCM' : 0 ≤ CM' := le_max_right _ _
  have hP3 : ‖mP - sigmaMinus b E s / W * B₁‖ ≤
      (W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹)) * n₁ := by
    have e : mP - sigmaMinus b E s / W * B₁ =
        (W : ℂ)⁻¹ * ((W : ℂ) * mP - sigmaMinus b E s * B₁) := by
      have : (W : ℂ) ≠ 0 := by exact_mod_cast hWr.ne'
      field_simp
    rw [e, norm_mul, norm_inv, Complex.norm_natCast]
    have : CM * (jetDist b E s X + (W : ℝ)⁻¹) * n₁ ≤ CM' * (jetDist b E s X + (W : ℝ)⁻¹) * n₁ := by
      gcongr; exact le_max_left _ _
    calc (W : ℝ)⁻¹ * ‖(W : ℂ) * mP - sigmaMinus b E s * B₁‖ ≤
        (W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹) * n₁) := by gcongr; exact hM0.trans this
      _ = _ := by ring
  have hP4 : ‖mP‖ ≤ Cσ * (W : ℝ)⁻¹ * n₁ := by
    have e : mP = (mP - sigmaMinus b E s / W * B₁) + sigmaMinus b E s / W * B₁ := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h5 : ‖sigmaMinus b E s / W * B₁‖ ≤ sigmaPlus b * (W : ℝ)⁻¹ * n₁ := by
      rw [norm_mul, norm_div, Complex.norm_natCast, div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hσm hWi0) (hB x y') (norm_nonneg _)
        (by positivity)
    have h6 : (W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹)) * n₁ ≤
        CM' * (dM + 1) * (W : ℝ)⁻¹ * n₁ := by
      have : jetDist b E s X + (W : ℝ)⁻¹ ≤ dM + 1 := by linarith
      have : 0 ≤ n₁ := by positivity
      calc (W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹)) * n₁ =
          CM' * (jetDist b E s X + (W : ℝ)⁻¹) * (W : ℝ)⁻¹ * n₁ := by ring
        _ ≤ CM' * (dM + 1) * (W : ℝ)⁻¹ * n₁ := by gcongr
    calc _ ≤ (W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹)) * n₁ +
          sigmaPlus b * (W : ℝ)⁻¹ * n₁ := add_le_add hP3 h5
      _ ≤ CM' * (dM + 1) * (W : ℝ)⁻¹ * n₁ + sigmaPlus b * (W : ℝ)⁻¹ * n₁ := by linarith
      _ = Cσ * (W : ℝ)⁻¹ * n₁ := by simp only [Cσ]; ring
  -- assembly
  have hn₁ : 0 ≤ n₁ := by positivity
  have hn₂ : 0 ≤ n₂ := by positivity
  have hCσ : 0 ≤ Cσ := by positivity
  have hηi : 0 ≤ ηi := by positivity
  rw [hN]
  calc ‖A + (mF - B₂) * mP + B₂ * (mP - sigmaMinus b E s / W * B₁)‖
      ≤ ‖A‖ + ‖mF - B₂‖ * ‖mP‖ + ‖B₂‖ * ‖mP - sigmaMinus b E s / W * B₁‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [← norm_mul, ← norm_mul]
        gcongr
        exact norm_add_le _ _
    _ ≤ C₁ * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDistance0 b E X) * (n₁ * n₂) +
          (ηi * (CΔ * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) * n₂) * (Cσ * (W : ℝ)⁻¹ * n₁) +
          n₂ * ((W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹)) * n₁) := by
        gcongr
        exact hB x' y
    _ = C₁ * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDistance0 b E X) * (n₁ * n₂) +
          Cσ * ηi * CΔ * ((W : ℝ)⁻¹ * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) * (n₁ * n₂) +
          CM' * ((W : ℝ)⁻¹ * (jetDist b E s X + (W : ℝ)⁻¹)) * (n₁ * n₂) := by ring
    _ ≤ C₁ * ε * (n₁ * n₂) + Cσ * ηi * CΔ * ε * (n₁ * n₂) + CM' * ε * (n₁ * n₂) := by
        rw [hcC]
        gcongr
    _ = (C₁ + Cσ * ηi * CΔ + CM') * ε * (n₁ * n₂) := by ring

/-- **`FullSourceCovarianceEnergyUniformContract`** (additive, energy-uniform), from
`GaussianAbsorptionContract`, `GaussianLpGradient` and `GaussianPoincare`. -/
theorem fullSourceCovarianceEnergyUniform_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    FullSourceCovarianceEnergyUniformContract :=
  fullSourceCovarianceEnergyUniform_of_bounds hGA hLp (firstTermBound_holds hGA hLp)
    (crossedSameBound_holds hGA hLp) (crossedOppBound_of_mean hGA hLp hP (phiOppMean_holds hGA hLp))

/-- **The fixed-`E` full-source covariance statement `FullSourceCovarianceContract`**, from
`GaussianAbsorptionContract`, `GaussianLpGradient` and `GaussianPoincare`. -/
theorem fullSourceCovariance_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) : FullSourceCovarianceContract :=
  fullSourceCovariance_of_bounds hGA hLp (firstTermBound_holds hGA hLp)
    (crossedSameBound_holds hGA hLp) (crossedOppBound_of_mean hGA hLp hP (phiOppMean_holds hGA hLp))

end BlockBand.SourceProcess.FullSourceCovariance
