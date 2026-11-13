module

public import BlockBand.SourceProcess.FullSourceCovariance.OffDomain
public import BlockBand.SourceProcess.FullSourceCovariance.FixedEnergy

/-!
# The two `Δ`-covariance Props from their on-domain forms; the covariance statements from those

* `deltaCovarianceSame_of_onDomain hGA hLp hS : DeltaCovarianceSame` and
  `deltaCovarianceOpposite_of_onDomain hGA hLp hO : DeltaCovarianceOpposite`, with constant
  `max C 0 + (C₁ + σ₊)/d` (`off_domain_bound`).
* **`fullSourceCovarianceEnergyUniform_of_onDomain hGA hLp hS hO`** and
  **`fullSourceCovariance_of_onDomain hGA hLp hS hO`** (the fixed-`E` statement), from
  `GaussianAbsorptionContract`, `GaussianLpGradient` and the two open on-domain Props.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform2
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PassiveCovariance
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The scalar off-domain argument. -/
theorem off_domain_bound {Q M : ℂ} {e dist d C C₁ σ fn w : ℝ} (hd : 0 < d) (hw : 0 < w)
    (hC₁ : 0 ≤ C₁ + σ) (he : w⁻¹ * dist ≤ e) (he0 : 0 ≤ e) (hfn : 0 ≤ fn)
    (hQ : ‖Q‖ ≤ C₁ / w * fn) (hM : ‖M‖ ≤ σ / w * fn) (hon : dist ≤ d → ‖Q - M‖ ≤ C * e * fn) :
    ‖Q - M‖ ≤ (max C 0 + (C₁ + σ) / d) * e * fn := by
  have hq : 0 ≤ (C₁ + σ) / d * e * fn := by positivity
  by_cases h : dist ≤ d
  · refine (hon h).trans ?_
    have : C * e * fn ≤ max C 0 * e * fn := by gcongr; exact le_max_left _ _
    nlinarith
  · rw [not_le] at h
    have h1 : ‖Q - M‖ ≤ (C₁ + σ) / w * fn := by
      have := norm_sub_le Q M
      have e1 : (C₁ + σ) / w * fn = C₁ / w * fn + σ / w * fn := by ring
      linarith
    have h2 : (C₁ + σ) / w ≤ (C₁ + σ) / d * e := by
      have : 1 / w ≤ e / d := by
        rw [div_le_div_iff₀ hw hd]
        have : w⁻¹ * d ≤ e := le_trans (by gcongr) he
        rw [inv_mul_le_iff₀ hw] at this; linarith
      calc (C₁ + σ) / w = (C₁ + σ) * (1 / w) := by ring
        _ ≤ (C₁ + σ) * (e / d) := by gcongr
        _ = (C₁ + σ) / d * e := by ring
    have h3 : (C₁ + σ) / w * fn ≤ (C₁ + σ) / d * e * fn := by gcongr
    have h4 : 0 ≤ max C 0 * e * fn := by have := le_max_right C 0; positivity
    nlinarith

theorem covErr_ge (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    (W : ℝ)⁻¹ * jetDist b E s X ≤ covErr b E s X := by
  rw [covErr, jetDist]; have := sq_nonneg ((W : ℝ)⁻¹); linarith

/-- `DeltaCovarianceSame` from its on-domain form. -/
theorem deltaCovarianceSame_of_onDomain (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (h : DeltaCovarianceSameOnDomain) : DeltaCovarianceSame := by
  intro b hb0 hb κI hκ
  obtain ⟨d, hd, C, W₀, hC⟩ := h b hb0 hb κI hκ
  obtain ⟨C₁, W₁, hC₁, hcr⟩ := crude_delta_cov hGA hLp b hb0 hb κI hκ
  have hσ0 : 0 ≤ sigmaPlus b := by
    rw [sigmaPlus, kPlus]; exact div_nonneg (by nlinarith) hb0.le
  refine ⟨max C 0 + (C₁ + sigmaPlus b) / d, max (max W₀ W₁) 1,
    fun W hW E hE s hs X hY x y x' y' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW1⟩, hWo⟩ := hW
  have hw : (0 : ℝ) < W := by exact_mod_cast hWo
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hη := (etaZ_pos b E (by linarith) hE1 hE2).le
  refine off_domain_bound hd hw (by linarith) (covErr_ge b E s X) (covErr_nonneg b E s hη hY)
    (fourNorm_nonneg _ _ _ _) (hcr W hW1 E hE X hY x y x' y').1 ?_ (hC W hW0 E hE s hs X hY · x y x' y')
  have hσ := (BlockBand.Transmission.LawClauses.norm_sigmaMinus_lt_sigmaPlus hb0 hb hE1 hE2 hs).le
  have hT := norm_crossedTensor_le x y x' y' (1 : Matrix (Fin W) (Fin W) ℂ) 1
  have h1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := norm_one_matrix_le
  have hT' : ‖crossedTensor x y x' y' 1 1‖ ≤ fourNorm x y x' y' := by
    have := fourNorm_nonneg x y x' y'
    have : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
      nlinarith [norm_nonneg (1 : Matrix (Fin W) (Fin W) ℂ)]
    nlinarith
  rw [norm_mul, norm_div, Complex.norm_natCast]
  have := fourNorm_nonneg x y x' y'
  calc ‖sigmaMinus b E s‖ / W * ‖crossedTensor x y x' y' 1 1‖
      ≤ sigmaPlus b / W * fourNorm x y x' y' := by gcongr

/-- `DeltaCovarianceOpposite` from its on-domain form. -/
theorem deltaCovarianceOpposite_of_onDomain (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (h : DeltaCovarianceOppositeOnDomain) :
    DeltaCovarianceOpposite := by
  intro b hb0 hb κI hκ
  obtain ⟨d, hd, C, W₀, hC⟩ := h b hb0 hb κI hκ
  obtain ⟨C₁, W₁, hC₁, hcr⟩ := crude_delta_cov hGA hLp b hb0 hb κI hκ
  have hσ0 : 0 ≤ sigmaPlus b := by
    rw [sigmaPlus, kPlus]; exact div_nonneg (by nlinarith) hb0.le
  refine ⟨max C 0 + (C₁ + sigmaPlus b) / d, max (max W₀ W₁) 1,
    fun W hW E hE s hs X hY x y x' y' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW1⟩, hWo⟩ := hW
  have hw : (0 : ℝ) < W := by exact_mod_cast hWo
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hη := (etaZ_pos b E (by linarith) hE1 hE2).le
  refine off_domain_bound hd hw (by linarith) (covErr_ge b E s X) (covErr_nonneg b E s hη hY)
    (fourNorm_nonneg _ _ _ _) (hcr W hW1 E hE X hY x y x' y').2 ?_ (hC W hW0 E hE s hs X hY · x y x' y')
  have h1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := norm_one_matrix_le
  have hb1 := norm_bilinear_le x (1 : Matrix (Fin W) (Fin W) ℂ) x'
  have hb2 := norm_bilinear_le y' (1 : Matrix (Fin W) (Fin W) ℂ) y
  have hx := vecNorm_nonneg x; have hy := vecNorm_nonneg y
  have hx' := vecNorm_nonneg x'; have hy' := vecNorm_nonneg y'
  have hb1' : ‖bilinear x 1 x'‖ ≤ vecNorm x * vecNorm x' := by
    refine hb1.trans ?_
    calc vecNorm x * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * vecNorm x' ≤ vecNorm x * 1 * vecNorm x' := by
          gcongr
      _ = _ := by ring
  have hb2' : ‖bilinear y' 1 y‖ ≤ vecNorm y' * vecNorm y := by
    refine hb2.trans ?_
    calc vecNorm y' * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * vecNorm y ≤ vecNorm y' * 1 * vecNorm y := by
          gcongr
      _ = _ := by ring
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hσ0,
    norm_mul]
  calc sigmaPlus b / W * (‖bilinear x 1 x'‖ * ‖bilinear y' 1 y‖)
      ≤ sigmaPlus b / W * ((vecNorm x * vecNorm x') * (vecNorm y' * vecNorm y)) := by gcongr
    _ = sigmaPlus b / W * fourNorm x y x' y' := by rw [fourNorm]; ring

/-- **The energy-uniform full-source contract** from input hypotheses and the two open on-domain `Δ` Props. -/
theorem fullSourceCovarianceEnergyUniform_of_onDomain (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hS : DeltaCovarianceSameOnDomain)
    (hO : DeltaCovarianceOppositeOnDomain) : FullSourceCovarianceEnergyUniformContract :=
  fullSourceCovarianceEnergyUniform_of_delta hGA (deltaCovarianceSame_of_onDomain hGA hLp hS)
    (deltaCovarianceOpposite_of_onDomain hGA hLp hO)

/-- **`FullSourceCovarianceContract`** from the Gaussian inputs and the two open on-domain
`Δ` Props. -/
theorem fullSourceCovariance_of_onDomain (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hS : DeltaCovarianceSameOnDomain)
    (hO : DeltaCovarianceOppositeOnDomain) : FullSourceCovarianceContract :=
  fullSourceCovariance_of_uniform (fullSourceCovarianceEnergyUniform_of_onDomain hGA hLp hS hO)

end BlockBand.SourceProcess.FullSourceCovariance
