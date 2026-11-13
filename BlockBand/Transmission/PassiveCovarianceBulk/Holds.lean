module

public import BlockBand.Transmission.PassiveCovarianceBulk.Statement
public import BlockBand.Transmission.PassiveCovarianceBulk.Strict
public import BlockBand.Transmission.PassiveCovarianceBulk.MeansMatch
public import BlockBand.Transmission.PassiveCovarianceBulk.M4Near
public import BlockBand.Transmission.PassiveCovariance.PassiveBoundsBridge
public import BlockBand.Transmission.LengthUniform.BulkMassLayer
public import BlockBand.Transmission.LawClauses.JetGap

/-!
# The bulk-uniform passive covariance

`passiveCovarianceBulk_holds`: under `GaussianAbsorptionContract`, `GaussianLpGradient` and
`GaussianPoincare`, the passive covariance bound holds with constants uniform on the bulk.

* `passiveFluctuationL2_of_passiveBounds_bulk` (`oneStepFluctuation_bulk`, `p = 2`);
* `crudeCovariance_of_fluctuation_bulk` (Cauchy–Schwarz, unchanged proof);
* `mainConst_le_bulk`: `mainConst b E s ≤ mainConstL b κ` (`D₀ = σ₊/(2η²)`, `|σ₋| < σ₊`,
  `η ≥ η_L`);
* `passiveCovariance_of_domain_bulk`, `passiveCovariance_holds_of_normalized_bulk`,
  `passiveCovariance_holds_of_match_bulk`, `passiveCovariance_holds_of_alp_bulk`;
* **`passiveCovarianceBulk_holds hGA hLp hP : PassiveCovarianceBulk`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.PathScalar (etaLow etaLow_pos etaLow_le bulk_bounds)
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

/-- Bulk-uniform `passiveFluctuationL2_of_passiveBounds`. -/
theorem passiveFluctuationL2_of_passiveBounds_bulk (h : PassiveBoundsStatement) :
    PassiveFluctuationL2Bulk := by
  intro b hb0 hb κ hκ
  obtain ⟨C, W₀, hC⟩ := oneStepFluctuation_bulk h hb0 hb hκ 2 one_le_two
  refine ⟨C, W₀, fun W hW E hEκ X hX u v => ?_⟩
  have := (hC W hW E hEκ X hX u v).1
  rwa [ENNReal.ofReal_ofNat] at this

/-- Bulk-uniform `crudeCovariance_of_fluctuation`. -/
theorem crudeCovariance_of_fluctuation_bulk (h : PassiveFluctuationL2Bulk) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (C₁ : ℝ) (W₀ : ℕ), 0 ≤ C₁ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
          ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄‖ ≤
            C₁ / W * fourNorm v₁ v₂ v₃ v₄ := by
  intro b hb0 hb κ hκ
  obtain ⟨C, W₀, hC⟩ := h b hb0 hb κ hκ
  refine ⟨|C| ^ 2, W₀, sq_nonneg _, fun W hW E hEκ X hX v₁ v₂ v₃ v₄ => ?_⟩
  set μ := freshLaw W b
  have hle : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
      matrixExpect μ (freshU b E X)) v) 2 μ ≤
      ENNReal.ofReal (|C| / Real.sqrt W * vecNorm u * vecNorm v) := fun u v =>
    (hC W hW E hEκ X hX u v).trans (ENNReal.ofReal_le_ofReal (by
      have := vecNorm_nonneg u; have := vecNorm_nonneg v
      gcongr; exact le_abs_self C))
  have hcs := enorm_bilinearCovariance_le μ (freshU b E X) v₁ v₂ v₃ v₄
    (measurable_bilinear_centered b E X _ v₁ v₂).aemeasurable
    (measurable_bilinear_centered b E X _ v₃ v₄).aemeasurable
  have hprod := hcs.trans (mul_le_mul' (hle v₁ v₂) (hle v₃ v₄))
  have hn := fun v : Fin W → ℂ => vecNorm_nonneg v
  have ha : 0 ≤ |C| / Real.sqrt W * vecNorm v₁ * vecNorm v₂ := by
    have := hn v₁; have := hn v₂; positivity
  rw [← ENNReal.ofReal_mul ha, ← ofReal_norm] at hprod
  have hb' := (ENNReal.ofReal_le_ofReal_iff (by have := hn v₃; have := hn v₄; positivity)).mp hprod
  refine hb'.trans (le_of_eq ?_)
  rw [fourNorm]
  rcases (Nat.cast_nonneg W : (0 : ℝ) ≤ W).lt_or_eq with hWp | hWz
  · have hs : Real.sqrt W ^ 2 = W := Real.sq_sqrt hWp.le
    have hs0 : Real.sqrt W ≠ 0 := (Real.sqrt_pos.mpr hWp).ne'
    field_simp
    rw [hs]
    ring
  · rw [← hWz]; simp

/-- Uniform majorant of `mainConst b E s` on `bulkInterval κ`. -/
def mainConstL (b κ : ℝ) : ℝ :=
  9 * (sigmaPlus b / (2 * etaLow b κ ^ 2)) + 2 * sigmaPlus b * (3 / (2 * etaLow b κ)) ^ 2

theorem mainConst_le_bulk {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s) :
    mainConst b E s ≤ mainConstL b κ := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hηL := etaLow_pos (b := b) (by linarith) hκ
  have hle := etaLow_le (b := b) (by linarith) hκ hE
  have hσ0 : 0 < sigmaPlus b := by
    rw [sigmaPlus, kPlus]; exact div_pos (by nlinarith) hb0
  have hD : transportD0 b E = sigmaPlus b / (2 * etaZ b E ^ 2) := by
    rw [sigmaPlus_eq b E hb0 h1 h2]; field_simp
  have hgap := (LawClauses.norm_sigmaMinus_lt_sigmaPlus hb0 hb h1 h2 hs).le
  have hD' : |transportD0 b E| ≤ sigmaPlus b / (2 * etaLow b κ ^ 2) := by
    rw [hD, abs_of_pos (by positivity)]
    gcongr
  have hq : (3 / (2 * etaZ b E)) ^ 2 ≤ (3 / (2 * etaLow b κ)) ^ 2 := by
    gcongr
  unfold mainConst mainConstL
  have : ‖sigmaMinus b E s‖ * (3 / (2 * etaZ b E)) ^ 2 ≤
      sigmaPlus b * (3 / (2 * etaLow b κ)) ^ 2 :=
    mul_le_mul hgap hq (by positivity) hσ0.le
  linarith

theorem mainConstL_nonneg {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    0 ≤ mainConstL b κ := by
  have hηL := etaLow_pos (b := b) (by linarith) hκ
  have hσ0 : 0 < sigmaPlus b := by
    rw [sigmaPlus, kPlus]; exact div_pos (by nlinarith) hb0
  unfold mainConstL; positivity

/-- Bulk-uniform `passiveCovariance_of_domain` (the off-domain argument). -/
theorem passiveCovariance_of_domain_bulk (hdom : PassiveCovarianceOnDomainBulk)
    (hfl : PassiveFluctuationL2Bulk) : PassiveCovarianceBulk := by
  intro b hb0 hb κ hκ
  obtain ⟨d, C, W₀, hd, hC⟩ := hdom b hb0 hb κ hκ
  obtain ⟨C₁, W₁, hC₁, hcr⟩ := crudeCovariance_of_fluctuation_bulk hfl b hb0 hb κ hκ
  have hm0 : 0 ≤ mainConstL b κ := mainConstL_nonneg hb0 hb hκ
  set K := C₁ + mainConstL b κ with hKdef
  refine ⟨max C 0 + K / d, max (max W₀ W₁) 1, fun W hW E hEκ s hs X hX v₁ v₂ v₃ v₄ => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hW0 : W₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWpos : (0 : ℝ) < W := by
    have : 1 ≤ W := le_trans (le_max_right _ _) hW
    exact_mod_cast this
  set δ := jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W with hδ
  have hδ0 : 0 ≤ δ := by
    have := passiveMass_nonneg b E hX
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    positivity
  have hF := fourNorm_nonneg v₁ v₂ v₃ v₄
  set F := fourNorm v₁ v₂ v₃ v₄
  have hB : 0 ≤ (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ := by positivity
  have hK0 : 0 ≤ K / d := by positivity
  show ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
      mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤ (max C 0 + K / d) * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ) * F
  by_cases hin : δ ≤ d
  · refine (hC W hW0 E hEκ s hs X hX hin v₁ v₂ v₃ v₄).trans ?_
    have : C ≤ max C 0 + K / d := le_trans (le_max_left _ _) (le_add_of_nonneg_right hK0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hB) hF
  · have hout : d < δ := lt_of_not_ge hin
    have h1' := hcr W hW1 E hEκ X hX v₁ v₂ v₃ v₄
    have h2' := norm_mainTensor_le hb0 hb h1 h2 s hX v₁ v₂ v₃ v₄
    have hmc : mainConst b E s / W * F ≤ mainConstL b κ / W * F :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (mainConst_le_bulk hb0 hb hκ hEκ hs) hWpos.le) hF
    have htri : ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
        mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤ K / W * F := by
      refine (norm_sub_le _ _).trans ?_
      have : K / W * F = C₁ / W * F + mainConstL b κ / W * F := by rw [hKdef]; ring
      linarith
    refine htri.trans ?_
    have hKd : K / W ≤ K / d * ((W : ℝ)⁻¹ * δ) := by
      have hK : 0 ≤ K := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hd, div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_left hout.le (mul_nonneg hK (inv_nonneg.mpr hWpos.le))
      linarith
    have hstep : K / d * ((W : ℝ)⁻¹ * δ) ≤ (max C 0 + K / d) * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ) := by
      have h3 : 0 ≤ (W : ℝ)⁻¹ * δ := by positivity
      have h4 : 0 ≤ (W : ℝ)⁻¹ ^ 2 := by positivity
      have h5 : 0 ≤ max C 0 := le_max_right _ _
      nlinarith
    exact mul_le_mul_of_nonneg_right (hKd.trans hstep) hF

/-- Bulk-uniform `passiveCovariance_holds_of_normalized`. -/
theorem passiveCovariance_holds_of_normalized_bulk (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hN : PassiveCovarianceNormalizedBulk) : PassiveCovarianceBulk := by
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  exact passiveCovariance_of_domain_bulk
    (passiveCovarianceOnDomain_of_strict_bulk hA (strict_of_normalized_bulk hN))
    (passiveFluctuationL2_of_passiveBounds_bulk hA)

/-- Bulk-uniform `passiveCovariance_holds_of_match`. -/
theorem passiveCovariance_holds_of_match_bulk (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hM : MeansMatchMainBulk) :
    PassiveCovarianceBulk :=
  passiveCovariance_holds_of_normalized_bulk hGA hLp
    (normalized_of_match_bulk hP (PassiveLayer.passiveBounds_holds hGA hLp) hM)

/-- Bulk-uniform `passiveCovariance_holds_of_alp`. -/
theorem passiveCovariance_holds_of_alp_bulk (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hα : MeanNearBulk alpFam leadAlp)
    (hQ : MeanNearBulk alpFamI leadAlpI) : PassiveCovarianceBulk :=
  passiveCovariance_holds_of_match_bulk hGA hLp hP
    (meansMatchMain_of_alp_bulk (PassiveLayer.passiveBounds_holds hGA hLp) hα hQ)

/-- **The bulk-uniform passive covariance bound** (`PassiveCovarianceBulk`), from the input
hypotheses `GaussianAbsorptionContract`, `GaussianLpGradient`, `GaussianPoincare` only.
-/
theorem passiveCovarianceBulk_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) : PassiveCovarianceBulk :=
  passiveCovariance_holds_of_alp_bulk hGA hLp hP
    (alpNear_holds_bulk (PassiveLayer.passiveBounds_holds hGA hLp))
    (alpINear_holds_bulk (PassiveLayer.passiveBounds_holds hGA hLp))

end BlockBand.Transmission.CovarianceBulk
