module

public import BlockBand.SourceProcess.ContractingWords.DeltaRefined
public import BlockBand.SourceProcess.FullSource.EstimatesHolds
public import BlockBand.SourceProcess.FullSource.DeltaHolds
public import BlockBand.SourceProcess.FullSourceCovariance.WardTensor

/-!
# The exact Ward mean `E𝓔 = Ω P𝕊 + Ω' 𝕊*P + O(δ₀² + W⁻²)`

`wardMean_refined`: at one fresh layer and every Hermitian old two-port, the mean of the Ward noise
`𝓔 = NN* - I` is `Ω P𝕊 + Ω' 𝕊*P` up to `O(δ₀² + W⁻²)`, with `|Ω|, |Ω'| ≤ C(δ₀ + W⁻²)`, uniformly on
the bulk.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSource BlockBand.Transmission BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator ComplexConjugate

variable {W : ℕ}

/-- `wardOf (m·I) F` with `ιF = -c₀P𝕊`. -/
theorem wardOf_smul_one (b E : ℝ) (hη : etaZ b E ≠ 0)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (m : ℂ) :
    wardOf (m • (1 : Matrix (Fin W) (Fin W) ℂ)) (wardF b E XX) =
      (-(m * cZero b E)) • (nearProjection W * twoPortScattering b E XX) +
        (star m * cZero b E) • ((twoPortScattering b E XX)ᴴ * nearProjection W) := by
  have h1 := FullSourceCovariance.iota_wardF b E hη XX
  have h2 := FullSourceCovariance.iota_wardF_conj b E hη XX
  have h3 : (wardF b E XX)ᴴ * nearSel W = ((nearSel W)ᴴ * wardF b E XX)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have t1 : (nearSel W)ᴴ * (m • (1 : Matrix (Fin W) (Fin W) ℂ) * wardF b E XX) =
      (-(m * cZero b E)) • (nearProjection W * twoPortScattering b E XX) := by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, h1, smul_smul, mul_neg]
  have t2 : (m • (1 : Matrix (Fin W) (Fin W) ℂ) * wardF b E XX)ᴴ * nearSel W =
      (star m * cZero b E) • ((twoPortScattering b E XX)ᴴ * nearProjection W) := by
    rw [Matrix.smul_mul, Matrix.one_mul, conjTranspose_smul, Matrix.smul_mul, h3, h2, smul_smul]
  rw [wardOf, t1, t2]

/-- `|⟨EΔ⟩| ≤ ‖EΔ‖ ≤ C(δ₀ + W⁻²)` for every passive `X`. -/
theorem deltaMean_all (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤
          C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
  intro b hb0 hb κ hκ
  obtain ⟨d₀, hd₀, C, W₀, hC⟩ := deltaMean_holds hGA hLp b hb0 hb κ hκ
  obtain ⟨CI, W₁, hCI, hI⟩ := delta_integrable hGA b hb0 hb κ hκ
  refine ⟨max C 0 + CI / d₀, max W₀ W₁, by positivity, fun W hW E hE X hY => ?_⟩
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans hW
  have hW1 : W₁ ≤ W := (le_max_right _ _).trans hW
  set δ := jetDistance0 b E X
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hw0 : 0 ≤ ((W : ℝ)⁻¹) ^ 2 := by positivity
  by_cases hd : δ ≤ d₀
  · refine (hC W hW0 E hE X hY hd).trans ?_
    have := mul_le_mul_of_nonneg_right (le_max_left C 0) (add_nonneg hδ0 hw0)
    have : 0 ≤ CI / d₀ * (δ + ((W : ℝ)⁻¹) ^ 2) := by positivity
    nlinarith
  · replace hd := not_le.mp hd
    have h1 : CI ≤ CI / d₀ * δ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd₀]
      exact mul_le_mul_of_nonneg_left hd.le hCI
    have : 0 ≤ max C 0 * (δ + ((W : ℝ)⁻¹) ^ 2) :=
      mul_nonneg (le_max_right _ _) (add_nonneg hδ0 hw0)
    have : CI / d₀ * δ ≤ CI / d₀ * (δ + ((W : ℝ)⁻¹) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [(hI W hW1 E hE X hY).2]

/-- **The exact Ward mean** (one fresh layer, every Hermitian `𝕏`). -/
theorem wardMean_refined (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        ∃ Ω Ω' : ℂ,
          ‖Ω‖ ≤ C * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2) ∧
          ‖Ω'‖ ≤ C * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2) ∧
          ‖matrixExpect (freshLaw W b) (wardNoise b E XX) -
              (Ω • (nearProjection W * twoPortScattering b E XX) +
                Ω' • ((twoPortScattering b E XX)ᴴ * nearProjection W))‖ ≤
            C * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) ^ 2 + ((W : ℝ)⁻¹) ^ 2) := by
  intro b hb0 hb κ hκ
  obtain ⟨C1, W1, hC1, hR⟩ := deltaMean_refined hGA hLp b hb0 hb κ hκ
  obtain ⟨C2, W2, hC2, hM⟩ := deltaMean_all hGA hLp b hb0 hb κ hκ
  obtain ⟨CI, W3, hCI, hI⟩ := delta_integrable hGA b hb0 hb κ hκ
  have hη₀ : 0 < (1 - b) * κ / 4 := by have : 0 < 1 - b := by linarith
                                       positivity
  set CF := ((1 - b) * κ / 4)⁻¹ + (2 * ((1 - b) * κ / 4))⁻¹
  have hCF : 0 ≤ CF := by positivity
  refine ⟨C2 * CF + 2 * C1 * CF, max (max W1 W2) (max W3 1), by positivity,
    fun W hW E hE XX hXX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW3, hW1'⟩ := hW
  set X := nearSchur (boundaryZ b E) XX
  obtain ⟨hη, hY, hF, hEw⟩ := ward_setup hb0 hb hκ hE hW1' hXX
    (fun hY => (hI W hW3 E hE X hY).1)
  set D := matrixExpect (freshLaw W b) (freshDelta b E X)
  set m := avgTr D
  have hc0 : ‖cZero b E‖ ≤ CF := by
    have hge := FullSource.etaZ_ge hb0 hb hκ hE
    have e : ‖cZero b E‖ = (2 * etaZ b E)⁻¹ := by
      rw [cZero, norm_inv, norm_mul, norm_mul, Complex.norm_two, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg hη.le]
    rw [e]
    have : (2 * etaZ b E)⁻¹ ≤ (2 * ((1 - b) * κ / 4))⁻¹ := inv_anti₀ (by positivity) (by linarith)
    have : 0 ≤ ((1 - b) * κ / 4)⁻¹ := by positivity
    linarith
  have hm : ‖m‖ ≤ C2 * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) :=
    (norm_avgTr_le hW1' D).trans (hM W hW2 E hE X hY)
  have hx : 0 ≤ jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2 := by
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    positivity
  have hx2 : 0 ≤ jetDistance0 b E X ^ 2 + ((W : ℝ)⁻¹) ^ 2 := by positivity
  have hΩ : ‖m * cZero b E‖ ≤ (C2 * CF + 2 * C1 * CF) *
      (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
    rw [norm_mul]
    have := mul_le_mul hm hc0 (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hC1 hCF) hx]
  refine ⟨-(m * cZero b E), star m * cZero b E, by rw [norm_neg]; exact hΩ,
    by rw [norm_mul, norm_star, ← norm_mul]; exact hΩ, ?_⟩
  rw [hEw, ← wardOf_smul_one b E hη.ne' XX m, wardOf_sub]
  refine (norm_wardOf_le _ _).trans ?_
  have := mul_le_mul (hR W hW1 E hE X hY) hF (norm_nonneg _) (by positivity)
  nlinarith [mul_nonneg (mul_nonneg hC2 hCF) hx2]

end BlockBand.SourceProcess.ContractingWords
