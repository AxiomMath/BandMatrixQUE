module

public import BlockBand.Transmission.Generator.StepLayer
public import BlockBand.Transmission.Generator.LayerAlg
public import BlockBand.Transmission.PassiveCovarianceBulk.Holds
public import BlockBand.Transmission.LawClauses.JetGap

/-!
# The `k = j + 2` one-layer drift, bulk-uniform

**`layer_bulk hGA hLp hP`**: `b ∈ (0,1/2)`, `κ > 0`, `j` first; then `K ≥ 0, W₀`; for
`W ≥ W₀`, `E ∈ bulkInterval κ`, every stationary jet `s` at `E` and every deterministic passive
`X` (`Y ⪰ 0`), with `T = T(X)`, `g = Tr T`, `e = δ₀ + W⁻²`, `δ₁ = jetDistance1 b E s X`,
`τ = layerTau`:
`|E Re Tr T(X₊)^{j+2} - Re Tr T^{j+2} - A_{j+2}(P)/W| ≤ K·layerErr g e δ₁ τ √W`.

Inputs: `hs_moments_bulk`, `ubarMean_bulk` (`U_a = C_u(e + q/W)`), PCB's
`passiveCovarianceBulk_holds hGA hLp hP` (`ε = C⁺(W⁻² + W⁻¹(δ₀ + δ₁ + q/W))`),
`ml_integrable_U_bulk`, `freshU_sq_integrable_bulk`; `|σ₋| < σ₊`
(`norm_sigmaMinus_lt_sigmaPlus`), `D₀ = σ₊/(2η²) ≤ σ₊/(2η_κ²)` (`sigmaPlus_eq`), `q = g/(4η)`.
Then `layer_point` and `layer_rhs_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.PathScalar
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- `g = 4η q`. -/
theorem trace_passiveTransmission_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    (passiveTransmission b E X).trace.re = 4 * etaZ b E * passiveMass b E X := by
  rw [passiveTransmission, trace_smul, smul_eq_mul, Complex.re_ofReal_mul, passiveMass]

/-- `q ≤ (4η_κ)⁻¹ g` on the bulk. -/
theorem mass_le_bulk {b κ E : ℝ} (hb : b < 1) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    passiveMass b E X ≤ (4 * etaLow b κ)⁻¹ * (passiveTransmission b E X).trace.re := by
  have hL := etaLow_pos hb hκ
  have hLe := etaLow_le hb hκ hE
  have hq := passiveMass_nonneg b E hX
  rw [trace_passiveTransmission_eq, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  nlinarith

/-- `0 ≤ D₀ ≤ σ₊/(2η_κ²)` on the bulk. -/
theorem transportD0_le_bulk {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) :
    0 ≤ transportD0 b E ∧ transportD0 b E ≤ sigmaPlus b / (2 * etaLow b κ ^ 2) := by
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hD : 0 ≤ transportD0 b E := by
    have : 0 < 4 - E ^ 2 := by nlinarith
    unfold transportD0; positivity
  refine ⟨hD, ?_⟩
  have hL := etaLow_pos hb hκ
  have hLe := etaLow_le hb hκ hE
  have hσ := sigmaPlus_eq b E hb0 h1 h2
  rw [le_div_iff₀ (by positivity), hσ]
  have : etaLow b κ ^ 2 ≤ etaZ b E ^ 2 := pow_le_pow_left₀ hL.le hLe 2
  nlinarith

/-- **The `k = j + 2` one-layer drift, bulk-uniform.** -/
theorem layer_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (j : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef →
        |∫ ω, ((passiveTransmission b E (freshSchur E X ω)) ^ (j + 2)).trace.re ∂freshLaw W b -
            ((passiveTransmission b E X) ^ (j + 2)).trace.re -
            transmissionDrift (transportD0 b E) (j + 2)
              (fun m => ((passiveTransmission b E X) ^ m).trace.re) / W| ≤
          K * layerErr (passiveTransmission b E X).trace.re
            (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) (jetDistance1 b E s X) (layerTau b E X)
            (Real.sqrt W) := by
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨Cb, Wb, hCb, hmomB⟩ := hs_moments_bulk hA hb0 hb hκ
  obtain ⟨Cu, Wu, hCu, hUB⟩ := ubarMean_bulk hA hb0 hb hκ
  obtain ⟨Cc, Wc, hcovB⟩ := CovarianceBulk.passiveCovarianceBulk_holds hGA hLp hP b hb0 hb κ hκ
  obtain ⟨Wi, hUi⟩ := ml_integrable_U_bulk hA hb0 hb hκ
  obtain ⟨W2, hU2⟩ := freshU_sq_integrable_bulk hA hb0 hb hκ
  set ηL := etaLow b κ
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ
  set cq := (4 * ηL)⁻¹
  set CD := sigmaPlus b / (2 * ηL ^ 2)
  set Cσ := sigmaPlus b
  set Cε := max Cc 0
  have hσ0 : 0 ≤ Cσ := by
    simp only [Cσ, sigmaPlus, kPlus]; have : 0 ≤ (1 - b) ^ 2 := sq_nonneg _
    have e : 1 - 2 * b + b ^ 2 = (1 - b) ^ 2 := by ring
    rw [e]; positivity
  refine ⟨layerK j cq CD Cb Cu Cu Cε Cσ, max (max (max Wb Wu) (max Wc Wi)) (max W2 1),
    layerK_nonneg j (by positivity) hCb hCu hCu (le_max_right _ _) hσ0,
    fun W hW E hE s hs X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWb, hWu⟩, hWc, hWi⟩, hW2, hW1⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hT : (passiveTransmission b E X).PosSemidef :=
    passiveTransmission_posSemidef (by linarith) h1 h2 hX
  set g := (passiveTransmission b E X).trace.re
  set δ := jetDistance0 b E X
  set d := jetDistance1 b E s X
  set q := passiveMass b E X
  have hg : 0 ≤ g := (mm_trace_posSemidef hT).1
  have hδ : 0 ≤ δ := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hq0 : 0 ≤ q := passiveMass_nonneg b E hX
  have hτ : 0 ≤ layerTau b E X := by
    unfold layerTau hsSandwich; positivity
  obtain ⟨hUa, hwm⟩ := hUB W hWu E hE X hX
  obtain ⟨hD0, hDC⟩ := transportD0_le_bulk hb0 (by linarith) hκ hE
  have hσm : ‖sigmaMinus b E s‖ ≤ Cσ := (LawClauses.norm_sigmaMinus_lt_sigmaPlus hb0 hb h1 h2 hs).le
  have hWpos : (0 : ℝ) < W := by linarith
  have hσW : ‖sigmaMinus b E s / W‖ ≤ Cσ / W := by
    rw [norm_div, Complex.norm_natCast]; exact div_le_div_of_nonneg_right hσm hWpos.le
  have hσW' : ‖conj (sigmaMinus b E s) / W‖ ≤ Cσ / W := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_conj]
    exact div_le_div_of_nonneg_right hσm hWpos.le
  set εv := Cε * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (δ + d + q / W))
  have hεv : 0 ≤ εv := by positivity
  have hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance (freshLaw W b) (freshU b E X)
      v₁ v₂ v₃ v₄ - ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
        (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - passiveTransmission b E X) +
          crossedTensor v₁ v₂ v₃ v₄ (1 - passiveTransmission b E X) 1) +
        sigmaMinus b E s / W * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X) (passiveF b E X) +
        conj (sigmaMinus b E s) / W *
          crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X)ᴴ (passiveF b E X)ᴴ)‖ ≤
      εv * fourNorm v₁ v₂ v₃ v₄ := fun v₁ v₂ v₃ v₄ => by
    refine (hcovB W hWc E hE s hs X hX v₁ v₂ v₃ v₄).trans ?_
    have hF := fourNorm_nonneg v₁ v₂ v₃ v₄
    have hA0 : 0 ≤ (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (δ + d + q / W) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hA0) hF
  have hpt := layer_point hb0 hb h1 h2 hW1 hX (hUi W hWi E hE X hX) (hU2 W hW2 E hE X hX)
    (hmomB W hWb E hE X hX) (sigmaMinus b E s) hεv hcov hUa hwm j
  refine hpt.trans ?_
  have hmax : max Cu 0 = Cu := max_eq_left hCu
  rw [hmax]
  have hs1 : 1 ≤ Real.sqrt W := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hWr
  exact layer_rhs_le j hg hδ hd hτ hs1 (Real.sq_sqrt hWpos.le) hq0
    (mass_le_bulk (by linarith) hκ hE hX) (by positivity) hD0 hDC hCb hCu hCu
    (le_max_right _ _) hσ0 (by positivity) le_rfl le_rfl hσW hσW'

end BlockBand.Transmission.Generator
