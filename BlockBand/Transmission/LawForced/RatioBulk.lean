module

public import BlockBand.Transmission.LawForced.RatioPB
public import BlockBand.Transmission.Generator.LayerBulk

/-!
# The `κ ≡ 0` one-layer `F_z` drift, bulk-uniform

**`ratio_layer_bulk hGA hLp hP`**: `b ∈ (0,1/2)`, `κ_I > 0` and a chamber point `z` first; then
`K ≥ 0, W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ_I`, every stationary jet `s` at `E`, every
deterministic passive `X` and every `u`:
`|E F_z(T(X₊)) − F_z(T) − ratioDrift D₀ E 0 u z μ_T/W| ≤ K·ratioP(X)²⁷·W^{-3/2}`.
Inputs: `oneStepFluctuation_bulk` (`p = 3, 9`), `ubarMean_bulk`, PCB's
`passiveCovarianceBulk_holds hGA hLp hP`, `ml_integrable_U_bulk`, `freshU_sq_integrable_bulk`,
`norm_sigmaMinus_lt_sigmaPlus`, `transportD0_le_bulk`, `mass_le_bulk`; then `ratio_layer_P`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.PathScalar
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {p : ℕ}

/-- **The `κ ≡ 0` one-layer `F_z` drift, bulk-uniform.** -/
theorem ratio_layer_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    {z : DualCoord p} (hz : z ∈ dualChamber p) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → ∀ u : ℝ,
        |∫ ω, transmissionRatio z.1 z.2
            (traceMeasure (passiveTransmission b E (freshSchur E X ω))) ∂freshLaw W b -
          transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E X)) -
          ratioDrift (transportD0 b E) E (fun _ => 0) u z
            (traceMeasure (passiveTransmission b E X)) / W| ≤
        K * (ratioP b E s X ^ 27 * (Real.sqrt W)⁻¹ ^ 3) := by
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨C3, W3, hC3⟩ := oneStepFluctuation_bulk hA hb0 hb hκ ((3 : ℕ) : ℝ) (by norm_num)
  obtain ⟨C9, W9, hC9⟩ := oneStepFluctuation_bulk hA hb0 hb hκ ((9 : ℕ) : ℝ) (by norm_num)
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
  set Cb := max (max C3 C9) 0
  set K := ratioKP z Cb Cσ Cε Cu CD cq
  refine ⟨max K 0, max (max (max W3 W9) (max Wu Wc)) (max (max Wi W2) 1), le_max_right _ _,
    fun W hW E hE s hs X hX u => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW3, hW9⟩, hWu, hWc⟩, ⟨hWi, hW2⟩, hW1⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  obtain ⟨hUa, hwm⟩ := hUB W hWu E hE X hX
  obtain ⟨-, hDC⟩ := transportD0_le_bulk hb0 (by linarith) hκ hE
  have hσm : ‖sigmaMinus b E s‖ ≤ Cσ :=
    (LawClauses.norm_sigmaMinus_lt_sigmaPlus hb0 hb h1 h2 hs).le
  have hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance (freshLaw W b) (freshU b E X)
      v₁ v₂ v₃ v₄ - ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
        (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - passiveTransmission b E X) +
          crossedTensor v₁ v₂ v₃ v₄ (1 - passiveTransmission b E X) 1) +
        sigmaMinus b E s / W * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X) (passiveF b E X) +
        conj (sigmaMinus b E s) / W *
          crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X)ᴴ (passiveF b E X)ᴴ)‖ ≤
      Cε * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X +
        passiveMass b E X / W)) * fourNorm v₁ v₂ v₃ v₄ := fun v₁ v₂ v₃ v₄ => by
    refine (hcovB W hWc E hE s hs X hX v₁ v₂ v₃ v₄).trans ?_
    have hF := fourNorm_nonneg v₁ v₂ v₃ v₄
    have hA0 : 0 ≤ (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X +
        passiveMass b E X / W) := by
      have := passiveMass_nonneg b E hX
      have : 0 ≤ jetDistance0 b E X := norm_nonneg _
      have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hA0) hF
  have hB : ∀ k : ℕ, (k = 3 ∨ k = 9) → ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u
      (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)) v)
      (ENNReal.ofReal (k : ℝ)) (freshLaw W b) ≤
      ENNReal.ofReal (Cb / Real.sqrt W * vecNorm u * vecNorm v) := by
    intro k hk u v
    have mono : ∀ Cx : ℝ, Cx ≤ Cb → ENNReal.ofReal (Cx / Real.sqrt W * vecNorm u * vecNorm v) ≤
        ENNReal.ofReal (Cb / Real.sqrt W * vecNorm u * vecNorm v) := fun Cx hCx =>
      ENNReal.ofReal_le_ofReal (by
        have := vecNorm_nonneg u; have := vecNorm_nonneg v
        have : Cx / Real.sqrt W ≤ Cb / Real.sqrt W :=
          div_le_div_of_nonneg_right hCx (Real.sqrt_nonneg _)
        gcongr)
    rcases hk with rfl | rfl
    · exact ((hC3 W hW3 E hE X hX u v).1).trans
        (mono C3 ((le_max_left _ _).trans (le_max_left _ _)))
    · exact ((hC9 W hW9 E hE X hX u v).1).trans
        (mono C9 ((le_max_right _ _).trans (le_max_left _ _)))
  have hq : passiveMass b E X ≤ cq * (passiveTransmission b E X).trace.re :=
    mass_le_bulk (by linarith) hκ hE hX
  have hcq : 0 ≤ cq := by positivity
  have hpt := ratio_layer_P hz hb0 hb hW1 h1 h2 hX (hUi W hWi E hE X hX) (hU2 W hW2 E hE X hX)
    (le_max_right _ _) hB s (sigmaMinus b E s) hσm (le_max_right _ _) hcov hCu hUa hwm hDC
    hcq hq u
  refine hpt.trans (mul_le_mul_of_nonneg_right (le_max_left K 0) ?_)
  have : 0 ≤ (Real.sqrt W)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hP1 := (ratio_atoms hb0 hb h1 h2 hW1 hX s hcq hq).1
  have : 0 ≤ ratioP b E s X := by linarith
  positivity

end BlockBand.Transmission.LawForced
