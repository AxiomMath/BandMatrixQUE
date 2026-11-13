module

public import BlockBand.SourceProcess.ContractingWords.SlotCovMain
public import BlockBand.SourceProcess.ContractingWords.WardRefined

/-!
# The means of the ordinary slots at one fresh layer

Measure `freshLaw W b`; deterministic Hermitian `𝕏`; `e = layerErr`; hypothesis `ProjGammaMean`.
`slot_mean`: the means of the transported separators `I` and `P` are expanded to second order in the
error scale `e`: with `C, W₀` from `b, κ`, there are `Ω, Ω'` with `|Ω|, |Ω'| ≤ Ce` and
* `‖E[NN*] - I - (ΩP𝕊 + Ω'𝕊*P)‖ ≤ Ce²` (`wardMean_refined`);
* `‖E[NPN*] - P - (ΩP𝕊P + Ω'P𝕊*P - (D₀g/2W)P)‖ ≤ C(1+g)e²` (`NPN* = P(NN*)P - projGamma`,
  `ProjGammaMean`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.PassiveCovariance
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

theorem norm_proj_sandwich_le (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ‖nearProjection W * M * nearProjection W‖ ≤ ‖M‖ := by
  have h1 := norm_mul_le (nearProjection W * M) (nearProjection W)
  have h2 := norm_mul_le (nearProjection W) M
  have hP := norm_nearProjection_le (W := W)
  have := norm_nonneg M
  calc _ ≤ ‖nearProjection W‖ * ‖M‖ * ‖nearProjection W‖ :=
        h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ ≤ 1 * ‖M‖ * 1 := by gcongr
    _ = ‖M‖ := by ring

/-- **The slot means.** -/
theorem slot_mean (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hΓM : ProjGammaMean) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∃ Ω Ω' : ℂ, ‖Ω‖ ≤ C * layerErr b E s XX ∧ ‖Ω'‖ ≤ C * layerErr b E s XX ∧
        ‖matrixExpect (freshLaw W b) (transportedSep b E XX .id) - 1 -
            (Ω • (nearProjection W * twoPortScattering b E XX) +
              Ω' • ((twoPortScattering b E XX)ᴴ * nearProjection W))‖ ≤
          C * layerErr b E s XX ^ 2 ∧
        ‖matrixExpect (freshLaw W b) (transportedSep b E XX .proj) - nearProjection W -
            (Ω • (nearProjection W * twoPortScattering b E XX * nearProjection W) +
              Ω' • (nearProjection W * (twoPortScattering b E XX)ᴴ * nearProjection W) -
              ((transportD0 b E *
                conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) /
                  (2 * W) : ℝ) : ℂ) • nearProjection W)‖ ≤
          C * (1 + conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))) *
            layerErr b E s XX ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hw⟩ := wardMean_refined hGA hLp b hb0 hb κ hκ
  obtain ⟨C₂, W₂, hC₂, hm⟩ := hΓM b hb0 hb κ hκ
  obtain ⟨μb, W₃, -, hfb⟩ := fresh_basic hGA hb0 hb hκ
  refine ⟨2 * C₁ + 3 * C₂, max (max W₁ W₂) (max W₃ 1), by positivity, ?_⟩
  intro W hW E hE s hs XX hXX
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW3, hW4⟩ := hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  obtain ⟨hδ0, hδe, hge, hWe, he0, hsum⟩ := layerErr_parts b E s XX hg (W := W)
  set g := conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))
  set δ₀ := jetDistance0 b E (nearSchur (boundaryZ b E) XX)
  set e := layerErr b E s XX
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW4
  have hWi : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWr
  have hW2e : ((W : ℝ)⁻¹) ^ 2 ≤ e := by nlinarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) W)]
  have hW2e2 : ((W : ℝ)⁻¹) ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ (by positivity) hWe 2
  have hδ2 : δ₀ ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hδ0 hδe 2
  obtain ⟨Ω, Ω', hΩ, hΩ', hR⟩ := hw W hW1 E hE XX hXX
  have hT := fun σ => (hfb W hW3 E hE XX hXX σ).1
  refine ⟨Ω, Ω', hΩ.trans (by nlinarith), hΩ'.trans (by nlinarith), ?_, ?_⟩
  · rw [matrixExpect_sub_one (hT .id)]
    exact hR.trans (by nlinarith)
  · have hG := matrixExpect_projGamma (hT .id) (hT .proj)
    have hΓb := hm W hW2 E hE s hs XX hXX
    simp only at hΓb
    set P := nearProjection W
    set S := twoPortScattering b E XX
    set R := matrixExpect (freshLaw W b) (wardNoise b E XX) - (Ω • (P * S) + Ω' • (Sᴴ * P))
      with hRdef
    have hEw : matrixExpect (freshLaw W b) (wardNoise b E XX) =
        matrixExpect (freshLaw W b) (transportedSep b E XX .id) - 1 :=
      (matrixExpect_sub_one (hT .id)).symm
    have hPP : P * P = P := BlockBand.Transmission.Bridge.nearProjection_mul_self
    have hEP : matrixExpect (freshLaw W b) (transportedSep b E XX .proj) =
        P * matrixExpect (freshLaw W b) (transportedSep b E XX .id) * P -
          matrixExpect (freshLaw W b) (projGamma b E XX) := by rw [hG]; abel
    have e1 : matrixExpect (freshLaw W b) (transportedSep b E XX .proj) - P -
        (Ω • (P * S * P) + Ω' • (P * Sᴴ * P) - ((transportD0 b E * g / (2 * W) : ℝ) : ℂ) • P) =
        P * R * P - (matrixExpect (freshLaw W b) (projGamma b E XX) -
          ((transportD0 b E * g / (2 * W) : ℝ) : ℂ) • P) := by
      have h1 : P * 1 * P = P := by rw [Matrix.mul_one, hPP]
      have h2 : P * (P * S) * P = P * S * P := by rw [← Matrix.mul_assoc, hPP]
      have h3 : P * (Sᴴ * P) * P = P * Sᴴ * P := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hPP, ← Matrix.mul_assoc]
      rw [hEP, hRdef, hEw]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, h1, h2, h3]
      abel
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    have h1 := (norm_proj_sandwich_le R).trans hR
    have hgW : g / W * (δ₀ + jetDistance1 b E s (nearSchur (boundaryZ b E) XX) + g / W) ≤ e ^ 2 := by
      have hd1 : 0 ≤ jetDistance1 b E s (nearSchur (boundaryZ b E) XX) := norm_nonneg _
      have : δ₀ + jetDistance1 b E s (nearSchur (boundaryZ b E) XX) + g / W ≤ e := by
        simp only [e, layerErr]; linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) W)]
      have hgw : 0 ≤ g / W := div_nonneg hg (Nat.cast_nonneg _)
      rw [sq]; exact mul_le_mul hge this (by linarith) he0
    have hgW2 : g * ((W : ℝ)⁻¹) ^ 2 ≤ g * e ^ 2 := mul_le_mul_of_nonneg_left hW2e2 hg
    calc _ ≤ C₁ * (δ₀ ^ 2 + ((W : ℝ)⁻¹) ^ 2) + C₂ * (δ₀ ^ 2 + g * ((W : ℝ)⁻¹) ^ 2 +
          g / W * (δ₀ + jetDistance1 b E s (nearSchur (boundaryZ b E) XX) + g / W)) :=
          add_le_add h1 hΓb
      _ ≤ C₁ * (2 * e ^ 2) + C₂ * (e ^ 2 + g * e ^ 2 + e ^ 2) := by gcongr; linarith
      _ ≤ _ := by nlinarith [sq_nonneg e, mul_nonneg hg (sq_nonneg e)]

end BlockBand.SourceProcess.ContractingWords
