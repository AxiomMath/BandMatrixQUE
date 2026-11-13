module

public import BlockBand.SourceProcess.ContractingWords.LayerCombi
public import BlockBand.SourceProcess.ContractingWords.LiftL2
public import BlockBand.SourceProcess.ContractingWords.LiftIdentify
public import BlockBand.SourceProcess.ContractingWords.DecayAll
public import BlockBand.SourceProcess.ContractingWords.AliveLetters
public import BlockBand.SourceProcess.FullSourceStops.PolyEval

/-!
# Path-form preliminaries for the ordinary drift step

Comparison of the one-layer error with the path error, and the polynomial value along the path in
`coreProd` form. They are used in the proof of
**`ordinaryDriftStepAll_of hMT hGA hLp hSR hLD : OrdinaryDriftStepAll`**, which goes as follows.
At a step `εW ≤ j`,
`j ≠ k_a`, `j + 1 ≤ TW` (births anywhere else), on `A = {j < σ_K}`:
1. `E_j[1_AΔ_w] = 1_A ∫(new w - old w) dfresh` (`condExp_alive_eq`, `ae_wordInc_eq`);
2. the letters at `j` are Hermitian with `Tr|A_ℓ| ≤ K` before the stop (`nuclearNorm_letter_le`),
   `𝕏_j` is Hermitian, old word values are `coreProd` values (`ae_step_state'`), so `LayerDrift`
   gives, pointwise on `A`, `|E_j[1_AΔ_w] - W⁻¹(drift + inj)| ≤ C₁ e_j Σ_{Z∈contrDrift w}|1_A Z_j| +
   C₁(W^{-3/2} + e_j² + e_j^{2d+4})`, with `e_j` the path error (`pathErr`, `layerErr ≤ pathErr`);
3. `L²`: Hölder `‖e_j|1_AZ_j|‖₂ ≤ ‖e_j‖₄‖1_AZ_j‖₄ ≤ (C/W)·C'(ρ^{j-r_j} + W^{-1/2})` (`errMoments`,
   `decay_restart`: the contracting products decay from the last restart), `‖e_j^n‖₂ ≤ (C/W)^n`
   (`pathErr_pow_le`), at most `20d²` products (`contrDrift_length_le`).
Constants: `C = C₁·20d²·C₄C_d + C₁(1 + C₂² + C_N^{2d+4})`, `ρ` of `decay_restart` at `p = 4`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge
open scoped ENNReal

variable {W nT nI : ℕ}

theorem abs_layerErr_le_pathErr (b E : ℝ) (s : ℂ) (j : ℕ) (ω : GrowthPath W) :
    |layerErr b E s (pathXX E W j ω)| ≤ pathErr b E s W j ω := by
  have h := pathX_eq b E j ω
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have h0 : 0 ≤ jetDistance0 b E (pathX b E W j ω) := norm_nonneg _
  have h1 : 0 ≤ jetDistance1 b E s (pathX b E W j ω) := norm_nonneg _
  have hc := abs_le.mp (le_refl |pathConductance b E W j ω|)
  have hg : |conductanceOf (passiveTransmission b E (pathX b E W j ω)) / W| ≤
      |pathConductance b E W j ω| / W := by
    rw [abs_div, abs_of_nonneg hW]; rfl
  have hWi : (0 : ℝ) ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr hW
  simp only [layerErr, pathErr, ← h]
  rw [abs_le] at hg ⊢
  constructor <;> linarith [hg.1, hg.2]

theorem layerRem_mono (W d : ℕ) {e e' : ℝ} (hee : |e| ≤ e') :
    layerRem W d e ≤ layerRem W d e' := by
  unfold layerRem
  have ha := abs_nonneg e
  have h2 : e ^ 2 ≤ e' ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ ha hee 2
  have hN : e ^ (2 * d + 4) ≤ e' ^ (2 * d + 4) := by
    rw [← (show Even (2 * d + 4) from ⟨d + 2, by ring⟩).pow_abs]
    exact pow_le_pow_left₀ ha hee _
  linarith

/-- The polynomial value at `j` in `coreProd` form. -/
theorem polyValue_eq_core {b E : ℝ} {k : Fin nT → ℕ} {q : Fin nI → ℝ → ℝ} {j : ℕ}
    {ω : GrowthPath W} {S : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (h : ∀ Zs : List (TraceWord nT nI),
      productValue b E k q W j ω Zs = coreProd (letterMatrix b E k q W j ω) S Zs)
    (Φ : TracePoly nT nI) :
    polyValue b E k q W j ω Φ =
      MvPolynomial.eval (fun v => coreProd (letterMatrix b E k q W j ω) S [v]) Φ := by
  unfold polyValue
  have e : wordValue b E k q W j ω = fun v => coreProd (letterMatrix b E k q W j ω) S [v] := by
    funext v
    rw [← h [v]]
    simp [productValue]
  rw [e]

end BlockBand.SourceProcess.ContractingWords
