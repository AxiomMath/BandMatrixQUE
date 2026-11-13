module

public import BlockBand.Transmission.PassiveCovarianceBulk.GsAdj
public import BlockBand.Transmission.PassiveCovarianceBulk.TqSys
public import BlockBand.Transmission.PassiveCovariance.VSys
public import BlockBand.Transmission.PassiveCovariance.WSys
public import BlockBand.Transmission.PassiveCovariance.ZSys
public import BlockBand.Transmission.PassiveCovariance.AdjMeans

/-!
# Bulk-uniform `v_p`, `w_p`, `z_p` blocks and the adjoint means

The blocks of `E[𝒢Π𝒢ᴴP_p𝒢]`, `E[𝒢P_p𝒢Π𝒢ᴴ]` and `E[𝒢Π𝒢ᴴP_p𝒢Π𝒢ᴴ]`, and the `γ₀` means of the
`m4_p` and `z_p` systems, with constants and `W₀` uniform in `E ∈ bulkInterval κ`.
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
open BlockBand.Transmission.PathScalar (etaLow etaLow_pos etaLow_le bulk_bounds bulk_eta_le_one bulk_norm_z)
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Blocks of `E[𝒢Π𝒢ᴴP_p𝒢]`.**
Bulk-uniform copy of `vP_blocks` (constants uniform on `bulkInterval κ`). -/
theorem vP_blocks_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ r, ‖vP b E X p r‖ ≤ C) ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ *
          (bProj p * gRes b E X ω))) : LayerMat W) α β) (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))))) 0 0 -
          SourceMixing.mOf b E X * (SourceMixing.sOne b E X • blkAt (gsMean b E X p) 0 0 +
            svP b E X p • blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))))) 1 1 -
          SourceMixing.vOf b E X • ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) •
              blkAt (gsMean b E X p) 1 1 +
            ((b : ℂ) * vP b E X p 0) •
              blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedBlock_bulk hA hb0 hb hκ 2 1
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 3 1
  refine ⟨Cu + Cw, max Wu Ww, by positivity, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hWu : Wu ≤ W := le_trans (le_max_left _ _) hW
  have hWw : Ww ≤ W := le_trans (le_max_right _ _) hW
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw E hEκ X hX.posSemidef 3 le_rfl ![0, 2, 0] (dV4 p) (norm_dV4_le p)
  have hle : Cw ≤ Cu + Cw := by linarith
  refine ⟨fun r => ?_, fun α β => ?_, ?_⟩
  · have h := hwt.2.2.2.2 r
    have e : (fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2, 0]
        (dV4 p)) r) = fun ω => SourceMixing.blkTr (gRes b E X ω * (portProj *
          ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)))) r := funext fun ω => by rw [wordVal_GV]
    rw [e] at h; exact h.trans hle
  · have h := hwt.1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 2, 0] (dV4 p) α β) =
        fun ω => (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :
          LayerMat W) α β := funext fun ω => by rw [wordVal_GV]
    rw [e] at h; exact h
  have hT := hU W hWu E hEκ X hX 2 le_rfl ![2, 0] (dV p) (norm_dV_le p)
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![2, 0] (dV p)) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :=
    funext fun ω => by rw [wordVal_V]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2, 0] (dV p)) =
      fun ω => portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)) :=
    funext fun ω => by rw [wordVal_V]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 0) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordAlpha_V0]
  have e4 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 1) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :=
    funext fun ω => by rw [wordAlpha_V1]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 0) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) :=
    funext fun ω => by rw [wordGamma_V0]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 1) =
      fun ω => gRes b E X ω := funext fun ω => by rw [wordGamma_V1]
  obtain ⟨p0, p1⟩ := blkAt_expect_portProj (μ := μ)
    (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))
  rw [e1, e2, e3, e4, e5, e6, p0, p1, zero_add] at hT
  obtain ⟨hT0, hT1⟩ := hT
  have hup : Cu / (W : ℝ) ^ 2 ≤ (Cu + Cw) / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  refine ⟨hT0.trans hup, ?_⟩
  change ‖_ - SourceMixing.vOf b E X • (blkAt (gsMean b E X p) 1 1 +
    (((b : ℂ) * SourceMixing.tTwo b E X 0) • blkAt (gsMean b E X p) 1 1 +
      ((b : ℂ) * vP b E X p 0) • _))‖ ≤ _ at hT1
  have eS : ∀ (c : ℂ) (Y : Matrix (Fin W) (Fin W) ℂ), Y + c • Y = (1 + c) • Y := fun c Y => by
    rw [add_smul, one_smul]
  rw [← add_assoc, eS] at hT1
  exact hT1.trans hup

/-- **Blocks of `E[𝒢P_p𝒢Π𝒢ᴴ]`.**
Bulk-uniform copy of `wP_blocks` (constants uniform on `bulkInterval κ`). -/
theorem wP_blocks_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ r, ‖wP b E X p r‖ ≤ C) ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (bProj p * (gRes b E X ω *
          (portProj * (gRes b E X ω)ᴴ))) : LayerMat W) α β) (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) 0 0 -
          SourceMixing.mOf b E X * (xP b E X p • blkAt (tMean b E X) 0 0 +
            swP b E X p • (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) 1 1 -
          SourceMixing.vOf b E X • ((ind 1 p + (b : ℂ) * tauP b E X p 0) • blkAt (tMean b E X) 1 1 +
            ((b : ℂ) * wP b E X p 0) •
              (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedBlock_bulk hA hb0 hb hκ 2 1
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 3 1
  refine ⟨Cu + Cw, max Wu Ww, by positivity, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hWu : Wu ≤ W := le_trans (le_max_left _ _) hW
  have hWw : Ww ≤ W := le_trans (le_max_right _ _) hW
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw E hEκ X hX.posSemidef 3 le_rfl ![0, 0, 2] (dW4 p) (norm_dW4_le p)
  have hle : Cw ≤ Cu + Cw := by linarith
  refine ⟨fun r => ?_, fun α β => ?_, ?_⟩
  · have h := hwt.2.2.2.2 r
    have e : (fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 2]
        (dW4 p)) r) = fun ω => SourceMixing.blkTr (gRes b E X ω * (bProj p *
          (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)))) r := funext fun ω => by rw [wordVal_GW]
    rw [e] at h; exact h.trans hle
  · have h := hwt.1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 2] (dW4 p) α β) =
        fun ω => (gRes b E X ω * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :
          LayerMat W) α β := funext fun ω => by rw [wordVal_GW]
    rw [e] at h; exact h
  have hT := hU W hWu E hEκ X hX 2 le_rfl ![0, 2] (dW p) (norm_dW_le p)
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dW p)) =
      fun ω => gRes b E X ω * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordVal_W]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dW p)) =
      fun ω => bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)) :=
    funext fun ω => by rw [wordVal_W]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 0) =
      fun ω => gRes b E X ω * (bProj p * gRes b E X ω) :=
    funext fun ω => by rw [wordAlpha_W0]
  have e4 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 1) =
      fun ω => gRes b E X ω * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordAlpha_W1]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 0) =
      fun ω => gRes b E X ω * (portProj * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordGamma_W0]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 1) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_W1]
  rw [e1, e2, e3, e4, e5, e6, blkAt_expect_bProj, blkAt_expect_bProj, blkAt_expect_conjT,
    blkAt_expect_conjT] at hT
  obtain ⟨hT0, hT1⟩ := hT
  have hup : Cu / (W : ℝ) ^ 2 ≤ (Cu + Cw) / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  constructor
  · change ‖_ - SourceMixing.mOf b E X * (ind 0 p • blkAt (tMean b E X) 0 0 +
      (sig1 b (tauP b E X p 0) (tauP b E X p 1) • blkAt (tMean b E X) 0 0 +
        swP b E X p • _))‖ ≤ _ at hT0
    rw [← add_assoc, ← add_smul] at hT0
    exact hT0.trans hup
  · change ‖_ - SourceMixing.vOf b E X • (ind 1 p • blkAt (tMean b E X) 1 1 +
      (((b : ℂ) * tauP b E X p 0) • blkAt (tMean b E X) 1 1 +
        ((b : ℂ) * wP b E X p 0) • _))‖ ≤ _ at hT1
    rw [← add_assoc, ← add_smul] at hT1
    exact hT1.trans hup

/-- **Blocks of `E[𝒢Π𝒢ᴴP_p𝒢Π𝒢ᴴ]`.**
Bulk-uniform copy of `zP_blocks` (constants uniform on `bulkInterval κ`). -/
theorem zP_blocks_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ r, ‖zP b E X p r‖ ≤ C) ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p *
          (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) : LayerMat W) α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (portProj * ((gRes b E X ω)ᴴ * (bProj p *
              (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))))) 0 0 -
          SourceMixing.mOf b E X * (SourceMixing.sOne b E X • blkAt (gsTMean b E X p) 0 0 +
            svP b E X p • blkAt (tMean b E X) 0 0 +
            szP b E X p • (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (portProj * ((gRes b E X ω)ᴴ * (bProj p *
              (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))))) 1 1 -
          SourceMixing.vOf b E X • ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) •
              blkAt (gsTMean b E X p) 1 1 +
            ((b : ℂ) * vP b E X p 0) • blkAt (tMean b E X) 1 1 +
            ((b : ℂ) * zP b E X p 0) •
              (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedBlock_bulk hA hb0 hb hκ 3 1
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 4 1
  refine ⟨Cu + Cw, max Wu Ww, by positivity, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hWu : Wu ≤ W := le_trans (le_max_left _ _) hW
  have hWw : Ww ≤ W := le_trans (le_max_right _ _) hW
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw E hEκ X hX.posSemidef 4 le_rfl ![0, 2, 0, 2] (dZ5 p) (norm_dZ5_le p)
  have hle : Cw ≤ Cu + Cw := by linarith
  refine ⟨fun r => ?_, integrable_entries_of_eq (fun ω => by rw [wordVal_GZ]) hwt.1, ?_⟩
  · have h := hwt.2.2.2.2 r
    have e : (fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2, 0, 2]
        (dZ5 p)) r) = fun ω => SourceMixing.blkTr (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ *
          (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)))))) r :=
      funext fun ω => by rw [wordVal_GZ]
    rw [e] at h; exact h.trans hle
  have hT := hU W hWu E hEκ X hX 3 le_rfl ![2, 0, 2] (dZ p) (norm_dZ_le p)
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![2, 0, 2] (dZ p)) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p *
        (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) := funext fun ω => by rw [wordVal_Z]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2, 0, 2] (dZ p)) =
      fun ω => portProj * ((gRes b E X ω)ᴴ * (bProj p *
        (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)))) := funext fun ω => by rw [wordVal_Z]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 0) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordAlpha_Z0]
  have e4 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 1) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :=
    funext fun ω => by rw [wordAlpha_Z1]
  have e5 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 2) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p *
        (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) := funext fun ω => by rw [wordAlpha_Z2]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 0) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordGamma_Z0]
  have e7 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 1) =
      fun ω => gRes b E X ω * (portProj * (gRes b E X ω)ᴴ) := funext fun ω => by rw [wordGamma_Z1]
  have e8 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 2) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_Z2]
  obtain ⟨p0, p1⟩ := blkAt_expect_portProj (μ := μ) (fun ω => (gRes b E X ω)ᴴ * (bProj p *
    (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))
  rw [e1, e2, e3, e4, e5, e6, e7, e8, p0, p1, zero_add, blkAt_expect_conjT,
    blkAt_expect_conjT] at hT
  obtain ⟨hT0, hT1⟩ := hT
  have hup : Cu / (W : ℝ) ^ 2 ≤ (Cu + Cw) / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  refine ⟨hT0.trans hup, ?_⟩
  change ‖_ - SourceMixing.vOf b E X • (blkAt (gsTMean b E X p) 1 1 +
    (((b : ℂ) * SourceMixing.tTwo b E X 0) • blkAt (gsTMean b E X p) 1 1 +
      ((b : ℂ) * vP b E X p 0) • _ + ((b : ℂ) * zP b E X p 0) • _))‖ ≤ _ at hT1
  have eS : ∀ (c : ℂ) (Y Z₁ Z₂ : Matrix (Fin W) (Fin W) ℂ), Y + (c • Y + Z₁ + Z₂) =
      (1 + c) • Y + Z₁ + Z₂ := fun c Y Z₁ Z₂ => by rw [add_smul, one_smul]; abel
  rw [eS] at hT1
  exact hT1.trans hup

/-- **The `γ₀` mean of `m4_p`.**
Bulk-uniform copy of `gsN_block` (constants uniform on `bulkInterval κ`). -/
theorem gsN_block_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => (gRes b E X ω)ᴴ *
            (bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 -
          (SourceMixing.mOf b E X)ᴴ * (rB b E X p • blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))) 0 0 +
            conj (svP b E X p) • (blkAt (kHat b E X *
              matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hw⟩ := adjBlock_bulk hA hb0 hb hκ 2 1
  obtain ⟨Cm, Wm, hCm, hm⟩ := wordMean_bound_bulk hA hb0 hb hκ 3 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  refine ⟨C, max W₁ (max Wm WD), hC, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨hW₁, hWm, hWD⟩ := hW
  obtain ⟨-, -, -, -, -, -, -, -, hG, -, -⟩ := hD W hWD E hEκ X hX
  set μ := layerLaw W b .oneBlockOnePort
  have I1 := (hm W hWm E hEκ X hX.posSemidef 2 (by norm_num) ![0, 3] (dM2 p) (norm_dM2_le p)).1
  have I2 : ∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ *
      wordVal (kHat b E X) (gRes b E X ω) ![0, 3] (dM2 p)) α β) μ :=
    integrable_entries_of_eq (fun ω => by rw [wordVal_GsM2, wordVal_M2])
      (hm W hWm E hEκ X hX.posSemidef 3 le_rfl ![2, 0, 3] (dM24 p) (norm_dM24_le p)).1
  have I3 : ∀ j α β, Integrable (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p)
      j α β) μ := fun j => by
    fin_cases j
    · exact integrable_entries_of_eq (fun ω => by rw [wordVal_GPKs]; exact (wordGamma_M20 _ _ p).symm)
        (hm W hWm E hEκ X hX.posSemidef 2 (by norm_num) ![0, 3] ![1, portProj, 1] norm_ins3_le).1
    · exact integrable_entries_of_eq (fun ω => by rw [wordVal_Ks]; exact (wordGamma_M21 _ _ p).symm)
        (hm W hWm E hEκ X hX.posSemidef 1 (by norm_num) ![3] ![1, 1] norm_ins2_le).1
  have hT := hw W hW₁ E hEκ X hX 2 le_rfl ![0, 3] (dM2 p) (norm_dM2_le p) I1 I2 I3
  rw [Fin.sum_univ_two] at hT
  have e1 : (fun ω => (gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) ![0, 3] (dM2 p)) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (kHat b E X * gRes b E X ω)ᴴ))) := funext fun ω => by rw [wordVal_M2]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 3] (dM2 p)) =
      fun ω => bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ)) :=
    funext fun ω => by rw [wordVal_M2]
  have e3 : (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 0) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) := funext fun ω => by rw [wordAlpha_M20]
  have e4 : (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 1) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordAlpha_M21]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 0) =
      fun ω => gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordGamma_M20]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 1) =
      fun ω => (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_M21]
  have e7 : matrixExpect μ (fun ω => kHat b E X * gRes b E X ω) =
      kHat b E X * matrixExpect μ (gRes b E X) := (SourceMixing.mul_matrixExpect' _ _ hG).symm
  rw [e1, e2, e3, e4, e5, e6, blkAt_expect_bProj, blkAt_expect_conjT, e7, trMean_rP, trMean_rP,
    trMean_rv, trMean_rv, sig1_conj] at hT
  rw [← add_assoc, ← add_smul] at hT
  exact hT

/-- **The `γ₀` mean of the `z_p` system.**
Bulk-uniform copy of `gsT_block` (constants uniform on `bulkInterval κ`). -/
theorem gsT_block_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
          (portProj * (gRes b E X ω)ᴴ))) : LayerMat W) α β) (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => (gRes b E X ω)ᴴ *
            (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) 0 0 -
          (SourceMixing.mOf b E X)ᴴ * (rB b E X p • blkAt (tMean b E X) 0 0 +
            conj (svP b E X p) •
              (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hw⟩ := adjBlock_bulk hA hb0 hb hκ 2 1
  obtain ⟨Cm, Wm, hCm, hm⟩ := wordMean_bound_bulk hA hb0 hb hκ 3 1
  refine ⟨C, max W₁ Wm, hC, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hWm : Wm ≤ W := le_trans (le_max_right _ _) hW
  set μ := layerLaw W b .oneBlockOnePort
  have I1 := (hm W hWm E hEκ X hX.posSemidef 2 (by norm_num) ![0, 2] (dW p) (norm_dW_le p)).1
  have I2' : ∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
      (portProj * (gRes b E X ω)ᴴ))) : LayerMat W) α β) μ :=
    integrable_entries_of_eq (fun ω => by rw [wordVal_GsW])
      (hm W hWm E hEκ X hX.posSemidef 3 le_rfl ![2, 0, 2] (dW4 p) (norm_dW4_le p)).1
  have I2 : ∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ *
      wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dW p)) α β) μ :=
    integrable_entries_of_eq (fun ω => by rw [wordVal_W]) I2'
  have I3 : ∀ j α β, Integrable (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p)
      j α β) μ := fun j => by
    fin_cases j
    · exact integrable_entries_of_eq (fun ω => by rw [wordVal_GPGs]; exact (wordGamma_W0 _ _ p).symm)
        (hm W hWm E hEκ X hX.posSemidef 2 (by norm_num) ![0, 2] ![1, portProj, 1] norm_ins3_le).1
    · exact integrable_entries_of_eq (fun ω => by rw [wordVal_Gs1]; exact (wordGamma_W1 _ _ p).symm)
        (hm W hWm E hEκ X hX.posSemidef 1 (by norm_num) ![2] ![1, 1] norm_ins2_le).1
  refine ⟨I2', ?_⟩
  have hT := hw W hW₁ E hEκ X hX 2 le_rfl ![0, 2] (dW p) (norm_dW_le p) I1 I2 I3
  rw [Fin.sum_univ_two] at hT
  have e1 : (fun ω => (gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dW p)) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordVal_W]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dW p)) =
      fun ω => bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)) :=
    funext fun ω => by rw [wordVal_W]
  have e3 : (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 0) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) := funext fun ω => by rw [wordAlpha_W0]
  have e4 : (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 1) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordAlpha_W1]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 0) =
      fun ω => gRes b E X ω * (portProj * (gRes b E X ω)ᴴ) := funext fun ω => by rw [wordGamma_W0]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 1) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_W1]
  rw [e1, e2, e3, e4, e5, e6, blkAt_expect_bProj, blkAt_expect_conjT, trMean_rP, trMean_rP,
    trMean_rv, trMean_rv, sig1_conj] at hT
  rw [← add_assoc, ← add_smul] at hT
  exact hT

end BlockBand.Transmission.CovarianceBulk
