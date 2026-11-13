module

public import BlockBand.Transmission.PassiveCovarianceBulk.Systems
public import BlockBand.Transmission.PassiveCovariance.ZSysTrace

/-!
# Bulk-uniform `z_p` system

The physical and port trace equations of the `z_p` system and the system itself, with constants and
`W₀` uniform in `E ∈ bulkInterval κ`.
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

/-- The physical trace equation of the `z_p` system.
Bulk-uniform copy of `zP_trace0` (constants uniform on `bulkInterval κ`). -/
theorem zP_trace0_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖szP b E X p‖ ≤ C ∧ (∀ r, ‖zP b E X p r‖ ≤ C) ∧
        ‖zP b E X p 0 - ((SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
          conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
          svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) + szP b E X p * SourceMixing.aOf b E X)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cz, Wz, hCz, hZb⟩ := zP_blocks_bulk hA hb0 hb hκ
  obtain ⟨Cg, Wg, hCg, hGs⟩ := gsT_block_bulk hA hb0 hb hκ
  obtain ⟨C1, W1, hC1, hS1⟩ := scalarS1_blocks_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean_bulk hA hb0 hb hκ
  obtain ⟨Cv, Wv, hCv, hVs⟩ := vP_system_bulk hA hb0 hb hκ
  obtain ⟨Cq, Wq, hCq, hQb⟩ := tP_blocks_bulk hA hb0 hb hκ
  set Cr := 1 + Cq
  set C₁ := Cz + CD * (Cf * Cg + Cf * (CD * (Cr * C1 + Cv * CD)) + Cv * C1 + Cz * CD) +
    CD * (b * Cz * CD)
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨C₁, max (max (max Wz Wg) (max W1 WD)) (max (max Wf Wv) Wq),
    by positivity, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWz, hWg⟩, hW1', hWD⟩, ⟨hWf, hWv⟩, hWq⟩ := hW
  obtain ⟨hzb, hentZ, hZ0, hZ1⟩ := hZb W hWz E hEκ X hX p
  obtain ⟨hentX, hX0⟩ := hGs W hWg E hEκ X hX p
  obtain ⟨hT00, -⟩ := hS1 W hW1' E hEκ X hX
  obtain ⟨hW1r, -, hM, hv, -, -, hE0, hE1, -, -, -⟩ := hD W hWD E hEκ X hX
  obtain ⟨-, hs, -⟩ := hF W hWf E hEκ X hX
  obtain ⟨hS, -⟩ := hVs W hWv E hEκ X hX p
  obtain ⟨ht, -, -, -⟩ := hQb W hWq E hEκ X hX 0
  obtain ⟨ht1, -, hentT, -⟩ := hQb W hWq E hEκ X hX 1
  rw [bProj_one] at hentT
  set μ := layerLaw W b .oneBlockOnePort
  set M := SourceMixing.mOf b E X
  set v := SourceMixing.vOf b E X
  set s₁ := SourceMixing.sOne b E X
  set S := svP b E X p
  set σ := szP b E X p
  set r := rB b E X p
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  set T0 := blkAt (tMean b E X) 0 0
  set T1 := blkAt (tMean b E X) 1 1
  set X0 := blkAt (gsTMean b E X p) 0 0
  set X1 := blkAt (gsTMean b E X p) 1 1
  set c := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hσ : ‖σ‖ ≤ Cz := norm_sig1_le hb0 hb (hzb 0) (hzb 1)
  have hr : ‖r‖ ≤ Cr := (norm_add_le _ _).trans (add_le_add (norm_ind_le 0 p)
    (norm_sig1_le hb0 hb (ht p) (ht1 p)))
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1r
    positivity
  have hzt : ∀ r', zP b E X p r' = SourceMixing.blkTr (matrixExpect μ (fun ω => gRes b E X ω *
      (portProj * ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (gRes b E X ω)ᴴ))))))) r' := fun r' =>
    SourceMixing.integral_blkTr _ hentZ r'
  have hC₁ : 0 ≤ C₁ := by positivity
  -- the physical trace
  have hZ := z0_trace M s₁ S σ r (conj S)
  rw [← cqOf, ← SourceMixing.aOf, ← conj_bOf] at hZ
  change _ = s₁ * (s₁ * r * cqOf b E X + conj S * conj (SourceMixing.bOf b E X)) +
    S * s₁ * SourceMixing.bOf b E X + σ * SourceMixing.aOf b E X at hZ
  have hMh : ‖Mᴴ‖ ≤ CD := by rw [Matrix.l2_opNorm_conjTranspose]; exact hM
  have hG0h : ‖G0ᴴ - Mᴴ‖ ≤ CD / (W : ℝ) ^ 2 := by
    rw [SourceMixing.norm_conjTranspose_sub]; exact hE0
  have hcS : ‖conj S‖ ≤ Cv := by rw [Complex.norm_conj]; exact hS
  have hb2 := z0_mat_bound hM hs hr hS hcS hσ hX0 hT00 hG0h hCD hCf (by positivity) hCv hCz
  have d0 : ‖zP b E X p 0 - (s₁ * (s₁ * r * cqOf b E X + conj S * conj (SourceMixing.bOf b E X)) +
      S * s₁ * SourceMixing.bOf b E X + σ * SourceMixing.aOf b E X)‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    rw [← hZ, hzt]
    refine (SourceMixing.norm_blkTr_sub_le _ 0 _).trans ?_
    refine (norm_sub_le_norm_sub_add_norm_sub _ (M * (s₁ • X0 + S • T0 + σ • G0ᴴ)) _).trans ?_
    refine (add_le_add hZ0 hb2).trans ?_
    rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hW2'.le
    have : 0 ≤ CD * (b * Cz * CD) := by positivity
    simp only [C₁]; linarith
  exact ⟨hσ.trans (by simp only [C₁]; linarith [show 0 ≤ CD * (Cf * Cg + Cf * (CD * (Cr * C1 + Cv * CD)) +
    Cv * C1 + Cz * CD) + CD * (b * Cz * CD) by positivity]),
    fun r' => (hzb r').trans (by simp only [C₁]; linarith [show 0 ≤ CD * (Cf * Cg + Cf * (CD * (Cr * C1 +
      Cv * CD)) + Cv * C1 + Cz * CD) + CD * (b * Cz * CD) by positivity]), d0⟩

/-- The port trace equation of the `z_p` system.
Bulk-uniform copy of `zP_trace1` (constants uniform on `bulkInterval κ`). -/
theorem zP_trace1_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖zP b E X p 1 - SourceMixing.vOf b E X * ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
          conj (vP b E X p 1) + (b : ℂ) * vP b E X p 0 * SourceMixing.tTwo b E X 1 +
          (b : ℂ) * zP b E X p 0 * conj (SourceMixing.vOf b E X))‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cz, Wz, hCz, hZb⟩ := zP_blocks_bulk hA hb0 hb hκ
  obtain ⟨Cg, Wg, hCg, hGs⟩ := gsT_block_bulk hA hb0 hb hκ
  obtain ⟨C1, W1, hC1, hS1⟩ := scalarS1_blocks_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean_bulk hA hb0 hb hκ
  obtain ⟨Cv, Wv, hCv, hVs⟩ := vP_system_bulk hA hb0 hb hκ
  obtain ⟨Cq, Wq, hCq, hQb⟩ := tP_blocks_bulk hA hb0 hb hκ
  set Cr := 1 + Cq
  set C₁ := Cz + CD * (Cf * Cg + Cf * (CD * (Cr * C1 + Cv * CD)) + Cv * C1 + Cz * CD) +
    CD * (b * Cz * CD)
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨C₁, max (max (max Wz Wg) (max W1 WD)) (max (max Wf Wv) Wq),
    by positivity, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWz, hWg⟩, hW1', hWD⟩, ⟨hWf, hWv⟩, hWq⟩ := hW
  obtain ⟨hzb, hentZ, hZ0, hZ1⟩ := hZb W hWz E hEκ X hX p
  obtain ⟨hentX, hX0⟩ := hGs W hWg E hEκ X hX p
  obtain ⟨hT00, -⟩ := hS1 W hW1' E hEκ X hX
  obtain ⟨hW1r, -, hM, hv, -, -, hE0, hE1, -, -, -⟩ := hD W hWD E hEκ X hX
  obtain ⟨-, hs, -⟩ := hF W hWf E hEκ X hX
  obtain ⟨hS, -⟩ := hVs W hWv E hEκ X hX p
  obtain ⟨ht, -, -, -⟩ := hQb W hWq E hEκ X hX 0
  obtain ⟨ht1, -, hentT, -⟩ := hQb W hWq E hEκ X hX 1
  rw [bProj_one] at hentT
  set μ := layerLaw W b .oneBlockOnePort
  set M := SourceMixing.mOf b E X
  set v := SourceMixing.vOf b E X
  set s₁ := SourceMixing.sOne b E X
  set S := svP b E X p
  set σ := szP b E X p
  set r := rB b E X p
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  set T0 := blkAt (tMean b E X) 0 0
  set T1 := blkAt (tMean b E X) 1 1
  set X0 := blkAt (gsTMean b E X p) 0 0
  set X1 := blkAt (gsTMean b E X p) 1 1
  set c := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hσ : ‖σ‖ ≤ Cz := norm_sig1_le hb0 hb (hzb 0) (hzb 1)
  have hr : ‖r‖ ≤ Cr := (norm_add_le _ _).trans (add_le_add (norm_ind_le 0 p)
    (norm_sig1_le hb0 hb (ht p) (ht1 p)))
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1r
    positivity
  have hzt : ∀ r', zP b E X p r' = SourceMixing.blkTr (matrixExpect μ (fun ω => gRes b E X ω *
      (portProj * ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (gRes b E X ω)ᴴ))))))) r' := fun r' =>
    SourceMixing.integral_blkTr _ hentZ r'
  have hC₁ : 0 ≤ C₁ := by positivity
  -- the port trace
  have hT1 : (W : ℂ)⁻¹ * T1.trace = SourceMixing.tTwo b E X 1 := by
    rw [← SourceMixing.blkTr_def, ← SourceMixing.integral_blkTr _ hentT]; rfl
  have hX1 : (W : ℂ)⁻¹ * X1.trace = conj (vP b E X p 1) := by
    rw [← SourceMixing.blkTr_def, ← SourceMixing.integral_blkTr _ hentX, ← trMean_rv]
  set Zt1 := v • (c • X1 + ((b : ℂ) * vP b E X p 0) • T1 + ((b : ℂ) * zP b E X p 0 * conj v) • 1)
  have hZ1 : (W : ℂ)⁻¹ * Zt1.trace = v * (c * conj (vP b E X p 1) +
      (b : ℂ) * vP b E X p 0 * SourceMixing.tTwo b E X 1 + (b : ℂ) * zP b E X p 0 * conj v) := by
    have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
    simp only [Zt1, trace_smul, trace_add, trace_one, Fintype.card_fin, smul_eq_mul]
    rw [← hT1, ← hX1]; field_simp
  have d1 : ‖zP b E X p 1 - v * (c * conj (vP b E X p 1) +
      (b : ℂ) * vP b E X p 0 * SourceMixing.tTwo b E X 1 + (b : ℂ) * zP b E X p 0 * conj v)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    rw [← hZ1, hzt]
    refine (SourceMixing.norm_blkTr_sub_le _ 1 _).trans ?_
    have e : v • (c • X1 + ((b : ℂ) * vP b E X p 0) • T1 + ((b : ℂ) * zP b E X p 0) • G1ᴴ) - Zt1 =
        v • (((b : ℂ) * zP b E X p 0) • (G1 - v • 1)ᴴ) := by
      rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one]
      simp only [Zt1, smul_sub, smul_add, smul_smul, mul_assoc, Complex.star_def]; abel
    have hb2 : ‖v • (c • X1 + ((b : ℂ) * vP b E X p 0) • T1 + ((b : ℂ) * zP b E X p 0) • G1ᴴ) - Zt1‖ ≤
        CD * (b * Cz * CD) / (W : ℝ) ^ 2 := by
      rw [e]
      refine (norm_smul_le _ _).trans ((mul_le_mul hv ((norm_smul_le _ _).trans (mul_le_mul
        (show ‖(b : ℂ) * zP b E X p 0‖ ≤ b * Cz by
          rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left (hzb 0) hb0.le)
        (show ‖(G1 - v • 1)ᴴ‖ ≤ CD / (W : ℝ) ^ 2 by rw [Matrix.l2_opNorm_conjTranspose]; exact hE1)
        (norm_nonneg _) (by positivity))) (by positivity) hCD).trans (le_of_eq (by ring)))
    have := norm_sub_le_norm_sub_add_norm_sub (blkAt (matrixExpect μ (fun ω => gRes b E X ω *
      (portProj * ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (gRes b E X ω)ᴴ))))))) 1 1)
      (v • (c • X1 + ((b : ℂ) * vP b E X p 0) • T1 + ((b : ℂ) * zP b E X p 0) • G1ᴴ)) Zt1
    calc _ ≤ Cz / (W : ℝ) ^ 2 + CD * (b * Cz * CD) / (W : ℝ) ^ 2 := by linarith
      _ ≤ C₁ / (W : ℝ) ^ 2 := by
          rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hW2'.le
          have : 0 ≤ CD * (Cf * Cg + Cf * (CD * (Cr * C1 + Cv * CD)) + Cv * C1 + Cz * CD) := by
            positivity
          simp only [C₁]; linarith
  exact d1

/-- **The `z_p` trace system.**
Bulk-uniform copy of `zP_system` (constants uniform on `bulkInterval κ`). -/
theorem zP_system_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖szP b E X p‖ ≤ C ∧
        ‖szP b E X p * (1 - SourceMixing.khOf b E X * SourceMixing.aOf b E X) -
          (SourceMixing.khOf b E X * (SourceMixing.sOne b E X * (SourceMixing.sOne b E X *
              rB b E X p * cqOf b E X + conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
              svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
            (b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
              conj (vP b E X p 1) +
            (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 *
              SourceMixing.tTwo b E X 1)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C₀, W₀, hC₀, hz0⟩ := zP_trace0_bulk hA hb0 hb hκ
  obtain ⟨C₂, W₂, hC₂, hz1⟩ := zP_trace1_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  set C₁ := C₀ + C₂
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨C₀ + (K + 1) * C₁, max (max W₀ W₂) WD, by positivity, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW2⟩, hWD⟩ := hW
  obtain ⟨hσ, -, d0'⟩ := hz0 W hW0 E hEκ X hX p
  have d1' := hz1 W hW2 E hEκ X hX p
  obtain ⟨hW1r, -, -, hv, -⟩ := hD W hWD E hEκ X hX
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1r
    positivity
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hc0 : C₀ ≤ C₁ := by simp only [C₁]; linarith
  have hc2 : C₂ ≤ C₁ := by simp only [C₁]; linarith
  have d0 := d0'.trans (div_le_div_of_nonneg_right hc0 hW2'.le)
  have d1 := d1'.trans (div_le_div_of_nonneg_right hc2 hW2'.le)
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  set v := SourceMixing.vOf b E X
  set σ := szP b E X p
  set c := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0
  have hup : ∀ c' : ℝ, c' ≤ C₀ + (K + 1) * C₁ → c' / (W : ℝ) ^ 2 ≤
      (C₀ + (K + 1) * C₁) / (W : ℝ) ^ 2 := fun c' hc' => div_le_div_of_nonneg_right hc' hW2'.le
  have hKC : 0 ≤ (K + 1) * C₁ := by positivity
  refine ⟨hσ.trans (by linarith), ?_⟩
  set A := SourceMixing.aOf b E X
  set I := SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
    conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
    svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X
  set t₂ := SourceMixing.tTwo b E X 1
  have e : σ * (1 - SourceMixing.khOf b E X * A) - (SourceMixing.khOf b E X * I +
      (b : ℂ) * v * c * conj (vP b E X p 1) + (b : ℂ) * ((b : ℂ) * v) * vP b E X p 0 * t₂) =
      ((1 - 2 * b : ℝ) : ℂ) * (zP b E X p 0 - (I + σ * A)) +
        (b : ℂ) * (zP b E X p 1 - v * (c * conj (vP b E X p 1) + (b : ℂ) * vP b E X p 0 * t₂ +
          (b : ℂ) * zP b E X p 0 * conj v)) +
        (b : ℂ) ^ 2 * (v * conj v) * (zP b E X p 0 - (I + σ * A)) := by
    unfold SourceMixing.khOf SourceMixing.hOf
    rw [show σ = ((1 - 2 * b : ℝ) : ℂ) * zP b E X p 0 + (b : ℂ) * zP b E X p 1 from rfl]
    ring
  rw [e]
  have hh : ‖v * conj v‖ ≤ CD * CD := by
    rw [norm_mul, Complex.norm_conj]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖((1 - 2 * b : ℝ) : ℂ) * (zP b E X p 0 - (I + σ * A))‖ +
        ‖(b : ℂ) * (zP b E X p 1 - v * (c * conj (vP b E X p 1) + (b : ℂ) * vP b E X p 0 * t₂ +
          (b : ℂ) * zP b E X p 0 * conj v))‖ +
        ‖(b : ℂ) ^ 2 * (v * conj v) * (zP b E X p 0 - (I + σ * A))‖ := norm_add₃_le
    _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ (C₀ + (K + 1) * C₁) / (W : ℝ) ^ 2 := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) = K * C₁ / (W : ℝ) ^ 2 by ring]
        refine hup _ ?_
        nlinarith

end BlockBand.Transmission.CovarianceBulk
