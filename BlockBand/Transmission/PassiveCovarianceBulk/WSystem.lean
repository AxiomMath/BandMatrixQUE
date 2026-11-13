module

public import BlockBand.Transmission.PassiveCovarianceBulk.Blocks
public import BlockBand.Transmission.PassiveCovarianceBulk.MatchedScalars
public import BlockBand.Transmission.PassiveCovariance.WSysTrace

/-!
# Bulk-uniform `w_p` system

The `w_p` trace system, with constants and `W₀` uniform in `E ∈ bulkInterval κ`.
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

/-- **The `w_p` trace system.**
Bulk-uniform copy of `wP_system` (constants uniform on `bulkInterval κ`). -/
theorem wP_system_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖swP b E X p‖ ≤ C ∧
        ‖tauP b E X p 0 - xP b E X p * SourceMixing.m2Of b E X‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖swP b E X p * (1 - SourceMixing.khOf b E X * SourceMixing.aOf b E X) -
          (SourceMixing.khOf b E X * (xP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
            (b : ℂ) * SourceMixing.vOf b E X * (ind 1 p + (b : ℂ) * tauP b E X p 0) *
              SourceMixing.tTwo b E X 1)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cv, Wv, hCv, hWb⟩ := wP_blocks_bulk hA hb0 hb hκ
  obtain ⟨C1, W1, hC1, hS1⟩ := scalarS1_blocks_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨Ct, Wt, hCt, hTb⟩ := tauP_blocks_bulk hA hb0 hb hκ
  obtain ⟨Cq, Wq, hCq, hQb⟩ := tP_blocks_bulk hA hb0 hb hκ
  set C₁ := Cv + CD * (Ct * C1 + Cv * CD) + CD * (b * Cv * CD)
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨Cv + Ct + (K + 1) * C₁, max (max (max Wv W1) WD) (max Wt Wq), by positivity,
    fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWv, hW1'⟩, hWD⟩, hWt, hWq⟩ := hW
  obtain ⟨hwb, hentW, hW0, hW1⟩ := hWb W hWv E hEκ X hX p
  obtain ⟨hT00, -⟩ := hS1 W hW1' E hEκ X hX
  obtain ⟨hW1r, -, hM, hv, -, -, hE0, hE1, -, -, -⟩ := hD W hWD E hEκ X hX
  obtain ⟨ht, hx, hentP, hP00, -⟩ := hTb W hWt E hEκ X hX p
  obtain ⟨-, -, hentT, -⟩ := hQb W hWq E hEκ X hX 1
  rw [bProj_one] at hentT
  set μ := layerLaw W b .oneBlockOnePort
  set M := SourceMixing.mOf b E X
  set v := SourceMixing.vOf b E X
  set s₁ := SourceMixing.sOne b E X
  set x := xP b E X p
  set S := swP b E X p
  set c := ind 1 p + (b : ℂ) * tauP b E X p 0
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  set T0 := blkAt (tMean b E X) 0 0
  set T1 := blkAt (tMean b E X) 1 1
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hS : ‖S‖ ≤ Cv := norm_sig1_le hb0 hb (hwb 0) (hwb 1)
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1r
    positivity
  have hwt : ∀ r, wP b E X p r = SourceMixing.blkTr (matrixExpect μ (fun ω => gRes b E X ω *
      (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) r := fun r =>
    SourceMixing.integral_blkTr _ hentW r
  have hC₁ : 0 ≤ C₁ := by positivity
  -- the `τ^p₀` trace
  have dτ : ‖tauP b E X p 0 - x * SourceMixing.m2Of b E X‖ ≤ Ct / (W : ℝ) ^ 2 := by
    have h := (SourceMixing.norm_blkTr_sub_le _ 0 _).trans hP00
    rw [trace_smul, smul_eq_mul, mul_left_comm, ← SourceMixing.integral_blkTr _ hentP] at h
    exact h
  -- the physical trace
  set Z := M * (x • (s₁ • (M * Mᴴ)) + S • Mᴴ)
  have hZ : (W : ℂ)⁻¹ * Z.trace = x * s₁ * SourceMixing.bOf b E X + S * SourceMixing.aOf b E X := by
    simp only [Z, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul,
      SourceMixing.bOf, SourceMixing.aOf]
    ring
  have d0 : ‖wP b E X p 0 - (x * s₁ * SourceMixing.bOf b E X + S * SourceMixing.aOf b E X)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    rw [← hZ, hwt]
    refine (SourceMixing.norm_blkTr_sub_le _ 0 _).trans ?_
    have e : M * (x • T0 + S • G0ᴴ) - Z = M * (x • (T0 - s₁ • (M * Mᴴ)) + S • (G0ᴴ - Mᴴ)) := by
      simp only [Z, Matrix.mul_sub, smul_sub, Matrix.mul_add]; abel
    have hb2 : ‖M * (x • T0 + S • G0ᴴ) - Z‖ ≤ CD * (Ct * C1 + Cv * CD) / (W : ℝ) ^ 2 := by
      rw [e]
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      have t1 : ‖x • (T0 - s₁ • (M * Mᴴ))‖ ≤ Ct * (C1 / (W : ℝ) ^ 2) :=
        (norm_smul_le _ _).trans (mul_le_mul hx hT00 (norm_nonneg _) hCt)
      have t2 : ‖S • (G0ᴴ - Mᴴ)‖ ≤ Cv * (CD / (W : ℝ) ^ 2) := by
        refine (norm_smul_le _ _).trans (mul_le_mul hS ?_ (norm_nonneg _) hCv)
        rw [SourceMixing.norm_conjTranspose_sub]; exact hE0
      refine (mul_le_mul hM ((norm_add_le _ _).trans (add_le_add t1 t2)) (by positivity)
        hCD).trans (le_of_eq ?_)
      ring
    have := norm_sub_le_norm_sub_add_norm_sub (blkAt (matrixExpect μ (fun ω => gRes b E X ω *
      (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) 0 0) (M * (x • T0 + S • G0ᴴ)) Z
    calc _ ≤ Cv / (W : ℝ) ^ 2 + CD * (Ct * C1 + Cv * CD) / (W : ℝ) ^ 2 := by linarith
      _ ≤ C₁ / (W : ℝ) ^ 2 := by
          rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hW2'.le
          have : 0 ≤ CD * (b * Cv * CD) := by positivity
          simp only [C₁]; linarith
  -- the port trace
  have hT1 : (W : ℂ)⁻¹ * T1.trace = SourceMixing.tTwo b E X 1 := by
    rw [← SourceMixing.blkTr_def, ← SourceMixing.integral_blkTr _ hentT]; rfl
  set Z1 := v • (c • T1 + ((b : ℂ) * wP b E X p 0 * conj v) • 1)
  have hZ1 : (W : ℂ)⁻¹ * Z1.trace = v * (c * SourceMixing.tTwo b E X 1 +
      (b : ℂ) * wP b E X p 0 * conj v) := by
    have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
    simp only [Z1, trace_smul, trace_add, trace_one, Fintype.card_fin, smul_eq_mul]
    rw [← hT1]; field_simp
  have d1 : ‖wP b E X p 1 - v * (c * SourceMixing.tTwo b E X 1 + (b : ℂ) * wP b E X p 0 * conj v)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    rw [← hZ1, hwt]
    refine (SourceMixing.norm_blkTr_sub_le _ 1 _).trans ?_
    have e : v • (c • T1 + ((b : ℂ) * wP b E X p 0) • G1ᴴ) - Z1 =
        v • (((b : ℂ) * wP b E X p 0) • (G1 - v • 1)ᴴ) := by
      rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one]
      simp only [Z1, smul_sub, smul_add, smul_smul, mul_assoc, Complex.star_def]; abel
    have hb2 : ‖v • (c • T1 + ((b : ℂ) * wP b E X p 0) • G1ᴴ) - Z1‖ ≤
        CD * (b * Cv * CD) / (W : ℝ) ^ 2 := by
      rw [e]
      refine (norm_smul_le _ _).trans ((mul_le_mul hv ((norm_smul_le _ _).trans (mul_le_mul
        (show ‖(b : ℂ) * wP b E X p 0‖ ≤ b * Cv by
          rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left (hwb 0) hb0.le)
        (show ‖(G1 - v • 1)ᴴ‖ ≤ CD / (W : ℝ) ^ 2 by rw [Matrix.l2_opNorm_conjTranspose]; exact hE1) (norm_nonneg _)
        (by positivity))) (by positivity) hCD).trans (le_of_eq (by ring)))
    have := norm_sub_le_norm_sub_add_norm_sub (blkAt (matrixExpect μ (fun ω => gRes b E X ω *
      (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) 1 1)
      (v • (c • T1 + ((b : ℂ) * wP b E X p 0) • G1ᴴ)) Z1
    calc _ ≤ Cv / (W : ℝ) ^ 2 + CD * (b * Cv * CD) / (W : ℝ) ^ 2 := by linarith
      _ ≤ C₁ / (W : ℝ) ^ 2 := by
          rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hW2'.le
          have : 0 ≤ CD * (Ct * C1 + Cv * CD) := by positivity
          simp only [C₁]; linarith
  -- the system
  have hup : ∀ c' : ℝ, c' ≤ Cv + Ct + (K + 1) * C₁ → c' / (W : ℝ) ^ 2 ≤
      (Cv + Ct + (K + 1) * C₁) / (W : ℝ) ^ 2 := fun c' hc' =>
    div_le_div_of_nonneg_right hc' hW2'.le
  have hKC : 0 ≤ (K + 1) * C₁ := by positivity
  refine ⟨hS.trans (by linarith), dτ.trans (hup _ (by linarith)), ?_⟩
  have hh : ‖v * conj v‖ ≤ CD * CD := by
    rw [norm_mul, Complex.norm_conj]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  set A := SourceMixing.aOf b E X
  set B := SourceMixing.bOf b E X
  set t₂ := SourceMixing.tTwo b E X 1
  have e : S * (1 - SourceMixing.khOf b E X * A) -
      (SourceMixing.khOf b E X * (x * s₁ * B) + (b : ℂ) * v * c * t₂) =
      ((1 - 2 * b : ℝ) : ℂ) * (wP b E X p 0 - (x * s₁ * B + S * A)) +
        (b : ℂ) * (wP b E X p 1 - v * (c * t₂ + (b : ℂ) * wP b E X p 0 * conj v)) +
        (b : ℂ) ^ 2 * (v * conj v) * (wP b E X p 0 - (x * s₁ * B + S * A)) := by
    unfold SourceMixing.khOf SourceMixing.hOf
    rw [show S = ((1 - 2 * b : ℝ) : ℂ) * wP b E X p 0 + (b : ℂ) * wP b E X p 1 from rfl]
    ring
  rw [e]
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖((1 - 2 * b : ℝ) : ℂ) * (wP b E X p 0 - (x * s₁ * B + S * A))‖ +
        ‖(b : ℂ) * (wP b E X p 1 - v * (c * t₂ + (b : ℂ) * wP b E X p 0 * conj v))‖ +
        ‖(b : ℂ) ^ 2 * (v * conj v) * (wP b E X p 0 - (x * s₁ * B + S * A))‖ := norm_add₃_le
    _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ (Cv + Ct + (K + 1) * C₁) / (W : ℝ) ^ 2 := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) = K * C₁ / (W : ℝ) ^ 2 by ring]
        refine hup _ ?_
        nlinarith

end BlockBand.Transmission.CovarianceBulk
