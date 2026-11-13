module

public import BlockBand.Transmission.PassiveCovariance.VSys

/-!
# The `v_p` trace system, scalar form

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` only, uniformly in `W ≥ W₀`,
`X`, `p`.

* `bProj_one`: `P₁ = Π` (so `tTwo = t¹`, `tTwo_eq`).
* **`vP_system`**: `|S_p| ≤ C` and
  `S_p(1 - k_v⟨M²⟩) = k_vs₁rB_p⟨M²Mᴴ⟩ + bv(1 + bt₁)t¹_p + O(W⁻²)` (`S_p = σ₁(v^p)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem bProj_one : (bProj 1 : LayerMat W) = portProj := by
  ext α β
  rcases α with ⟨i, x⟩ | ⟨i, x⟩ <;> rcases β with ⟨j, y⟩ | ⟨j, y⟩ <;>
    simp [bProj, bInd, blkOf, portProj, Matrix.diagonal_apply, Matrix.one_apply, fromBlocks]

theorem tTwo_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (r : Fin 2) :
    SourceMixing.tTwo b E X r = tP b E X 1 r := by
  simp only [SourceMixing.tTwo, tP, trMean, bProj_one]

/-- **The `v_p` trace system.** -/
theorem vP_system (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖svP b E X p‖ ≤ C ∧
        ‖svP b E X p * (1 - SourceMixing.kvOf b E X * SourceMixing.m2Of b E X) -
          (SourceMixing.kvOf b E X * SourceMixing.sOne b E X * rB b E X p * SourceMixing.bOf b E X +
            (b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
              tP b E X 1 p)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cv, Wv, hCv, hVb⟩ := vP_blocks hA hb0 hb h1 h2
  obtain ⟨Cg, Wg, hCg, hGs⟩ := gsMean_block hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  obtain ⟨Cf, Wf, hCf, hF⟩ := SourceMixing.freshU_mean hA hb0 hb h1 h2
  obtain ⟨Ct, Wt, hCt, hTb⟩ := tP_blocks hA hb0 hb h1 h2
  set Cr := 1 + Ct
  set C₁ := Cv + CD * (Cf * Cg + Cf * (Cr * (CD * CD)) + Cv * CD) + CD * (b * Cv * CD)
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨Cv + (K + 1) * C₁, max (max (max Wv Wg) (max WD Wf)) Wt, by positivity,
    fun W hW X hX p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWv, hWg⟩, hWD, hWf⟩, hWt⟩ := hW
  obtain ⟨hvb, hentV, hV0, hV1⟩ := hVb W hWv X hX p
  obtain ⟨hentX, hX00⟩ := hGs W hWg X hX p
  obtain ⟨hW1, -, hM, hv, -, -, hE0, hE1, -, -, -⟩ := hD W hWD X hX
  obtain ⟨-, hs, -⟩ := hF W hWf X hX
  obtain ⟨ht, -, -, -, -⟩ := hTb W hWt X hX 0
  obtain ⟨ht1, -, -, -, -⟩ := hTb W hWt X hX 1
  set μ := layerLaw W b .oneBlockOnePort
  set M := SourceMixing.mOf b E X
  set v := SourceMixing.vOf b E X
  set s₁ := SourceMixing.sOne b E X
  set S := svP b E X p
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  set X0 := blkAt (gsMean b E X p) 0 0
  set X1 := blkAt (gsMean b E X p) 1 1
  have hS : ‖S‖ ≤ Cv := norm_sig1_le hb0 hb (hvb 0) (hvb 1)
  have hr : ‖rB b E X p‖ ≤ Cr := (norm_add_le _ _).trans (add_le_add (norm_ind_le 0 p)
    (norm_sig1_le hb0 hb (ht p) (ht1 p)))
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    positivity
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hvt : ∀ r, vP b E X p r = SourceMixing.blkTr (matrixExpect μ (fun ω => gRes b E X ω *
      (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))))) r := fun r =>
    SourceMixing.integral_blkTr _ hentV r
  -- trace of the physical block
  set Z := M * (s₁ • (rB b E X p • (Mᴴ * M)) + S • M)
  have hZ : (W : ℂ)⁻¹ * Z.trace = s₁ * rB b E X p * SourceMixing.bOf b E X + S * SourceMixing.m2Of b E X := by
    have ec : (M * (Mᴴ * M)).trace = (M * (M * Mᴴ)).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Z, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul, ec,
      SourceMixing.bOf, SourceMixing.m2Of]
    ring
  have d0 : ‖vP b E X p 0 - (s₁ * rB b E X p * SourceMixing.bOf b E X + S * SourceMixing.m2Of b E X)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    rw [← hZ, hvt]
    refine (SourceMixing.norm_blkTr_sub_le _ 0 _).trans ?_
    have e : M * (s₁ • X0 + S • G0) - Z = M * (s₁ • (X0 - rB b E X p • (Mᴴ * G0)) +
        s₁ • (rB b E X p • (Mᴴ * (G0 - M))) + S • (G0 - M)) := by
      simp only [Z, Matrix.mul_sub, smul_sub, Matrix.mul_add, Matrix.mul_smul]; abel
    have hb2 : ‖M * (s₁ • X0 + S • G0) - Z‖ ≤
        CD * (Cf * Cg + Cf * (Cr * (CD * CD)) + Cv * CD) / (W : ℝ) ^ 2 := by
      rw [e]
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      have t1 : ‖s₁ • (X0 - rB b E X p • (Mᴴ * G0))‖ ≤ Cf * (Cg / (W : ℝ) ^ 2) :=
        (norm_smul_le _ _).trans (mul_le_mul hs hX00 (norm_nonneg _) hCf)
      have hMh : ‖Mᴴ‖ ≤ CD := by rw [Matrix.l2_opNorm_conjTranspose]; exact hM
      have t2a : ‖Mᴴ * (G0 - M)‖ ≤ CD * (CD / (W : ℝ) ^ 2) :=
        (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hMh hE0 (norm_nonneg _) hCD)
      have t2b : ‖rB b E X p • (Mᴴ * (G0 - M))‖ ≤ Cr * (CD * (CD / (W : ℝ) ^ 2)) :=
        (norm_smul_le _ _).trans (mul_le_mul hr t2a (norm_nonneg _) (by positivity))
      have t2 : ‖s₁ • (rB b E X p • (Mᴴ * (G0 - M)))‖ ≤ Cf * (Cr * (CD * (CD / (W : ℝ) ^ 2))) :=
        (norm_smul_le _ _).trans (mul_le_mul hs t2b (norm_nonneg _) hCf)
      have t3 : ‖S • (G0 - M)‖ ≤ Cv * (CD / (W : ℝ) ^ 2) :=
        (norm_smul_le _ _).trans (mul_le_mul hS hE0 (norm_nonneg _) hCv)
      refine (mul_le_mul hM ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add t1 t2)) t3)) (by positivity) hCD).trans (le_of_eq ?_)
      ring
    have := norm_sub_le_norm_sub_add_norm_sub (blkAt (matrixExpect μ (fun ω => gRes b E X ω *
      (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))))) 0 0) (M * (s₁ • X0 + S • G0)) Z
    calc _ ≤ Cv / (W : ℝ) ^ 2 + CD * (Cf * Cg + Cf * (Cr * (CD * CD)) + Cv * CD) / (W : ℝ) ^ 2 := by
          linarith
      _ ≤ C₁ / (W : ℝ) ^ 2 := by
          rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hW2'.le
          have : 0 ≤ CD * (b * Cv * CD) := by positivity
          simp only [C₁]; linarith
  -- trace of the port block
  have hX1 : (W : ℂ)⁻¹ * X1.trace = tP b E X 1 p := by
    rw [← SourceMixing.blkTr_def, ← SourceMixing.integral_blkTr _ hentX]
    have e : ∀ ω, SourceMixing.blkTr ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)) 1 =
        SourceMixing.blkTr (gRes b E X ω * (bProj 1 * (gRes b E X ω)ᴴ)) p := fun ω =>
      blkTr_cyc _ p 1
    simp only [e]; rfl
  set Z1 := v • ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) • X1 + ((b : ℂ) * vP b E X p 0 * v) • 1)
  have hZ1 : (W : ℂ)⁻¹ * Z1.trace = v * ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) * tP b E X 1 p +
      (b : ℂ) * vP b E X p 0 * v) := by
    have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
    simp only [Z1, trace_smul, trace_add, trace_one, Fintype.card_fin, smul_eq_mul]
    rw [← hX1]; field_simp
  have d1 : ‖vP b E X p 1 - v * ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) * tP b E X 1 p +
      (b : ℂ) * vP b E X p 0 * v)‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    rw [← hZ1, hvt]
    refine (SourceMixing.norm_blkTr_sub_le _ 1 _).trans ?_
    have e : v • ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) • X1 + ((b : ℂ) * vP b E X p 0) • G1) - Z1 =
        v • (((b : ℂ) * vP b E X p 0) • (G1 - v • 1)) := by
      simp only [Z1, smul_sub, smul_add, smul_smul, mul_assoc]; abel
    have hb2 : ‖v • ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) • X1 + ((b : ℂ) * vP b E X p 0) • G1) -
        Z1‖ ≤ CD * (b * Cv * CD) / (W : ℝ) ^ 2 := by
      rw [e]
      refine (norm_smul_le _ _).trans ((mul_le_mul hv ((norm_smul_le _ _).trans (mul_le_mul
        (show ‖(b : ℂ) * vP b E X p 0‖ ≤ b * Cv by
          rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left (hvb 0) hb0.le) hE1 (norm_nonneg _)
        (by positivity))) (by positivity) hCD).trans (le_of_eq (by ring)))
    have := norm_sub_le_norm_sub_add_norm_sub (blkAt (matrixExpect μ (fun ω => gRes b E X ω *
      (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))))) 1 1)
      (v • ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) • X1 + ((b : ℂ) * vP b E X p 0) • G1)) Z1
    calc _ ≤ Cv / (W : ℝ) ^ 2 + CD * (b * Cv * CD) / (W : ℝ) ^ 2 := by linarith
      _ ≤ C₁ / (W : ℝ) ^ 2 := by
          rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hW2'.le
          have : 0 ≤ CD * (Cf * Cg + Cf * (Cr * (CD * CD)) + Cv * CD) := by positivity
          simp only [C₁]; linarith
  -- the system
  refine ⟨hS.trans (by have : 0 ≤ (K + 1) * C₁ := by positivity
                       linarith), ?_⟩
  have hvv : ‖v‖ ^ 2 ≤ CD * CD := by rw [sq]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  set m := SourceMixing.m2Of b E X
  set B := SourceMixing.bOf b E X
  set T := (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) * tP b E X 1 p
  have e : S * (1 - SourceMixing.kvOf b E X * m) -
      (SourceMixing.kvOf b E X * s₁ * rB b E X p * B +
        (b : ℂ) * v * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) * tP b E X 1 p) =
      ((1 - 2 * b : ℝ) : ℂ) * (vP b E X p 0 - (s₁ * rB b E X p * B + S * m)) +
        (b : ℂ) * (vP b E X p 1 - v * (T + (b : ℂ) * vP b E X p 0 * v)) +
        (b : ℂ) ^ 2 * v ^ 2 * (vP b E X p 0 - (s₁ * rB b E X p * B + S * m)) := by
    unfold SourceMixing.kvOf
    rw [show S = ((1 - 2 * b : ℝ) : ℂ) * vP b E X p 0 + (b : ℂ) * vP b E X p 1 from rfl]
    simp only [T]; ring
  rw [e]
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖((1 - 2 * b : ℝ) : ℂ) * (vP b E X p 0 - (s₁ * rB b E X p * B + S * m))‖ +
        ‖(b : ℂ) * (vP b E X p 1 - v * (T + (b : ℂ) * vP b E X p 0 * v))‖ +
        ‖(b : ℂ) ^ 2 * v ^ 2 * (vP b E X p 0 - (s₁ * rB b E X p * B + S * m))‖ := norm_add₃_le
    _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        simp only [norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ (Cv + (K + 1) * C₁) / (W : ℝ) ^ 2 := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) = K * C₁ / (W : ℝ) ^ 2 by ring]
        refine div_le_div_of_nonneg_right ?_ hW2'.le
        have : 0 ≤ C₁ := by positivity
        nlinarith

end BlockBand.Transmission.PassiveCovariance
