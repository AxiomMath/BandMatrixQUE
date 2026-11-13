module

public import BlockBand.Transmission.PassiveCovariance.TauP

/-!
# The trace system of `E[𝒢P_q𝒢ᴴ]` for both blocks `q` (the `t^q`, hence `r_p`, traces)

The case `q = 1` is `ScalarS1`. **Hypothesis:** `PassiveBoundsStatement`. Law
`layerLaw W b .oneBlockOnePort`, strictly passive `X`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`;
constants depend on `b, E` only, uniformly in `W ≥ W₀`, `X`, `q`.

`t^q_r = E⟨(𝒢P_q𝒢ᴴ)_rr⟩` (`tP q r`), `y_q = [q = 0] + σ₁(t^q)` (`yP`), `A = ⟨MMᴴ⟩` (`aOf`),
`h = |v|²` (`hOf`), `k_h = c + b²h` (`khOf`).
* `tP_blocks`: `(E[𝒢P_q𝒢ᴴ])₀₀ = y_qMMᴴ + O(W⁻²)`, `(E[𝒢P_q𝒢ᴴ])₁₁ = v([q=1] + bt^q₀)v̄ + O(W⁻²)`;
* `tP_system`: `t^q₀ = y_qA`, `t^q₁ = h([q=1] + bt^q₀)`, `y_q(1 - k_hA) = [q=0] + bh[q=1]`, all
  `+ O(W⁻²)`.

By cyclicity, `r_{pq} = E⟨(𝒢ᴴP_p𝒢)_qq⟩ = t^q_p` (`TqMatched`).
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

theorem wordVal_PpGs (Kh G : LayerMat W) (p : Fin 2) : wordVal Kh G ![2] (dP p) = bProj p * Gᴴ := by
  rw [wordVal_succ, wordVal_zero]; simp [dP, wLetter]

theorem wordAlpha_PpGs (Kh G : LayerMat W) (p : Fin 2) (j : Fin 1) :
    wordAlpha Kh G 1 ![2] (dP p) j = bProj p * Gᴴ := by
  rw [Subsingleton.elim j 0]; simp [wordAlpha, dP, wLeft]

theorem wordGamma_PpGs (Kh G : LayerMat W) (p : Fin 2) (j : Fin 1) :
    wordGamma Kh G 1 ![2] (dP p) j = Gᴴ := by
  rw [Subsingleton.elim j 0]; simp [wordGamma, dP, wRight, wordVal]

theorem wordVal_GPpGs (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![0, 2] (dP3 p) = G * (bProj p * Gᴴ) := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [dP3, wLetter]

theorem wordVal_Gs1 (Kh G : LayerMat W) : wordVal Kh G ![2] ![1, 1] = Gᴴ := by
  rw [wordVal_succ, wordVal_zero]; simp [wLetter]

/-- `t^q_r = E⟨(𝒢P_q𝒢ᴴ)_rr⟩`. -/
def tP (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (q r : Fin 2) : ℂ :=
  trMean b (fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ)) r

/-- `y_q = [q = 0] + σ₁(t^q)`. -/
def yP (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (q : Fin 2) : ℂ :=
  ind 0 q + sig1 b (tP b E X q 0) (tP b E X q 1)

/-- **Blocks of `E[𝒢P_q𝒢ᴴ]`.** -/
theorem tP_blocks (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ q : Fin 2,
        (∀ r, ‖tP b E X q r‖ ≤ C) ∧ ‖yP b E X q‖ ≤ C ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ) : LayerMat W) α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ))) 0 0 -
          yP b E X q • (SourceMixing.mOf b E X * (SourceMixing.mOf b E X)ᴴ)‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ))) 1 1 -
          (SourceMixing.vOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0) *
            conj (SourceMixing.vOf b E X)) • 1‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedBlock hA hb0 hb h1 h2 1 1
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  obtain ⟨Cw, Ww, hCw, hw⟩ := SourceMixing.wordMean_bound hA hb0 hb h1 h2 2 1
  set K := Cw + 1 + (Cu + CD * (Cw + 1) * CD + CD * (1 + b * Cw) * CD)
  have hK1 : Cw + 1 ≤ K := by
    have : 0 ≤ Cu + CD * (Cw + 1) * CD + CD * (1 + b * Cw) * CD := by positivity
    linarith
  refine ⟨K, max (max Wu WD) Ww, by positivity, fun W hW X hX q => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWu, hWD⟩, hWw⟩ := hW
  obtain ⟨-, -, hM, hv, -, -, hE0, hE1, -, -, -⟩ := hD W hWD X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw X hX.posSemidef 2 le_rfl ![0, 2] (dP3 q) (norm_dP3_le q)
  have hGs : ∀ α β, Integrable (fun ω => (gRes b E X ω)ᴴ α β) μ := fun α β => by
    have h := (hw W hWw X hX.posSemidef 1 (by norm_num) ![2] ![1, 1]
      SourceMixing.norm_ins1_le).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2] ![1, 1] α β) =
        fun ω => (gRes b E X ω)ᴴ α β := funext fun ω => by rw [wordVal_Gs1]
    rw [e] at h; exact h
  have ht : ∀ r, ‖tP b E X q r‖ ≤ Cw := fun r => by
    have h := hwt.2.2.2.2 r
    have e : (fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dP3 q)) r) =
        fun ω => SourceMixing.blkTr (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ)) r :=
      funext fun ω => by rw [wordVal_GPpGs]
    rw [e] at h; exact h
  have hx : ‖yP b E X q‖ ≤ Cw + 1 :=
    (norm_add_le _ _).trans (by
      have := norm_sig1_le hb0 hb (ht 0) (ht 1)
      have := norm_ind_le 0 q
      linarith)
  have hent : ∀ α β, Integrable
      (fun ω => (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ) : LayerMat W) α β) μ := fun α β => by
    have h := hwt.1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dP3 q) α β) =
        fun ω => (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_GPpGs]
    rw [e] at h; exact h
  refine ⟨fun r => (ht r).trans (by linarith), hx.trans hK1, hent, ?_⟩
  have hT := hU W hWu X hX 1 le_rfl ![2] (dP q) (norm_dP_le q)
  rw [Fin.sum_univ_one, Fin.sum_univ_one] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![2] (dP q)) =
      fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ) := funext fun ω => by rw [wordVal_PpGs]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2] (dP q)) =
      fun ω => bProj q * (gRes b E X ω)ᴴ := funext fun ω => by rw [wordVal_PpGs]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 1 ![2] (dP q) 0) =
      fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordAlpha_PpGs]
  have e4 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 1 ![2] (dP q) 0) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_PpGs]
  have e5 : matrixExpect μ (fun ω => bProj q * (gRes b E X ω)ᴴ) =
      bProj q * (matrixExpect μ (gRes b E X))ᴴ := by
    rw [← SourceMixing.mul_matrixExpect' _ _ hGs, SourceMixing.matrixExpect_conjTranspose]
  have e6 : matrixExpect μ (fun ω => (gRes b E X ω)ᴴ) = (matrixExpect μ (gRes b E X))ᴴ :=
    SourceMixing.matrixExpect_conjTranspose _
  rw [e1, e2, e3, e4, e5, e6, blkAt_bProj_mul, blkAt_bProj_mul, blkAt_conjTranspose,
    blkAt_conjTranspose] at hT
  obtain ⟨hT0, hT1⟩ := hT
  change ‖_ - SourceMixing.mOf b E X * ((ind 0 q) • _ + sig1 b (tP b E X q 0) (tP b E X q 1) • _)‖
    ≤ _ at hT0
  change ‖_ - SourceMixing.vOf b E X • ((ind 1 q) • _ + ((b : ℂ) * tP b E X q 0) • _)‖ ≤ _ at hT1
  rw [← add_smul] at hT0 hT1
  set T := matrixExpect μ (fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ))
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  set M := SourceMixing.mOf b E X
  set v := SourceMixing.vOf b E X
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  constructor
  · have e : blkAt T 0 0 - yP b E X q • (M * Mᴴ) =
        (blkAt T 0 0 - M * (yP b E X q • G0ᴴ)) + M * (yP b E X q • (G0ᴴ - Mᴴ)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * ((Cw + 1) * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add hT0 ?_
          refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM ?_ (norm_nonneg _) hCD)
          refine (norm_smul_le _ _).trans (mul_le_mul hx ?_ (norm_nonneg _) (by positivity))
          rw [SourceMixing.norm_conjTranspose_sub]; exact hE0
      _ = (Cu + CD * (Cw + 1) * CD) / (W : ℝ) ^ 2 := by ring
      _ ≤ _ := by
          refine div_le_div_of_nonneg_right ?_ hW2
          have : 0 ≤ CD * (1 + b * Cw) * CD := by positivity
          simp only [K]; linarith
  · set y := ind 1 q + (b : ℂ) * tP b E X q 0
    have hy : ‖y‖ ≤ 1 + b * Cw := (norm_add_le _ _).trans (add_le_add (norm_ind_le 1 q) (by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
      exact mul_le_mul_of_nonneg_left (ht 0) hb0.le))
    have e : blkAt T 1 1 - (v * y * conj v) • 1 =
        (blkAt T 1 1 - v • (y • G1ᴴ)) + v • (y • (G1ᴴ - (v • 1)ᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_one, smul_sub, smul_sub, smul_smul, smul_smul]
      simp only [Complex.star_def, smul_smul, mul_assoc]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * ((1 + b * Cw) * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add hT1 ?_
          refine (norm_smul_le _ _).trans (mul_le_mul hv ?_ (norm_nonneg _) hCD)
          refine (norm_smul_le _ _).trans (mul_le_mul hy ?_ (norm_nonneg _) (by positivity))
          rw [SourceMixing.norm_conjTranspose_sub]; exact hE1
      _ = (Cu + CD * (1 + b * Cw) * CD) / (W : ℝ) ^ 2 := by ring
      _ ≤ _ := by
          refine div_le_div_of_nonneg_right ?_ hW2
          have : 0 ≤ CD * (Cw + 1) * CD := by positivity
          simp only [K]; linarith

/-- **The trace system for `t^q`.** -/
theorem tP_system (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ q : Fin 2,
        ‖yP b E X q‖ ≤ C ∧
        ‖tP b E X q 0 - yP b E X q * SourceMixing.aOf b E X‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖tP b E X q 1 - SourceMixing.hOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖yP b E X q * (1 - SourceMixing.khOf b E X * SourceMixing.aOf b E X) -
          (ind 0 q + (b : ℂ) * SourceMixing.hOf b E X * ind 1 q)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hB⟩ := tP_blocks hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨(K + 1) * C₁, max W₁ WD, by positivity, fun W hW X hX q => ?_⟩
  obtain ⟨hW1, -, -, hv, -⟩ := hD W (le_trans (le_max_right _ _) hW) X hX
  obtain ⟨-, hx, hent, hb00, hb11⟩ := hB W (le_trans (le_max_left _ _) hW) X hX q
  have ht : ∀ r, tP b E X q r = SourceMixing.blkTr (matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ))) r := fun r =>
    SourceMixing.integral_blkTr _ hent r
  have d1 : ‖tP b E X q 0 - yP b E X q * SourceMixing.aOf b E X‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    have h := (SourceMixing.norm_blkTr_sub_le _ 0 _).trans hb00
    rw [trace_smul, smul_eq_mul, mul_left_comm, ← ht] at h
    exact h
  have d2 : ‖tP b E X q 1 - SourceMixing.hOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    have h := (SourceMixing.norm_blkTr_sub_le _ 1 _).trans hb11
    rw [SourceMixing.normTrace_smul_one hW1, ← ht] at h
    have e : SourceMixing.vOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0) *
        conj (SourceMixing.vOf b E X) =
        SourceMixing.hOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0) := by
      unfold SourceMixing.hOf; ring
    rw [e] at h; exact h
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    positivity
  have hup : C₁ / (W : ℝ) ^ 2 ≤ (K + 1) * C₁ / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left hC₁ (by linarith)) hW2'.le
  refine ⟨hx.trans (le_mul_of_one_le_left hC₁ (by linarith)), d1.trans hup, d2.trans hup, ?_⟩
  have hh : ‖SourceMixing.hOf b E X‖ ≤ CD * CD := by
    unfold SourceMixing.hOf
    rw [norm_mul, Complex.norm_conj]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  set h := SourceMixing.hOf b E X
  set A := SourceMixing.aOf b E X
  have e : yP b E X q * (1 - SourceMixing.khOf b E X * A) - (ind 0 q + (b : ℂ) * h * ind 1 q) =
      ((1 - 2 * b : ℝ) : ℂ) * (tP b E X q 0 - yP b E X q * A) +
        (b : ℂ) * (tP b E X q 1 - h * (ind 1 q + (b : ℂ) * tP b E X q 0)) +
        (b : ℂ) ^ 2 * h * (tP b E X q 0 - yP b E X q * A) := by
    unfold SourceMixing.khOf
    rw [show yP b E X q = ind 0 q + (((1 - 2 * b : ℝ) : ℂ) * tP b E X q 0 +
      (b : ℂ) * tP b E X q 1) from rfl]; ring
  rw [e]
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖((1 - 2 * b : ℝ) : ℂ) * (tP b E X q 0 - yP b E X q * A)‖ +
        ‖(b : ℂ) * (tP b E X q 1 - h * (ind 1 q + (b : ℂ) * tP b E X q 0))‖ +
        ‖(b : ℂ) ^ 2 * h * (tP b E X q 0 - yP b E X q * A)‖ := norm_add₃_le
    _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        simp only [norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ _ := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) = K * C₁ / (W : ℝ) ^ 2 by ring]
        exact div_le_div_of_nonneg_right (by nlinarith) hW2'.le

end BlockBand.Transmission.PassiveCovariance
