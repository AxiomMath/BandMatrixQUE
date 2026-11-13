module

public import BlockBand.Transmission.SourceMixing.MeanBlockTools

/-!
# The scalar system for `s₁` (word `w = P₂𝒢ᴴ`)

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, deterministic strictly
passive `X` (`Y ≻ 0`), operator norm, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` only,
uniformly in `W ≥ W₀` and `X`.

The blocks of the two-resolvent mean `E[𝒢P₂𝒢ᴴ]` and the resulting scalar equations, up to
`O(W⁻²)`.

`T = E[𝒢P₂𝒢ᴴ]`, `t_r = ⟨T⟩_r` (`tTwo`), `s₁ = ct₁ + bt₂` (`sOne`), `A = ⟨MMᴴ⟩`, `h = |v|²`.
* `scalarS1_blocks`: `‖T₀₀ - s₁MMᴴ‖ ≤ C/W²`, `‖T₁₁ - v(1 + bt₁)v̄·I‖ ≤ C/W²`;
* `scalarS1`: `|t₁ - s₁A| ≤ C/W²`, `|t₂ - h(1 + bt₁)| ≤ C/W²`,
  `|s₁(1 - k_hA) - bh| ≤ C/W²` with `k_h = c + b²h`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `A = ⟨MMᴴ⟩`. -/
def aOf (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  (W : ℂ)⁻¹ * (mOf b E X * (mOf b E X)ᴴ).trace

/-- `h = v v̄`. -/
def hOf (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ := vOf b E X * conj (vOf b E X)

/-- Letters of `P₂𝒢ᴴ`. -/
def wdGs : Fin 1 → Fin 4 := fun _ => 2

theorem wordVal_Gs (Kh G : LayerMat W) : wordVal Kh G wdGs dStar2 = pTwo * Gᴴ := by
  rw [wordVal_succ, wordVal_zero]
  show dStar2 0 * wLetter Kh G (wdGs 0) * dStar2 (Fin.succ 0) = _
  rw [dStar2_zero, dStar2_one, Matrix.mul_one]; rfl

theorem wordAlpha_Gs (Kh G : LayerMat W) (j : Fin 1) :
    wordAlpha Kh G 1 wdGs dStar2 j = pTwo * Gᴴ := by
  rw [Subsingleton.elim j 0]
  show dStar2 0 * wLeft Kh G (wdGs 0) = _
  rw [dStar2_zero]; rfl

theorem wordGamma_Gs (Kh G : LayerMat W) (j : Fin 1) : wordGamma Kh G 1 wdGs dStar2 j = Gᴴ := by
  rw [Subsingleton.elim j 0]
  show wRight Kh G (wdGs 0) * wordVal Kh G (fun j => wdGs j.succ) (fun j => dStar2 j.succ) = _
  rw [wordVal_zero]
  show wRight Kh G (wdGs 0) * dStar2 (Fin.succ 0) = _
  rw [dStar2_one, Matrix.mul_one]; rfl

theorem norm_conjTranspose_sub (A B : Matrix (Fin W) (Fin W) ℂ) : ‖Aᴴ - Bᴴ‖ = ‖A - B‖ := by
  rw [← conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]

/-- The blocks of `E[𝒢P₂𝒢ᴴ]`. -/
theorem scalarS1_blocks (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))) 0 0 -
          sOne b E X • (mOf b E X * (mOf b E X)ᴴ)‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))) 1 1 -
          (vOf b E X * (1 + (b : ℂ) * tTwo b E X 0) * conj (vOf b E X)) • 1‖ ≤
            C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedExpansion hA hb0 hb h1 h2 1 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks hA hb0 hb h1 h2
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean hA hb0 hb h1 h2
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound hA hb0 hb h1 h2 2 1
  refine ⟨Cu + CD * Cf * CD + CD * (1 + b * Cw) * CD, max (max Wu WD) (max Wf Ww), by positivity,
    fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWu, hWD⟩, hWf, hWw⟩ := hW
  obtain ⟨-, -, hM, hv, bl0, bl1, hE0, hE1, -, -, -⟩ := hD W hWD X hX
  obtain ⟨-, hs, -⟩ := hF W hWf X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hT := hU W hWu X hX 1 le_rfl wdGs dStar2 norm_dStar2_le
  rw [Fin.sum_univ_one] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wdGs dStar2) =
      fun ω => gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ) := funext fun ω => by rw [wordVal_Gs]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) wdGs dStar2) =
      fun ω => pTwo * (gRes b E X ω)ᴴ := funext fun ω => by rw [wordVal_Gs]
  have e3 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 1 wdGs dStar2 0) r) =
      fun ω => blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) r :=
    fun r => funext fun ω => by rw [wordAlpha_Gs]
  have e4 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 1 wdGs dStar2 0) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_Gs]
  rw [e1, e2, e3 0, e3 1, e4] at hT
  have et : ∀ r, (∫ ω, blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) r ∂μ) = tTwo b E X r :=
    fun r => rfl
  rw [et 0, et 1] at hT
  set T := matrixExpect μ (fun ω => gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  obtain ⟨hS0, hS1⟩ := blkAt_selfEnergy_mul (W := W) b (tTwo b E X 0) (tTwo b E X 1)
    (matrixExpect μ fun ω => (gRes b E X ω)ᴴ)
  have hGs0 : blkAt (matrixExpect μ fun ω => (gRes b E X ω)ᴴ) 0 0 = G0ᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose]
  have hGs1 : blkAt (matrixExpect μ fun ω => (gRes b E X ω)ᴴ) 1 1 = G1ᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose]
  have hP0 : blkAt (matrixExpect μ fun ω => pTwo * (gRes b E X ω)ᴴ) 0 0 = 0 := by
    have e : (fun ω => blkAt (pTwo * (gRes b E X ω)ᴴ) 0 0) =
        fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) := funext fun ω => blkAt_portProj_mul_zero _ 0
    rw [blkAt_matrixExpect, e]; ext x y; simp [matrixExpect]
  have hP1 : blkAt (matrixExpect μ fun ω => pTwo * (gRes b E X ω)ᴴ) 1 1 = G1ᴴ := by
    have e : (fun ω => blkAt (pTwo * (gRes b E X ω)ᴴ) 1 1) =
        fun ω => blkAt ((gRes b E X ω)ᴴ) 1 1 := funext fun ω => blkAt_portProj_mul_one _
    rw [blkAt_matrixExpect, e, ← blkAt_matrixExpect, hGs1]
  have hst : ‖(b : ℂ) * tTwo b E X 0‖ ≤ b * Cw := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have h := (hw W hWw X hX.posSemidef 2 le_rfl ![0, 2] ![1, pTwo, 1] norm_ins_le).2.2.2.2 0
    have e : (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2] ![1, pTwo, 1]) 0) =
        fun ω => blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) 0 :=
      funext fun ω => by rw [wordVal_GPGstar]
    rw [e] at h
    exact mul_le_mul_of_nonneg_left h hb0.le
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  constructor
  · have hb0' := (norm_blkAt_le _ 0 0).trans hT
    rw [blkAt_sub, bl0, blkAt_add, hP0, zero_add, hS0, hGs0] at hb0'
    have e : blkAt T 0 0 - sOne b E X • (mOf b E X * (mOf b E X)ᴴ) =
        (blkAt T 0 0 - mOf b E X * (sOne b E X • G0ᴴ)) +
          mOf b E X * (sOne b E X • (G0ᴴ - (mOf b E X)ᴴ)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, smul_sub]; abel
    have hs' : sOne b E X = ((1 - 2 * b : ℝ) : ℂ) * tTwo b E X 0 + (b : ℂ) * tTwo b E X 1 := rfl
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * (Cf * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add (by rw [hs']; exact hb0') ?_
          refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM ?_ (norm_nonneg _) hCD)
          refine (norm_smul_le _ _).trans (mul_le_mul hs ?_ (norm_nonneg _) hCf)
          rw [norm_conjTranspose_sub]; exact hE0
      _ ≤ _ := by
          rw [show Cu / (W : ℝ) ^ 2 + CD * (Cf * (CD / (W : ℝ) ^ 2)) =
            (Cu + CD * Cf * CD) / (W : ℝ) ^ 2 by ring]
          have : 0 ≤ CD * (1 + b * Cw) * CD := by positivity
          exact div_le_div_of_nonneg_right (by linarith) hW2
  · have hb1 := (norm_blkAt_le _ 1 1).trans hT
    rw [blkAt_sub, bl1, blkAt_add, hP1, hS1, hGs1] at hb1
    have e0 : G1ᴴ + ((b : ℂ) * tTwo b E X 0) • G1ᴴ = (1 + (b : ℂ) * tTwo b E X 0) • G1ᴴ := by
      rw [add_smul, one_smul]
    rw [e0] at hb1
    have e : blkAt T 1 1 - (vOf b E X * (1 + (b : ℂ) * tTwo b E X 0) * conj (vOf b E X)) • 1 =
        (blkAt T 1 1 - vOf b E X • ((1 + (b : ℂ) * tTwo b E X 0) • G1ᴴ)) +
          vOf b E X • ((1 + (b : ℂ) * tTwo b E X 0) • (G1ᴴ - (vOf b E X • 1)ᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_one, smul_sub, smul_sub, smul_smul, smul_smul]
      simp only [Complex.star_def, smul_smul, mul_assoc]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * ((1 + b * Cw) * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add hb1 ?_
          refine (norm_smul_le _ _).trans (mul_le_mul hv ?_ (norm_nonneg _) hCD)
          refine (norm_smul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity))
          · calc ‖1 + (b : ℂ) * tTwo b E X 0‖ ≤ ‖(1 : ℂ)‖ + ‖(b : ℂ) * tTwo b E X 0‖ :=
                  norm_add_le _ _
              _ ≤ 1 + b * Cw := by rw [norm_one]; linarith
          · rw [norm_conjTranspose_sub]; exact hE1
      _ ≤ _ := by
          rw [show Cu / (W : ℝ) ^ 2 + CD * ((1 + b * Cw) * (CD / (W : ℝ) ^ 2)) =
            (Cu + CD * (1 + b * Cw) * CD) / (W : ℝ) ^ 2 by ring]
          gcongr
          have : 0 ≤ CD * Cf * CD := by positivity
          linarith

/-- `k_h = c + b²h`. -/
def khOf (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ := ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * hOf b E X

/-- The scalar system for `s₁`: `t₁ = s₁A`, `t₂ = h(1 + bt₁)`, `s₁(1 - k_hA) = bh`, each up
to `C/W²`. -/
theorem scalarS1 (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖tTwo b E X 0 - sOne b E X * aOf b E X‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖tTwo b E X 1 - hOf b E X * (1 + (b : ℂ) * tTwo b E X 0)‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hB⟩ := scalarS1_blocks hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks hA hb0 hb h1 h2
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound hA hb0 hb h1 h2 2 1
  refine ⟨((1 - 2 * b) + b + b ^ 2 * (CD * CD) + 1) * C₁, max (max W₁ WD) Ww, by
    have : 0 ≤ 1 - 2 * b := by linarith
    positivity, fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWD⟩, hWw⟩ := hW
  obtain ⟨hW1, -, -, hv, -⟩ := hD W hWD X hX
  obtain ⟨hb00, hb11⟩ := hB W hW₁ X hX
  have hent := (hw W hWw X hX.posSemidef 2 le_rfl ![0, 2] ![1, pTwo, 1] norm_ins_le).1
  have hent' : ∀ α β, Integrable (fun ω => (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ) :
      LayerMat W) α β) (layerLaw W b .oneBlockOnePort) := fun α β => by
    have h := hent α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 2] ![1, pTwo, 1] α β) =
        fun ω => (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_GPGstar]
    rw [e] at h; exact h
  have ht : ∀ r, tTwo b E X r = blkTr (matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))) r := fun r => integral_blkTr _ hent' r
  have d1 : ‖tTwo b E X 0 - sOne b E X * aOf b E X‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    have h := (norm_blkTr_sub_le _ 0 _).trans hb00
    rw [trace_smul, smul_eq_mul, mul_left_comm, ← ht] at h
    exact h
  have d2 : ‖tTwo b E X 1 - hOf b E X * (1 + (b : ℂ) * tTwo b E X 0)‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    have h := (norm_blkTr_sub_le _ 1 _).trans hb11
    rw [normTrace_smul_one hW1, ← ht] at h
    have e : vOf b E X * (1 + (b : ℂ) * tTwo b E X 0) * conj (vOf b E X) =
        hOf b E X * (1 + (b : ℂ) * tTwo b E X 0) := by unfold hOf; ring
    rw [e] at h; exact h
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    positivity
  have hfac : 1 ≤ (1 - 2 * b) + b + b ^ 2 * (CD * CD) + 1 := by nlinarith [mul_nonneg hCD hCD]
  have hup : C₁ / (W : ℝ) ^ 2 ≤ ((1 - 2 * b) + b + b ^ 2 * (CD * CD) + 1) * C₁ / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left hC₁ hfac) hW2'.le
  refine ⟨d1.trans hup, d2.trans hup, ?_⟩
  have hh : ‖hOf b E X‖ ≤ CD * CD := by
    unfold hOf; rw [norm_mul, Complex.norm_conj]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  have e : sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X =
      ((1 - 2 * b : ℝ) : ℂ) * (tTwo b E X 0 - sOne b E X * aOf b E X) +
        (b : ℂ) * (tTwo b E X 1 - hOf b E X * (1 + (b : ℂ) * tTwo b E X 0)) +
        (b : ℂ) ^ 2 * hOf b E X * (tTwo b E X 0 - sOne b E X * aOf b E X) := by
    unfold khOf; rw [show sOne b E X = ((1 - 2 * b : ℝ) : ℂ) * tTwo b E X 0 +
      (b : ℂ) * tTwo b E X 1 from rfl]; ring
  rw [e]
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖((1 - 2 * b : ℝ) : ℂ) * (tTwo b E X 0 - sOne b E X * aOf b E X)‖ +
        ‖(b : ℂ) * (tTwo b E X 1 - hOf b E X * (1 + (b : ℂ) * tTwo b E X 0))‖ +
        ‖(b : ℂ) ^ 2 * hOf b E X * (tTwo b E X 0 - sOne b E X * aOf b E X)‖ :=
        norm_add₃_le
    _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ _ := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) =
            ((1 - 2 * b) + b + b ^ 2 * (CD * CD)) * C₁ / (W : ℝ) ^ 2 by ring]
        exact div_le_div_of_nonneg_right (by nlinarith) hW2'.le

end BlockBand.Transmission.SourceMixing
