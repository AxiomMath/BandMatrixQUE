module

public import BlockBand.Transmission.SourceMixingBulk.Scalars
public import BlockBand.Transmission.SourceMixing.ScalarTheta
public import BlockBand.Transmission.LengthUniform.BulkScalarS1

/-!
# The scalar system for `θ`, uniformly on the bulk

The estimates `scalarTheta_blocks` and `scalarTheta` with constants uniform in `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixingBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The blocks of `E[𝒢P₂𝒢]`.
The version of `scalarTheta_blocks` with constants uniform on `bulkInterval κ`. -/
theorem scalarTheta_blocks_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        (∀ r, ‖tauTwo b E X r‖ ≤ C) ∧ ‖thetaOf b E X‖ ≤ C ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω) : LayerMat W) α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω))) 0 0 -
          thetaOf b E X • (mOf b E X * mOf b E X)‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω))) 1 1 -
          (vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * vOf b E X) • 1‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedExpansion_bulk hA hb0 hb hκ 1 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 2 1
  set Ct := (1 - 2 * b) * Cw + b * Cw
  have hCt : 0 ≤ Ct := by have : 0 ≤ 1 - 2 * b := by linarith
                          positivity
  refine ⟨Cw + Ct + (Cu + CD * Ct * CD + CD * (1 + b * Cw) * CD), max (max Wu WD) Ww,
    by positivity, fun W hW E hEκ X hX => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWu, hWD⟩, hWw⟩ := hW
  obtain ⟨-, -, hM, hv, bl0, bl1, hE0, hE1, -, -, -⟩ := hD W hWD E hEκ X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw E hEκ X hX.posSemidef 2 le_rfl ![0, 0] ![1, SourceMixing.pTwo, 1] norm_ins_le
  have ht : ∀ r, ‖tauTwo b E X r‖ ≤ Cw := fun r => by
    have h := hwt.2.2.2.2 r
    have e : (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 0] ![1, SourceMixing.pTwo, 1]) r) =
        fun ω => blkTr (gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω)) r :=
      funext fun ω => by rw [wordVal_GPG]
    rw [e] at h; exact h
  have hth : ‖thetaOf b E X‖ ≤ Ct := by
    unfold thetaOf
    have hb1 : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hb2 : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hb1, hb2]
    have : 0 ≤ 1 - 2 * b := by linarith
    exact add_le_add (mul_le_mul_of_nonneg_left (ht 0) this) (mul_le_mul_of_nonneg_left (ht 1) hb0.le)
  have hent : ∀ α β, Integrable (fun ω => (gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω) : LayerMat W) α β)
      μ := fun α β => by
    have h := hwt.1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 0] ![1, SourceMixing.pTwo, 1] α β) =
        fun ω => (gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_GPG]
    rw [e] at h; exact h
  have hCwle : Cw ≤ Cw + Ct + (Cu + CD * Ct * CD + CD * (1 + b * Cw) * CD) := by
    have : 0 ≤ Cu + CD * Ct * CD + CD * (1 + b * Cw) * CD := by positivity
    linarith
  refine ⟨fun r => (ht r).trans hCwle, hth.trans (by
    have : 0 ≤ Cu + CD * Ct * CD + CD * (1 + b * Cw) * CD := by positivity
    linarith), hent, ?_⟩
  have hT := hU W hWu E hEκ X hX 1 le_rfl wdG dStar2 norm_dStar2_le
  rw [Fin.sum_univ_one] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wdG dStar2) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω) := funext fun ω => by rw [wordVal_PG]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) wdG dStar2) =
      fun ω => SourceMixing.pTwo * gRes b E X ω := funext fun ω => by rw [wordVal_PG]
  have e3 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 1 wdG dStar2 0) r) =
      fun ω => blkTr (gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω)) r :=
    fun r => funext fun ω => by rw [wordAlpha_PG]
  have e4 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 1 wdG dStar2 0) =
      fun ω => gRes b E X ω := funext fun ω => by rw [wordGamma_PG]
  rw [e1, e2, e3 0, e3 1, e4] at hT
  have et : ∀ r, (∫ ω, blkTr (gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω)) r ∂μ) = tauTwo b E X r :=
    fun r => rfl
  rw [et 0, et 1] at hT
  set T := matrixExpect μ (fun ω => gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω))
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  obtain ⟨hS0, hS1⟩ := blkAt_selfEnergy_mul (W := W) b (tauTwo b E X 0) (tauTwo b E X 1)
    (matrixExpect μ fun ω => gRes b E X ω)
  have hP0 : blkAt (matrixExpect μ fun ω => SourceMixing.pTwo * gRes b E X ω) 0 0 = 0 := by
    have e : (fun ω => blkAt (SourceMixing.pTwo * gRes b E X ω) 0 0) =
        fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) := funext fun ω => blkAt_portProj_mul_zero _ 0
    rw [blkAt_matrixExpect, e]; ext x y; simp [matrixExpect]
  have hP1 : blkAt (matrixExpect μ fun ω => SourceMixing.pTwo * gRes b E X ω) 1 1 = G1 := by
    have e : (fun ω => blkAt (SourceMixing.pTwo * gRes b E X ω) 1 1) =
        fun ω => blkAt (gRes b E X ω) 1 1 := funext fun ω => blkAt_portProj_mul_one _
    rw [blkAt_matrixExpect, e]; rfl
  have hst : ‖(b : ℂ) * tauTwo b E X 0‖ ≤ b * Cw := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    exact mul_le_mul_of_nonneg_left (ht 0) hb0.le
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  have hrest : 0 ≤ Cw + Ct := by positivity
  constructor
  · have hb0' := (norm_blkAt_le _ 0 0).trans hT
    rw [blkAt_sub, bl0, blkAt_add, hP0, zero_add, hS0] at hb0'
    have e : blkAt T 0 0 - thetaOf b E X • (mOf b E X * mOf b E X) =
        (blkAt T 0 0 - mOf b E X * (thetaOf b E X • G0)) +
          mOf b E X * (thetaOf b E X • (G0 - mOf b E X)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * (Ct * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add hb0' ?_
          refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM ?_ (norm_nonneg _) hCD)
          exact (norm_smul_le _ _).trans (mul_le_mul hth hE0 (norm_nonneg _) hCt)
      _ ≤ _ := by
          rw [show Cu / (W : ℝ) ^ 2 + CD * (Ct * (CD / (W : ℝ) ^ 2)) =
            (Cu + CD * Ct * CD) / (W : ℝ) ^ 2 by ring]
          have : 0 ≤ CD * (1 + b * Cw) * CD := by positivity
          exact div_le_div_of_nonneg_right (by linarith) hW2
  · have hb1 := (norm_blkAt_le _ 1 1).trans hT
    rw [blkAt_sub, bl1, blkAt_add, hP1, hS1] at hb1
    have e0 : G1 + ((b : ℂ) * tauTwo b E X 0) • G1 = (1 + (b : ℂ) * tauTwo b E X 0) • G1 := by
      rw [add_smul, one_smul]
    rw [e0] at hb1
    have e : blkAt T 1 1 - (vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * vOf b E X) • 1 =
        (blkAt T 1 1 - vOf b E X • ((1 + (b : ℂ) * tauTwo b E X 0) • G1)) +
          vOf b E X • ((1 + (b : ℂ) * tauTwo b E X 0) • (G1 - vOf b E X • 1)) := by
      simp only [smul_sub, smul_smul, mul_assoc]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * ((1 + b * Cw) * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add hb1 ?_
          refine (norm_smul_le _ _).trans (mul_le_mul hv ?_ (norm_nonneg _) hCD)
          refine (norm_smul_le _ _).trans (mul_le_mul ?_ hE1 (norm_nonneg _) (by positivity))
          calc ‖1 + (b : ℂ) * tauTwo b E X 0‖ ≤ ‖(1 : ℂ)‖ + ‖(b : ℂ) * tauTwo b E X 0‖ :=
                norm_add_le _ _
            _ ≤ 1 + b * Cw := by rw [norm_one]; linarith
      _ ≤ _ := by
          rw [show Cu / (W : ℝ) ^ 2 + CD * ((1 + b * Cw) * (CD / (W : ℝ) ^ 2)) =
            (Cu + CD * (1 + b * Cw) * CD) / (W : ℝ) ^ 2 by ring]
          have : 0 ≤ CD * Ct * CD := by positivity
          exact div_le_div_of_nonneg_right (by linarith) hW2

/-- The scalar system for `θ`: `τ₁ = θ⟨M²⟩`, `τ₂ = v²(1 + bτ₁)`,
`θ(1 - k_v⟨M²⟩) = bv²`, each up to `C/W²`.
The version of `scalarTheta` with constants uniform on `bulkInterval κ`. -/
theorem scalarTheta_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖tauTwo b E X 0 - thetaOf b E X * m2Of b E X‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖tauTwo b E X 1 - vOf b E X ^ 2 * (1 + (b : ℂ) * tauTwo b E X 0)‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖thetaOf b E X * (1 - kvOf b E X * m2Of b E X) - (b : ℂ) * vOf b E X ^ 2‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hB⟩ := scalarTheta_blocks_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨(K + 1) * C₁, max W₁ WD, by positivity, fun W hW E hEκ X hX => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  obtain ⟨hW1, -, -, hv, -⟩ := hD W (le_trans (le_max_right _ _) hW) E hEκ X hX
  obtain ⟨-, -, hent, hb00, hb11⟩ := hB W (le_trans (le_max_left _ _) hW) E hEκ X hX
  have ht : ∀ r, tauTwo b E X r = blkTr (matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω))) r := fun r => integral_blkTr _ hent r
  have d1 : ‖tauTwo b E X 0 - thetaOf b E X * m2Of b E X‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    have h := (norm_blkTr_sub_le _ 0 _).trans hb00
    rw [trace_smul, smul_eq_mul, mul_left_comm, ← ht] at h
    exact h
  have d2 : ‖tauTwo b E X 1 - vOf b E X ^ 2 * (1 + (b : ℂ) * tauTwo b E X 0)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    have h := (norm_blkTr_sub_le _ 1 _).trans hb11
    rw [normTrace_smul_one hW1, ← ht] at h
    have e : vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * vOf b E X =
        vOf b E X ^ 2 * (1 + (b : ℂ) * tauTwo b E X 0) := by ring
    rw [e] at h; exact h
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    positivity
  have hup : C₁ / (W : ℝ) ^ 2 ≤ (K + 1) * C₁ / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left hC₁ (by linarith)) hW2'.le
  refine ⟨d1.trans hup, d2.trans hup, ?_⟩
  have hh : ‖vOf b E X‖ ^ 2 ≤ CD * CD := by
    rw [sq]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  have e : thetaOf b E X * (1 - kvOf b E X * m2Of b E X) - (b : ℂ) * vOf b E X ^ 2 =
      ((1 - 2 * b : ℝ) : ℂ) * (tauTwo b E X 0 - thetaOf b E X * m2Of b E X) +
        (b : ℂ) * (tauTwo b E X 1 - vOf b E X ^ 2 * (1 + (b : ℂ) * tauTwo b E X 0)) +
        (b : ℂ) ^ 2 * vOf b E X ^ 2 * (tauTwo b E X 0 - thetaOf b E X * m2Of b E X) := by
    unfold kvOf; rw [show thetaOf b E X = ((1 - 2 * b : ℝ) : ℂ) * tauTwo b E X 0 +
      (b : ℂ) * tauTwo b E X 1 from rfl]; ring
  rw [e]
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖((1 - 2 * b : ℝ) : ℂ) * (tauTwo b E X 0 - thetaOf b E X * m2Of b E X)‖ +
        ‖(b : ℂ) * (tauTwo b E X 1 - vOf b E X ^ 2 * (1 + (b : ℂ) * tauTwo b E X 0))‖ +
        ‖(b : ℂ) ^ 2 * vOf b E X ^ 2 * (tauTwo b E X 0 - thetaOf b E X * m2Of b E X)‖ :=
        norm_add₃_le
    _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        simp only [norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ _ := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) = K * C₁ / (W : ℝ) ^ 2 by ring]
        exact div_le_div_of_nonneg_right (by nlinarith) hW2'.le

end BlockBand.Transmission.SourceMixingBulk
