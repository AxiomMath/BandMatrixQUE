module

public import BlockBand.Transmission.PassiveCovarianceBulk.M4Near
public import BlockBand.Transmission.PassiveCovariance.GamNear

/-!
# Bulk-uniform `τ̄ ↦ 1` and `E[γ'_k] ↦ (R, I)`

`τ̄ = 1 + O(δ + W⁻¹)` and `E[γ'_k] ↦ (R, I)`, with constants and `W₀` uniform in
`E ∈ bulkInterval κ`.
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

/-- **`τ̄ = 1 + O(δ + W⁻¹)`**.
Bulk-uniform copy of `tauNear_holds` (constants uniform on `bulkInterval κ`). -/
theorem tauNear_holds_bulk (hA : PassiveLayer.PassiveBoundsStatement) : TauNearBulk := by
  intro b hb0 hb κ hκ
  obtain ⟨d₀, C, W₀, hd₀, hC, hm⟩ := matchedScalars_bulk hA hb0 hb hκ
  refine ⟨d₀, C, max W₀ 1, hd₀, hC, fun W hW E hEκ s hs X hX hδ => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  obtain ⟨h0, he⟩ := jetDelta_bounds (b := b) (E := E) s hX.posSemidef hW1
  obtain ⟨-, -, hs1, -⟩ := hm W (le_trans (le_max_left _ _) hW) E hEκ s hs X hX (h0.trans hδ)
  rw [tauBar_eq_sOne]
  exact hs1.trans (mul_le_mul_of_nonneg_left he hC)

/-- **`E[γ'_k] ↦ (R, I)`**.
Bulk-uniform copy of `gamNear_holds` (constants uniform on `bulkInterval κ`). -/
theorem gamNear_holds_bulk (hA : PassiveLayer.PassiveBoundsStatement) : MeanNearBulk gamFam leadGam := by
  intro b hb0 hb κ hκ
  obtain ⟨d₀, C₀, W₀, hd₀, hC₀, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨d₁, C₁, W₁, hd₁, hC₁, hms⟩ := matchedScalars_bulk hA hb0 hb hκ
  obtain ⟨Cx, Wx, hCx, hmx⟩ := mixedBlock_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 2 1
  have hηL := etaLow_pos (b := b) (by linarith) hκ
  set ηi := (etaLow b κ)⁻¹
  set K := 1 + C₀ * (d₀ + 1)
  set C := Cx + (C₁ * C₀ * K + C₀ * K + ηi * C₀) + C₀
  refine ⟨min d₀ d₁, C, max (max (max W₀ W₁) (max Wx Ww)) 1, lt_min hd₀ hd₁, by positivity,
    fun W hW E hEκ s hs X hX hδ i u v => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW₀, hW₁⟩, hWx, hWw⟩, hW1⟩ := hW
  obtain ⟨h0, he⟩ := jetDelta_bounds (b := b) (E := E) s hX.posSemidef hW1
  have hδ0 := jetDelta_nonneg b E s hX.posSemidef
  have hWi1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW1)
  set ε := jetDelta b E s X + (W : ℝ)⁻¹
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ d₀ + 1 := add_le_add (hδ.trans (min_le_left _ _)) hWi1
  have hW2 : Cx / (W : ℝ) ^ 2 ≤ Cx * ε := by
    have : (W : ℝ)⁻¹ ^ 2 ≤ ε := by
      have : (W : ℝ)⁻¹ ^ 2 ≤ (W : ℝ)⁻¹ := by
        rw [pow_two]; exact mul_le_of_le_one_left (by positivity) hWi1
      linarith
    rw [div_eq_mul_inv, ← inv_pow]; exact mul_le_mul_of_nonneg_left this hCx
  obtain ⟨hMb, -, hR, hKM1, hMR, -⟩ := hmb W hW₀ E hEκ s X hX (h0.trans (hδ.trans (min_le_left _ _)))
  replace hR := hR.trans (inv_etaZ_le_bulk hb hκ hEκ)
  obtain ⟨-, -, hs1, -⟩ := hms W hW₁ E hEκ s hs X hX (h0.trans (hδ.trans (min_le_right _ _)))
  obtain ⟨hx0, hx1⟩ := hmx W hWx E hEκ X hX
  set KM := SourceMixing.kmOf b E X
  set M := SourceMixing.mOf b E X
  set R := passiveResolvent b E X
  have hK1 : ‖KM - 1‖ ≤ C₀ * ε := hKM1.trans (mul_le_mul_of_nonneg_left he hC₀)
  have hMR' : ‖M - R‖ ≤ C₀ * ε := hMR.trans (mul_le_mul_of_nonneg_left he hC₀)
  have hs1' : ‖SourceMixing.sOne b E X - 1‖ ≤ C₁ * ε := hs1.trans (mul_le_mul_of_nonneg_left he hC₁)
  have hKM : ‖KM‖ ≤ K := by
    have : ‖KM‖ ≤ ‖KM - 1‖ + ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ := by
      have := norm_add_le (KM - 1) 1; rwa [sub_add_cancel] at this
    have := norm_one_matrix_le (n := Fin W)
    have := mul_le_mul_of_nonneg_left hε1 hC₀
    linarith
  have hKMh : ‖KMᴴ‖ ≤ K := by rw [Matrix.l2_opNorm_conjTranspose]; exact hKM
  have hC0 : 0 ≤ C₀ := hC₀
  fin_cases i
  · -- `k = 0`: `E[𝒢Π(K̂𝒢)ᴴ]₁₁ ≈ s₁M·KMᴴ ≈ R`
    have hint := (hw W hWw E hEκ X hX.posSemidef 2 le_rfl ![0, 3] ![1, SourceMixing.pTwo, 1]
      SourceMixing.norm_ins_le).1
    have ef : gamFam 0 b E W X = fun ω =>
        gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ) := by
      funext ω; rw [gamFam_zero, SourceMixing.wordVal_GPKGstar]
    have hint' : ∀ i j, Integrable (fun ω => gamFam 0 b E W X ω i j)
        (layerLaw W b .oneBlockOnePort) := fun i j => by
      simp only [gamFam_zero]; exact hint i j
    show ‖(∫ ω, star (physVec u) ⬝ᵥ (gamFam 0 b E W X ω *ᵥ physVec v)
      ∂layerLaw W b .oneBlockOnePort) - bilinear u R v‖ ≤ _
    rw [integral_form _ hint', ef]
    refine norm_bilinear_sub_le u v _ _ ?_
    set s₁ := SourceMixing.sOne b E X
    have e : s₁ • (M * KMᴴ) - R = (s₁ - 1) • (M * KMᴴ) + (M - R) * KMᴴ + R * (KMᴴ - 1) := by
      rw [sub_smul, one_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one]; abel
    have hb1 : ‖s₁ • (M * KMᴴ) - R‖ ≤ (C₁ * C₀ * K + C₀ * K + ηi * C₀) * ε := by
      rw [e]
      have t1 : ‖(s₁ - 1) • (M * KMᴴ)‖ ≤ C₁ * ε * (C₀ * K) := by
        refine (norm_smul_le _ _).trans (mul_le_mul hs1' ((Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul hMb hKMh (norm_nonneg _) hC0)) (norm_nonneg _) (by positivity))
      have t2 : ‖(M - R) * KMᴴ‖ ≤ C₀ * ε * K :=
        (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hMR' hKMh (norm_nonneg _) (by positivity))
      have t3 : ‖R * (KMᴴ - 1)‖ ≤ ηi * (C₀ * ε) := by
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hR ?_ (norm_nonneg _) (by positivity))
        rw [← conjTranspose_one, ← conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]; exact hK1
      have := norm_add_le ((s₁ - 1) • (M * KMᴴ) + (M - R) * KMᴴ) (R * (KMᴴ - 1))
      have := norm_add_le ((s₁ - 1) • (M * KMᴴ)) ((M - R) * KMᴴ)
      nlinarith
    have := norm_sub_le_norm_sub_add_norm_sub (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ)) 0 0)
      (s₁ • (M * KMᴴ)) R
    have : 0 ≤ (C₁ * C₀ * K + C₀ * K + ηi * C₀) * ε + C₀ * ε := by positivity
    calc _ ≤ Cx / (W : ℝ) ^ 2 + (C₁ * C₀ * K + C₀ * K + ηi * C₀) * ε := by linarith
      _ ≤ C * ε := by
        have hCe : C * ε = Cx * ε + (C₁ * C₀ * K + C₀ * K + ηi * C₀) * ε + C₀ * ε := by
          simp only [C]; ring
        have hC0e : 0 ≤ C₀ * ε := mul_nonneg hC₀ hε0
        linarith
  · -- `k = 1`: `E[(K̂𝒢)ᴴ]₁₁ = ((K̂E𝒢)₁₁)ᴴ ≈ KMᴴ ≈ I`
    have hint := (hw W hWw E hEκ X hX.posSemidef 1 (by norm_num) ![0] ![1, 1]
      SourceMixing.norm_ins1_le).1
    have hG : ∀ i j, Integrable (fun ω => gRes b E X ω i j) (layerLaw W b .oneBlockOnePort) :=
      fun i j => by
        have h := hint i j
        rwa [show (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0] ![1, 1] i j) =
          fun ω => gRes b E X ω i j from funext fun ω => by rw [SourceMixing.wordVal_G1]] at h
    have hKG : ∀ i j, Integrable (fun ω => (kHat b E X * gRes b E X ω) i j)
        (layerLaw W b .oneBlockOnePort) := fun i j => by
      simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun k _ => (hG k j).const_mul _
    have ef : ∀ ω, star (physVec u) ⬝ᵥ (gamFam 1 b E W X ω *ᵥ physVec v) =
        conj (star (physVec v) ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ physVec u)) := fun ω => by
      rw [conj_form, gamFam_one]
      simp [wordVal_succ, wordVal_zero, wLetter]
    show ‖(∫ ω, star (physVec u) ⬝ᵥ (gamFam 1 b E W X ω *ᵥ physVec v)
      ∂layerLaw W b .oneBlockOnePort) - bilinear u 1 v‖ ≤ _
    simp only [ef]
    rw [integral_conj, integral_form _ hKG, conj_bilinear, ← SourceMixing.mul_matrixExpect' _ _ hG]
    refine norm_bilinear_sub_le u v _ _ ?_
    rw [← conjTranspose_one, ← conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    have := norm_sub_le_norm_sub_add_norm_sub
      (blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0) KM 1
    calc _ ≤ Cx / (W : ℝ) ^ 2 + C₀ * ε := by linarith
      _ ≤ C * ε := by
        have : 0 ≤ (C₁ * C₀ * K + C₀ * K + ηi * C₀) * ε := by positivity
        have hCe : C * ε = Cx * ε + (C₁ * C₀ * K + C₀ * K + ηi * C₀) * ε + C₀ * ε := by
          simp only [C]; ring
        linarith

end BlockBand.Transmission.CovarianceBulk
