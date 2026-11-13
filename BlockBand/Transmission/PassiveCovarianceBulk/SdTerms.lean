module

public import BlockBand.Transmission.PassiveCovarianceBulk.SdBase
public import BlockBand.Transmission.PassiveCovariance.SdSelf
public import BlockBand.Transmission.PassiveCovariance.SdLetter

/-!
# Bulk-uniform self-energy and letter terms

The centred self-energy terms and the letter-trace terms of the first-letter expansion, for
`Ψ = 1` and `Ψ = Q⁰`, with constants and `W₀` uniform in `E ∈ bulkInterval κ`.
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
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The centred self-energy term, `Ψ = 1`**: `|E[x*(S[𝔊] - S̄)𝔊Nc]| ≤ (C/W²)‖x‖‖c‖`.
Bulk-uniform copy of `selfTerm_one` (constants uniform on `bulkInterval κ`). -/
theorem selfTerm_one_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) → ∀ x c : LayerSite W .oneBlockOnePort → ℂ,
        ‖∫ ω, star x ⬝ᵥ (((sdiag b (gSide b E X adj ω) - sbarSide b E X adj) * gSide b E X adj ω *
            wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) ∂layerLaw W b .oneBlockOnePort‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm c) := by
  obtain ⟨C, W₀, hC, h⟩ := layerTrace_dressedCov_bulk hA hb0 hb hκ (Lw + 1) (max Kd 1)
  refine ⟨2 * C, W₀, by positivity, fun W hW E hEκ X hX ℓ hℓ wd D hD x c => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  set μ := layerLaw W b .oneBlockOnePort
  have hD1 : ∀ q : Fin 2, ∀ j, ‖(Fin.cons (dRow b q) D : Fin (ℓ + 1 + 1) → LayerMat W) j‖ ≤ max Kd 1 :=
    fun q j => Fin.cases ((norm_dRow_le hb0 hb q).trans (le_max_right _ _))
      (fun k => (hD k).trans (le_max_left _ _)) j
  have h11 : ∀ j, ‖(![1, 1] : Fin 2 → LayerMat W) j‖ ≤ max Kd 1 := fun j => by
    fin_cases j <;> exact norm_one_matrix_le.trans (le_max_right _ _)
  have hq := fun q : Fin 2 => h W hW E hEκ X hX (ℓ + 1) (by omega) (Fin.cons (sideLetter adj) wd)
    (Fin.cons (dRow b q) D) (hD1 q) 1 (by omega) ![sideLetter adj] ![1, 1] h11 q x c
  simp only [selfTerm_pt hb0.le hb E X adj wd D x c, blkTr_side_word]
  rw [integral_finsetSum _ fun q _ => by
    simp_rw [sub_mul]
    exact (hq q).2.2.1.sub ((hq q).2.1.const_mul _)]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ q : Fin 2, ‖∫ ω, ((W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω) ![sideLetter adj]
        ![1, 1]) q q).trace - ∫ ω', (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω')
          ![sideLetter adj] ![1, 1]) q q).trace ∂μ) * wordForm (kHat b E X) x c
          (Fin.cons (sideLetter adj) wd) (Fin.cons (dRow b q) D) (gRes b E X ω) ∂μ‖
      ≤ ∑ _q : Fin 2, C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm c) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [integral_centred_mul (hq q).2.1 (hq q).2.2.1]
        exact (hq q).2.2.2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **The centred self-energy term, `Ψ = Q⁰`**: for `Q = u*w₂(𝒢)v` and `‖c‖‖u‖ ≤ 1`,
`|E[(x*(S[𝔊] - S̄)𝔊Nc)(Q - EQ)]| ≤ (C/W²)‖x‖‖v‖`.
Bulk-uniform copy of `selfTerm_Q` (constants uniform on `bulkInterval κ`). -/
theorem selfTerm_Q_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) → ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw →
      ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W), (∀ j, ‖D₂ j‖ ≤ Kd) →
      ∀ x c u v : LayerSite W .oneBlockOnePort → ℂ, vecNorm c * vecNorm u ≤ 1 →
        ‖∫ ω, star x ⬝ᵥ (((sdiag b (gSide b E X adj ω) - sbarSide b E X adj) * gSide b E X adj ω *
            wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) *
            (wordForm (kHat b E X) u v wd₂ D₂ (gRes b E X ω) -
              ∫ ω', wordForm (kHat b E X) u v wd₂ D₂ (gRes b E X ω') ∂layerLaw W b .oneBlockOnePort)
            ∂layerLaw W b .oneBlockOnePort‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) := by
  obtain ⟨C₁, W₁, hC₁, h⟩ := layerTrace_dressedCov_bulk hA hb0 hb hκ (Lw + 1) (max Kd 1)
  obtain ⟨C₂, W₂, hC₂, hp⟩ := layerTrace_cov_prod_bulk hA hb0 hb hκ (Lw + 1) (max Kd 1)
  obtain ⟨C₃, W₃, hC₃, hm⟩ := norm_integral_poly_le_bulk hA hb0 hb hκ (Lw + 1)
  set K1 := max Kd 1 ^ (Lw + 1)
  refine ⟨2 * (C₂ + K1 * C₃ * C₁), max W₁ (max W₂ W₃), by positivity,
    fun W hW E hEκ X hX ℓ hℓ wd D hD ℓ₂ hℓ₂ wd₂ D₂ hD₂ x c u v hcu => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  set μ := layerLaw W b .oneBlockOnePort
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  have hD1 : ∀ q : Fin 2, ∀ j, ‖(Fin.cons (dRow b q) D : Fin (ℓ + 1 + 1) → LayerMat W) j‖ ≤ max Kd 1 :=
    fun q j => Fin.cases ((norm_dRow_le hb0 hb q).trans (le_max_right _ _))
      (fun k => (hD k).trans (le_max_left _ _)) j
  have h11 : ∀ j, ‖(![1, 1] : Fin 2 → LayerMat W) j‖ ≤ max Kd 1 := fun j => by
    fin_cases j <;> exact norm_one_matrix_le.trans (le_max_right _ _)
  have hD₂' : ∀ j, ‖D₂ j‖ ≤ max Kd 1 := fun j => (hD₂ j).trans (le_max_left _ _)
  set Q := fun ω => wordForm (kHat b E X) u v wd₂ D₂ (gRes b E X ω)
  have hQb : ‖∫ ω, Q ω ∂μ‖ ≤ K1 * (vecNorm u * vecNorm v) * C₃ := hm W hW3 E hEκ X hX Q _ (Lw + 1) le_rfl
    fun ω => (wordForm_poly_bounds b E X hKd hℓ₂ wd₂ D₂ hD₂ u v ω).1
  have hq := fun q : Fin 2 => h W hW1 E hEκ X hX (ℓ + 1) (by omega) (Fin.cons (sideLetter adj) wd)
    (Fin.cons (dRow b q) D) (hD1 q) 1 (by omega) ![sideLetter adj] ![1, 1] h11 q x c
  have hpq := fun q : Fin 2 => hp W hW2 E hEκ X hX (ℓ + 1) (by omega) (Fin.cons (sideLetter adj) wd)
    (Fin.cons (dRow b q) D) (hD1 q) ℓ₂ (by omega) wd₂ D₂ hD₂' 1 (by omega) ![sideLetter adj] ![1, 1]
    h11 q x c u v hcu
  set τ := fun (q : Fin 2) ω => (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω)
    ![sideLetter adj] ![1, 1]) q q).trace
  set F := fun (q : Fin 2) ω => wordForm (kHat b E X) x c (Fin.cons (sideLetter adj) wd)
    (Fin.cons (dRow b q) D) (gRes b E X ω)
  have hpt : ∀ ω, (∑ q : Fin 2, (τ q ω - ∫ ω', τ q ω' ∂μ) * F q ω) * (Q ω - ∫ ω', Q ω' ∂μ) =
      ∑ q : Fin 2, (((τ q ω - ∫ ω', τ q ω' ∂μ) * (F q ω * Q ω)) -
        (∫ ω', Q ω' ∂μ) * ((τ q ω - ∫ ω', τ q ω' ∂μ) * F q ω)) := fun ω => by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun q _ => by ring
  have i1 : ∀ q, Integrable (fun ω => (τ q ω - ∫ ω', τ q ω' ∂μ) * (F q ω * Q ω)) μ := fun q => by
    simp_rw [sub_mul]; exact (hpq q).2.1.sub ((hpq q).1.const_mul _)
  have i2 : ∀ q, Integrable (fun ω => (τ q ω - ∫ ω', τ q ω' ∂μ) * F q ω) μ := fun q => by
    simp_rw [sub_mul]; exact (hq q).2.2.1.sub ((hq q).2.1.const_mul _)
  simp only [selfTerm_pt hb0.le hb E X adj wd D x c, blkTr_side_word]
  change ‖∫ ω, (∑ q : Fin 2, (τ q ω - ∫ ω', τ q ω' ∂μ) * F q ω) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ‖ ≤ _
  simp only [hpt]
  have i12 : ∀ q, Integrable (fun ω => (τ q ω - ∫ ω', τ q ω' ∂μ) * (F q ω * Q ω) -
      (∫ ω', Q ω' ∂μ) * ((τ q ω - ∫ ω', τ q ω' ∂μ) * F q ω)) μ := fun q =>
    (i1 q).sub ((i2 q).const_mul _)
  rw [integral_finsetSum _ fun q _ => i12 q]
  refine (norm_sum_le _ _).trans ?_
  have hxc : vecNorm x * vecNorm c * (vecNorm u * vecNorm v) ≤ vecNorm x * vecNorm v := by
    have := vecNorm_nonneg x; have := vecNorm_nonneg v
    calc vecNorm x * vecNorm c * (vecNorm u * vecNorm v) = vecNorm x * vecNorm v *
        (vecNorm c * vecNorm u) := by ring
      _ ≤ vecNorm x * vecNorm v * 1 := mul_le_mul_of_nonneg_left hcu (by positivity)
      _ = _ := by ring
  calc ∑ q : Fin 2, ‖∫ ω, ((τ q ω - ∫ ω', τ q ω' ∂μ) * (F q ω * Q ω) -
        (∫ ω', Q ω' ∂μ) * ((τ q ω - ∫ ω', τ q ω' ∂μ) * F q ω)) ∂μ‖
      ≤ ∑ _q : Fin 2, (C₂ + K1 * C₃ * C₁) / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [integral_sub (i1 q) ((i2 q).const_mul _), integral_const_mul (∫ ω', Q ω' ∂μ),
          integral_centred_mul (hpq q).1 (hpq q).2.1, integral_centred_mul (hq q).2.1 (hq q).2.2.1]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
        have hb1 := (hpq q).2.2
        have hb2 := (hq q).2.2.2
        have hW0 : (0 : ℝ) ≤ 1 / (W : ℝ) ^ 2 := by positivity
        calc _ ≤ C₂ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) +
              K1 * (vecNorm u * vecNorm v) * C₃ * (C₁ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm c)) :=
              add_le_add hb1 (mul_le_mul hQb hb2 (norm_nonneg _) (by
                have := vecNorm_nonneg u; have := vecNorm_nonneg v
                have : 0 ≤ K1 := by positivity
                positivity))
          _ = C₂ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) +
              K1 * C₃ * C₁ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm c * (vecNorm u * vecNorm v)) := by
              ring
          _ ≤ C₂ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) +
              K1 * C₃ * C₁ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) := by gcongr
          _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Trace centring against `F·Q⁰`.**
Bulk-uniform copy of `traceQ_centre` (constants uniform on `bulkInterval κ`). -/
theorem traceQ_centre_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      ∀ ℓ₁ : ℕ, ℓ₁ ≤ Lw → ∀ (wd₁ : Fin ℓ₁ → Fin 4) (D₁ : Fin (ℓ₁ + 1) → LayerMat W), (∀ j, ‖D₁ j‖ ≤ Kd) →
      ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw → ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W), (∀ j, ‖D₂ j‖ ≤ Kd) →
      ∀ ℓ' : ℕ, ℓ' ≤ Lw → ∀ (wd' : Fin ℓ' → Fin 4) (D' : Fin (ℓ' + 1) → LayerMat W), (∀ j, ‖D' j‖ ≤ Kd) →
      ∀ (q : Fin 2) (x c u v : LayerSite W .oneBlockOnePort → ℂ), vecNorm c * vecNorm u ≤ 1 →
        let μ := layerLaw W b .oneBlockOnePort
        let τ := fun ω => (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω) wd' D') q q).trace
        let F := fun ω => wordForm (kHat b E X) x c wd₁ D₁ (gRes b E X ω)
        let Q := fun ω => wordForm (kHat b E X) u v wd₂ D₂ (gRes b E X ω)
        Integrable (fun ω => F ω * (Q ω - ∫ ω', Q ω' ∂μ)) μ ∧
        Integrable (fun ω => τ ω * (F ω * (Q ω - ∫ ω', Q ω' ∂μ))) μ ∧
        ‖∫ ω, τ ω * (F ω * (Q ω - ∫ ω', Q ω' ∂μ)) ∂μ -
            (∫ ω, τ ω ∂μ) * ∫ ω, F ω * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) := by
  obtain ⟨C₁, W₁, hC₁, h⟩ := layerTrace_dressedCov_bulk hA hb0 hb hκ Lw Kd
  obtain ⟨C₂, W₂, hC₂, hp⟩ := layerTrace_cov_prod_bulk hA hb0 hb hκ Lw Kd
  obtain ⟨C₃, W₃, hC₃, hm⟩ := norm_integral_poly_le_bulk hA hb0 hb hκ (Lw + 1)
  set K1 := max Kd 1 ^ (Lw + 1)
  refine ⟨C₂ + K1 * C₃ * C₁, max W₁ (max W₂ W₃), by positivity,
    fun W hW E hEκ X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ ℓ' hℓ' wd' D' hD' q x c u v hcu => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  intro μ τ F Q
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD₁ 0)
  obtain ⟨-, hFi, hτF, hb2⟩ := h W hW1 E hEκ X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ' hℓ' wd' D' hD' q x c
  obtain ⟨hFQ, hτFQ, hb1⟩ := hp W hW2 E hEκ X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ ℓ' hℓ' wd' D' hD'
    q x c u v hcu
  have hQb : ‖∫ ω, Q ω ∂μ‖ ≤ K1 * (vecNorm u * vecNorm v) * C₃ := hm W hW3 E hEκ X hX Q _ (Lw + 1) le_rfl
    fun ω => (wordForm_poly_bounds b E X hKd hℓ₂ wd₂ D₂ hD₂ u v ω).1
  set a := ∫ ω, Q ω ∂μ
  have e1 : (fun ω => F ω * (Q ω - a)) = fun ω => F ω * Q ω - a * F ω := by
    funext ω; ring
  have e2 : (fun ω => τ ω * (F ω * (Q ω - a))) = fun ω => τ ω * (F ω * Q ω) - a * (τ ω * F ω) := by
    funext ω; ring
  have i1 : Integrable (fun ω => F ω * (Q ω - a)) μ := by rw [e1]; exact hFQ.sub (hFi.const_mul a)
  have i2 : Integrable (fun ω => τ ω * (F ω * (Q ω - a))) μ := by
    rw [e2]; exact hτFQ.sub (hτF.const_mul a)
  refine ⟨i1, i2, ?_⟩
  rw [e1, e2, integral_sub hτFQ (hτF.const_mul a), integral_sub hFQ (hFi.const_mul a),
    integral_const_mul a (fun ω => τ ω * F ω), integral_const_mul a F]
  have hrw : ∫ ω, τ ω * (F ω * Q ω) ∂μ - a * ∫ ω, τ ω * F ω ∂μ -
      (∫ ω, τ ω ∂μ) * (∫ ω, F ω * Q ω ∂μ - a * ∫ ω, F ω ∂μ) =
      (∫ ω, τ ω * (F ω * Q ω) ∂μ - (∫ ω, τ ω ∂μ) * ∫ ω, F ω * Q ω ∂μ) -
        a * (∫ ω, τ ω * F ω ∂μ - (∫ ω, τ ω ∂μ) * ∫ ω, F ω ∂μ) := by ring
  rw [hrw]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have hxc : vecNorm x * vecNorm c * (vecNorm u * vecNorm v) ≤ vecNorm x * vecNorm v := by
    have := vecNorm_nonneg x; have := vecNorm_nonneg v
    calc vecNorm x * vecNorm c * (vecNorm u * vecNorm v) = vecNorm x * vecNorm v *
        (vecNorm c * vecNorm u) := by ring
      _ ≤ vecNorm x * vecNorm v * 1 := mul_le_mul_of_nonneg_left hcu (by positivity)
      _ = _ := by ring
  have hK1 : 0 ≤ K1 := by positivity
  have := vecNorm_nonneg u; have := vecNorm_nonneg v
  calc _ ≤ C₂ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) +
        K1 * (vecNorm u * vecNorm v) * C₃ * (C₁ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm c)) :=
        add_le_add hb1 (mul_le_mul hQb hb2 (norm_nonneg _) (by positivity))
    _ = C₂ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) +
        K1 * C₃ * C₁ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm c * (vecNorm u * vecNorm v)) := by ring
    _ ≤ C₂ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) +
        K1 * C₃ * C₁ / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) := by gcongr
    _ = _ := by ring

/-- **The letter-trace term, `Ψ = 1`.**
Bulk-uniform copy of `letterTerm_one` (constants uniform on `bulkInterval κ`). -/
theorem letterTerm_one_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) →
      ∀ x c : LayerSite W .oneBlockOnePort → ℂ, ∀ j : Fin ℓ,
        let μ := layerLaw W b .oneBlockOnePort
        let α := fun ω => wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j
        let γ := fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j
        Integrable (fun ω => star x ⬝ᵥ ((sdiag b (gSide b E X adj ω * α ω) * γ ω) *ᵥ c)) μ ∧
        (∀ q : Fin 2, Integrable (fun ω => star x ⬝ᵥ ((dRow b q * γ ω) *ᵥ c)) μ) ∧
        ‖∫ ω, star x ⬝ᵥ ((sdiag b (gSide b E X adj ω * α ω) * γ ω) *ᵥ c) ∂μ -
          ∑ q : Fin 2, (∫ ω, SourceMixing.blkTr (gSide b E X adj ω * α ω) q ∂μ) *
            ∫ ω, star x ⬝ᵥ ((dRow b q * γ ω) *ᵥ c) ∂μ‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm c) := by
  obtain ⟨C, W₀, hC, h⟩ := layerTrace_dressedCov_bulk hA hb0 hb hκ (Lw + 1) (max Kd 1)
  refine ⟨2 * C, W₀, by positivity, fun W hW E hEκ X hX ℓ hℓ wd D hD x c j => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  intro μ α γ
  obtain ⟨ℓA, wdA, DA, ℓG, wdG, DG, hlA, hlG, hDA, -, hDP, hτ, hF⟩ :=
    letter_words b E X adj hb0 hb wd D hD j
  have hc := fun q : Fin 2 => h W hW E hEκ X hX ℓG (by omega) wdG (preD (dRow b q) DG) (hDP q)
    (ℓA + 1) (by omega) (Fin.cons (sideLetter adj) wdA) (Fin.cons 1 DA)
    (norm_cons_one_le (le_max_right _ _) hDA) q x c
  set τ := fun (q : Fin 2) ω => (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω)
    (Fin.cons (sideLetter adj) wdA) (Fin.cons 1 DA)) q q).trace
  set F := fun (q : Fin 2) ω => wordForm (kHat b E X) x c wdG (preD (dRow b q) DG) (gRes b E X ω)
  have hpt : ∀ ω, star x ⬝ᵥ ((sdiag b (gSide b E X adj ω * α ω) * γ ω) *ᵥ c) =
      ∑ q : Fin 2, τ q ω * F q ω := fun ω => by
    rw [letter_pt hb0.le hb]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hτ ω q, hF ω q x c]
  have hFq : ∀ q, (fun ω => star x ⬝ᵥ ((dRow b q * γ ω) *ᵥ c)) = F q := fun q =>
    funext fun ω => hF ω q x c
  have hτq : ∀ q, (fun ω => SourceMixing.blkTr (gSide b E X adj ω * α ω) q) = τ q :=
    fun q => funext fun ω => hτ ω q
  have hI : Integrable (fun ω => ∑ q : Fin 2, τ q ω * F q ω) μ :=
    integrable_finsetSum _ fun q _ => (hc q).2.2.1
  refine ⟨by simp only [hpt]; exact hI, fun q => by rw [hFq q]; exact (hc q).2.1, ?_⟩
  simp only [hpt, hFq, hτq]
  rw [integral_finsetSum _ fun q _ => (hc q).2.2.1, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ q : Fin 2, ‖∫ ω, τ q ω * F q ω ∂μ - (∫ ω, τ q ω ∂μ) * ∫ ω, F q ω ∂μ‖
      ≤ ∑ _q : Fin 2, C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm c) :=
        Finset.sum_le_sum fun q _ => (hc q).2.2.2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **The letter-trace term, `Ψ = Q⁰`.**
Bulk-uniform copy of `letterTerm_Q` (constants uniform on `bulkInterval κ`). -/
theorem letterTerm_Q_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) → ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw →
      ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W), (∀ j, ‖D₂ j‖ ≤ Kd) →
      ∀ x c u v : LayerSite W .oneBlockOnePort → ℂ, vecNorm c * vecNorm u ≤ 1 → ∀ j : Fin ℓ,
        let μ := layerLaw W b .oneBlockOnePort
        let Q := fun ω => wordForm (kHat b E X) u v wd₂ D₂ (gRes b E X ω)
        let α := fun ω => wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j
        let γ := fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j
        Integrable (fun ω => star x ⬝ᵥ ((sdiag b (gSide b E X adj ω * α ω) * γ ω) *ᵥ c) *
          (Q ω - ∫ ω', Q ω' ∂μ)) μ ∧
        (∀ q : Fin 2, Integrable (fun ω => star x ⬝ᵥ ((dRow b q * γ ω) *ᵥ c) *
          (Q ω - ∫ ω', Q ω' ∂μ)) μ) ∧
        ‖∫ ω, star x ⬝ᵥ ((sdiag b (gSide b E X adj ω * α ω) * γ ω) *ᵥ c) *
            (Q ω - ∫ ω', Q ω' ∂μ) ∂μ -
          ∑ q : Fin 2, (∫ ω, SourceMixing.blkTr (gSide b E X adj ω * α ω) q ∂μ) *
            ∫ ω, star x ⬝ᵥ ((dRow b q * γ ω) *ᵥ c) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) := by
  obtain ⟨C, W₀, hC, h⟩ := traceQ_centre_bulk hA hb0 hb hκ (Lw + 1) (max Kd 1)
  refine ⟨2 * C, W₀, by positivity,
    fun W hW E hEκ X hX ℓ hℓ wd D hD ℓ₂ hℓ₂ wd₂ D₂ hD₂ x c u v hcu j => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  intro μ Q α γ
  obtain ⟨ℓA, wdA, DA, ℓG, wdG, DG, hlA, hlG, hDA, -, hDP, hτ, hF⟩ :=
    letter_words b E X adj hb0 hb wd D hD j
  have hD₂' : ∀ i, ‖D₂ i‖ ≤ max Kd 1 := fun i => (hD₂ i).trans (le_max_left _ _)
  have hc := fun q : Fin 2 => h W hW E hEκ X hX ℓG (by omega) wdG (preD (dRow b q) DG) (hDP q) ℓ₂
    (by omega) wd₂ D₂ hD₂' (ℓA + 1) (by omega) (Fin.cons (sideLetter adj) wdA) (Fin.cons 1 DA)
    (norm_cons_one_le (le_max_right _ _) hDA) q x c u v hcu
  set τ := fun (q : Fin 2) ω => (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω)
    (Fin.cons (sideLetter adj) wdA) (Fin.cons 1 DA)) q q).trace
  set F := fun (q : Fin 2) ω => wordForm (kHat b E X) x c wdG (preD (dRow b q) DG) (gRes b E X ω)
  set a := ∫ ω', Q ω' ∂μ
  have hpt : ∀ ω, star x ⬝ᵥ ((sdiag b (gSide b E X adj ω * α ω) * γ ω) *ᵥ c) * (Q ω - a) =
      ∑ q : Fin 2, τ q ω * (F q ω * (Q ω - a)) := fun ω => by
    rw [letter_pt hb0.le hb, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hτ ω q, hF ω q x c]; ring
  have hFq : ∀ q, (fun ω => star x ⬝ᵥ ((dRow b q * γ ω) *ᵥ c) * (Q ω - a)) =
      fun ω => F q ω * (Q ω - a) := fun q => funext fun ω => by rw [hF ω q x c]
  have hτq : ∀ q, (fun ω => SourceMixing.blkTr (gSide b E X adj ω * α ω) q) = τ q :=
    fun q => funext fun ω => hτ ω q
  have hI : Integrable (fun ω => ∑ q : Fin 2, τ q ω * (F q ω * (Q ω - a))) μ :=
    integrable_finsetSum _ fun q _ => (hc q).2.1
  refine ⟨by simp only [hpt]; exact hI, fun q => by rw [hFq q]; exact (hc q).1, ?_⟩
  simp only [hpt, hFq, hτq]
  rw [integral_finsetSum _ fun q _ => (hc q).2.1, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ q : Fin 2, ‖∫ ω, τ q ω * (F q ω * (Q ω - a)) ∂μ -
        (∫ ω, τ q ω ∂μ) * ∫ ω, F q ω * (Q ω - a) ∂μ‖
      ≤ ∑ _q : Fin 2, C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v) :=
        Finset.sum_le_sum fun q _ => (hc q).2.2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end BlockBand.Transmission.CovarianceBulk
