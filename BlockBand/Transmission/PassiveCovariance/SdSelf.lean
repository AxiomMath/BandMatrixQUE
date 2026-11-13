module

public import BlockBand.Transmission.PassiveCovariance.SdCentreProd

/-!
# The centred self-energy term of `sd_expand` is `O(W⁻²)`

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, `z = z_∂(E)`, strictly
passive `X`; `b, E, L_w, K_d` and the side `adj` are fixed, then `C, W₀`; uniform in `X`.

With `𝔊 = gSide adj`, `S̄ = sbarSide adj`, `N = w(𝒢)` (length `≤ L_w`, insertions `≤ K_d`):
* `selfTerm_pt`: `x*(S[𝔊] - S̄)𝔊Nc = Σ_q (τ_q - Eτ_q)·F_q`, with `τ_q = ⟨𝔊_{qq}⟩` and dressed forms
  `F_q = x*diag(d_q)𝔊Nc` (`d₀ = dOne`, `d₁ = dTwo`);
* `selfTerm_one`: `|E[x*(S[𝔊] - S̄)𝔊Nc]| ≤ (C/W²)‖x‖‖c‖` (the `Ψ = 1` case);
* `selfTerm_Q`: for `Q = u*w₂(𝒢)v` with `‖c‖‖u‖ ≤ 1`:
  `|E[(x*(S[𝔊] - S̄)𝔊Nc)(Q - EQ)]| ≤ (C/W²)‖x‖‖v‖` (the `Ψ = Q⁰` case).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The letter of the side: `𝒢` (`0`) or `𝒢ᴴ` (`2`). -/
def sideLetter (adj : Bool) : Fin 4 := if adj then 2 else 0

/-- The row weights `dOne`, `dTwo`. -/
def dRow (b : ℝ) (q : Fin 2) : LayerMat W :=
  if q = 0 then diagonal (SourceMixing.dOne b) else diagonal (SourceMixing.dTwo b)

theorem norm_dRow_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (q : Fin 2) : ‖(dRow b q : LayerMat W)‖ ≤ 1 := by
  unfold dRow; split_ifs
  · exact SourceMixing.norm_diag_dOne_le hb0 hb
  · exact SourceMixing.norm_diag_dTwo_le hb0 hb

theorem wLetter_side (Kh G : LayerMat W) (adj : Bool) :
    wLetter Kh G (sideLetter adj) = if adj then Gᴴ else G := by
  cases adj <;> rfl

theorem blkTr_side_word (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) (q : Fin 2)
    (ω : LayerSample W .oneBlockOnePort) :
    SourceMixing.blkTr (gSide b E X adj ω) q = (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X)
      (gRes b E X ω) ![sideLetter adj] ![1, 1]) q q).trace := by
  rw [SourceMixing.blkTr]
  congr 3
  rw [wordVal_succ, wordVal_zero]
  cases adj <;> simp [gSide, wLetter, sideLetter]

theorem form_side_word (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) (P : LayerMat W)
    {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W) (x c : LayerSite W .oneBlockOnePort → ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    star x ⬝ᵥ ((P * gSide b E X adj ω * wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) =
      wordForm (kHat b E X) x c (Fin.cons (sideLetter adj) wd) (Fin.cons P D) (gRes b E X ω) := by
  rw [wordForm, wordVal_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  cases adj <;> rfl

/-- **Pointwise decomposition of the centred self-energy term.** -/
theorem selfTerm_pt {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (adj : Bool) {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W)
    (x c : LayerSite W .oneBlockOnePort → ℂ) (ω : LayerSample W .oneBlockOnePort) :
    star x ⬝ᵥ (((sdiag b (gSide b E X adj ω) - sbarSide b E X adj) * gSide b E X adj ω *
        wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) =
      ∑ q : Fin 2, (SourceMixing.blkTr (gSide b E X adj ω) q -
          ∫ ω', SourceMixing.blkTr (gSide b E X adj ω') q ∂layerLaw W b .oneBlockOnePort) *
        wordForm (kHat b E X) x c (Fin.cons (sideLetter adj) wd) (Fin.cons (dRow b q) D)
          (gRes b E X ω) := by
  rw [sdiag_sub_sbarSide hb0 hb, selfEnergy_eq_smul, Fin.sum_univ_two, ← form_side_word,
    ← form_side_word]
  simp only [dRow, Fin.isValue, ↓reduceIte, one_ne_zero, Matrix.add_mul, Matrix.smul_mul,
    add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]

theorem integral_centred_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {τ F : Ω → ℂ}
    (hF : Integrable F μ) (hτF : Integrable (fun ω => τ ω * F ω) μ) :
    ∫ ω, (τ ω - ∫ ω', τ ω' ∂μ) * F ω ∂μ = (∫ ω, τ ω * F ω ∂μ) - (∫ ω, τ ω ∂μ) * ∫ ω, F ω ∂μ := by
  simp_rw [sub_mul]
  rw [integral_sub hτF (hF.const_mul _), integral_const_mul]

/-- **The centred self-energy term, `Ψ = 1`**: `|E[x*(S[𝔊] - S̄)𝔊Nc]| ≤ (C/W²)‖x‖‖c‖`. -/
theorem selfTerm_one (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) → ∀ x c : LayerSite W .oneBlockOnePort → ℂ,
        ‖∫ ω, star x ⬝ᵥ (((sdiag b (gSide b E X adj ω) - sbarSide b E X adj) * gSide b E X adj ω *
            wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) ∂layerLaw W b .oneBlockOnePort‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm c) := by
  obtain ⟨C, W₀, hC, h⟩ := layerTrace_dressedCov hA hb0 hb h1 h2 (Lw + 1) (max Kd 1)
  refine ⟨2 * C, W₀, by positivity, fun W hW X hX ℓ hℓ wd D hD x c => ?_⟩
  set μ := layerLaw W b .oneBlockOnePort
  have hD1 : ∀ q : Fin 2, ∀ j, ‖(Fin.cons (dRow b q) D : Fin (ℓ + 1 + 1) → LayerMat W) j‖ ≤ max Kd 1 :=
    fun q j => Fin.cases ((norm_dRow_le hb0 hb q).trans (le_max_right _ _))
      (fun k => (hD k).trans (le_max_left _ _)) j
  have h11 : ∀ j, ‖(![1, 1] : Fin 2 → LayerMat W) j‖ ≤ max Kd 1 := fun j => by
    fin_cases j <;> exact norm_one_matrix_le.trans (le_max_right _ _)
  have hq := fun q : Fin 2 => h W hW X hX (ℓ + 1) (by omega) (Fin.cons (sideLetter adj) wd)
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
`|E[(x*(S[𝔊] - S̄)𝔊Nc)(Q - EQ)]| ≤ (C/W²)‖x‖‖v‖`. -/
theorem selfTerm_Q (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨C₁, W₁, hC₁, h⟩ := layerTrace_dressedCov hA hb0 hb h1 h2 (Lw + 1) (max Kd 1)
  obtain ⟨C₂, W₂, hC₂, hp⟩ := layerTrace_cov_prod hA hb0 hb h1 h2 (Lw + 1) (max Kd 1)
  obtain ⟨C₃, W₃, hC₃, hm⟩ := norm_integral_poly_le hA hb0 hb h1 h2 (Lw + 1)
  set K1 := max Kd 1 ^ (Lw + 1)
  refine ⟨2 * (C₂ + K1 * C₃ * C₁), max W₁ (max W₂ W₃), by positivity,
    fun W hW X hX ℓ hℓ wd D hD ℓ₂ hℓ₂ wd₂ D₂ hD₂ x c u v hcu => ?_⟩
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
  have hQb : ‖∫ ω, Q ω ∂μ‖ ≤ K1 * (vecNorm u * vecNorm v) * C₃ := hm W hW3 X hX Q _ (Lw + 1) le_rfl
    fun ω => (wordForm_poly_bounds b E X hKd hℓ₂ wd₂ D₂ hD₂ u v ω).1
  have hq := fun q : Fin 2 => h W hW1 X hX (ℓ + 1) (by omega) (Fin.cons (sideLetter adj) wd)
    (Fin.cons (dRow b q) D) (hD1 q) 1 (by omega) ![sideLetter adj] ![1, 1] h11 q x c
  have hpq := fun q : Fin 2 => hp W hW2 X hX (ℓ + 1) (by omega) (Fin.cons (sideLetter adj) wd)
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

end BlockBand.Transmission.PassiveCovariance
