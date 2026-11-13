module

public import BlockBand.Transmission.PassiveCovariance.WordFactor

/-!
# The letter-trace terms of `sd_expand`

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, `z = z_∂(E)`,
passive `X`; fixed `b, E, L_w, K_d`, side `adj`; then `C, W₀`; uniform in `X`, the words and the
vectors.

The third term of `sd_expand` is `Σ_j E[(x*S[𝔊α_j]γ_jc)Ψ]`. With `S[M] = Σ_q ⟨M_qq⟩·d_q`
(`letter_pt`), the trace `τ_{jq} = ⟨(𝔊α_j)_{qq}⟩` is a multi-letter dressed trace and
`x*d_qγ_jc` a dressed form (`WordFactor`), so the trace can be replaced by its mean:

* `traceQ_centre`: `|E[τ·F·Q⁰] - Eτ·E[F·Q⁰]| ≤ (C/W²)‖x‖‖v‖` for a dressed trace `τ`, dressed
  forms `F = x*w₁c`, `Q = u*w₂v`, `Q⁰ = Q - EQ`, `‖c‖‖u‖ ≤ 1`;
* **`letterTerm_Q`** (`Ψ = Q⁰`): `|E[(x*S[𝔊α_j]γ_jc)Q⁰] - Σ_q Eτ_{jq}·E[(x*d_qγ_jc)Q⁰]| ≤ (C/W²)‖x‖‖v‖`;
* **`letterTerm_one`** (`Ψ = 1`): `|E[x*S[𝔊α_j]γ_jc] - Σ_q Eτ_{jq}·E[x*d_qγ_jc]| ≤ (C/W²)‖x‖‖c‖`.
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

theorem gSide_letter (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool)
    (ω : LayerSample W .oneBlockOnePort) :
    gSide b E X adj ω = wLetter (kHat b E X) (gRes b E X ω) (sideLetter adj) := by
  rw [wLetter_side]; rfl

/-- `x*S[M]γc = Σ_q ⟨M_qq⟩·x*d_qγc`. -/
theorem letter_pt {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) (M Γ : LayerMat W)
    (x c : LayerSite W .oneBlockOnePort → ℂ) :
    star x ⬝ᵥ ((sdiag b M * Γ) *ᵥ c) =
      ∑ q : Fin 2, SourceMixing.blkTr M q * star x ⬝ᵥ ((dRow b q * Γ) *ᵥ c) := by
  rw [sdiag_eq_selfEnergy hb0 hb, selfEnergy_eq_smul, Fin.sum_univ_two]
  simp only [dRow, Fin.isValue, ↓reduceIte, one_ne_zero, Matrix.add_mul, Matrix.smul_mul,
    add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]

/-- **Trace centring against `F·Q⁰`.** -/
theorem traceQ_centre (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨C₁, W₁, hC₁, h⟩ := layerTrace_dressedCov hA hb0 hb h1 h2 Lw Kd
  obtain ⟨C₂, W₂, hC₂, hp⟩ := layerTrace_cov_prod hA hb0 hb h1 h2 Lw Kd
  obtain ⟨C₃, W₃, hC₃, hm⟩ := norm_integral_poly_le hA hb0 hb h1 h2 (Lw + 1)
  set K1 := max Kd 1 ^ (Lw + 1)
  refine ⟨C₂ + K1 * C₃ * C₁, max W₁ (max W₂ W₃), by positivity,
    fun W hW X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ ℓ' hℓ' wd' D' hD' q x c u v hcu => ?_⟩
  intro μ τ F Q
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD₁ 0)
  obtain ⟨-, hFi, hτF, hb2⟩ := h W hW1 X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ' hℓ' wd' D' hD' q x c
  obtain ⟨hFQ, hτFQ, hb1⟩ := hp W hW2 X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ ℓ' hℓ' wd' D' hD'
    q x c u v hcu
  have hQb : ‖∫ ω, Q ω ∂μ‖ ≤ K1 * (vecNorm u * vecNorm v) * C₃ := hm W hW3 X hX Q _ (Lw + 1) le_rfl
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

/-- The two words of a letter-trace term. -/
theorem letter_words (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) {Kd : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W)
    (hD : ∀ j, ‖D j‖ ≤ Kd) (j : Fin ℓ) :
    ∃ (ℓA : ℕ) (wdA : Fin ℓA → Fin 4) (DA : Fin (ℓA + 1) → LayerMat W)
      (ℓG : ℕ) (wdG : Fin ℓG → Fin 4) (DG : Fin (ℓG + 1) → LayerMat W),
      ℓA ≤ ℓ ∧ ℓG ≤ ℓ ∧ (∀ i, ‖DA i‖ ≤ max Kd 1) ∧ (∀ i, ‖DG i‖ ≤ max Kd 1) ∧
      (∀ q : Fin 2, ∀ i, ‖preD (dRow b q) DG i‖ ≤ max Kd 1) ∧
      (∀ ω q, SourceMixing.blkTr (gSide b E X adj ω *
          wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) q =
        (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω) (Fin.cons (sideLetter adj) wdA)
          (Fin.cons 1 DA)) q q).trace) ∧
      ∀ ω q (x c : LayerSite W .oneBlockOnePort → ℂ),
        star x ⬝ᵥ ((dRow b q * wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) *ᵥ c) =
          wordForm (kHat b E X) x c wdG (preD (dRow b q) DG) (gRes b E X ω) := by
  obtain ⟨ℓA', wdA, DA, hlA, hFA, hGA⟩ := wordAlpha_word (kHat b E X) ℓ wd D j
  obtain ⟨ℓG, wdG, DG, hlG, hFG, hGG⟩ := wordGamma_word (kHat b E X) ℓ wd D j
  have hK := le_max_right Kd 1
  have hD' : ∀ i, ‖D i‖ ≤ max Kd 1 := fun i => (hD i).trans (le_max_left _ _)
  have hDA := hFA.norm_le hK hD'
  have hDG := hFG.norm_le hK hD'
  refine ⟨ℓA', wdA, DA, ℓG, wdG, DG, hlA, hlG, hDA, hDG,
    fun q => norm_preD_le (norm_dRow_le hb0 hb q) hDG, fun ω q => ?_, fun ω q x c => ?_⟩
  · rw [hGA, gSide_letter, letter_mul_wordVal]; rfl
  · rw [hGG, wordForm, wordVal_preD]

theorem norm_cons_one_le {ℓ : ℕ} {DA : Fin (ℓ + 1) → LayerMat W} {K : ℝ} (hK : 1 ≤ K)
    (h : ∀ i, ‖DA i‖ ≤ K) : ∀ i, ‖(Fin.cons 1 DA : Fin (ℓ + 2) → LayerMat W) i‖ ≤ K := fun i =>
  Fin.cases (norm_one_matrix_le.trans hK) (fun i => h i) i

/-- **The letter-trace term, `Ψ = Q⁰`.** -/
theorem letterTerm_Q (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨C, W₀, hC, h⟩ := traceQ_centre hA hb0 hb h1 h2 (Lw + 1) (max Kd 1)
  refine ⟨2 * C, W₀, by positivity, fun W hW X hX ℓ hℓ wd D hD ℓ₂ hℓ₂ wd₂ D₂ hD₂ x c u v hcu j => ?_⟩
  intro μ Q α γ
  obtain ⟨ℓA, wdA, DA, ℓG, wdG, DG, hlA, hlG, hDA, -, hDP, hτ, hF⟩ :=
    letter_words b E X adj hb0 hb wd D hD j
  have hD₂' : ∀ i, ‖D₂ i‖ ≤ max Kd 1 := fun i => (hD₂ i).trans (le_max_left _ _)
  have hc := fun q : Fin 2 => h W hW X hX ℓG (by omega) wdG (preD (dRow b q) DG) (hDP q) ℓ₂
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

/-- **The letter-trace term, `Ψ = 1`.** -/
theorem letterTerm_one (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨C, W₀, hC, h⟩ := layerTrace_dressedCov hA hb0 hb h1 h2 (Lw + 1) (max Kd 1)
  refine ⟨2 * C, W₀, by positivity, fun W hW X hX ℓ hℓ wd D hD x c j => ?_⟩
  intro μ α γ
  obtain ⟨ℓA, wdA, DA, ℓG, wdG, DG, hlA, hlG, hDA, -, hDP, hτ, hF⟩ :=
    letter_words b E X adj hb0 hb wd D hD j
  have hc := fun q : Fin 2 => h W hW X hX ℓG (by omega) wdG (preD (dRow b q) DG) (hDP q)
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

end BlockBand.Transmission.PassiveCovariance
