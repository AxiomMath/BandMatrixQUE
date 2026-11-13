module

public import BlockBand.Transmission.PassiveCovariance.SdCross

/-!
# The first-letter expansion with all errors: `E[(x*P₀𝔊Nc)Ψ]` for `Ψ = Q⁰` and `Ψ = 1`

* **`sdOne_expand`** (hypothesis: `PassiveBoundsStatement` only):
  `E[x*P₀𝔊Nc] = E[x*P₀M̄Nc] + Σ_j Σ_q E⟨(𝔊α_j)_qq⟩·E[x̌*d_qγ_jc] + O(W⁻²‖x̌‖‖c‖)`.

The three error terms are `SdSelf.selfTerm_Q/_one` (centred self-energy),
`SdLetter.letterTerm_Q/_one`
(letter traces) and `crossTerm_Q` (crossed contraction, `W⁻¹·W⁻¹`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The first-letter expansion against `Q⁰`, with all errors.** -/
theorem sdQ_expand (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b E : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) → ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw →
      ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W), (∀ j, ‖D₂ j‖ ≤ Kd) →
      ∀ (P₀ : LayerMat W) (x c u v : LayerSite W .oneBlockOnePort → ℂ), vecNorm c * vecNorm u ≤ 1 →
        let μ := layerLaw W b .oneBlockOnePort
        let Kh := kHat b E X
        let N := fun ω => wordVal Kh (gRes b E X ω) wd D
        let Q := fun ω => wordForm Kh u v wd₂ D₂ (gRes b E X ω)
        let xc := (P₀ * mbarSide b E X adj)ᴴ *ᵥ x
        let M := fun ω => gSide b E X adj ω * N ω
        ‖∫ ω, star x ⬝ᵥ ((P₀ * gSide b E X adj ω * N ω) *ᵥ c) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ -
          ∫ ω, star x ⬝ᵥ ((P₀ * mbarSide b E X adj * N ω) *ᵥ c) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ -
          ∑ j, ∑ q : Fin 2,
            (∫ ω, SourceMixing.blkTr (gSide b E X adj ω * wordAlpha Kh (gRes b E X ω) ℓ wd D j) q ∂μ) *
            ∫ ω, star xc ⬝ᵥ ((dRow b q * wordGamma Kh (gRes b E X ω) ℓ wd D j) *ᵥ c) *
              (Q ω - ∫ ω', Q ω' ∂μ) ∂μ -
          ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
            ((∫ ω, star xc ⬝ᵥ ((bProj p * wordGamma Kh (gRes b E X ω) ℓ₂ wd₂ D₂ k) *ᵥ v) ∂μ) *
              ∫ ω, star u ⬝ᵥ ((wordAlpha Kh (gRes b E X ω) ℓ₂ wd₂ D₂ k * bProj p' * M ω) *ᵥ c) ∂μ)‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v) := by
  obtain ⟨W₁, hsd⟩ := sd_expand hA hb0 hb h1 h2 Lw (Lw + 1) Kd adj
  obtain ⟨CS, WS, hCS, hS⟩ := selfTerm_Q hA hb0 hb h1 h2 Lw Kd adj
  obtain ⟨CL, WL, hCL, hL⟩ := letterTerm_Q hA hb0 hb h1 h2 Lw Kd adj
  obtain ⟨CX, WX, hCX, hX'⟩ := crossTerm_Q hP hA hb0 hb h1 h2 Lw Kd adj
  obtain ⟨C₃, W₃, hC₃, hm⟩ := norm_integral_poly_le hA hb0 hb h1 h2 (Lw + 1)
  refine ⟨CS + Lw * CL + CX, max (max W₁ WS) (max (max WL WX) W₃), by positivity,
    fun W hW X hX ℓ hℓ wd D hD ℓ₂ hℓ₂ wd₂ D₂ hD₂ P₀ x c u v hcu => ?_⟩
  intro μ Kh N Q xc M
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWS : WS ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWL : WL ≤ W :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hW
  have hWX : WX ≤ W :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  set K1 := max Kd 1 ^ (Lw + 1)
  set uv := vecNorm u * vecNorm v
  have huv : 0 ≤ uv := mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
  have hQb : ‖∫ ω, Q ω ∂μ‖ ≤ K1 * uv * C₃ := hm W hW3 X hX.posSemidef Q _ (Lw + 1) le_rfl
    fun ω => (wordForm_poly_bounds b E X hKd hℓ₂ wd₂ D₂ hD₂ u v ω).1
  set a := ∫ ω', Q ω' ∂μ
  -- the test functional `Q⁰` and its derivative
  have hΨ : HasLayerDeriv (fun ω => Q ω - a) (fun ω => wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω)) :=
    fun ω hω Δ hΔ => (hasLayerDeriv_wordForm hη hX Kh u v wd₂ D₂ ω hω Δ hΔ).sub_const _
  have hΨm : Measurable fun ω => Q ω - a :=
    (measurable_wordForm Kh u v wd₂ D₂ (measurable_layerRes E (boundaryZ b E) X)).sub_const _
  have hDm : ∀ N', Measurable fun ω => wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) N' :=
    measurable_wordFormDeriv Kh u v wd₂ D₂ (measurable_layerRes E (boundaryZ b E) X)
  set K := K1 * uv * (1 + C₃ + Lw)
  have hK1 : 0 ≤ K1 := by positivity
  have hΨb : ∀ ω, ‖Q ω - a‖ ≤ K * (1 + btFun b E X ω) ^ (Lw + 1) := fun ω => by
    have h0 := (wordForm_poly_bounds b E X hKd hℓ₂ wd₂ D₂ hD₂ u v ω).1
    have hp : 1 ≤ (1 + btFun b E X ω) ^ (Lw + 1) := one_le_pow₀ (one_le_one_add_btFun b E X ω)
    have hL0 : (0 : ℝ) ≤ Lw := Nat.cast_nonneg _
    calc ‖Q ω - a‖ ≤ ‖Q ω‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ K1 * uv * (1 + btFun b E X ω) ^ (Lw + 1) + K1 * uv * C₃ * (1 + btFun b E X ω) ^ (Lw + 1) :=
          add_le_add h0 (hQb.trans (le_mul_of_one_le_right (by positivity) hp))
      _ ≤ K * (1 + btFun b E X ω) ^ (Lw + 1) := by
          have : 0 ≤ K1 * uv * Lw * (1 + btFun b E X ω) ^ (Lw + 1) := by positivity
          simp only [K]; nlinarith
  have hDb : ∀ ω N', ‖wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) N'‖ ≤
      K * ‖N'‖ * (1 + btFun b E X ω) ^ (Lw + 1) := fun ω N' => by
    refine ((wordForm_poly_bounds b E X hKd hℓ₂ wd₂ D₂ hD₂ u v ω).2 N').trans ?_
    have : 0 ≤ ‖N'‖ * (1 + btFun b E X ω) ^ (Lw + 1) := by
      have := btFun_nonneg b E X ω; positivity
    have hle : (Lw : ℝ) * K1 * ‖N'‖ * uv * (1 + btFun b E X ω) ^ (Lw + 1) =
        K1 * uv * Lw * (‖N'‖ * (1 + btFun b E X ω) ^ (Lw + 1)) := by ring
    have hle2 : K * ‖N'‖ * (1 + btFun b E X ω) ^ (Lw + 1) =
        K1 * uv * (1 + C₃ + Lw) * (‖N'‖ * (1 + btFun b E X ω) ^ (Lw + 1)) := by simp only [K]; ring
    rw [hle, hle2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith)
      (by positivity)) this
  have hE := hsd W hW1 X hX ℓ hℓ wd D hD P₀ x c (fun ω => Q ω - a)
    (fun ω => wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω)) K hΨ hΨm hDm hΨb hDb
  have hSb := hS W hWS X hX.posSemidef ℓ hℓ wd D hD ℓ₂ hℓ₂ wd₂ D₂ hD₂ xc c u v hcu
  have hLb := fun j => (hL W hWL X hX.posSemidef ℓ hℓ wd D hD ℓ₂ hℓ₂ wd₂ D₂ hD₂ xc c u v hcu j).2.2
  have hXb := hX' W hWX X hX ℓ hℓ wd D hD ℓ₂ hℓ₂ wd₂ D₂ hD₂ xc c u v
  simp only at hE hSb hLb hXb ⊢
  rw [hE]
  set TS := ∫ ω, star xc ⬝ᵥ (((sdiag b (gSide b E X adj ω) - sbarSide b E X adj) *
    gSide b E X adj ω * wordVal Kh (gRes b E X ω) wd D) *ᵥ c) * (Q ω - a) ∂μ
  set TL := fun j : Fin ℓ => ∫ ω, star xc ⬝ᵥ ((sdiag b (gSide b E X adj ω *
    wordAlpha Kh (gRes b E X ω) ℓ wd D j) * wordGamma Kh (gRes b E X ω) ℓ wd D j) *ᵥ c) *
    (Q ω - a) ∂μ
  set LL := fun j : Fin ℓ => ∑ q : Fin 2,
    (∫ ω, SourceMixing.blkTr (gSide b E X adj ω * wordAlpha Kh (gRes b E X ω) ℓ wd D j) q ∂μ) *
    ∫ ω, star xc ⬝ᵥ ((dRow b q * wordGamma Kh (gRes b E X ω) ℓ wd D j) *ᵥ c) * (Q ω - a) ∂μ
  set TX := ∑ α, ∑ γ, siteVar W b α γ * ∫ ω, star (xc α) *
    ((gSide b E X adj ω * wordVal Kh (gRes b E X ω) wd D) *ᵥ c) γ *
    wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1) ∂μ
  set LX := ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
    ((∫ ω, star xc ⬝ᵥ ((bProj p * wordGamma Kh (gRes b E X ω) ℓ₂ wd₂ D₂ k) *ᵥ v) ∂μ) *
      ∫ ω, star u ⬝ᵥ ((wordAlpha Kh (gRes b E X ω) ℓ₂ wd₂ D₂ k * bProj p' *
        (gSide b E X adj ω * wordVal Kh (gRes b E X ω) wd D)) *ᵥ c) ∂μ)
  set TM := ∫ ω, star x ⬝ᵥ ((P₀ * mbarSide b E X adj * wordVal Kh (gRes b E X ω) wd D) *ᵥ c) *
    (Q ω - a) ∂μ
  have halg : TM + TS + ∑ j, TL j - TX - TM - ∑ j, LL j - LX =
      TS + ∑ j, (TL j - LL j) - (TX + LX) := by
    rw [Finset.sum_sub_distrib]; ring
  change ‖TM + TS + ∑ j, TL j - TX - TM - ∑ j, LL j - LX‖ ≤ _
  rw [halg]
  have hxv : 0 ≤ vecNorm xc * vecNorm v := mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
  have hXb' : ‖TX + LX‖ ≤ CX / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v) := by
    refine hXb.trans ?_
    have : vecNorm u * vecNorm c ≤ 1 := by rw [mul_comm]; exact hcu
    have h0 : 0 ≤ CX / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v) := by positivity
    calc CX / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v * (vecNorm u * vecNorm c))
        ≤ CX / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v * 1) := by gcongr
      _ = _ := by ring
  have hLsum : ‖∑ j, (TL j - LL j)‖ ≤ Lw * (CL / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖TL j - LL j‖ ≤ ∑ _j : Fin ℓ, CL / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v) :=
          Finset.sum_le_sum fun j _ => hLb j
      _ = ℓ * (CL / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v)) := by simp
      _ ≤ _ := by gcongr
  calc ‖TS + ∑ j, (TL j - LL j) - (TX + LX)‖ ≤ ‖TS‖ + ‖∑ j, (TL j - LL j)‖ + ‖TX + LX‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ CS / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v) +
        Lw * (CL / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v)) +
        CX / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v) := add_le_add (add_le_add hSb hLsum) hXb'
    _ = _ := by ring

/-- **The first-letter expansion for means (`Ψ = 1`), with all errors.** -/
theorem sdOne_expand (hA : PassiveBoundsStatement) {b E : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) →
      ∀ (P₀ : LayerMat W) (x c : LayerSite W .oneBlockOnePort → ℂ),
        let μ := layerLaw W b .oneBlockOnePort
        let Kh := kHat b E X
        let N := fun ω => wordVal Kh (gRes b E X ω) wd D
        let xc := (P₀ * mbarSide b E X adj)ᴴ *ᵥ x
        ‖∫ ω, star x ⬝ᵥ ((P₀ * gSide b E X adj ω * N ω) *ᵥ c) ∂μ -
          ∫ ω, star x ⬝ᵥ ((P₀ * mbarSide b E X adj * N ω) *ᵥ c) ∂μ -
          ∑ j, ∑ q : Fin 2,
            (∫ ω, SourceMixing.blkTr (gSide b E X adj ω * wordAlpha Kh (gRes b E X ω) ℓ wd D j) q ∂μ) *
            ∫ ω, star xc ⬝ᵥ ((dRow b q * wordGamma Kh (gRes b E X ω) ℓ wd D j) *ᵥ c) ∂μ‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm c) := by
  obtain ⟨W₁, hsd⟩ := sd_expand hA hb0 hb h1 h2 Lw 0 Kd adj
  obtain ⟨CS, WS, hCS, hS⟩ := selfTerm_one hA hb0 hb h1 h2 Lw Kd adj
  obtain ⟨CL, WL, hCL, hL⟩ := letterTerm_one hA hb0 hb h1 h2 Lw Kd adj
  refine ⟨CS + Lw * CL, max W₁ (max WS WL), by positivity,
    fun W hW X hX ℓ hℓ wd D hD P₀ x c => ?_⟩
  intro μ Kh N xc
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hWS : WS ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWL : WL ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hΨ : HasLayerDeriv (fun _ => (1 : ℂ)) (fun _ => (0 : LayerMat W →ₗ[ℂ] ℂ)) :=
    fun ω _ Δ _ => by simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  have hE := hsd W hW1 X hX ℓ hℓ wd D hD P₀ x c (fun _ => (1 : ℂ))
    (fun _ => (0 : LayerMat W →ₗ[ℂ] ℂ)) 1 hΨ measurable_const (fun _ => measurable_const)
    (fun ω => by simp) (fun ω N' => by simp)
  have hSb := hS W hWS X hX.posSemidef ℓ hℓ wd D hD xc c
  have hLb := fun j => (hL W hWL X hX.posSemidef ℓ hℓ wd D hD xc c j).2.2
  simp only [mul_one, LinearMap.zero_apply, mul_zero, integral_zero, Finset.sum_const_zero,
    sub_zero] at hE
  simp only at hSb hLb ⊢
  rw [hE]
  set TS := ∫ ω, star xc ⬝ᵥ (((sdiag b (gSide b E X adj ω) - sbarSide b E X adj) *
    gSide b E X adj ω * wordVal Kh (gRes b E X ω) wd D) *ᵥ c) ∂μ
  set TL := fun j : Fin ℓ => ∫ ω, star xc ⬝ᵥ ((sdiag b (gSide b E X adj ω *
    wordAlpha Kh (gRes b E X ω) ℓ wd D j) * wordGamma Kh (gRes b E X ω) ℓ wd D j) *ᵥ c) ∂μ
  set LL := fun j : Fin ℓ => ∑ q : Fin 2,
    (∫ ω, SourceMixing.blkTr (gSide b E X adj ω * wordAlpha Kh (gRes b E X ω) ℓ wd D j) q ∂μ) *
    ∫ ω, star xc ⬝ᵥ ((dRow b q * wordGamma Kh (gRes b E X ω) ℓ wd D j) *ᵥ c) ∂μ
  set TM := ∫ ω, star x ⬝ᵥ ((P₀ * mbarSide b E X adj * wordVal Kh (gRes b E X ω) wd D) *ᵥ c) ∂μ
  have halg : TM + TS + ∑ j, TL j - TM - ∑ j, LL j = TS + ∑ j, (TL j - LL j) := by
    rw [Finset.sum_sub_distrib]; ring
  change ‖TM + TS + ∑ j, TL j - TM - ∑ j, LL j‖ ≤ _
  rw [halg]
  have hxc : 0 ≤ vecNorm xc * vecNorm c := mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
  have hLsum : ‖∑ j, (TL j - LL j)‖ ≤ Lw * (CL / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm c)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖TL j - LL j‖ ≤ ∑ _j : Fin ℓ, CL / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm c) :=
          Finset.sum_le_sum fun j _ => hLb j
      _ = ℓ * (CL / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm c)) := by simp
      _ ≤ _ := by gcongr
  calc ‖TS + ∑ j, (TL j - LL j)‖ ≤ ‖TS‖ + ‖∑ j, (TL j - LL j)‖ := norm_add_le _ _
    _ ≤ CS / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm c) +
        Lw * (CL / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm c)) := add_le_add hSb hLsum
    _ = _ := by ring

end BlockBand.Transmission.PassiveCovariance
