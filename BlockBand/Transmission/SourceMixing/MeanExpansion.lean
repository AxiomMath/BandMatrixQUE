module

public import BlockBand.Transmission.SourceMixing.Expansion

/-!
# The mean-field expansion of `E[𝒢·w(𝒢)]` in operator norm

Hypothesis `PassiveLayer.PassiveBoundsStatement` (`moments`, `traceMatrix`), at `w = z_∂`. Law
`layerLaw W b .oneBlockOnePort` (`= freshLaw W b`), deterministic strictly passive `X`, operator norm
on `2W × 2W` layer matrices, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`.

`meanExpansion`: with the dressed matrix `D = H₀ - S̄` (`dressed`), the
self-energy map `𝒮[F] = selfEnergy b ⟨F₁₁⟩ ⟨F₂₂⟩`, and for every dressed word `w` (length
`≤ L_w`, insertions `≤ K_d`) with derivative factors `α_j, γ_j`:

`‖D·E[𝒢w] - E[w] - Σ_j 𝒮[E(𝒢α_j)]·E[γ_j]‖ ≤ C/W²`,

uniformly in `W ≥ W₀` and strictly passive `X`; `C` depends on `b, E, L_w, K_d` only. This is
the general one-step Schwinger–Dyson expansion; for `w = P₂(K̂𝒢)ᴴ` it is the two-resolvent
equation behind the passive mean, for `w = P₂𝒢P₂(K̂𝒢)ᴴ` the three-resolvent equation behind
the differentiated mean.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Row coefficient of `⟨F₁₁⟩` in the self-energy. -/
def dOne (b : ℝ) : LayerSite W .oneBlockOnePort → ℂ :=
  Sum.elim (fun _ => ((1 - 2 * b : ℝ) : ℂ)) fun _ => (b : ℂ)

/-- Row coefficient of `⟨F₂₂⟩` in the self-energy. -/
def dTwo (b : ℝ) : LayerSite W .oneBlockOnePort → ℂ := Sum.elim (fun _ => (b : ℂ)) fun _ => 0

theorem selfEnergy_eq (b : ℝ) (m₁ m₂ : ℂ) :
    (selfEnergy b m₁ m₂ : LayerMat W) = diagonal fun ρ => dOne b ρ * m₁ + dTwo b ρ * m₂ := by
  unfold selfEnergy
  congr 1; funext ρ
  rcases ρ with ρ | ρ <;> simp [dOne, dTwo]

/-- The self-energy map `𝒮[F]` with mean traces `m₁, m₂`. -/
abbrev selfOf (b : ℝ) (m₁ m₂ : ℂ) : LayerMat W := selfEnergy b m₁ m₂

theorem norm_diag_dOne_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ‖(diagonal (dOne (W := W) b) : LayerMat W)‖ ≤ 1 :=
  norm_diagonal_le _ zero_le_one fun i => by
    rcases i with i | i
    · simp only [dOne, Sum.elim_inl, Complex.norm_real,
        Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * b)]
      linarith
    · simp only [dOne, Sum.elim_inr, Complex.norm_real, Real.norm_of_nonneg hb0.le]; linarith

theorem norm_diag_dTwo_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ‖(diagonal (dTwo (W := W) b) : LayerMat W)‖ ≤ 1 :=
  norm_diagonal_le _ zero_le_one fun i => by
    rcases i with i | i
    · simp only [dTwo, Sum.elim_inl, Complex.norm_real, Real.norm_of_nonneg hb0.le]; linarith
    · simp [dTwo]

/-- The unified row form of `expansion_phys`/`expansion_port`. -/
theorem expansion_rows (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) → ∀ (ρ γ : LayerSite W .oneBlockOnePort),
        ∫ ω, (layerLin ω * gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) ρ γ
            ∂layerLaw W b .oneBlockOnePort =
          ∫ ω, (-((dOne b ρ * blkTr (gRes b E X ω) 0 + dTwo b ρ * blkTr (gRes b E X ω) 1) *
              (gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) ρ γ) -
            ∑ j, (dOne b ρ * blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0 +
                dTwo b ρ * blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1) *
              wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j ρ γ)
            ∂layerLaw W b .oneBlockOnePort := by
  obtain ⟨W₁, hp⟩ := expansion_phys hA hb0 hb h1 h2 Lw Kd
  obtain ⟨W₂, hq⟩ := expansion_port hA hb0 hb h1 h2 Lw Kd
  refine ⟨max W₁ W₂, fun W hW X hX ℓ hℓ wd D hD ρ γ => ?_⟩
  have h0 : ∀ a : Fin 1, a = 0 := fun a => Subsingleton.elim _ _
  rcases ρ with ⟨i0, x⟩ | ⟨i0, x⟩ <;> rw [h0 i0]
  · rw [hp W (le_trans (le_max_left _ _) hW) X hX ℓ hℓ wd D hD x γ]
    simp only [sPhys, dOne, dTwo, Sum.elim_inl]
  · rw [hq W (le_trans (le_max_right _ _) hW) X hX ℓ hℓ wd D hD x γ]
    simp only [sPort, dOne, dTwo, Sum.elim_inr, zero_mul, add_zero]

theorem trLetter_zero_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    trLetter b E X 0 ω = blkTr (gRes b E X ω) 0 := by
  simp only [trLetter, blkTr, trace_letter0]
  congr 1

theorem trLetter_three_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    trLetter b E X 3 ω = blkTr (gRes b E X ω) 1 := by
  simp only [trLetter, blkTr, trace_letter3]
  congr 1

theorem selfEnergy_mul_apply (b : ℝ) (m₁ m₂ : ℂ) (M : LayerMat W) (ρ γ : LayerSite W .oneBlockOnePort) :
    ((selfEnergy b m₁ m₂ : LayerMat W) * M) ρ γ = (dOne b ρ * m₁ + dTwo b ρ * m₂) * M ρ γ := by
  rw [selfEnergy_eq, diagonal_mul]

theorem covMat_apply {Ω n : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℂ)
    (U : Ω → Matrix n n ℂ) (ρ γ : n) :
    covMat μ f U ρ γ = (∫ ω, f ω * U ω ρ γ ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, U ω ρ γ ∂μ := rfl

/-- `G` itself as a dressed word of length one. -/
theorem wordVal_G (Kh G : LayerMat W) :
    wordVal Kh G (![0] : Fin 1 → Fin 4) ![1, 1] = G := by
  rw [wordVal_succ, wordVal_zero]; simp [wLetter]

/-- The mean-field expansion of `E[𝒢·w(𝒢)]`. -/
theorem meanExpansion (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) →
        ‖dressed b E X * matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) -
          matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D) -
          ∑ j, selfEnergy b
              (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0
                ∂layerLaw W b .oneBlockOnePort)
              (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1
                ∂layerLaw W b .oneBlockOnePort) *
            matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨W₁, hrow⟩ := expansion_rows hA hb0 hb h1 h2 Lw Kd
  obtain ⟨Ct, Wt, hCt, htc⟩ := wordTraceCov hA hb0 hb h1 h2 (Lw + 1) (max Kd 1)
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨_, Wm, hmom⟩ := hA.moments b hb0 hb _ hκ 1 le_rfl
  refine ⟨2 * (Lw + 1) * Ct, max (max W₁ Wt) Wm, by positivity, fun W hW X hX ℓ hℓ wd D hD => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWt : Wt ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWm : Wm ≤ W := le_trans (le_max_right _ _) hW
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set G := gRes b E X
  set H₀ := layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) 0
  have hD' : ∀ i, ‖D i‖ ≤ max Kd 1 := fun i => (hD i).trans (le_max_left _ _)
  -- trace–matrix covariance for any two shapes
  have key : ∀ (s₁ s₂ : WordShape (LayerSite W .oneBlockOnePort) (Lw + 1) (max Kd 1)) (r : Fin 2),
      Integrable (fun ω => blkTr (wordVal Kh (G ω) s₁.wd s₁.D) r) μ ∧
      (∀ α β, Integrable (fun ω => wordVal Kh (G ω) s₂.wd s₂.D α β) μ) ∧
      (∀ α β, Integrable (fun ω => blkTr (wordVal Kh (G ω) s₁.wd s₁.D) r *
        wordVal Kh (G ω) s₂.wd s₂.D α β) μ) ∧
      ‖covMat μ (fun ω => blkTr (wordVal Kh (G ω) s₁.wd s₁.D) r)
        (fun ω => wordVal Kh (G ω) s₂.wd s₂.D)‖ ≤ Ct / (W : ℝ) ^ 2 := fun s₁ s₂ r =>
    htc W hWt X hX.posSemidef s₁.len s₁.hlen s₁.wd s₁.D s₁.hD s₂.len s₂.hlen s₂.wd s₂.D s₂.hD r
  -- the shapes
  set sG : WordShape (LayerSite W .oneBlockOnePort) (Lw + 1) (max Kd 1) :=
    ⟨1, by omega, ![0], ![1, 1], fun i => by fin_cases i <;> exact norm_one_le_max Kd⟩
  set sN : WordShape (LayerSite W .oneBlockOnePort) (Lw + 1) (max Kd 1) :=
    ⟨ℓ, by omega, wd, D, hD'⟩
  set sGN : WordShape (LayerSite W .oneBlockOnePort) (Lw + 1) (max Kd 1) :=
    ⟨ℓ + 1, by omega, Fin.cons 0 wd, Fin.cons 1 D, norm_cons_le _ _ (norm_one_le_max Kd) hD'⟩
  have eG : ∀ ω, wordVal Kh (G ω) sG.wd sG.D = G ω := fun ω => wordVal_G Kh (G ω)
  have eGN : ∀ ω, wordVal Kh (G ω) sGN.wd sGN.D = G ω * wordVal Kh (G ω) wd D :=
    fun ω => (G_mul_wordVal Kh (G ω) wd D).symm
  have sα : ∀ j, ∃ s : WordShape (LayerSite W .oneBlockOnePort) (Lw + 1) (max Kd 1),
      ∀ ω, wordVal Kh (G ω) s.wd s.D = G ω * wordAlpha Kh (G ω) ℓ wd D j := fun j => by
    obtain ⟨s, hs⟩ := G_mul_wordAlpha_shape Kh ℓ wd D hD j
    exact ⟨⟨s.len, by have := s.hlen; omega, s.wd, s.D, s.hD⟩, fun ω => (hs (G ω)).symm⟩
  have sγ : ∀ j, ∃ s : WordShape (LayerSite W .oneBlockOnePort) (Lw + 1) (max Kd 1),
      ∀ ω, wordVal Kh (G ω) s.wd s.D = wordGamma Kh (G ω) ℓ wd D j := fun j => by
    obtain ⟨s, hs⟩ := wordGamma_shape Kh ℓ wd D hD j
    exact ⟨⟨s.len, by have := s.hlen; omega, s.wd, s.D, s.hD⟩, fun ω => (hs (G ω)).symm⟩
  choose sA hsA using sα
  choose sC hsC using sγ
  -- the facts in the original variables
  have kGGN := fun r => key sG sGN r
  simp only [eG, eGN] at kGGN
  have kGN : ∀ α β, Integrable (fun ω => wordVal Kh (G ω) wd D α β) μ := (key sG sN 0).2.1
  have kj := fun j r => key (sA j) (sC j) r
  simp only [hsA, hsC] at kj
  -- a.s. `V𝒢w = w - H₀(𝒢w)`
  have hae : ∀ᵐ ω ∂μ, layerLin ω * G ω * wordVal Kh (G ω) wd D =
      wordVal Kh (G ω) wd D - H₀ * (G ω * wordVal Kh (G ω) wd D) := by
    filter_upwards [(hmom W hWm E (mem_bulkInterval_min E) _
      (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX.posSemidef).1] with ω hω
    rw [layerLin_mul_gRes b E X ω ((Matrix.isUnit_iff_isUnit_det _).mpr hω), Matrix.sub_mul,
      Matrix.one_mul, Matrix.mul_assoc]
    rfl
  set A := matrixExpect μ (fun ω => G ω * wordVal Kh (G ω) wd D)
  set c0 := covMat μ (fun ω => blkTr (G ω) 0) (fun ω => G ω * wordVal Kh (G ω) wd D)
  set c1 := covMat μ (fun ω => blkTr (G ω) 1) (fun ω => G ω * wordVal Kh (G ω) wd D)
  set cj : Fin ℓ → Fin 2 → LayerMat W := fun j r =>
    covMat μ (fun ω => blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) r)
      (fun ω => wordGamma Kh (G ω) ℓ wd D j)
  have hid : dressed b E X * A - matrixExpect μ (fun ω => wordVal Kh (G ω) wd D) -
      ∑ j, selfEnergy b (∫ ω, blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 0 ∂μ)
          (∫ ω, blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 1 ∂μ) *
        matrixExpect μ (fun ω => wordGamma Kh (G ω) ℓ wd D j) =
      diagonal (dOne b) * c0 + diagonal (dTwo b) * c1 +
        ∑ j, (diagonal (dOne b) * cj j 0 + diagonal (dTwo b) * cj j 1) := by
    ext ρ γ
    -- `(H₀A)_{ργ} = E w_{ργ} - E(V𝒢w)_{ργ}`
    have hH : (H₀ * A) ρ γ = (∫ ω, wordVal Kh (G ω) wd D ρ γ ∂μ) -
        ∫ ω, (layerLin ω * G ω * wordVal Kh (G ω) wd D) ρ γ ∂μ := by
      have e : ∀ ω, (wordVal Kh (G ω) wd D - H₀ * (G ω * wordVal Kh (G ω) wd D)) ρ γ =
          wordVal Kh (G ω) wd D ρ γ - ∑ δ, H₀ ρ δ * (G ω * wordVal Kh (G ω) wd D) δ γ :=
        fun ω => by rw [Matrix.sub_apply, Matrix.mul_apply]
      have hi : Integrable (fun ω => ∑ δ, H₀ ρ δ * (G ω * wordVal Kh (G ω) wd D) δ γ) μ :=
        integrable_finsetSum _ fun δ _ => ((kGGN 0).2.1 δ γ).const_mul _
      rw [integral_congr_ae (hae.mono fun ω hω => congrFun (congrFun hω ρ) γ),
        integral_congr_ae (Eventually.of_forall e), integral_sub (kGN ρ γ) hi,
        integral_finsetSum _ fun δ _ => ((kGGN 0).2.1 δ γ).const_mul _]
      simp only [integral_const_mul]
      rw [Matrix.mul_apply]
      simp only [A, matrixExpect, Matrix.of_apply]
      ring
    have hR := hrow W hW1 X hX ℓ hℓ wd D hD ρ γ
    have hsplit : ∫ ω, (-((dOne b ρ * blkTr (G ω) 0 + dTwo b ρ * blkTr (G ω) 1) *
          (G ω * wordVal Kh (G ω) wd D) ρ γ) -
        ∑ j, (dOne b ρ * blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 0 +
            dTwo b ρ * blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 1) *
          wordGamma Kh (G ω) ℓ wd D j ρ γ) ∂μ =
        -(dOne b ρ * ∫ ω, blkTr (G ω) 0 * (G ω * wordVal Kh (G ω) wd D) ρ γ ∂μ +
            dTwo b ρ * ∫ ω, blkTr (G ω) 1 * (G ω * wordVal Kh (G ω) wd D) ρ γ ∂μ) -
          ∑ j, (dOne b ρ * ∫ ω, blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 0 *
              wordGamma Kh (G ω) ℓ wd D j ρ γ ∂μ +
            dTwo b ρ * ∫ ω, blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 1 *
              wordGamma Kh (G ω) ℓ wd D j ρ γ ∂μ) := by
      have i0 : Integrable (fun ω => dOne b ρ * (blkTr (G ω) 0 *
          (G ω * wordVal Kh (G ω) wd D) ρ γ)) μ := ((kGGN 0).2.2.1 ρ γ).const_mul (dOne b ρ)
      have i1 : Integrable (fun ω => dTwo b ρ * (blkTr (G ω) 1 *
          (G ω * wordVal Kh (G ω) wd D) ρ γ)) μ := ((kGGN 1).2.2.1 ρ γ).const_mul (dTwo b ρ)
      have i01 : Integrable (fun ω => -(dOne b ρ * (blkTr (G ω) 0 *
          (G ω * wordVal Kh (G ω) wd D) ρ γ) + dTwo b ρ * (blkTr (G ω) 1 *
          (G ω * wordVal Kh (G ω) wd D) ρ γ))) μ := (i0.add i1).neg
      have ij : ∀ j, Integrable (fun ω => (dOne b ρ * blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 0 +
            dTwo b ρ * blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 1) *
          wordGamma Kh (G ω) ℓ wd D j ρ γ) μ := fun j => by
        have := (((kj j 0).2.2.1 ρ γ).const_mul (dOne b ρ)).add (((kj j 1).2.2.1 ρ γ).const_mul (dTwo b ρ))
        refine this.congr (Eventually.of_forall fun ω => ?_)
        simp only [Pi.add_apply]; ring
      have e : (fun ω => -((dOne b ρ * blkTr (G ω) 0 + dTwo b ρ * blkTr (G ω) 1) *
          (G ω * wordVal Kh (G ω) wd D) ρ γ) -
          ∑ j, (dOne b ρ * blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 0 +
              dTwo b ρ * blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 1) *
            wordGamma Kh (G ω) ℓ wd D j ρ γ) = fun ω =>
          -(dOne b ρ * (blkTr (G ω) 0 * (G ω * wordVal Kh (G ω) wd D) ρ γ) +
            dTwo b ρ * (blkTr (G ω) 1 * (G ω * wordVal Kh (G ω) wd D) ρ γ)) -
          ∑ j, (dOne b ρ * blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 0 +
              dTwo b ρ * blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 1) *
            wordGamma Kh (G ω) ℓ wd D j ρ γ := by
        funext ω; ring
      rw [e, integral_sub i01 (integrable_finsetSum _ fun j _ => ij j),
        integral_neg, integral_add i0 i1, integral_const_mul, integral_const_mul,
        integral_finsetSum _ fun j _ => ij j]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have e2 : (fun ω => (dOne b ρ * blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 0 +
            dTwo b ρ * blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 1) *
          wordGamma Kh (G ω) ℓ wd D j ρ γ) = fun ω =>
          dOne b ρ * (blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 0 * wordGamma Kh (G ω) ℓ wd D j ρ γ) +
            dTwo b ρ * (blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 1 *
              wordGamma Kh (G ω) ℓ wd D j ρ γ) := by funext ω; ring
      rw [e2, integral_add (((kj j 0).2.2.1 ρ γ).const_mul _) (((kj j 1).2.2.1 ρ γ).const_mul _),
        integral_const_mul, integral_const_mul]
    have hm0 : meanTr b E X 0 = ∫ ω, blkTr (G ω) 0 ∂μ := by
      simp only [meanTr, trLetter_zero_eq]; rfl
    have hm3 : meanTr b E X 3 = ∫ ω, blkTr (G ω) 1 ∂μ := by
      simp only [meanTr, trLetter_three_eq]; rfl
    have hS : ∑ j, (dOne b ρ * cj j 0 ρ γ + dTwo b ρ * cj j 1 ρ γ) =
        ∑ j, (dOne b ρ * ∫ ω, blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 0 *
              wordGamma Kh (G ω) ℓ wd D j ρ γ ∂μ +
            dTwo b ρ * ∫ ω, blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 1 *
              wordGamma Kh (G ω) ℓ wd D j ρ γ ∂μ) -
        ∑ j, (dOne b ρ * ∫ ω, blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 0 ∂μ +
            dTwo b ρ * ∫ ω, blkTr (G ω * wordAlpha Kh (G ω) ℓ wd D j) 1 ∂μ) *
          matrixExpect μ (fun ω => wordGamma Kh (G ω) ℓ wd D j) ρ γ := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [cj, covMat_apply, matrixExpect, Matrix.of_apply]
      ring
    have hd : (dressed b E X * A) ρ γ = (H₀ * A) ρ γ -
        (dOne b ρ * meanTr b E X 0 + dTwo b ρ * meanTr b E X 3) * A ρ γ := by
      rw [show dressed b E X = H₀ - selfEnergy b (meanTr b E X 0) (meanTr b E X 3) from rfl,
        Matrix.sub_mul, Matrix.sub_apply, selfEnergy_mul_apply]
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.add_apply,
      Matrix.sum_apply]
    simp only [diagonal_mul, Matrix.add_apply]
    rw [hd, hS, hH, hR, hsplit, hm0, hm3,
      Finset.sum_congr rfl fun j _ => selfEnergy_mul_apply b _ _ _ ρ γ]
    simp only [c0, c1, covMat_apply, A, matrixExpect, Matrix.of_apply]
    ring
  rw [hid]
  have hn1 := norm_diag_dOne_le (W := W) hb0 hb
  have hn2 := norm_diag_dTwo_le (W := W) hb0 hb
  have hc : ∀ (M : LayerMat W) (d : LayerSite W .oneBlockOnePort → ℂ),
      ‖(diagonal d : LayerMat W)‖ ≤ 1 → ‖M‖ ≤ Ct / (W : ℝ) ^ 2 →
        ‖diagonal d * M‖ ≤ Ct / (W : ℝ) ^ 2 := fun M d h1 h2 =>
    (Matrix.l2_opNorm_mul _ _).trans (by
      calc ‖(diagonal d : LayerMat W)‖ * ‖M‖ ≤ 1 * (Ct / (W : ℝ) ^ 2) :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _)
  have hC0 : 0 ≤ Ct / (W : ℝ) ^ 2 := by positivity
  have hℓr : (ℓ : ℝ) ≤ Lw := by exact_mod_cast hℓ
  calc _ ≤ ‖diagonal (dOne b) * c0 + diagonal (dTwo b) * c1‖ +
        ‖∑ j, (diagonal (dOne b) * cj j 0 + diagonal (dTwo b) * cj j 1)‖ := norm_add_le _ _
    _ ≤ (Ct / (W : ℝ) ^ 2 + Ct / (W : ℝ) ^ 2) +
        ∑ _j : Fin ℓ, (Ct / (W : ℝ) ^ 2 + Ct / (W : ℝ) ^ 2) := by
      refine add_le_add ((norm_add_le _ _).trans (add_le_add (hc _ _ hn1 (kGGN 0).2.2.2)
        (hc _ _ hn2 (kGGN 1).2.2.2))) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
          (norm_add_le _ _).trans (add_le_add (hc _ _ hn1 (kj j 0).2.2.2)
            (hc _ _ hn2 (kj j 1).2.2.2))))
    _ = (1 + ℓ) * (2 * (Ct / (W : ℝ) ^ 2)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ (1 + Lw) * (2 * (Ct / (W : ℝ) ^ 2)) := by gcongr
    _ = _ := by ring

end BlockBand.Transmission.SourceMixing
