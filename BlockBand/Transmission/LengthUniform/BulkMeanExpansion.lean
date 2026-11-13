module

public import BlockBand.Transmission.SourceMixing.MeanExpansion
public import BlockBand.Transmission.LengthUniform.BulkExpansion

/-!
# Bulk-uniform trace–matrix covariances and mean-field expansion

The multi-letter dressed trace–matrix covariance bound and the mean-field expansion of
`E[𝒢·w(𝒢)]`, uniformly in `E ∈ bulkInterval κ`: the constants and `W₀` depend only on `b`, the bulk
margin `κ` and the word data.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Multi-letter dressed trace–matrix covariance in operator norm.**
Bulk-uniform copy of `wordTraceCov`: constants uniform over `E ∈ bulkInterval κ`. -/
theorem wordTraceCov_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ₁ : ℕ, ℓ₁ ≤ Lw → ∀ (wd₁ : Fin ℓ₁ → Fin 4)
      (D₁ : Fin (ℓ₁ + 1) → LayerMat W), (∀ j, ‖D₁ j‖ ≤ Kd) → ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw →
      ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W), (∀ j, ‖D₂ j‖ ≤ Kd) →
      ∀ r : Fin 2,
        Integrable (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r)
          (layerLaw W b .oneBlockOnePort) ∧
        (∀ α β, Integrable (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂ α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        (∀ α β, Integrable (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r *
          wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂ α β) (layerLaw W b .oneBlockOnePort)) ∧
        ‖covMat (layerLaw W b .oneBlockOnePort)
            (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r)
            (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C₀, W₀, h⟩ := hA.traceMatrix b hb0 hb _ hκ Lw Kd
  refine ⟨4 * (4 ^ Lw * 4 ^ Lw * max C₀ 0), W₀, by positivity,
    fun W hW E hE X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ r => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  set μ := layerLaw W b .oneBlockOnePort
  set z := boundaryZ b E
  -- the passive pieces
  set f : (Fin ℓ₁ → Fin 2 × Fin 2) → LayerSample W .oneBlockOnePort → ℂ := fun π ω =>
    (W : ℂ)⁻¹ * (passiveWord E z X (pathWd wd₁ π) (pathD ℓ₁ D₁ r r π) ω).trace
  set U : Fin 2 → Fin 2 → (Fin ℓ₂ → Fin 2 × Fin 2) → LayerSample W .oneBlockOnePort →
      Matrix (Fin W) (Fin W) ℂ := fun s t π ω => passiveWord E z X (pathWd wd₂ π) (pathD ℓ₂ D₂ s t π) ω
  have hf : ∀ ω, blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r = ∑ π, f π ω := fun ω => by
    rw [blkTr, blkAt_wordVal, Matrix.trace_sum, Finset.mul_sum]
  have hU : ∀ ω s t, blkAt (wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂) s t = ∑ π, U s t π ω :=
    fun ω s t => blkAt_wordVal b E X ω ℓ₂ wd₂ D₂ s t
  have hpc : ∀ s t π₁ π₂, Integrable (f π₁) μ ∧ (∀ x y, Integrable (fun ω => U s t π₂ ω x y) μ) ∧
      (∀ x y, Integrable (fun ω => f π₁ ω * U s t π₂ ω x y) μ) ∧
      ‖covMat μ (f π₁) (U s t π₂)‖ ≤ C₀ / (W : ℝ) ^ 2 := fun s t π₁ π₂ =>
    h W hW E hE _ (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX
      ℓ₁ ℓ₂ hℓ₁ hℓ₂ (pathWd wd₁ π₁) (pathD ℓ₁ D₁ r r π₁) (pathWd wd₂ π₂) (pathD ℓ₂ D₂ s t π₂)
      (norm_pathD_le ℓ₁ D₁ hD₁ r r π₁) (norm_pathD_le ℓ₂ D₂ hD₂ s t π₂)
  have hπ : ∀ π : Fin ℓ₁ → Fin 2 × Fin 2, Integrable (f π) μ :=
    fun π => (hpc 0 0 π fun _ => (0, 0)).1
  have hent : ∀ ω (s t : Fin 2) (x y : Fin W),
      wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂ (siteOf s x) (siteOf t y) = ∑ π, U s t π ω x y :=
    fun ω s t x y => by
      have := congrFun (congrFun (hU ω s t) x) y
      simpa [blkAt, Matrix.sum_apply] using this
  have hfi : Integrable (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r) μ := by
    simp only [hf]; exact integrable_finsetSum _ fun π _ => hπ π
  refine ⟨hfi, fun α β => ?_, fun α β => ?_, ?_⟩
  · obtain ⟨s, x, rfl⟩ := exists_siteOf α
    obtain ⟨t, y, rfl⟩ := exists_siteOf β
    simp only [hent]
    exact integrable_finsetSum _ fun π _ => (hpc s t (fun _ => (0, 0)) π).2.1 x y
  · obtain ⟨s, x, rfl⟩ := exists_siteOf α
    obtain ⟨t, y, rfl⟩ := exists_siteOf β
    simp only [hent, hf, Finset.sum_mul, Finset.mul_sum]
    exact integrable_finsetSum _ fun π₂ _ => integrable_finsetSum _ fun π₁ _ =>
      (hpc s t π₁ π₂).2.2.1 x y
  · have hblk : ∀ s t, ‖blkAt (covMat μ (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r)
        (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂)) s t‖ ≤
          4 ^ Lw * 4 ^ Lw * max C₀ 0 / (W : ℝ) ^ 2 := fun s t => by
      rw [blkAt_covMat]
      have e1 : (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r) =
          fun ω => ∑ π, f π ω := funext hf
      have e2 : (fun ω => blkAt (wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂) s t) =
          fun ω => ∑ π, U s t π ω := funext fun ω => hU ω s t
      rw [e1, e2, covMat_sum_sum f (U s t) hπ (fun π => (hpc s t (fun _ => (0, 0)) π).2.1)
        (fun π₁ π₂ => (hpc s t π₁ π₂).2.2.1)]
      have hC : 0 ≤ max C₀ 0 / (W : ℝ) ^ 2 := by positivity
      calc ‖∑ π₁, ∑ π₂, covMat μ (f π₁) (U s t π₂)‖
          ≤ ∑ _π₁ : Fin ℓ₁ → Fin 2 × Fin 2, ∑ _π₂ : Fin ℓ₂ → Fin 2 × Fin 2,
              max C₀ 0 / (W : ℝ) ^ 2 :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun π₁ _ => (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun π₂ _ => (hpc s t π₁ π₂).2.2.2.trans
                (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))))
        _ = (4 : ℝ) ^ ℓ₁ * (4 ^ ℓ₂ * (max C₀ 0 / (W : ℝ) ^ 2)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_prod,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
        _ ≤ (4 : ℝ) ^ Lw * (4 ^ Lw * (max C₀ 0 / (W : ℝ) ^ 2)) := by
            gcongr <;> norm_num
        _ = _ := by ring
    calc _ ≤ _ := norm_layerMat_le' _
      _ ≤ _ := add_le_add (add_le_add (add_le_add (hblk 0 0) (hblk 0 1)) (hblk 1 0)) (hblk 1 1)
      _ = _ := by ring

/-- The unified row form of `expansion_phys`/`expansion_port`.
Bulk-uniform copy of `expansion_rows`: constants uniform over `E ∈ bulkInterval κ`. -/
theorem expansion_rows_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
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
  obtain ⟨W₁, hp⟩ := expansion_phys_bulk hA hb0 hb hκ Lw Kd
  obtain ⟨W₂, hq⟩ := expansion_port_bulk hA hb0 hb hκ Lw Kd
  refine ⟨max W₁ W₂, fun W hW E hE X hX ℓ hℓ wd D hD ρ γ => ?_⟩
  have h0 : ∀ a : Fin 1, a = 0 := fun a => Subsingleton.elim _ _
  rcases ρ with ⟨i0, x⟩ | ⟨i0, x⟩ <;> rw [h0 i0]
  · rw [hp W (le_trans (le_max_left _ _) hW) E hE X hX ℓ hℓ wd D hD x γ]
    simp only [sPhys, dOne, dTwo, Sum.elim_inl]
  · rw [hq W (le_trans (le_max_right _ _) hW) E hE X hX ℓ hℓ wd D hD x γ]
    simp only [sPort, dOne, dTwo, Sum.elim_inr, zero_mul, add_zero]

/-- **The mean-field expansion of `E[𝒢·w(𝒢)]`.**
Bulk-uniform copy of `meanExpansion`: constants uniform over `E ∈ bulkInterval κ`. -/
theorem meanExpansion_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨W₁, hrow⟩ := expansion_rows_bulk hA hb0 hb hκ Lw Kd
  obtain ⟨Ct, Wt, hCt, htc⟩ := wordTraceCov_bulk hA hb0 hb hκ (Lw + 1) (max Kd 1)
  obtain ⟨_, Wm, hmom⟩ := hA.moments b hb0 hb _ hκ 1 le_rfl
  refine ⟨2 * (Lw + 1) * Ct, max (max W₁ Wt) Wm, by positivity,
    fun W hW E hE X hX ℓ hℓ wd D hD => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
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
    htc W hWt E hE X hX.posSemidef s₁.len s₁.hlen s₁.wd s₁.D s₁.hD s₂.len s₂.hlen s₂.wd s₂.D s₂.hD r
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
    filter_upwards [(hmom W hWm E hE _
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
    have hR := hrow W hW1 E hE X hX ℓ hℓ wd D hD ρ γ
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

end BlockBand.Transmission.LengthUniform
