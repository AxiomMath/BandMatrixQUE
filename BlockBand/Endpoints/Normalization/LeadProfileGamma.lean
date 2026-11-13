module

public import BlockBand.Internal.Contracts.ClocksLeadProfile
public import BlockBand.Endpoints.Normalization.GammaComparison
public import BlockBand.Layers.MatchedScalar

/-!
# `BlockGammaClosenessContract` from the block regular event

We prove `blockGammaCloseness_of (hReg : BlockRegularEventContract) :
BlockGammaClosenessContract`: for fixed
`b ∈ (0,1/2)`, `κ > 0`, `T` and every `ε > 0` there is `W₀`; for `W ≥ W₀`, `4 ≤ n ≤ TW`, every
model, block `k`, one-block splitting law `Pω`, reindexing `σ` and `e ∈ bulkInterval κ`, the
`Pω`-(outer) probability that `(1-ε)Γ₀ ⪯ Γ ⪯ (1+ε)Γ₀` fails is at most `ε`,
`Γ = freshGamma (blockDeformation σ ω e) c e`, `Γ₀ = reindex σ σ (c|z₀ - Σ|^{-2})`.

**Proof.**
1. *Matched scalar.* `z₀ = -e - c a` on `[-2,2]` (`commonZ_eq`), so
   `reindex σ σ (z₀ + blockF) = F - (e + c a)` with `F = blockDeformation σ ω e`, and
   `reindex σ σ (blockMatchedGamma) = gammaAt F c e a` (`reindex_blockMatchedGamma`).
2. *Conjugation.* For Hermitian `F`,
   `(F - w)ᴴ(F - w) = F² - (w + w̄)F + |w|²` is invariant under `w ↦ w̄`; with `w = e + c a`
   (`e, c` real) this gives `gammaAt F c e a = gammaAt F c e (conj a) = gammaMatched F c e`
   (`gammaAt_conj`).
3. *Loewner.* On the regular event `IsBlockRegular … η e ω` (`F` Hermitian, `‖m - conj a‖ ≤ η`),
   `blockRegular_freshGamma_loewner` gives relative error
   `γ = gammaConst e · η`; with `η = min(ερ_κ/8, ρ_κ/2)`, `ρ_κ = √(min κ 1)/2 ≤ Im conj a(e)` on
   `bulkInterval κ`, `γ ≤ ε`, and `Γ₀ ⪰ 0` widens `γ` to `ε`.
4. *Probability.* `BlockRegularEventContract` at `D = 1` bounds the failure of the regular event
   by `W^{-1} ≤ ε` for `W ≥ max(W₀(η), ⌈1/ε⌉)`; monotonicity of the outer measure.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ComplexConjugate ComplexOrder Matrix ENNReal

namespace LeadProfile

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(F - w)ᴴ(F - w) = F² - (w + w̄)F + w̄w` for Hermitian `F`. -/
theorem shift_gram {F : Matrix ι ι ℂ} (hF : F.IsHermitian) (w : ℂ) :
    (F - w • 1)ᴴ * (F - w • 1) = F * F - (w + star w) • F + (star w * w) • 1 := by
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hF.eq]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_smul]
  module

/-- The Gram matrix of a scalar shift of a Hermitian matrix is invariant under conjugating the
shift. -/
theorem shift_gram_conj {F : Matrix ι ι ℂ} (hF : F.IsHermitian) (w : ℂ) :
    (F - star w • 1)ᴴ * (F - star w • 1) = (F - w • 1)ᴴ * (F - w • 1) := by
  rw [shift_gram hF, shift_gram hF, star_star, add_comm (star w) w, mul_comm]

omit [DecidableEq ι] in
theorem reindex_mul' {κ : Type*} [Fintype κ] (σ : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    Matrix.reindex σ σ (A * B) = Matrix.reindex σ σ A * Matrix.reindex σ σ B := by
  simp only [reindex_apply]
  exact (submatrix_mul_equiv A B _ _ _).symm

omit [Fintype ι] [DecidableEq ι] in
theorem reindex_smul' {κ : Type*} (σ : ι ≃ κ) (c : ℂ) (A : Matrix ι ι ℂ) :
    Matrix.reindex σ σ (c • A) = c • Matrix.reindex σ σ A := by
  ext i j
  simp [reindex_apply]

end LeadProfile

variable {N : ℕ}

/-- `Γ_{conj m} = Γ_m` for Hermitian `F` (real `c₀`, `E`). -/
theorem gammaAt_conj {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (c₀ E : ℝ) (m : ℂ) :
    gammaAt F c₀ E (conj m) = gammaAt F c₀ E m := by
  unfold gammaAt
  have hw : ((E : ℂ) + (c₀ : ℂ) * conj m) = star ((E : ℂ) + (c₀ : ℂ) * m) := by
    simp [Complex.conj_ofReal]
  rw [hw, LeadProfile.shift_gram_conj hF]

section Block

variable (p : Parameters) (k : ZMod p.n)

/-- `reindex σ σ (z₀ + blockF) = F - (e + c a)`, `F = blockDeformation σ ω e`, on `[-2,2]`. -/
theorem reindex_blockShifted (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (ω : BlockState p k) {e : ℝ} (he : |e| ≤ 2) :
    Matrix.reindex σ σ (blockShifted p k ω e) =
      blockDeformation p k σ ω e - ((e : ℂ) + (p.c : ℂ) * matchedA e) • 1 := by
  unfold blockShifted blockDeformation
  rw [BlockBand.Layers.commonZ_eq he]
  ext i j
  simp only [reindex_apply, submatrix_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, smul_eq_mul,
    Parameters.c]
  push_cast
  split_ifs <;> ring

/-- `reindex σ σ (c|z₀ - Σ|^{-2}) = Γ_a(F)` with `F = blockDeformation σ ω e`, on `[-2,2]`. -/
theorem reindex_blockMatchedGamma (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (ω : BlockState p k) {e : ℝ} (he : |e| ≤ 2) :
    Matrix.reindex σ σ (blockMatchedGamma p k ω e) =
      gammaAt (blockDeformation p k σ ω e) p.c e (matchedA e) := by
  unfold blockMatchedGamma gammaAt
  rw [← reindex_blockShifted p k σ ω he, LeadProfile.reindex_smul', ← inv_reindex,
    LeadProfile.reindex_mul', conjTranspose_reindex]

/-- On `[-2,2]`, for Hermitian `F = blockDeformation σ ω e`, the matched covariance of
`ClocksLeadProfile` is `gammaMatched`. -/
theorem reindex_blockMatchedGamma_eq_gammaMatched
    (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (ω : BlockState p k) {e : ℝ}
    (he : |e| ≤ 2) (hF : (blockDeformation p k σ ω e).IsHermitian) :
    Matrix.reindex σ σ (blockMatchedGamma p k ω e) =
      gammaMatched (blockDeformation p k σ ω e) p.c e := by
  rw [reindex_blockMatchedGamma p k σ ω he, gammaMatched, gammaAt_conj hF]

end Block

/-- A uniform lower bound for `Im conj a(e) = √(4-e²)/2` on `bulkInterval κ`. -/
theorem matchedIm_ge_of_mem_bulkInterval {κ e : ℝ} (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    Real.sqrt (min κ 1) / 2 ≤ matchedIm e := by
  unfold matchedIm
  obtain ⟨h1, h2⟩ := he
  have hκ2 : κ ≤ 2 := by linarith
  have hab : |e| ≤ 2 - κ := abs_le.mpr ⟨by linarith, h2⟩
  have hsq : e ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg e) hab 2
  have : min κ 1 ≤ 4 - e ^ 2 := by
    have := min_le_left κ 1
    nlinarith
  gcongr

theorem mem_bulkInterval_bounds {κ e : ℝ} (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    -2 < e ∧ e < 2 ∧ |e| ≤ 2 := by
  obtain ⟨h1, h2⟩ := he
  exact ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- Widening a relative Loewner sandwich: if `(1+γ)Γ₀ - Γ ⪰ 0`, `Γ - (1-γ)Γ₀ ⪰ 0`, `Γ₀ ⪰ 0`
and `γ ≤ ε`, the same holds with `ε`. -/
theorem loewner_widen {ι : Type*} [Fintype ι] {Γ₀ Γ : Matrix ι ι ℂ} {γ ε : ℝ} (hΓ₀ : Γ₀.PosSemidef)
    (hγ : γ ≤ ε)
    (h : ((((1 + γ : ℝ) : ℂ) • Γ₀ - Γ).PosSemidef ∧ (Γ - ((1 - γ : ℝ) : ℂ) • Γ₀).PosSemidef)) :
    ((((1 + ε : ℝ) : ℂ) • Γ₀ - Γ).PosSemidef ∧ (Γ - ((1 - ε : ℝ) : ℂ) • Γ₀).PosSemidef) := by
  have hd : (((ε - γ : ℝ) : ℂ) • Γ₀).PosSemidef := hΓ₀.smul (by exact_mod_cast sub_nonneg.mpr hγ)
  constructor
  · have := h.1.add hd
    convert this using 1
    push_cast
    module
  · have := h.2.add hd
    convert this using 1
    push_cast
    module

/-- **`BlockGammaClosenessContract`**, from `BlockRegularEventContract`. -/
theorem blockGammaCloseness_of (hReg : BlockRegularEventContract) :
    BlockGammaClosenessContract := by
  intro b hb hb' κ T hκ ε hε
  obtain ⟨r₀, s₀, v₀, -, hrest⟩ := hReg b hb hb' κ T hκ
  obtain ⟨A, hA⟩ := hrest 1 one_pos
  set ρ : ℝ := Real.sqrt (min κ 1) / 2 with hρ
  have hρpos : 0 < ρ := by
    have : 0 < min κ 1 := lt_min hκ one_pos
    positivity
  set η : ℝ := min (ε * ρ / 8) (ρ / 2) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  obtain ⟨W₁, hW₁⟩ := hA η hηpos
  refine ⟨max W₁ (⌈ε⁻¹⌉₊ + 1), ?_⟩
  intro p hpb hW hnT model k Pω hsplit σ e he
  have hW1 : W₁ ≤ p.W := (le_max_left _ _).trans hW
  have hW2 : ⌈ε⁻¹⌉₊ + 1 ≤ p.W := (le_max_right _ _).trans hW
  obtain ⟨he1, he2, hea⟩ := mem_bulkInterval_bounds hκ he
  have hρe : ρ ≤ matchedIm e := matchedIm_ge_of_mem_bulkInterval hκ he
  have hmIm : 0 < matchedIm e := matchedIm_pos he1 he2
  -- the regular event implies closeness at `ε`
  have hsub : {ω : BlockState p k | ¬ ((((1 + ε : ℝ) : ℂ) • Matrix.reindex σ σ
        (blockMatchedGamma p k ω e) - freshGamma (blockDeformation p k σ ω e) p.c e).PosSemidef ∧
      (freshGamma (blockDeformation p k σ ω e) p.c e -
        ((1 - ε : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p k ω e)).PosSemidef)} ⊆
      {ω | ¬ IsBlockRegular p k σ A r₀ s₀ v₀ η e ω} := by
    intro ω hω hreg
    apply hω
    have hF : (blockDeformation p k σ ω e).IsHermitian := hreg.1.1
    have hηρ : η ≤ matchedIm e / 2 := (min_le_right _ _).trans (by linarith)
    have hL := blockRegular_freshGamma_loewner p k σ hreg he1 he2 hηρ
    rw [reindex_blockMatchedGamma_eq_gammaMatched p k σ ω hea hF]
    have hcpos : 0 < p.c := by have := p.b_lt_half; unfold Parameters.c; linarith
    have hΓ₀ : (gammaMatched (blockDeformation p k σ ω e) p.c e).PosSemidef :=
      gammaAt_posSemidef hF hcpos e (by rw [im_conj_matchedA]; exact hmIm)
    refine loewner_widen hΓ₀ ?_ hL
    -- `gammaConst e * η ≤ (8/ρ) (ερ/8) = ε`
    unfold gammaConst
    have h1 : η ≤ ε * ρ / 8 := min_le_left _ _
    calc 8 / matchedIm e * η ≤ 8 / ρ * η := by gcongr
      _ ≤ 8 / ρ * (ε * ρ / 8) := by gcongr
      _ = ε := by field_simp
  refine (measure_mono hsub).trans ((hW₁ p hpb hW1 hnT model k Pω hsplit σ e he).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  -- `W^{-1} ≤ ε` for `W ≥ ⌈1/ε⌉ + 1`
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  rw [Real.rpow_neg_one]
  have hceil : ε⁻¹ ≤ (p.W : ℝ) := by
    have := Nat.le_ceil ε⁻¹
    have h2 : ((⌈ε⁻¹⌉₊ + 1 : ℕ) : ℝ) ≤ p.W := by exact_mod_cast hW2
    push_cast at h2
    linarith
  rw [inv_le_comm₀ hWpos hε]
  exact hceil

end BlockBand.Endpoints.Normalization
