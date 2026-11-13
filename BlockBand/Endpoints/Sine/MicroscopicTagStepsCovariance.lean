module

public import BlockBand.Endpoints.Sine.MicroscopicTagInputs
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Relative Loewner closeness of the one-block covariances

This file proves `MicroscopicTagCovarianceCloseness` from `BlockRegularEventContract`
(`microscopicTagCovarianceStability_holds`): the fresh one-block covariance is within a relative
factor `1 ± ω₀` of the stationary one in the Loewner order, outside an event of small probability.

With `F = blockDeformation σ ω e` Hermitian, `m = freshDyson F c e`, `a = matchedA e`
(`commonZ b e = -e - ca`, so `Γ₀ = c|F - e - ca|⁻²` after reindexing) and `Γ = c|F - e - cm|⁻²`,
both are functions of `F`: in an eigenbasis `F = U diag(λ) U*`,
`|F - z|⁻² = U diag(|λ_i - z|⁻²) U*` (`mts_gram_inv_eq`). For real `λ`,
`|λ - e - ca| = |λ - e - c ā| ≥ c·h`, `h = -Im a = √(4-e²)/2`, and `|m - ā| ≤ η` gives
`|λ-e-cm| / |λ-e-cā| ∈ [1-δ, 1+δ]`, `δ = η/h`; for `δ ≤ min(ω₀/4, 1/4)` the eigenvalue ratios
lie in `[1-ω₀, 1+ω₀]` (`mts_ratio_bounds`). On `bulkInterval κ`, `h ≥ √(3 min(κ,1))/2`.
Probability: the regular event of `BlockRegularEventContract` (`D = 1`) fails with
`Pω`-probability `≤ W⁻¹ ≤ ε`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal ComplexOrder ComplexConjugate

/-!
## Scalar facts
-/

/-- `a = matchedA e` satisfies `a² + ea + 1 = 0` on `[-2, 2]`. -/
theorem mts_matchedA_quadratic {e : ℝ} (he : |e| ≤ 2) :
    matchedA e ^ 2 + (e : ℂ) * matchedA e + 1 = 0 := by
  have h4 : 0 ≤ 4 - e ^ 2 := by
    have := abs_le.1 he; nlinarith
  have hs : Real.sqrt (4 - e * e) * Real.sqrt (4 - e * e) = 4 - e * e :=
    Real.mul_self_sqrt (by nlinarith)
  apply Complex.ext <;> simp [matchedA, pow_two] <;> nlinarith [hs]

/-- `commonZ b e = -e - (1-2b) a`. -/
theorem mts_commonZ_eq {b e : ℝ} (he : |e| ≤ 2) :
    commonZ b e = -((e : ℂ) + ((1 - 2 * b : ℝ) : ℂ) * matchedA e) := by
  have hq := mts_matchedA_quadratic he
  have ha : matchedA e ≠ 0 := by
    intro h0; rw [h0] at hq; simp at hq
  have hinv : (matchedA e)⁻¹ = -(e : ℂ) - matchedA e :=
    inv_eq_of_mul_eq_one_right (by linear_combination -hq)
  unfold commonZ
  rw [hinv]
  push_cast
  ring

theorem mts_matchedA_im {e : ℝ} : (matchedA e).im = -(Real.sqrt (4 - e ^ 2) / 2) := by
  simp [matchedA, neg_div]

/-- The ratio bounds: if `x(1-δ) ≤ y ≤ x(1+δ)`, `0 ≤ δ ≤ min(ω/4, 1/4)`, then
`(1-ω)/x² ≤ 1/y² ≤ (1+ω)/x²`. -/
theorem mts_ratio_bounds {x y δ ω : ℝ} (hx : 0 < x) (hδ0 : 0 ≤ δ) (hδω : δ ≤ ω / 4)
    (hδ1 : δ ≤ 1 / 4) (hlo : x * (1 - δ) ≤ y) (hhi : y ≤ x * (1 + δ)) :
    (1 - ω) / x ^ 2 ≤ 1 / y ^ 2 ∧ 1 / y ^ 2 ≤ (1 + ω) / x ^ 2 := by
  have hy : 0 < y := lt_of_lt_of_le (by nlinarith) hlo
  have hx2 : 0 < x ^ 2 := by positivity
  constructor
  · rw [div_le_div_iff₀ hx2 (by positivity)]
    have h1 : y ^ 2 ≤ x ^ 2 * (1 + δ) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hy.le hhi 2
    have hω0 : 0 ≤ ω := by linarith
    have hk : (1 - ω) * (1 + δ) ^ 2 ≤ 1 := by
      by_cases hω1 : 1 ≤ ω
      · nlinarith [sq_nonneg (1 + δ)]
      · have h3 : (1 + δ) ^ 2 ≤ 1 + 3 * ω / 4 := by nlinarith
        have h4 : (1 - ω) * (1 + δ) ^ 2 ≤ (1 - ω) * (1 + 3 * ω / 4) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
        nlinarith
    rcases le_or_gt 0 (1 - ω) with h0 | h0
    · calc (1 - ω) * y ^ 2 ≤ (1 - ω) * (x ^ 2 * (1 + δ) ^ 2) := mul_le_mul_of_nonneg_left h1 h0
        _ = x ^ 2 * ((1 - ω) * (1 + δ) ^ 2) := by ring
        _ ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left hk hx2.le
        _ = 1 * x ^ 2 := by ring
    · nlinarith [sq_nonneg y]
  · rw [div_le_div_iff₀ (by positivity) hx2]
    have h1 : x ^ 2 * (1 - δ) ^ 2 ≤ y ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by nlinarith) hlo 2
    have hω0 : 0 ≤ ω := by linarith
    have h3 : 1 - 2 * δ ≤ (1 - δ) ^ 2 := by nlinarith
    have h5 : 1 ≤ (1 + ω) * (1 - 2 * δ) := by
      nlinarith [mul_le_mul_of_nonneg_left hδ1 hω0]
    have hk : 1 ≤ (1 + ω) * (1 - δ) ^ 2 :=
      h5.trans (mul_le_mul_of_nonneg_left h3 (by linarith))
    calc 1 * x ^ 2 ≤ x ^ 2 * ((1 + ω) * (1 - δ) ^ 2) := by nlinarith
      _ = (1 + ω) * (x ^ 2 * (1 - δ) ^ 2) := by ring
      _ ≤ (1 + ω) * y ^ 2 := mul_le_mul_of_nonneg_left h1 (by linarith)

/-!
## Functions of a Hermitian matrix
-/

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mts_conj_mul_conj (U A B : Matrix ι ι ℂ) (h : star U * U = 1) :
    U * A * star U * (U * B * star U) = U * (A * B) * star U := by
  calc U * A * star U * (U * B * star U) = U * A * (star U * U) * B * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * (A * B) * star U := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- For Hermitian `F` with eigenvector unitary `U` and `Im z ≠ 0`:
`((F - z)*(F - z))⁻¹ = U diag(|λ_i - z|⁻²) U*`. -/
theorem mts_gram_inv_eq {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ((F - z • 1)ᴴ * (F - z • 1))⁻¹ =
      (hF.eigenvectorUnitary : Matrix ι ι ℂ) *
        diagonal (fun i => (((‖((hF.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2)⁻¹ : ℝ) : ℂ)) *
        star (hF.eigenvectorUnitary : Matrix ι ι ℂ) := by
  set U : Matrix ι ι ℂ := ↑hF.eigenvectorUnitary
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : F = U * diagonal (fun i => ((hF.eigenvalues i : ℝ) : ℂ)) * star U := by
    have := hF.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, Function.comp_def] using this
  have hX : F - z • 1 = U * diagonal (fun i => ((hF.eigenvalues i : ℝ) : ℂ) - z) * star U := by
    conv_lhs => rw [hspec]
    have : (z • (1 : Matrix ι ι ℂ)) = U * (z • (1 : Matrix ι ι ℂ)) * star U := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
    rw [this, ← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hXH : (F - z • 1)ᴴ = U * diagonal (fun i => star (((hF.eigenvalues i : ℝ) : ℂ) - z)) *
      star U := by
    rw [hX, conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose]
    simp only [← Matrix.star_eq_conjTranspose, star_star, Matrix.mul_assoc]
    rfl
  have hne : ∀ i, ‖((hF.eigenvalues i : ℝ) : ℂ) - z‖ ≠ 0 := by
    intro i h0
    rw [norm_eq_zero, sub_eq_zero] at h0
    apply hz; rw [← h0]; simp
  apply Matrix.inv_eq_left_inv
  rw [hXH, hX, mts_conj_mul_conj U _ _ hU1, mts_conj_mul_conj U _ _ hU1, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  have : (fun i => (((‖((hF.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (star (((hF.eigenvalues i : ℝ) : ℂ) - z) * (((hF.eigenvalues i : ℝ) : ℂ) - z))) =
      fun _ => 1 := by
    funext i
    have h2 : star (((hF.eigenvalues i : ℝ) : ℂ) - z) * (((hF.eigenvalues i : ℝ) : ℂ) - z) =
        ((‖((hF.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [h2, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 2 (hne i)), Complex.ofReal_one]
  rw [this, diagonal_one, Matrix.mul_one, hU2]

/-- A linear combination of two matrices diagonal in the same unitary basis. -/
theorem mts_unitary_diag_comb (U : Matrix ι ι ℂ) (r s : ℝ) (d₁ d₂ : ι → ℝ) :
    (r : ℂ) • (U * diagonal (fun i => (d₁ i : ℂ)) * star U) -
        (s : ℂ) • (U * diagonal (fun i => (d₂ i : ℂ)) * star U) =
      U * diagonal (fun i => ((r * d₁ i - s * d₂ i : ℝ) : ℂ)) * star U := by
  have : diagonal (fun i => ((r * d₁ i - s * d₂ i : ℝ) : ℂ)) =
      (r : ℂ) • diagonal (fun i => (d₁ i : ℂ)) - (s : ℂ) • diagonal (fun i => (d₂ i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [diagonal_apply_ne _ hij]
  rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul]

theorem mts_unitary_diag_posSemidef (U : Matrix ι ι ℂ) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (U * diagonal (fun i => (d i : ℂ)) * star U).PosSemidef := by
  rw [Matrix.star_eq_conjTranspose]
  refine PosSemidef.mul_mul_conjTranspose_same ?_ U
  rw [posSemidef_diagonal_iff]
  intro i
  exact Complex.zero_le_real.2 (hd i)

/-- **Deterministic relative Loewner bound.** For Hermitian `F`, `c > 0`, `m, a ∈ ℂ` with
`h := -Im a > 0` and `‖m - ā‖ ≤ δh`, `δ ≤ min(ω/4, 1/4)`:
`(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`, `Γ = c|F - e - cm|⁻²`, `Γ₀ = c|F - e - ca|⁻²`. -/
theorem mts_relLoewner {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {c e ω δ : ℝ} (hc : 0 < c)
    {m a : ℂ} (ha : a.im < 0) (hδ0 : 0 ≤ δ) (hδω : δ ≤ ω / 4) (hδ1 : δ ≤ 1 / 4)
    (hm : ‖m - conj a‖ ≤ δ * (-a.im)) :
    let Γ := (c : ℂ) • ((F - ((e : ℂ) + (c : ℂ) * m) • 1)ᴴ * (F - ((e : ℂ) + (c : ℂ) * m) • 1))⁻¹
    let Γ₀ := (c : ℂ) • ((F - ((e : ℂ) + (c : ℂ) * a) • 1)ᴴ * (F - ((e : ℂ) + (c : ℂ) * a) • 1))⁻¹
    (((1 + ω : ℝ) : ℂ) • Γ₀ - Γ).PosSemidef ∧ (Γ - ((1 - ω : ℝ) : ℂ) • Γ₀).PosSemidef := by
  intro Γ Γ₀
  set h := -a.im with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  have hmim : 0 < m.im := by
    have h1 : |(m - conj a).im| ≤ ‖m - conj a‖ := Complex.abs_im_le_norm _
    have h2 : (m - conj a).im = m.im - h := by simp [hh]
    rw [h2] at h1
    have := (abs_le.1 (h1.trans hm)).1
    nlinarith
  have hzm : ((e : ℂ) + (c : ℂ) * m).im ≠ 0 := by
    rw [show ((e : ℂ) + (c : ℂ) * m).im = c * m.im by simp]; positivity
  have hza : ((e : ℂ) + (c : ℂ) * a).im ≠ 0 := by
    rw [show ((e : ℂ) + (c : ℂ) * a).im = c * a.im by simp]
    exact mul_ne_zero hc.ne' ha.ne
  set U : Matrix ι ι ℂ := ↑hF.eigenvectorUnitary
  set lam := hF.eigenvalues
  set dM : ι → ℝ := fun i => (‖((lam i : ℝ) : ℂ) - ((e : ℂ) + (c : ℂ) * m)‖ ^ 2)⁻¹
  set dA : ι → ℝ := fun i => (‖((lam i : ℝ) : ℂ) - ((e : ℂ) + (c : ℂ) * a)‖ ^ 2)⁻¹
  have hΓ : Γ = (c : ℂ) • (U * diagonal (fun i => (dM i : ℂ)) * star U) := by
    simp only [Γ]; rw [mts_gram_inv_eq hF hzm]
  have hΓ₀ : Γ₀ = (c : ℂ) • (U * diagonal (fun i => (dA i : ℂ)) * star U) := by
    simp only [Γ₀]; rw [mts_gram_inv_eq hF hza]
  -- the eigenvalue-wise bounds
  have hb : ∀ i, (1 - ω) * dA i ≤ dM i ∧ dM i ≤ (1 + ω) * dA i := by
    intro i
    set A : ℂ := ((lam i : ℝ) : ℂ) - ((e : ℂ) + (c : ℂ) * conj a)
    set Mi : ℂ := ((lam i : ℝ) : ℂ) - ((e : ℂ) + (c : ℂ) * m)
    have hAeq : ‖((lam i : ℝ) : ℂ) - ((e : ℂ) + (c : ℂ) * a)‖ = ‖A‖ := by
      rw [← Complex.norm_conj]; congr 1; simp [A, map_sub, map_add, map_mul]
    have hAlow : c * h ≤ ‖A‖ := by
      have h1 : |A.im| ≤ ‖A‖ := Complex.abs_im_le_norm _
      have h2 : A.im = -(c * h) := by simp [A, hh]
      rw [h2, abs_neg, abs_of_pos (mul_pos hc hh0)] at h1
      exact h1
    have hAp : 0 < ‖A‖ := lt_of_lt_of_le (mul_pos hc hh0) hAlow
    have hdiff : ‖Mi - A‖ ≤ c * (δ * h) := by
      have : Mi - A = -((c : ℂ) * (m - conj a)) := by simp only [Mi, A]; ring
      rw [this, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
      exact mul_le_mul_of_nonneg_left hm hc.le
    have hlo : ‖A‖ * (1 - δ) ≤ ‖Mi‖ := by
      have := norm_sub_norm_le A (A - Mi)
      rw [sub_sub_cancel] at this
      rw [norm_sub_rev] at hdiff
      nlinarith [mul_le_mul_of_nonneg_left hAlow hδ0]
    have hhi : ‖Mi‖ ≤ ‖A‖ * (1 + δ) := by
      have := norm_add_le A (Mi - A)
      rw [add_sub_cancel] at this
      nlinarith [mul_le_mul_of_nonneg_left hAlow hδ0]
    obtain ⟨r1, r2⟩ := mts_ratio_bounds hAp hδ0 hδω hδ1 hlo hhi
    simp only [dM, dA, hAeq]
    constructor
    · have := r1; simp only [div_eq_mul_inv, one_mul] at this; exact this
    · have := r2; simp only [div_eq_mul_inv, one_mul] at this; exact this
  constructor
  · rw [hΓ, hΓ₀, smul_smul, ← Complex.ofReal_mul, mts_unitary_diag_comb]
    refine mts_unitary_diag_posSemidef U _ fun i => ?_
    have := (hb i).2
    nlinarith
  · rw [hΓ, hΓ₀, smul_smul, ← Complex.ofReal_mul, mts_unitary_diag_comb]
    refine mts_unitary_diag_posSemidef U _ fun i => ?_
    have := (hb i).1
    nlinarith

end Gram

/-!
## Reindexing of the one-block covariance
-/

theorem mts_reindex_gramInv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (σ : ι ≃ κ) (c : ℂ) (X : Matrix ι ι ℂ) :
    Matrix.reindex σ σ (c • (Xᴴ * X)⁻¹) =
      c • ((Matrix.reindex σ σ X)ᴴ * Matrix.reindex σ σ X)⁻¹ := by
  simp only [Matrix.reindex_apply, conjTranspose_submatrix]
  rw [submatrix_mul_equiv, inv_submatrix_equiv]
  rfl

theorem mts_reindex_blockGamma0 (p : Parameters) (k : ZMod p.n)
    (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (ω : BlockState p k) {e : ℝ}
    (he : |e| ≤ 2) :
    Matrix.reindex σ σ (mts_blockGamma0 p k ω e) =
      (p.c : ℂ) • ((blockDeformation p k σ ω e - ((e : ℂ) + (p.c : ℂ) * matchedA e) • 1)ᴴ *
        (blockDeformation p k σ ω e - ((e : ℂ) + (p.c : ℂ) * matchedA e) • 1))⁻¹ := by
  unfold mts_blockGamma0
  rw [mts_reindex_gramInv]
  have : Matrix.reindex σ σ (commonZ p.b e • (1 : Matrix (BlockSite p k) (BlockSite p k) ℂ) +
      blockF p k ω e) = blockDeformation p k σ ω e - ((e : ℂ) + (p.c : ℂ) * matchedA e) • 1 := by
    ext i j
    rw [mts_commonZ_eq he]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Equiv.apply_eq_iff_eq, blockDeformation,
      Parameters.c, smul_eq_mul]
    split_ifs <;> ring
  rw [this]

/-!
## The covariance closeness
-/

/-- **Covariance closeness** from `BlockRegularEventContract`
(regularity constants at the margin `κ`, `D = 1`, `η = √(3 min(κ,1))/2 · min(ω₀/4, 1/4)`):
`MicroscopicTagCovarianceCloseness`.
-/
theorem microscopicTagCovarianceStability_holds (hReg : BlockRegularEventContract) :
    MicroscopicTagCovarianceCloseness := by
  intro b hb hb' κ T hκ ω₀ hω₀ ε hε
  obtain ⟨r₀, s₀, v₀, -, hD⟩ := hReg b hb hb' κ T hκ
  obtain ⟨A, hA⟩ := hD 1 one_pos
  set h0 := Real.sqrt (3 * min κ 1) / 2 with hh0
  have hh0p : 0 < h0 := by
    rw [hh0]; exact div_pos (Real.sqrt_pos.2 (by positivity)) (by norm_num)
  set δ := min (ω₀ / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  obtain ⟨W₁, hW₁⟩ := hA (h0 * δ) (mul_pos hh0p hδ)
  refine ⟨max W₁ (⌈ε⁻¹⌉₊ + 1), ?_⟩
  intro p hpb hW hn model k Pω hs σ e he
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  refine (measure_mono ?_).trans ((hW₁ p hpb ((le_max_left _ _).trans hW) hn model k Pω hs σ e
    he).trans ?_)
  · intro ω hω hreg
    apply hω
    obtain ⟨⟨hF, -, -⟩, hm⟩ := hreg
    have he2 : |e| ≤ 2 := by
      have := he.1; have := he.2
      rw [abs_le]; constructor <;> linarith
    -- the height `h = √(4-e²)/2 ≥ h0`
    have hah : h0 ≤ -(matchedA e).im := by
      rw [mts_matchedA_im, neg_neg, hh0]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Real.sqrt_le_sqrt
      have hk1 : min κ 1 ≤ 1 := min_le_right _ _
      have hkk : min κ 1 ≤ κ := min_le_left _ _
      have hm0 : 0 ≤ min κ 1 := le_min hκ.le zero_le_one
      have h1 := he.1; have h2 := he.2
      nlinarith
    have ha : (matchedA e).im < 0 := by linarith
    have hm' : ‖freshDyson (blockDeformation p k σ ω e) p.c e - conj (matchedA e)‖ ≤
        δ * (-(matchedA e).im) := by
      have : p.b = b := hpb
      calc _ ≤ h0 * δ := by simpa [this] using hm
        _ ≤ δ * (-(matchedA e).im) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hah hδ.le
    have key := mts_relLoewner (e := e) hF p.c_pos ha hδ.le (min_le_left _ _)
      (min_le_right _ _) hm'
    rw [mts_reindex_blockGamma0 p k σ ω he2]
    unfold freshGamma
    exact key
  · have hc : (⌈ε⁻¹⌉₊ : ℝ) + 1 ≤ p.W := by
      exact_mod_cast (le_max_right _ _).trans hW
    have hε' : ε⁻¹ ≤ p.W := by linarith [Nat.le_ceil ε⁻¹]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_neg_one]
    calc (p.W : ℝ)⁻¹ ≤ (ε⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hε) hε'
      _ = ε := inv_inv ε

end BlockBand.Endpoints
