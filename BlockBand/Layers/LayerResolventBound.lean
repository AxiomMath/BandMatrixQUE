module

public import BlockBand.Layers.AbsorberUniform
public import BlockBand.Internal.Contracts.Layers

/-!
# The deterministic layer-resolvent bound (the Gaussian absorption lemma, block inverse step)

The deterministic part of the Gaussian absorption lemma: from the deterministic absorber bound
`‖(D - z⁻¹BB*)⁻¹‖ ≤ C(1+K)⁴ d⁻² δ⁻²`, "the block inverse formula proves it for `𝒢`".

Setting: finite index types `n` (physical) and `m` (ports); matrices over `ℂ`; every matrix norm
is the `ℓ²` operator norm (`Matrix.Norms.L2Operator`) and every vector norm is the Euclidean norm
of `EuclideanSpace ℂ _`, matrices acting through `Matrix.toEuclideanLin`.

* `isUnit_det_and_norm_inv_le_of_lower`: a lower bound `c‖x‖ ≤ ‖T x‖`, `c > 0`, gives
  `T` invertible with `‖T⁻¹‖ ≤ c⁻¹`.
* `absorber_matrix_lower`, `absorber_matrix_inv`: matrix transfer of
  `BlockBand.Layers.absorber_lower` to `T = D - z⁻¹ B Bᴴ`, `D` Hermitian:
  `‖T⁻¹‖ ≤ absorberConstant (-z⁻¹)² (1+K)⁴ / (dδ)²`.
* `fromBlocks_lower`, `fromBlocks_inv`: the block inverse step. If `T` is invertible and
  `z ≠ 0`, then `𝒢⁻¹ = [[D, B], [Bᴴ, z]]` is invertible and
  `‖𝒢‖ ≤ (1 + ‖B‖/|z|)² ‖T⁻¹‖ + |z|⁻¹` (from `u = z⁻¹(g - Bᴴv)`, `T v = f - z⁻¹ B g`).
* `layerResolvent_bound`: the combination for `layerMatrix σ E z X ω`, uniform in the shape
  `σ`, `W`, Hermitian `X`, real `E`, `Im z ≥ η₀ > 0`, `|z| ≤ M`:
  `‖layerResolvent σ E z X ω‖ ≤ layerResolventConstant η₀ M (1+K)⁶ / (dδ)²`.

Everything is deterministic: no dimension, probability or norm bound on `D` enters. The
probabilistic input of the Gaussian absorption lemma (the moments of `d⁻¹, δ⁻¹, K`) is not treated
here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix WithLp
open BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

section General

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- `‖A x‖ ≤ ‖A‖ ‖x‖` for the `ℓ²` operator norm, rectangular `A`. -/
theorem norm_toEuclideanLin_le (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin A x‖ ≤ ‖A‖ * ‖x‖ :=
  ((toEuclideanLin (𝕜 := ℂ) (m := m) (n := n)).trans LinearMap.toContinuousLinearMap
    A).le_opNorm x

omit [DecidableEq m] in
/-- `‖A f‖ ≤ ‖A‖ ‖f‖` in `mulVec` form, Euclidean norms. -/
theorem norm_toLp_mulVec_le (A : Matrix m n ℂ) (f : n → ℂ) :
    ‖(toLp 2 (A *ᵥ f) : EuclideanSpace ℂ m)‖ ≤ ‖A‖ * ‖(toLp 2 f : EuclideanSpace ℂ n)‖ :=
  norm_toEuclideanLin_le A (toLp 2 f)

/-- **Lower bound ⇒ inverse bound.** If `c > 0` and `c ‖x‖ ≤ ‖T x‖` for every Euclidean
vector `x`, then `T` is invertible and `‖T⁻¹‖ ≤ c⁻¹` (`ℓ²` operator norm). -/
theorem isUnit_det_and_norm_inv_le_of_lower {T : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (hT : ∀ x : EuclideanSpace ℂ n, c * ‖x‖ ≤ ‖toEuclideanLin T x‖) :
    IsUnit T.det ∧ ‖T⁻¹‖ ≤ c⁻¹ := by
  have hinj : Function.Injective T.mulVec := by
    intro f g hfg
    have h := hT (toLp 2 (f - g))
    have h0 : toEuclideanLin T (toLp 2 (f - g)) = 0 := by
      rw [toLpLin_apply]; simp [mulVec_sub, hfg]
    rw [h0, norm_zero] at h
    have hn : ‖(toLp 2 (f - g) : EuclideanSpace ℂ n)‖ = 0 := by
      have := norm_nonneg (toLp 2 (f - g) : EuclideanSpace ℂ n); nlinarith
    rw [norm_eq_zero] at hn
    have := congrArg ofLp hn
    simpa [sub_eq_zero] using this
  have hU : IsUnit T := mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit T.det := (isUnit_iff_isUnit_det T).mp hU
  refine ⟨hdet, ?_⟩
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) fun y => ?_
  change ‖toEuclideanLin T⁻¹ y‖ ≤ c⁻¹ * ‖y‖
  have hTT : toEuclideanLin T (toEuclideanLin T⁻¹ y) = y := by
    rw [toLpLin_apply, toLpLin_apply]; simp [mulVec_mulVec, mul_nonsing_inv _ hdet]
  have := hT (toEuclideanLin T⁻¹ y)
  rw [hTT] at this
  rw [le_inv_mul_iff₀ hc]
  exact this

/-- The continuous linear map of a rectangular matrix on Euclidean spaces; its operator norm is
the matrix norm by definition (`Matrix.l2_opNorm_def`). -/
abbrev eclm (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  LinearMap.toContinuousLinearMap (toEuclideanLin A)

omit [DecidableEq m] in
theorem norm_eclm (A : Matrix m n ℂ) : ‖eclm A‖ = ‖A‖ := rfl

theorem adjoint_eclm (A : Matrix m n ℂ) :
    ContinuousLinearMap.adjoint (eclm A) = eclm Aᴴ := by
  rw [eclm, eclm, toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_toContinuousLinearMap]

/-- **Matrix form of the deterministic absorber bound**. `D` Hermitian,
`Im z > 0`, `‖B‖ ≤ K`, `δ, d ∈ (0,1]`, a matrix `P` with `δ‖v - Pv‖ ≤ ‖Dv‖` and
`d‖Pv‖ ≤ ‖Bᴴ Pv‖` for all Euclidean `v`. Then for every `v`,
`(dδ)² / (C₀² (1+K)⁴) ‖v‖ ≤ ‖(D - z⁻¹ B Bᴴ) v‖`, `C₀ = absorberConstant (-z⁻¹)`. Transferred from
`absorber_lower` through `toEuclideanLin`; deterministic, dimension-free. -/
theorem absorber_matrix_lower (D : Matrix n n ℂ) (hD : D.IsHermitian) (B : Matrix n m ℂ)
    (P : Matrix n n ℂ) (z : ℂ) (hz : 0 < z.im) (d δ K : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : ‖B‖ ≤ K)
    (hPD : ∀ v : EuclideanSpace ℂ n, δ * ‖v - toEuclideanLin P v‖ ≤ ‖toEuclideanLin D v‖)
    (hPB : ∀ v : EuclideanSpace ℂ n,
      d * ‖toEuclideanLin P v‖ ≤ ‖toEuclideanLin Bᴴ (toEuclideanLin P v)‖)
    (v : EuclideanSpace ℂ n) :
    (d * δ) ^ 2 / (absorberConstant (-z⁻¹) ^ 2 * (1 + K) ^ 4) * ‖v‖ ≤
      ‖toEuclideanLin (D - z⁻¹ • (B * Bᴴ)) v‖ := by
  have hw : 0 < (-z⁻¹).im := by
    rw [im_neg_inv]; exact div_pos hz (Complex.normSq_pos.mpr fun h => by
      rw [h, Complex.zero_im] at hz; exact lt_irrefl 0 hz)
  have hDs : IsSelfAdjoint (eclm D) := by
    change ContinuousLinearMap.adjoint (eclm D) = eclm D
    rw [adjoint_eclm, hD.eq]
  have hKs : ‖eclm Bᴴ‖ ≤ K := by rw [norm_eclm, l2_opNorm_conjTranspose]; exact hK
  have h := absorber_lower (eclm D) hDs (eclm Bᴴ) (eclm P) (-z⁻¹) hw d δ K hd hd1 hδ hδ1 hKs
    hPD hPB v
  have heq : (eclm D + (-z⁻¹) • ((ContinuousLinearMap.adjoint (eclm Bᴴ)).comp (eclm Bᴴ))) v =
      toEuclideanLin (D - z⁻¹ • (B * Bᴴ)) v := by
    rw [adjoint_eclm, conjTranspose_conjTranspose]
    simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', toLpLin_apply]
    rw [sub_mulVec, smul_mulVec, ← mulVec_mulVec]
    ext i
    simp [sub_eq_add_neg]
  rw [heq] at h
  exact h

/-- **Inverse form of the deterministic absorber bound**: under the hypotheses of
`absorber_matrix_lower`, `T = D - z⁻¹ B Bᴴ` is invertible and
`‖T⁻¹‖ ≤ absorberConstant (-z⁻¹)² (1+K)⁴ / (dδ)²` (`ℓ²` operator norm). -/
theorem absorber_matrix_inv (D : Matrix n n ℂ) (hD : D.IsHermitian) (B : Matrix n m ℂ)
    (P : Matrix n n ℂ) (z : ℂ) (hz : 0 < z.im) (d δ K : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : ‖B‖ ≤ K)
    (hPD : ∀ v : EuclideanSpace ℂ n, δ * ‖v - toEuclideanLin P v‖ ≤ ‖toEuclideanLin D v‖)
    (hPB : ∀ v : EuclideanSpace ℂ n,
      d * ‖toEuclideanLin P v‖ ≤ ‖toEuclideanLin Bᴴ (toEuclideanLin P v)‖) :
    IsUnit (D - z⁻¹ • (B * Bᴴ)).det ∧
      ‖(D - z⁻¹ • (B * Bᴴ))⁻¹‖ ≤ absorberConstant (-z⁻¹) ^ 2 * (1 + K) ^ 4 / (d * δ) ^ 2 := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hK
  have hC := one_le_absorberConstant (-z⁻¹)
  have hc : 0 < (d * δ) ^ 2 / (absorberConstant (-z⁻¹) ^ 2 * (1 + K) ^ 4) := by positivity
  have := isUnit_det_and_norm_inv_le_of_lower hc
    (absorber_matrix_lower D hD B P z hz d δ K hd hd1 hδ hδ1 hK hPD hPB)
  rwa [inv_div] at this

omit [DecidableEq n] [DecidableEq m] in
/-- Euclidean norm on `n ⊕ m`: `‖y‖² = ‖y ∘ inl‖² + ‖y ∘ inr‖²`. -/
theorem norm_sq_toLp_sum (y : n ⊕ m → ℂ) :
    ‖(toLp 2 y : EuclideanSpace ℂ (n ⊕ m))‖ ^ 2 =
      ‖(toLp 2 (y ∘ Sum.inl) : EuclideanSpace ℂ n)‖ ^ 2 +
        ‖(toLp 2 (y ∘ Sum.inr) : EuclideanSpace ℂ m)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  rfl

omit [DecidableEq n] [DecidableEq m] in
theorem norm_toLp_inl_le (y : n ⊕ m → ℂ) :
    ‖(toLp 2 (y ∘ Sum.inl) : EuclideanSpace ℂ n)‖ ≤ ‖(toLp 2 y : EuclideanSpace ℂ (n ⊕ m))‖ := by
  have h := norm_sq_toLp_sum y
  have h1 := norm_nonneg (toLp 2 y : EuclideanSpace ℂ (n ⊕ m))
  have h2 := norm_nonneg (toLp 2 (y ∘ Sum.inl) : EuclideanSpace ℂ n)
  have h3 := norm_nonneg (toLp 2 (y ∘ Sum.inr) : EuclideanSpace ℂ m)
  nlinarith

omit [DecidableEq n] [DecidableEq m] in
theorem norm_toLp_inr_le (y : n ⊕ m → ℂ) :
    ‖(toLp 2 (y ∘ Sum.inr) : EuclideanSpace ℂ m)‖ ≤ ‖(toLp 2 y : EuclideanSpace ℂ (n ⊕ m))‖ := by
  have h := norm_sq_toLp_sum y
  have h1 := norm_nonneg (toLp 2 y : EuclideanSpace ℂ (n ⊕ m))
  have h2 := norm_nonneg (toLp 2 (y ∘ Sum.inl) : EuclideanSpace ℂ n)
  have h3 := norm_nonneg (toLp 2 (y ∘ Sum.inr) : EuclideanSpace ℂ m)
  nlinarith

omit [DecidableEq n] [DecidableEq m] in
theorem norm_toLp_le_add (y : n ⊕ m → ℂ) :
    ‖(toLp 2 y : EuclideanSpace ℂ (n ⊕ m))‖ ≤
      ‖(toLp 2 (y ∘ Sum.inl) : EuclideanSpace ℂ n)‖ +
        ‖(toLp 2 (y ∘ Sum.inr) : EuclideanSpace ℂ m)‖ := by
  have h := norm_sq_toLp_sum y
  have h1 := norm_nonneg (toLp 2 y : EuclideanSpace ℂ (n ⊕ m))
  have h2 := norm_nonneg (toLp 2 (y ∘ Sum.inl) : EuclideanSpace ℂ n)
  have h3 := norm_nonneg (toLp 2 (y ∘ Sum.inr) : EuclideanSpace ℂ m)
  nlinarith

/-- **Block inverse step, lower-bound form**. If `z ≠ 0` and
`T = D - z⁻¹ B Bᴴ` is invertible, then for every Euclidean `x = (v, u)`,
`‖x‖ ≤ ((1 + ‖B‖/|z|)² ‖T⁻¹‖ + |z|⁻¹) ‖𝒢⁻¹ x‖`, `𝒢⁻¹ = [[D, B], [Bᴴ, z]]`. Proof: with
`(f, g) = 𝒢⁻¹ x`, `T v = f - z⁻¹ B g` and `u = z⁻¹ (g - Bᴴ v)`. No hypothesis on `D`. -/
theorem fromBlocks_lower (D : Matrix n n ℂ) (B : Matrix n m ℂ) (z : ℂ) (hz : z ≠ 0)
    (hT : IsUnit (D - z⁻¹ • (B * Bᴴ)).det) (x : EuclideanSpace ℂ (n ⊕ m)) :
    ‖x‖ ≤ ((1 + ‖B‖ / ‖z‖) ^ 2 * ‖(D - z⁻¹ • (B * Bᴴ))⁻¹‖ + ‖z‖⁻¹) *
      ‖toEuclideanLin (fromBlocks D B Bᴴ (z • (1 : Matrix m m ℂ))) x‖ := by
  set T := D - z⁻¹ • (B * Bᴴ) with hTdef
  set y : n ⊕ m → ℂ := ofLp x with hy
  set v : n → ℂ := y ∘ Sum.inl with hv
  set u : m → ℂ := y ∘ Sum.inr with hu
  set f : n → ℂ := D *ᵥ v + B *ᵥ u with hf
  set g : m → ℂ := Bᴴ *ᵥ v + z • u with hg
  have hMx : toEuclideanLin (fromBlocks D B Bᴴ (z • (1 : Matrix m m ℂ))) x =
      toLp 2 (Sum.elim f g) := by
    rw [toLpLin_apply, fromBlocks_mulVec, smul_mulVec, one_mulVec]
  set N := ‖toEuclideanLin (fromBlocks D B Bᴴ (z • (1 : Matrix m m ℂ))) x‖ with hN
  have hfN : ‖(toLp 2 f : EuclideanSpace ℂ n)‖ ≤ N := by
    rw [hN, hMx]; exact norm_toLp_inl_le (Sum.elim f g)
  have hgN : ‖(toLp 2 g : EuclideanSpace ℂ m)‖ ≤ N := by
    rw [hN, hMx]; exact norm_toLp_inr_le (Sum.elim f g)
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  -- `T v = f - z⁻¹ B g`
  have hTv : T *ᵥ v = f - z⁻¹ • (B *ᵥ g) := by
    rw [hTdef, hf, hg, sub_mulVec, smul_mulVec, ← mulVec_mulVec, mulVec_add, mulVec_smul,
      smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul]
    abel
  have hvT : v = T⁻¹ *ᵥ (f - z⁻¹ • (B *ᵥ g)) := by
    rw [← hTv, mulVec_mulVec, nonsing_inv_mul _ hT, one_mulVec]
  have hBg : ‖(toLp 2 (B *ᵥ g) : EuclideanSpace ℂ n)‖ ≤ ‖B‖ * N :=
    (norm_toLp_mulVec_le B g).trans (mul_le_mul_of_nonneg_left hgN (norm_nonneg _))
  have hrhs : ‖(toLp 2 (f - z⁻¹ • (B *ᵥ g)) : EuclideanSpace ℂ n)‖ ≤ (1 + ‖B‖ / ‖z‖) * N := by
    rw [toLp_sub, toLp_smul]
    calc _ ≤ ‖(toLp 2 f : EuclideanSpace ℂ n)‖ + ‖z⁻¹‖ * ‖(toLp 2 (B *ᵥ g) : EuclideanSpace ℂ n)‖ :=
          (norm_sub_le _ _).trans (by rw [norm_smul])
      _ ≤ N + ‖z‖⁻¹ * (‖B‖ * N) := by
          rw [norm_inv]; gcongr
      _ = (1 + ‖B‖ / ‖z‖) * N := by field_simp
  set τ := ‖T⁻¹‖ with hτ
  set β := ‖B‖ with hβ
  have hvN : ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ≤ τ * ((1 + β / ‖z‖) * N) := by
    rw [hvT]
    exact (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left hrhs (norm_nonneg _))
  -- `u = z⁻¹ (g - Bᴴ v)`
  have huv : u = z⁻¹ • (g - Bᴴ *ᵥ v) := by
    rw [hg, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hz, one_smul]
  have huN : ‖(toLp 2 u : EuclideanSpace ℂ m)‖ ≤
      ‖z‖⁻¹ * (N + β * ‖(toLp 2 v : EuclideanSpace ℂ n)‖) := by
    rw [huv, toLp_smul, norm_smul, norm_inv, toLp_sub]
    gcongr
    refine (norm_sub_le _ _).trans (add_le_add hgN ?_)
    have := norm_toLp_mulVec_le Bᴴ v
    rwa [l2_opNorm_conjTranspose] at this
  have hx : ‖x‖ ≤ ‖(toLp 2 v : EuclideanSpace ℂ n)‖ + ‖(toLp 2 u : EuclideanSpace ℂ m)‖ :=
    norm_toLp_le_add y
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hτ0 : 0 ≤ τ := norm_nonneg _
  have hN0 : 0 ≤ N := norm_nonneg _
  have hq : 0 ≤ β / ‖z‖ := by positivity
  have hzi : 0 ≤ ‖z‖⁻¹ := by positivity
  have hv0 := norm_nonneg (toLp 2 v : EuclideanSpace ℂ n)
  calc ‖x‖ ≤ ‖(toLp 2 v : EuclideanSpace ℂ n)‖ +
        ‖z‖⁻¹ * (N + β * ‖(toLp 2 v : EuclideanSpace ℂ n)‖) := hx.trans (by linarith)
    _ = (1 + β / ‖z‖) * ‖(toLp 2 v : EuclideanSpace ℂ n)‖ + ‖z‖⁻¹ * N := by
        rw [div_eq_mul_inv]; ring
    _ ≤ (1 + β / ‖z‖) * (τ * ((1 + β / ‖z‖) * N)) + ‖z‖⁻¹ * N := by gcongr
    _ = ((1 + β / ‖z‖) ^ 2 * τ + ‖z‖⁻¹) * N := by ring

/-- **Block inverse step** ("the block inverse formula proves it for `𝒢`").
If `z ≠ 0` and `T = D - z⁻¹ B Bᴴ` is invertible, then `[[D, B], [Bᴴ, z]]` is invertible and
`‖[[D, B], [Bᴴ, z]]⁻¹‖ ≤ (1 + ‖B‖/|z|)² ‖T⁻¹‖ + |z|⁻¹` (`ℓ²` operator norms). -/
theorem fromBlocks_inv (D : Matrix n n ℂ) (B : Matrix n m ℂ) (z : ℂ) (hz : z ≠ 0)
    (hT : IsUnit (D - z⁻¹ • (B * Bᴴ)).det) :
    IsUnit (fromBlocks D B Bᴴ (z • (1 : Matrix m m ℂ))).det ∧
      ‖(fromBlocks D B Bᴴ (z • (1 : Matrix m m ℂ)))⁻¹‖ ≤
        (1 + ‖B‖ / ‖z‖) ^ 2 * ‖(D - z⁻¹ • (B * Bᴴ))⁻¹‖ + ‖z‖⁻¹ := by
  set c := (1 + ‖B‖ / ‖z‖) ^ 2 * ‖(D - z⁻¹ • (B * Bᴴ))⁻¹‖ + ‖z‖⁻¹ with hc
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hcpos : 0 < c := by positivity
  have := isUnit_det_and_norm_inv_le_of_lower (inv_pos.mpr hcpos) fun x => by
    rw [inv_mul_le_iff₀ hcpos]
    exact fromBlocks_lower D B z hz hT x
  rwa [inv_inv] at this

end General

/-!
## The layer matrix
-/

/-- The explicit constant of the layer-resolvent bound:
`(1 + η₀⁻¹)² absorberBound η₀ M² + η₀⁻¹`. Depends only on `η₀, M`. -/
def layerResolventConstant (η₀ M : ℝ) : ℝ :=
  (1 + η₀⁻¹) ^ 2 * absorberBound η₀ M ^ 2 + η₀⁻¹

/-- `blockDiag A - E - X` is Hermitian when `blockDiag A` and `X` are and `E` is real. -/
theorem layerDiag_isHermitian {W : ℕ} {σ : LayerShape} (E : ℝ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : (blockDiag ω.1).IsHermitian) :
    (blockDiag ω.1 - (E : ℂ) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X).IsHermitian := by
  refine (hA.sub ?_).sub hX
  unfold IsHermitian
  rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

/-- **Deterministic layer-resolvent bound** (the Gaussian absorption lemma, proof:
the deterministic absorber bound plus the block inverse formula). For every shape `σ`, every `W`,
every Hermitian `X`, real `E`, `z` with `Im z ≥ η₀ > 0` and `|z| ≤ M`, and every sample `ω`
with `blockDiag ω.1` Hermitian (true for GUE samples) for which, with
`D = blockDiag ω.1 - E - X`, `B = bondMatrix σ ω.2` and a matrix `P`, the absorber hypotheses
`δ‖v - Pv‖ ≤ ‖Dv‖`, `d‖Pv‖ ≤ ‖Bᴴ Pv‖` (all Euclidean `v`), `d, δ ∈ (0,1]`, `‖B‖ ≤ K` hold:
the layer matrix is invertible and
`‖layerResolvent σ E z X ω‖ ≤ layerResolventConstant η₀ M (1+K)⁶ / (dδ)²`
(`ℓ²` operator norm). The constant depends only on `η₀, M`; deterministic, uniform in
`σ, W, X, E, ω`. -/
theorem layerResolvent_bound {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : (blockDiag ω.1).IsHermitian) {η₀ M : ℝ} (hη : 0 < η₀) (hz : η₀ ≤ z.im)
    (hM : ‖z‖ ≤ M) (P : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (d δ K : ℝ) (hd : 0 < d)
    (hd1 : d ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : ‖bondMatrix σ ω.2‖ ≤ K)
    (hPD : ∀ v : EuclideanSpace ℂ (PhysSite W σ), δ * ‖v - toEuclideanLin P v‖ ≤
      ‖toEuclideanLin (blockDiag ω.1 - (E : ℂ) • 1 - X) v‖)
    (hPB : ∀ v : EuclideanSpace ℂ (PhysSite W σ), d * ‖toEuclideanLin P v‖ ≤
      ‖toEuclideanLin (bondMatrix σ ω.2)ᴴ (toEuclideanLin P v)‖) :
    IsUnit (layerMatrix σ E z X ω).det ∧
      ‖layerResolvent σ E z X ω‖ ≤ layerResolventConstant η₀ M * (1 + K) ^ 6 / (d * δ) ^ 2 := by
  set D := blockDiag ω.1 - (E : ℂ) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X with hD
  set B := bondMatrix σ ω.2 with hB
  have hzpos : 0 < z.im := lt_of_lt_of_le hη hz
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hzpos; exact lt_irrefl 0 hzpos
  have hzn : η₀ ≤ ‖z‖ := hz.trans (Complex.im_le_norm z)
  obtain ⟨hTu, hTn⟩ := absorber_matrix_inv D (layerDiag_isHermitian E X hX ω hA) B P z hzpos
    d δ K hd hd1 hδ hδ1 hK hPD hPB
  obtain ⟨hGu, hGn⟩ := fromBlocks_inv D B z hz0 hTu
  refine ⟨hGu, ?_⟩
  change ‖(fromBlocks D B Bᴴ (z • (1 : Matrix _ _ ℂ)))⁻¹‖ ≤ _
  refine hGn.trans ?_
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hK
  have hdδ : 0 < d * δ := mul_pos hd hδ
  have hdδ1 : (d * δ) ^ 2 ≤ 1 := by
    have : d * δ ≤ 1 := by nlinarith
    nlinarith
  have hC1 := one_le_absorberConstant (-z⁻¹)
  have hCb := absorberConstant_le hη hz hM
  have hC2 : absorberConstant (-z⁻¹) ^ 2 ≤ absorberBound η₀ M ^ 2 :=
    pow_le_pow_left₀ (by linarith) hCb 2
  have hηi : 0 < η₀⁻¹ := inv_pos.mpr hη
  -- `1 + ‖B‖/|z| ≤ (1 + η₀⁻¹)(1 + K)`
  have hq : 1 + ‖B‖ / ‖z‖ ≤ (1 + η₀⁻¹) * (1 + K) := by
    have : ‖B‖ / ‖z‖ ≤ η₀⁻¹ * K := by
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul (inv_anti₀ hη hzn) hK (norm_nonneg _) hηi.le
    nlinarith
  have hq0 : 0 ≤ 1 + ‖B‖ / ‖z‖ := by positivity
  have hq2 : (1 + ‖B‖ / ‖z‖) ^ 2 ≤ (1 + η₀⁻¹) ^ 2 * (1 + K) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hq0 hq 2
  have hzi : ‖z‖⁻¹ ≤ η₀⁻¹ := inv_anti₀ hη hzn
  set τ := ‖(D - z⁻¹ • (B * Bᴴ))⁻¹‖ with hτ
  have hτ0 : 0 ≤ τ := norm_nonneg _
  have hpos : 0 < (d * δ) ^ 2 := by positivity
  have hK1 : 1 ≤ 1 + K := by linarith
  -- the two pieces
  have e1 : (1 + ‖B‖ / ‖z‖) ^ 2 * τ ≤
      (1 + η₀⁻¹) ^ 2 * absorberBound η₀ M ^ 2 * (1 + K) ^ 6 / (d * δ) ^ 2 := by
    calc (1 + ‖B‖ / ‖z‖) ^ 2 * τ
        ≤ ((1 + η₀⁻¹) ^ 2 * (1 + K) ^ 2) *
            (absorberConstant (-z⁻¹) ^ 2 * (1 + K) ^ 4 / (d * δ) ^ 2) :=
          mul_le_mul hq2 hTn hτ0 (by positivity)
      _ ≤ ((1 + η₀⁻¹) ^ 2 * (1 + K) ^ 2) *
            (absorberBound η₀ M ^ 2 * (1 + K) ^ 4 / (d * δ) ^ 2) := by gcongr
      _ = (1 + η₀⁻¹) ^ 2 * absorberBound η₀ M ^ 2 * (1 + K) ^ 6 / (d * δ) ^ 2 := by ring
  have e2 : ‖z‖⁻¹ ≤ η₀⁻¹ * (1 + K) ^ 6 / (d * δ) ^ 2 := by
    rw [le_div_iff₀ hpos]
    have h6 : 1 ≤ (1 + K) ^ 6 := one_le_pow₀ hK1
    calc ‖z‖⁻¹ * (d * δ) ^ 2 ≤ η₀⁻¹ * 1 :=
          mul_le_mul hzi hdδ1 (by positivity) hηi.le
      _ ≤ η₀⁻¹ * (1 + K) ^ 6 := mul_le_mul_of_nonneg_left h6 hηi.le
  calc (1 + ‖B‖ / ‖z‖) ^ 2 * τ + ‖z‖⁻¹
      ≤ (1 + η₀⁻¹) ^ 2 * absorberBound η₀ M ^ 2 * (1 + K) ^ 6 / (d * δ) ^ 2 +
          η₀⁻¹ * (1 + K) ^ 6 / (d * δ) ^ 2 := add_le_add e1 e2
    _ = layerResolventConstant η₀ M * (1 + K) ^ 6 / (d * δ) ^ 2 := by
        unfold layerResolventConstant; ring

end BlockBand.Layers
