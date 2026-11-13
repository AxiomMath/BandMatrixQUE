module

public import BlockBand.LocalWindow.ProofCertificate
public import BlockBand.LocalWindow.ProofTruncationBounds
public import BlockBand.LocalWindow.ProofCrowding

/-!
# Transfer of the pole certificate to `F̂`

Deterministic transfer of the pole certificate from the exact residual `F` to the truncated
residual `F̂`, for the physical local-window lemma.

## Main results

* `im_mul_norm_le`, `det_sub_smul_ne_zero`, `norm_resolvent_le`: for Hermitian `K` and
  `Im z ≠ 0`, `‖(K - z)v‖ ≥ |Im z| ‖v‖`, `K - z` is invertible and `‖(K - z)⁻¹‖ ≤ 1/|Im z|`
  (pointwise Euclidean form).
* `norm_weightedTrace_resolvent_sub_le`: if `K - K'` has rank one (`vecMulVec a b`), then for
  every diagonal weight `|d_x| ≤ 1`, `|Σ_x d_x ((K - z)⁻¹ - (K' - z)⁻¹)_{xx}| ≤ 2/|Im z|`
  (the trace norm is at most twice the inverse height, in the form needed for `W⁻¹ Tr P_k`).
* `physicalCoareaF_sub_truncF_rankOne`: at a nonpole energy with at most one exterior
  eigenvalue within `ε` of `E`, `F(E) - F̂(E)` has rank one.
* `certErrHat_le`: the certificate error of `F̂` exceeds that of `F` by at most
  `2/(W s |Im a|)` (deterministic).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCertificate

open MeasureTheory ProbabilityTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.LocalWindow.ProofCount BlockBand.Coarea
open BlockBand.DeterminantScore.MinorTailInverse
open scoped ENNReal InnerProductSpace ComplexConjugate

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

/-!
## Resolvent bounds for Hermitian matrices
-/

section Resolvent

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `|Im z| ‖v‖ ≤ ‖(K - z) v‖` for Hermitian `K`. -/
theorem im_mul_norm_le {K : Matrix ι ι ℂ} (hK : K.IsHermitian) (z : ℂ)
    (v : EuclideanSpace ℂ ι) : |z.im| * ‖v‖ ≤ ‖T (K - z • 1) v‖ := by
  have hsym : (T K).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hK
  set w := T (K - z • 1) v
  have hw : w = T K v - z • v := by
    simp only [w, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
    rw [toE_apply (1 : Matrix ι ι ℂ), Matrix.one_mulVec, WithLp.toLp_ofLp]
  have hre : ((RCLike.re ⟪T K v, v⟫_ℂ : ℝ) : ℂ) = ⟪T K v, v⟫_ℂ := hsym.coe_re_inner_apply_self v
  have hinner : ⟪w, v⟫_ℂ = ⟪T K v, v⟫_ℂ - conj z * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hw, inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  have him : (⟪w, v⟫_ℂ).im = z.im * ‖v‖ ^ 2 := by
    rw [hinner, ← hre]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re]
    ring
  have h1 : |z.im| * ‖v‖ ^ 2 ≤ ‖w‖ * ‖v‖ := by
    calc |z.im| * ‖v‖ ^ 2 = |(⟪w, v⟫_ℂ).im| := by
          rw [him, abs_mul, abs_of_nonneg (sq_nonneg ‖v‖)]
      _ ≤ ‖⟪w, v⟫_ℂ‖ := Complex.abs_im_le_norm _
      _ ≤ ‖w‖ * ‖v‖ := norm_inner_le_norm w v
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have : |z.im| * ‖v‖ * ‖v‖ ≤ ‖w‖ * ‖v‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- `K - z` is invertible for Hermitian `K` and nonreal `z`. -/
theorem det_sub_smul_ne_zero {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (K - z • (1 : Matrix ι ι ℂ)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h := im_mul_norm_le hK z (WithLp.toLp 2 v)
  rw [toE_apply, WithLp.ofLp_toLp, hzero, WithLp.toLp_zero, norm_zero] at h
  have hn : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ = 0 := by
    have := abs_pos.mpr hz
    nlinarith [norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ ι)]
  apply hv
  have := norm_eq_zero.mp hn
  exact (WithLp.toLp_eq_zero 2).mp this

/-- `‖(K - z)⁻¹ x‖ ≤ |Im z|⁻¹ ‖x‖` for Hermitian `K` and nonreal `z`. -/
theorem norm_resolvent_le {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (x : EuclideanSpace ℂ ι) : ‖T (K - z • (1 : Matrix ι ι ℂ))⁻¹ x‖ ≤ |z.im|⁻¹ * ‖x‖ := by
  have hu : IsUnit (K - z • (1 : Matrix ι ι ℂ)).det := isUnit_iff_ne_zero.mpr
    (det_sub_smul_ne_zero hK hz)
  have hmul : (K - z • (1 : Matrix ι ι ℂ)) * (K - z • (1 : Matrix ι ι ℂ))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hu
  have h := im_mul_norm_le hK z (T (K - z • (1 : Matrix ι ι ℂ))⁻¹ x)
  rw [toE_toE, hmul, toE_apply (1 : Matrix ι ι ℂ), Matrix.one_mulVec, WithLp.toLp_ofLp] at h
  have hz' : 0 < |z.im| := abs_pos.mpr hz
  rw [inv_mul_eq_div, le_div_iff₀ hz', mul_comm]
  exact h

end Resolvent

/-!
## Rank-one differences
-/

section RankOne

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `M (a bᵀ) N = (M a)(bᵀ N)`. -/
theorem mul_vecMulVec_mul {l m n k : Type} [Fintype m] [Fintype n] (M : Matrix l m ℂ)
    (a : m → ℂ) (b : n → ℂ) (N : Matrix n k ℂ) :
    M * vecMulVec a b * N = vecMulVec (M *ᵥ a) (b ᵥ* N) := by
  rw [mul_vecMulVec, vecMulVec_mul]

/-- **Weighted trace of a rank-one matrix**: if `‖(a bᵀ) v‖ ≤ B ‖v‖` for every `v`, then
`|Σ_x d_x (a bᵀ)_{xx}| ≤ B` for every weight `|d_x| ≤ 1`. -/
theorem norm_weightedTrace_vecMulVec_le (a b d : ι → ℂ) (hd : ∀ x, ‖d x‖ ≤ 1) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ v, ‖T (vecMulVec a b) v‖ ≤ B * ‖v‖) :
    ‖∑ x, d x * vecMulVec a b x x‖ ≤ B := by
  set na := ‖(WithLp.toLp 2 a : EuclideanSpace ℂ ι)‖
  set nb := ‖(WithLp.toLp 2 b : EuclideanSpace ℂ ι)‖
  -- the trace is an inner product
  set u : EuclideanSpace ℂ ι := WithLp.toLp 2 (star (fun x => d x * b x))
  have hsum : ∑ x, d x * vecMulVec a b x x = ⟪u, (WithLp.toLp 2 a : EuclideanSpace ℂ ι)⟫_ℂ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [u, star_star, dotProduct, vecMulVec_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hu : ‖u‖ ≤ nb := by
    simp only [u, nb, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun x _ => ?_
    simp only [Pi.star_apply, norm_star, norm_mul]
    apply pow_le_pow_left₀ (by positivity)
    calc ‖d x‖ * ‖b x‖ ≤ 1 * ‖b x‖ := mul_le_mul_of_nonneg_right (hd x) (norm_nonneg _)
      _ = ‖b x‖ := one_mul _
  have h1 : ‖∑ x, d x * vecMulVec a b x x‖ ≤ na * nb := by
    rw [hsum]
    calc ‖⟪u, (WithLp.toLp 2 a : EuclideanSpace ℂ ι)⟫_ℂ‖ ≤ ‖u‖ * na := norm_inner_le_norm _ _
      _ ≤ nb * na := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
      _ = na * nb := mul_comm _ _
  -- the operator bound at `v = conj b`
  have h2 : na * nb ^ 2 ≤ B * nb := by
    have h := hB (WithLp.toLp 2 (star b))
    have hv : T (vecMulVec a b) (WithLp.toLp 2 (star b)) =
        ((nb ^ 2 : ℝ) : ℂ) • (WithLp.toLp 2 a : EuclideanSpace ℂ ι) := by
      rw [toE_apply, WithLp.ofLp_toLp, vecMulVec_mulVec]
      have hbb : b ⬝ᵥ star b = ((nb ^ 2 : ℝ) : ℂ) := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 b : EuclideanSpace ℂ ι)
        rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp] at this
        rw [this]; push_cast; rfl
      rw [hbb]
      ext x
      simp [mul_comm]
    have hnb : ‖(WithLp.toLp 2 (star b) : EuclideanSpace ℂ ι)‖ = nb := by
      simp only [nb, EuclideanSpace.norm_eq, Pi.star_apply, norm_star]
    rw [hv, norm_smul, hnb, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)] at h
    linarith
  rcases (norm_nonneg (WithLp.toLp 2 b : EuclideanSpace ℂ ι)).eq_or_lt with h0 | hpos
  · have : nb = 0 := h0.symm
    rw [this, mul_zero] at h1; exact h1.trans hB0
  · have : na * nb * nb ≤ B * nb := by nlinarith
    exact h1.trans (le_of_mul_le_mul_right this hpos)

/-- **Rank one at fixed height**: if `K, K'` are Hermitian and
`K - K' = a bᵀ`, then for `Im z ≠ 0` and every weight `|d_x| ≤ 1`,
`|Σ_x d_x ((K - z)⁻¹ - (K' - z)⁻¹)_{xx}| ≤ 2/|Im z|`. -/
theorem norm_weightedTrace_resolvent_sub_le {K K' : Matrix ι ι ℂ} (hK : K.IsHermitian)
    (hK' : K'.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (a b : ι → ℂ) (hD : K - K' = vecMulVec a b)
    (d : ι → ℂ) (hd : ∀ x, ‖d x‖ ≤ 1) :
    ‖∑ x, d x * ((K - z • (1 : Matrix ι ι ℂ))⁻¹ - (K' - z • (1 : Matrix ι ι ℂ))⁻¹) x x‖ ≤
      2 * |z.im|⁻¹ := by
  set R := (K - z • (1 : Matrix ι ι ℂ))⁻¹
  set R' := (K' - z • (1 : Matrix ι ι ℂ))⁻¹
  have hu : IsUnit (K - z • (1 : Matrix ι ι ℂ)).det :=
    isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hK hz)
  have hu' : IsUnit (K' - z • (1 : Matrix ι ι ℂ)).det :=
    isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hK' hz)
  have hdiff : R - R' = vecMulVec (-(R *ᵥ a)) (b ᵥ* R') := by
    have e1 : R * (K' - z • (1 : Matrix ι ι ℂ)) * R' = R := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
    have e2 : R * (K - z • (1 : Matrix ι ι ℂ)) * R' = R' := by
      rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    have : R - R' = -(R * (K - K') * R') := by
      calc R - R' = R * (K' - z • (1 : Matrix ι ι ℂ)) * R' - R * (K - z • (1 : Matrix ι ι ℂ)) * R' := by
            rw [e1, e2]
        _ = -(R * (K - K') * R') := by
            simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [this, hD, mul_vecMulVec_mul, neg_vecMulVec]
  have hbound : ∀ v, ‖T (R - R') v‖ ≤ 2 * |z.im|⁻¹ * ‖v‖ := by
    intro v
    rw [map_sub, LinearMap.sub_apply]
    calc ‖T R v - T R' v‖ ≤ ‖T R v‖ + ‖T R' v‖ := norm_sub_le _ _
      _ ≤ |z.im|⁻¹ * ‖v‖ + |z.im|⁻¹ * ‖v‖ :=
          add_le_add (norm_resolvent_le hK hz v) (norm_resolvent_le hK' hz v)
      _ = 2 * |z.im|⁻¹ * ‖v‖ := by ring
  rw [hdiff] at hbound ⊢
  exact norm_weightedTrace_vecMulVec_le _ _ d hd (by positivity) hbound

end RankOne

/-!
## `F(E) - F̂(E)` has rank one off the crowding event
-/

section Truncation

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A diagonal matrix supported on a set of at most one index has rank one. -/
theorem diagonal_eq_vecMulVec (h : α → ℂ) (s : Finset α) (hs : s.card ≤ 1)
    (hsupp : ∀ j, j ∉ s → h j = 0) : ∃ u w : α → ℂ, diagonal h = vecMulVec u w := by
  rcases s.eq_empty_or_nonempty with he | ⟨j, hj⟩
  · refine ⟨0, 0, ?_⟩
    have : h = 0 := funext fun k => hsupp k (by simp [he])
    rw [this, zero_vecMulVec]; exact diagonal_zero
  · refine ⟨Pi.single j (h j), Pi.single j 1, ?_⟩
    have hk : ∀ k, k ≠ j → h k = 0 := fun k hkj =>
      hsupp k fun hks => hkj (Finset.card_le_one.mp hs k hks j hj)
    ext k l
    simp only [diagonal_apply, vecMulVec_apply, Pi.single_apply]
    by_cases hkl : k = l
    · subst hkl
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [hkj, hk k hkj]
    · by_cases hkj : k = j
      · subst hkj
        simp [hkl, Ne.symm hkl]
      · simp [hkl, hkj]

/-- **Rank one**: at a nonpole energy with at most one exterior eigenvalue
within `ε` of `E`, `F(E) - F̂(E) = a bᵀ` for some vectors `a, b`. -/
theorem physicalCoareaF_sub_truncF_rankOne {H_R : Matrix α α ℂ} (hH : H_R.IsHermitian)
    (C : Matrix α β ℂ) (V : Matrix β β ℂ) {ε E : ℝ}
    (hdet : (H_R - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0) (hnear : (nearSet ε hH E).card ≤ 1) :
    ∃ a b : β → ℂ, physicalCoareaF H_R C V E - truncF ε H_R C V E = vecMulVec a b := by
  set U := hH.eigenvectorUnitary
  set h : α → ℂ := fun j => if |hH.eigenvalues j - E| ≤ ε then
    ((((hH.eigenvalues j - E)⁻¹ - truncInv ε (hH.eigenvalues j - E)) : ℝ) : ℂ) else 0
  have hdiff : physicalCoareaF H_R C V E - truncF ε H_R C V E =
      -(Cᴴ * ((U : Matrix α α ℂ) * diagonal h * star (U : Matrix α α ℂ)) * C) := by
    unfold physicalCoareaF truncF
    rw [← resolvent_sub_trunc hH ε hdet, Matrix.mul_sub, Matrix.sub_mul]
    abel
  obtain ⟨u, w, huw⟩ := diagonal_eq_vecMulVec h (nearSet ε hH E) hnear fun j hj => by
    have : ¬ |hH.eigenvalues j - E| ≤ ε := by simpa [nearSet] using hj
    simp [h, this]
  refine ⟨-(Cᴴ *ᵥ ((U : Matrix α α ℂ) *ᵥ u)), (w ᵥ* star (U : Matrix α α ℂ)) ᵥ* C, ?_⟩
  rw [hdiff, huw, mul_vecMulVec_mul, mul_vecMulVec_mul, neg_vecMulVec]

/-- `F(E)` is Hermitian for Hermitian `H_R`, `V` (Lean's totalized inverse at a pole). -/
theorem isHermitian_physicalCoareaF {H_R : Matrix α α ℂ} (hH : H_R.IsHermitian)
    (C : Matrix α β ℂ) {V : Matrix β β ℂ} (hV : V.IsHermitian) (E : ℝ) :
    (physicalCoareaF H_R C V E).IsHermitian := by
  unfold physicalCoareaF physicalCoareaResolvent
  have h1 : (H_R - (E : ℂ) • (1 : Matrix α α ℂ)).IsHermitian :=
    hH.sub (by
      rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal])
  exact hV.sub (isHermitian_conjTranspose_mul_mul C h1.inv)

/-- `g_ε(H - E)` is Hermitian. -/
theorem isHermitian_truncResolvent (ε : ℝ) (H : Matrix α α ℂ) (E : ℝ) :
    (truncResolvent ε H E).IsHermitian := by
  unfold truncResolvent
  split_ifs with hH
  · rw [star_eq_conjTranspose]
    refine isHermitian_mul_mul_conjTranspose _ ?_
    refine isHermitian_diagonal_of_self_adjoint _ ?_
    ext j
    simp
  · exact isHermitian_zero

/-- `F̂(E)` is Hermitian for Hermitian `V`. -/
theorem isHermitian_truncF (ε : ℝ) (H_R : Matrix α α ℂ) (C : Matrix α β ℂ) {V : Matrix β β ℂ}
    (hV : V.IsHermitian) (E : ℝ) : (truncF ε H_R C V E).IsHermitian := by
  unfold truncF
  exact hV.sub (isHermitian_conjTranspose_mul_mul C (isHermitian_truncResolvent ε H_R E))

end Truncation

/-!
## The certificate of the truncated residual
-/

section CertHat

variable {p : Parameters} {i : ZMod p.n}

/-- The certificate error `max_{k = i, i+1} |W⁻¹ Tr P_k (K̂(E) - s a)⁻¹ - a|` of the truncated
residual `K̂(E) = F̂(E) - E`, `s = splitS p`, `a = matchedA E`. -/
def certErrHat (ε : ℝ) (p : Parameters) (i : ZMod p.n) (om : SplitState p i) (E : ℝ) : ℝ :=
  max ‖pairBlockTrace p i ((truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1 -
        ((splitS p : ℂ) * matchedA E) • 1)⁻¹) i - matchedA E‖
    ‖pairBlockTrace p i ((truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1 -
        ((splitS p : ℂ) * matchedA E) • 1)⁻¹) (i + 1) - matchedA E‖

/-- Block traces of the resolvents of two Hermitian pair matrices differing by rank one differ
by at most `2/(W |Im z|)`. -/
theorem norm_pairBlockTrace_sub_le {K K' : PairMatrix p i} (hK : K.IsHermitian)
    (hK' : K'.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (a b : PairSite p i → ℂ)
    (hD : K - K' = vecMulVec a b) (k : ZMod p.n) :
    ‖pairBlockTrace p i (K - z • (1 : PairMatrix p i))⁻¹ k -
        pairBlockTrace p i (K' - z • (1 : PairMatrix p i))⁻¹ k‖ ≤
      2 / ((p.W : ℝ) * |z.im|) := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  set d : PairSite p i → ℂ := fun x => if x.1.1 = k then 1 else 0
  have hd : ∀ x, ‖d x‖ ≤ 1 := fun x => by
    simp only [d]; split_ifs <;> simp
  have he : pairBlockTrace p i (K - z • (1 : PairMatrix p i))⁻¹ k -
      pairBlockTrace p i (K' - z • (1 : PairMatrix p i))⁻¹ k =
      (p.W : ℂ)⁻¹ * ∑ x, d x * ((K - z • (1 : PairMatrix p i))⁻¹ -
        (K' - z • (1 : PairMatrix p i))⁻¹) x x := by
    unfold pairBlockTrace
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [d, Matrix.sub_apply]
    split_ifs <;> ring
  rw [he, norm_mul, norm_inv, Complex.norm_natCast]
  have h := norm_weightedTrace_resolvent_sub_le hK hK' hz a b hD d hd
  calc (p.W : ℝ)⁻¹ * ‖∑ x, d x * ((K - z • (1 : PairMatrix p i))⁻¹ -
        (K' - z • (1 : PairMatrix p i))⁻¹) x x‖ ≤ (p.W : ℝ)⁻¹ * (2 * |z.im|⁻¹) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 / ((p.W : ℝ) * |z.im|) := by field_simp

/-- `(matchedA E).im = -√(4 - E²)/2`. -/
theorem matchedA_im (E : ℝ) : (matchedA E).im = -Real.sqrt (4 - E ^ 2) / 2 := rfl

/-- On `bulkInterval κ`, `|Im a(E)| ≥ √κ / 2`. -/
theorem sqrt_le_abs_matchedA_im {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    Real.sqrt κ / 2 ≤ |(matchedA E).im| := by
  obtain ⟨h1, h2⟩ := hE
  have hk2 : κ ≤ 2 := by linarith
  have h4 : κ ≤ 4 - E ^ 2 := by nlinarith
  rw [matchedA_im, abs_div, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _), abs_two]
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt h4) (by norm_num)

/-- **Transfer `F → F̂`**: at a nonpole energy `E` with at most one exterior
eigenvalue within `ε` of `E`, for Hermitian `H_R`, `V` and `Im a(E) ≠ 0`, `s = splitS p > 0`,
`certErrHat ≤ certErr + 2/(W s |Im a|)`. -/
theorem certErrHat_le {ε : ℝ} (om : SplitState p i) (hH : om.1.IsHermitian)
    (hV : om.2.2.IsHermitian) {E : ℝ} (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    (hnear : (nearSet ε hH E).card ≤ 1) (him : (matchedA E).im ≠ 0) (hs : 0 < splitS p) :
    certErrHat ε p i om E ≤
      certErr p i om E + 2 / ((p.W : ℝ) * (splitS p * |(matchedA E).im|)) := by
  obtain ⟨a, b, hab⟩ := physicalCoareaF_sub_truncF_rankOne hH om.2.1 om.2.2 hdet hnear
  have hEh : ((E : ℂ) • (1 : PairMatrix p i)).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hK : (pairResidual p i om E).IsHermitian :=
    (isHermitian_physicalCoareaF hH om.2.1 hV E).sub hEh
  have hK' : (truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1).IsHermitian :=
    (isHermitian_truncF ε om.1 om.2.1 hV E).sub hEh
  set z : ℂ := (splitS p : ℂ) * matchedA E
  have hzim : z.im = splitS p * (matchedA E).im := by
    simp [z, Complex.mul_im]
  have hz : z.im ≠ 0 := by rw [hzim]; exact mul_ne_zero hs.ne' him
  have hzabs : |z.im| = splitS p * |(matchedA E).im| := by
    rw [hzim, abs_mul, abs_of_pos hs]
  have hD : truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1 - pairResidual p i om E =
      vecMulVec (-a) b := by
    rw [neg_vecMulVec, ← hab]
    unfold pairResidual
    abel
  have hk : ∀ k : ZMod p.n,
      ‖pairBlockTrace p i ((truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1 - z • 1)⁻¹) k -
          matchedA E‖ ≤
        ‖pairBlockTrace p i ((pairResidual p i om E - z • 1)⁻¹) k - matchedA E‖ +
          2 / ((p.W : ℝ) * (splitS p * |(matchedA E).im|)) := by
    intro k
    have h := norm_pairBlockTrace_sub_le hK' hK hz (-a) b hD k
    rw [hzabs] at h
    calc _ = ‖(pairBlockTrace p i ((pairResidual p i om E - z • 1)⁻¹) k - matchedA E) +
            (pairBlockTrace p i ((truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1 - z • 1)⁻¹) k -
              pairBlockTrace p i ((pairResidual p i om E - z • 1)⁻¹) k)‖ := by
            congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right h _)
  unfold certErrHat certErr
  refine max_le ((hk i).trans ?_) ((hk (i + 1)).trans ?_)
  · exact add_le_add_left (le_max_left _ _) _
  · exact add_le_add_left (le_max_right _ _) _

end CertHat

/-!
## Fixed energies are almost surely not poles
-/

section Pole

variable {α : Type} [Fintype α] [DecidableEq α]

/-- `det(H - E) = 0` forces an eigenvalue equal to `E`. -/
theorem exists_eigenvalue_eq_of_det {H : Matrix α α ℂ} (hH : H.IsHermitian) {E : ℝ}
    (hdet : (H - (E : ℂ) • (1 : Matrix α α ℂ)).det = 0) : ∃ j, hH.eigenvalues j = E := by
  rw [sub_eq_conj hH E, Matrix.det_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul, det_diagonal] at hdet
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hdet
  exact ⟨j, by
    have : hH.eigenvalues j - E = 0 := by exact_mod_cast hj
    linarith⟩

variable {p : Parameters} {i : ZMod p.n}

/-- **Pole null set**: from
`PhysicalBlockConditionalCount` at `r = 1` on the degenerate interval `[e, e]`, under the
split law the exterior block has `e` as an eigenvalue with probability zero.
-/
theorem splitLaw_pole_null (hPBC : PhysicalBlockConditionalCount) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hsplit : IsPairSplitting p i model (splitS p) Pω) (e : ℝ) :
    splitLaw p i Pω {x | (x.1.1 - (e : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det = 0} = 0 := by
  obtain ⟨C, hC, hcount⟩ := hPBC
  set μ : Measure p.SiteMatrix := (model.law : Measure p.SiteMatrix) with hμ
  set R := ProofCrowding.exteriorBlocks p i
  set cnt := subsystemCount p R (ProofCrowding.zeroDeformation p i) (Set.Icc e e)
  have hf : Measurable (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) :=
    BlockBand.Angular.PairCoareaBridge.measurable_assemble p i
  have hmap : (splitLaw p i Pω).map (fun x => assemble p i x.1 x.2) = μ := hsplit
  obtain ⟨hint, hle⟩ := hcount p model R (ProofCrowding.zeroDeformation p i) measurable_const e e
    le_rfl 1 le_rfl
  set g := BlockBand.External.PSSS.factorialCount cnt 1
  set S : Set p.SiteMatrix := {H | (1 : ℝ) ≤ g H}
  set T' : Set p.SiteMatrix := {H | ¬ H.IsHermitian}
  have hT : μ T' = 0 := by
    have := model.isPhysical.1
    rw [ae_iff] at this
    exact this
  have hsub : {x : SplitState p i × PairMatrix p i |
      (x.1.1 - (e : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det = 0} ⊆
      (fun x => assemble p i x.1 x.2) ⁻¹' S ∪ (fun x => assemble p i x.1 x.2) ⁻¹' T' := by
    intro x hx
    by_cases hH : (assemble p i x.1 x.2).IsHermitian
    · left
      have hc := ProofCrowding.subsystemCount_eq p i _ hH e e
      rw [ProofCrowding.exteriorBlock_assemble] at hc
      have hHR : x.1.1.IsHermitian := by
        have := hH.submatrix (Subtype.val : ExteriorSite p i → p.Site)
        rwa [← ProofCrowding.exteriorBlock_assemble p i x.1 x.2]
      obtain ⟨j, hj⟩ := exists_eigenvalue_eq_of_det hHR hx
      have h1 : (1 : ℝ) ≤ spectralSum x.1.1 (ProofCrowding.iccInd e e) := by
        rw [spectralSum_eq_sum hHR]
        calc (1 : ℝ) = ProofCrowding.iccInd e e (hHR.eigenvalues j) := by
              simp [ProofCrowding.iccInd, hj]
          _ ≤ ∑ k, ProofCrowding.iccInd e e (hHR.eigenvalues k) :=
              Finset.single_le_sum (f := fun k => ProofCrowding.iccInd e e (hHR.eigenvalues k))
                (fun k _ => by unfold ProofCrowding.iccInd; split_ifs <;> norm_num)
                (Finset.mem_univ j)
      show (1 : ℝ) ≤ (Nat.descFactorial (cnt (assemble p i x.1 x.2)) 1 : ℝ)
      rw [Nat.descFactorial_one]
      rw [hc]; exact h1
    · right
      exact hH
  have hS : μ S = 0 := by
    have hg0 : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall fun H => by
      simp only [g, BlockBand.External.PSSS.factorialCount, Pi.zero_apply]; positivity
    have hM := mul_meas_ge_le_integral_of_nonneg hg0 hint 1
    have hreal : μ.real S ≤ 0 := by
      have := hM.trans hle
      simpa using this
    have h0 : μ.real S = 0 := le_antisymm hreal measureReal_nonneg
    exact (measureReal_eq_zero_iff (measure_ne_top μ S)).mp h0
  refine le_antisymm ?_ (zero_le)
  calc splitLaw p i Pω _
      ≤ splitLaw p i Pω ((fun x => assemble p i x.1 x.2) ⁻¹' S) +
          splitLaw p i Pω ((fun x => assemble p i x.1 x.2) ⁻¹' T') :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ μ S + μ T' := by
        gcongr
        · rw [← hmap]; exact Measure.le_map_apply hf.aemeasurable S
        · rw [← hmap]; exact Measure.le_map_apply hf.aemeasurable T'
    _ = 0 := by rw [hS, hT, add_zero]

end Pole

end BlockBand.LocalWindow.ProofCertificate
