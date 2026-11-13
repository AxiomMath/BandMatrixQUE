module

public import BlockBand.Coarea.ClockRank

/-!
# Rank identification on the fresh eigenpair fiber (empty exterior)

Pointwise, exact, finite-dimensional statements; no measure occurs.

* `fresh_rank`: for a unit `v`, an orthonormal frame `U` of `v^⊥`, Hermitian `X` with
  `det(X - E) ≠ 0` and `N_-(X - E) = ℓ`, the matrix `K = E vv* + U X U*` has `λ_ℓ(K) = E`
  (zero-based increasing rank) and selected eigenprojector `u_ℓ u_ℓ* = vv*`.
* `fresh_rank_shift`: the same for `K - c I`, `c ∈ ℝ`, with `λ_ℓ(K - c) = E - c` and the same
  eigenprojector (`K - c = (E - c) vv* + U (X - c) U*`).
* `freshReconstructed_rank`: on the support of the fresh fiber density, i.e. `det M ≠ 0` and
  `N_-(M) = ℓ`, with `G_rec = freshReconstructed U F E v G'`, `G'` Hermitian:
  `λ_ℓ(F + G_rec - cI) = E - c` and the eigenprojector of `F + G_rec - cI` is `vv*`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FreshPalm

open Matrix BlockBand.Model.Construction BlockBand.Foundations.Spectral
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea BlockBand.Coarea.ClockRank
open CoareaNative.BlockBand (negativeEigenvalueCount)
open scoped ComplexConjugate

variable {N : ℕ}

theorem vecMulVec_self_isHermitian (v : Fin N → ℂ) : (vecMulVec v (star v)).IsHermitian := by
  ext a b
  simp [vecMulVec_apply, mul_comm]

/-- **Fresh rank identification.** -/
theorem fresh_rank (hN : 0 < N) (U : Matrix (Fin N) (Fin (N - 1)) ℂ) (v : Fin N → ℂ)
    (hUU : Uᴴ * U = 1) (hUv : Uᴴ *ᵥ v = 0) (hv : l2Norm v = 1)
    (X : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ) (hX : X.IsHermitian) (E : ℝ)
    (hdet : (X - (E : ℂ) • 1).det ≠ 0) (ℓ : Fin N)
    (hcnt : negativeCount (X - (E : ℂ) • 1) = ℓ.val) :
    freshEigenvalue ((E : ℂ) • vecMulVec v (star v) + U * X * Uᴴ) ℓ = E ∧
      vecMulVec (freshEigenvector ((E : ℂ) • vecMulVec v (star v) + U * X * Uᴴ) ℓ)
          (star (freshEigenvector ((E : ℂ) • vecMulVec v (star v) + U * X * Uᴴ) ℓ)) =
        vecMulVec v (star v) := by
  classical
  set K := (E : ℂ) • vecMulVec v (star v) + U * X * Uᴴ with hKdef
  set M := X - (E : ℂ) • 1
  have hvv := dotProduct_self_of_l2Norm v hv
  have hcard : Fintype.card (Fin N) = Fintype.card (Unit ⊕ Fin (N - 1)) := by
    rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_fin]; omega
  have hc := frame_complete U v hUU hUv hvv hcard
  have hKE : K - (E : ℂ) • 1 = U * M * Uᴴ := by
    have h1 : (E : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) =
        (E : ℂ) • vecMulVec v (star v) +
          U * ((E : ℂ) • (1 : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ)) * Uᴴ := by
      rw [← hc, smul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [h1, hKdef]
    simp only [M, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hKh : K.IsHermitian :=
    ((vecMulVec_self_isHermitian v).smul (Complex.conj_ofReal E)).add
      (isHermitian_mul_mul_conjTranspose U hX)
  have hMh : M.IsHermitian := hX.sub (isHermitian_one.smul (Complex.conj_ofReal E))
  have hKs : (K - (E : ℂ) • 1).IsHermitian := shift_isHermitian hKh E
  have hUMU : (U * M * Uᴴ).IsHermitian := by rw [← hKE]; exact hKs
  have hcntK : negativeEigenvalueCount hKs = ℓ.val := by
    rw [negCount_congr hKs hUMU hKE, negCount_frame U M hUU hUMU hMh, ← negativeCount_eq hMh,
      hcnt]
  have hEC : CoareaNative.BlockBand.eigenCount
      (⟨K, hKh⟩ : CoareaNative.BlockBand.HermitianMatrix (Fin N)) (Set.Iio E) = ℓ.val := by
    rw [← hcntK]
    exact (CoareaNative.BlockBand.negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio
      ⟨K, hKh⟩ E).symm
  -- kernel of `K - E` is `ℂ v`
  have hL0 : (K - (E : ℂ) • 1) *ᵥ v = 0 := by
    rw [hKE, ← Matrix.mulVec_mulVec, hUv, Matrix.mulVec_zero]
  have hker : ∀ y : Fin N → ℂ, (K - (E : ℂ) • 1) *ᵥ y = 0 → y = (star v ⬝ᵥ y) • v := by
    intro y hy
    rw [hKE] at hy
    have hMU : M *ᵥ (Uᴴ *ᵥ y) = 0 := by
      have h := congrArg (fun x => Uᴴ *ᵥ x) hy
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h
      rw [Matrix.mulVec_mulVec]
      rwa [show Uᴴ * (U * M * Uᴴ) = (Uᴴ * U) * M * Uᴴ by simp only [Matrix.mul_assoc], hUU,
        Matrix.one_mul] at h
    have hUy : Uᴴ *ᵥ y = 0 := by
      by_contra h0
      exact hdet ((Matrix.exists_mulVec_eq_zero_iff (M := M)).mp ⟨_, h0, hMU⟩)
    have h := congrArg (fun Z => Z *ᵥ y) hc
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hUy,
      Matrix.mulVec_zero, add_zero, Matrix.vecMulVec_mulVec] at h
    nth_rewrite 1 [← h]
    ext s
    simp [mul_comm]
  have hvne : v ≠ 0 := by
    intro h; rw [h] at hvv; simp at hvv
  obtain ⟨j0, hj0⟩ :=
    CoareaNative.BlockBand.exists_orderedEigenvalue_eq_of_shift_mulVec_eq_zero
      (⟨K, hKh⟩ : CoareaNative.BlockBand.HermitianMatrix (Fin N)) hvne hL0
  change increasingEigenvalue hKh j0 = E at hj0
  have hmult : ∀ j, increasingEigenvalue hKh j = E →
      increasingEigenvector hKh j = (star v ⬝ᵥ increasingEigenvector hKh j) • v := by
    intro j hj
    apply hker
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, mulVec_increasingEigenvector,
      hj, sub_self]
  have hsimple : ∀ j, increasingEigenvalue hKh j = E → j = j0 := by
    intro j hj
    by_contra hne
    set cj := star v ⬝ᵥ increasingEigenvector hKh j
    set ck := star v ⬝ᵥ increasingEigenvector hKh j0
    set s := ∑ x, starRingEnd ℂ (v x) * v x
    have horth := increasingEigenvector_orthonormal hKh
    have h0 := horth j j0
    have h1 := horth j j
    have h2 := horth j0 j0
    rw [hmult j hj] at h0 h1
    rw [hmult j0 hj0] at h0 h2
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hne, ↓reduceIte] at h0 h1 h2
    have e0 : starRingEnd ℂ cj * ck * s = 0 := by
      rw [← h0, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have e1 : starRingEnd ℂ cj * cj * s = 1 := by
      rw [← h1, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have e2 : starRingEnd ℂ ck * ck * s = 1 := by
      rw [← h2, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have : (1 : ℂ) = 0 := by
      linear_combination (cj * starRingEnd ℂ ck * s) * e0 - (starRingEnd ℂ ck * ck * s) * e1 - e2
    exact one_ne_zero this
  have hrank := rank_of_simple hKh E j0 hj0 hsimple
  rw [hEC] at hrank
  set r : Fin (Fintype.card (Fin N)) := Fin.cast (Fintype.card_fin N).symm ℓ with hrdef
  have hr : r = j0 := Fin.ext (by simp [r, hrank])
  have hEr : freshEigenvalue K ℓ = E := by
    rw [show freshEigenvalue K ℓ = increasingEigenvalue hKh r from
      rawIncreasingEigenvalue_eq r K hKh, hr, hj0]
  refine ⟨hEr, ?_⟩
  have hsr : RankSimple (⟨K, hKh⟩ : HermitianMatrix (Fin N)) r := by
    intro j hj
    change increasingEigenvalue hKh j = increasingEigenvalue hKh r at hj
    rw [hr, hj0] at hj
    rw [hr]; exact hsimple j hj
  obtain ⟨z, hz, hsel⟩ := orderedColumnSelection_eq_phase_of_rankSimple r _ hsr
  have hψ : freshEigenvector K ℓ = z • increasingEigenvector hKh r :=
    (funext (rawOrderedColumnSelection_eq r K hKh)).trans hsel
  set c := star v ⬝ᵥ increasingEigenvector hKh r
  have hur : increasingEigenvector hKh r = c • v := hmult r (by rw [hr, hj0])
  have hnorm := sum_norm_sq_increasingEigenvector hKh r
  rw [hur] at hnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow] at hnorm
  rw [← Finset.mul_sum] at hnorm
  have hv2 : ∑ x, ‖v x‖ ^ 2 = 1 := by
    have h0 : 0 ≤ ∑ k, ‖v k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    unfold l2Norm at hv
    have := Real.sq_sqrt h0
    rw [hv] at this
    linarith
  rw [hv2, mul_one] at hnorm
  have hzz : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hcc : c * starRingEnd ℂ c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
  rw [hψ, hur]
  ext x y
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_mul']
  have : z * (c * v x) * (star z * (star c * star (v y))) =
      (z * starRingEnd ℂ z) * (c * starRingEnd ℂ c) * (v x * star (v y)) := by
    simp only [RCLike.star_def]; ring
  rw [this, hzz, hcc, one_mul, one_mul]

/-- `K - cI = (E - c) vv* + U (X - c) U*` for an orthonormal frame `U` of `v^⊥`. -/
theorem shift_frame_eq (hN : 0 < N) (U : Matrix (Fin N) (Fin (N - 1)) ℂ) (v : Fin N → ℂ)
    (hUU : Uᴴ * U = 1) (hUv : Uᴴ *ᵥ v = 0) (hv : l2Norm v = 1)
    (X : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ) (E c : ℝ) :
    (E : ℂ) • vecMulVec v (star v) + U * X * Uᴴ - (c : ℂ) • 1 =
      ((E - c : ℝ) : ℂ) • vecMulVec v (star v) + U * (X - (c : ℂ) • 1) * Uᴴ := by
  have hvv := dotProduct_self_of_l2Norm v hv
  have hcard : Fintype.card (Fin N) = Fintype.card (Unit ⊕ Fin (N - 1)) := by
    rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_fin]; omega
  have hc := frame_complete U v hUU hUv hvv hcard
  have h1 : (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) =
      (c : ℂ) • vecMulVec v (star v) +
        U * ((c : ℂ) • (1 : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ)) * Uᴴ := by
    rw [← hc, smul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [h1, Matrix.mul_sub, Matrix.sub_mul, Complex.ofReal_sub, sub_smul]
  abel

/-- **Shifted fresh rank identification.** -/
theorem fresh_rank_shift (hN : 0 < N) (U : Matrix (Fin N) (Fin (N - 1)) ℂ) (v : Fin N → ℂ)
    (hUU : Uᴴ * U = 1) (hUv : Uᴴ *ᵥ v = 0) (hv : l2Norm v = 1)
    (X : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ) (hX : X.IsHermitian) (E : ℝ)
    (hdet : (X - (E : ℂ) • 1).det ≠ 0) (ℓ : Fin N)
    (hcnt : negativeCount (X - (E : ℂ) • 1) = ℓ.val) (c : ℝ) :
    freshEigenvalue ((E : ℂ) • vecMulVec v (star v) + U * X * Uᴴ - (c : ℂ) • 1) ℓ = E - c ∧
      vecMulVec (freshEigenvector ((E : ℂ) • vecMulVec v (star v) + U * X * Uᴴ - (c : ℂ) • 1) ℓ)
          (star (freshEigenvector
            ((E : ℂ) • vecMulVec v (star v) + U * X * Uᴴ - (c : ℂ) • 1) ℓ)) =
        vecMulVec v (star v) := by
  rw [shift_frame_eq hN U v hUU hUv hv X E c]
  have hXc : (X - (c : ℂ) • 1).IsHermitian := hX.sub (isHermitian_one.smul (Complex.conj_ofReal c))
  have hsame : X - (c : ℂ) • 1 - ((E - c : ℝ) : ℂ) • 1 = X - (E : ℂ) • 1 := by
    rw [Complex.ofReal_sub, sub_smul]; abel
  exact fresh_rank hN U v hUU hUv hv (X - (c : ℂ) • 1) hXc (E - c) (by rwa [hsame]) ℓ
    (by rwa [hsame])

/-- **Rank identification on the fresh fiber.** -/
theorem freshReconstructed_rank (hN : 0 < N)
    (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ) (hU : IsFreshFrame U)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (E : ℝ) (v : Fin N → ℂ)
    (hv : l2Norm v = 1) (G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ) (hG' : G'.IsHermitian)
    (hdet : (freshFrameM U F E v G').det ≠ 0) (ℓ : Fin N)
    (hcnt : negativeCount (freshFrameM U F E v G') = ℓ.val) (c : ℝ) :
    freshEigenvalue (F + freshReconstructed U F E v G' - (c : ℂ) • 1) ℓ = E - c ∧
      vecMulVec (freshEigenvector (F + freshReconstructed U F E v G' - (c : ℂ) • 1) ℓ)
          (star (freshEigenvector (F + freshReconstructed U F E v G' - (c : ℂ) • 1) ℓ)) =
        vecMulVec v (star v) := by
  obtain ⟨hUU, hUv⟩ := hU.2 v hv
  have hK : F + freshReconstructed U F E v G' =
      (E : ℂ) • vecMulVec v (star v) + U v * ((U v)ᴴ * F * U v + G') * (U v)ᴴ := by
    unfold freshReconstructed; abel
  have hX : ((U v)ᴴ * F * U v + G').IsHermitian :=
    (isHermitian_conjTranspose_mul_mul (U v) hF).add hG'
  rw [hK]
  exact fresh_rank_shift hN (U v) v hUU hUv hv _ hX E hdet ℓ hcnt c

end BlockBand.Coarea.FreshPalm
