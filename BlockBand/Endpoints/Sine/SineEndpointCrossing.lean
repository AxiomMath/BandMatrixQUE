module

public import BlockBand.Endpoints.Sine.CrossingSineAlgebra
public import BlockBand.Model.Construction.SpectralPhysical

/-!
# Crossing parameters as branch crossings (deterministic)

For Hermitian `H` with invertible exterior minor `H_RR - E` and `𝒩ρ ≠ 0`, the crossing
parameters of the pair flow `H(t) = H + t/(𝒩ρ) P_S` (real roots of `crossingPoly`, with
multiplicity) are exactly the branch crossings: every real `t` has root multiplicity
`#{k : -𝒩ρ μ_k = t}` (`μ_k` the eigenvalues of the Schur complement `pairSchur`), and this equals
`#{α : λ_α(H(t)) = E}` (`sec_count`). The proof is by ranks: `rank(H(t) - E) =
#{α : λ_α(H(t)) ≠ E}` (spectral theorem, `sec_rank_add`), and the LDU factorization of the
block form with invertible corner `H_RR - E` gives
`rank(H(t) - E) = rank(pairSchur + t/(𝒩ρ)) + |R|` (`sec_rank_pairFlow`).

Main results: `se_mem_rootSet`, `se_crossingSum_eq`. Deterministic; no measure.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix Polynomial
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers

theorem sec_conj_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (c : ℝ) :
    A + (c : ℂ) • 1 = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun x => ((hA.eigenvalues x + c : ℝ) : ℂ)) *
        star (hA.eigenvectorUnitary : Matrix ι ι ℂ) := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hd : diagonal (fun x => ((hA.eigenvalues x + c : ℝ) : ℂ)) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) + (c : ℂ) • 1 := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · simp [diagonal, h]
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

theorem sec_rank_add {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (c : ℝ) :
    (A + (c : ℂ) • 1).rank = (Finset.univ.filter fun x => hA.eigenvalues x + c ≠ 0).card := by
  rw [sec_conj_diag hA c]
  have h1 : IsUnit (star (hA.eigenvectorUnitary : Matrix ι ι ℂ)).det := by
    rw [← Unitary.coe_star]; exact UnitaryGroup.det_isUnit _
  have h2 : IsUnit (hA.eigenvectorUnitary : Matrix ι ι ℂ).det :=
    UnitaryGroup.det_isUnit hA.eigenvectorUnitary
  rw [rank_mul_eq_left_of_isUnit_det _ _ h1, rank_mul_eq_right_of_isUnit_det _ _ h2,
    rank_diagonal, Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Complex.ofReal_eq_zero]

theorem sec_rank_fromBlocks {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : D.det ≠ 0) (hS : (A - B * D⁻¹ * C).IsHermitian) :
    (fromBlocks A B C D).rank = (A - B * D⁻¹ * C).rank + Fintype.card n := by
  let _ := invertibleOfIsUnitDet D (isUnit_iff_ne_zero.mpr hD)
  rw [fromBlocks_eq_of_invertible₂₂, invOf_eq_nonsing_inv]
  rw [rank_mul_eq_left_of_isUnit_det _ _ (by simp),
    rank_mul_eq_right_of_isUnit_det _ _ (by simp)]
  set S := A - B * D⁻¹ * C
  set U : Matrix m m ℂ := (hS.eigenvectorUnitary : Matrix m m ℂ)
  have hSU : S = U * diagonal (RCLike.ofReal ∘ hS.eigenvalues) * star U := by
    conv_lhs => rw [hS.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have hfac : fromBlocks S 0 0 D = fromBlocks U 0 0 1 *
      fromBlocks (diagonal (RCLike.ofReal ∘ hS.eigenvalues)) 0 0 (1 : Matrix n n ℂ) *
        fromBlocks (star U) 0 0 D := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one]
    rw [← hSU]
  have h1 : IsUnit (star U).det := by
    rw [← Unitary.coe_star]; exact UnitaryGroup.det_isUnit _
  have h2 : IsUnit U.det := UnitaryGroup.det_isUnit hS.eigenvectorUnitary
  rw [hfac, rank_mul_eq_left_of_isUnit_det _ _ (by
      rw [det_fromBlocks_zero₂₁]; exact h1.mul (isUnit_iff_ne_zero.mpr hD)),
    rank_mul_eq_right_of_isUnit_det _ _ (by rw [det_fromBlocks_zero₂₁]; simpa using h2),
    ← diagonal_one, fromBlocks_diagonal, rank_diagonal,
    Fintype.card_congr (Equiv.subtypeSum), Fintype.card_sum, Fintype.card_subtype]
  rw [hS.rank_eq_card_non_zero_eigs, Fintype.card_subtype (fun i => hS.eigenvalues i ≠ 0)]
  congr 1
  · congr 1; ext k; simp
  · simp

theorem sec_card_eig (p : Parameters) (M : p.SiteMatrix) (hM : M.IsHermitian) (E : ℝ) :
    (Finset.univ.filter fun α : Fin p.N => physicalOrderedEigenvalue p M α = E).card =
      (Finset.univ.filter fun x : p.Site => hM.eigenvalues x = E).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  refine Fintype.card_congr (Equiv.subtypeEquiv ((finCongr (physicalSite_card p).symm).trans
    BlockBand.Foundations.Spectral.increasingIndex) fun α => ?_)
  simp only [Equiv.trans_apply, BlockBand.Foundations.Spectral.eigenvalue_increasingIndex,
    physicalOrderedEigenvalue, rawIncreasingEigenvalue_eq _ M hM, physicalSpectralRank,
    finCongr_apply]

section Pair

variable (p : Parameters) (i : ZMod p.n)

theorem sec_isHermitian_pairFlow (H : p.SiteMatrix) (hH : H.IsHermitian) (E t : ℝ) :
    (pairFlow p i H E t).IsHermitian := by
  refine hH.add ?_
  ext x y
  by_cases h : x = y
  · subst h
    simp only [pairProjector, conjTranspose_apply, Matrix.smul_apply, diagonal_apply_eq]
    split_ifs <;> simp
  · simp [pairProjector, h, Ne.symm h]

theorem sec_schur_blocks (H : p.SiteMatrix) (E t : ℝ) :
    let M := ((pairFlow p i H E t - (E : ℂ) • 1).submatrix (pairSplit p i) (pairSplit p i))
    M.toBlocks₂₂ = exteriorBlock p i H - (E : ℂ) • 1 ∧
      M.toBlocks₁₂ = pairExteriorBlock p i H ∧ M.toBlocks₂₁ = couplingBlock p i H ∧
      M.toBlocks₁₁ = pairBlock p i H - (E : ℂ) • 1 +
        ((t / crossingScale p E : ℝ) : ℂ) • 1 := by
  intro M
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x y
    have hx := x.2
    simp only [M, toBlocks₂₂, submatrix_apply, of_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.add_apply, pairFlow, pairProjector, exteriorBlock, Equiv.sumCompl_apply_inr]
    by_cases hxy : x = y
    · subst hxy; simp [hx]
    · have : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      simp [one_apply, this, hxy]
  · ext a b
    have hne : a.1 ≠ b.1 := fun h => b.2 (h ▸ a.2)
    simp [M, toBlocks₁₂, pairFlow, pairProjector, pairExteriorBlock, one_apply, hne]
  · ext a b
    have hne : a.1 ≠ b.1 := fun h => a.2 (h ▸ b.2)
    simp [M, toBlocks₂₁, pairFlow, pairProjector, couplingBlock, one_apply, hne]
  · ext a b
    have ha := a.2
    simp only [M, toBlocks₁₁, submatrix_apply, of_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.add_apply, pairFlow, pairProjector, pairBlock, Equiv.sumCompl_apply_inl, smul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp [ha]; ring
    · have : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      simp [one_apply, this, hab]

theorem sec_rank_pairFlow (H : p.SiteMatrix) (hH : H.IsHermitian) (E t : ℝ)
    (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0) :
    (pairFlow p i H E t - (E : ℂ) • 1).rank =
      (pairSchur p i H E + ((t / crossingScale p E : ℝ) : ℂ) • 1).rank +
        Fintype.card (ExteriorSite p i) := by
  obtain ⟨h22, h12, h21, h11⟩ := sec_schur_blocks p i H E t
  set M := ((pairFlow p i H E t - (E : ℂ) • 1).submatrix (pairSplit p i) (pairSplit p i))
  have hS : M.toBlocks₁₁ - M.toBlocks₁₂ * M.toBlocks₂₂⁻¹ * M.toBlocks₂₁ =
      pairSchur p i H E + ((t / crossingScale p E : ℝ) : ℂ) • 1 := by
    rw [h22, h12, h21, h11, pairSchur]
    abel
  have hSh : (M.toBlocks₁₁ - M.toBlocks₁₂ * M.toBlocks₂₂⁻¹ * M.toBlocks₂₁).IsHermitian := by
    rw [hS]
    exact (pairSchur_isHermitian p i H hH E).add (isHermitian_real_smul_one _)
  rw [← rank_submatrix _ (pairSplit p i) (pairSplit p i)]
  change M.rank = _
  rw [← fromBlocks_toBlocks M, sec_rank_fromBlocks _ _ _ _ (by rw [h22]; exact hdet) hSh, hS]

theorem sec_count (H : p.SiteMatrix) (hH : H.IsHermitian) (E : ℝ)
    (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0) (hsc : crossingScale p E ≠ 0) (t : ℝ) :
    (Finset.univ.filter fun α : Fin p.N =>
        physicalOrderedEigenvalue p (pairFlow p i H E t) α = E).card =
      (Finset.univ.filter fun k : PairSite p i =>
        -(crossingScale p E * (pairSchur_isHermitian p i H hH E).eigenvalues k) = t).card := by
  have hM := sec_isHermitian_pairFlow p i H hH E t
  rw [sec_card_eig p _ hM E]
  set μ := (pairSchur_isHermitian p i H hH E).eigenvalues
  have h1 := sec_rank_add hM (-E)
  have h2 := sec_rank_pairFlow p i H hH E t hdet
  have h3 := sec_rank_add (pairSchur_isHermitian p i H hH E) (t / crossingScale p E)
  have hsub : pairFlow p i H E t + ((-E : ℝ) : ℂ) • 1 = pairFlow p i H E t - (E : ℂ) • 1 := by
    rw [Complex.ofReal_neg, neg_smul, ← sub_eq_add_neg]
  rw [hsub] at h1
  have a1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : p.Site => hM.eigenvalues x = E)
  have a2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun k : PairSite p i => -(crossingScale p E * μ k) = t)
  have e1 : (Finset.univ.filter fun x : p.Site => hM.eigenvalues x + -E ≠ 0) =
      Finset.univ.filter fun x : p.Site => ¬ hM.eigenvalues x = E := by
    ext x; simp [sub_eq_zero, ← sub_eq_add_neg]
  have e2 : (Finset.univ.filter fun k : PairSite p i => μ k + t / crossingScale p E ≠ 0) =
      Finset.univ.filter fun k : PairSite p i => ¬ -(crossingScale p E * μ k) = t := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    refine not_congr ⟨fun h => ?_, fun h => ?_⟩
    · have : μ k = -(t / crossingScale p E) := by linarith
      rw [this]; field_simp
    · rw [← h]; field_simp; ring
  have hcard : Fintype.card p.Site = Fintype.card (PairSite p i) + Fintype.card (ExteriorSite p i) := by
    rw [Fintype.card_congr (pairSplit p i).symm, Fintype.card_sum]
  rw [e1] at h1
  rw [e2] at h3
  rw [Finset.card_univ] at a1 a2
  omega

/-- The (finite) set of distinct real crossing parameters: real roots of `crossingPoly`. -/
def se_rootSet (H : p.SiteMatrix) (E : ℝ) : Finset ℝ :=
  (((crossingPoly p i H E).roots.filter fun z => z.im = 0).map fun z => z.re).toFinset

/-- All roots of `crossingPoly` are real: their real parts are the `-𝒩ρ μ_k`. -/
theorem sec_realRoots (H : p.SiteMatrix) (hH : H.IsHermitian) (E : ℝ)
    (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0) (hsc : crossingScale p E ≠ 0) :
    ((crossingPoly p i H E).roots.filter fun z => z.im = 0).map (fun z => z.re) =
      Finset.univ.val.map
        (fun k => -(crossingScale p E * (pairSchur_isHermitian p i H hH E).eigenvalues k)) := by
  rw [crossingPoly_eq p i H hH E hdet hsc, roots_C_mul]
  · set g : PairSite p i → ℂ :=
      fun k => ((-(crossingScale p E * (pairSchur_isHermitian p i H hH E).eigenvalues k) : ℝ) : ℂ)
    have hprod : ∏ k, (X - C (g k)) = ((Finset.univ.val.map g).map fun a => X - C a).prod := by
      rw [Multiset.map_map, Finset.prod_eq_multiset_prod]; rfl
    rw [hprod, roots_multiset_prod_X_sub_C, Multiset.filter_eq_self.mpr, Multiset.map_map]
    · simp only [Function.comp_def, g, Complex.ofReal_re]
    · intro z hz
      obtain ⟨k, _, rfl⟩ := Multiset.mem_map.mp hz
      simp [g]
  · refine mul_ne_zero hdet (pow_ne_zero _ ?_)
    exact_mod_cast inv_ne_zero hsc

theorem sec_rootSet_eq (H : p.SiteMatrix) (hH : H.IsHermitian) (E : ℝ)
    (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0) (hsc : crossingScale p E ≠ 0) :
    se_rootSet p i H E = Finset.univ.image
      (fun k => -(crossingScale p E * (pairSchur_isHermitian p i H hH E).eigenvalues k)) := by
  unfold se_rootSet
  rw [sec_realRoots p i H hH E hdet hsc]
  rfl

/-- A real `t` is a crossing parameter iff `E` is an eigenvalue of `H(t)`. -/
theorem se_mem_rootSet (H : p.SiteMatrix) (hH : H.IsHermitian) (E : ℝ)
    (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0) (hsc : crossingScale p E ≠ 0) (t : ℝ) :
    t ∈ se_rootSet p i H E ↔
      ∃ α : Fin p.N, physicalOrderedEigenvalue p (pairFlow p i H E t) α = E := by
  have hc := sec_count p i H hH E hdet hsc t
  rw [sec_rootSet_eq p i H hH E hdet hsc, Finset.mem_image]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    have h0 : 0 < (Finset.univ.filter fun k : PairSite p i =>
        -(crossingScale p E * (pairSchur_isHermitian p i H hH E).eigenvalues k) = t).card :=
      Finset.card_pos.mpr ⟨k, by simp [hk]⟩
    rw [← hc] at h0
    obtain ⟨α, hα⟩ := Finset.card_pos.mp h0
    exact ⟨α, (Finset.mem_filter.mp hα).2⟩
  · rintro ⟨α, hα⟩
    have h0 : 0 < (Finset.univ.filter fun α : Fin p.N =>
        physicalOrderedEigenvalue p (pairFlow p i H E t) α = E).card :=
      Finset.card_pos.mpr ⟨α, by simp [hα]⟩
    rw [hc] at h0
    obtain ⟨k, hk⟩ := Finset.card_pos.mp h0
    exact ⟨k, (Finset.mem_filter.mp hk).2⟩

/-- **The crossing statistic is the sum over branch crossings** (with multiplicity): each
crossing parameter `t` is counted as many times as there are ranks `α` with
`λ_α(H(t)) = E`. -/
theorem se_crossingSum_eq (H : p.SiteMatrix) (hH : H.IsHermitian) (E : ℝ)
    (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0) (hsc : crossingScale p E ≠ 0)
    (g : ℝ → ℝ) :
    crossingSum p i g H E =
      ∑ α : Fin p.N, ∑ t ∈ (se_rootSet p i H E).filter
        (fun t => physicalOrderedEigenvalue p (pairFlow p i H E t) α = E), g t := by
  set r : PairSite p i → ℝ :=
    fun k => -(crossingScale p E * (pairSchur_isHermitian p i H hH E).eigenvalues k) with hr
  rw [crossingSum_eq p i g H hH E hdet hsc]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  have hstep : ∀ t ∈ se_rootSet p i H E,
      (∑ α : Fin p.N, if physicalOrderedEigenvalue p (pairFlow p i H E t) α = E then g t else 0) =
        ∑ k ∈ Finset.univ.filter (fun k => r k = t), g (r k) := by
    intro t _
    rw [← Finset.sum_filter, Finset.sum_const, sec_count p i H hH E hdet hsc t,
      Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const]
  rw [Finset.sum_congr rfl hstep, Finset.sum_fiberwise_of_maps_to]
  intro k _
  rw [sec_rootSet_eq p i H hH E hdet hsc]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ k)

end Pair

end BlockBand.Endpoints
