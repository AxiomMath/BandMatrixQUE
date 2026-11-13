module

public import BlockBand.SourceProcess.ModelExist.SelectSpec
public import BlockBand.SourceProcess.Stochastic.RankBarrier

/-!
# A perpendicular near direction exists when the near rank is full

`selExists_of_rank`: for a frame `X` (rows `ι`) with `rank(P X) ≥ rank P` and
`#cur + n + |ι| < 2 rank P`, the subspace `range X ∩ range P` has dimension
`≥ 2 rank P − |ι|`, so it contains a nonzero vector `X a` perpendicular to the current columns
`X e_k` and to `X prev_l`; then `a` satisfies the linear conditions for `gramPair P X` with
`M a ≠ 0`. `rank_le_of_principalMinorSum_pos`: `e_k(A) > 0 ⇒ rank A ≥ k`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open Matrix Finset Module BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open scoped ComplexOrder

variable {ι c' : Type*} [Fintype ι] [DecidableEq ι] [Fintype c'] [DecidableEq c'] {n : ℕ}

theorem rank_le_of_principalMinorSum_pos (A : Matrix c' c' ℂ) (k : ℕ)
    (h : 0 < principalMinorSum k A) : k ≤ A.rank := by
  obtain ⟨s, hs, hdet⟩ : ∃ s ∈ (univ : Finset c').powersetCard k,
      (A.submatrix (fun i : s => (i : c')) (fun i : s => (i : c'))).det ≠ 0 := by
    by_contra hall
    push Not at hall
    simp only [principalMinorSum, Finset.sum_eq_zero hall, Complex.zero_re, lt_irrefl] at h
  have hu : IsUnit (A.submatrix (fun i : s => (i : c')) (fun i : s => (i : c'))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have h1 := rank_of_isUnit _ hu
  have h2 := rank_submatrix_le A (fun i : s => (i : c')) (fun i : s => (i : c'))
  rw [h1, Fintype.card_coe, (Finset.mem_powersetCard.1 hs).2] at h2
  exact h2

omit [DecidableEq ι] [DecidableEq c'] in
theorem selExists_of_rank {P : Matrix ι ι ℂ} (hPP : P * P = P) (X : Matrix ι c' ℂ)
    (cur : c' → Prop) [DecidablePred cur] (prev : Fin n → c' → ℂ)
    (hdim : (univ.filter cur).card + n + Fintype.card ι < 2 * P.rank)
    (hrank : P.rank ≤ (P * X).rank) : SelExists cur (gramPair P X) prev := by
  set U := LinearMap.range X.mulVecLin
  set N := LinearMap.range P.mulVecLin
  have hU : P.rank ≤ finrank ℂ U := hrank.trans (rank_mul_le_right P X)
  have hN : finrank ℂ N = P.rank := rfl
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq U N
  have hle : finrank ℂ ↥(U ⊔ N) ≤ Fintype.card ι :=
    (Submodule.finrank_le _).trans (Module.finrank_fintype_fun_eq_card ℂ).le
  -- the perpendicularity functionals
  let u : {k // cur k} ⊕ Fin n → ι → ℂ := fun r => match r with
    | Sum.inl k => fun i => X i k
    | Sum.inr l => X *ᵥ prev l
  let A : Matrix ({k // cur k} ⊕ Fin n) ι ℂ := fun r => star (u r)
  let ψ := A.mulVecLin.domRestrict (U ⊓ N)
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  have hrange : finrank ℂ (LinearMap.range ψ) ≤ (univ.filter cur).card + n := by
    refine (Submodule.finrank_le _).trans ?_
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_subtype]
  have hker : 0 < finrank ℂ (LinearMap.ker ψ) := by omega
  have hbot : LinearMap.ker ψ ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hker; exact lt_irrefl _ hker
  obtain ⟨⟨w, hw⟩, hψ, hne⟩ := (Submodule.ne_bot_iff _).1 hbot
  have hw0 : w ≠ 0 := fun h => hne (by ext; simp [h])
  obtain ⟨a, ha⟩ := hw.1
  obtain ⟨z, hz⟩ := hw.2
  have hAw : A *ᵥ w = 0 := LinearMap.mem_ker.1 hψ
  simp only [mulVecLin_apply] at ha hz
  have hPw : P *ᵥ w = w := by rw [← hz, mulVec_mulVec, hPP]
  have hMa : (gramPair P X).1 *ᵥ a = Xᴴ *ᵥ w := by
    simp only [gramPair, sourceGram, ← mulVec_mulVec, ha]
  refine ⟨a, ⟨?_, fun k hk => ?_, fun l => ?_⟩, ?_⟩
  · simp only [gramPair, sourceGram, nearGram, sub_mulVec, ← mulVec_mulVec, ha, hPw, sub_self]
  · rw [hMa]
    have := congrFun hAw (Sum.inl ⟨k, hk⟩)
    simpa [A, u, mulVec, dotProduct, conjTranspose_apply] using this
  · rw [hMa, dotProduct_mulVec, ← star_mulVec]
    exact congrFun hAw (Sum.inr l)
  · rw [hMa]
    intro h0
    have : star w ⬝ᵥ w = 0 := by
      calc star w ⬝ᵥ w = star (X *ᵥ a) ⬝ᵥ w := by rw [ha]
        _ = star a ⬝ᵥ (Xᴴ *ᵥ w) := by rw [star_mulVec, ← dotProduct_mulVec]
        _ = 0 := by rw [h0, dotProduct_zero]
    exact hw0 (dotProduct_star_self_eq_zero.1 this)

end BlockBand.SourceProcess.ModelExist
