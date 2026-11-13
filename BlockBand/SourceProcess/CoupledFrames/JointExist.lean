module

public import BlockBand.SourceProcess.CoupledFrames.JointSpec

/-!
# The two-frame selection: existence of a solution

`jointExists`: if `rank(P Y_j) ≥ rank P` (`j = 1, 2`) and `2 #cur + 2n + 2|ι| < 3 rank P`, then
some `a` has `jointG H prev a = 0` and `jointQ H a ≠ 0`, `H = gramPair P [Y₁ | Y₂]`: take the
common perpendicular near direction `w = Y₁ a₁ = Y₂ a₂` of `exists_common_perp`, perpendicular to
the current columns of both frames and to the earlier vectors `[Y₁|Y₂] prev_lᴶ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open scoped ComplexOrder

variable {c' : Type*} [Fintype c'] [DecidableEq c'] {n : ℕ} {cur : c' → Prop} [DecidablePred cur]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype c'] [DecidableEq c'] [DecidableEq ι] in
theorem conjTranspose_mulVec_apply (Y : Matrix ι c' ℂ) (w : ι → ℂ) (k : c') :
    (Yᴴ *ᵥ w) k = star (fun i => Y i k) ⬝ᵥ w := by
  simp [mulVec, dotProduct, conjTranspose_apply]

theorem jointExists {P : Matrix ι ι ℂ} (hPP : P * P = P) (Y₁ Y₂ : Matrix ι c' ℂ)
    (h₁ : P.rank ≤ (P * Y₁).rank) (h₂ : P.rank ≤ (P * Y₂).rank) (prev : Fin n → c' ⊕ c' → ℂ)
    (hdim : 2 * (univ.filter cur).card + 2 * n + 2 * Fintype.card ι < 3 * P.rank) :
    ∃ a, jointG cur (gramPair P (fromCols Y₁ Y₂)) prev *ᵥ a = 0 ∧
      jointQ (gramPair P (fromCols Y₁ Y₂)) *ᵥ a ≠ 0 := by
  set V := fromCols Y₁ Y₂
  let u : ({k // cur k} ⊕ {k // cur k}) ⊕ (Fin n × Fin 2) → ι → ℂ := fun f => match f with
    | Sum.inl (Sum.inl k) => fun i => Y₁ i k.1
    | Sum.inl (Sum.inr k) => fun i => Y₂ i k.1
    | Sum.inr (l, j) => V *ᵥ (projF j *ᵥ prev l)
  have hcard : Fintype.card (({k // cur k} ⊕ {k // cur k}) ⊕ (Fin n × Fin 2)) =
      2 * (univ.filter cur).card + 2 * n := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype]
    ring
  obtain ⟨w, hw0, ⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, hPw, hperp⟩ :=
    exists_common_perp hPP Y₁ Y₂ h₁ h₂ u (by rw [hcard]; omega)
  set a : c' ⊕ c' → ℂ := Sum.elim a₁ a₂
  obtain ⟨e1, e2⟩ := fromCols_mulVec_projF Y₁ Y₂ a
  have hf1 : V *ᵥ (projF 0 *ᵥ a) = w := e1.trans ha₁
  have hf2 : V *ᵥ (projF 1 *ᵥ a) = w := e2.trans ha₂
  have hM : (gramPair P V).1 = Vᴴ * V := rfl
  have hMB : (gramPair P V).1 - (gramPair P V).2 = Vᴴ * ((1 - P) * V) := by
    simp only [gramPair, sourceGram, nearGram, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc]
  have hMa : (gramPair P V).1 *ᵥ (projF 0 *ᵥ a) = Vᴴ *ᵥ w := by
    rw [hM, ← mulVec_mulVec, hf1]
  refine ⟨a, funext fun r => ?_, fun hQ => hw0 ?_⟩
  · rcases r with z | z | z | ⟨l, j⟩
    · change (((gramPair P V).1 * (projF 0 - projF 1)) *ᵥ a) z = 0
      rw [← mulVec_mulVec, sub_mulVec, hM, ← mulVec_mulVec, mulVec_sub, hf1, hf2, sub_self,
        mulVec_zero]
      rfl
    · change ((((gramPair P V).1 - (gramPair P V).2) * projF 0) *ᵥ a) z = 0
      rw [← mulVec_mulVec, hMB, ← mulVec_mulVec, ← mulVec_mulVec, hf1, sub_mulVec, one_mulVec,
        hPw, sub_self, mulVec_zero]
      rfl
    · change ((curMat cur * (gramPair P V).1 * projF 0) *ᵥ a) z = 0
      rw [← mulVec_mulVec, ← mulVec_mulVec, hMa]
      rcases z with k | k
      · simp only [curMat, mulVec_diagonal]
        split_ifs with hk
        · rw [one_mul, (fromCols_conjTranspose_mulVec Y₁ Y₂ w k).1, conjTranspose_mulVec_apply]
          exact hperp (Sum.inl (Sum.inl ⟨k, hk⟩))
        · rw [zero_mul]
      · simp only [curMat, mulVec_diagonal]
        split_ifs with hk
        · rw [one_mul, (fromCols_conjTranspose_mulVec Y₁ Y₂ w k).2, conjTranspose_mulVec_apply]
          exact hperp (Sum.inl (Sum.inr ⟨k, hk⟩))
        · rw [zero_mul]
    · change (star (projF j *ᵥ prev l) ᵥ* ((gramPair P V).1 * projF 0)) ⬝ᵥ a = 0
      rw [← dotProduct_mulVec, ← mulVec_mulVec, hMa, dot_conjTranspose_mulVec]
      exact hperp (Sum.inr (l, j))
  · have h0 : star a ⬝ᵥ (jointQ (gramPair P V) *ᵥ a) = 0 := by rw [hQ, dotProduct_zero]
    have e : star a ⬝ᵥ (jointQ (gramPair P V) *ᵥ a) = star w ⬝ᵥ w := by
      rw [jointQ, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← projF_herm 0,
        ← star_mulVec, projF_herm, hMa, dot_conjTranspose_mulVec, hf1]
    rw [e] at h0
    exact dotProduct_star_self_eq_zero.1 h0

end BlockBand.SourceProcess.CoupledFrames
