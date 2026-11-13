module

public import BlockBand.SourceProcess.CoupledFrames.JointSel

/-!
# The two-frame selection: specification and existence

* `jointSpec_of`: `jointG H prev a = 0` and `aᴴ jointQ a = v` give `Y₂ a₂ = w`, `P w = w`,
  `(Y_jᴴ w)_k = 0` for current `k`, `⟨Y_j prev_lᴶ, w⟩ = 0` and `‖w‖² = v` (`JointSpec`).
* `jointExists` (proved in the sibling module): if `rank(P Y_j) ≥ rank P` and `2 #cur + 2n + 2|ι| < 3 rank P`, some `a` has
  `jointG H prev a = 0` and `jointQ H a ≠ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open scoped ComplexOrder

variable {c' : Type*} [Fintype c'] [DecidableEq c'] {n : ℕ} (cur : c' → Prop) [DecidablePred cur]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The frame-level specification of a shared birth vector `a` (new column `Y₁ a₁`). -/
def JointSpec (P : Matrix ι ι ℂ) (Y₁ Y₂ : Matrix ι c' ℂ) (prev : Fin n → c' ⊕ c' → ℂ) (v : ℝ)
    (a : c' ⊕ c' → ℂ) : Prop :=
  Y₂ *ᵥ sndV a = Y₁ *ᵥ fstV a ∧ P *ᵥ (Y₁ *ᵥ fstV a) = Y₁ *ᵥ fstV a ∧
    (∀ k, cur k → (Y₁ᴴ *ᵥ (Y₁ *ᵥ fstV a)) k = 0 ∧ (Y₂ᴴ *ᵥ (Y₁ *ᵥ fstV a)) k = 0) ∧
    (∀ l, star (Y₁ *ᵥ fstV (prev l)) ⬝ᵥ (Y₁ *ᵥ fstV a) = 0 ∧
      star (Y₂ *ᵥ sndV (prev l)) ⬝ᵥ (Y₁ *ᵥ fstV a) = 0) ∧
    star (Y₁ *ᵥ fstV a) ⬝ᵥ (Y₁ *ᵥ fstV a) = (v : ℂ)

omit [Fintype ι] [DecidableEq ι] in
theorem gram_dot {κ : Type*} [Fintype ι] (V : Matrix ι κ ℂ) [Fintype κ] (u x : κ → ℂ) :
    star u ⬝ᵥ ((Vᴴ * V) *ᵥ x) = star (V *ᵥ u) ⬝ᵥ (V *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

omit [DecidableEq ι] in
theorem eq_zero_of_dot_proj {Q : Matrix ι ι ℂ} (hQh : Qᴴ = Q) (hQQ : Q * Q = Q) {y : ι → ℂ}
    (h : star y ⬝ᵥ (Q *ᵥ y) = 0) : Q *ᵥ y = 0 := by
  have e : star y ⬝ᵥ (Q *ᵥ y) = star (Q *ᵥ y) ⬝ᵥ (Q *ᵥ y) := by
    conv_lhs => rw [← hQQ, ← mulVec_mulVec]
    rw [dotProduct_mulVec, star_mulVec, hQh]
  rw [e] at h
  exact dotProduct_star_self_eq_zero.1 h

omit [DecidableEq ι] in
theorem dot_conjTranspose_mulVec {κ : Type*} [Fintype κ] (V : Matrix ι κ ℂ) (x : κ → ℂ)
    (y : ι → ℂ) : star x ⬝ᵥ (Vᴴ *ᵥ y) = star (V *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, star_mulVec]

omit [Fintype c'] [DecidableEq c'] [DecidableEq ι] in
theorem fromCols_conjTranspose_mulVec (Y₁ Y₂ : Matrix ι c' ℂ) (w : ι → ℂ) (k : c') :
    ((fromCols Y₁ Y₂)ᴴ *ᵥ w) (Sum.inl k) = (Y₁ᴴ *ᵥ w) k ∧
      ((fromCols Y₁ Y₂)ᴴ *ᵥ w) (Sum.inr k) = (Y₂ᴴ *ᵥ w) k := by
  constructor <;> simp [mulVec, dotProduct, fromCols, conjTranspose_apply]

variable {cur}

theorem jointSpec_of {P : Matrix ι ι ℂ} (hPh : Pᴴ = P) (hPP : P * P = P) {Y₁ Y₂ : Matrix ι c' ℂ}
    {prev : Fin n → c' ⊕ c' → ℂ} {v : ℝ} {a : c' ⊕ c' → ℂ}
    (hG : jointG cur (gramPair P (fromCols Y₁ Y₂)) prev *ᵥ a = 0)
    (hQ : star a ⬝ᵥ (jointQ (gramPair P (fromCols Y₁ Y₂)) *ᵥ a) = (v : ℂ)) :
    JointSpec cur P Y₁ Y₂ prev v a := by
  set V := fromCols Y₁ Y₂
  obtain ⟨h1, h2⟩ := fromCols_mulVec_projF Y₁ Y₂ a
  have hM : (gramPair P V).1 = Vᴴ * V := rfl
  have hMB : (gramPair P V).1 - (gramPair P V).2 = Vᴴ * ((1 - P) * V) := by
    simp only [gramPair, sourceGram, nearGram, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc]
  have row : ∀ (A : Matrix (c' ⊕ c') (c' ⊕ c') ℂ) (f : (c' ⊕ c') → _),
      (∀ z, (jointG cur (gramPair P V) prev *ᵥ a) (f z) = (A *ᵥ a) z) → A *ᵥ a = 0 :=
    fun A f hf => funext fun z => by rw [← hf z, hG]; rfl
  have b1 := row ((gramPair P V).1 * (projF 0 - projF 1)) Sum.inl fun z => rfl
  have b2 := row (((gramPair P V).1 - (gramPair P V).2) * projF 0)
    (fun z => Sum.inr (Sum.inl z)) fun z => rfl
  have b3 := row (curMat cur * (gramPair P V).1 * projF 0)
    (fun z => Sum.inr (Sum.inr (Sum.inl z))) fun z => rfl
  have b4 : ∀ l j, star (projF j *ᵥ prev l) ⬝ᵥ ((gramPair P V).1 *ᵥ (projF 0 *ᵥ a)) = 0 :=
    fun l j => by
      have := congrFun hG (Sum.inr (Sum.inr (Sum.inr (l, j))))
      rw [mulVec_mulVec, dotProduct_mulVec]
      exact this
  rw [← mulVec_mulVec, sub_mulVec] at b1
  rw [← mulVec_mulVec] at b2
  -- `Y₁ a₁ = Y₂ a₂`
  have hd : V *ᵥ (projF 0 *ᵥ a - projF 1 *ᵥ a) = 0 := by
    have := congrArg (fun y => star (projF 0 *ᵥ a - projF 1 *ᵥ a) ⬝ᵥ y) b1
    simp only [dotProduct_zero] at this
    rw [hM, gram_dot] at this
    exact dotProduct_star_self_eq_zero.1 this
  rw [mulVec_sub, h1, h2, sub_eq_zero] at hd
  -- `w` is near
  have hnear : (1 - P) *ᵥ (Y₁ *ᵥ fstV a) = 0 := by
    have h1P : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hPh]
    have h1PP : (1 - P) * (1 - P) = 1 - P := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hPP, sub_self, sub_zero]
    refine eq_zero_of_dot_proj h1P h1PP ?_
    have := congrArg (fun y => star (projF 0 *ᵥ a) ⬝ᵥ y) b2
    simp only [dotProduct_zero] at this
    rw [hMB, ← mulVec_mulVec, ← mulVec_mulVec, dot_conjTranspose_mulVec, h1] at this
    exact this
  have hw : P *ᵥ (Y₁ *ᵥ fstV a) = Y₁ *ᵥ fstV a := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hnear
    exact hnear.symm
  refine ⟨hd.symm, hw, fun k hk => ?_, fun l => ?_, ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hM, ← mulVec_mulVec, h1] at b3
    have e1 := congrFun b3 (Sum.inl k)
    have e2 := congrFun b3 (Sum.inr k)
    simp only [curMat, mulVec_diagonal, hk, ↓reduceIte, one_mul, Pi.zero_apply] at e1 e2
    rw [(fromCols_conjTranspose_mulVec Y₁ Y₂ _ k).1] at e1
    rw [(fromCols_conjTranspose_mulVec Y₁ Y₂ _ k).2] at e2
    exact ⟨e1, e2⟩
  · have e1 := b4 l 0
    have e2 := b4 l 1
    rw [hM, gram_dot, h1] at e1 e2
    obtain ⟨p1, p2⟩ := fromCols_mulVec_projF Y₁ Y₂ (prev l)
    rw [p1] at e1
    rw [p2] at e2
    exact ⟨e1, e2⟩
  · have e : star a ⬝ᵥ (jointQ (gramPair P V) *ᵥ a) =
        star (projF 0 *ᵥ a) ⬝ᵥ ((gramPair P V).1 *ᵥ (projF 0 *ᵥ a)) := by
      rw [jointQ, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
      congr 1
      rw [star_mulVec, projF_herm]
    rw [e, hM, gram_dot, h1] at hQ
    exact hQ

end BlockBand.SourceProcess.CoupledFrames
