module

public import BlockBand.Transmission.PassiveCovariance.SdSelf

/-!
# Derivative factors are dressed words; the block form of the crossed contraction

* `leftL`, `rightL`: `wLeft k = wLetter (leftL k)`, `wRight k = wLetter (rightL k)`.
* `wordAlpha_word`, `wordGamma_word`: every derivative factor `α_j`, `γ_j` of a dressed word is
  itself a dressed word (length `≤ ℓ`, insertions among those of the word and `1`), for every `G`.
* `preD`: `wordVal wd (preD P D) = P * wordVal wd D`; `letter_mul_wordVal`.
* `blkOf`, `bProj` (block projectors), `bVar` (block variances): `siteVar_eq_bVar`.
* **`crossed_pt`**: the crossed contraction of `sd_expand` against `DQ` for `Q = u*w₂v` is
  `-Σ_k Σ_{p,p'} s_{pp'} (x̌*P_pγ'_kv)(u*α'_kP_{p'}Mc)` (the block form, `s_{pp'} = bVar`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal Matrix.Norms.L2Operator

section Generic
variable {n : Type} [Fintype n] [DecidableEq n]

/-- The letter of `wLeft k`. -/
def leftL (k : Fin 4) : Fin 4 := ![0, 1, 2, 2] k

/-- The letter of `wRight k`. -/
def rightL (k : Fin 4) : Fin 4 := ![0, 0, 2, 3] k

omit [DecidableEq n] in
theorem wLeft_eq (Kh G : Matrix n n ℂ) (k : Fin 4) : wLeft Kh G k = wLetter Kh G (leftL k) := by
  fin_cases k <;> rfl

omit [DecidableEq n] in
theorem wRight_eq (Kh G : Matrix n n ℂ) (k : Fin 4) : wRight Kh G k = wLetter Kh G (rightL k) := by
  fin_cases k <;> rfl

theorem wordVal_cons (Kh G P : Matrix n n ℂ) {ℓ : ℕ} (k : Fin 4) (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → Matrix n n ℂ) :
    wordVal Kh G (Fin.cons k wd : Fin (ℓ + 1) → Fin 4) (Fin.cons P D : Fin (ℓ + 2) → Matrix n n ℂ) =
      P * wLetter Kh G k * wordVal Kh G wd D := by
  rw [wordVal_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem letter_mul_wordVal (Kh G : Matrix n n ℂ) {ℓ : ℕ} (k : Fin 4) (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → Matrix n n ℂ) :
    wLetter Kh G k * wordVal Kh G wd D =
      wordVal Kh G (Fin.cons k wd : Fin (ℓ + 1) → Fin 4) (Fin.cons 1 D : Fin (ℓ + 2) → Matrix n n ℂ) := by
  rw [wordVal_cons, Matrix.one_mul]

/-- Pre-multiply the first insertion. -/
def preD {ℓ : ℕ} (P : Matrix n n ℂ) (D : Fin (ℓ + 1) → Matrix n n ℂ) : Fin (ℓ + 1) → Matrix n n ℂ :=
  Fin.cons (P * D 0) (Fin.tail D)

theorem wordVal_preD (Kh G P : Matrix n n ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → Matrix n n ℂ) : wordVal Kh G wd (preD P D) = P * wordVal Kh G wd D := by
  simp only [wordVal, preD, Fin.cons_zero, Fin.cons_succ, Fin.tail, Matrix.mul_assoc]

theorem norm_preD_le {P : Matrix n n ℂ} (hP : ‖P‖ ≤ 1) {Kd : ℝ} {ℓ : ℕ}
    {D : Fin (ℓ + 1) → Matrix n n ℂ} (hD : ∀ i, ‖D i‖ ≤ Kd) : ∀ i, ‖preD P D i‖ ≤ Kd := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [preD, Fin.cons_zero]
    calc ‖P * D 0‖ ≤ ‖P‖ * ‖D 0‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * Kd := mul_le_mul hP (hD 0) (norm_nonneg _) zero_le_one
      _ = Kd := one_mul _
  · simp only [preD, Fin.cons_succ, Fin.tail]; exact hD _

/-- Insertions drawn from `D` and `1`. -/
def FromIns {ℓ ℓ' : ℕ} (D : Fin (ℓ + 1) → Matrix n n ℂ) (D' : Fin (ℓ' + 1) → Matrix n n ℂ) : Prop :=
  ∀ i, D' i = 1 ∨ ∃ k, D' i = D k

theorem FromIns.norm_le {ℓ ℓ' : ℕ} {D : Fin (ℓ + 1) → Matrix n n ℂ} {D' : Fin (ℓ' + 1) → Matrix n n ℂ}
    (h : FromIns D D') {Kd : ℝ} (hK : 1 ≤ Kd) (hD : ∀ i, ‖D i‖ ≤ Kd) : ∀ i, ‖D' i‖ ≤ Kd := by
  intro i
  rcases h i with h | ⟨k, h⟩
  · rw [h]; exact norm_one_matrix_le.trans hK
  · rw [h]; exact hD k

/-- **`α_j` is a dressed word.** -/
theorem wordAlpha_word (Kh : Matrix n n ℂ) :
    ∀ (ℓ : ℕ) (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ) (j : Fin ℓ),
      ∃ (ℓ' : ℕ) (wd' : Fin ℓ' → Fin 4) (D' : Fin (ℓ' + 1) → Matrix n n ℂ), ℓ' ≤ ℓ ∧
        FromIns D D' ∧ ∀ G, wordAlpha Kh G ℓ wd D j = wordVal Kh G wd' D' := by
  intro ℓ
  induction ℓ with
  | zero => intro _ _ j; exact j.elim0
  | succ ℓ ih =>
    intro wd D j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨1, ![leftL (wd 0)], ![D 0, 1], by omega, fun i => ?_, fun G => ?_⟩
      · fin_cases i
        · exact Or.inr ⟨0, rfl⟩
        · exact Or.inl rfl
      · simp only [wordAlpha, Fin.cons_zero]
        rw [wordVal_succ, wordVal_zero, wLeft_eq]
        simp
    · obtain ⟨ℓ', wd', D', hl, hD', hG⟩ := ih (fun j => wd j.succ) (fun j => D j.succ) j
      refine ⟨ℓ' + 1, Fin.cons (wd 0) wd', Fin.cons (D 0) D', by omega, fun i => ?_, fun G => ?_⟩
      · refine Fin.cases (Or.inr ⟨0, rfl⟩) (fun i => ?_) i
        simp only [Fin.cons_succ]
        rcases hD' i with h | ⟨k, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨k.succ, h⟩
      · simp only [wordAlpha, Fin.cons_succ]
        rw [hG, wordVal_cons]

/-- **`γ_j` is a dressed word.** -/
theorem wordGamma_word (Kh : Matrix n n ℂ) :
    ∀ (ℓ : ℕ) (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ) (j : Fin ℓ),
      ∃ (ℓ' : ℕ) (wd' : Fin ℓ' → Fin 4) (D' : Fin (ℓ' + 1) → Matrix n n ℂ), ℓ' ≤ ℓ ∧
        FromIns D D' ∧ ∀ G, wordGamma Kh G ℓ wd D j = wordVal Kh G wd' D' := by
  intro ℓ
  induction ℓ with
  | zero => intro _ _ j; exact j.elim0
  | succ ℓ ih =>
    intro wd D j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨ℓ + 1, Fin.cons (rightL (wd 0)) (fun j => wd j.succ), Fin.cons 1 (fun j => D j.succ),
        le_rfl, fun i => ?_, fun G => ?_⟩
      · refine Fin.cases (Or.inl rfl) (fun i => Or.inr ⟨i.succ, ?_⟩) i
        simp only [Fin.cons_succ]
      · simp only [wordGamma, Fin.cons_zero]
        rw [wordVal_cons, Matrix.one_mul, wRight_eq]
    · obtain ⟨ℓ', wd', D', hl, hD', hG⟩ := ih (fun j => wd j.succ) (fun j => D j.succ) j
      refine ⟨ℓ', wd', D', by omega, fun i => ?_, fun G => ?_⟩
      · rcases hD' i with h | ⟨k, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨k.succ, h⟩
      · simp only [wordGamma, Fin.cons_succ]
        exact hG G

end Generic

section Blocks
variable {W : ℕ}

/-- The block of a layer site: `0` physical, `1` port. -/
def blkOf : LayerSite W .oneBlockOnePort → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The indicator of block `p`. -/
def bInd (p : Fin 2) (α : LayerSite W .oneBlockOnePort) : ℂ := if blkOf α = p then 1 else 0

/-- The block projector `P_p`. -/
def bProj (p : Fin 2) : LayerMat W := diagonal (bInd p)

/-- The block variances `s_{pp'}`: `σ(α,γ) = s_{blk α, blk γ}`. -/
def bVar (W : ℕ) (b : ℝ) (p p' : Fin 2) : ℂ :=
  if p = 0 then (if p' = 0 then (gueVar W b : ℂ) else (ginVar W b : ℂ))
  else (if p' = 0 then (ginVar W b : ℂ) else 0)

theorem siteVar_eq_bVar (b : ℝ) (α γ : LayerSite W .oneBlockOnePort) :
    siteVar W b α γ = bVar W b (blkOf α) (blkOf γ) := by
  rcases α with α | α <;> rcases γ with γ | γ <;> rfl

theorem norm_bVar_le (b : ℝ) (hb0 : 0 ≤ b) (hb : b < 1 / 2) (p p' : Fin 2) :
    ‖bVar W b p p'‖ ≤ 1 / W := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hg : ‖((gueVar W b : ℝ≥0) : ℂ)‖ ≤ 1 / W := by
    rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    simp only [gueVar, Real.coe_toNNReal']
    exact max_le (div_le_div_of_nonneg_right (by linarith) hW) (by positivity)
  have hn : ‖((ginVar W b : ℝ≥0) : ℂ)‖ ≤ 1 / W := by
    rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    simp only [ginVar, Real.coe_toNNReal']
    exact max_le (div_le_div_of_nonneg_right (by linarith) hW) (by positivity)
  unfold bVar
  split_ifs
  · exact hg
  · exact hn
  · exact hn
  · simp only [norm_zero]; positivity

theorem norm_bProj_le (p : Fin 2) : ‖(bProj p : LayerMat W)‖ ≤ 1 :=
  norm_diagonal_le _ zero_le_one fun α => by unfold bInd; split_ifs <;> simp

theorem sum_bVar_bInd (b : ℝ) (α γ : LayerSite W .oneBlockOnePort) :
    ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' * bInd p α * bInd p' γ = siteVar W b α γ := by
  rw [siteVar_eq_bVar]
  rcases α with α | α <;> rcases γ with γ | γ <;>
    simp [bInd, blkOf, Fin.sum_univ_two]

theorem form_bProj_left (p : Fin 2) (xc v : LayerSite W .oneBlockOnePort → ℂ) (Γ : LayerMat W) :
    star xc ⬝ᵥ ((bProj p * Γ) *ᵥ v) = ∑ α, bInd p α * (star (xc α) * (Γ *ᵥ v) α) := by
  rw [← mulVec_mulVec, bProj, dotProduct]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mulVec_diagonal, Pi.star_apply]; ring

theorem form_bProj_mid (p : Fin 2) (u c : LayerSite W .oneBlockOnePort → ℂ) (A M : LayerMat W) :
    star u ⬝ᵥ ((A * bProj p * M) *ᵥ c) = ∑ γ, bInd p γ * ((star u ᵥ* A) γ * (M *ᵥ c) γ) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, bProj, dotProduct]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [mulVec_diagonal]; ring

theorem form_single (u v : LayerSite W .oneBlockOnePort → ℂ) (A Γ : LayerMat W)
    (γ α : LayerSite W .oneBlockOnePort) :
    star u ⬝ᵥ ((A * Matrix.single γ α (1 : ℂ) * Γ) *ᵥ v) = (star u ᵥ* A) γ * (Γ *ᵥ v) α := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, single_mulVec, one_mul,
    ← Pi.single, dotProduct_single]

/-- Block separation of a site-variance double sum. -/
theorem block_sum (b : ℝ) (f g : LayerSite W .oneBlockOnePort → ℂ) :
    ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' * ((∑ α, bInd p α * f α) * (∑ γ, bInd p' γ * g γ)) =
      ∑ α, ∑ γ, siteVar W b α γ * (f α * g γ) := by
  simp_rw [← sum_bVar_bInd b, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun p' _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  refine (Finset.sum_congr rfl fun p' _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
  ring

/-- **Block form of the crossed contraction.** -/
theorem crossed_pt (b : ℝ) (xc u v c : LayerSite W .oneBlockOnePort → ℂ) (M : LayerMat W) {ℓ : ℕ}
    (A Γ : Fin ℓ → LayerMat W) :
    ∑ α, ∑ γ, siteVar W b α γ * (star (xc α) * (M *ᵥ c) γ *
        -∑ k, star u ⬝ᵥ ((A k * Matrix.single γ α (1 : ℂ) * Γ k) *ᵥ v)) =
      -∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
        ((star xc ⬝ᵥ ((bProj p * Γ k) *ᵥ v)) * (star u ⬝ᵥ ((A k * bProj p' * M) *ᵥ c))) := by
  have e : ∀ (k : Fin ℓ) (α γ : LayerSite W .oneBlockOnePort),
      star u ⬝ᵥ ((A k * Matrix.single γ α (1 : ℂ) * Γ k) *ᵥ v) = (star u ᵥ* A k) γ * (Γ k *ᵥ v) α :=
    fun k α γ => form_single u v (A k) (Γ k) γ α
  simp only [e]
  have e2 : ∀ k p, star xc ⬝ᵥ ((bProj p * Γ k) *ᵥ v) = _ := fun k p => form_bProj_left p xc v (Γ k)
  have e3 : ∀ k p', star u ⬝ᵥ ((A k * bProj p' * M) *ᵥ c) = _ :=
    fun k p' => form_bProj_mid p' u c (A k) M
  have e4 : ∀ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
      ((∑ α, bInd p α * (star (xc α) * (Γ k *ᵥ v) α)) *
        (∑ γ, bInd p' γ * ((star u ᵥ* A k) γ * (M *ᵥ c) γ))) = _ := fun k => block_sum b _ _
  simp only [e2, e3]
  simp only [e4]
  simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_inj]
  refine ((Finset.sum_congr rfl fun α _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun γ _ => ?_
  ring

end Blocks

end BlockBand.Transmission.PassiveCovariance
