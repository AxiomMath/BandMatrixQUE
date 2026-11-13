module

public import BlockBand.SourceProcess.ClosedSum.Main

/-!
# Deterministic bounds on Gram states before the trace stop

* `norm_sourceGram_le`, `norm_nearGram_le`: every entry of `M = VᴴV` and of `B = VᴴPV` (`P` the
  near-port projection) is at most `Re Tr M`; hence `norm_gramEntry_le`.
* `star_gramEntry`: Gram coordinates are Hermitian, `conj G_{(c,a,b)} = G_{(c,b,a)}`.
* `l1` (entrywise `ℓ¹` norm, submultiplicative) and the bounds `norm_gramDriftEntry_le`,
  `norm_gramCovEntry_le` of the model drift and bracket by `l1` of `M, B, 𝖣`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit

variable {ι c : Type*} [Fintype c]

/-- The entrywise `ℓ¹` norm. -/
def l1 (X : Matrix c c ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖

theorem l1_nonneg (X : Matrix c c ℂ) : 0 ≤ l1 X :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

theorem norm_entry_le_l1 (X : Matrix c c ℂ) (a b : c) : ‖X a b‖ ≤ l1 X :=
  (single_le_sum (f := fun b => ‖X a b‖) (fun _ _ => norm_nonneg _) (mem_univ b)).trans
    (single_le_sum (f := fun a => ∑ b, ‖X a b‖) (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _)
      (mem_univ a))

theorem l1_add_le (X Y : Matrix c c ℂ) : l1 (X + Y) ≤ l1 X + l1 Y := by
  unfold l1; rw [← sum_add_distrib]
  exact sum_le_sum fun a _ => by rw [← sum_add_distrib]; exact sum_le_sum fun b _ => norm_add_le _ _

theorem l1_mul_le (X Y : Matrix c c ℂ) : l1 (X * Y) ≤ l1 X * l1 Y := by
  unfold l1
  calc ∑ a, ∑ d, ‖(X * Y) a d‖ ≤ ∑ a, ∑ d, ∑ b, ‖X a b‖ * ‖Y b d‖ :=
        sum_le_sum fun a _ => sum_le_sum fun d _ => by
          rw [mul_apply]; exact (norm_sum_le _ _).trans (sum_le_sum fun b _ => norm_mul_le _ _)
    _ ≤ ∑ a, ∑ b, ∑ b', ∑ d, ‖X a b‖ * ‖Y b' d‖ := by
        refine sum_le_sum fun a _ => ?_
        rw [sum_comm]
        refine sum_le_sum fun b _ => ?_
        exact single_le_sum (f := fun b' => ∑ d, ‖X a b‖ * ‖Y b' d‖)
          (fun _ _ => sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mem_univ b)
    _ = (∑ a, ∑ b, ‖X a b‖) * ∑ b', ∑ d, ‖Y b' d‖ := by
        rw [sum_mul]; refine sum_congr rfl fun a _ => ?_
        rw [sum_mul]; refine sum_congr rfl fun b _ => ?_
        rw [mul_sum]; refine sum_congr rfl fun b' _ => ?_
        rw [mul_sum]

theorem l1_conjTranspose (X : Matrix c c ℂ) : l1 Xᴴ = l1 X := by
  unfold l1; rw [sum_comm]; simp [conjTranspose_apply]

theorem norm_trace_le_l1 (X : Matrix c c ℂ) : ‖X.trace‖ ≤ l1 X := by
  unfold trace l1
  exact (norm_sum_le _ _).trans (sum_le_sum fun a _ =>
    single_le_sum (f := fun b => ‖X a b‖) (fun _ _ => norm_nonneg _) (mem_univ a))

theorem l1_le_of_entry {X : Matrix c c ℂ} {r : ℝ} (h : ∀ a b, ‖X a b‖ ≤ r) :
    l1 X ≤ (Fintype.card c : ℝ) ^ 2 * r := by
  unfold l1
  calc ∑ a, ∑ b, ‖X a b‖ ≤ ∑ _a : c, ∑ _b : c, r := sum_le_sum fun a _ => sum_le_sum fun b _ => h a b
    _ = _ := by simp [sum_const, card_univ]; ring

/-!
## Entries of Gram matrices
-/

theorem norm_mul_le_sum_sq {ι : Type*} (V : Matrix ι c ℂ) (x : ι) (a b : c) :
    ‖V x a‖ * ‖V x b‖ ≤ ∑ d, ‖V x d‖ ^ 2 := by
  have ha := single_le_sum (f := fun d => ‖V x d‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ a)
  have hb := single_le_sum (f := fun d => ‖V x d‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ b)
  nlinarith [sq_nonneg (‖V x a‖ - ‖V x b‖)]

theorem re_trace_sourceGram [Fintype ι] (V : Matrix ι c ℂ) :
    ((sourceGram V).trace).re = ∑ x, ∑ d, ‖V x d‖ ^ 2 := by
  simp only [sourceGram, Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun d _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast

theorem norm_sourceGram_le [Fintype ι] (V : Matrix ι c ℂ) (a b : c) :
    ‖sourceGram V a b‖ ≤ ((sourceGram V).trace).re := by
  rw [re_trace_sourceGram]
  simp only [sourceGram, mul_apply, conjTranspose_apply]
  refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
  rw [norm_mul, norm_star]; exact norm_mul_le_sum_sq V x a b

theorem norm_nearGram_le [Fintype ι] [DecidableEq ι] (V : Matrix ι c ℂ) (w : ι → ℂ)
    (hw : ∀ x, ‖w x‖ ≤ 1) (a b : c) :
    ‖nearGram (diagonal w) V a b‖ ≤ ((sourceGram V).trace).re := by
  rw [re_trace_sourceGram, nearGram, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply]
  refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have := norm_mul_le_sum_sq V x a b
  have h0 : 0 ≤ ‖V x a‖ := norm_nonneg _
  nlinarith [hw x, norm_nonneg (w x), norm_nonneg (V x b), mul_nonneg h0 (norm_nonneg (V x b))]

/-- A Gram pair at a diagonal contraction has all coordinates bounded by `Re Tr M`. -/
theorem norm_gramEntry_le [Fintype ι] [DecidableEq ι] (V : Matrix ι c ℂ) (w : ι → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (e : Fin 2 × c × c) :
    ‖gramEntry e (gramPair (diagonal w) V)‖ ≤ ((gramPair (diagonal w) V).1.trace).re := by
  unfold gramEntry gramPair
  split_ifs
  · exact norm_sourceGram_le V _ _
  · exact norm_nearGram_le V w hw _ _

theorem norm_nearPortProj_entry_le (W : ℕ) (x : Fin 2 × Fin W) :
    ‖(fun z : Fin 2 × Fin W => if z.1 = 0 then (1 : ℂ) else 0) x‖ ≤ 1 := by
  dsimp only; split_ifs <;> simp

/-- The transposed Gram coordinate. -/
def swapE (e : Fin 2 × c × c) : Fin 2 × c × c := (e.1, e.2.2, e.2.1)

omit [Fintype c] in
theorem star_gramEntry [Fintype ι] (P : Matrix ι ι ℂ) (hP : Pᴴ = P) (V : Matrix ι c ℂ)
    (e : Fin 2 × c × c) :
    star (gramEntry e (gramPair P V)) = gramEntry (swapE e) (gramPair P V) := by
  have h1 : (sourceGram V)ᴴ = sourceGram V := by
    simp [sourceGram, conjTranspose_mul]
  have h2 : (nearGram P V)ᴴ = nearGram P V := by
    simp [nearGram, conjTranspose_mul, hP, Matrix.mul_assoc]
  unfold gramEntry gramPair swapE
  split_ifs
  · change star (sourceGram V e.2.1 e.2.2) = sourceGram V e.2.2 e.2.1
    conv_rhs => rw [← h1]
    rw [conjTranspose_apply]
  · change star (nearGram P V e.2.1 e.2.2) = nearGram P V e.2.2 e.2.1
    conv_rhs => rw [← h2]
    rw [conjTranspose_apply]

/-!
## The model drift and bracket
-/

/-- The common bound of `C₀, C₁ᴴ, C₁, C₂`. -/
def cBound (M B D : Matrix c c ℂ) : ℝ := l1 B + l1 M * l1 D * (l1 M + l1 B)

theorem l1_gramC0_le (M B D : Matrix c c ℂ) : l1 (gramC0 M B D) ≤ cBound M B D := by
  unfold gramC0 cBound
  refine (l1_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (l1_mul_le _ _).trans ?_
  have := l1_mul_le M D
  nlinarith [l1_nonneg M, l1_nonneg B, l1_nonneg D, l1_nonneg (M * D)]

theorem l1_gramC1_le (M B D : Matrix c c ℂ) : l1 (gramC1 M B D) ≤ cBound M B D := by
  unfold gramC1 cBound
  refine (l1_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (l1_mul_le _ _).trans ?_
  have := l1_mul_le M D
  nlinarith [l1_nonneg M, l1_nonneg B, l1_nonneg D, l1_nonneg (M * D)]

theorem l1_gramC2_le (M B D : Matrix c c ℂ) (hBM : l1 B ≤ l1 M) :
    l1 (gramC2 B D) ≤ cBound M B D := by
  unfold gramC2 cBound
  refine (l1_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (l1_mul_le _ _).trans ?_
  have := l1_mul_le B D
  nlinarith [l1_nonneg M, l1_nonneg B, l1_nonneg D, l1_nonneg (B * D),
    mul_le_mul_of_nonneg_right hBM (l1_nonneg D)]

theorem norm_crossedBracket_le (D0 : ℝ) (B Cl Cr : Matrix c c ℂ) (Q : ℝ) (hl : l1 Cl ≤ Q)
    (hr : l1 Cr ≤ Q) (i j k l : c) :
    ‖crossedBracket D0 B Cl Cr i j k l‖ ≤ |D0| * l1 B * Q := by
  unfold crossedBracket
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
  have h1 := norm_add_le (B i l * Cl k j) (Cr i l * B k j)
  rw [norm_mul, norm_mul] at h1
  have hB1 := norm_entry_le_l1 B i l
  have hB2 := norm_entry_le_l1 B k j
  have hC1 := (norm_entry_le_l1 Cl k j).trans hl
  have hC2 := (norm_entry_le_l1 Cr i l).trans hr
  have h2 : ‖B i l‖ * ‖Cl k j‖ + ‖Cr i l‖ * ‖B k j‖ ≤ 2 * (l1 B * Q) := by
    nlinarith [norm_nonneg (B i l), norm_nonneg (Cl k j), norm_nonneg (Cr i l),
      norm_nonneg (B k j), l1_nonneg B]
  have := abs_nonneg D0
  nlinarith

/-- **The model bracket is bounded by `l1` of the Gram state** (when `l1 B ≤ l1 M`). -/
theorem norm_gramCovEntry_le (D0 : ℝ) (D : Matrix c c ℂ) (e e' : Fin 2 × c × c)
    (G : GramState c) (hBM : l1 G.2 ≤ l1 G.1) :
    ‖gramCovEntry D0 D e e' G‖ ≤ |D0| * l1 G.2 * cBound G.1 G.2 D := by
  have h0 := l1_gramC0_le G.1 G.2 D
  have h1 := l1_gramC1_le G.1 G.2 D
  have h1' : l1 (gramC1 G.1 G.2 D)ᴴ ≤ cBound G.1 G.2 D := by rwa [l1_conjTranspose]
  have h2 := l1_gramC2_le G.1 G.2 D hBM
  unfold gramCovEntry
  rcases e with ⟨e1, e2⟩; rcases e' with ⟨f1, f2⟩
  fin_cases e1 <;> fin_cases f1 <;> exact norm_crossedBracket_le _ _ _ _ _ (by assumption)
    (by assumption) _ _ _ _

/-- **The model drift is bounded by `l1` of the Gram state.** -/
theorem norm_gramDriftEntry_le (D0 : ℝ) (D : Matrix c c ℂ) (e : Fin 2 × c × c)
    (G : GramState c) :
    ‖gramDriftEntry D0 D e G‖ ≤ |D0| * (l1 D * l1 G.1) ^ 2 * l1 G.2 := by
  unfold gramDriftEntry
  split_ifs
  · rw [norm_zero]; have := l1_nonneg G.2; positivity
  · rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    have hs : ‖gramScalar D G.1‖ ≤ (l1 D * l1 G.1) ^ 2 / 2 := by
      unfold gramScalar
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
      have := (norm_trace_le_l1 _).trans (l1_mul_le (D * G.1 * D) G.1)
      have h3 := l1_mul_le (D * G.1) D
      have h4 := l1_mul_le D G.1
      have := l1_nonneg G.1; have := l1_nonneg D
      have := l1_nonneg (D * G.1); have := l1_nonneg (D * G.1 * D)
      nlinarith
    have hb := norm_entry_le_l1 G.2 e.2.1 e.2.2
    have := abs_nonneg D0
    have := norm_nonneg (gramScalar D G.1)
    have := norm_nonneg (G.2 e.2.1 e.2.2)
    have h5 := mul_le_mul hs hb (norm_nonneg _) (by positivity : 0 ≤ (l1 D * l1 G.1) ^ 2 / 2)
    have h7 : 0 ≤ |D0| * ((l1 D * l1 G.1) ^ 2 / 2 * l1 G.2) :=
      mul_nonneg (abs_nonneg D0) (mul_nonneg (by positivity) (l1_nonneg _))
    calc |D0| / 2 * ‖gramScalar D G.1‖ * ‖G.2 e.2.1 e.2.2‖
        = |D0| * (‖gramScalar D G.1‖ * ‖G.2 e.2.1 e.2.2‖) / 2 := by ring
      _ ≤ |D0| * ((l1 D * l1 G.1) ^ 2 / 2 * l1 G.2) / 2 := by gcongr
      _ ≤ _ := by nlinarith

/-- **Bracket bound at a level `ρ`**: `l1 M, l1 B ≤ ρ`. -/
theorem norm_gramCovEntry_le_rho (D0 : ℝ) (D : Matrix c c ℂ) (e e' : Fin 2 × c × c)
    (G : GramState c) {ρ : ℝ} (hM : l1 G.1 ≤ ρ) (hB : l1 G.2 ≤ ρ) :
    ‖gramCovEntry D0 D e e' G‖ ≤ |D0| * ρ * (ρ + ρ * l1 D * ρ) := by
  have hρ : 0 ≤ ρ := (l1_nonneg _).trans hM
  have hD := l1_nonneg D
  have key : ∀ X Y : Matrix c c ℂ, l1 X ≤ ρ → l1 Y ≤ ρ → l1 (G.2 + X * D * Y) ≤
      ρ + ρ * l1 D * ρ := fun X Y hX hY => by
    refine (l1_add_le _ _).trans (add_le_add hB ((l1_mul_le _ _).trans ?_))
    have h1 := (l1_mul_le X D).trans (mul_le_mul_of_nonneg_right hX hD)
    exact mul_le_mul h1 hY (l1_nonneg _) (mul_nonneg hρ hD)
  have h0 : l1 (gramC0 G.1 G.2 D) ≤ ρ + ρ * l1 D * ρ := key _ _ hM hM
  have h1 : l1 (gramC1 G.1 G.2 D) ≤ ρ + ρ * l1 D * ρ := key _ _ hM hB
  have h1' : l1 (gramC1 G.1 G.2 D)ᴴ ≤ ρ + ρ * l1 D * ρ := by rwa [l1_conjTranspose]
  have h2 : l1 (gramC2 G.2 D) ≤ ρ + ρ * l1 D * ρ := key _ _ hB hB
  have hcb : ∀ Cl Cr : Matrix c c ℂ, l1 Cl ≤ ρ + ρ * l1 D * ρ → l1 Cr ≤ ρ + ρ * l1 D * ρ →
      ∀ i j k l, ‖crossedBracket D0 G.2 Cl Cr i j k l‖ ≤ |D0| * ρ * (ρ + ρ * l1 D * ρ) :=
    fun Cl Cr hl hr i j k l => (norm_crossedBracket_le D0 G.2 Cl Cr _ hl hr i j k l).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
        (by positivity))
  unfold gramCovEntry
  rcases e with ⟨e1, e2⟩; rcases e' with ⟨f1, f2⟩
  fin_cases e1 <;> fin_cases f1 <;> exact hcb _ _ (by assumption) (by assumption) _ _ _ _

/-- **Drift bound at a level `ρ`.** -/
theorem norm_gramDriftEntry_le_rho (D0 : ℝ) (D : Matrix c c ℂ) (e : Fin 2 × c × c)
    (G : GramState c) {ρ : ℝ} (hM : l1 G.1 ≤ ρ) (hB : l1 G.2 ≤ ρ) :
    ‖gramDriftEntry D0 D e G‖ ≤ |D0| * (l1 D * ρ) ^ 2 * ρ := by
  refine (norm_gramDriftEntry_le D0 D e G).trans ?_
  have h1 : l1 D * l1 G.1 ≤ l1 D * ρ := mul_le_mul_of_nonneg_left hM (l1_nonneg D)
  have h2 : (l1 D * l1 G.1) ^ 2 ≤ (l1 D * ρ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (l1_nonneg _) (l1_nonneg _)) h1 2
  have := abs_nonneg D0
  exact mul_le_mul (mul_le_mul_of_nonneg_left h2 this) hB (l1_nonneg _) (by positivity)

end BlockBand.SourceProcess.ClosedSumProof
