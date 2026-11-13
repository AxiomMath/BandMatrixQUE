module

public import BlockBand.Transmission.PassiveCovariance.WordReplica

/-!
# Derivative factors of dressed words are dressed words

The factors `α_j, γ_j` in the derivative of a dressed word `w(G)`, and the product `G·w(G)`, are
again dressed words of a fixed shape, with controlled length and insertion norms.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open Matrix
open BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `wLeft = wLetter ∘ leftIdx`. -/
def leftIdx (k : Fin 4) : Fin 4 := ![0, 1, 2, 2] k

/-- `wRight = wLetter ∘ rightIdx`. -/
def rightIdx (k : Fin 4) : Fin 4 := ![0, 0, 2, 3] k

omit [DecidableEq n] in
theorem wLeft_eq (Kh G : Matrix n n ℂ) (k : Fin 4) : wLeft Kh G k = wLetter Kh G (leftIdx k) := by
  fin_cases k <;> rfl

omit [DecidableEq n] in
theorem wRight_eq (Kh G : Matrix n n ℂ) (k : Fin 4) : wRight Kh G k = wLetter Kh G (rightIdx k) := by
  fin_cases k <;> rfl

/-- A dressed word "shape": letters and insertions (independent of `G`). -/
structure WordShape (n : Type) [Fintype n] [DecidableEq n] (Lw : ℕ) (Kd : ℝ) where
  len : ℕ
  hlen : len ≤ Lw
  wd : Fin len → Fin 4
  D : Fin (len + 1) → Matrix n n ℂ
  hD : ∀ j, ‖D j‖ ≤ Kd

theorem wordVal_cons (Kh G : Matrix n n ℂ) {ℓ : ℕ} (k : Fin 4) (wd : Fin ℓ → Fin 4)
    (D₀ : Matrix n n ℂ) (D : Fin (ℓ + 1) → Matrix n n ℂ) :
    wordVal Kh G (Fin.cons k wd : Fin (ℓ + 1) → Fin 4) (Fin.cons D₀ D) =
      D₀ * wLetter Kh G k * wordVal Kh G wd D := by
  rw [wordVal_succ]; rfl

theorem norm_cons_le {ℓ : ℕ} {Kd : ℝ} (D₀ : Matrix n n ℂ) (D : Fin (ℓ + 1) → Matrix n n ℂ)
    (h₀ : ‖D₀‖ ≤ Kd) (hD : ∀ j, ‖D j‖ ≤ Kd) :
    ∀ j, ‖(Fin.cons D₀ D : Fin (ℓ + 2) → Matrix n n ℂ) j‖ ≤ Kd := fun j =>
  Fin.cases (by simpa using h₀) (fun j => by simpa using hD j) j

theorem norm_one_le_max (Kd : ℝ) : ‖(1 : Matrix n n ℂ)‖ ≤ max Kd 1 :=
  norm_one_matrix_le.trans (le_max_right _ _)

/-- `G·w(G)` is the dressed word with the letter `G` prepended (insertion `1`). -/
theorem G_mul_wordVal (Kh G : Matrix n n ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → Matrix n n ℂ) :
    G * wordVal Kh G wd D = wordVal Kh G (Fin.cons 0 wd : Fin (ℓ + 1) → Fin 4) (Fin.cons 1 D) := by
  rw [wordVal_cons, Matrix.one_mul]; rfl

/-- `α_j(G) = w'(G)` for a fixed shape `w'` of length `≤ ℓ`, insertions `≤ max K_d 1`. -/
theorem wordAlpha_shape (Kh : Matrix n n ℂ) {Kd : ℝ} :
    ∀ (ℓ : ℕ) (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ), (∀ j, ‖D j‖ ≤ Kd) →
      ∀ j : Fin ℓ, ∃ s : WordShape n ℓ (max Kd 1),
        ∀ G, wordAlpha Kh G ℓ wd D j = wordVal Kh G s.wd s.D := by
  intro ℓ
  induction ℓ with
  | zero => intro _ _ _ j; exact j.elim0
  | succ ℓ ih =>
    intro wd D hD j
    have hD' : ∀ i, ‖D i‖ ≤ max Kd 1 := fun i => (hD i).trans (le_max_left _ _)
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨⟨1, by omega, ![leftIdx (wd 0)], ![D 0, 1], fun i => ?_⟩, fun G => ?_⟩
      · fin_cases i
        · exact hD' 0
        · exact norm_one_le_max Kd
      · simp only [wordAlpha, Fin.cons_zero]
        rw [wordVal_succ, wordVal_zero, wLeft_eq]
        simp
    · obtain ⟨s, hs⟩ := ih (fun j => wd j.succ) (fun j => D j.succ) (fun i => hD _) j
      refine ⟨⟨s.len + 1, by have := s.hlen; omega, Fin.cons (wd 0) s.wd, Fin.cons (D 0) s.D,
        norm_cons_le _ _ (hD' 0) s.hD⟩, fun G => ?_⟩
      simp only [wordAlpha, Fin.cons_succ]
      rw [hs G, wordVal_cons, Matrix.mul_assoc]

/-- `γ_j(G) = w'(G)` for a fixed shape `w'` of length `≤ ℓ`, insertions `≤ max K_d 1`. -/
theorem wordGamma_shape (Kh : Matrix n n ℂ) {Kd : ℝ} :
    ∀ (ℓ : ℕ) (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ), (∀ j, ‖D j‖ ≤ Kd) →
      ∀ j : Fin ℓ, ∃ s : WordShape n ℓ (max Kd 1),
        ∀ G, wordGamma Kh G ℓ wd D j = wordVal Kh G s.wd s.D := by
  intro ℓ
  induction ℓ with
  | zero => intro _ _ _ j; exact j.elim0
  | succ ℓ ih =>
    intro wd D hD j
    have hD' : ∀ i, ‖D i‖ ≤ max Kd 1 := fun i => (hD i).trans (le_max_left _ _)
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨⟨ℓ + 1, le_rfl, Fin.cons (rightIdx (wd 0)) (fun j => wd j.succ),
        Fin.cons 1 (fun j => D j.succ), norm_cons_le _ _ (norm_one_le_max Kd) fun i => hD' _⟩,
        fun G => ?_⟩
      simp only [wordGamma, Fin.cons_zero]
      rw [wordVal_cons, Matrix.one_mul, wRight_eq]
    · obtain ⟨s, hs⟩ := ih (fun j => wd j.succ) (fun j => D j.succ) (fun i => hD _) j
      exact ⟨⟨s.len, by have := s.hlen; omega, s.wd, s.D, s.hD⟩, fun G => by
        simp only [wordGamma, Fin.cons_succ]; exact hs G⟩

/-- `G·α_j(G) = w'(G)` for a fixed shape of length `≤ ℓ + 1`. -/
theorem G_mul_wordAlpha_shape (Kh : Matrix n n ℂ) {Kd : ℝ} (ℓ : ℕ) (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → Matrix n n ℂ) (hD : ∀ j, ‖D j‖ ≤ Kd) (j : Fin ℓ) :
    ∃ s : WordShape n (ℓ + 1) (max Kd 1),
      ∀ G, G * wordAlpha Kh G ℓ wd D j = wordVal Kh G s.wd s.D := by
  obtain ⟨s, hs⟩ := wordAlpha_shape Kh ℓ wd D hD j
  refine ⟨⟨s.len + 1, by have := s.hlen; omega, Fin.cons 0 s.wd, Fin.cons 1 s.D,
    norm_cons_le _ _ (norm_one_le_max Kd) s.hD⟩, fun G => ?_⟩
  rw [hs G, G_mul_wordVal]

end BlockBand.Transmission.SourceMixing
