module

public import BlockBand.Transmission.SchurDerivative
public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# Calculus of dressed resolvent words

A **dressed word** is `D₀ ℓ₁ D₁ ⋯ ℓ_m D_m` with letters `ℓ ∈ {G, K̂G, Gᴴ, (K̂G)ᴴ}` (`wLetter`)
and deterministic square insertions `D_j`. For the fresh layer, `G = 𝒢` (the `2W × 2W` layer
resolvent) and `K̂ = diag(K, I)` with `K = z - X` (`kHat`). Then every letter of
a `passiveWord` (`𝒢_{ij}`, `K𝒢₁₁`, `L = K𝒢₁₂` and their adjoints) is a block of one of these
four, and every bilinear form `u*w v` of a passive word is a bilinear form of a dressed word.
Weighted letters keep their weight attached ("all derivatives keep their outside factors"):
`d(K̂G) = -(K̂G)NG`, so no bound below involves `‖K̂‖`.

* `norm_wordVal_le`: `‖w(G)‖ ≤ K_d^{m+1} B^m`, `B = ‖G‖ + ‖K̂G‖` (`wBound`).
* `hasDerivAt_wordVal_line` (**product rule along a line**): for `G(t) = (M + tN)⁻¹`, `N`
  Hermitian, `d/dt w(G(t))|₀ = -Σ_{j<m} α_j N γ_j` with the explicit factors
  `α_j = wordAlpha`, `γ_j = wordGamma` (independent of `N`; the ℂ-linear extension to
  non-Hermitian `N` is the one the replica identity needs);
  `norm_wordAlpha_mul_le`: `‖α_j‖‖γ_j‖ ≤ K_d^{m+1} B^{m+1}`; `word_line` packages both.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open scoped Matrix.Norms.L2Operator

section
variable {n : Type} [Fintype n] [DecidableEq n]

/-- The four letters `G, K̂G, Gᴴ, (K̂G)ᴴ`. -/
def wLetter (Kh G : Matrix n n ℂ) (k : Fin 4) : Matrix n n ℂ := ![G, Kh * G, Gᴴ, (Kh * G)ᴴ] k

/-- Left factor of the letter derivative `dℓ = -(wLeft) N (wRight)`. -/
def wLeft (Kh G : Matrix n n ℂ) (k : Fin 4) : Matrix n n ℂ := ![G, Kh * G, Gᴴ, Gᴴ] k

/-- Right factor of the letter derivative. -/
def wRight (Kh G : Matrix n n ℂ) (k : Fin 4) : Matrix n n ℂ := ![G, G, Gᴴ, (Kh * G)ᴴ] k

/-- A dressed word `D₀ ℓ₁ D₁ ⋯ ℓ_m D_m`. -/
def wordVal (Kh G : Matrix n n ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ) :
    Matrix n n ℂ :=
  D 0 * (List.ofFn fun j : Fin ℓ => wLetter Kh G (wd j) * D j.succ).prod

/-- The letter bound `B = ‖G‖ + ‖K̂G‖`. -/
def wBound (Kh G : Matrix n n ℂ) : ℝ := ‖G‖ + ‖Kh * G‖

theorem wBound_nonneg (Kh G : Matrix n n ℂ) : 0 ≤ wBound Kh G := by unfold wBound; positivity

theorem wordVal_zero (Kh G : Matrix n n ℂ) (wd : Fin 0 → Fin 4) (D : Fin 1 → Matrix n n ℂ) :
    wordVal Kh G wd D = D 0 := by
  simp [wordVal]

theorem wordVal_succ (Kh G : Matrix n n ℂ) {ℓ : ℕ} (wd : Fin (ℓ + 1) → Fin 4)
    (D : Fin (ℓ + 2) → Matrix n n ℂ) :
    wordVal Kh G wd D = D 0 * wLetter Kh G (wd 0) *
      wordVal Kh G (fun j => wd j.succ) (fun j => D j.succ) := by
  simp only [wordVal, List.ofFn_succ, List.prod_cons, Matrix.mul_assoc]

theorem norm_wLetter_le (Kh G : Matrix n n ℂ) (k : Fin 4) : ‖wLetter Kh G k‖ ≤ wBound Kh G := by
  have h1 := norm_nonneg G; have h2 := norm_nonneg (Kh * G)
  fin_cases k <;> simp [wLetter, wBound, -conjTranspose_mul, Matrix.l2_opNorm_conjTranspose]

theorem norm_wLeft_le (Kh G : Matrix n n ℂ) (k : Fin 4) : ‖wLeft Kh G k‖ ≤ wBound Kh G := by
  have h1 := norm_nonneg G; have h2 := norm_nonneg (Kh * G)
  fin_cases k <;> simp [wLeft, wBound, -conjTranspose_mul, Matrix.l2_opNorm_conjTranspose]

theorem norm_wRight_le (Kh G : Matrix n n ℂ) (k : Fin 4) : ‖wRight Kh G k‖ ≤ wBound Kh G := by
  have h1 := norm_nonneg G; have h2 := norm_nonneg (Kh * G)
  fin_cases k <;> simp [wRight, wBound, -conjTranspose_mul, Matrix.l2_opNorm_conjTranspose]

/-- `‖w(G)‖ ≤ K_d^{m+1} B^m`. -/
theorem norm_wordVal_le (Kh G : Matrix n n ℂ) {Kd : ℝ} (hKd : 0 ≤ Kd) :
    ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ), (∀ j, ‖D j‖ ≤ Kd) →
      ‖wordVal Kh G wd D‖ ≤ Kd ^ (ℓ + 1) * wBound Kh G ^ ℓ := by
  intro ℓ
  induction ℓ with
  | zero => intro wd D hD; simpa [wordVal_zero] using hD 0
  | succ ℓ ih =>
    intro wd D hD
    rw [wordVal_succ]
    have hB := wBound_nonneg Kh G
    have h1 := ih (fun j => wd j.succ) (fun j => D j.succ) fun j => hD _
    calc ‖D 0 * wLetter Kh G (wd 0) * wordVal Kh G (fun j => wd j.succ) fun j => D j.succ‖
        ≤ ‖D 0‖ * ‖wLetter Kh G (wd 0)‖ * ‖wordVal Kh G (fun j => wd j.succ) fun j => D j.succ‖ :=
          (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
            (norm_nonneg _))
      _ ≤ Kd * wBound Kh G * (Kd ^ (ℓ + 1) * wBound Kh G ^ ℓ) := by
          gcongr
          · exact hD 0
          · exact norm_wLetter_le _ _ _
      _ = Kd ^ (ℓ + 1 + 1) * wBound Kh G ^ (ℓ + 1) := by ring

/-- `d/dt (M + tN)⁻¹ = -M⁻¹NM⁻¹` at `t = 0` (real `t`). -/
theorem hasDerivAt_inv_line' (M N : Matrix n n ℂ) (hM : IsUnit M) :
    HasDerivAt (fun t : ℝ => (M + (t : ℂ) • N)⁻¹) (-(M⁻¹ * N * M⁻¹)) 0 := by
  have h := affineInverse_hasDerivAt M N 0 (by simpa using hM)
  simp only [zero_smul, add_zero] at h
  have h' : HasDerivAt (fun s : ℂ => (M + s • N)⁻¹) (-(M⁻¹ * N * M⁻¹)) (Complex.ofRealCLM 0) := by
    simpa using h
  have := h'.scomp (0 : ℝ) Complex.ofRealCLM.hasDerivAt
  simpa [Function.comp_def] using this

theorem inv_line_zero (M N : Matrix n n ℂ) : (M + ((0 : ℝ) : ℂ) • N)⁻¹ = M⁻¹ := by simp

/-- Derivative of a letter along the line, `N` Hermitian. -/
theorem hasDerivAt_wLetter (Kh M N : Matrix n n ℂ) (hM : IsUnit M) (hN : N.IsHermitian)
    (k : Fin 4) :
    HasDerivAt (fun t : ℝ => wLetter Kh ((M + (t : ℂ) • N)⁻¹) k)
      (-(wLeft Kh M⁻¹ k * N * wRight Kh M⁻¹ k)) 0 := by
  have hG := hasDerivAt_inv_line' M N hM
  have hS : HasDerivAt (fun t : ℝ => ((M + (t : ℂ) • N)⁻¹)ᴴ) (-(M⁻¹ᴴ * N * M⁻¹ᴴ)) 0 := by
    have := hG.star
    simp only [star_neg, Matrix.star_eq_conjTranspose, conjTranspose_mul, hN.eq,
      Matrix.mul_assoc] at this
    simpa [Matrix.mul_assoc] using this
  have hK : HasDerivAt (fun t : ℝ => Kh * (M + (t : ℂ) • N)⁻¹) (-(Kh * M⁻¹ * N * M⁻¹)) 0 := by
    have := hG.const_mul Kh
    simpa [Matrix.mul_neg, Matrix.mul_assoc] using this
  have hKS : HasDerivAt (fun t : ℝ => (Kh * (M + (t : ℂ) • N)⁻¹)ᴴ)
      (-(M⁻¹ᴴ * N * (Kh * M⁻¹)ᴴ)) 0 := by
    have := hK.star
    simp only [star_neg, Matrix.star_eq_conjTranspose, conjTranspose_mul, hN.eq,
      Matrix.mul_assoc] at this
    simpa [Matrix.mul_assoc, conjTranspose_mul] using this
  fin_cases k
  · simpa [wLetter, wLeft, wRight] using hG
  · simpa [wLetter, wLeft, wRight, Matrix.mul_assoc] using hK
  · simpa [wLetter, wLeft, wRight] using hS
  · simpa [wLetter, wLeft, wRight, Matrix.mul_assoc] using hKS

/-- Left derivative factors `α_j = D₀ℓ₁⋯D_{j-1}·wLeft(ℓ_j)` of a dressed word. -/
def wordAlpha (Kh G : Matrix n n ℂ) :
    (ℓ : ℕ) → (Fin ℓ → Fin 4) → (Fin (ℓ + 1) → Matrix n n ℂ) → Fin ℓ → Matrix n n ℂ
  | 0, _, _ => Fin.elim0
  | ℓ + 1, wd, D => Fin.cons (D 0 * wLeft Kh G (wd 0)) fun j =>
      D 0 * wLetter Kh G (wd 0) * wordAlpha Kh G ℓ (fun j => wd j.succ) (fun j => D j.succ) j

/-- Right derivative factors `γ_j = wRight(ℓ_j)·D_jℓ_{j+1}⋯D_m` of a dressed word. -/
def wordGamma (Kh G : Matrix n n ℂ) :
    (ℓ : ℕ) → (Fin ℓ → Fin 4) → (Fin (ℓ + 1) → Matrix n n ℂ) → Fin ℓ → Matrix n n ℂ
  | 0, _, _ => Fin.elim0
  | ℓ + 1, wd, D => Fin.cons (wRight Kh G (wd 0) * wordVal Kh G (fun j => wd j.succ) fun j => D j.succ)
      (wordGamma Kh G ℓ (fun j => wd j.succ) fun j => D j.succ)

/-- `‖α_j‖‖γ_j‖ ≤ K_d^{m+1}B^{m+1}`. -/
theorem norm_wordAlpha_mul_le (Kh G : Matrix n n ℂ) {Kd : ℝ} (hKd : 0 ≤ Kd) :
    ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ), (∀ j, ‖D j‖ ≤ Kd) →
      ∀ j, ‖wordAlpha Kh G ℓ wd D j‖ * ‖wordGamma Kh G ℓ wd D j‖ ≤
        Kd ^ (ℓ + 1) * wBound Kh G ^ (ℓ + 1) := by
  intro ℓ
  induction ℓ with
  | zero => intro wd D _ j; exact j.elim0
  | succ ℓ ih =>
    intro wd D hD j
    have hB := wBound_nonneg Kh G
    set B := wBound Kh G
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [wordAlpha, wordGamma, Fin.cons_zero]
      have hR := norm_wordVal_le Kh G hKd (fun j => wd j.succ) (fun j => D j.succ) fun j => hD _
      calc ‖D 0 * wLeft Kh G (wd 0)‖ *
            ‖wRight Kh G (wd 0) * wordVal Kh G (fun j => wd j.succ) fun j => D j.succ‖
          ≤ (‖D 0‖ * ‖wLeft Kh G (wd 0)‖) *
              (‖wRight Kh G (wd 0)‖ * ‖wordVal Kh G (fun j => wd j.succ) fun j => D j.succ‖) :=
            mul_le_mul (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
              (by positivity)
        _ ≤ (Kd * B) * (B * (Kd ^ (ℓ + 1) * B ^ ℓ)) := by
            gcongr
            · exact hD 0
            · exact norm_wLeft_le _ _ _
            · exact norm_wRight_le _ _ _
        _ = Kd ^ (ℓ + 1 + 1) * B ^ (ℓ + 1 + 1) := by ring
    · simp only [wordAlpha, wordGamma, Fin.cons_succ]
      have hb' := ih (fun j => wd j.succ) (fun j => D j.succ) (fun j => hD _) j
      calc ‖D 0 * wLetter Kh G (wd 0) * wordAlpha Kh G ℓ (fun j => wd j.succ) (fun j => D j.succ) j‖ *
            ‖wordGamma Kh G ℓ (fun j => wd j.succ) (fun j => D j.succ) j‖
          ≤ (‖D 0‖ * ‖wLetter Kh G (wd 0)‖ *
              ‖wordAlpha Kh G ℓ (fun j => wd j.succ) (fun j => D j.succ) j‖) *
            ‖wordGamma Kh G ℓ (fun j => wd j.succ) (fun j => D j.succ) j‖ := by
            gcongr
            exact (Matrix.l2_opNorm_mul _ _).trans
              (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
        _ = ‖D 0‖ * ‖wLetter Kh G (wd 0)‖ *
              (‖wordAlpha Kh G ℓ (fun j => wd j.succ) (fun j => D j.succ) j‖ *
                ‖wordGamma Kh G ℓ (fun j => wd j.succ) (fun j => D j.succ) j‖) := by ring
        _ ≤ Kd * B * (Kd ^ (ℓ + 1) * B ^ (ℓ + 1)) :=
            mul_le_mul (mul_le_mul (hD 0) (norm_wLetter_le _ _ _) (norm_nonneg _) hKd) hb'
              (by positivity) (by positivity)
        _ = Kd ^ (ℓ + 1 + 1) * B ^ (ℓ + 1 + 1) := by ring

/-- **Product rule for dressed words along a line**: for `M` invertible and every Hermitian `N`,
`d/dt w((M + tN)⁻¹)|₀ = -Σ_j α_j N γ_j` with the explicit factors at `G = M⁻¹`. -/
theorem hasDerivAt_wordVal_line (Kh M : Matrix n n ℂ) (hM : IsUnit M) :
    ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ) (N : Matrix n n ℂ),
      N.IsHermitian →
        HasDerivAt (fun t : ℝ => wordVal Kh ((M + (t : ℂ) • N)⁻¹) wd D)
          (-∑ j, wordAlpha Kh M⁻¹ ℓ wd D j * N * wordGamma Kh M⁻¹ ℓ wd D j) 0 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro wd D N _
    simp only [wordVal_zero, Finset.univ_eq_empty, Finset.sum_empty, neg_zero]
    exact hasDerivAt_const _ _
  | succ ℓ ih =>
    intro wd D N hN
    have hL := hasDerivAt_wLetter Kh M N hM hN (wd 0)
    have hR := ih (fun j => wd j.succ) (fun j => D j.succ) N hN
    have h := (hL.const_mul (D 0)).mul hR
    simp only [inv_line_zero] at h
    have e : (fun t : ℝ => wordVal Kh ((M + (t : ℂ) • N)⁻¹) wd D) = fun t : ℝ =>
        D 0 * wLetter Kh ((M + (t : ℂ) • N)⁻¹) (wd 0) *
          wordVal Kh ((M + (t : ℂ) • N)⁻¹) (fun j => wd j.succ) (fun j => D j.succ) := by
      funext t; exact wordVal_succ _ _ _ _
    rw [e]
    convert h using 1
    rw [Fin.sum_univ_succ]
    simp only [wordAlpha, wordGamma, Fin.cons_zero, Fin.cons_succ, Matrix.mul_neg, Matrix.neg_mul,
      Finset.mul_sum, Matrix.mul_assoc, neg_add]

/-- The existential form used by `WordGrad`. -/
theorem word_line (Kh M : Matrix n n ℂ) (hM : IsUnit M) {Kd : ℝ} (hKd : 0 ≤ Kd) :
    ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ), (∀ j, ‖D j‖ ≤ Kd) →
      ∃ α γ : Fin ℓ → Matrix n n ℂ,
        (∀ j, ‖α j‖ * ‖γ j‖ ≤ Kd ^ (ℓ + 1) * wBound Kh M⁻¹ ^ (ℓ + 1)) ∧
        ∀ N : Matrix n n ℂ, N.IsHermitian →
          HasDerivAt (fun t : ℝ => wordVal Kh ((M + (t : ℂ) • N)⁻¹) wd D)
            (-∑ j, α j * N * γ j) 0 := fun wd D hD =>
  ⟨wordAlpha Kh M⁻¹ _ wd D, wordGamma Kh M⁻¹ _ wd D,
    norm_wordAlpha_mul_le Kh M⁻¹ hKd wd D hD, fun N hN => hasDerivAt_wordVal_line Kh M hM wd D N hN⟩

end

end BlockBand.Transmission.PassiveCovariance
