module

public import BlockBand.Transmission.PassiveLayer.BilLayer

/-!
# Passive words as functions of the full layer resolvent

Every letter of `passiveLetter` is a block `P 𝒢 Q` of the full resolvent `𝒢`, with
`P ∈ {ι₁, ι₂, Kι₁}` (`lP K`) and `Q ∈ {ι₁ᴴ, ι₂ᴴ}` (`lQ`), `K = w - X`; a word is `tmWord K wd D 𝒢`
(`passiveWord_eq`). The unbounded `K` enters **only** through `Kι₁𝒢`: with
`Λ(K, 𝒢) = 1 + ‖𝒢‖ + ‖Kι₁𝒢‖` (`lam`),
* `norm_lP_mul_le`, `norm_tmLetter_le`: `‖P𝒢‖, ‖𝒢Q‖, ‖letter‖ ≤ Λ`;
* `norm_tmWord_le`: `‖w(𝒢)‖ ≤ K_d^{ℓ+1} Λ^ℓ` when every insertion has `‖D_j‖ ≤ K_d`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix
open BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The layer sites of the one-block one-port layer. -/
abbrev LS (W : ℕ) : Type := LayerSite W .oneBlockOnePort

/-- Left factors of the six letters: `ι₁, ι₁, ι₂, ι₂, Kι₁, Kι₁`. -/
def lP (K : Matrix (Fin W) (Fin W) ℂ) : Fin 6 → Matrix (Fin W) (LS W) ℂ :=
  ![iota1 W, iota1 W, iota2 W, iota2 W, K * iota1 W, K * iota1 W]

/-- Right factors of the six letters: `ι₁ᴴ, ι₂ᴴ, ι₁ᴴ, ι₂ᴴ, ι₁ᴴ, ι₂ᴴ`. -/
def lQ (W : ℕ) : Fin 6 → Matrix (LS W) (Fin W) ℂ :=
  ![(iota1 W)ᴴ, (iota2 W)ᴴ, (iota1 W)ᴴ, (iota2 W)ᴴ, (iota1 W)ᴴ, (iota2 W)ᴴ]

/-- A letter `P𝒢Q` or its adjoint. -/
def tmLetter (K : Matrix (Fin W) (Fin W) ℂ) (l : Fin 6 × Bool) (G : Matrix (LS W) (LS W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  if l.2 then (lP K l.1 * G * lQ W l.1)ᴴ else lP K l.1 * G * lQ W l.1

/-- The word `D₀ ℓ₁ D₁ ⋯ ℓ_m D_m` as a function of the full resolvent. -/
def tmWord (K : Matrix (Fin W) (Fin W) ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 6 × Bool)
    (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ) (G : Matrix (LS W) (LS W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  D 0 * (List.ofFn fun j : Fin ℓ => tmLetter K (wd j) G * D j.succ).prod

/-- The weight `Λ(K, 𝒢) = 1 + ‖𝒢‖ + ‖Kι₁𝒢‖`. -/
def lam (K : Matrix (Fin W) (Fin W) ℂ) (G : Matrix (LS W) (LS W) ℂ) : ℝ :=
  1 + ‖G‖ + ‖K * iota1 W * G‖

theorem one_le_lam (K : Matrix (Fin W) (Fin W) ℂ) (G : Matrix (LS W) (LS W) ℂ) :
    1 ≤ lam K G := by
  unfold lam; linarith [norm_nonneg G, norm_nonneg (K * iota1 W * G)]

/-!
## Identification with `passiveWord`
-/

theorem g11_eq_iota (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    g11 E w X ω = iota1 W * layerAt E w X ω * (iota1 W)ᴴ := by
  ext x y
  simp [g11, iota1, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem g21_eq_iota (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    g21 E w X ω = iota2 W * layerAt E w X ω * (iota1 W)ᴴ := by
  ext x y
  simp [g21, iota1, iota2, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem passiveLetter_eq (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (j : Fin 6) :
    passiveLetter E w X ω j = lP (w • 1 - X) j * layerAt E w X ω * lQ W j := by
  fin_cases j
  · exact g11_eq_iota E w X ω
  · exact g12_eq_iota E w X ω
  · exact g21_eq_iota E w X ω
  · exact g22_eq_iota E w X ω
  · show kG11 E w X ω = (w • 1 - X) * iota1 W * layerAt E w X ω * (iota1 W)ᴴ
    rw [kG11, g11_eq_iota]; simp only [Matrix.mul_assoc]
  · exact lAt_eq_iota E w X ω

/-- **`passiveWord` is the word `tmWord (w - X)` of the full resolvent.** -/
theorem passiveWord_eq (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    passiveWord E w X wd D ω = tmWord (w • 1 - X) wd D (layerAt E w X ω) := by
  simp only [passiveWord, tmWord, tmLetter, passiveLetter_eq]

/-!
## Recursion and norms
-/

theorem tmWord_zero (K : Matrix (Fin W) (Fin W) ℂ) (wd : Fin 0 → Fin 6 × Bool)
    (D : Fin 1 → Matrix (Fin W) (Fin W) ℂ) (G : Matrix (LS W) (LS W) ℂ) :
    tmWord K wd D G = D 0 := by
  simp [tmWord]

/-- **Recursion** `w(𝒢) = D₀ ℓ₀(𝒢) w'(𝒢)`, `w'` the word of the tail. -/
theorem tmWord_succ (K : Matrix (Fin W) (Fin W) ℂ) {ℓ : ℕ} (wd : Fin (ℓ + 1) → Fin 6 × Bool)
    (D : Fin (ℓ + 2) → Matrix (Fin W) (Fin W) ℂ) (G : Matrix (LS W) (LS W) ℂ) :
    tmWord K wd D G = D 0 * tmLetter K (wd 0) G *
      tmWord K (fun j => wd j.succ) (fun j => D j.succ) G := by
  simp only [tmWord, List.ofFn_succ, List.prod_cons]
  simp only [Fin.succ_zero_eq_one, Matrix.mul_assoc]

theorem iota1_mul_conjTranspose : iota1 W * (iota1 W)ᴴ = 1 := by
  ext x y
  simp [iota1, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

theorem iota2_mul_conjTranspose : iota2 W * (iota2 W)ᴴ = 1 := by
  ext x y
  simp [iota2, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

theorem norm_one_le' : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun _ => by simp

theorem norm_le_one_of_mul_conjTranspose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {A : Matrix m n ℂ} (h : ‖A * Aᴴ‖ ≤ 1) : ‖A‖ ≤ 1 := by
  have e := Matrix.l2_opNorm_conjTranspose_mul_self Aᴴ
  rw [conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at e
  rw [e] at h
  nlinarith [norm_nonneg A]

theorem norm_iota1_le : ‖iota1 W‖ ≤ 1 :=
  norm_le_one_of_mul_conjTranspose (by rw [iota1_mul_conjTranspose]; exact norm_one_le')

theorem norm_iota2_le : ‖iota2 W‖ ≤ 1 :=
  norm_le_one_of_mul_conjTranspose (by rw [iota2_mul_conjTranspose]; exact norm_one_le')

theorem norm_lQ_le (j : Fin 6) : ‖lQ W j‖ ≤ 1 := by
  have h1 : ‖(iota1 W)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact norm_iota1_le
  have h2 : ‖(iota2 W)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact norm_iota2_le
  fin_cases j
  · exact h1
  · exact h2
  · exact h1
  · exact h2
  · exact h1
  · exact h2

theorem norm_mul_le_of_le_one {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] {A : Matrix m n ℂ} (B : Matrix n p ℂ)
    (hA : ‖A‖ ≤ 1) : ‖A * B‖ ≤ ‖B‖ :=
  (Matrix.l2_opNorm_mul A B).trans (by nlinarith [norm_nonneg A, norm_nonneg B])

theorem norm_mul_le_of_le_one' {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] (A : Matrix m n ℂ) {B : Matrix n p ℂ}
    (hB : ‖B‖ ≤ 1) : ‖A * B‖ ≤ ‖A‖ :=
  (Matrix.l2_opNorm_mul A B).trans (by nlinarith [norm_nonneg A, norm_nonneg B])

theorem norm_lP_mul_le (K : Matrix (Fin W) (Fin W) ℂ) (G : Matrix (LS W) (LS W) ℂ) (j : Fin 6) :
    ‖lP K j * G‖ ≤ lam K G := by
  have h1 : ‖iota1 W * G‖ ≤ lam K G :=
    (norm_mul_le_of_le_one G norm_iota1_le).trans (by unfold lam; linarith [norm_nonneg (K * iota1 W * G)])
  have h2 : ‖iota2 W * G‖ ≤ lam K G :=
    (norm_mul_le_of_le_one G norm_iota2_le).trans (by unfold lam; linarith [norm_nonneg (K * iota1 W * G)])
  have h3 : ‖K * iota1 W * G‖ ≤ lam K G := by unfold lam; linarith [norm_nonneg G]
  fin_cases j
  · exact h1
  · exact h1
  · exact h2
  · exact h2
  · exact h3
  · exact h3

theorem norm_mul_lQ_le (K : Matrix (Fin W) (Fin W) ℂ) (G : Matrix (LS W) (LS W) ℂ) (j : Fin 6) :
    ‖G * lQ W j‖ ≤ lam K G :=
  (norm_mul_le_of_le_one' G (norm_lQ_le j)).trans
    (by unfold lam; linarith [norm_nonneg (K * iota1 W * G)])

theorem norm_tmLetter_le (K : Matrix (Fin W) (Fin W) ℂ) (l : Fin 6 × Bool)
    (G : Matrix (LS W) (LS W) ℂ) : ‖tmLetter K l G‖ ≤ lam K G := by
  have h : ‖lP K l.1 * G * lQ W l.1‖ ≤ lam K G :=
    (norm_mul_le_of_le_one' _ (norm_lQ_le l.1)).trans (norm_lP_mul_le K G l.1)
  unfold tmLetter
  split_ifs
  · rwa [Matrix.l2_opNorm_conjTranspose]
  · exact h

/-- `‖w(𝒢)‖ ≤ K_d^{ℓ+1} Λ^ℓ`. -/
theorem norm_tmWord_le (K : Matrix (Fin W) (Fin W) ℂ) {Kd : ℝ} (hKd : 0 ≤ Kd) :
    ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ)
      (G : Matrix (LS W) (LS W) ℂ), (∀ j, ‖D j‖ ≤ Kd) →
      ‖tmWord K wd D G‖ ≤ Kd ^ (ℓ + 1) * lam K G ^ ℓ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro wd D G hD
    rw [tmWord_zero]
    simpa using hD 0
  | succ ℓ ih =>
    intro wd D G hD
    rw [tmWord_succ]
    have h1 := ih (fun j => wd j.succ) (fun j => D j.succ) G (fun j => hD _)
    have h0 := hD 0
    have hl := norm_tmLetter_le K (wd 0) G
    have hL0 : 0 ≤ lam K G := (zero_le_one).trans (one_le_lam K G)
    calc ‖D 0 * tmLetter K (wd 0) G * tmWord K (fun j => wd j.succ) (fun j => D j.succ) G‖
        ≤ ‖D 0‖ * ‖tmLetter K (wd 0) G‖ *
            ‖tmWord K (fun j => wd j.succ) (fun j => D j.succ) G‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ ≤ Kd * lam K G * (Kd ^ (ℓ + 1) * lam K G ^ ℓ) := by gcongr
      _ = Kd ^ (ℓ + 1 + 1) * lam K G ^ (ℓ + 1) := by ring

/-- Words are jointly continuous in `(K, 𝒢)`. -/
theorem continuous_tmWord :
    ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ),
      Continuous (fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (LS W) (LS W) ℂ =>
        tmWord p.1 wd D p.2) := by
  have hP : ∀ j : Fin 6, Continuous (fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (LS W) (LS W) ℂ =>
      lP p.1 j * p.2 * lQ W j) := by
    intro j
    fin_cases j <;> simp only [lP, lQ] <;> fun_prop
  have hl : ∀ l : Fin 6 × Bool, Continuous (fun p : Matrix (Fin W) (Fin W) ℂ ×
      Matrix (LS W) (LS W) ℂ => tmLetter p.1 l p.2) := by
    intro l
    unfold tmLetter
    split_ifs
    · exact (hP l.1).matrix_conjTranspose
    · exact hP l.1
  intro ℓ
  induction ℓ with
  | zero =>
    intro wd D
    simp only [tmWord_zero]
    exact continuous_const
  | succ ℓ ih =>
    intro wd D
    simp only [tmWord_succ]
    exact (continuous_const.mul (hl _)).mul (ih _ _)

end BlockBand.Transmission.PassiveLayer
