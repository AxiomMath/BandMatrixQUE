module

public import BlockBand.Transmission.PassiveCovariance.TraceBilin

/-!
# Concatenation of dressed words: a product of two dressed forms is one dressed form

Deterministic. `catWd`, `catD`: the word `w₁ Z w₂` (letters of `w₁`, then of `w₂`; the junction
insertion is `D₁(ℓ₁)·Z·D₂(0)`), indexed by `ℓ₂ + ℓ₁` so that the recursion on `ℓ₁` is
definitional.

* `wordVal_cat`: `w(cat) = w₁ Z w₂`.
* `wordForm_mul_wordForm`: `(u₁*w₁v₁)(u₂*w₂v₂) = u₁*(w₁ (v₁u₂*) w₂)v₂`.
* `norm_catD_le`: insertions stay `≤ K_d²` when `‖Z‖ ≤ 1 ≤ K_d`; `norm_vecMulVec_le`:
  `‖v u*‖ ≤ ‖v‖‖u‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix.Norms.L2Operator

section
variable {n : Type} [Fintype n] [DecidableEq n]

/-- Letters of the concatenation `w₁ Z w₂`. -/
def catWd {ℓ₂ : ℕ} (wd₂ : Fin ℓ₂ → Fin 4) : (ℓ₁ : ℕ) → (Fin ℓ₁ → Fin 4) → Fin (ℓ₂ + ℓ₁) → Fin 4
  | 0, _ => wd₂
  | ℓ₁ + 1, wd₁ => Fin.cons (wd₁ 0) (catWd wd₂ ℓ₁ fun j => wd₁ j.succ)

/-- Insertions of the concatenation `w₁ Z w₂`. -/
def catD {ℓ₂ : ℕ} (Z : Matrix n n ℂ) (D₂ : Fin (ℓ₂ + 1) → Matrix n n ℂ) :
    (ℓ₁ : ℕ) → (Fin (ℓ₁ + 1) → Matrix n n ℂ) → Fin (ℓ₂ + ℓ₁ + 1) → Matrix n n ℂ
  | 0, D₁ => Fin.cons (D₁ 0 * Z * D₂ 0) fun k => D₂ k.succ
  | ℓ₁ + 1, D₁ => Fin.cons (D₁ 0) (catD Z D₂ ℓ₁ fun j => D₁ j.succ)

theorem wordVal_cat (Kh G Z : Matrix n n ℂ) {ℓ₂ : ℕ} (wd₂ : Fin ℓ₂ → Fin 4)
    (D₂ : Fin (ℓ₂ + 1) → Matrix n n ℂ) :
    ∀ (ℓ₁ : ℕ) (wd₁ : Fin ℓ₁ → Fin 4) (D₁ : Fin (ℓ₁ + 1) → Matrix n n ℂ),
      wordVal Kh G (catWd wd₂ ℓ₁ wd₁) (catD Z D₂ ℓ₁ D₁) =
        wordVal Kh G wd₁ D₁ * Z * wordVal Kh G wd₂ D₂ := by
  intro ℓ₁
  induction ℓ₁ with
  | zero =>
    intro wd₁ D₁
    simp only [wordVal, catWd, catD, Fin.cons_zero, Fin.cons_succ, List.ofFn_zero, List.prod_nil,
      Matrix.mul_one, Matrix.mul_assoc]
    rfl
  | succ ℓ₁ ih =>
    intro wd₁ D₁
    have e := ih (fun j => wd₁ j.succ) (fun j => D₁ j.succ)
    rw [wordVal_succ, wordVal_succ Kh G wd₁ D₁]
    show D₁ 0 * wLetter Kh G (wd₁ 0) * wordVal Kh G (catWd wd₂ ℓ₁ fun j => wd₁ j.succ)
      (catD Z D₂ ℓ₁ fun j => D₁ j.succ) = _
    rw [e]
    simp only [Matrix.mul_assoc]

theorem norm_catD_le {Kd : ℝ} (hK : 1 ≤ Kd) (Z : Matrix n n ℂ) (hZ : ‖Z‖ ≤ 1) {ℓ₂ : ℕ}
    (D₂ : Fin (ℓ₂ + 1) → Matrix n n ℂ) (hD₂ : ∀ j, ‖D₂ j‖ ≤ Kd) :
    ∀ (ℓ₁ : ℕ) (D₁ : Fin (ℓ₁ + 1) → Matrix n n ℂ), (∀ j, ‖D₁ j‖ ≤ Kd) →
      ∀ j, ‖catD Z D₂ ℓ₁ D₁ j‖ ≤ Kd ^ 2 := by
  have hK0 : 0 ≤ Kd := zero_le_one.trans hK
  have hKK : Kd ≤ Kd ^ 2 := by nlinarith
  intro ℓ₁
  induction ℓ₁ with
  | zero =>
    intro D₁ hD₁ j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [catD, Fin.cons_zero]
      calc ‖D₁ 0 * Z * D₂ 0‖ ≤ ‖D₁ 0‖ * ‖Z‖ * ‖D₂ 0‖ :=
            (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
              (norm_nonneg _))
        _ ≤ Kd * 1 * Kd := by gcongr <;> simp_all
        _ = Kd ^ 2 := by ring
    · simp only [catD, Fin.cons_succ]; exact (hD₂ _).trans hKK
  | succ ℓ₁ ih =>
    intro D₁ hD₁ j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [catD, Fin.cons_zero]; exact (hD₁ 0).trans hKK
    · simp only [catD, Fin.cons_succ]; exact ih _ (fun j => hD₁ _) k

omit [DecidableEq n] in
theorem vecMulVec_mulVec' (v u x : n → ℂ) : vecMulVec v u *ᵥ x = (u ⬝ᵥ x) • v := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [DecidableEq n] in
theorem vecNorm_smul' (c : ℂ) (x : n → ℂ) : vecNorm (c • x) = ‖c‖ * vecNorm x := by
  simp only [vecNorm, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem wordForm_mul_wordForm (Kh G : Matrix n n ℂ) (u₁ v₁ u₂ v₂ : n → ℂ) {ℓ₁ ℓ₂ : ℕ}
    (wd₁ : Fin ℓ₁ → Fin 4) (D₁ : Fin (ℓ₁ + 1) → Matrix n n ℂ) (wd₂ : Fin ℓ₂ → Fin 4)
    (D₂ : Fin (ℓ₂ + 1) → Matrix n n ℂ) :
    wordForm Kh u₁ v₁ wd₁ D₁ G * wordForm Kh u₂ v₂ wd₂ D₂ G =
      wordForm Kh u₁ v₂ (catWd wd₂ ℓ₁ wd₁) (catD (vecMulVec v₁ (star u₂)) D₂ ℓ₁ D₁) G := by
  rw [wordForm, wordForm, wordForm, wordVal_cat, ← mulVec_mulVec, ← mulVec_mulVec,
    vecMulVec_mulVec', mulVec_smul, dotProduct_smul, smul_eq_mul, mul_comm]

theorem norm_vecMulVec_le (v u : n → ℂ) : ‖vecMulVec v (star u)‖ ≤ vecNorm v * vecNorm u := by
  refine opNorm_le_of_vec _ (mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)) fun x => ?_
  rw [vecMulVec_mulVec', vecNorm_smul']
  have h := norm_star_dotProduct_le u x
  calc ‖star u ⬝ᵥ x‖ * vecNorm v ≤ vecNorm u * vecNorm x * vecNorm v :=
        mul_le_mul_of_nonneg_right h (vecNorm_nonneg _)
    _ = _ := by ring

end

end BlockBand.Transmission.PassiveCovariance
