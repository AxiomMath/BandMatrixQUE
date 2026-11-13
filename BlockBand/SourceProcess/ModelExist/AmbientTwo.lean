module

public import BlockBand.SourceProcess.ModelExist.Ambient

/-!
# The extended initial frame satisfies the two-projection constraint

The extended initial frame `[initialFrame | 1]` in the ambient space is an admissible initial
condition of the finite source equation.

`gramProjection_extFrame`: `ambP + V 𝖣 Vᴴ = W Wᴴ` (`mode_identity` on the retained modes);
`twoProjection_extFrame`: with `Wᴴ W = 1`, `W Wᴴ` is a Hermitian idempotent of trace `K + R`.
`isNearProjection_ambP`, `isSignature_extSig`: the standing hypotheses of the finite source
equation.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped ComplexConjugate

variable (K R : ℕ)

/-- The current part of a row of the extended frame. -/
def curPart (t : ℕ → ℝ) (h : ℝ) (r : Amb K R) (y : Fin K × Fin 2) : ℂ :=
  match r with
  | Sum.inl x => curFrame K t h x y
  | Sum.inr _ => 0

theorem extFrame_sig_entry (t : ℕ → ℝ) (h : ℝ) (r r' : Amb K R) :
    (extFrame K R t h * extSig K R * (extFrame K R t h)ᴴ) r r' =
      ∑ y, curPart K R t h r y * ((sgn y.2 : ℝ) : ℂ) * star (curPart K R t h r' y) := by
  have hm : ∀ c, (extFrame K R t h * extSig K R) r c = extFrame K R t h r c *
      (match c with | Sum.inl x => if x.2 = 0 then (1 : ℂ) else -1 | Sum.inr _ => 0) :=
    fun c => by rw [extSig, Matrix.mul_diagonal]; rfl
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hm, conjTranspose_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun y _ => ?_
  rcases r with x | i <;> rcases r' with x' | i' <;>
    simp [extFrame, curPart, sgn]
  split_ifs <;> simp

theorem curFrame_apply (t : ℕ → ℝ) (h : ℝ) (x y : Fin K × Fin 2) :
    curFrame K t h x y = if x.1 = y.1 ∧ h ^ 2 < t y.1.val then
      ((t y.1.val ^ (1 / 4 : ℝ) * ev (t y.1.val) y.2 x.2 : ℝ) : ℂ) else 0 := by
  simp only [curFrame, modeVector_eq, Complex.ofReal_mul]

theorem mode_entry {t : ℕ → ℝ} (ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1) (h : ℝ) (k k' : Fin K)
    (a b : Fin 2) :
    ∑ y : Fin K × Fin 2, curFrame K t h (k, a) y * ((sgn y.2 : ℝ) : ℂ) *
        star (curFrame K t h (k', b) y) =
      if k = k' ∧ h ^ 2 < t k.val then
        ((Real.sqrt (t k.val) * ∑ σ, sgn σ * ev (t k.val) σ a * ev (t k.val) σ b : ℝ) : ℂ)
      else 0 := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k (fun b' _ hb' => by
    refine Finset.sum_eq_zero fun σ _ => ?_
    simp [curFrame_apply, Ne.symm hb']) (by simp)]
  by_cases hk : k = k'
  · subst hk
    by_cases hr : h ^ 2 < t k.val
    · simp only [curFrame_apply, hr, ↓reduceIte, and_self, RCLike.star_def,
        Complex.conj_ofReal]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [← rpow_quarter_mul (ht k.val).1]
      push_cast
      ring
    · simp [curFrame_apply, hr]
  · simp [curFrame_apply, hk, Ne.symm hk]

theorem gramProjection_extFrame {t : ℕ → ℝ} (ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1) (h : ℝ) :
    gramProjection (ambP K R) (extFrame K R t h) (extSig K R) =
      wFrame K R t h * (wFrame K R t h)ᴴ := by
  ext r r'
  rw [gramProjection, Matrix.add_apply, extFrame_sig_entry]
  simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_sum_type]
  rcases r with ⟨k, a⟩ | i <;> rcases r' with ⟨k', b⟩ | i'
  · simp only [curPart]
    rw [mode_entry K ht h k k' a b]
    simp only [wFrame, ambP, Matrix.diagonal_apply, Sum.inl.injEq, Prod.mk.injEq, star_zero,
      mul_zero, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single k (fun b' _ hb' => by simp [Ne.symm hb']) (by simp)]
    by_cases hk : k = k'
    · subst hk
      have hid := mode_identity (ht k.val).1 (ht k.val).2 a b
      by_cases hr : h ^ 2 < t k.val
      · simp only [true_and, hr, and_self, ↓reduceIte, wv, RCLike.star_def, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, ← hid]
        fin_cases a <;> fin_cases b <;> push_cast <;> simp [add_comm]
      · simp only [true_and, hr, and_false, ↓reduceIte, wv, RCLike.star_def]
        fin_cases a <;> fin_cases b <;> simp
    · simp [hk, Ne.symm hk]
  · simp [curPart, wFrame, ambP]
  · simp [curPart, wFrame, ambP]
  · simp only [curPart, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, wFrame, star_zero,
      zero_add, ambP, Matrix.diagonal_apply, Sum.inr.injEq]
    by_cases hi : i = i'
    · subst hi
      rw [Finset.sum_eq_single i (fun b' _ hb' => by simp [Ne.symm hb']) (by simp)]
      simp
    · rw [Finset.sum_eq_zero fun b' _ => ?_]
      · simp [hi]
      · by_cases hb : i = b'
        · subst hb; simp [Ne.symm hi]
        · simp [hb]

theorem trace_ambP : (ambP K R).trace = ((K + R : ℕ) : ℂ) := by
  simp only [ambP, Matrix.trace_diagonal, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, add_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem isNearProjection_ambP : IsNearProjection (ambP K R) (K + R) := by
  refine ⟨?_, ?_, trace_ambP K R⟩
  · rw [ambP, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    rcases i with x | i
    · simp only [Pi.star_apply]; split_ifs <;> simp
    · simp
  · rw [ambP, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases i with x | i
    · dsimp only; split_ifs <;> simp
    · simp

theorem isSignature_extSig : IsSignature (extSig K R) := by
  refine ⟨?_, ?_⟩
  · rw [extSig, Matrix.diagonal_conjTranspose]
    congr 1
    funext c
    rcases c with x | i
    · simp only [Pi.star_apply]; split_ifs <;> simp
    · simp
  · rw [extSig, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext c
    rcases c with x | i
    · dsimp only; split_ifs <;> simp
    · simp

/-- **The extended initial frame satisfies the two-projection constraint.** -/
theorem twoProjection_extFrame {t : ℕ → ℝ} (ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1) (h : ℝ) :
    TwoProjection (ambP K R) (extSig K R) (extFrame K R t h) := by
  have hW := wFrame_orthonormal K R ht h
  unfold TwoProjection
  rw [gramProjection_extFrame K R ht h]
  refine ⟨by rw [conjTranspose_mul, conjTranspose_conjTranspose], ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (wFrame K R t h)ᴴ, hW, Matrix.one_mul]
  · rw [Matrix.trace_mul_comm, hW, Matrix.trace_one, trace_ambP]
    simp

end BlockBand.SourceProcess.ModelExist
