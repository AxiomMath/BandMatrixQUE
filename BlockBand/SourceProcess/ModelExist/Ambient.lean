module

public import BlockBand.SourceProcess.ModelExist.ModeAlg

/-!
# The padded ambient space and the extended initial frame

* Ambient space `Amb K R = (Fin K × Fin 2) ⊕ Fin R`: the `K` canonical mode blocks
  `(near, far)` and `R` extra near coordinates; `ambP` is the near projection (rank `K + R`).
* Extended columns `ExtCol K R = (Fin K × Fin 2) ⊕ Amb K R`: the current columns and one
  zero-signature column per ambient coordinate (`extSig`).
* `extFrame t h = [initialFrame | 1]`. `twoProjection_extFrame`: for `t_k ∈ [0,1]`,
  `ambP + V 𝖣 Vᴴ = W Wᴴ` with orthonormal columns `W` (the projections `P_k'` and the extra
  near coordinates), so the constraint holds.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped ComplexConjugate

variable (K R : ℕ)

/-- The padded ambient index. -/
abbrev Amb := (Fin K × Fin 2) ⊕ Fin R

/-- The extended column index. -/
abbrev ExtCol := (Fin K × Fin 2) ⊕ Amb K R

/-- The near projection: near coordinate of every mode, all extra coordinates. -/
def ambP : Matrix (Amb K R) (Amb K R) ℂ :=
  Matrix.diagonal fun i => match i with
    | Sum.inl x => if x.2 = 0 then 1 else 0
    | Sum.inr _ => 1

/-- The extended signature: `±1` on current columns, `0` on the ambient columns. -/
def extSig : Matrix (ExtCol K R) (ExtCol K R) ℂ :=
  Matrix.diagonal fun c => match c with
    | Sum.inl x => if x.2 = 0 then 1 else -1
    | Sum.inr _ => 0

/-- The current block of the canonical frame. -/
def curFrame (t : ℕ → ℝ) (h : ℝ) (x y : Fin K × Fin 2) : ℂ :=
  if x.1 = y.1 ∧ h ^ 2 < t y.1.val then
    ((t y.1.val ^ (1 / 4 : ℝ) : ℝ) : ℂ) * modeVector (t y.1.val) y.2 x.2 else 0

/-- The extended initial frame `[initialFrame | 1]`. -/
def extFrame (t : ℕ → ℝ) (h : ℝ) : Matrix (Amb K R) (ExtCol K R) ℂ :=
  fun r c => match c with
    | Sum.inl y => (match r with
      | Sum.inl x => curFrame K t h x y
      | Sum.inr _ => 0)
    | Sum.inr i => if r = i then 1 else 0

theorem curFrame_eq_initialFrame {π : Type*} (t : ℕ → ℝ) (h : ℝ) (x y : Fin K × Fin 2) :
    curFrame K t h x y = initialFrame K π t h x (Sum.inl y) := rfl

/-- The unit vector of mode `k`: `u(t_k)` if retained, the near coordinate otherwise. -/
def wv (t : ℕ → ℝ) (h : ℝ) (k : Fin K) (a : Fin 2) : ℝ :=
  if h ^ 2 < t k.val then uv (t k.val) a else (if a = 0 then 1 else 0)

/-- The orthonormal frame of `P'`. -/
def wFrame (t : ℕ → ℝ) (h : ℝ) : Matrix (Amb K R) (Fin K ⊕ Fin R) ℂ :=
  fun r c => match r, c with
    | Sum.inl x, Sum.inl k => if x.1 = k then (wv K t h k x.2 : ℂ) else 0
    | Sum.inr i, Sum.inr i' => if i = i' then 1 else 0
    | _, _ => 0

theorem wv_sq_sum {t : ℕ → ℝ} (ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1) (h : ℝ) (k : Fin K) :
    ∑ a, wv K t h k a * wv K t h k a = 1 := by
  unfold wv
  split_ifs
  · exact uv_sq_sum (ht _).1 (ht _).2
  · simp

theorem wFrame_orthonormal {t : ℕ → ℝ} (ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1) (h : ℝ) :
    (wFrame K R t h)ᴴ * wFrame K R t h = 1 := by
  ext c c'
  rcases c with k | i <;> rcases c' with k' | i' <;>
    simp only [Matrix.mul_apply, conjTranspose_apply, wFrame, Fintype.sum_sum_type,
      Fintype.sum_prod_type, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, ↓reduceIte]
  · by_cases hk : k = k'
    · subst hk
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
      simp only [↓reduceIte, RCLike.star_def, Complex.conj_ofReal]
      exact_mod_cast wv_sq_sum K ht h k
    · rw [Finset.sum_eq_zero fun b _ => ?_]
      · simp [hk]
      · by_cases hb : b = k <;> simp [hb, hk]
  · by_cases hi : i = i'
    · subst hi; simp
    · rw [Finset.sum_eq_zero fun b _ => ?_]
      · simp [hi]
      · by_cases hb : b = i <;> simp [hb, hi]

end BlockBand.SourceProcess.ModelExist
