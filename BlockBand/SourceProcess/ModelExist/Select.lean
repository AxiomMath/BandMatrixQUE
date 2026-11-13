module

public import BlockBand.SourceProcess.ModelExist.KerProj
public import BlockBand.SourceProcess.ModelExist.SelectSpec

/-!
# The measurable perpendicular selection

The linear conditions on a birth vector are `G a = 0` for the stacked matrix `selG` (rows of
`M − B`, rows `k` of `M` for current `k`, rows `prev_lᴴ M`). With `Π = specProj G` (measurable
in the data), the candidates are the columns `q_k = Π e_k ∈ ker G`; the selection takes the first
`k` (in a fixed enumeration of `c'`) with `r_k = Re(q_kᴴ M q_k) > 0` and rescales it to
`√(v / r_k) q_k`. If some `w ∈ ker G` has `M w ≠ 0`, such a `k` exists: otherwise `M q_k = 0`
(`M ⪰ 0`) for all `k`, so `M w = M Π w = 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open Matrix Finset MeasureTheory
open scoped ComplexOrder

variable {c' : Type*} [Fintype c'] [DecidableEq c'] {n : ℕ} (cur : c' → Prop) [DecidablePred cur]

/-- The stacked linear conditions. -/
def selG (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ) :
    Matrix (c' ⊕ {k // cur k} ⊕ Fin n) c' ℂ :=
  fun r => match r with
    | Sum.inl x => (H.1 - H.2) x
    | Sum.inr (Sum.inl k) => H.1 k.1
    | Sum.inr (Sum.inr l) => star (prev l) ᵥ* H.1

omit [DecidableEq c'] [DecidablePred cur] in
theorem selG_mulVec_eq_zero {H : Matrix c' c' ℂ × Matrix c' c' ℂ} {prev : Fin n → c' → ℂ}
    {a : c' → ℂ} : selG cur H prev *ᵥ a = 0 ↔ SelLin cur H prev a := by
  constructor
  · intro h
    refine ⟨funext fun x => congrFun h (Sum.inl x), fun k hk => congrFun h (Sum.inr (Sum.inl ⟨k, hk⟩)),
      fun l => ?_⟩
    have := congrFun h (Sum.inr (Sum.inr l))
    simp only [mulVec, selG, Pi.zero_apply] at this
    rw [dotProduct_mulVec]
    exact this
  · rintro ⟨h1, h2, h3⟩
    funext r
    rcases r with x | k | l
    · exact congrFun h1 x
    · exact h2 k.1 k.2
    · simp only [mulVec, selG, Pi.zero_apply]
      rw [← dotProduct_mulVec]
      exact h3 l

/-- The candidate columns `q_k = Π e_k`. -/
def candQ (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ) (k : c') : c' → ℂ :=
  specProj (selG cur H prev) *ᵥ Pi.single k 1

/-- Their `M`-norms `Re(q_kᴴ M q_k)`. -/
def candR (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ) (k : c') : ℝ :=
  (star (candQ cur H prev k) ⬝ᵥ (H.1 *ᵥ candQ cur H prev k)).re

/-- `j` is the first index with a positive candidate. -/
def IsFirst (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ)
    (j : Fin (Fintype.card c')) : Prop :=
  0 < candR cur H prev ((Fintype.equivFin c').symm j) ∧
    ∀ j' < j, ¬ 0 < candR cur H prev ((Fintype.equivFin c').symm j')

instance (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ)
    (j : Fin (Fintype.card c')) : Decidable (IsFirst cur H prev j) := by
  unfold IsFirst; infer_instance

/-- **The selection.** -/
def perpSel (z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) × ℝ) : c' → ℂ :=
  ∑ j, if IsFirst cur z.1 z.2.1 j then
    ((Real.sqrt (z.2.2 / candR cur z.1 z.2.1 ((Fintype.equivFin c').symm j)) : ℝ) : ℂ) •
      candQ cur z.1 z.2.1 ((Fintype.equivFin c').symm j) else 0

end BlockBand.SourceProcess.ModelExist
