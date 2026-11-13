module

public import BlockBand.SourceProcess.CoupledFrames.GenSel
public import BlockBand.SourceProcess.CoupledFrames.JointRank
public import BlockBand.SourceProcess.Stochastic.FiniteSource

/-!
# The two-frame selection

Two frames `Y₁, Y₂ : Matrix ι c'` are stacked into `Ŷ = [Y₁ | Y₂]` (columns `c' ⊕ c'`); their
joint Gram state is `gramPair P Ŷ`. A birth vector is `a = (a₁, a₂) : c' ⊕ c' → ℂ`, the new
column is `w = Y₁ a₁`. The linear conditions are `jointG H prev a = 0`:
* `M (a₁, −a₂) = 0` (`Y₁ a₁ = Y₂ a₂`);
* `(M − B)(a₁, 0) = 0` (`w` is near);
* `(M (a₁, 0))_z = 0` for the current columns `z` of both frames;
* `prev_lᴶᴴ M (a₁, 0) = 0` for the earlier vectors in both frames (`J = 1, 2`);
and `(a₁, 0)ᴴ M (a₁, 0) = v` (`jointQ`). `jointSel = genSel jointG jointQ`.

`jointSpec_of`: the conditions in terms of the frames; `jointExists`: a solution with
`jointQ a ≠ 0` exists when `rank(P Y_j) ≥ rank P` and `2#cur + 2n + 2|ι| < 3 rank P`
(`exists_common_perp`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open Matrix Finset BlockBand.SourceProcess.Stochastic
open scoped ComplexOrder

variable {c' : Type*} [Fintype c'] [DecidableEq c'] {n : ℕ} (cur : c' → Prop) [DecidablePred cur]

/-- First and second halves of a joint vector. -/
def fstV (a : c' ⊕ c' → ℂ) : c' → ℂ := fun y => a (Sum.inl y)
def sndV (a : c' ⊕ c' → ℂ) : c' → ℂ := fun y => a (Sum.inr y)

/-- The coordinate projections onto the two halves. -/
def projF (j : Fin 2) : Matrix (c' ⊕ c') (c' ⊕ c') ℂ :=
  diagonal fun z => match z with
    | Sum.inl _ => if j = 0 then 1 else 0
    | Sum.inr _ => if j = 0 then 0 else 1

/-- The current columns of both frames. -/
def curMat : Matrix (c' ⊕ c') (c' ⊕ c') ℂ :=
  diagonal fun z => match z with
    | Sum.inl y => if cur y then 1 else 0
    | Sum.inr y => if cur y then 1 else 0

/-- **The joint linear conditions.** -/
def jointG (H : Matrix (c' ⊕ c') (c' ⊕ c') ℂ × Matrix (c' ⊕ c') (c' ⊕ c') ℂ)
    (prev : Fin n → c' ⊕ c' → ℂ) :
    Matrix ((c' ⊕ c') ⊕ (c' ⊕ c') ⊕ (c' ⊕ c') ⊕ (Fin n × Fin 2)) (c' ⊕ c') ℂ :=
  fun r => match r with
    | Sum.inl z => (H.1 * (projF 0 - projF 1) : Matrix (c' ⊕ c') (c' ⊕ c') ℂ) z
    | Sum.inr (Sum.inl z) => ((H.1 - H.2) * projF 0 : Matrix (c' ⊕ c') (c' ⊕ c') ℂ) z
    | Sum.inr (Sum.inr (Sum.inl z)) =>
      (curMat cur * H.1 * projF 0 : Matrix (c' ⊕ c') (c' ⊕ c') ℂ) z
    | Sum.inr (Sum.inr (Sum.inr (l, j))) => star (projF j *ᵥ prev l) ᵥ* (H.1 * projF 0)

/-- The quadratic form `(a₁, 0)ᴴ M (a₁, 0)`. -/
def jointQ (H : Matrix (c' ⊕ c') (c' ⊕ c') ℂ × Matrix (c' ⊕ c') (c' ⊕ c') ℂ) :
    Matrix (c' ⊕ c') (c' ⊕ c') ℂ :=
  projF 0 * H.1 * projF 0

variable (n) in
/-- **The two-frame selection.** -/
def jointSel : (Matrix (c' ⊕ c') (c' ⊕ c') ℂ × Matrix (c' ⊕ c') (c' ⊕ c') ℂ) ×
    (Fin n → c' ⊕ c' → ℂ) × ℝ → c' ⊕ c' → ℂ :=
  genSel (fun z => jointG cur z.1 z.2.1) (fun z => jointQ z.1) (fun z => z.2.2)

omit [DecidablePred cur] in
theorem projF_mulVec (j : Fin 2) (a : c' ⊕ c' → ℂ) :
    projF j *ᵥ a = fun z => match z with
      | Sum.inl y => if j = 0 then a (Sum.inl y) else 0
      | Sum.inr y => if j = 0 then 0 else a (Sum.inr y) := by
  funext z
  rcases z with y | y <;> simp [projF, mulVec_diagonal]

omit [Fintype c'] [DecidablePred cur] in
theorem projF_herm (j : Fin 2) : (projF (c' := c') j)ᴴ = projF j := by
  simp only [projF, diagonal_conjTranspose]
  congr 1
  funext z
  rcases z with y | y <;> by_cases h : j = 0 <;> simp [h]

variable {ι : Type*}

theorem fromCols_mulVec_projF (Y₁ Y₂ : Matrix ι c' ℂ) (a : c' ⊕ c' → ℂ) :
    fromCols Y₁ Y₂ *ᵥ (projF 0 *ᵥ a) = Y₁ *ᵥ fstV a ∧
      fromCols Y₁ Y₂ *ᵥ (projF 1 *ᵥ a) = Y₂ *ᵥ sndV a := by
  constructor <;> rw [projF_mulVec] <;> funext i <;>
    simp [mulVec, dotProduct, Fintype.sum_sum_type, fstV, sndV, fromCols]

end BlockBand.SourceProcess.CoupledFrames
