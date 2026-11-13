module

public import BlockBand.SourceProcess.ModelExist.KerProj
public import BlockBand.SourceProcess.EigenSelConstruct.FirstNZ
public import BlockBand.SourceProcess.EigenSelConstruct.Exist
public import BlockBand.SourceProcess.EigenSelConstruct.Lam
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# The measurable eigenvector selection: construction and measurability

The selection `eigSel` chooses, step by step, the normalized first nonzero column of the projection
onto the vectors that are eigenvectors for the `k`-th sorted eigenvalue and orthogonal to the
earlier choices; each step is a measurable function of the matrix.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.EigenSelConstruct
open Matrix MeasureTheory BlockBand.SourceProcess.ModelExist

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The stacked linear conditions `(A - λ_k) x = 0`, `⟨W l, x⟩ = 0`. -/
def condMat (k : Fin (Fintype.card n)) (A : Matrix n n ℂ) (W : Fin (Fintype.card n) → n → ℂ) :
    Matrix (n ⊕ Fin (Fintype.card n)) n ℂ :=
  fromRows (A - ((lam k A : ℝ) : ℂ) • 1) (Matrix.of fun l y => star (W l y))

/-- The columns of a square matrix, enumerated by `Fin (card n)`. -/
def cols (P : Matrix n n ℂ) : Fin (Fintype.card n) → n → ℂ :=
  fun i x => P x ((Fintype.equivFin n).symm i)

/-- The `k`-th selection step: the normalized first nonzero column of the projection onto
`ker (condMat k A W)`. -/
def step (k : Fin (Fintype.card n)) (A : Matrix n n ℂ) (W : Fin (Fintype.card n) → n → ℂ) :
    n → ℂ :=
  firstNZ (Fintype.card n) (cols (specProj (condMat k A W)))

/-- The vectors chosen after `k` steps (zero at the indices `≥ k`). -/
def vecs (A : Matrix n n ℂ) : ℕ → Fin (Fintype.card n) → n → ℂ
  | 0 => 0
  | k + 1 => fun j => if j.val = k then step j A (vecs A k) else vecs A k j

/-- **The selection** `V A x k = (k-th selected vector)_x`. -/
def eigSel (A : n → n → ℂ) : n → Fin (Fintype.card n) → ℂ :=
  fun x k => vecs (Matrix.of A) (Fintype.card n) k x

/-!
## Measurability
-/

theorem measurable_condMat (k : Fin (Fintype.card n)) {f : Matrix n n ℂ → Fin (Fintype.card n) → n → ℂ}
    (hf : Measurable f) : Measurable fun A => condMat k A (f A) := by
  refine Measurable.of_eval_matrix _ fun r y => ?_
  rcases r with x | l
  · simp only [condMat, fromRows_apply_inl, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact Matrix.measurable_apply.sub
      ((Complex.measurable_ofReal.comp (measurable_lam k)).mul measurable_const)
  · simp only [condMat, fromRows_apply_inr, of_apply]
    exact Complex.continuous_conj.measurable.comp ((hf.eval (a := l)).eval (a := y))

omit [DecidableEq n] in
theorem measurable_cols : Measurable (cols : Matrix n n ℂ → Fin (Fintype.card n) → n → ℂ) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ => Matrix.measurable_apply

theorem measurable_step (k : Fin (Fintype.card n)) {f : Matrix n n ℂ → Fin (Fintype.card n) → n → ℂ}
    (hf : Measurable f) : Measurable fun A => step k A (f A) :=
  (measurable_firstNZ _).comp (measurable_cols.comp (measurable_specProj.comp
    (measurable_condMat k hf)))

theorem measurable_vecs : (k : ℕ) → Measurable fun A : Matrix n n ℂ => vecs A k
  | 0 => measurable_const
  | k + 1 => by
    refine Measurable.of_eval fun j => ?_
    by_cases hj : j.val = k
    · simp only [vecs, hj, ↓reduceIte]
      exact measurable_step j (measurable_vecs k)
    · simp only [vecs, hj, ↓reduceIte]
      exact (measurable_pi_apply j).comp (measurable_vecs k)

theorem measurable_eigSel : Measurable (eigSel (n := n)) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun k => ?_
  exact (measurable_pi_apply x).comp ((measurable_pi_apply k).comp
    ((measurable_vecs (Fintype.card n)).comp (measurable_of n n ℂ)))

/-!
## Specification
-/

theorem condMat_mulVec_eq_zero {k : Fin (Fintype.card n)} {A : Matrix n n ℂ}
    {W : Fin (Fintype.card n) → n → ℂ} {x : n → ℂ} :
    condMat k A W *ᵥ x = 0 ↔
      A *ᵥ x = ((lam k A : ℝ) : ℂ) • x ∧ ∀ l, star (W l) ⬝ᵥ x = 0 := by
  rw [condMat, fromRows_mulVec]
  constructor
  · intro h
    refine ⟨?_, fun l => ?_⟩
    · have h1 : (A - ((lam k A : ℝ) : ℂ) • 1) *ᵥ x = 0 := funext fun y => congrFun h (Sum.inl y)
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
      exact h1
    · have h2 := congrFun h (Sum.inr l)
      simpa [Matrix.mulVec, dotProduct] using h2
  · rintro ⟨h1, h2⟩
    funext r
    rcases r with y | l
    · simp [Matrix.sub_mulVec, Matrix.smul_mulVec, h1]
    · have := h2 l
      simpa [Matrix.mulVec, dotProduct] using this

end BlockBand.SourceProcess.EigenSelConstruct
