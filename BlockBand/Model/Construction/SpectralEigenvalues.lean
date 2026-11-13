module

public import BlockBand.Model.Construction.OrderedSpectrum
public import BlockBand.Model.Observables

/-!
# Raw-matrix extension of the physical increasing spectrum

Borel measurable ordered eigenvalues on all raw site matrices: on Hermitian matrices the values
are the increasing eigenvalues, and non-Hermitian matrices are sent to zero. More generally, any
Borel function on the Hermitian subtype extends by a default value to a Borel function on all
matrices.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Hermitian matrices form a Borel set in the entrywise matrix topology. -/
theorem measurableSet_isHermitian :
    MeasurableSet {A : Matrix ι ι ℂ | A.IsHermitian} := by
  have hm : MeasurableSet {A : Matrix ι ι ℂ |
      ∀ x y, starRingEnd ℂ (A y x) = A x y} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro x
    apply MeasurableSet.iInter
    intro y
    exact measurableSet_eq_fun
      (Complex.continuous_conj.measurable.comp
        ((measurable_pi_apply x).comp (measurable_pi_apply y)))
      ((measurable_pi_apply y).comp (measurable_pi_apply x))
  have hs : {A : Matrix ι ι ℂ | A.IsHermitian} =
      {A : Matrix ι ι ℂ | ∀ x y, starRingEnd ℂ (A y x) = A x y} := by
    ext A
    constructor
    · intro h x y
      change A.conjTranspose = A at h
      exact congrFun (congrFun h x) y
    · intro h
      change A.conjTranspose = A
      ext x y
      exact h x y
  rw [hs]
  exact hm

/-- Increasing eigenvalues of raw H, zero outside the Hermitian locus. -/
def rawIncreasingEigenvalue (i : Fin (Fintype.card ι))
    (A : Matrix ι ι ℂ) : ℝ :=
  if h : A.IsHermitian then
    BlockBand.Foundations.Spectral.increasingEigenvalue h i else 0

/-- The raw extension agrees pointwise with the increasing spectrum on Hermitian matrices. -/
theorem rawIncreasingEigenvalue_eq (i : Fin (Fintype.card ι))
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    rawIncreasingEigenvalue i A =
      BlockBand.Foundations.Spectral.increasingEigenvalue hA i := by
  simp [rawIncreasingEigenvalue, hA]

/-- Each raw increasing eigenvalue is Borel measurable. -/
theorem measurable_rawIncreasingEigenvalue (i : Fin (Fintype.card ι)) :
    Measurable (rawIncreasingEigenvalue (ι := ι) i) := by
  classical
  let f : Matrix ι ι ℂ → ℝ := fun A =>
    if h : A ∈ {B : Matrix ι ι ℂ | B.IsHermitian} then
      BlockBand.Foundations.Spectral.increasingEigenvalue h i else 0
  have hm : Measurable f := by
    convert (measurable_increasingEigenvalue i).dite
      (g := fun _ => (0 : ℝ)) measurable_const measurableSet_isHermitian using 1
    funext A
    by_cases hA : A.IsHermitian
    · have he : A.conjTranspose = A := hA
      simp [f, hA]
      intro hn
      exact False.elim (hn he)
    · have he : ¬ A.conjTranspose = A := hA
      simp [f, hA]
      intro hp
      exact False.elim (he hp)
  have heq : rawIncreasingEigenvalue (ι := ι) i = f := by
    funext A
    by_cases hA : A.IsHermitian <;> simp [rawIncreasingEigenvalue, f, hA]
  rw [heq]
  exact hm

/-- Default extension from the Hermitian subtype to raw matrices. -/
def rawHermitianExtension {β : Type*} (f : HermitianMatrix ι → β) (default : β)
    (A : Matrix ι ι ℂ) : β :=
  if h : A.IsHermitian then f ⟨A, h⟩ else default

/-- The default extension equals its prescribed value on every Hermitian matrix. -/
theorem rawHermitianExtension_eq {β : Type*} (f : HermitianMatrix ι → β) (default : β)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    rawHermitianExtension f default A = f ⟨A, hA⟩ := by
  simp [rawHermitianExtension, hA]

/-- Extending a Borel function on the Hermitian subtype by a fixed default is Borel on all raw
matrices. -/
theorem measurable_rawHermitianExtension {β : Type*} [MeasurableSpace β]
    (f : HermitianMatrix ι → β) (hf : Measurable f) (default : β) :
    Measurable (rawHermitianExtension f default) := by
  classical
  let g : Matrix ι ι ℂ → β := fun A =>
    if h : A ∈ {B : Matrix ι ι ℂ | B.IsHermitian} then f ⟨A, h⟩ else default
  have hm : Measurable g := by
    convert hf.dite (g := fun _ => default) measurable_const measurableSet_isHermitian using 1
    funext A
    by_cases hA : A.IsHermitian
    · have he : A.conjTranspose = A := hA
      simp only [g, Set.mem_ofPred_eq, hA, dite_true]
      split_ifs with hp
      · rfl
      · exact False.elim (hp he)
    · have he : ¬ A.conjTranspose = A := hA
      simp only [g, Set.mem_ofPred_eq, hA, dite_false]
      split_ifs with hp
      · exact False.elim (he hp)
      · rfl
  have heq : rawHermitianExtension f default = g := by
    funext A
    by_cases hA : A.IsHermitian <;> simp [rawHermitianExtension, g, hA]
  rw [heq]
  exact hm

end BlockBand.Model.Construction
