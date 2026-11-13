module

public import BlockBand.Model.Construction.OrderedSpectrum

/-!
# Borel measurability of the sorted eigenvalues

The `k`-th sorted eigenvalue, extended by `0` off the Hermitian matrices, is Borel measurable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.EigenSelConstruct
open Matrix MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `k`-th largest eigenvalue `eigenvalues₀ k`, extended by `0` off the Hermitian set. -/
def lam (k : Fin (Fintype.card n)) (A : Matrix n n ℂ) : ℝ :=
  if h : A.IsHermitian then h.eigenvalues₀ k else 0

theorem lam_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    lam k A = hA.eigenvalues₀ k := by
  simp [lam, hA]

omit [DecidableEq n] in
theorem measurableSet_hermitian : MeasurableSet {A : Matrix n n ℂ | A.IsHermitian} := by
  have : {A : Matrix n n ℂ | A.IsHermitian} = ⋂ x, ⋂ y, {A | star (A y x) = A x y} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h x y; exact congrFun (congrFun h x) y
    · intro h; ext x y; exact h x y
  rw [this]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
  exact measurableSet_eq_fun
    (Complex.continuous_conj.measurable.comp ((measurable_pi_apply x).comp (measurable_pi_apply y)))
    ((measurable_pi_apply y).comp (measurable_pi_apply x))

/-- **The sorted eigenvalues are Borel measurable** (via the continuity of the ordered
spectrum, `BlockBand.Model.Construction.measurable_increasingEigenvalue`). -/
theorem measurable_lam (k : Fin (Fintype.card n)) : Measurable (lam (n := n) k) := by
  refine measurable_of_restrict_of_restrict_compl measurableSet_hermitian ?_ ?_
  · have h : Measurable fun A : ({A : Matrix n n ℂ | A.IsHermitian} : Set (Matrix n n ℂ)) =>
        BlockBand.Foundations.Spectral.increasingEigenvalue A.2 k.rev :=
      BlockBand.Model.Construction.measurable_increasingEigenvalue (ι := n) k.rev
    have e : Set.domRestrict {A : Matrix n n ℂ | A.IsHermitian} (lam k) = fun A =>
        BlockBand.Foundations.Spectral.increasingEigenvalue A.2 k.rev := by
      funext A
      simp only [Set.domRestrict_apply, BlockBand.Foundations.Spectral.increasingEigenvalue,
        Fin.rev_rev]
      exact lam_eq A.2 k
    rw [e]
    exact h
  · have : Set.domRestrict {A : Matrix n n ℂ | A.IsHermitian}ᶜ (lam k) = fun _ => 0 := by
      funext A
      have hA : ¬ (A : Matrix n n ℂ).IsHermitian := A.2
      simp [lam, hA]
    rw [this]
    exact measurable_const

end BlockBand.SourceProcess.EigenSelConstruct
