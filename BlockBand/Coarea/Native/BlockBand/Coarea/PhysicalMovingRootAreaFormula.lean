module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalMovingSchurCover
public import BlockBand.Coarea.Native.BlockBand.Coarea.Crossing
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# One-dimensional area formula for physical moving Schur roots

For fixed physical block data and one pole-free energy interval, the scalar
coordinate used in the final coarea step is the increasingly ordered Schur
eigenvalue `ζᵣ(E)`.  The Loewner contraction makes each such
branch injective on the interval.  Consequently Mathlib's one-dimensional
Jacobian theorem applies directly.

The final theorem sums the branchwise identities and packages them with
`physicalMovingSchur_globalCover`.  Thus the analytic scalar area formula and
the set-theoretic statement that every fixed-rank physical root is represented
exactly once are available together.  The Hellmann–Feynman theorem at
the end identifies the absolute scalar Jacobian with the positive Schur-clock
quadratic form at a simple crossing.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal ComplexOrder MatrixOrder InnerProductSpace

/-- The scalar `ζ` coordinate on the `r`-th increasingly ordered physical
moving-Schur branch. -/
def physicalMovingSchurZeta
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian)
    (r : Fin (Fintype.card m)) (E : ℝ) : ℝ :=
  orderedEigenvalue (physicalSchurFamily A B D hA hD E) r

/-- The physical Loewner contraction makes every ordered scalar branch
injective on a pole-free interval.  This is stronger than uniqueness of the
zero: it is the injectivity needed by the one-dimensional area formula. -/
theorem physicalMovingSchurZeta_injOn
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) {I : Set ℝ}
    (hloewner : ∀ E₁ ∈ I, ∀ E₂ ∈ I, E₁ < E₂ →
      physicalSchurMatrix A B D E₂ ≤
        physicalSchurMatrix A B D E₁ - ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (r : Fin (Fintype.card m)) :
    Set.InjOn (physicalMovingSchurZeta A B D hA hD r) I := by
  let hcontract := physicalSchurFamily_contractsOn_of_loewner
    A B D hA hD hloewner
  intro E₁ hE₁ E₂ hE₂ heq
  rcases lt_trichotomy E₁ E₂ with hlt | he | hgt
  · have hc := hcontract r E₁ hE₁ E₂ hE₂ hlt
    change physicalMovingSchurZeta A B D hA hD r E₂ ≤
      physicalMovingSchurZeta A B D hA hD r E₁ - (E₂ - E₁) at hc
    rw [heq] at hc
    linarith
  · exact he
  · have hc := hcontract r E₂ hE₂ E₁ hE₁ hgt
    change physicalMovingSchurZeta A B D hA hD r E₁ ≤
      physicalMovingSchurZeta A B D hA hD r E₂ - (E₁ - E₂) at hc
    rw [heq] at hc
    linarith

/-- Differentiability and monotonicity make the scalar branch image of a
measurable pole-free interval measurable. -/
theorem measurableSet_physicalMovingSchurZeta_image
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) {I : Set ℝ}
    (hI : MeasurableSet I)
    (hloewner : ∀ E₁ ∈ I, ∀ E₂ ∈ I, E₁ < E₂ →
      physicalSchurMatrix A B D E₂ ≤
        physicalSchurMatrix A B D E₁ - ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (r : Fin (Fintype.card m)) (ζ' : ℝ → ℝ)
    (hderiv : ∀ E ∈ I, HasDerivWithinAt
      (physicalMovingSchurZeta A B D hA hD r) (ζ' E) I E) :
    MeasurableSet (physicalMovingSchurZeta A B D hA hD r '' I) := by
  exact MeasureTheory.measurable_image_of_fderivWithin hI
    (fun E hE => (hderiv E hE).hasFDerivWithinAt)
    (physicalMovingSchurZeta_injOn A B D hA hD hloewner r)

/-- One-dimensional scalar-`ζ` area formula on a pole-free interval.  The
right-hand side contains the absolute crossing derivative. -/
theorem lintegral_physicalMovingSchurZeta_image
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) {I : Set ℝ}
    (hI : MeasurableSet I)
    (hloewner : ∀ E₁ ∈ I, ∀ E₂ ∈ I, E₁ < E₂ →
      physicalSchurMatrix A B D E₂ ≤
        physicalSchurMatrix A B D E₁ - ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (r : Fin (Fintype.card m)) (ζ' : ℝ → ℝ)
    (hderiv : ∀ E ∈ I, HasDerivWithinAt
      (physicalMovingSchurZeta A B D hA hD r) (ζ' E) I E)
    (g : ℝ → ℝ≥0∞) :
    (∫⁻ ζ in physicalMovingSchurZeta A B D hA hD r '' I, g ζ) =
      ∫⁻ E in I, ENNReal.ofReal |ζ' E| *
        g (physicalMovingSchurZeta A B D hA hD r E) := by
  exact MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul hI hderiv
    (physicalMovingSchurZeta_injOn A B D hA hD hloewner r) g

/-- Summing the scalar area formula over all increasingly ordered Schur
branches on one pole-free interval. -/
theorem tsum_lintegral_physicalMovingSchurZeta_image
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) {I : Set ℝ}
    (hI : MeasurableSet I)
    (hloewner : ∀ E₁ ∈ I, ∀ E₂ ∈ I, E₁ < E₂ →
      physicalSchurMatrix A B D E₂ ≤
        physicalSchurMatrix A B D E₁ - ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (ζ' : Fin (Fintype.card m) → ℝ → ℝ)
    (hderiv : ∀ r E, E ∈ I → HasDerivWithinAt
      (physicalMovingSchurZeta A B D hA hD r) (ζ' r E) I E)
    (g : Fin (Fintype.card m) → ℝ → ℝ≥0∞) :
    (∑' r, ∫⁻ ζ in physicalMovingSchurZeta A B D hA hD r '' I, g r ζ) =
      ∑' r, ∫⁻ E in I, ENNReal.ofReal |ζ' r E| *
        g r (physicalMovingSchurZeta A B D hA hD r E) := by
  apply tsum_congr
  intro r
  exact lintegral_physicalMovingSchurZeta_image A B D hA hD hI hloewner
    r (ζ' r) (hderiv r) (g r)

/-- The analytic scalar area formula together with the exact physical
fixed-rank root cover.  The first component is the branch sum with its absolute
Jacobian; the second component says that the branch crossings represent every
physical root in the chosen rank sector exactly once and that no branch
contributes two roots on the interval. -/
theorem physicalMovingRoot_areaFormula_globalCover
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (I : Set ℝ)
    (α : Fin (Fintype.card (m ⊕ n)))
    (hpoleFree : ∀ E ∈ I, IsUnit (physicalExteriorPencil D E).det)
    (hI : MeasurableSet I)
    (hloewner : ∀ E₁ ∈ I, ∀ E₂ ∈ I, E₁ < E₂ →
      physicalSchurMatrix A B D E₂ ≤
        physicalSchurMatrix A B D E₁ - ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (hsimple : ∀ E ∈ I,
      Function.Injective (orderedEigenvalue
        (physicalSchurFamily A B D hA hD E)))
    (ζ' : Fin (Fintype.card m) → ℝ → ℝ)
    (hderiv : ∀ r E, E ∈ I → HasDerivWithinAt
      (physicalMovingSchurZeta A B D hA hD r) (ζ' r E) I E)
    (g : Fin (Fintype.card m) → ℝ → ℝ≥0∞) :
    ((∑' r, ∫⁻ ζ in physicalMovingSchurZeta A B D hA hD r '' I, g r ζ) =
        ∑' r, ∫⁻ E in I, ENNReal.ofReal |ζ' r E| *
          g r (physicalMovingSchurZeta A B D hA hD r E)) ∧
      (Function.Bijective
          (physicalFixedRankEigenEnergyMap A B D hA hD I α hpoleFree) ∧
        ∀ p q : MovingFixedRankSchurCrossing
            (physicalSchurFamily A B D hA hD) I
            (fun E => negativeEigenvalueCount
              (physicalExteriorFamily D hD E).property) α.val,
          p.1.1 = q.1.1 → p.1.2 = q.1.2) := by
  exact ⟨tsum_lintegral_physicalMovingSchurZeta_image
      A B D hA hD hI hloewner ζ' hderiv g,
    physicalMovingSchur_globalCover
      A B D hA hD I α hpoleFree hloewner hsimple⟩

/-- Sum the scalar change-of-variables identities over a countable family
of pole-free intervals and retain the exact fixed-rank global cover on every
interval.  This is the form used after decomposing the energy axis at the
exterior poles. -/
theorem physicalMovingRoot_areaFormula_poleIntervals
    {κ m n : Type*} [Countable κ] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (I : κ → Set ℝ)
    (α : Fin (Fintype.card (m ⊕ n)))
    (hpoleFree : ∀ j E, E ∈ I j → IsUnit (physicalExteriorPencil D E).det)
    (hI : ∀ j, MeasurableSet (I j))
    (hloewner : ∀ j E₁, E₁ ∈ I j → ∀ E₂, E₂ ∈ I j → E₁ < E₂ →
      physicalSchurMatrix A B D E₂ ≤
        physicalSchurMatrix A B D E₁ - ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (hsimple : ∀ j E, E ∈ I j →
      Function.Injective (orderedEigenvalue
        (physicalSchurFamily A B D hA hD E)))
    (ζ' : κ → Fin (Fintype.card m) → ℝ → ℝ)
    (hderiv : ∀ j r E, E ∈ I j → HasDerivWithinAt
      (physicalMovingSchurZeta A B D hA hD r) (ζ' j r E) (I j) E)
    (g : κ → Fin (Fintype.card m) → ℝ → ℝ≥0∞) :
    ((∑' j, ∑' r,
        ∫⁻ ζ in physicalMovingSchurZeta A B D hA hD r '' I j, g j r ζ) =
      ∑' j, ∑' r, ∫⁻ E in I j, ENNReal.ofReal |ζ' j r E| *
        g j r (physicalMovingSchurZeta A B D hA hD r E)) ∧
      ∀ j,
        Function.Bijective
            (physicalFixedRankEigenEnergyMap
              A B D hA hD (I j) α (hpoleFree j)) ∧
          ∀ p q : MovingFixedRankSchurCrossing
              (physicalSchurFamily A B D hA hD) (I j)
              (fun E => negativeEigenvalueCount
                (physicalExteriorFamily D hD E).property) α.val,
            p.1.1 = q.1.1 → p.1.2 = q.1.2 := by
  constructor
  · apply tsum_congr
    intro j
    exact tsum_lintegral_physicalMovingSchurZeta_image
      A B D hA hD (hI j) (hloewner j) (ζ' j) (hderiv j) (g j)
  · intro j
    exact physicalMovingSchur_globalCover A B D hA hD (I j) α
      (hpoleFree j) (hloewner j) (hsimple j)

/-- The positive scalar Jacobian associated with a normalized Schur crossing
vector. -/
def physicalMovingRootCrossingJacobian
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (T : Matrix n m ℂ) (v : m → ℂ) : ℝ :=
  (star v ⬝ᵥ (schurClock T *ᵥ v)).re

/-- At a normalized simple physical Schur crossing, Hellmann–Feynman gives
both the signed derivative and its absolute Jacobian.  The latter is exactly
the positive Schur-clock quadratic form appearing in the coarea density. -/
theorem physicalMovingSchurZeta_crossing_derivative_abs
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian)
    (r : Fin (Fintype.card m)) (T : Matrix n m ℂ)
    (v : ℝ → m → ℂ) (v' : m → ℂ) (ζ' E : ℝ)
    (hsimple : SimpleHermitianEigenpair
      (physicalSchurMatrix A B D E)
      (physicalMovingSchurZeta A B D hA hD r E) (v E))
    (hAderiv : HasDerivAt (physicalSchurMatrix A B D)
      (-(schurClock T)) E)
    (hvderiv : HasDerivAt v v' E)
    (hζderiv : HasDerivAt
      (physicalMovingSchurZeta A B D hA hD r) ζ' E)
    (heigenpair : ∀ s : ℝ,
      physicalSchurMatrix A B D s *ᵥ v s =
        (physicalMovingSchurZeta A B D hA hD r s : ℂ) • v s) :
    ζ' = -physicalMovingRootCrossingJacobian T (v E) ∧
      |ζ'| = physicalMovingRootCrossingJacobian T (v E) := by
  have hcross := hellmannFeynman_schurClockCrossing T hsimple hAderiv
    hvderiv hζderiv heigenpair
  have hsigned := congrArg Complex.re hcross
  simp only [Complex.ofReal_re] at hsigned
  have hsigned' :
      ζ' = -physicalMovingRootCrossingJacobian T (v E) := by
    simpa [physicalMovingRootCrossingJacobian] using hsigned
  have hv0 : v E ≠ 0 := by
    intro hv
    have hn := hsimple.normalized
    rw [hv] at hn
    simp at hn
  have hpos : 0 < physicalMovingRootCrossingJacobian T (v E) := by
    exact (Complex.pos_iff.mp (schurClock_quadratic_pos T hv0)).1
  constructor
  · exact hsigned'
  · rw [hsigned', abs_neg, abs_of_pos hpos]

end CoareaNative.BlockBand
