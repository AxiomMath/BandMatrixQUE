module

public import BlockBand.Coarea.Native.BlockBand.Coarea.MovingSchurRankSector
public import BlockBand.Coarea.Native.BlockBand.Spectral.Measurable.OrderedSpectrum

/-!
# Intervalwise cover by moving Schur eigenvalue branches

This module isolates the global one-dimensional part of Claim 3 in the RBM
coarea argument.  On one pole-free energy interval, a quantitative spectral
contraction makes each increasingly ordered Schur eigenvalue branch cross zero
at most once.  Simplicity prevents two ordered branches from representing the
same crossing.  Consequently the finite branch crossing space covers the zero
energies bijectively, including after restriction to the paper's additive
fixed-rank sector.

The contraction estimate is explicit rather than inferred from derivatives of
chosen eigenvectors.  Downstream it is the min–max consequence of
`A(E₂) ≤ A(E₁) - (E₂-E₁)I`.  Thus no monotonicity of an unproved eigenvector
branch is assumed here.  Coverage of physical eigenvalues across exterior
poles additionally needs the moving Schur determinant identity and pole
exclusion; this module makes no such global assertion.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Filter Set
open scoped Topology

/-- A zero of one increasingly ordered eigenvalue branch on an energy set. -/
abbrev MovingSchurBranchCrossing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → HermitianMatrix ι) (I : Set ℝ) :=
  {p : Fin (Fintype.card ι) × ℝ //
    p.2 ∈ I ∧ orderedEigenvalue (A p.2) p.1 = 0}

/-- An energy in the interval at which the moving Hermitian matrix has a zero
ordered eigenvalue. -/
abbrev MovingSchurCrossingEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → HermitianMatrix ι) (I : Set ℝ) :=
  {E : ℝ // E ∈ I ∧ ∃ r, orderedEigenvalue (A E) r = 0}

/-- Forget the ordered branch label of a Schur crossing. -/
def movingSchurCrossingEnergyMap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → HermitianMatrix ι) (I : Set ℝ) :
    MovingSchurBranchCrossing A I → MovingSchurCrossingEnergy A I :=
  fun p => ⟨p.1.2, p.2.1, p.1.1, p.2.2⟩

/-- The quantitative min–max estimate used between two consecutive exterior
poles.  It says that every *ordered* branch falls by at least the elapsed
energy. -/
def OrderedSpectrumContractsOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → HermitianMatrix ι) (I : Set ℝ) : Prop :=
  ∀ r E₁, E₁ ∈ I → ∀ E₂, E₂ ∈ I → E₁ < E₂ →
    orderedEigenvalue (A E₂) r ≤
      orderedEigenvalue (A E₁) r - (E₂ - E₁)

/-- Under the min–max contraction estimate, one ordered Schur branch has at
most one zero on a pole-free interval. -/
theorem orderedSchurBranch_zero_unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → HermitianMatrix ι} {I : Set ℝ}
    (hcontract : OrderedSpectrumContractsOn A I)
    {r : Fin (Fintype.card ι)} {E₁ E₂ : ℝ}
    (hE₁ : E₁ ∈ I) (hE₂ : E₂ ∈ I)
    (hz₁ : orderedEigenvalue (A E₁) r = 0)
    (hz₂ : orderedEigenvalue (A E₂) r = 0) :
    E₁ = E₂ := by
  rcases lt_trichotomy E₁ E₂ with hlt | heq | hgt
  · have h := hcontract r E₁ hE₁ E₂ hE₂ hlt
    rw [hz₁, hz₂] at h
    linarith
  · exact heq
  · have h := hcontract r E₂ hE₂ E₁ hE₁ hgt
    rw [hz₁, hz₂] at h
    linarith

/-- At a simple crossing, continuity isolates the zero branch from every other
ordered eigenvalue in one common neighborhood.

This is the precise local control of the remaining branches used before the
intervalwise cover.  Simplicity is expressed without choosing eigenvectors:
the ordered spectrum at the crossing is injective. -/
theorem eventually_other_orderedSchurBranches_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → HermitianMatrix ι} {t : ℝ}
    (hA : ContinuousAt A t)
    (hsimple : Function.Injective (orderedEigenvalue (A t)))
    {r : Fin (Fintype.card ι)}
    (hr : orderedEigenvalue (A t) r = 0) :
    ∀ᶠ s in 𝓝 t, ∀ j, j ≠ r → orderedEigenvalue (A s) j ≠ 0 := by
  rw [eventually_all]
  intro j
  by_cases hj : j = r
  · exact Filter.Eventually.of_forall (fun _ hne => (hne hj).elim)
  · have hj0 : orderedEigenvalue (A t) j ≠ 0 := by
      intro hzero
      apply hj
      exact hsimple (hzero.trans hr.symm)
    exact ((continuous_orderedEigenvalue j).continuousAt.comp hA).eventually_ne hj0
      |>.mono (fun _ hs _ => hs)

/-- On a simple-spectrum interval, forgetting the ordered branch label is a
bijection from branch crossings to zero energies.  Surjectivity is
finite branch coverage; injectivity says that no energy is counted twice.
Together with `orderedSchurBranch_zero_unique`, every branch contributes at
most one energy as well. -/
theorem movingSchurCrossingEnergyMap_bijective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → HermitianMatrix ι} {I : Set ℝ}
    (hsimple : ∀ E ∈ I, Function.Injective (orderedEigenvalue (A E))) :
    Function.Bijective (movingSchurCrossingEnergyMap A I) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply hsimple p.1.2 p.2.1
      change orderedEigenvalue (A p.1.2) p.1.1 =
        orderedEigenvalue (A p.1.2) q.1.1
      rw [p.2.2]
      have hE : p.1.2 = q.1.2 := congrArg Subtype.val hpq
      simpa [hE] using q.2.2.symm
    · exact congrArg Subtype.val hpq
  · intro E
    rcases E.2.2 with ⟨r, hr⟩
    exact ⟨⟨(r, E.1), E.2.1, hr⟩, Subtype.ext rfl⟩

/-- The crossings in a fixed rank sector.  The equation is total
and subtraction-free: exterior inertia plus retained inertia plus the selected
zero equals the one-based physical rank. -/
abbrev MovingFixedRankSchurCrossing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → HermitianMatrix ι) (I : Set ℝ)
    (exteriorInertia : ℝ → ℕ) (α : ℕ) :=
  {p : Fin (Fintype.card ι) × ℝ //
    p.2 ∈ I ∧ orderedEigenvalue (A p.2) p.1 = 0 ∧
      exteriorInertia p.2 + negativeEigenvalueCount (A p.2).property + 1 = α + 1}

/-- The zero energies belonging to a fixed additive rank sector. -/
abbrev MovingFixedRankSchurEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → HermitianMatrix ι) (I : Set ℝ)
    (exteriorInertia : ℝ → ℕ) (α : ℕ) :=
  {E : ℝ // E ∈ I ∧
    (∃ r, orderedEigenvalue (A E) r = 0) ∧
      exteriorInertia E + negativeEigenvalueCount (A E).property + 1 = α + 1}

/-- Forgetting the branch label preserves the exact additive rank sector. -/
def movingFixedRankSchurEnergyMap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → HermitianMatrix ι) (I : Set ℝ)
    (exteriorInertia : ℝ → ℕ) (α : ℕ) :
    MovingFixedRankSchurCrossing A I exteriorInertia α →
      MovingFixedRankSchurEnergy A I exteriorInertia α :=
  fun p => ⟨p.1.2, p.2.1, ⟨p.1.1, p.2.2.1⟩, p.2.2.2⟩

/-- Global intervalwise cover and no-double-counting in one fixed additive
rank sector.  Every sector energy is represented by exactly one ordered Schur
branch, provided the Schur spectrum is simple throughout the pole interval. -/
theorem movingFixedRankSchurEnergyMap_bijective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → HermitianMatrix ι} {I : Set ℝ}
    {exteriorInertia : ℝ → ℕ} {α : ℕ}
    (hsimple : ∀ E ∈ I, Function.Injective (orderedEigenvalue (A E))) :
    Function.Bijective
      (movingFixedRankSchurEnergyMap A I exteriorInertia α) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply hsimple p.1.2 p.2.1
      change orderedEigenvalue (A p.1.2) p.1.1 =
        orderedEigenvalue (A p.1.2) q.1.1
      rw [p.2.2.1]
      have hE : p.1.2 = q.1.2 := congrArg Subtype.val hpq
      simpa [hE] using q.2.2.1.symm
    · exact congrArg Subtype.val hpq
  · intro E
    rcases E.2.2.1 with ⟨r, hr⟩
    exact ⟨⟨(r, E.1), E.2.1, hr, E.2.2.2⟩, Subtype.ext rfl⟩

/-- Complete intervalwise cover/no-double-counting package in a fixed rank
sector.  The first conclusion says every sector energy has exactly one branch
label.  The second says a fixed ordered branch supplies at most one such
energy anywhere in the pole interval.  These are the two injectivity facts
needed before applying the one-dimensional area formula branch by branch. -/
theorem movingFixedRankSchur_globalCover
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → HermitianMatrix ι} {I : Set ℝ}
    {exteriorInertia : ℝ → ℕ} {α : ℕ}
    (hcontract : OrderedSpectrumContractsOn A I)
    (hsimple : ∀ E ∈ I, Function.Injective (orderedEigenvalue (A E))) :
    Function.Bijective
        (movingFixedRankSchurEnergyMap A I exteriorInertia α) ∧
      ∀ p q : MovingFixedRankSchurCrossing A I exteriorInertia α,
        p.1.1 = q.1.1 → p.1.2 = q.1.2 := by
  refine ⟨movingFixedRankSchurEnergyMap_bijective hsimple, ?_⟩
  intro p q hrank
  exact orderedSchurBranch_zero_unique hcontract p.2.1 q.2.1 p.2.2.1
    (hrank ▸ q.2.2.1)

end CoareaNative.BlockBand
