module

public import BlockBand.External.PSSS.NativeLaw
public import BlockBand.External.PSSS.Proof
public import BlockBand.Foundations.Spectral.OrderedEigenpairs

/-!
# The Peled–Schenker–Shamis–Sodin (PSSS) bound, as a hypothesis

`SourceContract` is the cited theorem of PSSS, used as an explicit hypothesis, never an axiom
or typeclass. One absolute strictly positive real `C` is chosen before all block
numbers, positive block sizes, arbitrary deterministic Hermitian deformations
(without a norm bound), real endpoints and positive factorial orders. Empty
block families are permitted. There is no asymptotic limit or physical ring law.

The matrix-law adapters in `NativeLaw` are proved, not assumed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.External.PSSS

open MeasureTheory ProbabilityTheory

universe u

/-- The number of eigenvalues of a Hermitian matrix in `I`, counted with multiplicity.
No phase choice or simple-spectrum hypothesis is involved. The increasing rank
is the `Fin.rev` enumeration (`increasingEigenvalue`). -/
def eigenCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (I : Set ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i =>
    BlockBand.Foundations.Spectral.increasingEigenvalue A.2 i ∈ I).card

/-- The dimension bound for the count, for every finite Hermitian
matrix and every set. This is deterministic and uniform in the matrix and set. -/
theorem eigenCount_le_dimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (I : Set ℝ) : eigenCount A I ≤ Fintype.card ι := by
  classical
  unfold eigenCount
  simpa using Finset.card_filter_le (s := Finset.univ)
    (p := fun i => BlockBand.Foundations.Spectral.increasingEigenvalue A.2 i ∈ I)

/-- The finite source dimension is exactly the sum of all block sizes, including
zero when the family is empty. -/
theorem blockGUE_dimension {k : ℕ} (d : Fin k → ℕ) :
    Fintype.card (BlockGUE.Index d) = ∑ j, d j := by
  simp [BlockGUE.Index]

/-- Multiplicity count of the independently normalized block-GUE noise
plus the specified deterministic deformation. Its law is exactly `M.P`. -/
def BlockGUE.intervalCount {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law d hd) (A₀ : HermitianMatrix (BlockGUE.Index d))
    (I : Set ℝ) (ω : M.Ω) : ℕ :=
  eigenCount (BlockGUE.deformed M A₀ ω) I

/-- Count boundedness uses the finite spectrum and does not assume a
PSSS moment estimate. -/
theorem BlockGUE.intervalCount_le_dimension {k : ℕ} {d : Fin k → ℕ}
    {hd : ∀ j, 0 < d j} (M : BlockGUE.Law d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d)) (I : Set ℝ) (ω : M.Ω) :
    BlockGUE.intervalCount M A₀ I ω ≤ Fintype.card (BlockGUE.Index d) :=
  eigenCount_le_dimension _ _

/-- Exact cited PSSS boundary at its independent block-GUE scope.

The constant is absolute and precedes dimensions, deformation, endpoints and
positive orders. The integrability field covers all orders and all endpoints,
so a totalized Bochner integral cannot make the bound vacuous. All randomness
and entry variances are fixed by `BlockGUE.Law`; no arbitrary law predicate or
paper-internal conclusion appears in this contract. The proved witness
is recorded in the task packet, but not imported or asserted here. -/
structure SourceContract where
  C : ℝ
  C_pos : 0 < C
  factorialIntegrable :
    ∀ {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
      (M : BlockGUE.Law.{u} d hd) (A₀ : HermitianMatrix (BlockGUE.Index d))
      (a b : ℝ) (r : ℕ),
      Integrable (factorialCount (BlockGUE.intervalCount M A₀ (Set.Icc a b)) r) M.P
  factorialBound :
    ∀ {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
      (M : BlockGUE.Law.{u} d hd) (A₀ : HermitianMatrix (BlockGUE.Index d))
      (a b : ℝ), a ≤ b → ∀ r : ℕ, 1 ≤ r →
      FactorialMomentBound M.P (BlockGUE.intervalCount M A₀ (Set.Icc a b))
        (Fintype.card (BlockGUE.Index d)) (b - a) C r

/-- Transport a count estimate to an identically distributed
count on another probability space, with the same positive constant, dimension,
interval and factorial order. This generic adapter asserts no physical law. -/
theorem SourceContract.factorialBound_transport (source : SourceContract.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd) (A₀ : HermitianMatrix (BlockGUE.Index d))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {count : Ω → ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (hlaw : IdentDistrib count (BlockGUE.intervalCount M A₀ (Set.Icc a b)) μ M.P)
    (r : ℕ) (hr : 1 ≤ r) :
    FactorialMomentBound μ count (Fintype.card (BlockGUE.Index d))
      (b - a) source.C r :=
  factorialMomentBound_transport hlaw (source.factorialBound hd M A₀ a b hab r hr)

end BlockBand.External.PSSS
