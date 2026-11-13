module

public import BlockBand.Coarea.Native.BlockBand.Probability.GUEBlocks
public import BlockBand.Coarea.Native.BlockBand.Spectral.Measurable.Counts
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# PSSS factorial-count input

This is the interface for the external theorem: the unitary
Peled–Schenker–Shamis–Sodin factorial-count estimate.
The interface retains the exact normalization `G_j ~ GUE_{d_j}(1/d_j)`, an
arbitrary deterministic Hermitian deformation, multiplicity-counted interval
counts, and the falling-factorial convention.

The cited theorem is passed as an explicit value of `PSSSInput`; it is not
installed as an axiom or typeclass.  Downstream results derive their conclusions
from this interface and proved analytic identities.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

universe u

open MeasureTheory
open scoped ENNReal NNReal

/-- The deformed matrix in the exact PSSS block normalization. -/
def BlockGUE.deformed {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law d hd) (A₀ : HermitianMatrix (BlockGUE.Index d))
    (ω : M.Ω) : HermitianMatrix (BlockGUE.Index d) :=
  ⟨A₀.1 + M.G ω, A₀.2.add (M.hermitian ω)⟩

/-- The multiplicity-counted number of eigenvalues of the deformed ensemble in
`I`. -/
def BlockGUE.intervalCount {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law d hd) (A₀ : HermitianMatrix (BlockGUE.Index d))
    (I : Set ℝ) (ω : M.Ω) : ℕ :=
  eigenCount (BlockGUE.deformed M A₀ ω) I

/-- Statement of the external PSSS factorial-count theorem.

`C` is absolute.  `factorialCount` is uniform in the number and sizes of the
blocks, the deterministic deformation, the real interval, and the positive
falling-factorial order.  The interval length is written as `b-a`, exactly as
for `Icc a b`; the hypothesis `a ≤ b` prevents a negative right side. -/
structure PSSSInput where
  C : ℝ
  C_nonneg : 0 ≤ C
  factorialIntegrable :
    ∀ {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
      (M : BlockGUE.Law.{u} d hd)
      (A₀ : HermitianMatrix (BlockGUE.Index d))
      (a b : ℝ) (r : ℕ),
      Integrable (fun ω =>
        ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ)) M.P
  factorialCount :
    ∀ {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
      (M : BlockGUE.Law.{u} d hd)
      (A₀ : HermitianMatrix (BlockGUE.Index d))
      (a b : ℝ) (_hab : a ≤ b) (r : ℕ) (_hr : 1 ≤ r),
      ∫ ω, ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ) ∂M.P
        ≤ (C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) ^ r

/-- The interface's dimension is the sum of its block sizes. -/
theorem blockGUE_dimension {k : ℕ} (d : Fin k → ℕ) :
    Fintype.card (BlockGUE.Index d) = ∑ j, d j := by
  simp [BlockGUE.Index]

/-- Falling-factorial counts in the imported theorem are integrable;
this field prevents the totalized Bochner integral from making the bound
vacuous on a nonintegrable function. -/
theorem psss_factorialIntegrable (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (r : ℕ) :
    Integrable (fun ω =>
      ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ)) M.P :=
  input.factorialIntegrable hd M A₀ a b r

/-- The PSSS factorial-count bound, as a theorem about a `PSSSInput`. -/
theorem psss_factorialCount (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (hab : a ≤ b) (r : ℕ) (hr : 1 ≤ r) :
    ∫ ω, ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ) ∂M.P
      ≤ (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) ^ r :=
  input.factorialCount hd M A₀ a b hab r hr

end CoareaNative.BlockBand
