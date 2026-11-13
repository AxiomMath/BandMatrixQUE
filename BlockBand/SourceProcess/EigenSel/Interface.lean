module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# A Borel-measurable sorted orthonormal eigenbasis of Hermitian matrices

The statement `MeasurableEigenSelection`: Hermitian matrices admit a Borel-measurable choice of an
orthonormal eigenbasis ordered as `eigenvalues₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.EigenSel

open Matrix

/-- **A measurable sorted orthonormal eigenbasis.** For every finite index type `n` there is a
map `V` on the entry arrays `n → n → ℂ` (product Borel structure), Borel measurable, such that for every
Hermitian `A` the matrix `Matrix.of (V A)` has orthonormal columns and
`A * Matrix.of (V A) = Matrix.of (V A) * diagonal (eigenvalues₀)`. -/
def MeasurableEigenSelection : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n],
    ∃ V : (n → n → ℂ) → n → Fin (Fintype.card n) → ℂ, Measurable V ∧
      ∀ (A : Matrix n n ℂ) (hA : A.IsHermitian),
        (Matrix.of (V A))ᴴ * Matrix.of (V A) = 1 ∧
          A * Matrix.of (V A) = Matrix.of (V A) * diagonal (fun k => ((hA.eigenvalues₀ k : ℝ) : ℂ))

end BlockBand.SourceProcess.EigenSel
