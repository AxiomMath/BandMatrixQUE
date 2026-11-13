module

public import BlockBand.Coarea.Native.BlockBand.Spectral.Ordered
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic

/-!
# Independent block-GUE noise

This file fixes the normalization used by the external PSSS counting theorem.  A family with block sizes `d j` acts on the
sigma type `Σ j, Fin (d j)`.  Entries joining distinct blocks vanish.  Inside
block `j`, the diagonal is real Gaussian with variance `1 / d j`, while each
strictly upper entry has independent real and imaginary components of variance
`1 / (2 d j)`.  All upper-triangular complex entries are jointly independent.

The structure is an explicit input, not an existence axiom: a user must supply
every probability and Gaussian-law field.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BlockGUE

/-- The coordinate space for a family of blocks. -/
abbrev Index {k : ℕ} (d : Fin k → ℕ) := Σ j, Fin (d j)

/-- The canonical finite ordering used to select upper-triangular entries. -/
def indexLE {k : ℕ} (d : Fin k → ℕ) (x y : Index d) : Prop :=
  (Fintype.equivFin (Index d) x).val ≤ (Fintype.equivFin (Index d) y).val

instance {k : ℕ} (d : Fin k → ℕ) (x y : Index d) : Decidable (indexLE d x y) :=
  by unfold indexLE; infer_instance

/-- Upper-triangular coordinates of the full block-diagonal noise matrix. -/
def UpperPair {k : ℕ} (d : Fin k → ℕ) :=
  {q : Index d × Index d // indexLE d q.1 q.2}

/-- Total variance of one within-block complex entry in the PSSS normalization. -/
def entryVariance {k : ℕ} (d : Fin k → ℕ) (x y : Index d) : ℝ :=
  if x.1 = y.1 then 1 / (d x.1 : ℝ) else 0

/-- Nonnegativity of the PSSS variance when all blocks are nonempty. -/
theorem entryVariance_nonneg {k : ℕ} {d : Fin k → ℕ}
    (hd : ∀ j, 0 < d j) (x y : Index d) : 0 ≤ entryVariance d x y := by
  unfold entryVariance
  split_ifs
  · exact one_div_nonneg.mpr (by exact_mod_cast (hd x.1).le)
  · exact le_rfl

/-- The PSSS block-GUE law at variance `1 / d_j` in block `j`.

The structure records the normalization and all independence assertions
used downstream.  It is separate from the ring law: conditioning
on the ring bonds produces a deterministic deformation plus a law of this
shape for its diagonal blocks. -/
structure Law {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) where
  Ω : Type*
  mΩ : MeasurableSpace Ω
  P : Measure Ω
  probability : IsProbabilityMeasure P
  G : Ω → Matrix (Index d) (Index d) ℂ
  hermitian : ∀ ω, (G ω).IsHermitian
  measurable_entry : ∀ x y, Measurable (fun ω => G ω x y)
  block_diagonal : ∀ x y, x.1 ≠ y.1 → ∀ᵐ ω ∂P, G ω x y = 0
  upper_independent :
    @iIndepFun Ω (UpperPair d) mΩ
      (fun _ => ℂ) (fun _ => Complex.measurableSpace)
      (fun q ω => G ω q.1.1 q.1.2) P
  diagonal_im_zero : ∀ x, ∀ᵐ ω ∂P, (G ω x x).im = 0
  diagonal_re_law : ∀ x,
    HasLaw (fun ω => (G ω x x).re)
      (gaussianReal 0 ⟨entryVariance d x x, entryVariance_nonneg hd x x⟩) P
  offdiag_components_independent : ∀ x y, indexLE d x y → x ≠ y → x.1 = y.1 →
    IndepFun (fun ω => (G ω x y).re) (fun ω => (G ω x y).im) P
  offdiag_re_law : ∀ x y, indexLE d x y → x ≠ y → x.1 = y.1 →
    HasLaw (fun ω => (G ω x y).re)
      (gaussianReal 0 ⟨entryVariance d x y / 2,
        div_nonneg (entryVariance_nonneg hd x y) (by norm_num)⟩) P
  offdiag_im_law : ∀ x y, indexLE d x y → x ≠ y → x.1 = y.1 →
    HasLaw (fun ω => (G ω x y).im)
      (gaussianReal 0 ⟨entryVariance d x y / 2,
        div_nonneg (entryVariance_nonneg hd x y) (by norm_num)⟩) P

attribute [instance] Law.mΩ Law.probability

/-- A sample of block-GUE noise is Hermitian. -/
theorem Law.isHermitian {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : Law d hd) (ω : M.Ω) : (M.G ω).IsHermitian := M.hermitian ω

end BlockGUE

end CoareaNative.BlockBand
