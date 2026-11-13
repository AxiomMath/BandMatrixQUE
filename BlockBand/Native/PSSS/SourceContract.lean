module

public import BlockBand.External.PSSS.SourceStatement
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedAllOrderRoot

/-!
# Proof of the PSSS eigenvalue-count theorem

The eigenvalue-count theorem of PSSS (Peled–Schenker–Shamis–Sodin) in the form
`BlockBand.External.PSSS.SourceContract`, proved with no hypothesis, from
`correctedStrictPositivePSSSInput`. Block-GUE laws and eigenvalue counts of the statement are
identified with those of the proof.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Native.PSSS

open MeasureTheory ProbabilityTheory

universe u

/-- The law record `PSSSNative.BlockBand.BlockGUE.Law` of a supplied normalized block-GUE
law of the statement: same sample space, measure, noise matrix and every
Gaussian/independence field (normalization `G_j ~ GUE_{d_j}(1/d_j)`).
-/
def toNativeLaw {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockBand.External.PSSS.BlockGUE.Law.{u} d hd) :
    PSSSNative.BlockBand.BlockGUE.Law.{u} d hd where
  Ω := M.Ω
  mΩ := M.mΩ
  P := M.P
  probability := M.probability
  G := M.G
  hermitian := M.hermitian
  measurable_entry := M.measurable_entry
  block_diagonal := M.block_diagonal
  upper_independent := M.upper_independent
  diagonal_im_zero := M.diagonal_im_zero
  diagonal_re_law := M.diagonal_re_law
  offdiag_components_independent := M.offdiag_components_independent
  offdiag_re_law := M.offdiag_re_law
  offdiag_im_law := M.offdiag_im_law

/-- The two eigenvalue counts (of the statement and of the proof) agree for every finite
Hermitian matrix and every
set of reals (both count increasing eigenvalues `eigenvalues₀ ∘ Fin.rev` in the set).
-/
theorem eigenCount_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : BlockBand.External.PSSS.HermitianMatrix ι) (I : Set ℝ) :
    BlockBand.External.PSSS.eigenCount A I = PSSSNative.BlockBand.eigenCount A I := by
  classical
  unfold BlockBand.External.PSSS.eigenCount PSSSNative.BlockBand.eigenCount
  congr 1

/-- The deformed interval count of a supplied law equals the count of its record
`toNativeLaw M`, pointwise on the common sample space, for every deformation and every set.
-/
theorem intervalCount_eq {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockBand.External.PSSS.BlockGUE.Law.{u} d hd)
    (A₀ : BlockBand.External.PSSS.HermitianMatrix (BlockBand.External.PSSS.BlockGUE.Index d))
    (I : Set ℝ) :
    BlockBand.External.PSSS.BlockGUE.intervalCount M A₀ I =
      PSSSNative.BlockBand.BlockGUE.intervalCount (toNativeLaw M) A₀ I := by
  funext w
  exact eigenCount_eq _ I

/-- The source contract carried by a strictly positive PSSS input: same constant
`C > 0`; integrability and the factorial bound are the fields read through `toNativeLaw`
and `intervalCount_eq`, at every supplied law, deformation, interval and order.
-/
def ofStrictPositive (strict : PSSSNative.BlockBand.StrictPositivePSSSInput.{u}) :
    BlockBand.External.PSSS.SourceContract.{u} where
  C := strict.input.C
  C_pos := strict.C_pos
  factorialIntegrable := by
    intro k d hd M A₀ a b r
    have h := strict.factorialIntegrable hd (toNativeLaw M) A₀ a b r
    unfold BlockBand.External.PSSS.factorialCount
    rw [intervalCount_eq M A₀ (Set.Icc a b)]
    exact h
  factorialBound := by
    intro k d hd M A₀ a b hab r hr
    have h := strict.factorialCount hd (toNativeLaw M) A₀ a b hab r hr
    unfold BlockBand.External.PSSS.FactorialMomentBound BlockBand.External.PSSS.factorialCount
    rw [intervalCount_eq M A₀ (Set.Icc a b)]
    exact h

/-- The adapter keeps the constant exactly. -/
theorem ofStrictPositive_C (strict : PSSSNative.BlockBand.StrictPositivePSSSInput.{u}) :
    (ofStrictPositive strict).C = strict.input.C := rfl

/-- **PSSS Theorems 2–3, unitary case**, with no hypothesis: one absolute `C > 0`,
integrability of every falling-factorial count, and
`E[(N_{[a,b]})_r] ≤ (C d (b-a))^r` for every supplied independent normalized block-GUE law,
deterministic Hermitian deformation, `a ≤ b` and `r ≥ 1`.
The contract is a structure (data:
the constant `C`), so the constructor is a definition;
`nonempty_sourceContract` is its
propositional form.
-/
def sourceContract_holds : BlockBand.External.PSSS.SourceContract.{u} :=
  ofStrictPositive PSSSNative.BlockBand.PSSS.correctedStrictPositivePSSSInput.{u}

/-- Propositional form of `sourceContract_holds`: the PSSS source contract is
inhabited, in every universe of sample spaces.
-/
theorem nonempty_sourceContract : Nonempty BlockBand.External.PSSS.SourceContract.{u} :=
  ⟨sourceContract_holds⟩

/-- `sourceContract_holds` in universe `0`. -/
def sourceContract_holds_zero : BlockBand.External.PSSS.SourceContract.{0} :=
  sourceContract_holds.{0}

end BlockBand.Native.PSSS
