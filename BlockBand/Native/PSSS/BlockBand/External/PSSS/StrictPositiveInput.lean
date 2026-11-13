module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Interface

/-!
# Strictly positive PSSS factorial-count input

The source formulation of the Peled–Schenker–Shamis–Sodin factorial-count
estimate uses a strictly positive absolute constant.  The interface `PSSSInput`
records only the weaker field `0 ≤ C`, which suffices for its conditional uses.
This module records the exact source-side positivity without changing that
interface.

This is a conditional input.  In particular, no inhabitant is constructed here:
supplying a value of `StrictPositivePSSSInput` is precisely the external theorem
that is assumed.  All model, block-size,
deformation, interval, and factorial-order quantifiers remain those of
`PSSSInput`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand

universe u

open MeasureTheory

/-- The PSSS factorial-count input together with the strict positivity of
its single absolute constant.

The structure is separate from `PSSSInput`: conditional developments need only
nonnegativity, while a transcription of the cited source theorem constructs this
stronger object. -/
structure StrictPositivePSSSInput where
  input : PSSSInput.{u}
  C_pos : 0 < input.C

namespace StrictPositivePSSSInput

/-- The source constant in a strict input is nonnegative, compatibly with the
field already stored by `PSSSInput`. -/
theorem C_nonneg (strict : StrictPositivePSSSInput.{u}) :
    0 ≤ strict.input.C :=
  strict.C_pos.le

/-- Strict inputs expose the same factorial integrability statement as
`PSSSInput`. -/
theorem factorialIntegrable (strict : StrictPositivePSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (r : ℕ) :
    Integrable (fun ω =>
      ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ)) M.P :=
  strict.input.factorialIntegrable hd M A₀ a b r

/-- Strict inputs expose the exact all-orders factorial-count inequality,
uniform in every parameter quantified by the cited result. -/
theorem factorialCount (strict : StrictPositivePSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (hab : a ≤ b) (r : ℕ) (hr : 1 ≤ r) :
    ∫ ω, ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ) ∂M.P
      ≤ (strict.input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) ^ r :=
  strict.input.factorialCount hd M A₀ a b hab r hr

end StrictPositivePSSSInput

end PSSSNative.BlockBand
