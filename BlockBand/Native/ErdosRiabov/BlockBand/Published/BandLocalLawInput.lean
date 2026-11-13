module

public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ResolventIdentities
public import BlockBand.Native.ErdosRiabov.BlockBand.CriticalSequences
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import BlockBand.Native.ErdosRiabov.BlockBand.Model.GaussianRing
public import Mathlib.Analysis.RCLike.Sqrt

/-!
# Quantities of the short-ring band local law

The quantities in which the external band local law of Erdős–Riabov is stated for the short
ring: the circular site distance, the diffusion length, the semicircle Stieltjes transform,
the Green function and the entrywise error. No local law is asserted.

The model has `m ≥ 4` cyclic blocks of width `W`, total dimension
`N = mW`, and fixed `0 < b < 1/2`.  No parity restriction is imposed: the
definitions apply to even and odd block counts.

Citation normalization: ER, arXiv:2506.06441v1, Definition 2.1,
Proposition 2.8(ii), Theorem 3.3 and (3.17).  ER use
`G(z) = (H - z)⁻¹`, whereas `matrixResolvent` is
`(z I - H)⁻¹`; hence `shortRingGreen` includes the necessary minus sign.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand

open MeasureTheory
open scoped ENNReal NNReal

/-- The circular distance `|x-y|_N` after the row-major
identification of the `mW` sites with a cycle.  This definition works for both
parities of the block count. -/
def shortRingSiteDistance (p : Params) (x y : Site p.n p.W) : ℕ :=
  let _ := p.nNeZero
  let i := (p.siteIndexEquiv x).val
  let j := (p.siteIndexEquiv y).val
  let d := max i j - min i j
  min d (p.L - d)

/-- ER's diffusion length `ℓ = min(N, W / √η)`, as a real number. -/
def shortRingLength (p : Params) (η : ℝ) : ℝ :=
  min (p.L : ℝ) ((p.W : ℝ) / Real.sqrt η)

/-- The Stieltjes transform of the standard semicircle law, with the branch
used on the upper half-plane.  It solves `m² + z m + 1 = 0` and matches the
convention `G(z) = (H-z)⁻¹`.

This definition is deliberately a *restricted upper-half-plane helper*, not a
total Herglotz definition: its lower-half-plane value would require Schwarz
reflection.  It is used only at `e + η i` with `0 < η`. -/
def semicircleStieltjes (z : ℂ) : ℂ :=
  if z.re < 0 then
    (-z - Complex.sqrt (z ^ 2 - 4)) / 2
  else
    (-z + Complex.sqrt (z ^ 2 - 4)) / 2

/-- The ER resolvent `Gᴷ(z) = (K-z)⁻¹`.  The resolvent
`matrixResolvent K z` has the opposite sign convention. -/
def shortRingGreen {p : Params} (K : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (z : ℂ) : Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  let _ := p.nNeZero
  (-matrixResolvent K z)

/-- The entrywise deviation `|G_{xy}(e + iη) - m δ_{xy}|` in the short-ring local law. -/
def shortRingEntryError {p : Params} (K : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (e η : ℝ) (x y : Site p.n p.W) : ℝ :=
  ‖shortRingGreen K (e + η * Complex.I) x y -
      semicircleStieltjes (e + η * Complex.I) * if x = y then 1 else 0‖

end ERNative.BlockBand
