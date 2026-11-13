module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalMultiBlockReconstruction

/-!
# Unconditional physical multi-block moment bounds

This module exposes the paper-facing all-order factorial and exponential estimates for
the physical Gaussian ring.  The physical interval count is the eigenvalue count of the
matrix normalized by `sqrt c`, hence its PSSS counting constant is exactly
`input.C / sqrt p.c`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand
open MeasureTheory
namespace GaussianRing
local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The physical closed-interval eigenvalue count, expressed through the normalized
physical matrix.  Thus `[a,b]` in physical energy corresponds exactly to
`[a / sqrt c, b / sqrt c]` for `normalizedPhysicalMatrix`. -/
def Law.physicalIntervalCount {p : Params} (M : Law p)
    (a b : ℝ) (ω : M.Ω) : ℕ :=
  M.normalizedPhysicalIntervalCount a b ω

/-- Exact PSSS intensity constant after the physical `sqrt c` rescaling. -/
def physicalMultiBlockCountingConstant (input : PSSSInput.{0}) (p : Params) : ℝ :=
  input.C / Real.sqrt p.c

/-- The physical count on the unfolded window centered at `e` with half-width
`R / (L ρ)`. -/
def Law.physicalUnfoldedIntervalCount {p : Params} (M : Law p)
    (e L ρ R : ℝ) (ω : M.Ω) : ℕ :=
  M.physicalIntervalCount (e - R / (L * ρ)) (e + R / (L * ρ)) ω

/-- Physical falling factorials are integrable at every order. -/
theorem Law.physicalIntervalCount_factorialIntegrable
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    {a b : ℝ} (hab : a ≤ b) (r : ℕ) :
    Integrable (fun ω => ((M.physicalIntervalCount a b ω).descFactorial r : ℝ)) M.P := by
  have htransport :
      PhysicalMultiBlockCountTransport M.P M.normalizedOffDiagonalBackgroundLaw p
        M.normalizedAllDiagonalBlocksGUE (fun A => A)
        M.normalizedPhysicalIntervalCount :=
    M.physicalMultiBlockCountTransport_unconditional
  simpa [Law.physicalIntervalCount] using
    htransport.factorialIntegrable input
      M.P M.normalizedOffDiagonalBackgroundLaw M.normalizedAllDiagonalBlocksGUE
      (fun A => A) M.normalizedPhysicalIntervalCount hab r

/-- **Unconditional physical all-order factorial estimate.**  The constant is exactly
`C / sqrt c`, uniformly in the interval and factorial order. -/
theorem Law.physicalIntervalCount_factorial
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    {a b : ℝ} (hab : a ≤ b) (r : ℕ) (hr : 1 ≤ r) :
    ∫ ω, ((M.physicalIntervalCount a b ω).descFactorial r : ℝ) ∂M.P ≤
      (physicalMultiBlockCountingConstant input p *
        (p.n * p.W : ℝ) * (b - a)) ^ r := by
  have htransport :
      PhysicalMultiBlockCountTransport M.P M.normalizedOffDiagonalBackgroundLaw p
        M.normalizedAllDiagonalBlocksGUE (fun A => A)
        M.normalizedPhysicalIntervalCount :=
    M.physicalMultiBlockCountTransport_unconditional
  simpa [Law.physicalIntervalCount, physicalMultiBlockCountingConstant] using
    htransport.factorialCount input
      M.P M.normalizedOffDiagonalBackgroundLaw M.normalizedAllDiagonalBlocksGUE
      (fun A => A) M.normalizedPhysicalIntervalCount hab r hr

/-- **Unconditional physical exponential count estimate.** -/
theorem Law.physicalIntervalCount_exponential
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    {a b t : ℝ} (hab : a ≤ b) (ht : 0 ≤ t) :
    ∫ ω, Real.exp (t * (M.physicalIntervalCount a b ω : ℝ)) ∂M.P ≤
      Real.exp (physicalMultiBlockCountingConstant input p *
        (p.n * p.W : ℝ) * (b - a) * (Real.exp t - 1)) := by
  have htransport :
      PhysicalMultiBlockCountTransport M.P M.normalizedOffDiagonalBackgroundLaw p
        M.normalizedAllDiagonalBlocksGUE (fun A => A)
        M.normalizedPhysicalIntervalCount :=
    M.physicalMultiBlockCountTransport_unconditional
  simpa [Law.physicalIntervalCount, physicalMultiBlockCountingConstant] using
    htransport.countExponential input
      M.P M.normalizedOffDiagonalBackgroundLaw M.normalizedAllDiagonalBlocksGUE
      (fun A => A) M.normalizedPhysicalIntervalCount hab ht

/-- **Unconditional unfolded physical exponential estimate.**  Under the paper's
normalization `nW ≤ L`, the resulting intensity is exactly
`(C / sqrt c) / ρ`. -/
theorem Law.physicalUnfoldedIntervalCount_exponential
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    (e L ρ R t : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hdim : (p.n * p.W : ℝ) ≤ L) (ht : 0 ≤ t) :
    ∫ ω, Real.exp (t *
      (M.physicalUnfoldedIntervalCount e L ρ R ω : ℝ)) ∂M.P ≤
      Real.exp (2 * R * (physicalMultiBlockCountingConstant input p / ρ) *
        (Real.exp t - 1)) := by
  have htransport :
      PhysicalMultiBlockCountTransport M.P M.normalizedOffDiagonalBackgroundLaw p
        M.normalizedAllDiagonalBlocksGUE (fun A => A)
        M.normalizedPhysicalIntervalCount :=
    M.physicalMultiBlockCountTransport_unconditional
  simpa [Law.physicalUnfoldedIntervalCount, Law.physicalIntervalCount,
    transportedUnfoldedIntervalCount, physicalMultiBlockCountingConstant] using
    htransport.unfoldedCountExponential input
      M.P M.normalizedOffDiagonalBackgroundLaw M.normalizedAllDiagonalBlocksGUE
      (fun A => A) M.normalizedPhysicalIntervalCount e L ρ R t hL hρ hR hdim ht

end GaussianRing
end CoareaNative.BlockBand
