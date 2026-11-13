module

public import BlockBand.Model.Parameters
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite positive sources and their boundary-port response

`Y = K⁻¹ᴴ S K⁻¹ = K^{-*} S K⁻¹`.

The physical path has source index type `ι` and retained-port index type `κ` (the latter is
`Fin (2 * W)` in the two-input construction). These are separate finite types: the physical
source can live on all interior blocks while its response is a matrix on only the two boundary
ports.

The clock normalization is `W⁻¹ Tr Y`, with the real part made explicit. At every admissible
`Parameters` value `W ≥ 1`. The normalizations of the tags and interval sources by `W` and `W²`
are not part of this algebraic response.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.SourceProcess

open Matrix
open scoped ComplexOrder

/-- Pull a finite positive spectral source `S` back through an interior-to-port transfer `U`
(the full clock recursion).

The source coordinates `ι` and boundary ports `κ` are independent finite types, so this
Gram-matrix representation covers both the physical formula `𝒰ᴴ diag(q₁I,…,qⱼI) 𝒰` and a single
tagged block projection. -/
def positivePortResponse
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix ι κ ℂ) (S : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  Uᴴ * S * U

/-- The response on any finite family of retained ports is positive
semidefinite whenever the physical spectral source is positive semidefinite.
This is the positivity needed before taking trace words or Gaussian source transforms. -/
theorem positivePortResponse_posSemidef
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix ι κ ℂ) {S : Matrix ι ι ℂ} (hS : S.PosSemidef) :
    (positivePortResponse U S).PosSemidef := by
  exact hS.conjTranspose_mul_mul_same U

/-- For a finite square transfer matrix `K = z - X`, the positive response is
`Y = K^{-*} S K⁻¹` (with Mathlib's total matrix inverse). -/
def positiveResponse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  positivePortResponse K⁻¹ S

/-- Expansion of `positiveResponse` as `K^{-*} S K⁻¹`. -/
theorem positiveResponse_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℂ) :
    positiveResponse K S = K⁻¹ᴴ * S * K⁻¹ :=
  rfl

/-- A positive spectral source remains positive after the inverse transfer (no invertibility
assumption is needed). -/
theorem positiveResponse_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) {S : Matrix ι ι ℂ} (hS : S.PosSemidef) :
    (positiveResponse K S).PosSemidef :=
  positivePortResponse_posSemidef K⁻¹ hS

/-- The normalized clock: the real part of the trace of the port response divided by the block
width `W`. -/
def normalizedPositiveClock
    {κ : Type*} [Fintype κ]
    (p : BlockBand.Parameters) (Y : Matrix κ κ ℂ) : ℝ :=
  Y.trace.re / (p.W : ℝ)

/-- The normalized clock is nonnegative for every admissible model and every positive response. -/
theorem normalizedPositiveClock_nonneg
    {κ : Type*} [Fintype κ]
    (p : BlockBand.Parameters) {Y : Matrix κ κ ℂ} (hY : Y.PosSemidef) :
    0 ≤ normalizedPositiveClock p Y := by
  apply div_nonneg
  · exact (Complex.nonneg_iff.mp hY.trace_nonneg).1
  · exact_mod_cast (Nat.zero_le p.W)

/-- In particular the inverse-transfer response of any positive spectral
source has a nonnegative `W⁻¹ Tr` clock. -/
theorem normalizedPositiveClock_response_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : BlockBand.Parameters) (K : Matrix ι ι ℂ) {S : Matrix ι ι ℂ}
    (hS : S.PosSemidef) :
    0 ≤ normalizedPositiveClock p (positiveResponse K S) :=
  normalizedPositiveClock_nonneg p (positiveResponse_posSemidef K hS)

end BlockBand.SourceProcess
