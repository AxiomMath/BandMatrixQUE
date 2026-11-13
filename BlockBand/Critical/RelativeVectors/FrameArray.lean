module

public import BlockBand.Critical.RelativeVectors.Statement

/-!
# The complex eigenvector array, label phases, Euclidean bounds

* `frameArray V K`: the array `z_i = √N V^*u_i(K)` (`u_i` the selected rank-`i` unit
  eigenvector, increasing ranks).
* `labelPhase α z`: `(e^{iα_1}z_1, …, e^{iα_N}z_N)`; `IsLabelPhaseInvariant g`: `g ∘ labelPhase α
  = g` for every `α`. Such `g(frameArray V K)` does not depend on the eigenvector selection.
* `arrayNormSq z = Σ_i Σ_q |z_iq|²` (Euclidean norm on `ℂ^{N×r}`; the normed-space norm of
  `Fin N → Fin r → ℂ` is the sup norm).
* `IsArrayC2Bounded C g`: `g` is `C²`, `|g| ≤ C`, `|Dg(z)v| ≤ C‖v‖₂`, `|D²g(z)(v,w)| ≤ C‖v‖₂‖w‖₂`.
  These Euclidean bounds are the ones the reference flow preserves (`‖𝓜‖₂ ≤ 1`), and a test of
  the tested labels (`IsC2Bounded C` on `MarkArray k r`, sup norm) composed with the restriction
  to the tested labels satisfies them with the same constant.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm

variable {N r : ℕ}

/-- Complex eigenvector array `z_i = √N V^* u_i(K)` (`u_i` the rank-`i` unit eigenvector,
increasing ranks; phase-free in every use, see `IsLabelPhaseInvariant`). -/
def frameArray (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ) :
    Fin N → Fin r → ℂ :=
  fun i => ((Real.sqrt N : ℝ) : ℂ) • (Vᴴ *ᵥ freshEigenvector K i)

/-- Label phases `z ↦ (e^{iα_1}z_1, …, e^{iα_N}z_N)`. -/
def labelPhase (α : Fin N → ℝ) (z : Fin N → Fin r → ℂ) : Fin N → Fin r → ℂ :=
  fun i => Complex.exp ((α i : ℂ) * Complex.I) • z i

/-- `g(e^{iα_1}z_1, …, e^{iα_N}z_N) = g(z)` for all label phases. Such `g(frameArray V K)` does
not depend on the eigenvector selection. -/
def IsLabelPhaseInvariant (g : (Fin N → Fin r → ℂ) → ℝ) : Prop :=
  ∀ (α : Fin N → ℝ) (z : Fin N → Fin r → ℂ),
    g (fun i => Complex.exp ((α i : ℂ) * Complex.I) • z i) = g z

/-- Squared Euclidean norm `Σ_i Σ_q |z_iq|²` of an array. -/
def arrayNormSq (z : Fin N → Fin r → ℂ) : ℝ :=
  ∑ i, ∑ q, ‖z i q‖ ^ 2

/-- Bounded `C²` with constant `C` for the Euclidean norm of `ℂ^{N×r}`: `|g| ≤ C`,
`|Dg(z)v| ≤ C‖v‖₂` and `|D²g(z)(v,w)| ≤ C‖v‖₂‖w‖₂` (real derivatives). -/
structure IsArrayC2Bounded (C : ℝ) (g : (Fin N → Fin r → ℂ) → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 g
  bound : ∀ z, |g z| ≤ C
  deriv_bound : ∀ z v, |fderiv ℝ g z v| ≤ C * Real.sqrt (arrayNormSq v)
  hessian_bound : ∀ z v w, |fderiv ℝ (fderiv ℝ g) z v w| ≤
    C * Real.sqrt (arrayNormSq v) * Real.sqrt (arrayNormSq w)

end BlockBand.Critical.RelativeVectors
