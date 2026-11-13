module

public import BlockBand.Endpoints.Response.TaggedConvexOrderStepAbel
public import BlockBand.Endpoints.Response.TaggedConvexOrderMoments
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable

/-!
# The explicit drift-deficit witness of the tagged convex order

Law: `probedClockLaw W b` (the near-end-grown path `growthPathLaw W b` with an independent
`h ~ CN(0, I_{2W})`). At energy `e`, path length `l` and birth index `k`:

* `Q = Q_{l;k} = W⁻¹Y_{l;k}` (`tco_tagQ`, positive semidefinite);
* `tcw_v`: `v = Q^{1/2}h`; `tcw_X`: `X = ‖v‖² = h*Qh = Z_{l;k}` (`tcw_X_eq`);
* `P = nearProjection W`, `tcw_conjProj`: `P' = 𝕊*P𝕊` with `𝕊 = scatteringMatrix` of the path of
  length `l` (the old path before the step `l → l+1`, as in `FullSourceCovarianceContract`);
* `tcw_G`: `G = (v*Pv)(v*P'v)`;
* `tcw_deficit b e W l k m = (D₀/2W) E[m(m-1) X^{m-2}(G - X²)]`, `D₀ = transportD0 b e`.

`TcwRemainderAlong` and `TcwRemainderCoreFixed` are the remainder clause of
`TcsOneStepSplitAlong` for this fixed witness; see the docstring of `TcwRemainderAlong`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

/-- `Q_{l;k}^{1/2}`: the positive square root (`CFC.sqrt`, matrix order) of
`Q_{l;k} = W⁻¹Y_{l;k}`. -/
def tcw_sqrtQ (b e : ℝ) (W l k : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  CFC.sqrt (tco_tagQ b e W l k ω)

/-- `v = Q_{l;k}^{1/2}h` on the probed path `(ω, h)`. -/
def tcw_v (b e : ℝ) (W l k : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : Fin 2 × Fin W → ℂ :=
  tcw_sqrtQ b e W l k x.1 *ᵥ x.2

/-- `P' = 𝕊*P𝕊`, `𝕊` the scattering matrix of the path of length `l`. -/
def tcw_conjProj (b e : ℝ) (W l : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (scatteringMatrix b e W l ω)ᴴ * nearProjection W * scatteringMatrix b e W l ω

/-- `X = ‖v‖² = h*Q_{l;k}h` (equal to `Z_{l;k}`, `tcw_X_eq`). -/
def tcw_X (b e : ℝ) (W l k : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  (star (tcw_v b e W l k x) ⬝ᵥ tcw_v b e W l k x).re

/-- `G = (v*Pv)(v*P'v)`, the opposite-sign covariance factor. -/
def tcw_G (b e : ℝ) (W l k : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  (star (tcw_v b e W l k x) ⬝ᵥ (nearProjection W *ᵥ tcw_v b e W l k x)).re *
    (star (tcw_v b e W l k x) ⬝ᵥ (tcw_conjProj b e W l x.1 *ᵥ tcw_v b e W l k x)).re

/-- The explicit drift deficit `d_l(m) = (D₀/2W) E E_h[m(m-1) X^{m-2}((v*Pv)(v*P'v) - X²)]`,
`D₀ = D₀(e)`, under `probedClockLaw W b`. For a polynomial `ψ` of degree `≤ M`,
`Σ_{m≤M} ψ_m d_l(m)` is `(D₀/2W) E E_h[ψ''(X)(G - X²)]`, the one-step drift minus the
geometric-Brownian drift `(D₀/2W) E ψ''(X)X²`. -/
def tcw_deficit (b e : ℝ) (W l k m : ℕ) : ℝ :=
  transportD0 b e / (2 * W) *
    ∫ x, (m : ℝ) * ((m : ℝ) - 1) * tcw_X b e W l k x ^ (m - 2) *
      (tcw_G b e W l k x - tcw_X b e W l k x ^ 2) ∂probedClockLaw W b

/-- The remainder clause along one tagged sequence, for the fixed explicit witness `tcw_deficit`.

For every degree `M` and `δ > 0`, eventually in `j`: for every `m ≤ M` and every partial range
`k+1 ≤ l' ≤ n`, `|Σ_{k+1≤l<l'} (ε_l(m) - d_l(m))| ≤ δ`, where `ε_l(m) = tcs_monoErr` (the
one-step error of the monomial `X^m` at `D₀ = D₀(E)`) and `d_l(m) = tcw_deficit` (at the path
energy).

Content: `ε_l(m) - d_l(m) = r_l(X^m)`, the remainder of the one-step tagged convex generator
expansion for the monomial, explicitly
`E Z_{l+1}^m - E Z_l^m - (D₀/2W) m(m-1) E E_h[X^{m-2}(v*Pv)(v*P'v)]`. After the stop is removed,
`Σ_l E|r_l| ≤ C(W^{-1/2} + W⁻¹)`, and every partial sum is at most this absolute sum. -/
def TcwRemainderAlong (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) : Prop :=
  ∀ (M : ℕ) (δ : ℝ), 0 < δ → ∀ᶠ j in atTop, ∀ m ≤ M, ∀ l', σ.k j + 1 ≤ l' → l' ≤ σ.n j →
    |∑ l ∈ Ico (σ.k j + 1) l',
      (tcs_monoErr b (σ.energy j) (transportD0 b E) (σ.W j) l (σ.k j) m -
        tcw_deficit b (σ.energy j) (σ.W j) l (σ.k j) m)| ≤ δ

/-- `TcwRemainderAlong` along every tagged sequence at the constant energy `E` (fixed
`0 < b < 1/2`, bulk `E`, `s > 0`). -/
def TcwRemainderCoreFixed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ : ℝ, 0 < s →
    ∀ σ : TcoTagSequence s τ E, (∀ j, σ.energy j = E) → TcwRemainderAlong b σ

end BlockBand.Endpoints
