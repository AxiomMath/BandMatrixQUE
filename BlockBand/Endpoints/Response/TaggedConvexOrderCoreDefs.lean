module

public import BlockBand.Endpoints.Response.TaggedConvexOrderDefs
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Definitions for the proof of the tagged convex order theorem

Law: `probedClockLaw W b` (the near-end-grown path with an independent `h ~ CN(0, I_{2W})`). For
the tag of birth index `k` and a path length `l > k`, `Z_{l;k} = W⁻¹h*Y_{l;k}h`
(`lmf_tagResponseClock`).

* `tcc_psi b e W l k ψ = E ψ(Z_{l;k})`: the polynomial test `Ψ_ψ(Q) = E_h ψ(h*Qh)`, averaged over
  the path, at `Q = Q_{l;k} = Y_{l;k}/W`.
* `tcc_gen D₀ ψ = (D₀/2) X² ψ''`: the generator of geometric Brownian motion applied to `ψ`.
* `tcc_backward D₀ t φ = Σ_m φ_m e^{(D₀/2)m(m-1)t} X^m`: the backward polynomial
  `u(t, x) = E φ(x e^{√D₀B_t - D₀t/2})`, written in coefficients. It solves
  `∂_t u = (D₀/2)x²∂²_x u` coefficientwise.
* `TcoOneStepAlong`, `TcoOneStepCoreFixed`: the summed one-step inequality, i.e. the one-step
  tagged convex generator expansion (from the full-source covariance lemma), summed with the
  remainder bound (from the contracting-words and full-source-stops lemmas), with the drift
  bounded through `0 ≤ (v*Pv)(v*P'v) ≤ X²` for convex tests. See the docstring of
  `TcoOneStepAlong` for the precise form and why it is strictly weaker than
  `TcoTagComparisonCoreFixed`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks

/-- The averaged polynomial test `E Ψ_ψ(Q_{l;k}) = E ψ(Z_{l;k})`, `Z_{l;k} = W⁻¹h*Y_{l;k}h` under
`probedClockLaw W b`, at energy `e`, path length `l` and birth index `k` (averaged over the
path). -/
def tcc_psi (b e : ℝ) (W l k : ℕ) (ψ : ℝ[X]) : ℝ :=
  ∫ x, ψ.eval (lmf_tagResponseClock b e W l k x) ∂probedClockLaw W b

/-- The geometric Brownian generator `(D₀/2) x² ψ''` applied to a polynomial `ψ`. -/
def tcc_gen (D0 : ℝ) (ψ : ℝ[X]) : ℝ[X] :=
  C (D0 / 2) * X ^ 2 * derivative (derivative ψ)

/-- The backward polynomial `u(t, ·) = Σ_m φ_m e^{(D₀/2)m(m-1)t} X^m`
(`u(t, x) = E φ(x e^{√D₀B_t - D₀t/2})` for `t ≥ 0`, see `tcc_gbmExpect_eq_eval_backward`). -/
def tcc_backward (D0 t : ℝ) (φ : ℝ[X]) : ℝ[X] :=
  ∑ m ∈ Finset.range (φ.natDegree + 1),
    C (φ.coeff m * Real.exp (D0 / 2 * ((m : ℝ) * ((m : ℝ) - 1)) * t)) * X ^ m

/-- The summed one-step inequality along one tagged sequence.

Along the tagged sequence `σ` (index `j`; width `W = W_j`, length `n = n_j`, birth index
`k = k_j`, energy `e = e_j`), for every degree bound `M`, coefficient bound `A` and `δ > 0`,
eventually in `j`: for every family `(ψ_l)` of polynomials convex on `[0,∞)` with
`deg ψ_l ≤ M` and `|coeff| ≤ A`,
`Σ_{k+1 ≤ l < n} [E Ψ_{ψ_l}(Q_{l+1}) - E Ψ_{ψ_l}(Q_l) - W⁻¹ E Ψ_{(D₀/2)x²ψ_l''}(Q_l)] ≤ δ`,
with `D₀ = D₀(E)` at the base energy.

Content: the one-step change `E Ψ(Q_+) - E Ψ(Q)` equals
`(D₀/2W) E E_h[ψ''(X)(v*Pv)(v*P'v)] + r_l` (from the full-source covariance lemma), the bound
`Σ_l E|r_l| = o(1)` (from the contracting-words and full-source-stops lemmas), and the pointwise
drift bound `ψ''(X)(v*Pv)(v*P'v) ≤ ψ''(X)X²` for convex `ψ`. The uniformity over
coefficient-bounded families follows from linearity of the error `r_l` in `ψ` (it is a fixed
polynomial of degree `≤ M` in the monomials).

It is a finite-`W` statement about every intermediate length `k < l < n` with arbitrary convex
test families; `TcoTagComparisonCoreFixed` only bounds the final `limsup_j E φ(Z_{n_j;k_j})`. The
core does not imply it (for `ψ_l = X²` it is the integral inequality
`E Z_n² - E Z_{k+1}² ≤ D₀W⁻¹Σ_l E Z_l² + δ`, which the endpoint bound `E Z_n² ≲ d²e^{D₀(τ-s)}`
does not give). The backward comparison with `tcc_backward` and the initial value are proved from
it in `tcc_comparisonAlong`. -/
def TcoOneStepAlong (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) : Prop :=
  ∀ (M : ℕ) (A δ : ℝ), 0 < δ → ∀ᶠ j in atTop, ∀ ψ : ℕ → ℝ[X],
    (∀ l, ConvexOn ℝ (Set.Ici 0) (fun x => (ψ l).eval x)) → (∀ l, (ψ l).natDegree ≤ M) →
    (∀ l i, |(ψ l).coeff i| ≤ A) →
    ∑ l ∈ Finset.Ico (σ.k j + 1) (σ.n j),
      (tcc_psi b (σ.energy j) (σ.W j) (l + 1) (σ.k j) (ψ l) -
        tcc_psi b (σ.energy j) (σ.W j) l (σ.k j) (ψ l) -
        (σ.W j : ℝ)⁻¹ * tcc_psi b (σ.energy j) (σ.W j) l (σ.k j)
          (tcc_gen (transportD0 b E) (ψ l))) ≤ δ

/-- `TcoOneStepAlong` along every tagged sequence at the constant energy `E` (fixed
`0 < b < 1/2`, bulk `E`, `s > 0`); strictly weaker than `TcoTagComparisonCoreFixed` (see
`TcoOneStepAlong`). -/
def TcoOneStepCoreFixed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ : ℝ, 0 < s →
    ∀ σ : TcoTagSequence s τ E, (∀ j, σ.energy j = E) → TcoOneStepAlong b σ

/-- **`TcoOneStepAlong` along every tagged sequence, energy-uniform reading** (moving energies
`e_j → E`, as in `TcoTagComparisonCore`). It is not used for the fixed-energy result; with it,
the energy-uniform core needs only energy-uniform versions of the moment and tag-birth inputs of
`tcc_comparisonAlong`.
-/
def TcoOneStepCore : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ : ℝ, 0 < s →
    ∀ σ : TcoTagSequence s τ E, TcoOneStepAlong b σ

end BlockBand.Endpoints
