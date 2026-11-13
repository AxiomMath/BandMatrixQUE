module

public import BlockBand.Endpoints.Response.ClockEntrance
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The weighted one-step fractional clock inequality

Part of the clock fractional-entrance lemma. `ClockFractionalLogisticRecursion` is equivalent to
the `later` clause; this file states a strictly smaller hypothesis, `ClockFractionalOneStep`: the
one-step clock fractional logistic inequality for the *weighted expectation*, on the scalar-jet
domain of the old path, integrated over that domain; the exceptional sets are not part of the
input. Definitions only.

Law: the unabsorbed two-input path `growthPathLaw W b` with matched leads, fixed
`0 < b < 1/2`, bulk `-2 < E < 2`; clock `A_j = nearClock b E W j q` of a unit source at path
length `j`.

Vocabulary (path length `j`, sample `ω`):
* `ce_fracClock` — `H_p(A_j) = Tr A_j^p`; `ce_clockTrace` — `γ_j = Tr A_j`;
* `ce_jet0`, `ce_jet1` — `δ₀, δ₁` of the passive near self-energy `X_j = pathX b E W j`
  (the scalar-jet domain; `δ₁` at a stationary jet `s`);
* `ce_weight K` — the scalar weight `1 + K δ₀` (the paper's `1 + K_p δ_{0,+}`);
* `ce_jetDomain s d` — the positive-time scalar-jet domain
  `{δ₀ ≤ d, δ₁ ≤ d, g ≤ d W}` (`g/W` sufficiently small), `g = pathConductance`;
* the moments of the inequality: `ce_weightedMoment` `E[(1 + Kδ₀) H_p]` (the paper's `y_j`),
  `ce_retainedNext` `E[1_{D_j}(1 + Kδ₀) H_p]` at length `j + 1`, `ce_concavityMoment`
  `E[1_D H_p²/γ^p]` (the retained negative term) and `ce_forcingMoment` `E[g^{2(1-p)} γ^p]`.
  The exceptional sets `D_jᶜ` are not part of the input: they are paid in `ClockEntranceStep`
  from the moment inputs.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-- `H_p(A_j) = Tr A_j^p` of the near clock at path length `j`. -/
def ce_fracClock (b E p : ℝ) (W j : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) : ℝ :=
  fracTrace p (nearClock b E W j q ω)

/-- `γ_j = Tr A_j` of the near clock at path length `j`. -/
def ce_clockTrace (b E : ℝ) (W j : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) : ℝ :=
  (nearClock b E W j q ω).trace.re

/-- `δ₀` of the passive near self-energy of the path of length `j`. -/
def ce_jet0 (b E : ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  jetDistance0 b E (pathX b E W j ω)

/-- `δ₁` (at the stationary jet `s`) of the passive near self-energy of the path of length `j`. -/
def ce_jet1 (b E : ℝ) (s : ℂ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  jetDistance1 b E s (pathX b E W j ω)

/-- The scalar weight `1 + K δ₀`. -/
def ce_weight (K b E : ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  1 + K * ce_jet0 b E W j ω

/-- The positive-time scalar-jet domain `{δ₀ ≤ d, δ₁ ≤ d, g ≤ d W}`. -/
def ce_jetDomain (b E : ℝ) (s : ℂ) (d : ℝ) (W j : ℕ) : Set (GrowthPath W) :=
  {ω | ce_jet0 b E W j ω ≤ d ∧ ce_jet1 b E s W j ω ≤ d ∧ pathConductance b E W j ω ≤ d * W}

/-- The weighted expectation `y_j = E[(1 + K δ₀) H_p]`. -/
def ce_weightedMoment (K b E p : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω) ∂growthPathLaw W b

/-- The retained concavity term `E[1_D H_p²/γ^p]` (quotient `0` when `A = 0`). -/
def ce_concavityMoment (b E p : ℝ) (s : ℂ) (d : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (ce_jetDomain b E s d W j).indicator (fun ω => ENNReal.ofReal
    (ce_fracClock b E p W j q ω ^ 2 / ce_clockTrace b E W j q ω ^ p)) ω ∂growthPathLaw W b

/-- The forcing `E[|g|^{2(1-p)} γ^p]`. -/
def ce_forcingMoment (b E p : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (|pathConductance b E W j ω| ^ (2 * (1 - p)) *
    ce_clockTrace b E W j q ω ^ p) ∂growthPathLaw W b

/-- The retained next weighted clock `E[1_{D_j} (1 + Kδ₀) H_p]` at length `j + 1`, on the jet
domain `D_j` of the old length `j` (the conditional inequality is applied on `D_j`). -/
def ce_retainedNext (K b E p : ℝ) (s : ℂ) (d : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (ce_jetDomain b E s d W j).indicator (fun ω => ENNReal.ofReal
    (ce_weight K b E W (j + 1) ω * ce_fracClock b E p W (j + 1) q ω)) ω ∂growthPathLaw W b

/-- **Isolated input: the weighted one-step fractional clock inequality** (the clock fractional
logistic inequality multiplied by the scalar weight, integrated over the jet domain of the old
path). It is the conditional one-step inequality
`E_j[(1 + Kδ_{0,+}) H_{p,+}] ≤ (1 + C/W)(1 + Kδ₀) H_p - (c/W) H_p²/γ^p + (C/W) g^{2(1-p)}γ^p
  + o(W⁻²)`
on the scalar-jet domain `D_j` of the old path, integrated over `D_j` (an old-path event, so
the integrated form follows from the conditional one; the right side is then enlarged to the
whole space). Nothing is asserted off `D_j`.

Its derivation in the paper needs, besides `A₊ = L*AL` and the product structure of the growth
step, the integral Hessian (`TransmissionLawContract.fractionalHessian`), the clock covariance
gap (from `PassiveCovarianceContract` and `TransmissionLawContract.jetGap`), and three one-port
inputs: (a) the passive mean `E_j LL* ⪯ (1 + Cδ₀ + CW⁻²)I` for `freshU`; (b) operator-norm
moments of the fresh one-port `L`; (c) the one-step predictable contraction of the weight
`1 + K_p δ_{0,+}` with the centered jet correlation.

Quantifiers. Fixed `b`, bulk `E`, `0 < p < 1`, a comparison interval of travel times
`0 < s₀ ≤ s₂`; then the weight `K ≥ 0`, constants `C ≥ 0`, `c > 0`, the domain radius `d > 0`
and a stationary jet `s`, all chosen before the source and the preceding middle length `t₁`;
for every unit source an `o(W⁻²)` error `e` (`W² e(W) → 0`) and `W₀`; for `W ≥ W₀` and every
step `travelLength W t₁ R s₀ ≤ j < travelLength W t₁ R s₂`:
`E[1_{D_j} y'_{j+1}] + (c/W) E[1_{D_j} H_p²/γ^p] ≤ (1 + C/W) y_j + (C/W) E[g^{2(1-p)}γ^p] + e(W)`,
`y_j = E[(1 + Kδ₀) H_p(A_j)]`, `E[1_{D_j} y'_{j+1}] = E[1_{D_j}(1 + Kδ₀) H_p(A_{j+1})]`.

**Why this is strictly smaller than `later`.** Unlike `ClockFractionalLogisticRecursion`,
nothing here is chosen freely: `y_j` is the fixed weighted expectation, and the `Prop` bounds its
*increment* from length `j` to `j + 1` (on the jet domain) by `O(W⁻¹)` with a strictly negative
concavity term. `later` bounds `E H_p` at each length separately and says nothing about
increments, the weight or the concavity term, so it does not give this `Prop` (a constant
sequence satisfies `later` but has no counterpart here). The converse direction, this `Prop` ⇒
`later`, is proved in `ce_logisticRecursion_of_oneStep`: Cauchy–Schwarz
`E(1_D H_p²/γ^p) ≥ (E 1_D H_p)²/E γ^p`, the exceptional sets by Markov and polynomial failure
powers with `H_p ≤ W^{1-p}γ^p`, the edge-clock, conductance and jet moments uniform in the
preceding middle (`EdgeClockMomentsContract`, `TransmissionLengthUniformContract`), and the
discrete logistic comparison. -/
def ClockFractionalOneStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ s₀ s₂ : ℝ, 0 < s₀ → s₀ ≤ s₂ →
      ∃ (K C c d : ℝ) (s : ℂ), 0 ≤ K ∧ 0 ≤ C ∧ 0 < c ∧ 0 < d ∧ IsStationaryJet b E s ∧
        ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
          ∃ e : ℕ → ℝ, Tendsto (fun W : ℕ => (W : ℝ) ^ 2 * e W) atTop (𝓝 0) ∧
          ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ j : ℕ, travelLength W t₁ R s₀ ≤ j →
            j < travelLength W t₁ R s₂ →
            ce_retainedNext K b E p s d W j q +
                ENNReal.ofReal (c / W) * ce_concavityMoment b E p s d W j q ≤
              ENNReal.ofReal (1 + C / W) * ce_weightedMoment K b E p W j q +
                ENNReal.ofReal (C / W) * ce_forcingMoment b E p W j q + ENNReal.ofReal (e W)

end BlockBand.Endpoints
