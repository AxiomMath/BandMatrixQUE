module

public import BlockBand.Endpoints.Response.ClockEntranceStepDefs

/-!
# The near-clock part of the remote higher-order clock theorem

At finite width the higher moments of a near clock are bounded only up to `O(1)` after positive
travel (by the higher logistic inequality and the discrete comparison); the exponential decay in
the travel time comes from the limiting generator and is brought back to `limsup_W` through
critical limits, as for near-Schatten decay (these assertions concern critical limits and limsups,
not a uniform prelimit theorem). The reduction is therefore that of `ns_limsupDecay`, with `H_p`
replaced by `H_p^r`:

* `RhnHigherWeightedRecursion`: the finite-`W` recursion of the fixed weighted expectation
  `y_j = E[(1 + Kδ₀) H_p(A_j)^r]`, stated in this file;
* the lower and upper passages of `E H_p^r` between finite width and critical limits.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Endpoints

/-- The weighted higher expectation `y_j = E[(1 + Kδ₀) H_p(A_j)^r]`, with the same linear scalar
weight as `ce_weightedMoment`. -/
def rhn_weightedHigherMoment (K b E p r : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω ^ r)
    ∂growthPathLaw W b

/-- The finite-`W` higher logistic recursion of the weighted expectation: a discrete comparison
`y₊ ≤ y + W⁻¹(Cy - c y^{1+1/r} + C) + o(W⁻²)`.

Fixed `0 < b < 1/2`, bulk `E`, `0 < p < 1`, `r ≥ 1`, `pr < 1`, a comparison interval of travel
times `0 < s₀ ≤ s₂`; a weight `K ≥ 0` and constants `C`, `c > 0`, chosen before the source and the
preceding middle length `t₁` (they may depend on `p, r, s₀, s₂`); for every unit source an
`o(W⁻²)` error `e` (`W² e(W) → 0`) and `W₀`; for `W ≥ W₀`, at every length
`travelLength W t₁ R s₀ ≤ j ≤ travelLength W t₁ R s₂` the weighted expectation
`y_j = E[(1 + Kδ₀) H_p(A_j)^r]` is finite, and on each step of that range
`y_{j+1} ≤ y_j + W⁻¹(C y_j - c y_j^{1+1/r} + C) + e(W)` (`y_j` the real value).

Derivation: the concavity of `H^r` on positive matrices for `pr < 1` (from the trace Hessian and
Cauchy–Schwarz `(DH[A₁])² ≤ p/(1-p) H(-D²H[A₁,A₁])`); on the scalar-jet/`g/W` domain the passive
mean `E_j LL* ⪰ I/2`, the event `‖LL*‖ ≤ K`, the clock between `A/4` and `K'A` on the first half
of the segment, and the clock covariance gap, giving the Jensen deficit
`c_{p,r} H^{r-1}(H - C_p g^{1-p}γ^p)_+²/(Wγ^p)`; `(x-a)_+² x^{r-1} ≥ c_r x^{r+1} - C_r a^{r+1}`,
hence the higher logistic inequality
`E_j H_+^r ≤ (1 + Cδ₀ + CW⁻²)H^r - (c/W)H^{r+1}/γ^p + (C/W) g^{(r+1)(1-p)}γ^{pr}`; the scalar
weight (correlation cost `CH^r/W` since `H_+^r ≤ ‖L‖^{2pr} H^r`); exceptional sets paid by
polynomial powers and `H^r ≤ W^{r(1-p)}γ^{pr}`; the edge-clock moments for the forcing; Hölder
`E(H^{r+1}/γ^p) ≥ (EH^r)^{(r+1)/r}/(Eγ^{pr})^{1/r}`. -/
def RhnHigherWeightedRecursion : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 → ∀ s₀ s₂ : ℝ, 0 < s₀ → s₀ ≤ s₂ →
      ∃ K C c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
        ∃ e : ℕ → ℝ, Tendsto (fun W : ℕ => (W : ℝ) ^ 2 * e W) atTop (𝓝 0) ∧
        ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
          (∀ j : ℕ, travelLength W t₁ R s₀ ≤ j → j ≤ travelLength W t₁ R s₂ →
            rhn_weightedHigherMoment K b E p r W j q ≠ ⊤) ∧
          ∀ j : ℕ, travelLength W t₁ R s₀ ≤ j → j < travelLength W t₁ R s₂ →
            (rhn_weightedHigherMoment K b E p r W (j + 1) q).toReal ≤
              (rhn_weightedHigherMoment K b E p r W j q).toReal + (W : ℝ)⁻¹ *
                (C * (rhn_weightedHigherMoment K b E p r W j q).toReal -
                  c * (rhn_weightedHigherMoment K b E p r W j q).toReal ^ (1 + 1 / r) + C) + e W

/-- On each fixed travel interval `[s₁, s₂]`, `0 < s₁ ≤ s₂`, the expectations
`E H_p(A)^r` are bounded uniformly in `W ≥ W₀` and `s ∈ [s₁, s₂]` by a constant chosen before the
source and the preceding middle length; the threshold `W₀` may depend on the source.
At `r = 1`
it is the `later` clause.
Proved from `RhnHigherWeightedRecursion`
(`rhn_higherLater_of_recursion`); not an isolated input.
-/
def RhnHigherLater : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 → ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
        ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ s ∈ Set.Icc s₁ s₂,
          ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W (travelLength W t₁ R s) q ω)) ^ r
            ∂growthPathLaw W b ≤ ENNReal.ofReal C

end BlockBand.Endpoints
