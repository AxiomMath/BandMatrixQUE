module

public import BlockBand.Internal.Contracts.Endpoints
public import BlockBand.Endpoints.Response.NearSchattenPassage

/-!
# Hypotheses of the near-Schatten decay theorem

* `NsRegularizedLimitGenerator`: the integrated regularized generator inequality at every critical
  limit. It packages the trace generator of `Tr f(A)` derived from the word generator, the sign of
  the divided-difference terms, the bound of the first two terms by
  `-(Dp(1-p)/2) Σ_i λ_i²(λ_i+ε)^{p-2}` for `f_ε(x) = (x+ε)^p - ε^p`, polynomial approximation
  through three derivatives on a trace stop, stop removal, and integration in time. It is used
  only for `limitDecay`; the remaining steps (from the entrance bound on `E H_{p₀}` on) are proved
  in `ns_limitDecay`.
* `NsCriticalClockLimitsExist`: critical limits of the clock exist along subsequences.

The regularized traces are measured against a clock trace measure `μ`:
`nsRegTrace p ε μ = ∫ f_ε(x)/x dμ` (at finite width, `Tr f_ε(A)`) and
`nsDissTrace p ε μ = ∫ x(x+ε)^{p-2} dμ` (at finite width, `Σ_i λ_i²(λ_i+ε)^{p-2}`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-- `Tr f_ε(A) = ∫ f_ε(x)/x dμ` for a clock trace measure `μ` (`f_ε(x) = (x+ε)^p - ε^p`; an atom
of `μ` at `0` counts `f_ε'(0) = pε^{p-1}` per unit mass). -/
def nsRegTrace (p ε : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (nsRegKernel p ε x) ∂μ

/-- The regularized dissipation `Σ_i λ_i²(λ_i+ε)^{p-2} = ∫ x(x+ε)^{p-2} dμ`. -/
def nsDissTrace (p ε : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (nsDissKernel p ε x) ∂μ

/-- The decay rate `κ = D₀ p (1-p)/2` of the homogeneous clock decay. -/
def nsDecayRate (b E p : ℝ) : ℝ := transportD0 b E * p * (1 - p) / 2

/-- The integrated regularized generator inequality at critical limits.

Same law, parameters, source class and critical-limit encoding as
`NearSchattenDecayContract.limitDecay` (fixed `0 < b < 1/2`, bulk `E`, `0 < p < 1`, a unit
source `IsUnitSource t₁ R q`, a joint critical word limit `(P, Z)` of the one-source family on
`[t₁ + R, ∞)` with a.s. clock measures `μ_t`). For every `ε > 0` and all times
`t₁ + R < u₁ ≤ u₂` (strictly after the last injection):
`E Tr f_ε(A_{u₂}) + κ ∫_{u₁}^{u₂} E Σ_i λ_i²(λ_i+ε)^{p-2}(u) du ≤ E Tr f_ε(A_{u₁})`,
`κ = D₀p(1-p)/2`, in the measure encoding `nsRegTrace`/`nsDissTrace` (lower integrals in
`ℝ≥0∞`; the time integral is the lower Lebesgue integral, no measurability assumed).

Derivation. The projected word generator has mean `-DgA/2` and covariance `D(I⊗S + S⊗I)/2`; for
`f` with `f(0) = 0` this gives the Schatten trace generator; the divided-difference summands are
`≤ 0` for concave `f`; the first two terms are `≤ -(Dp(1-p)/2)Σ_i λ_i²(λ_i+ε)^{p-2}` because
`gu + (1-p)u²S_ii ≥ (1-p)u²`, `u = λ_i/(λ_i+ε)`, `T_ii ≤ g`. The non-polynomial `f_ε` enters by
polynomial approximation through three derivatives on a trace stop, and the fixed clock/current
moments remove the stops.

This statement concerns only the regularized traces and their dissipation and does not imply the
homogeneous decay: removing the regularization error needs the smaller-power bound `E H_{p₀}` on
the later interval, i.e. the entrance class (`ClockFractionalEntranceContract.later` passed to
the limit), plus the power regularization bound, Gronwall and `ε ↓ 0`. Those steps are proved in
`ns_limitDecay`. Conversely `limitDecay` does not mention `f_ε` or the dissipation term and does
not imply this statement. -/
def NsRegularizedLimitGenerator : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : ClockWord → ℝ → Ω → ℂ),
      IsWordLimit b E noTags (fun _ => q) (t₁ + R) P Z →
    ∀ μ : ℝ → Ω → Measure ℝ, (∀ t : ℝ, t₁ + R ≤ t → ∀ᵐ ω ∂P, IsClockMeasure Z t ω (μ t ω)) →
    ∀ ε : ℝ, 0 < ε → ∀ u₁ u₂ : ℝ, t₁ + R < u₁ → u₁ ≤ u₂ →
      ∫⁻ ω, nsRegTrace p ε (μ u₂ ω) ∂P +
          ENNReal.ofReal (nsDecayRate b E p) *
            ∫⁻ u in Icc u₁ u₂, ∫⁻ ω, nsDissTrace p ε (μ u ω) ∂P ≤
        ∫⁻ ω, nsRegTrace p ε (μ u₁ ω) ∂P

/-- Critical limits of the clock exist along subsequences.

Fixed `0 < b < 1/2`, bulk `E`, a unit source `IsUnitSource t₁ R q` whose injection ends at a
positive time `t₁ + R > 0`. Every strictly increasing sequence of widths `ψ` has a further
subsequence `ψ ∘ φ` along which the ordinary word values of the one-source family converge in
finite-dimensional distributions (`NsFddAlong`, bounded continuous tests) to a joint critical word
limit `(P, Z)` on `[t₁ + R, ∞)` (`IsWordLimit`) that carries, at every time `t ≥ t₁ + R`, a.s. a
limiting clock trace measure `μ_t` (`IsClockMeasure`). -/
def NsCriticalClockLimitsExist : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q → 0 < t₁ + R →
    ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : ClockWord → ℝ → Ω → ℂ)
        (μ : ℝ → Ω → Measure ℝ),
        IsWordLimit b E noTags (fun _ => q) (t₁ + R) P Z ∧
        NsFddAlong b E q (t₁ + R) P Z (ψ ∘ φ) ∧
        ∀ t : ℝ, t₁ + R ≤ t → ∀ᵐ ω ∂P, IsClockMeasure Z t ω (μ t ω)

end BlockBand.Endpoints
