module

public import BlockBand.Transmission.DualLift.LReal

/-!
# Statements of the Feller-type continuity lemmas for the lift

Definitions only: `LiftStartContinuity` (start continuity) and `LiftCornerAbsorption` (corner
absorption), used for the `unique` and `law` fields of `DualBoundaryStartContract`.

Setting: any `S : Type`, any probability `μ` on `S`, the driver space `LΩ S` with law
`LP μ` and the augmented filtration; two admissible random starts `ξ, ξ'` (`IsLiftStart`:
augmented-`𝓕₀`-measurable, values in the invariant manifold `liftM`), and any two lifted
families `F, F'` (exit-time solutions of all radii) on the **same** driver space.
`F.zeta = sup_n e_n` is the lifetime `ζ`. `liftZbar F` is `Z̄ = π(ξ) 1{t < ζ}` read off the
lifted realization: `Z₂` where the level `N₂` is `1`, and `0` where it is `0`. (`Z₂` itself is
**not** `0` after `ζ`: there it keeps the value `π(ξ)` of the radius-`0` family; only the
level-truncated state, as in `truncDualState`, is meaningful.) Norms: sup norms on `ℝ⁶` and
`ℝ²`.

**Form of the statements.** A modulus uniform over all start laws,
`E[sup_{t≤T}|Z̄^ξ − Z̄^{ξ'}| ∧ 1] ≤ ω_T(E[|ξ − ξ'| ∧ 1])`, is false: for deterministic starts
with `|w| = R`, `w' = w + 1/(2R)` one has `|x − x'| ≥ 1` at `t = 0`, while `|ξ − ξ'| → 0` as
`R → ∞`. The statements therefore localize the starts: the closeness `δ` depends on `T`, `η`
and a bound `R` on `‖ξ‖` (which also bounds `s = 1/S̃ ≤ R`, i.e. keeps the start at distance
`≥ 1/R` from the corner), and the bad event is intersected with `{‖ξ‖ ≤ R}`. Closeness of the
starts is measured by the Ky Fan condition `P(‖ξ − ξ'‖ ≥ δ) ≤ δ`. Both uses fit: in the
uniqueness proof the starts `σ(Z^i_s)` converge in probability to `σ(z₀)` with `z₀` off the
corner, so `P(‖ξ‖ > R)` is small for large `R`; in the law identity the starts are
deterministic.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Transmission.DualLift
open scoped NNReal ENNReal

/-- `Z̄_t = π(ξ_t) 1{t < ζ}` from the realization of `B1Family`: the coordinates `Z₂` at level `N₂ = 1`, and
`0` at level `0` (the state seen by the `truncDualState` at `p = 1`).
-/
def liftZbar {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
    {ξ : LΩ S → Fin 6 → ℝ} (F : LiftFamily μ D0 ξ) (t : ℝ≥0) (ω : LΩ S) : Fin 2 → ℝ :=
  if F.N₂ t ω = 1 then F.Z₂ t ω else 0

/-- **Start continuity, as a named statement.** For every horizon `T`, start bound `R` and
tolerance `η > 0` there is `δ > 0` such that, on any driver space, for any two admissible random
starts with `P(‖ξ − ξ'‖ ≥ δ) ≤ δ` and any two lifted families,
`P(‖ξ‖ ≤ R, sup_{t ≤ T} ‖Z̄_t − Z̄'_t‖ ≥ η) ≤ η`.
Here `Z̄ = π(ξ)1{t<ζ}` is continuous through `ζ`, so this is uniform convergence on `[0,T]` in
probability, through the corner. -/
def LiftStartContinuity (D0 : ℝ) : Prop :=
  ∀ (T : ℝ≥0) (R η : ℝ), 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
      (ξ ξ' : LΩ S → Fin 6 → ℝ), IsLiftStart μ ξ → IsLiftStart μ ξ' →
      ∀ (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ'),
      LP μ {ω | δ ≤ ‖ξ ω - ξ' ω‖} ≤ ENNReal.ofReal δ →
      LP μ {ω | ‖ξ ω‖ ≤ R ∧ ∃ t : ℝ≥0, t ≤ T ∧ η ≤ ‖liftZbar F t ω - liftZbar F' t ω‖} ≤
        ENNReal.ofReal η

/-- **Corner absorption, as a named statement.** Same quantifiers as `LiftStartContinuity`;
the conclusion is closeness in probability of the truncated lifetimes `ζ ∧ T` and `ζ' ∧ T`:
`P(‖ξ‖ ≤ R, |ζ ∧ T − ζ' ∧ T| ≥ η) ≤ η`. With start continuity this gives the convergence of
`1{ζⁿ ≤ t}` at every `t` that is not an atom of the law of `ζ`. -/
def LiftCornerAbsorption (D0 : ℝ) : Prop :=
  ∀ (T : ℝ≥0) (R η : ℝ), 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
      (ξ ξ' : LΩ S → Fin 6 → ℝ), IsLiftStart μ ξ → IsLiftStart μ ξ' →
      ∀ (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ'),
      LP μ {ω | δ ≤ ‖ξ ω - ξ' ω‖} ≤ ENNReal.ofReal δ →
      LP μ {ω | ‖ξ ω‖ ≤ R ∧ η ≤ |((min (T : WithTop ℝ≥0) (F.zeta ω)).untopA : ℝ) -
        ((min (T : WithTop ℝ≥0) (F'.zeta ω)).untopA : ℝ)|} ≤ ENNReal.ofReal η

end BlockBand.Transmission.DualFeller
