module

public import BlockBand.Endpoints.Sine.CrossingSine
public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Asymptotics.CriticalSequence

/-!
# Definitions for the admission of the velocity error along the scalar pair flow

This file defines the flow observable and the velocity error, states the pair clause of local
mass flatness (`FaLocalMassFlatPair`) and the mass Palm identity under a deterministic pair shift
(`FaShiftedMassPalm`: the exact mass Palm identity for the law of `H + a P_S`), and states
`FlowAdmissionStatement`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks
open scoped ENNReal

/-!
## The observable along the flow
-/

/-- `Σ_α χ(u_α)|(n/2)‖P_Sψ_α‖² - 1|` of a matrix `H` (raw `H`, ranks with multiplicity), in
`ℝ≥0∞`. -/
def fa_obs (p : Parameters) (i : ZMod p.n) (E : ℝ) (χ : ℝ → ℝ) (H : p.SiteMatrix) : ℝ≥0∞ :=
  ∑ α : Fin p.N, ENNReal.ofReal
    (χ (microCoord p E (physicalOrderedEigenvalue p H α)) *
      |(p.n : ℝ) / 2 * pairMass p i α H - 1|)

/-- `Σ_α χ(u_α(t))|v_α(t) - 1|` at time `t`, with `H(t) = H + t/(𝒩ρ) P_S`,
`u_α(t) = Nρ(λ_α(H(t)) - E)`, `v_α(t) = (n/2)‖P_Sψ_α(t)‖²`. -/
def fa_flowIntegrand (p : Parameters) (i : ZMod p.n) (E : ℝ) (χ : ℝ → ℝ) (H : p.SiteMatrix)
    (t : ℝ) : ℝ≥0∞ :=
  fa_obs p i E χ (pairFlow p i H E t)

/-- `E ∫_{-T}^T Σ_α χ(u_α(t))|v_α(t) - 1| dt` (the left side of flow admission before the
limsup), exact physical law, Lebesgue measure in `t`. -/
def fa_velocityError (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n) (E T : ℝ)
    (χ : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ H, (∫⁻ t in Set.Icc (-T) T, fa_flowIntegrand p i E χ H t)
    ∂(model.law : Measure p.SiteMatrix)

/-!
## The pair clause of local mass flatness
-/

/-- `E Σ_α w(u_α)|(n/2)‖P_Sψ_α‖² - 1|` (exact physical law, Bochner integral). The body is
identical to `lmf_pairFlatness`. -/
def fa_pairFlatness (p : Parameters) (model : p.GaussianRingModel) (E : ℝ) (w : ℝ → ℝ)
    (i : ZMod p.n) : ℝ :=
  ∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      |(p.n : ℝ) / 2 * BlockBand.Internal.Contracts.CoareaPalm.pairMass p i α H - 1|
    ∂(model.law : Measure p.SiteMatrix)

/-- **The pair clause of the local mass flatness theorem**: for every fixed adjacent pair `S`
and `0 < τ ≤ T₀`, `limsup_{W→∞, n/W→τ} E Σ_α w(u_α)|(n/2)‖P_Sψ_α‖² - 1| ≤ C_{b,E,T₀}√τ`, for a
window `w ≥ 0` smooth, compactly supported, `∫ w = 1` (`IsWindow` and `C^∞`).
Law: exact physical law.
Quantifiers:
`0 < b < 1/2`, bulk `-2 < E < 2`, `T₀ > 0`, the window
`w`; then `C`; then every `τ ∈ (0,T₀]`, critical sequence, models and pair sequence `i_j`;
`limsup ≤ C√τ` as `∀ ε > 0, ∀ᶠ j, · ≤ C√τ + ε`.
This is implied by (the first conjunct of) `LocalMassFlatStatement`, which chooses `C` before `w` (`fa_pairFlatness` = `lmf_pairFlatness`); allowing `C` to depend on
the fixed window is the weaker reading, so nothing is strengthened.
The one-block clause is not
used.
-/
def FaLocalMassFlatPair : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 → ∀ T₀ : ℝ, 0 < T₀ →
    ∀ w : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w → IsWindow w → ∃ C : ℝ,
    ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
      (i : ∀ j, ZMod (s.parameters b hb hb' j).n),
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        fa_pairFlatness (s.parameters b hb hb' j) (R j) E w (i j) ≤ C * Real.sqrt τ + ε

/-!
## The mass Palm identity under a deterministic pair shift
-/

/-- The exterior `ω = (H_R, C, V)` with the pair residual shifted, `(H_R, C, V + a I_S)`:
`assemble (fa_shiftExterior a ω) G = assemble ω G + a P_S`. -/
def fa_shiftExterior (p : Parameters) (i : ZMod p.n) (a : ℝ) (ω : SplitState p i) :
    SplitState p i :=
  (ω.1, ω.2.1, ω.2.2 + (a : ℂ) • 1)

/-- **The mass Palm identity under a deterministic scalar pair shift.** In the proof of flow
admission the mass-weighted term is uniformly bounded: the mass Palm identity cancels the
crossing derivative, and its deformed fresh-GUE density is at most `C_b𝒩` regardless of the
scalar shift. `ExactPalmContract.mass` is stated only for the law `model.law` itself; the same
identity is applied to the law of `H + a P_S`. Under the fresh-pair split (`IsPairSplitting` at
`s = min(b, 1-2b)`), `H + a P_S = assemble (H_R, C, V + a I) G`: the shift is a deterministic
deformation of the pair residual `V` and leaves the fresh `G ~ GUE_𝒩(s/𝒩)` and its independence
untouched. Statement: for every admissible `p`, model, pair, splitting law `Pω`,
measurable frame `U`, real `a` and measurable `f ≥ 0` of `(e, p)`:
`E Σ_α q_{αS}(H + aP_S) f(λ_α(H + aP_S), p_α(H + aP_S)) = E_ext ∫ 𝒜^{(a)}_e[f(e, p^{(a)}(v,e))] de`,
the right side being that of `ExactPalmContract.mass` with `ω` replaced by
`fa_shiftExterior a ω`.
At `a = 0` it is `ExactPalmContract.mass` (up to `+ 0`). It is proved from `CoareaContract` as
`faShiftedMassPalm_holds`.
-/
def FaShiftedMassPalm : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
    (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
    ∀ U, IsPairFrame p i U → ∀ (a : ℝ) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞),
      Measurable (Function.uncurry f) →
      (∫⁻ H, ∑ α : Fin p.N,
          ENNReal.ofReal (pairMass p i α (H + (a : ℂ) • pairProjector p i)) *
          f (physicalOrderedEigenvalue p (H + (a : ℂ) • pairProjector p i) α)
            (blockMassVector p (H + (a : ℂ) • pairProjector p i) α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ ω, ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          pairSectorFiber p i U (fa_shiftExterior p i a ω) e ℓ
            (fun v => f e (reconBlockMass p i (fa_shiftExterior p i a ω) e v)) ∂volume ∂Pω

/-!
## The statement
-/

/-- Flow admission. Law: the exact physical law. Fixed first: `0 < b < 1/2`, a bulk energy
`-2 < E < 2`, `T₀ > 0`, then `T, K < ∞` and a smooth (`C^∞`) compactly supported `χ ≥ 0` equal to
one on `[-K, K]`; then one constant `C = C_{T,χ}` (also depending on `b, E, T₀`); then for every
`τ ∈ (0, T₀]`, every critical sequence `n/W → τ` (`W → ∞`), all models and pair sequences
`S_j = {i_j, i_j + 1}`: `limsup_j E ∫_{-T}^T Σ_α χ(u_α(t))|v_α(t) - 1| dt ≤ C τ^{1/4}`, written
`∀ ε > 0, ∀ᶠ j, · ≤ Cτ^{1/4} + ε` (`fa_velocityError`, a lower integral in `ℝ≥0∞`). -/
def FlowAdmissionStatement : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 → ∀ T₀ : ℝ, 0 < T₀ →
    ∀ (T K : ℝ) (χ : ℝ → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x) → (∀ x ∈ Set.Icc (-K) K, χ x = 1) →
    ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
      (i : ∀ j, ZMod (s.parameters b hb hb' j).n),
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        fa_velocityError (s.parameters b hb hb' j) (R j) (i j) E T χ ≤
          ENNReal.ofReal (C * τ ^ (1 / 4 : ℝ) + ε)

end BlockBand.Endpoints
