module

public import BlockBand.Internal.Contracts.Layers
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Mode bound, window transfer and small critical variance

Statements of the Fourier mode bound for eigenvector block masses, the transfer of microscopic
window expectations, and the profile-variance and mode bounds for critical marked laws at small
ratio.

## Conventions

* **Ranks** are zero-based (`α : Fin p.N`, the paper's rank is `α.val + 1`), as in
  `IsBulkRank`; eigenvalues are the increasing raw-`H` eigenvalues
  `physicalOrderedEigenvalue`; block masses are `physicalOrderedBlockMass`.
* **Fourier modes.** `A_m = Σ_k z_m^{-k} p_{αk}` is `QUE.Fourier.physicalMode p α m`
  (`m : ZMod n`, `1 ≤ m < n` is `m ≠ 0`) and `d_m = |1 - z_m| = ‖1 - stdAddChar m‖`, as in
  `QUE.PairResidual.mode_variance_le_of_pair`.
* **Window observables.** "A nonnegative observable `0 ≤ A_α ≤ 1` invariant under adding a
  scalar matrix to `H`" is a Borel function `A α : SiteMatrix → ℝ` with values in `[0,1]` and
  `A α (H + t I) = A α H` for every real `t` (measurability is what gives `E A_α` its
  meaning). It may depend on the rank and on the whole matrix.
* **Bulk margin containing `N F_sc(E)`.** The ranks `ϑ ≤ α/N ≤ 1-ϑ` (`IsBulkRank p ϑ`) with
  `ϑ < F_sc(E) < 1 - ϑ`: the proof uses that the two boundary ranks of the margin have
  classical locations a fixed distance from `E`, i.e. `N F_sc(E)` is inside
  the margin.
* **The remainder `r_{n,W,q}`** is a function of `(n, W)` alone, chosen after the fixed data
  `b, T, E, ρ, w, ϑ, q` and before the model, the observables and `ε`; "tends to zero along
  every fixed critical sequence" is `Tendsto (r (s.n j) (s.W j)) atTop (𝓝 0)` for every
  `CriticalSequence τ`, `τ > 0`. The `limsup` corollary in the paper is a consequence of the
  finite inequality and is not a separate clause.
* **Critical subsequential marked laws** `𝔏_{τ,b,E}`: weak limits along a strictly increasing
  subsequence of the physical marked laws `(R j).markedLaw E` of a critical sequence with ratio
  `τ`, the binder pattern of `Inputs.ForEveryCriticalLimit` (`E² < 4`, every realization).
* **Mark functionals.** For a marked point measure `ξ`, `Σ_α w(u_α) F(ν_α)` is
  `∫ x, w x.1 * F x.2 ∂ξ.marked`; expectations are lower Lebesgue integrals of nonnegative
  integrands, so the bounds below also assert finiteness ("these expectations are finite").
  `ν(φ) = ∫ φ dν`, `φ̄ = ∫_𝕋 φ` (Haar probability on `AddCircle 1`), and the Fourier coefficient
  `∫ e^{-2πimr} ν(dr)` is `∫ fourier (-m) dν`. `‖φ - φ̄‖_∞ ≤ M` is the hypothesis
  `∀ r, |φ r - φ̄| ≤ M`.
* **Spectral weights** in `V_P(w,φ)` and `v_m(P)` are `SpectralWeight`s (smooth,
  compactly supported, nonnegative, `∫ w = 1`); the paper's `V_P(φ)` is `V_P(w,φ)` for any
  such `w`, and the bounds are uniform in `w`.
* **Profile marks of the limit** are the atoms `x` of `ξ.marked` (`ξ.marked.measure {x} ≠ 0`);
  `ν ∈ H^{-s}(𝕋)` is `Σ_m (1 + 4π²m²)^{-s} |ν̂_m|² < ∞`; "no atoms" is `ν {r} = 0` for every `r`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.WindowAngular

open MeasureTheory Filter Topology
open BlockBand.Model.Construction BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal ContDiff

/-!
## 1. The mode bound in the proof of the QUE theorem
-/

/-- The mode separation `d_m = |1 - z_m|`, `z_m = e^{2πim/n}`. -/
def modeSeparation (p : Parameters) (m : ZMod p.n) : ℝ :=
  ‖(1 : ℂ) - ZMod.stdAddChar m‖

/-- **The mode bound**, a lemma of the proof of the QUE theorem (used in the small-ratio
critical theorem). `b, ϑ, T` first; then `C`; for every
`4 ≤ n ≤ TW`, every model, every `ϑ`-bulk rank `α` (one-based convention of `IsBulkRank`) and
every nonzero mode `m`, under the physical law, `γ_m = E|A_m|²` and `d_m = |1 - z_m|`:
`γ_m ≤ C{1/(W d_m) + 1/(√n W^{3/2} d_m²)} ≤ C{n/W + (n/W)^{3/2}}`.
The paper proves it for `W > W₀`; for `W ≤ W₀` it holds with `C ≥ 2W₀` since `γ_m ≤ 1` and
`d_m ≤ 2`, so the statement carries no width threshold.
-/
def ModeBoundContract (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n W : ℕ) (hn : 4 ≤ n) (hW : 0 < W), (n : ℝ) ≤ T * (W : ℝ) →
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p θ α →
        ∀ m : ZMod p.n, m ≠ 0 →
          let γ := ∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix)
          let d := modeSeparation p m
          γ ≤ C * (1 / ((W : ℝ) * d) +
              1 / (Real.sqrt n * ((W : ℝ) * Real.sqrt W) * d ^ 2)) ∧
            γ ≤ C * ((n : ℝ) / W + ((n : ℝ) / W) ^ (3 / 2 : ℝ))

/-!
## 2. The window transfer theorem
-/

/-- `a_{n,W} = √n + n/W + W^{2/5} log(2W)`. -/
def countScale (n W : ℝ) : ℝ :=
  Real.sqrt n + n / W + W ^ (2 / 5 : ℝ) * Real.log (2 * W)

/-- A matrix observable invariant under adding a real scalar matrix to `H`. -/
def IsScalarShiftInvariant {p : Parameters} (A : p.SiteMatrix → ℝ) : Prop :=
  ∀ (H : p.SiteMatrix) (t : ℝ), A (H + (t : ℂ) • (1 : p.SiteMatrix)) = A H

/-- The microscopic physical window expectation
`𝒱_{n,W} = E Σ_α w(Nρ(λ_α - E)) A_α`, under the exact physical law. -/
def windowExpectation (p : Parameters) (model : p.GaussianRingModel) (E ρ : ℝ)
    (w : ℝ → ℝ) (A : Fin p.N → p.SiteMatrix → ℝ) : ℝ :=
  ∫ H, ∑ α : Fin p.N,
      w ((p.N : ℝ) * ρ * (physicalOrderedEigenvalue p H α - E)) * A α H
    ∂(model.law : Measure p.SiteMatrix)

/-- **The window transfer theorem** (used in the small-ratio critical theorem and the endpoint
theorems). Fixed first:
`b`, `T`, a bulk energy `E` (`E² < 4`), a
unit `ρ > 0`, a continuous compactly supported `w ≥ 0` with `∫ w = 1`, a bulk margin `ϑ`
with `ϑ < F_sc(E) < 1 - ϑ`, and `q > 1`.
Then `C_q` and a remainder `r(n, W)` with
`r → 0` along every critical sequence `n/W → τ > 0`, both independent of the observables and
of `ε`.
For every `4 ≤ n ≤ TW`, model, `0 < ε ≤ 1` and Borel observables `0 ≤ A_α ≤ 1`
invariant under scalar shifts, if `E A_α ≤ ε` for every rank in the margin, then
`𝒱_{n,W} ≤ C_q (a_{n,W}/√n) ε^{1-1/q} + r(n,W)`.
No independence of `A_α` from the spectrum
and no rank-conditioned density bound is assumed.
-/
def WindowTransferContract : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (T E ρ : ℝ), E ^ 2 < 4 → 0 < ρ →
    ∀ w : ℝ → ℝ, Continuous w → HasCompactSupport w → (∀ x, 0 ≤ w x) → ∫ x, w x = 1 →
    ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 → ϑ < semicircleCDF E → semicircleCDF E < 1 - ϑ →
    ∀ q : ℝ, 1 < q →
      ∃ (C : ℝ) (r : ℕ → ℕ → ℝ),
        (∀ (τ : ℝ) (s : CriticalSequence τ), 0 < τ →
          Tendsto (fun j => r (s.n j) (s.W j)) atTop (𝓝 0)) ∧
        ∀ (n W : ℕ) (hn : 4 ≤ n) (hW : 0 < W), (n : ℝ) ≤ T * (W : ℝ) →
          let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
          ∀ (model : p.GaussianRingModel) (ε : ℝ), 0 < ε → ε ≤ 1 →
          ∀ A : Fin p.N → p.SiteMatrix → ℝ, (∀ α, Measurable (A α)) →
            (∀ α H, 0 ≤ A α H ∧ A α H ≤ 1) → (∀ α, IsScalarShiftInvariant (A α)) →
            (∀ α, IsBulkRank p ϑ α →
              ∫ H, A α H ∂(model.law : Measure p.SiteMatrix) ≤ ε) →
            windowExpectation p model E ρ w A ≤
              C * (countScale n W / Real.sqrt n) * ε ^ (1 - 1 / q) + r n W

/-!
## 3. The small-ratio critical theorem
-/

/-- `P ∈ 𝔏_{τ,b,E}`: `P` is a weak limit, along a strictly increasing subsequence, of the
physical marked laws at energy `E` of some critical sequence with ratio `τ` and some
realizations (the binder pattern of `Inputs.ForEveryCriticalLimit`). -/
def IsCriticalMarkedLimit (τ b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (P : ProbabilityMeasure MarkedPointMeasure) : Prop :=
  ∃ (s : CriticalSequence τ) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j))
    (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (fun j => (R (φ j)).markedLaw E) atTop (𝓝 P)

/-- `V_𝖯(w, φ) = E_𝖯 Σ_α w(u_α) |ν_α(φ) - φ̄|²`, as a lower integral. -/
def markVariance (P : ProbabilityMeasure MarkedPointMeasure) (w : SpectralWeight)
    (φ : Torus → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (w x.1 *
      |(∫ r, φ r ∂(x.2 : Measure Torus)) - ∫ r, φ r| ^ 2) ∂ξ.marked.measure
    ∂(P : Measure MarkedPointMeasure)

/-- `v_m(𝖯) = E_𝖯 Σ_α w(u_α) |∫ e^{-2πimr} ν_α(dr)|²`, as a lower integral. -/
def modeVariance (P : ProbabilityMeasure MarkedPointMeasure) (w : SpectralWeight)
    (m : ℤ) : ℝ≥0∞ :=
  ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (w x.1 *
      ‖∫ r, fourier (-m) r ∂(x.2 : Measure Torus)‖ ^ 2) ∂ξ.marked.measure
    ∂(P : Measure MarkedPointMeasure)

/-- A smooth real test on the unit torus (`C^∞` `1`-periodic lift, `ContDiff ℝ ∞`, as in
`ProfileTest`; not the analytic class `⊤ = ω`); constants are allowed. -/
def IsSmoothTorusTest (φ : Torus → ℝ) : Prop :=
  Continuous φ ∧ ContDiff ℝ ∞ (fun x : ℝ => φ (QuotientAddGroup.mk x))

/-- The small-ratio critical theorem.
* `variance`: `b`, a bulk energy `E` (`E² < 4`) and `0 < η < 1` first; then `C_{b,E,η}`;
  uniformly over `0 < τ ≤ 1`, every `𝖯 ∈ 𝔏_{τ,b,E}`, every spectral weight `w` and every
  smooth real `φ` with `‖φ - φ̄‖_∞ ≤ M`: `V_𝖯(w, φ) ≤ C M² τ^{1-η}`.
* `mode`: `b, E`, `T < ∞` and `0 < η < 1` first; then `C_{b,E,T,η}`; for every `0 < τ ≤ T`,
  `𝖯 ∈ 𝔏_{τ,b,E}`, `w` and integer `m ≠ 0`:
  `v_m(𝖯) ≤ C min(1, [τ/|m| + τ^{3/2}/m²]^{1-η})`.
* `diffuse`: for each fixed `τ > 0` and `𝖯 ∈ 𝔏_{τ,b,E}`, `𝖯`-almost surely every profile mark
  `ν` of the limiting point process lies in `H^{-s}(𝕋)` for every `s > 0` and has no atoms.
No identification or uniqueness of the critical law is used. -/
structure SmallCriticalContract : Prop where
  variance : ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), E ^ 2 < 4 →
    ∀ η : ℝ, 0 < η → η < 1 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (τ : ℝ), 0 < τ → τ ≤ 1 → ∀ P : ProbabilityMeasure MarkedPointMeasure,
        IsCriticalMarkedLimit τ b E hb hb' P →
        ∀ (w : SpectralWeight) (φ : Torus → ℝ), IsSmoothTorusTest φ →
        ∀ M : ℝ, (∀ r, |φ r - ∫ r', φ r'| ≤ M) →
          markVariance P w φ ≤ ENNReal.ofReal (C * M ^ 2 * τ ^ (1 - η))
  mode : ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), E ^ 2 < 4 →
    ∀ T η : ℝ, 0 < η → η < 1 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (τ : ℝ), 0 < τ → τ ≤ T → ∀ P : ProbabilityMeasure MarkedPointMeasure,
        IsCriticalMarkedLimit τ b E hb hb' P →
        ∀ (w : SpectralWeight) (m : ℤ), m ≠ 0 →
          modeVariance P w m ≤ ENNReal.ofReal (C * min 1
            ((τ / |(m : ℝ)| + τ ^ (3 / 2 : ℝ) / (m : ℝ) ^ 2) ^ (1 - η)))
  diffuse : ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), E ^ 2 < 4 →
    ∀ τ : ℝ, 0 < τ → ∀ P : ProbabilityMeasure MarkedPointMeasure,
      IsCriticalMarkedLimit τ b E hb hb' P →
      ∀ᵐ ξ ∂(P : Measure MarkedPointMeasure), ∀ x : MarkedSpectralSpace,
        ξ.marked.measure {x} ≠ 0 →
          (∀ σ : ℝ, 0 < σ → Summable (fun m : ℤ =>
            (1 + 4 * Real.pi ^ 2 * (m : ℝ) ^ 2) ^ (-σ) *
              ‖∫ r, fourier m r ∂(x.2 : Measure Torus)‖ ^ 2)) ∧
          ∀ r : Torus, (x.2 : Measure Torus) {r} = 0

end BlockBand.Internal.Contracts.WindowAngular
