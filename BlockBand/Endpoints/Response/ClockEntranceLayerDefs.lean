module

public import BlockBand.Endpoints.Response.ClockEntranceCore
public import BlockBand.Endpoints.Response.FractionalTraceIntegral

/-!
# The one-layer clock step: one-port inputs and the Jensen gap

This file states the hypotheses of the one-layer clock step.

* `cel_InJetDomain b E s d X`: `-Im X ⪰ 0`, `δ₀(X) ≤ d`, `δ₁(X) ≤ d`, `g(X) ≤ dW` (the
  deterministic form of `ce_jetDomain`).
* The one-port inputs:
  - `OnePortPassiveMean`: (a) `0 ⪯ E_ν LL* ⪯ (1 + Cδ₀ + CW⁻²) I`;
  - `OnePortOperatorMoments`: (b) `E_ν ‖L‖^{2r} ≤ C_r`;
  - `OnePortJetContraction`: (c) `δ_{0,+} ≤ ρδ₀ + C/W² + |ξ₊|`, `‖ξ₊‖_{L^r(ν)} ≤ C√r/W`.
* `cel_retained`, `cel_retainedGap`: the retained indices `T_ii ≤ 1/2` in the eigenbasis of `A`
  and the retained concavity kernel sum `Σ_{i,j ret} λ_iλ_j ∫_0^∞ s^{p-1}/((Kλ_i+s)(Kλ_j+s)) ds`.
* `ClockLayerJensenGap`: the integral-Hessian concavity gap of one fresh layer.
* `ClockLayerLogistic`: the deterministic conditional fractional logistic inequality, proved
  from `ClockLayerJensenGap` and (a) in `clockLayerLogistic_of_jensenGap`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Layers

/-- The deterministic positive-time scalar-jet domain of an old passive input `X` (the
deterministic form of `ce_jetDomain`): `Y = -Im X ⪰ 0`, `δ₀ ≤ d`, `δ₁ ≤ d` and `g = Tr T ≤ d W`. -/
def cel_InJetDomain (b E : ℝ) (s : ℂ) (d : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : Prop :=
  (passiveY X).PosSemidef ∧ jetDistance0 b E X ≤ d ∧ jetDistance1 b E s X ≤ d ∧
    conductanceOf (passiveTransmission b E X) ≤ d * W

/-!
## The one-port inputs
-/

/-- The passive cancelled mean gives
`E(LL*|X) = (I + Ωf + Ω̄f*)/(1 + αq/W) + O_op(δ₀² + δ₀q/W + W⁻²)` with `Ω = O(δ₀)`,
`f = R - c₀I` bounded (`‖R‖ ≤ η⁻¹` for passive `X`) and `αq/W ≥ 0`; on the jet domain
`q/W ≤ g/(4ηW) ≤ d/(4η)`, so the right side is `⪯ (1 + Cδ₀ + CW⁻²)I`. Also, by the weighted Ward
identity, `‖E(LL*|X) - I‖ ≤ C(d(X) + W⁻²)` on the scalar domain. The lower bound `0 ⪯ E_ν LL*` is
the positivity of the mean of the positive matrices `LL*`. -/
def OnePortPassiveMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℂ, IsStationaryJet b E s →
    ∃ (C d : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 < d ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, cel_InJetDomain b E s d X →
        (matrixExpect (freshLaw W b) (freshU b E X)).PosSemidef ∧
          (((1 + C * jetDistance0 b E X + C / (W : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) -
            matrixExpect (freshLaw W b) (freshU b E X)).PosSemidef

/-- **Operator-norm moments of the fresh one-port `L`** (one-port input (b)):
`E_ν ‖L‖^{2r} ≤ C_r` (Euclidean operator norm), for every fixed `r ∈ ℕ`, uniformly in passive
`X` in a fixed jet domain. In the paper, `L` has uniformly bounded fixed moments for `W ≥ W₀(p)`
(the weighted-layer lemma), extended to passive inputs by the scalar Poisson argument of the
passive-bounds lemma. It does not follow from `oneStepFluctuation`, which bounds `L^p` norms of
centered bilinear entries `u*(U - EU)v`; these do not control `‖L‖` (a supremum over
`W`-dimensional unit spheres). It follows from `OnePortOperatorMomentsContract` by
`onePortOperatorMoments_of_contract`.
-/
def OnePortOperatorMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℂ, IsStationaryJet b E s →
    ∃ d : ℝ, 0 < d ∧ ∀ r : ℕ, ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, cel_InJetDomain b E s d X →
        ∫⁻ ν, ENNReal.ofReal (‖freshL b E X ν‖ ^ (2 * r)) ∂freshLaw W b ≤ ENNReal.ofReal C

/-- **The one-step scalar-jet contraction** (one-port input (c)). In the clock step the
predictable contraction absorbs the term `C_p δ₀ H_p`, and the centered jet correlation costs
`C_p H_p/W`: there are `ρ < 1`, `C`, `a_* > 0` and a jet radius such that for every passive `X` in the jet
domain there is a fluctuation `ξ₊` (a function of the fresh layer) with
`δ_{0,+} ≤ ρδ₀ + C/W² + |ξ₊|` a.s. and `‖ξ₊‖_{L^r(ν)} ≤ C√r/W` for `1 ≤ r ≤ a_*W`, where
`δ_{0,+} = cec_freshJet0 b E X ν = ‖W⁻¹ Tr 𝒢_{port,port}(X, ν) - a‖` (`= δ₀(X_{j+1})` along the
path, `cec_passiveResolvent_succ`).

The bound is conditional on the old path, i.e. deterministic in the old `X`. The centered jet
correlation `E_ν|ξ₊|H_{p,+} ≤ C H_p/W` is not part of this statement: it is proved from (b) and
the `L²` case of (c) (`cel_cross_le`), through `H_{p,+} ≤ ‖L‖^{2p}H_p` and Cauchy–Schwarz.
It does not follow from `PassiveInitialScalarContract`, which bounds moments of `δ₀` along the
path, nor from `TransmissionLawContract.jetGap`, a scalar inequality at the stationary jet;
neither states the one-step drift of `δ₀`. It is a hypothesis here.
-/
def OnePortJetContraction : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℂ, IsStationaryJet b E s →
    ∃ (ρ C a d : ℝ) (W₀ : ℕ), 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧ 0 < a ∧ 0 < d ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, cel_InJetDomain b E s d X →
        ∃ ξ : LayerSample W .oneBlockOnePort → ℝ, AEStronglyMeasurable ξ (freshLaw W b) ∧
          (∀ᵐ ν ∂freshLaw W b,
            cec_freshJet0 b E X ν ≤ ρ * jetDistance0 b E X + C / (W : ℝ) ^ 2 + |ξ ν|) ∧
          ∀ r : ℝ, 1 ≤ r → r ≤ a * W →
            eLpNorm ξ (ENNReal.ofReal r) (freshLaw W b) ≤ ENNReal.ofReal (C * Real.sqrt r / W)

/-!
## Retained indices and the retained concavity kernel
-/

/-- The retained indices: in the eigenbasis of the Hermitian `A` (columns of
`hA.eigenvectorUnitary`, paired with `hA.eigenvalues`), the indices with
`T_ii = (U* T U)_ii ≤ 1/2`, `T = passiveTransmission b E X`. -/
def cel_retained (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : A.IsHermitian) : Finset (Fin W) :=
  Finset.univ.filter fun i =>
    ((star (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) * passiveTransmission b E X *
      (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)) i i).re ≤ 1 / 2

/-- The retained concavity kernel sum
`Σ_{i,j retained} λ_iλ_j ∫_0^∞ s^{p-1} ds/((Kλ_i+s)(Kλ_j+s))`. -/
def cel_retainedGap (b E p K : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i ∈ cel_retained b E X hA, ∑ j ∈ cel_retained b E X hA,
    hA.eigenvalues i * hA.eigenvalues j *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) /
        ((K * hA.eigenvalues i + t) * (K * hA.eigenvalues j + t))

/-!
## The Jensen gap and the deterministic logistic inequality
-/

/-- The integral-Hessian concavity (Jensen) gap of one fresh layer: for passive `X` in the jet
domain and every `A ⪰ 0`,
`E_ν Tr(L*AL)^p + (c/W) Σ_{i,j ret} λ_iλ_j ∫_0^∞ s^{p-1}ds/((Kλ_i+s)(Kλ_j+s)) ≤ Tr(Ū A)^p`,
`Ū = E_ν LL*` (note `Tr(ŪA)^p = Tr(A^{1/2}ŪA^{1/2})^p = Tr(E_ν B)^p`, `B = A^{1/2}LL*A^{1/2}`,
since `fracTrace` reads `charpoly`, and `Tr(L*AL)^p = Tr B^p`).

Derivation, at fixed old data: the covariance gap `E_ν|(LL* - E_νLL*)_{ij}|² ≥ c/W` for retained
`i, j` in the `A`-eigenbasis (from `PassiveCovarianceContract`, the fast source `f = -(2iη)⁻¹r`,
`|r_ii| ≤ √S_ii` and `σ₊ > |σ₋|`, which is `TransmissionLawContract.jetGap`); the event
`‖LL*‖ ≤ K` inside `E_ν` (from the fourth bilinear moment and (b)); the integral Hessian
`TransmissionLawContract.fractionalHessian` along the segment from `E_νB` to `B`, bounded by `KA`
on the event; positive regularization of zero eigenvalues. -/
def ClockLayerJensenGap : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ p : ℝ, 0 < p → p < 1 →
    ∀ s : ℂ, IsStationaryJet b E s →
      ∃ (K c d : ℝ) (W₀ : ℕ), 0 < K ∧ 0 < c ∧ 0 < d ∧ ∀ W : ℕ, W₀ ≤ W →
        ∀ X : Matrix (Fin W) (Fin W) ℂ, cel_InJetDomain b E s d X →
          ∀ (A : Matrix (Fin W) (Fin W) ℂ) (hA : A.PosSemidef),
            ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν))
                ∂freshLaw W b +
              ENNReal.ofReal (c / W * cel_retainedGap b E p K X hA.isHermitian) ≤
            ENNReal.ofReal (fracTrace p (matrixExpect (freshLaw W b) (freshU b E X) * A))

/-- The deterministic conditional fractional logistic inequality: for passive `X` in the jet
domain and every `A ⪰ 0`, with `H_p = Tr A^p`, `γ = Tr A`, `g = Tr T(X)`,
`E_ν H_p(L*AL) + (c/W) H_p²/γ^p ≤ (1 + Cδ₀ + CW⁻²) H_p + (C/W) |g|^{2(1-p)} γ^p`
(quotient `0` when `A = 0`). Proved from `ClockLayerJensenGap` and (a) in
`clockLayerLogistic_of_jensenGap`. -/
def ClockLayerLogistic : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ p : ℝ, 0 < p → p < 1 →
    ∀ s : ℂ, IsStationaryJet b E s →
      ∃ (C c d : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 < c ∧ 0 < d ∧ ∀ W : ℕ, W₀ ≤ W →
        ∀ X : Matrix (Fin W) (Fin W) ℂ, cel_InJetDomain b E s d X →
          ∀ A : Matrix (Fin W) (Fin W) ℂ, A.PosSemidef →
            ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν))
                ∂freshLaw W b +
              ENNReal.ofReal (c / W) * ENNReal.ofReal (fracTrace p A ^ 2 / A.trace.re ^ p) ≤
            ENNReal.ofReal ((1 + C * jetDistance0 b E X + C / (W : ℝ) ^ 2) * fracTrace p A) +
              ENNReal.ofReal (C / W) * ENNReal.ofReal
                (|conductanceOf (passiveTransmission b E X)| ^ (2 * (1 - p)) * A.trace.re ^ p)

end BlockBand.Endpoints
