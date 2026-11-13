module

public import BlockBand.Endpoints.Response.ClockEntranceLayerDefs

/-!
# The matrix Taylor step of the clock Jensen gap

Part of the clock fractional-entrance lemma: apply the integral Hessian for `Tr B^p` to
`B = A^{1/2}LL*A^{1/2}`; on the retained event the interpolation segment is bounded by `KA`, and
the concavity gap is bounded below; zero eigenvalues follow by positive regularization.

* `FractionalTraceJensenGap` — the model-free second-order (integral
  Hessian) Jensen gap of `Φ = Tr(·)^p`, `0 < p < 1`, for a random PSD matrix `B` with integrable
  entries, bounded on a measurable event `G` by a fixed PSD `Q = V diag(q) V*` that also bounds
  `E B`:
  `E Φ(B) + c E[1_G Σ_{ij} |(V*(B - EB)V)_ij|² ∫_0^∞ s^{p-1}ds/((q_i+s)(q_j+s))] ≤ Φ(E B)`.
  It is proved as `fractionalTraceJensenGap_holds`.

It contains no random-band-matrix object (no layer law, no passive input, no transmission): it is
the matrix-analytic content of this step alone. Everything else in `ClockLayerJensenGap` (the
covariance gap in the `A`-eigenbasis, the retained event, the `A^{1/2}`-sandwich, the expectation
and the kernel bookkeeping) is proved elsewhere.

**Why it is true** (deterministic matrix analysis): for `E B ≻ 0`,
`φ(τ) = Φ(EB + τH)`, `H = B - EB`, is `C²` on `[0,1]` with
`φ''(τ) = -(p sin πp/π) ∫_0^∞ s^{p-1} Tr[(B_τ+s)⁻¹H(B_τ+s)⁻¹H] ds`
(`TransmissionLawContract.fractionalHessian`, applied at each `B_τ ≻ 0`); the first-order
term `φ'(0) = p Tr((EB)^{p-1}H)` is linear in `H` and has mean zero; on `G`, `B_τ ⪯ Q`, so
`(B_τ+s)⁻¹ ⪰ (Q+s)⁻¹` and by monotonicity of `P ↦ Tr(PHPH)` on `P ⪰ 0`,
`Tr[(B_τ+s)⁻¹H(B_τ+s)⁻¹H] ≥ Σ_{ij}|(V*HV)_ij|²/((q_i+s)(q_j+s))`. Taylor's formula with
integral remainder gives the gap with `c = p sin(πp)/(2π)`. Singular `E B` (and `q_i = 0`) follow
by the regularization `B ↦ B + εI`, `Q ↦ Q + εI`, `ε ↓ 0` (monotone convergence for the kernel;
entries `(V*HV)_ij` with `q_i = 0` vanish on `G`, since `0 ⪯ B, EB ⪯ Q`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers

/-- **The second-order Jensen gap of `Tr(·)^p`** (matrix-analytic,
model-free; proved as `fractionalTraceJensenGap_holds`). For `0 < p < 1` there is `c > 0` such that for every probability space, every random
PSD `B` with integrable entries, every measurable event `G` and every `Q = V diag(q) V*` (`V`
unitary, `q ≥ 0`) with `E B ⪯ Q` and `B ⪯ Q` on `G`,
`E Tr B^p + c ∫_G Σ_{ij} |(V*(B - EB)V)_ij|² ∫_0^∞ s^{p-1}ds/((q_i+s)(q_j+s)) ≤ Tr (EB)^p`.
(`concavityKernel p a b s = s^{p-1}/((a+s)(b+s))`; for `q_i = q_j = 0` the Bochner integral is
the junk value `0`, and such entries vanish on `G` anyway.) -/
def FractionalTraceJensenGap : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (B : Ω → Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) (q : Fin n → ℝ)
      (G : Set Ω),
      (∀ ω, (B ω).PosSemidef) → (∀ a b, Integrable (fun ω => B ω a b) μ) → MeasurableSet G →
      V ∈ unitaryGroup (Fin n) ℂ → (∀ i, 0 ≤ q i) →
      (V * diagonal (fun i => ((q i : ℝ) : ℂ)) * star V - matrixExpect μ B).PosSemidef →
      (∀ ω ∈ G, (V * diagonal (fun i => ((q i : ℝ) : ℂ)) * star V - B ω).PosSemidef) →
      ∫⁻ ω, ENNReal.ofReal (fracTrace p (B ω)) ∂μ +
          ENNReal.ofReal c * ∫⁻ ω in G, ENNReal.ofReal (∑ i, ∑ j,
            ‖(star V * (B ω - matrixExpect μ B) * V) i j‖ ^ 2 *
              ∫ s in Set.Ioi (0 : ℝ), concavityKernel p (q i) (q j) s) ∂μ ≤
        ENNReal.ofReal (fracTrace p (matrixExpect μ B))

end BlockBand.Endpoints
