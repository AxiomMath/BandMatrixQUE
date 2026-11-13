module

public import BlockBand.SourceProcess.ClosedSummedProof.ClosedInt

/-!
# The closed path as a Hermitian two-port chain with summable errors

**`IsClosedChain … W Vs X`** (structure of the closed path at width `W`, steps `n_s ≤ j < ⌊WT⌋`):
`X j` is a measurable function of the closed past (`cpast j`: path up to `j`, samples, phase),
Hermitian, and almost surely, alive and without a birth at `j`,
* the closed frame is transported by the fresh layer of `X j`:
  `C_{j+1}(z)ᴴX_{j+1} = N(X j, A_j, B_{j+1})ᴴ C_j(z)ᴴX_j` with `N = freshTransport`
  (subsequent layers remain independent Gaussians conditional on the old state and phase; the
  full-source calculation applies with finitely many far open channels, and unused far
  coordinates can be padded by decoupled ones);
* the frame carries the whole current: `currentOf (X j) = V𝖣Vᴴ` (on `physCapEvent`, the `K`
  pairs carry every open mode).

**`chainErr`** is the one-layer error scale of `gram_layer_drift`/`gram_layer_cov` at `X j`:
`e(X j)·contrGram(X j, V_j) + layerRem W 1 e(X j)`, `e = layerErr` (`δ₀ + δ₁ + g/W + W⁻¹` of the
closed near Schur complement).

**`ClosedChainPin`**: for the data of `ClosedSummed`, some stationary jet and some
chain `X` (eventually in `W`) with `Σ_j E[1_{alive ∩ no birth} chainErr_j] → 0`. This is the
contracting-words lemma for the closed path: contracting Gram coordinates decay geometrically,
`E e ≲ W⁻¹`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedSumProof
open BlockBand.SourceProcess.ContractingWords BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedPath
open scoped ENNReal

variable {W p K M : ℕ}

/-- A two-port state for every length, as a function of the closed past. -/
abbrev ChainState (W p M : ℕ) :=
  (j : ℕ) → ClosedPast W j p M → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ

/-- Alive and no birth at step `j` (the event of the drift and bracket sums). -/
abbrev aliveNB (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    Set (SampledPath W p M × ℝ) :=
  closedAlive b E s T h q R W j Vs ∩ noBirth j

/-- **The closed path as a Hermitian two-port chain** at width `W`. -/
def IsClosedChain (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (X : ChainState W p M) :
    Prop :=
  ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
    Measurable (X j) ∧ (∀ x, (X j x).IsHermitian) ∧
    ∀ᵐ y ∂lawW b T q M W, y ∈ aliveNB b E s T h q R W j Vs →
      closedFrameAt b E s T h q W (j + 1) Vs y =
          (freshTransport b E (X j (cpast j y)) (freshSample W j y.1.1))ᴴ *
            closedFrameAt b E s T h q W j Vs y ∧
        currentOf b E (X j (cpast j y)) = closedFrameAt b E s T h q W j Vs y *
          srcSignature K (Fin p × Fin M) * (closedFrameAt b E s T h q W j Vs y)ᴴ

/-- The one-layer error scale at step `j`. -/
def chainErr (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (X : ChainState W p M)
    (σ : ℂ) (j : ℕ) (y : SampledPath W p M × ℝ) : ℝ :=
  layerErr b E σ (X j (cpast j y)) *
      contrGram b E (X j (cpast j y)) (closedFrameAt b E s T h q W j Vs y) +
    layerRem W 1 (layerErr b E σ (X j (cpast j y)))

/-- The summed one-layer error scale. -/
def chainErrSum (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (X : ChainState W p M)
    (σ : ℂ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∫⁻ y,
    (aliveNB b E s T h q R W j Vs).indicator
      (fun y => ENNReal.ofReal (chainErr b E s T h q W Vs X σ j y)) y ∂lawW b T q M W

/-- **`ClosedChainPin`**: the closed path is a Hermitian two-port chain with summable one-layer
errors. This is stated as a hypothesis. -/
def ClosedChainPin : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) → ∀ h : ℝ, 0 < h → h < 1 →
    ∀ K M : ℕ, 0 < M → ∀ R : ℝ,
    ∀ Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      (∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)) →
    ∃ σ : ℂ, IsStationaryJet b E σ ∧ ∃ X : (W : ℕ) → ChainState W p M,
      (∀ᶠ W in atTop, IsClosedChain b E s T h q R W (Vs W) (X W)) ∧
      Tendsto (fun W => chainErrSum b E s T h q R W (Vs W) (X W) σ) atTop (𝓝 0)

end BlockBand.SourceProcess.ClosedSummedProof
