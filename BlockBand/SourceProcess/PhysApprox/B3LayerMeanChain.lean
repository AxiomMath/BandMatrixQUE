module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepDefs
public import BlockBand.SourceProcess.ClosedSummedProof.LayerAux

/-!
# The closed path as a padded Hermitian two-port chain

**The padded closed scatterer** (`b3PadScatter`). With `A = farEmbed(omittedProj)`,
`Π = farEmbed(closingPairing)` (time-`s` data), `O = ΠᴴΠ` and the closing map `C_j(z)`,
`𝕊_pad = (1 - O)𝕊_jC_j(z)(1 - A) + ΠᴴA`. The first term is the closed scatterer from the retained
inputs to the retained outputs; the second pads the omitted channels by the decoupled reflection
`Πᴴ : ran A → ran O`. **`b3ChainXX`** is its Cayley inverse `z_∂ - 2iη(1 - 𝕊_pad)⁻¹`.

**`B3ClosedChainAt … j XX C`** (one step `j`, a two-port state `XX` of the closed past):
`XX` is measurable and a function of the past at `j` (`b3Ext W j`), and a.e. on the alive set
`A_j`:
* the state `XX` is Hermitian;
* `nearSchur z_∂ XX = b3ClosedX` (the closed one-port input `X_cl = z_∂ - R_cl⁻¹`);
* the closed frame is transported by the fresh layer of `XX`:
  `V_{j+1} = freshTransport(XX, F_j)ᴴ V_j`, `V = b3ClosedFrameAt`, `F_j = freshSample W j`;
* the frame carries the whole current: `currentOf XX = V 𝖣 Vᴴ`, `𝖣 = srcSignature`;
* `contrGram(XX, V) ≤ C · b3CovZ` (the contracting Gram sum is controlled by the closed
  contracting coordinates).

**The chain hypotheses.**
* `B3ClosedChainPin`: for every admissible frame and trace level there is `C ≥ 0` such that,
  eventually in `W`, at every no-birth step some state `XX` satisfies `B3ClosedChainAt`.
* `B3CayleyChain`: the same with the concrete state `b3ChainXX` and `C = 1`. It implies
  `B3ClosedChainPin` (`b3ClosedChainPin_of_cayley`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ContractingWords (currentOf)
open BlockBand.SourceProcess.ClosedSummedProof (contrGram)
open BlockBand.Transmission.Bridge

/-!
## The padded closed scatterer and its Cayley inverse
-/

/-- **The padded closed scatterer** `𝕊_pad = (1 - O)𝕊_jC_j(z)(1 - A) + ΠᴴA` at length `j`. -/
def b3PadScatter (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  let A := farEmbed (omittedProj b E h W (closeLen s W) ω)
  let Pi := farEmbed (closingPairing b E h W (closeLen s W) ω)
  (1 - Piᴴ * Pi) * scatteringMatrix b E W j ω * physClosingMapAt b E s h W j ω z * (1 - A) +
    Piᴴ * A

/-- **The padded closed two-port** `𝕏_pad = z_∂ - 2iη(1 - 𝕊_pad)⁻¹` (Cayley inverse) at length `j`
and phase `e^{iθ}`. -/
def b3ChainXX (b E s h : ℝ) {np : ℕ} (W j : ℕ) (y : ProbedPath W np × ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
    (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) • (1 - b3PadScatter b E s h W j y.1.1 (phase y.2))⁻¹

/-!
## The chain property and the chain hypotheses
-/

/-- **The closed path is a padded Hermitian two-port chain at step `j`**, with state `XX` and
constant `C`. -/
def B3ClosedChainAt (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (XX : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (C : ℝ) : Prop :=
  Measurable XX ∧ (∀ y, XX (b3Ext W j y) = XX y) ∧
    ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
      (XX y).IsHermitian ∧
      nearSchur (boundaryZ b E) (XX y) = b3ClosedX b E s h τ m W j y ∧
      b3ClosedFrameAt b E s h τ m W (j + 1) Vs y =
        (freshTransport b E (XX y) (freshSample W j y.1.1))ᴴ *
          b3ClosedFrameAt b E s h τ m W j Vs y ∧
      currentOf b E (XX y) = b3ClosedFrameAt b E s h τ m W j Vs y * srcSignature K (Fin np) *
        (b3ClosedFrameAt b E s h τ m W j Vs y)ᴴ ∧
      contrGram b E (XX y) (b3ClosedFrameAt b E s h τ m W j Vs y) ≤
        C * b3CovZ b E np τ m s h K W Vs j y

/-- **`B3ClosedChainPin`**: the closed path is, eventually in `W` and
at every no-birth step, a padded Hermitian two-port chain with a uniform constant. -/
def B3ClosedChainPin : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∃ XX : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        B3ClosedChainAt b E s h τ m R W j (Vs W) XX C

/-- **`B3CayleyChain`**: the concrete padded state `b3ChainXX` is a chain with `C = 1`. -/
def B3CayleyChain : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      B3ClosedChainAt b E s h τ m R W j (Vs W) (b3ChainXX b E s h W j) 1

theorem b3ClosedChainPin_of_cayley (h : B3CayleyChain) : B3ClosedChainPin := by
  intro b E np τ m T s h' K Vs hF R
  exact ⟨1, zero_le_one, (h b E np τ m T s h' K Vs hF R).mono fun W hW j hj =>
    ⟨_, hW j hj⟩⟩

end BlockBand.SourceProcess.PhysApprox.B3
