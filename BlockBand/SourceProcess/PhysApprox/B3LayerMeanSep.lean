module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanChain
public import BlockBand.SourceProcess.PhysApprox.B3DecayDefs

/-!
# The separators of the padded closed two-port (statement)

`B3ClosedContrLayerForm` needs more than `B3ClosedChainPin`: the closed
contracting separators `b3ContrSep` must be the contracting separators of the padded state on the
closed frame, at `j` and at `j + 1`, and the padded state must grow by the fresh Schur step. With
these, `Q^σ_{kl}(j) = Tr(L Σ_σ)` and `Q^σ_{kl}(j+1) = Tr(NᴴLN Σ_σ(Φ_F 𝕏))` for the rank-one
letter `L = V_je_le_kᴴV_jᴴ = L₊ + iL₋` (polarization, `wt = (1, i)`, no injection).

**`B3CayleySep`**, stated as a hypothesis: eventually in `W`, at every no-birth step, a.e. on
`A_j`, with `V_i = b3ClosedFrameAt` and `𝕏_i = b3ChainXX`:
* `V_jᴴ b3ContrSep_σ(j) V_j = V_jᴴ sepOf(𝕏_j, contrSepOf σ) V_j` for the four `σ`;
* `𝕏_{j+1} = freshTwoPortSchur E 𝕏_j F_j`;
* the same separator identity at `j + 1`.

For `σ = 1, 2, 3` the identity follows from `σ = 0` by `P𝕊_pad = P𝕊C(1 - A)`, `(1 - A)V = V`.
`b3CayleySep_of_pad` derives `B3CayleySep` from `B3PadInvertible` and `B3PadGrowth`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.Transmission.Bridge

/-- The four contracting separators in `b3ContrSep` order (as in `contrSeps`). -/
def contrSepOf : Fin 4 → Separator := ![.projS, .sStarProj, .projSProj, .projSStarProj]

/-- The separator identity of the padded state on the closed frame at length `i`. -/
def B3SepAt (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (y : ProbedPath W np × ℝ) : Prop :=
  ∀ σ : Fin 4,
    (b3ClosedFrameAt b E s h τ m W i Vs y)ᴴ * b3ContrSep b E s h W i y.1.1 (phase y.2) σ *
        b3ClosedFrameAt b E s h τ m W i Vs y =
      (b3ClosedFrameAt b E s h τ m W i Vs y)ᴴ * sepOf b E XX (contrSepOf σ) *
        b3ClosedFrameAt b E s h τ m W i Vs y

/-- **`B3CayleySep`**: the separators and the growth of the padded closed state. -/
def B3CayleySep : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        B3SepAt b E s h τ m W j (Vs W) (b3ChainXX b E s h W j y) y ∧
        b3ChainXX b E s h W (j + 1) y =
          freshTwoPortSchur E (b3ChainXX b E s h W j y) (freshSample W j y.1.1) ∧
        B3SepAt b E s h τ m W (j + 1) (Vs W) (b3ChainXX b E s h W (j + 1) y) y

end BlockBand.SourceProcess.PhysApprox.B3
