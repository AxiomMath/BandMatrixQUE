module

public import BlockBand.SourceProcess.LengthCont.MemLp
public import BlockBand.SourceProcess.LengthCont.Main

/-!
# Splitting `LayerIncrementBounds`: `RawTagMoments` plus the drift and fluctuation bounds

`LayerIncrementBounds` follows from the raw tag moments and the one-layer drift and fluctuation
bounds `LayerDriftBounds`; hence so do length continuity and the complex source limit sequence
statement.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont

open MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionSequences
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **One-layer drift and fluctuation bounds**: `LayerIncrementBounds` without the `L²` conjunct.
Window `δ > 0`,
constants `C, W₀`; for `W ≥ W₀` and `(T - δ)W ≤ n ≤ (T + δ)W`, every real coordinate of the
source data has predictable one-layer part of `L¹` norm `≤ C/W` and martingale difference of
second moment `≤ C/W`. -/
def LayerDriftBounds : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
    ∃ δ : ℝ, 0 < δ ∧ ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ n : ℕ,
      (T - δ) * W ≤ n → (n : ℝ) ≤ (T + δ) * W →
      ∀ (r : Fin 4) (i k : Fin np) (s : Bool),
        ∫ x, |(probedPathLaw W np b)[incr (sourceCoord b E W τ m r i k s) n |
            probedSigma W np n] x| ∂probedPathLaw W np b ≤ C / W ∧
        ∫ x, mart (probedPathLaw W np b) (probedSigma W np) (sourceCoord b E W τ m r i k s) n x ^ 2
            ∂probedPathLaw W np b ≤ C / W

/-- `RawTagMoments` and `LayerDriftBounds` give `LayerIncrementBounds`. -/
theorem layerIncrementBounds_of (hR : RawTagMoments) (hD : LayerDriftBounds) :
    LayerIncrementBounds := by
  intro b E np τ m T hdom
  obtain ⟨δ, hδ, C, W₀, hB⟩ := hD b E np τ m T hdom
  obtain ⟨W₁, hW₁⟩ := memLp_incr_of_rawTagMoments hR b E τ m T hdom (T + δ + 1)
  refine ⟨δ, hδ, C, max (max W₀ W₁) 1, fun W hW n h1 h2 r i k s => ?_⟩
  have hW0 : W₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWone : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hn : ((n + 1 : ℕ) : ℝ) ≤ (T + δ + 1) * W := by
    push_cast
    nlinarith
  exact ⟨hW₁ W hW1 n hn r i k s, hB W hW0 n h1 h2 r i k s⟩

/-- **Length continuity** from `RawTagMoments` and the drift and fluctuation bounds. -/
theorem lengthContinuity_of_drift (hR : RawTagMoments) (hD : LayerDriftBounds) :
    LengthContinuity :=
  lengthContinuity_of_layerIncrements (layerIncrementBounds_of hR hD)

/-- **The `ComplexSourceLimitSequenceContract`** from `RawTagMoments` and the
drift and fluctuation hypothesis `LayerDriftBounds`.
-/
theorem complexSourceLimitSequence_of_drift (hR : RawTagMoments) (hD : LayerDriftBounds) :
    ComplexSourceLimitSequenceContract :=
  complexSourceLimitSequence_holds (layerIncrementBounds_of hR hD)

end BlockBand.SourceProcess.LengthCont
