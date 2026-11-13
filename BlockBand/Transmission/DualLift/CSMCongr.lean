module

public import BlockBand.SourceProcess.Stochastic.Bridges.Structural

/-!
# Continuous semimartingales: modification on a null set of paths

`IsContinuousSemimartingale.congr_ae`: if `Y` is a continuous semimartingale with
characteristics `(β, α)`, and `(Y', β', α')` agree with `(Y, β, α)` for all times on almost
every path, with `Y'` adapted and `Y', β', α'` progressively measurable, then `Y'` is a
continuous semimartingale with characteristics `(β', α')`, with the same localizing sequence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {d : ℕ}

theorem _root_.BlockBand.Internal.Contracts.Transmission.IsContinuousSemimartingale.congr_ae
    {Y Y' β β' : ℝ≥0 → Ω → Fin d → ℝ} {α α' : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
    (H : IsContinuousSemimartingale Q 𝓖 Y β α) (hYa : ∀ t, StronglyMeasurable[𝓖 t] (Y' t))
    (hYp : IsStronglyProgressive 𝓖 Y') (hβ : IsStronglyProgressive 𝓖 β')
    (hα : IsStronglyProgressive 𝓖 α')
    (h : ∀ᵐ ω ∂Q, ∀ t, Y' t ω = Y t ω ∧ β' t ω = β t ω ∧ α' t ω = α t ω) :
    IsContinuousSemimartingale Q 𝓖 Y' β' α' := by
  obtain ⟨τ, hτ, hτlim, hmart⟩ := H.localizing
  have hY : ∀ᵐ ω ∂Q, ∀ t, Y' t ω = Y t ω := h.mono fun ω hω t => (hω t).1
  have hb : ∀ᵐ ω ∂Q, (fun t => β' t ω) = fun t => β t ω := h.mono fun ω hω => funext fun t => (hω t).2.1
  have ha : ∀ᵐ ω ∂Q, (fun t => α' t ω) = fun t => α t ω := h.mono fun ω hω => funext fun t => (hω t).2.2
  have hcomp : ∀ i, ∀ᵐ ω ∂Q, ∀ t, smCompensated Y β i t ω = smCompensated Y' β' i t ω := fun i => by
    filter_upwards [hY, hb] with ω h1 h2 t
    simp only [smCompensated, h1, congrFun h2]
  refine ⟨hYa, hYp, ?_, hβ, hα, ?_, ⟨τ, hτ, hτlim, fun n => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [H.continuous, hY] with ω h1 h2
    exact (funext h2) ▸ h1
  · filter_upwards [H.integrable, hb, ha] with ω h1 h2 h3 t
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · have := (h1 t).1 i; rwa [show (fun s : ℝ => β s.toNNReal ω i) =
        fun s : ℝ => β' s.toNNReal ω i from funext fun s => by rw [congrFun h2]] at this
    · have := (h1 t).2 i j; rwa [show (fun s : ℝ => α s.toNNReal ω i j) =
        fun s : ℝ => α' s.toNNReal ω i j from funext fun s => by rw [congrFun h3]] at this
  · exact hasMartingaleModification_stopped_congr ((hmart n).1 i) (hcomp i)
  · refine hasMartingaleModification_stopped_congr ((hmart n).2 i j) ?_
    filter_upwards [hcomp i, hcomp j, ha] with ω h1 h2 h3 t
    simp only [h1, h2, congrFun h3]

end BlockBand.Transmission.DualLift
