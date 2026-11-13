module

public import BlockBand.Transmission.PassiveLayer.Statement
public import BlockBand.Transmission.Bridge.AlmostSure

/-!
# The passive bounds lemma at `w = z_∂` and the `oneStepFluctuation` field

At `w = z_∂` the fresh layer quantities are those of `TransmissionPath` (`lAt_boundaryZ`,
`uAt_boundaryZ`, `transportedFAt_boundaryZ`).

* `boundaryZ_mem_paramDisk`: `z_∂(E)` lies in the parameter disk for bulk `E`.
* `oneStepFluctuation_of_passiveBounds`: the `bilinear` clause at `w = z_∂` gives the
  `oneStepFluctuation` field of `PassiveSourceMixingContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem lAt_boundaryZ (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : lAt E (boundaryZ b E) X ω = freshL b E X ω := rfl

theorem uAt_boundaryZ (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    uAt E (boundaryZ b E) X = freshU b E X := rfl

theorem transportedFAt_boundaryZ (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    transportedFAt b E (boundaryZ b E) X = freshTransportedF b E X := rfl

theorem etaZ_nonneg {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) : 0 ≤ etaZ b E :=
  (Bridge.boundaryZ_im_pos hb hE1 hE2).le

theorem boundaryZ_mem_paramDisk {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    boundaryZ b E ∈ paramDisk b E :=
  Metric.mem_closedBall_self (by have := etaZ_nonneg hb hE1 hE2; linarith)

/-- Every energy lies in `bulkInterval (min (2+E) (2-E))` (with `κ > 0` in the bulk). -/
theorem mem_bulkInterval_min (E : ℝ) :
    E ∈ bulkInterval (min (2 + E) (2 - E)) := by
  constructor
  · have := min_le_left (2 + E) (2 - E); linarith
  · have := min_le_right (2 + E) (2 - E); linarith

/-- `PassiveBoundsStatement.bilinear` at `w = z_∂` is
`PassiveSourceMixingContract.oneStepFluctuation`.
-/
theorem oneStepFluctuation_of_passiveBounds (h : PassiveBoundsStatement) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (freshU b E X ω -
            matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) ∧
        eLpNorm (fun ω => bilinear u (freshTransportedF b E X ω -
            matrixExpect (freshLaw W b) (freshTransportedF b E X)) v) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) := by
  intro b hb0 hb E hE1 hE2 p hp
  obtain ⟨C, W₀, hC⟩ := h.bilinear b hb0 hb (min (2 + E) (2 - E))
    (lt_min (by linarith) (by linarith)) p hp
  refine ⟨C, W₀, fun W hW X hX u v => ?_⟩
  exact hC W hW E (mem_bulkInterval_min E) (boundaryZ b E)
    (boundaryZ_mem_paramDisk (by linarith) hE1 hE2) X hX u v

end BlockBand.Transmission.PassiveLayer
