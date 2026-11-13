module

public import BlockBand.Transmission.Bridge.PencilAE

/-!
# Fully almost-sure bridges (i)–(iii) for the unabsorbed path (`0 < b < 1/2`)

For `0 < b < 1/2`, `-2 < E < 2`, `W ≥ 1`, `growthPathLaw W b`-almost surely, for every `j ≥ 1`
(no invertibility hypothesis left): the exact recursion `ae_pathX_succ`, the transport
`ae_boundaryToInterior_succ_full`, current conservation `ae_pathCurrent_succ_full`, old tags
`ae_tagResponse_succ_full` and the new-tag injection `ae_tagResponse_succ_new_full`. The pencil
hypotheses are discharged by `ae_isUnit_pathPencil_growth` (needs `b < 1/2`); the fresh-layer
hypothesis by `ae_isUnit_growth_bond` (needs `b > 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix

variable {W : ℕ} {b E : ℝ}

/-- **Bridge (i), unabsorbed, almost surely**: `X_{r+1} = freshSchur E X_r (freshSample W r ω)`
for every `r ≥ 1`. -/
theorem ae_pathX_succ (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ r, 1 ≤ r →
      pathX b E W (r + 1) ω = freshSchur E (pathX b E W r ω) (freshSample W r ω) := by
  filter_upwards [ae_isUnit_pathPencil_growth hb hW E,
    ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) (by linarith) hE1 hE2] with ω hF hP r hr
  have hz : boundaryZ b E ≠ 0 := fun h0 => by have := hP.height; rw [h0] at this; simp at this
  have hpen : ∀ n, pathPencil E (layerAbsorption W (fun _ => 0) n) (pathAt W n ω) =
      pathMatrix (pathAt W n ω) - (E : ℂ) • 1 := fun n => by
    rw [pathPencil, absorptionDiag_zero, add_zero]
  exact pathX_succ b E hr ω hz (by rw [hpen]; exact hF r) (isUnit_farPencil hP r)
    (by rw [hpen]; exact hF (r + 1)) (isUnit_farPencil hP (r + 1))

/-- **Bridge (ii), almost surely, no pencil hypothesis.** -/
theorem ae_boundaryToInterior_succ_full (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      (boundaryToInterior b E W (j + 1) ω).submatrix (headEquiv j W) id =
          Matrix.fromRows (nearSel W * boundaryResolvent b E W j ω * transportN b E W j ω)
            (boundaryToInterior b E W j ω * transportN b E W j ω) ∧
        boundaryResolvent b E W (j + 1) ω = (boundaryZ b E)⁻¹ • (1 -
          (ω.2 (j + 1) * nearSel W)ᴴ *
            (nearSel W * boundaryResolvent b E W j ω * transportN b E W j ω) -
          (farCoupling W j ω)ᴴ * (boundaryToInterior b E W j ω * transportN b E W j ω)) := by
  filter_upwards [ae_boundaryToInterior_succ hb (by linarith) hE1 hE2 hW,
    ae_isUnit_pathPencil_growth hb2 hW E] with ω h hF j hj
  exact h j hj (hF j) (hF (j + 1))

/-- **Current conservation, almost surely, no pencil hypothesis.** -/
theorem ae_pathCurrent_succ_full (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      pathCurrent b E W (j + 1) ω =
        (transportN b E W j ω)ᴴ * pathCurrent b E W j ω * transportN b E W j ω := by
  filter_upwards [ae_pathCurrent_succ hb (by linarith) hE1 hE2 hW,
    ae_isUnit_pathPencil_growth hb2 hW E] with ω h hF j hj
  exact h j hj (hF j) (hF (j + 1))

/-- **Old tags, almost surely, no pencil hypothesis.** -/
theorem ae_tagResponse_succ_full (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → ∀ k, k < j →
      tagResponse b E W (j + 1) k ω =
        (transportN b E W j ω)ᴴ * tagResponse b E W j k ω * transportN b E W j ω := by
  filter_upwards [ae_tagResponse_succ hb (by linarith) hE1 hE2 hW,
    ae_isUnit_pathPencil_growth hb2 hW E] with ω h hF j hj k hk
  exact h j hj (hF j) (hF (j + 1)) k hk

/-- **New-tag injection, almost surely, no pencil hypothesis** (`Y_{j+1;j} = D₊ᴴD₊`). -/
theorem ae_tagResponse_succ_new_full (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      tagResponse b E W (j + 1) j ω =
        (freshD b E (pathSchur E (pathAt W j ω)) (freshSample W j ω))ᴴ *
          freshD b E (pathSchur E (pathAt W j ω)) (freshSample W j ω) := by
  filter_upwards [ae_tagResponse_succ_new hb (by linarith) hE1 hE2 hW,
    ae_isUnit_pathPencil_growth hb2 hW E] with ω h hF j hj
  exact h j hj (hF j) (hF (j + 1))

end BlockBand.Transmission.Bridge
