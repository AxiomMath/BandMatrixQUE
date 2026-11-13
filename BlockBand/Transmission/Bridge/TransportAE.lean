module

public import BlockBand.Transmission.Bridge.NewRow
public import BlockBand.Transmission.Bridge.NullDet

/-!
# Almost-sure transport along the near-end growth (no fresh-layer hypothesis)

Under `growthPathLaw W b` with `0 < b < 1`, `-2 < E < 2`, `W ≥ 1`, almost surely, for every
`j ≥ 1` at which the unabsorbed pencils `H_j - E`, `H_{j+1} - E` are invertible:
`ae_boundaryToInterior_succ`, `ae_pathCurrent_succ`, `ae_tagResponse_succ`,
`ae_tagResponse_succ_new`. The fresh-layer hypothesis `hG` is discharged by
`ae_isUnit_growth_bond` and `isUnit_freshLayer_path`; the Hermitian and height hypotheses by
`ae_passiveSample`. The pencil hypotheses remain here (with `κ ≡ 0`).
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

/-- Almost surely: Hermitian blocks, `Im z > 0`, and every fresh layer matrix invertible. -/
theorem ae_transport_hypotheses (hb : 0 < b) (hb1 : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, (∀ k, (ω.1 k).IsHermitian) ∧ 0 < (boundaryZ b E).im ∧
      ∀ j, IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
        (Matrix.of fun (u v : Fin 1 × Fin W) => pathX b E W j ω u.2 v.2) (freshSample W j ω)) := by
  filter_upwards [ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb1 hE1 hE2,
    ae_isUnit_growth_bond hb hW] with ω hP hB
  exact ⟨hP.herm, hP.height, fun j => isUnit_freshLayer_path hP j (hB (j + 1))⟩

/-- **Transport of the boundary-to-interior map, almost surely**. -/
theorem ae_boundaryToInterior_succ (hb : 0 < b) (hb1 : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1) →
      IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1) →
      (boundaryToInterior b E W (j + 1) ω).submatrix (headEquiv j W) id =
          Matrix.fromRows (nearSel W * boundaryResolvent b E W j ω * transportN b E W j ω)
            (boundaryToInterior b E W j ω * transportN b E W j ω) ∧
        boundaryResolvent b E W (j + 1) ω = (boundaryZ b E)⁻¹ • (1 -
          (ω.2 (j + 1) * nearSel W)ᴴ *
            (nearSel W * boundaryResolvent b E W j ω * transportN b E W j ω) -
          (farCoupling W j ω)ᴴ * (boundaryToInterior b E W j ω * transportN b E W j ω)) := by
  filter_upwards [ae_transport_hypotheses hb hb1 hE1 hE2 hW] with ω ⟨hA, hη, hG⟩ j hj hF hF'
  exact boundaryToInterior_succ b E hj ω hA hη hF hF' (hG j)

/-- **Current conservation, almost surely**. -/
theorem ae_pathCurrent_succ (hb : 0 < b) (hb1 : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1) →
      IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1) →
      pathCurrent b E W (j + 1) ω =
        (transportN b E W j ω)ᴴ * pathCurrent b E W j ω * transportN b E W j ω := by
  filter_upwards [ae_transport_hypotheses hb hb1 hE1 hE2 hW] with ω ⟨hA, hη, hG⟩ j hj hF hF'
  exact pathCurrent_succ b E hj ω hA hη hF hF' (hG j)

/-- **Old tags, almost surely**. -/
theorem ae_tagResponse_succ (hb : 0 < b) (hb1 : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1) →
      IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1) → ∀ k, k < j →
      tagResponse b E W (j + 1) k ω =
        (transportN b E W j ω)ᴴ * tagResponse b E W j k ω * transportN b E W j ω := by
  filter_upwards [ae_transport_hypotheses hb hb1 hE1 hE2 hW] with ω ⟨hA, hη, hG⟩ j hj hF hF' k hk
  exact tagResponse_succ b E hj ω hA hη hF hF' (hG j) hk

/-- **New-tag injection, almost surely** (`Y_{j+1;j} = D₊ᴴD₊`). -/
theorem ae_tagResponse_succ_new (hb : 0 < b) (hb1 : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1) →
      IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1) →
      tagResponse b E W (j + 1) j ω =
        (freshD b E (pathSchur E (pathAt W j ω)) (freshSample W j ω))ᴴ *
          freshD b E (pathSchur E (pathAt W j ω)) (freshSample W j ω) := by
  filter_upwards [ae_transport_hypotheses hb hb1 hE1 hE2 hW] with ω ⟨hA, hη, hG⟩ j hj hF hF'
  exact tagResponse_succ_new b E hj ω hA hη hF hF' (hG j)

end BlockBand.Transmission.Bridge
