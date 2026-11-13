module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalMultiBlockCountConstruction
public import Mathlib.Probability.IdentDistribIndep

/-!
# Grouping independent physical upper coordinates

This module proves the reusable finite-family grouping step and reduces the remaining
physical product coupling to independence of the two concrete matrix reconstructions.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand
open MeasureTheory ProbabilityTheory Set
namespace GaussianRing

/-- Measurable reconstructions of two disjoint subfamilies of an independent family are
independent. -/
theorem iIndepFun.indepFun_disjoint_reconstructions
    {Ω ι E F G : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace G] {μ : Measure Ω}
    {X : ι → Ω → E} (hX : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    [DecidableEq ι] (S T : Finset ι) (hST : Disjoint S T)
    (Φ : (S → E) → F) (Ψ : (T → E) → G)
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    IndepFun (fun ω => Φ (fun i => X i ω))
      (fun ω => Ψ (fun i => X i ω)) μ := by
  have h := iIndepFun.indepFun_finset S T hST hX hXm
  exact h.comp hΦ hΨ

/-- The exact remaining deterministic grouping obligation.  Unlike the earlier product
coupling, this contains only independence of the two already-constructed matrix-valued
functions; their measurability and marginal laws are theorems. -/
structure PhysicalMultiBlockGroupedIndependence {p : Params} (M : Law p) : Prop where
  independent : IndepFun M.normalizedOffDiagonalBackground
    M.normalizedAllDiagonalBlocksHermitian M.P

/-- Independence of the two concrete groups gives the required product coupling. -/
theorem PhysicalMultiBlockGroupedIndependence.productCoupling
    {p : Params} {M : Law p} (h : PhysicalMultiBlockGroupedIndependence M) :
    PhysicalMultiBlockProductCoupling M := by
  let ν := M.normalizedOffDiagonalBackgroundLaw
  let D := M.normalizedAllDiagonalBlocksHermitian
  have hsource : M.P.map (fun ω =>
      (M.normalizedOffDiagonalBackground ω, D ω)) =
      ν.prod (M.P.map D) :=
    h.independent.map_prod_eq_prod_map_map
      M.measurable_normalizedOffDiagonalBackground.aemeasurable
      M.measurable_normalizedAllDiagonalBlocksHermitian.aemeasurable
  have hm₁ : AEMeasurable (fun ω =>
      (M.normalizedOffDiagonalBackground ω,
        M.normalizedAllDiagonalBlocksHermitian ω)) M.P :=
    (M.measurable_normalizedOffDiagonalBackground.prodMk
      M.measurable_normalizedAllDiagonalBlocksHermitian).aemeasurable
  have hm₂ : AEMeasurable (fun z :
      HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)) × M.Ω =>
      (z.1, M.normalizedAllDiagonalBlocksHermitian z.2))
      (ν.prod M.P) :=
    (measurable_fst.prodMk
      (M.measurable_normalizedAllDiagonalBlocksHermitian.comp measurable_snd)).aemeasurable
  refine ⟨?_⟩
  refine ⟨hm₁, hm₂, ?_⟩
  rw [hsource]
  calc
    ν.prod (M.P.map D) =
        (ν.map id).prod (M.P.map D) := by rw [Measure.map_id]
    _ = (ν.prod M.P).map (Prod.map id D) :=
      Measure.map_prod_map ν M.P measurable_id
        M.measurable_normalizedAllDiagonalBlocksHermitian
    _ = (ν.prod M.P).map (fun z =>
        (z.1, M.normalizedAllDiagonalBlocksHermitian z.2)) := by
      congr 1

/-- Consequently the paper-facing count transport follows from only the grouped
independence assertion. -/
theorem PhysicalMultiBlockGroupedIndependence.countTransport
    {p : Params} {M : Law p} (h : PhysicalMultiBlockGroupedIndependence M) :
    PhysicalMultiBlockCountTransport M.P M.normalizedOffDiagonalBackgroundLaw p
      M.normalizedAllDiagonalBlocksGUE (fun A => A)
      M.normalizedPhysicalIntervalCount :=
  M.physicalMultiBlockCountTransport h.productCoupling

end GaussianRing
end CoareaNative.BlockBand
