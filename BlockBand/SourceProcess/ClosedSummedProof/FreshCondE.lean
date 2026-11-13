module

public import BlockBand.SourceProcess.ClosedSummedProof.FreshCond

/-!
# The closed conditional expectation is the fresh-layer integral

**`condExp_closed_fresh`**: for jointly measurable `Ψ` with `Ψ(cpast j, fresh j)` integrable,
`lawW[Ψ(cpast j, fresh j) | closedSigma W j] =ᵐ ∫ Ψ(cpast j, y) dfreshLaw(y)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Bridge BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedSumProof
open BlockBand.SourceProcess.SourceProcessLaw

variable {W p M : ℕ}

/-- **Conditional expectation over one fresh layer, closed filtration.** -/
theorem condExp_closed_fresh (b T : ℝ) {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (j : ℕ)
    {Ψ : ClosedPast W j p M × LayerSample W .oneBlockOnePort → ℂ} (hΨ : Measurable Ψ)
    (hint : Integrable (fun y => Ψ (cpast j y, freshSample W j y.1.1)) (lawW b T q M W)) :
    (lawW b T q M W)[fun y => Ψ (cpast j y, freshSample W j y.1.1) | closedSigma W j p M] =ᵐ[
      lawW b T q M W] fun y => ∫ f, Ψ (cpast j y, f) ∂freshLaw W b := by
  have := isProbabilityMeasure_sampLaw (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  have := BlockBand.SourceProcess.ClosedIdent.isProbabilityMeasure_sampledPathLaw (b := b)
    (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  have : IsProbabilityMeasure (cpLaw b W j ⌊(W : ℝ) * T⌋₊ q M) := by unfold cpLaw; infer_instance
  set μ := lawW b T q M W
  set ρ := (cpLaw b W j ⌊(W : ℝ) * T⌋₊ q M).prod (freshLaw W b)
  have hT : Measurable fun y : SampledPath W p M × ℝ => (cpast j y, freshSample W j y.1.1) :=
    (measurable_cpast j).prodMk ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  have hmap : μ.map (fun y => (cpast j y, freshSample W j y.1.1)) = ρ := lawW_map_closed_fresh b T hq j
  have hΨi : Integrable Ψ ρ := by
    rw [← hmap]; exact (integrable_map_measure hΨ.aestronglyMeasurable hT.aemeasurable).mpr hint
  set G : ClosedPast W j p M → ℂ := fun x => ∫ f, Ψ (x, f) ∂freshLaw W b
  have hG : Measurable G :=
    (hΨ.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  have hGi : Integrable G (cpLaw b W j ⌊(W : ℝ) * T⌋₊ q M) := hΨi.integral_prod_left
  have hm : closedSigma W j p M ≤ (inferInstance : MeasurableSpace (SampledPath W p M × ℝ)) := by
    rw [closedSigma_eq_comap]; exact (measurable_cpast j).comap_le
  have hGμ : Integrable (fun y => G (cpast j y)) μ :=
    (integrable_map_measure hG.aestronglyMeasurable (measurable_cpast j).aemeasurable).mp
      (by rw [lawW_map_cpast b T hq j]; exact hGi)
  have hgm : Measurable[closedSigma W j p M] fun y => G (cpast j y) :=
    hG.comp (comap_measurable (cpast j))
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hint (fun s _ _ => hGμ.integrableOn)
    (fun s hs _ => ?_) hgm.aestronglyMeasurable).symm
  obtain ⟨B, hB, rfl⟩ := hs
  change ∫ y in cpast j ⁻¹' B, G (cpast j y) ∂μ =
    ∫ y in cpast j ⁻¹' B, Ψ (cpast j y, freshSample W j y.1.1) ∂μ
  have hind : ∀ f : SampledPath W p M × ℝ → ℂ, ∫ y in cpast j ⁻¹' B, f y ∂μ =
      ∫ y, (cpast j ⁻¹' B).indicator f y ∂μ := fun f =>
    (integral_indicator (measurable_cpast j hB)).symm
  rw [hind, hind]
  set Φ : ClosedPast W j p M × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => B.indicator (fun _ => (1 : ℂ)) z.1 * Ψ z
  have hΦ : Measurable Φ := ((measurable_const.indicator hB).comp measurable_fst).mul hΨ
  have hΦi : Integrable Φ ρ := by
    refine hΨi.norm.mono' hΦ.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    by_cases hz : z.1 ∈ B <;> simp [Φ, hz]
  have e1 : ∫ y, (cpast j ⁻¹' B).indicator
      (fun y => Ψ (cpast j y, freshSample W j y.1.1)) y ∂μ = ∫ z, Φ z ∂ρ := by
    rw [← hmap, integral_map hT.aemeasurable hΦ.aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : cpast j y ∈ B
    · simp [Φ, hy]
    · simp [Φ, hy]
  have e2 : ∫ y, (cpast j ⁻¹' B).indicator (fun y => G (cpast j y)) y ∂μ =
      ∫ x, B.indicator G x ∂cpLaw b W j ⌊(W : ℝ) * T⌋₊ q M := by
    rw [← lawW_map_cpast b T hq j, integral_map (measurable_cpast j).aemeasurable
      (hG.indicator hB).aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : cpast j y ∈ B
    · simp [hy]
    · simp [hy]
  rw [e1, e2, integral_prod Φ hΦi]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ B <;> simp [Φ, G, hx]

end BlockBand.SourceProcess.ClosedSummedProof
