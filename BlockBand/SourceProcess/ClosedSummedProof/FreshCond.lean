module

public import BlockBand.SourceProcess.ClosedSummedProof.LayerCovG
public import BlockBand.SourceProcess.ClosedSumProof.Main

/-!
# Conditioning on the closed past: integration over the fresh layer

On `lawW = sampledPathLaw ⊗ phaseLaw` with the
closed filtration `closedSigma W j = σ(pastCoords j, samples, phase)`, the fresh layer
`freshSample W j` (block `A_j`, near bond `B_{j+1}`) is independent of the closed past, with law
`freshLaw W b`.

* `cpast j y = (pastCoords j, samples, phase)`; `closedSigma W j p M = comap cpast`;
* **`lawW_map_closed_fresh`**: `(cpast, fresh)` has law `cpLaw ⊗ freshLaw`;
* in the sibling module `FreshCondE`, from this: `condExp_closed_fresh`,
  `E[Ψ(cpast, fresh) | closedSigma j] = ∫Ψ(cpast, y) dfresh(y)` a.s.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedSumProof
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.CoareaPalm

variable {W p M : ℕ}

/-- The sample coordinates (tag indices, Gaussians). -/
abbrev SampCoords (W p M : ℕ) := (Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ)

/-- The closed past coordinates at length `j`. -/
abbrev ClosedPast (W j p M : ℕ) := PastSample W j × SampCoords W p M × ℝ

/-- `cpast j y = (pastCoords j, samples, phase)`. -/
def cpast (j : ℕ) (y : SampledPath W p M × ℝ) : ClosedPast W j p M :=
  (pastCoords W j y.1.1, y.1.2, y.2)

theorem measurable_cpast (j : ℕ) : Measurable (cpast (W := W) (p := p) (M := M) j) :=
  ((measurable_pastCoords W j).comp (measurable_fst.comp measurable_fst)).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem closedSigma_eq_comap (j : ℕ) :
    closedSigma W j p M = MeasurableSpace.comap (cpast j) inferInstance := rfl

/-- The law of the samples. -/
def sampLaw (W n : ℕ) (q : Fin p → ℝ → ℝ) (M : ℕ) : Measure (SampCoords W p M) :=
  (Measure.pi fun i : Fin p × Fin M => tagSampleLaw W n (q i.1)).prod
    (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W))

/-- The law of the closed past. -/
def cpLaw (b : ℝ) (W j n : ℕ) (q : Fin p → ℝ → ℝ) (M : ℕ) : Measure (ClosedPast W j p M) :=
  (pastLaw W j b).prod ((sampLaw W n q M).prod phaseLaw)

theorem isProbabilityMeasure_sampLaw {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (n : ℕ) :
    IsProbabilityMeasure (sampLaw W n q M) := by
  have : ∀ x : Fin p × Fin M, IsProbabilityMeasure (tagSampleLaw W n (q x.1)) :=
    fun x => Sampling.isProbabilityMeasure_tagSampleLaw W _ (hq x.1)
  unfold sampLaw; infer_instance

/-- **The closed past and the fresh layer are independent.** -/
theorem lawW_map_closed_fresh (b T : ℝ) {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (j : ℕ) :
    (lawW b T q M W).map (fun y => (cpast j y, freshSample W j y.1.1)) =
      (cpLaw b W j ⌊(W : ℝ) * T⌋₊ q M).prod (freshLaw W b) := by
  have := isProbabilityMeasure_sampLaw (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  set P := pastLaw W j b
  set F := freshLaw W b
  set S := sampLaw W ⌊(W : ℝ) * T⌋₊ q M
  have hτ : MeasurePreserving (fun g => (pastCoords W j g, freshSample W j g))
      (growthPathLaw W b) (P.prod F) :=
    ⟨(measurable_pastCoords W j).prodMk (measurable_freshSample W j),
      growthPathLaw_map_past_fresh W j b⟩
  have h1 := (hτ.prod (MeasurePreserving.id S)).prod (MeasurePreserving.id phaseLaw)
  have h2 := measurePreserving_prodAssoc (P.prod F) S phaseLaw
  have h3 := measurePreserving_prodAssoc P F (S.prod phaseLaw)
  have h4 := (MeasurePreserving.id P).prod
    (Measure.measurePreserving_swap (μ := F) (ν := S.prod phaseLaw))
  have h5 := (measurePreserving_prodAssoc P (S.prod phaseLaw) F).symm
  have hall := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  exact hall.map_eq

theorem lawW_map_cpast (b T : ℝ) {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (j : ℕ) :
    (lawW b T q M W).map (cpast j) = cpLaw b W j ⌊(W : ℝ) * T⌋₊ q M := by
  have := isProbabilityMeasure_sampLaw (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  have h := congrArg (fun ν => ν.map Prod.fst) (lawW_map_closed_fresh b T hq j (M := M) (W := W))
  have hm : Measurable fun y : SampledPath W p M × ℝ => (cpast j y, freshSample W j y.1.1) :=
    (measurable_cpast j).prodMk ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  rw [Measure.map_map measurable_fst hm, Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

end BlockBand.SourceProcess.ClosedSummedProof
