module

public import BlockBand.SourceProcess.ComplexSourceLaw.Measurability
public import BlockBand.SourceProcess.ComplexSourceLaw.Slutsky

/-!
# `ComplexSourceLimitSequenceContract` from length continuity

`complexSourceLimitSequence_of : LengthContinuity → ComplexSourceLimitSequenceContract`: if the
source data at lengths `r_j ~ T W_j` and at `⌊W_j T⌋` are entrywise close in probability, the
sup-norm deviation is small in probability (union bound, `measure_norm_ge_le`), and Slutsky
transfers the complex source limit along the sequence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionSequences

section SupNorm

attribute [local instance] Matrix.normedAddCommGroup

/-- The Borel structure of the source data (product σ-algebra, product topology). -/
theorem sourceData_borelSpace (np : ℕ) : @BorelSpace (SourceData np)
    (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
      (@SeminormedAddCommGroup.toPseudoMetricSpace _
        (@NormedAddCommGroup.toSeminormedAddCommGroup _ inferInstance)))) _ :=
  inferInstanceAs (BorelSpace (Fin 4 → Fin np → Fin np → ℂ))

theorem sourceData_secondCountable (np : ℕ) : @SecondCountableTopology (SourceData np)
    (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
      (@SeminormedAddCommGroup.toPseudoMetricSpace _
        (@NormedAddCommGroup.toSeminormedAddCommGroup _ inferInstance)))) :=
  inferInstanceAs (SecondCountableTopology (Fin 4 → Fin np → Fin np → ℂ))

attribute [local instance] sourceData_borelSpace sourceData_secondCountable

/-- If every entry of `Z` is `< ε` then `‖Z‖ < ε` (sup norm). -/
theorem norm_lt_of_entries {np : ℕ} {ε : ℝ} (hε : 0 < ε) (Z : SourceData np)
    (h : ∀ r i k, ‖Z r i k‖ < ε) : ‖Z‖ < ε :=
  (pi_norm_lt_iff hε).2 fun r => (Matrix.norm_lt_iff hε).2 fun i k => h r i k

/-- The union bound: the sup-norm deviation is controlled by the entrywise deviations. -/
theorem measure_norm_ge_le {α : Type*} [MeasurableSpace α] (ρ : Measure α) {np : ℕ}
    (U V : α → SourceData np) {ε : ℝ} (hε : 0 < ε) :
    ρ {a | ε ≤ ‖U a - V a‖} ≤ ∑ r, ∑ i, ∑ k, ρ {a | ε ≤ ‖U a r i k - V a r i k‖} := by
  have hsub : {a | ε ≤ ‖U a - V a‖} ⊆
      ⋃ r, ⋃ i, ⋃ k, {a | ε ≤ ‖U a r i k - V a r i k‖} := by
    intro a ha
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hne
    exact absurd ha (not_le.2 (norm_lt_of_entries hε _ fun r i k => hne r i k))
  refine (measure_mono hsub).trans ?_
  refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact measure_iUnion_fintype_le _ _

/-- **The `ComplexSourceLimitSequenceContract`** from `LengthContinuity`. -/
theorem complexSourceLimitSequence_of (hLC : LengthContinuity) :
    ComplexSourceLimitSequenceContract := by
  refine ⟨fun b hb0 hb1 E hE0 hE1 np τ m hinj hτ hm T hT ν hν Wseq rseq hW hr => ?_⟩
  have hD : ComplexSourceLawDomain b E τ m T := ⟨hb0, hb1, hE0, hE1, hinj, hτ, hm, hT⟩
  have : IsProbabilityMeasure ν := hν.1
  have hclose : ∀ ε : ℝ, 0 < ε → Tendsto (fun j => probedPathLaw (Wseq j) np b
      {x | ε ≤ ‖complexSourceData b E (Wseq j) (rseq j) τ m x -
        complexSourceData b E (Wseq j) ⌊(Wseq j : ℝ) * T⌋₊ τ m x‖}) atTop (𝓝 0) := by
    intro ε hε
    have hsum : Tendsto (fun j => ∑ r, ∑ i, ∑ k, probedPathLaw (Wseq j) np b
        {x | ε ≤ ‖complexSourceData b E (Wseq j) (rseq j) τ m x r i k -
          complexSourceData b E (Wseq j) ⌊(Wseq j : ℝ) * T⌋₊ τ m x r i k‖}) atTop
        (𝓝 (∑ _r : Fin 4, ∑ _i : Fin np, ∑ _k : Fin np, (0 : ENNReal))) :=
      tendsto_finsetSum _ fun r _ => tendsto_finsetSum _ fun i _ =>
        tendsto_finsetSum _ fun k _ => hLC b E np τ m T hD Wseq rseq hW hr r i k ε hε
    simp only [Finset.sum_const_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) fun j => measure_norm_ge_le _ _ _ hε
  exact tendsto_integral_of_close (μ := fun j => probedPathLaw (Wseq j) np b)
    (X := fun j => complexSourceData b E (Wseq j) (rseq j) τ m)
    (Y := fun j => complexSourceData b E (Wseq j) ⌊(Wseq j : ℝ) * T⌋₊ τ m)
    (fun j => measurable_complexSourceData b E _ _ τ m)
    (fun j => measurable_complexSourceData b E _ _ τ m) ν
    (fun Φ => (hν.2 Φ).comp hW) hclose

end SupNorm

end BlockBand.SourceProcess.ComplexSourceLaw
