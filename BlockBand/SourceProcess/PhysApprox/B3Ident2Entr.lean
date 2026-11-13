module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2Main

/-!
# `CapIdentEntrance` reduced to the finite-dimensional entrance laws

Measure: the candidate's `Q`, the conditioned entrance `ρ[|capSet K h]`, `ρ = entranceLaw P μ s`.

* **`CapIdentEntranceFdd`**: for every finite `J ⊆ ℕ`, the law of `(tseq_k)_{k ∈ J}` under
  `Q` is the law of `(t_k(ν))_{k ∈ J}` (`seqExtract`) under `ρ[|capSet K h]`. This is the core of
  the entrance identification (convergence of the conditioned laws of the finite-`W`
  eigenvalues `physTseq`).
* `map_cond`: `(P.map f)[|A] = (P[|f⁻¹' A]).map f`.
* `isTransmissionSequence_iff_mem`, `measurableSet_transSeq`: transmission sequences form a
  measurable set (summability of a nonnegative sequence as bounded partial sums).
* **`capIdentEntrance_of_fdd`**: `CapIdentEntranceFdd → CapIdentEntrance`. The two laws on
  `ℕ → ℝ` agree (Kolmogorov uniqueness `IsProjectiveLimit.unique`); `ρ`-a.s. the trace measure
  of `seqExtract ν` is `ν` and `seqExtract ν` is a transmission sequence
  (`entranceAtomic_of`, `seqExtract_seqTraceMeasure`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal ENNReal

/-- **`CapIdentEntranceFdd`**: the finite-dimensional laws of the
limit entrance coordinates are those of the transmission sequence of `μ(s)` conditioned on the
cap. -/
def CapIdentEntranceFdd : Prop :=
  TransmissionLawContract →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    ∀ J : Finset ℕ, Q.map (fun ω => J.restrict (tseq ω)) =
      ((entranceLaw P μ s)[|capSet K h]).map fun ν => J.restrict (seqExtract ν)

theorem map_cond {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (P : Measure α)
    {f : α → β} (hf : Measurable f) {A : Set β} (hA : MeasurableSet A) :
    (P.map f)[|A] = (P[|f ⁻¹' A]).map f := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul,
    Measure.restrict_map hf hA, Measure.map_apply hf hA]
  exact hf.aemeasurable

/-- Transmission sequences as a countable combination of measurable conditions. -/
theorem isTransmissionSequence_iff_mem (t : ℕ → ℝ) : IsTransmissionSequence t ↔
    (∀ i, t (i + 1) ≤ t i) ∧ (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
      ∃ C : ℕ, ∀ n, ∑ i ∈ Finset.range n, t i ≤ C := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => h1 (Nat.le_succ i), h2, ?_⟩
    obtain ⟨C, hC⟩ := exists_nat_ge (∑' i, t i)
    exact ⟨C, fun n => (h3.sum_le_tsum _ fun i _ => (h2 i).1).trans hC⟩
  · rintro ⟨h1, h2, C, hC⟩
    exact ⟨antitone_nat_of_succ_le h1, h2, summable_of_sum_range_le (fun i => (h2 i).1) hC⟩

theorem measurableSet_transSeq : MeasurableSet {t : ℕ → ℝ | IsTransmissionSequence t} := by
  have e : {t : ℕ → ℝ | IsTransmissionSequence t} =
      (⋂ i, {t : ℕ → ℝ | t (i + 1) ≤ t i}) ∩ ((⋂ i, {t : ℕ → ℝ | 0 ≤ t i ∧ t i ≤ 1}) ∩
        ⋃ C : ℕ, ⋂ n, {t : ℕ → ℝ | ∑ i ∈ Finset.range n, t i ≤ C}) := by
    ext t
    simp only [Set.mem_ofPred_eq, isTransmissionSequence_iff_mem, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_iUnion]
  rw [e]
  refine (MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply (i + 1))
    (measurable_pi_apply i)).inter ((MeasurableSet.iInter fun i =>
      (measurableSet_le measurable_const (measurable_pi_apply i)).inter
        (measurableSet_le (measurable_pi_apply i) measurable_const)).inter
      (MeasurableSet.iUnion fun C => MeasurableSet.iInter fun n => measurableSet_le
        (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const))

/-- **`CapIdentEntrance` from the finite-dimensional entrance laws.** -/
theorem capIdentEntrance_of_fdd (hF : CapIdentEntranceFdd) : CapIdentEntrance := by
  intro hTL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP
  have hJ := hF hTL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP
  obtain ⟨hD, hlim, -, hne, -, ⟨hQ, htm, -⟩, -⟩ := hP
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, hs, -⟩ := hD
  have := hlim.prob
  have := CapCond.isFiniteMeasure_entranceLaw P μ s
  set Mf : Ω → Measure unitInterval := fun ω => (μ s ω : Measure unitInterval)
  have hMf : Measurable Mf := measurable_subtype_coe.comp (hlim.measurable s hs)
  set A := capSet K h
  have hA : MeasurableSet A := measurableSet_capSet K h
  set P' := P[|Mf ⁻¹' A]
  have hρc : (entranceLaw P μ s)[|A] = P'.map Mf := map_cond P hMf hA
  have hne' : P (Mf ⁻¹' A) ≠ 0 := by rwa [← Measure.map_apply hMf hA]
  have hP' : IsProbabilityMeasure P' := cond_isProbabilityMeasure hne'
  -- `P`-a.s. the entrance is the trace measure of its transmission sequence
  have hat := SourcePins.entranceAtomic_of hTL b hb0 hb E hE1 hE2 Ω mΩ P μ hlim s hs
  have hat' : ∀ᵐ ω ∂P', IsTransmissionSequence (seqExtract (Mf ω)) ∧
      seqTraceMeasure (seqExtract (Mf ω)) = Mf ω := cond_absolutelyContinuous.ae_le
    (hat.mono fun ω ⟨t, ht, he⟩ => by
      have he' : Mf ω = seqTraceMeasure t := he
      rw [he', seqExtract_seqTraceMeasure ht]
      exact ⟨ht, rfl⟩)
  -- the two laws on `ℕ → ℝ`
  set g : Ω → ℕ → ℝ := fun ω => seqExtract (Mf ω)
  have hg : Measurable g := measurable_seqExtract.comp hMf
  have hlaw : Q.map tseq = P'.map g := by
    have h1 : IsProjectiveLimit (Q.map tseq) fun J : Finset ℕ => (P'.map g).map J.restrict := by
      intro J
      show _ = (P'.map g).map J.restrict
      rw [Measure.map_map (Finset.measurable_restrict J) htm,
        Measure.map_map (Finset.measurable_restrict J) hg]
      have := hJ J
      rw [hρc, Measure.map_map (show Measurable fun ν => J.restrict (seqExtract ν) from
        (Finset.measurable_restrict J).comp measurable_seqExtract) hMf] at this
      exact this
    have h2 : IsProjectiveLimit (P'.map g) fun J : Finset ℕ => (P'.map g).map J.restrict :=
      fun J => rfl
    exact h1.unique h2
  refine ⟨?_, ?_⟩
  · have h0 : (P'.map g) {t | IsTransmissionSequence t}ᶜ = 0 := by
      rw [Measure.map_apply hg measurableSet_transSeq.compl]
      exact measure_eq_zero_iff_ae_notMem.2 (hat'.mono fun ω hω h' => h' hω.1)
    rw [← hlaw, Measure.map_apply htm measurableSet_transSeq.compl] at h0
    exact measure_eq_zero_iff_ae_notMem.1 h0 |>.mono fun ω hω => by
      simpa using hω
  · have e1 : Q.map (fun ω => seqTraceMeasure (tseq ω)) = (Q.map tseq).map seqTraceMeasure :=
      (Measure.map_map measurable_seqTraceMeasure htm).symm
    rw [e1, hlaw, Measure.map_map measurable_seqTraceMeasure hg, hρc]
    exact Measure.map_congr (hat'.mono fun ω hω => hω.2)

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
