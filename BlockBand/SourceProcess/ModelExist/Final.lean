module

public import BlockBand.SourceProcess.ModelExist.Holds

/-!
# `ModelExists` from `PerpSelectionHolds`

`modelExists_of_perpSelection`: if a measurable perpendicular selection exists for every finite
column type, then the positive finite source model exists (`ModelExists`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Set Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- **`ModelExists` from the perpendicular selection.** -/
theorem modelExists_of_perpSelection (hPS : PerpSelectionHolds) : ModelExists := by
  intro b hb0 hb1 E hE1 hE2 s T _ _ p q hq ρ hρ hρseq h K M _ _
  classical
  set n := Fintype.card (Fin p × Fin M)
  let eπ : (Fin p × Fin M) ≃ Fin n := Fintype.equivFin _
  set R := 2 * K + n + 1
  have : ∀ i : Fin p × Fin M, IsProbabilityMeasure (birthTimeLaw s T (q i.1)) :=
    fun i => isProbabilityMeasure_birthTimeLaw (hq i.1)
  set ν : Measure (Fin p × Fin M → ℝ) := Measure.pi fun i => birthTimeLaw s T (q i.1)
  set μ : Measure ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) := ρ.prod ν
  let κ := SourceNoise (Amb K R)
  let tseq : DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) κ → ℕ → ℝ := fun x => x.1.1
  let τ : DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) κ → Fin p × Fin M → ℝ := fun x => x.1.2
  have htseq0 : Measurable[driverAugmented (κ := κ) μ 0] tseq :=
    measurable_fst.comp (measurable_fst_driver μ)
  have hτ0 : Measurable[driverAugmented (κ := κ) μ 0] τ :=
    measurable_snd.comp (measurable_fst_driver μ)
  have hseq := ae_seq (κ := κ) (ν := ν) hρseq
  have hD0 := transportD0_pos' hb0 hE1 hE2
  have hξm := stronglyMeasurable_extFrame (R := R) htseq0 h
  have hξc : ∀ᵐ x ∂driverLaw (κ := κ) μ,
      TwoProjection (ambP K R) (extSig K R) (extFrame K R (tseq x) h) :=
    hseq.mono fun x hx => twoProjection_extFrame K R (fun k => hx.2.1 k) h
  obtain ⟨X, hX⟩ := (SourceSDE.finiteSourceWellPosed_holds μ (transportD0 b E) (K + R)
    (ambP K R) (extSig K R) hD0 (isNearProjection_ambP K R) (isSignature_extSig K R) _ hξm
    hξc).1
  set 𝒢 := fun t x => gramPair (ambP K R) (X t x)
  have h𝒢 := GramUniqueness.ambient_isGramMartingaleSolution μ hD0 (isNearProjection_ambP K R)
    (isSignature_extSig K R) hξm hξc hX
  have hp : IsStronglyProgressive (driverAugmented (κ := κ) μ) 𝒢 := fun T =>
    (continuous_gramPair _).comp_stronglyMeasurable (hX.1.progressive T)
  have hrank := ae_rank_of_sol hD0 hξm hξc (fun x => principalMinorSum_extFrame_pos K R _ h) hX
  obtain ⟨sel, hselm, hsel⟩ := hPS (ExtCol K R) n (isCur K R)
  set v : Fin p × Fin M → ℝ := fun i => dStar b * sourceMass s T (q i.1) / M
  have hv : ∀ i, 0 ≤ v i := fun i => v_nonneg hb1 (hq i.1) M
  set σ : Fin p × Fin M → DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) κ → ℝ :=
    fun i x => τ x i - s
  have hσ : ∀ i, Measurable[driverAugmented (κ := κ) μ 0] (σ i) := fun i =>
    ((measurable_pi_apply i).comp hτ0).sub_const s
  have hθ : ∀ y, Measurable[driverAugmented (κ := κ) μ 0] (mθ K σ y) := by
    intro y
    rcases y with k | i
    · exact measurable_const
    · exact (hσ i).real_toNNReal
  have hθf : ∀ m, Measurable[driverAugmented (κ := κ) μ 0] (mθf eπ σ m) := fun m =>
    (hσ _).real_toNNReal
  have hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace]
      (mlam K R eπ sel 𝒢 σ v y) := by
    intro y
    rcases y with k | i
    · exact stronglyMeasurable_const
    · have h1 := measurable_probeV sel 𝒢 (mvf eπ v) hθf hselm hp (eπ i)
      have e : mθf eπ σ (eπ i) = mθ K σ (Sum.inr i) := by
        funext x; simp [mθf, mθ]
      have e' : (fun x => ((mθf eπ σ (eπ i) x : ℝ≥0) : WithTop ℝ≥0)) =
          fun x => ((mθ K σ (Sum.inr i) x : ℝ≥0) : WithTop ℝ≥0) := by rw [e]
      rw [measurableSpace_congr e' _ (isStoppingTime_of_meas0 (hθ (Sum.inr i)))] at h1
      exact h1.stronglyMeasurable
  have hherm : ∀ x t, (𝒢 t x).1ᴴ = (𝒢 t x).1 ∧ (𝒢 t x).2ᴴ = (𝒢 t x).2 := fun x t =>
    herm_gramPair (isNearProjection_ambP K R).1 (X t x)
  have hspec : ∀ᵐ x ∂driverLaw (κ := κ) μ, AllSpec K R eπ sel 𝒢 σ v x :=
    hrank.mono fun x hx => allSpec_of_rank hsel hv (by omega) hx
  have hj : ∀ f, 0 ≤ ((probeJump (K := K) v f).1.trace).re := fun f => by
    simp [probeJump, hv f]
  have hsol := isBornGramSolution_bornG h𝒢 hp hθ hlam (bornL_sig K R eπ sel 𝒢 σ v) hj hσ
    (hspec.mono fun x hx => bornRepresents_model hx (hherm x))
  have h0 := ae_birth_zero (b := b) hq (κ := κ) ρ (M := M)
  refine ⟨DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) κ, inferInstance,
    driverAugmented (κ := κ) μ, driverLaw (κ := κ) μ, tseq, τ,
    bornG 𝒢 (mθ K σ) (mlam K R eπ sel 𝒢 σ v), ?_⟩
  exact
    { prob := inferInstance
      entrance_measurable := htseq0
      entrance_sequence := hseq
      entrance_law := map_seqTrace
      births_measurable := hτ0
      births_law := map_τ
      independent := indep_tseq_τ
      initial := by
        filter_upwards [hX.2, hspec, h0] with x hx0 hs hz
        refine bornG_zero ?_ hs (hherm x) hz
        simp only [𝒢]
        rw [hx0]
      solution := hsol }

end BlockBand.SourceProcess.ModelExist
