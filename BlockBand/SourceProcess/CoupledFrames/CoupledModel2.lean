module

public import BlockBand.SourceProcess.CoupledFrames.CoupledModel

/-!
# `frame_model`: each born frame is a finite source model

`frame_model`: the Gram process of a born frame built from an extended solution of the finite source
equation, on the driver space with independent birth times, is a finite source model.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Stochastic.GramUniqueness

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {b E s T : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ} {K M R n : ℕ}
  (eπ : (Fin p × Fin M) ≃ Fin n) {ρ : Measure (ℕ → ℝ)} [IsProbabilityMeasure ρ]
  [∀ i : Fin p × Fin M, IsProbabilityMeasure (birthTimeLaw s T (q i.1))]

/-- **Each born frame is a finite source model.** -/
theorem frame_model (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hq : ∀ i, IsSourceTest s T (q i))
    (hρseq : ∀ᵐ t ∂ρ, IsTransmissionSequence t) {h : ℝ}
    {Y : ℝ≥0 → DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) (SourceNoise (Amb K R)) →
      Matrix (Amb K R) (ExtCol K R) ℂ}
    (hY : IsSDESolution (ρ.prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1)))
      (sourceDrift (transportD0 b E) (K + R) (ambP K R))
      (sourceDiffusion (transportD0 b E) (ambP K R) (extSig K R))
      (fun x => extFrame K R x.1.1 h) Y)
    {pv : Fin p × Fin M → DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) (SourceNoise (Amb K R)) →
      ExtCol K R → ℂ}
    (hpv : ∀ i, StronglyMeasurable[(isStoppingTime_of_meas0
      (measurable_σs s (ρ.prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1)))
        i).real_toNNReal).measurableSpace] (pv i))
    {w : Fin n → DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) (SourceNoise (Amb K R)) →
      Amb K R → ℂ}
    (hw : ∀ k, StronglyMeasurable[(isStoppingTime_of_meas0
      (measurable_σs s (ρ.prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1)))
        (eπ.symm k)).real_toNNReal).measurableSpace] (w k))
    (hspec : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R))
      (ρ.prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1))),
      ProbeSpec (fun t x => gramPair (ambP K R) (Y t x)) (σs s)
        (fun i => dStar b * sourceMass s T (q i.1) / M) pv x)
    (hgood : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R))
      (ρ.prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1))),
      ∀ k, Y (bτ eπ (σs s) k x) x *ᵥ ba eπ pv k x = w k x) :
    IsFiniteSourceModel b E s T q h K M (ρ.map seqTraceMeasure)
      (driverAugmented (κ := SourceNoise (Amb K R))
        (ρ.prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1))))
      (driverLaw (κ := SourceNoise (Amb K R))
        (ρ.prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1))))
      (fun x => x.1.1) (fun x => x.1.2)
      (fun t x => gramPair (ambP K R) (bornFrame eπ Y (σs s) pv w t x)) := by
  set μ := ρ.prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1))
  set v : Fin p × Fin M → ℝ := fun i => dStar b * sourceMass s T (q i.1) / M
  have hD0 := transportD0_pos' hb0 hE1 hE2
  have htseq0 : Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0]
      (fun x : DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) (SourceNoise (Amb K R)) => x.1.1) :=
    measurable_fst.comp (measurable_fst_driver μ)
  have hτ0 : Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0]
      (fun x : DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) (SourceNoise (Amb K R)) => x.1.2) :=
    measurable_snd.comp (measurable_fst_driver μ)
  have hseq := ae_seq (κ := SourceNoise (Amb K R)) (ν := Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1))
    hρseq
  have hξm := stronglyMeasurable_extFrame (R := R) htseq0 h
  have hξc : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ,
      TwoProjection (ambP K R) (extSig K R) (extFrame K R x.1.1 h) :=
    hseq.mono fun x hx => twoProjection_extFrame K R (fun k => hx.2.1 k) h
  have h𝒢 := ambient_isGramMartingaleSolution μ hD0 (isNearProjection_ambP K R)
    (isSignature_extSig K R) hξm hξc hY
  have hp : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ)
      (fun t x => gramPair (ambP K R) (Y t x)) := fun T =>
    (continuous_gramPair _).comp_stronglyMeasurable (hY.1.progressive T)
  have hθ : ∀ y, Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (mθ K (σs (κ := SourceNoise (Amb K R)) s) y) := by
    intro y
    rcases y with k | i
    · exact measurable_const
    · exact (measurable_σs s μ i).real_toNNReal
  have hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace]
      (glam K R pv y) := by
    intro y
    rcases y with k | i
    · exact stronglyMeasurable_const
    · exact hpv i
  have hherm : ∀ x t, (gramPair (ambP K R) (Y t x)).1ᴴ = (gramPair (ambP K R) (Y t x)).1 ∧
      (gramPair (ambP K R) (Y t x)).2ᴴ = (gramPair (ambP K R) (Y t x)).2 := fun x t =>
    herm_gramPair (isNearProjection_ambP K R).1 (Y t x)
  have hj : ∀ f, 0 ≤ ((probeJump (K := K) v f).1.trace).re := fun f => by
    simp [probeJump, v, v_nonneg hb1 (hq f.1) M]
  have hrep : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ,
      BornRepresents (fun t x => gramPair (ambP K R) (Y t x)) (mθ K (σs s)) (glam K R pv)
        (probeJump (K := K) v) (σs s) x :=
    hspec.mono fun x hx => bornRepresents_probe hx (hherm x)
  have hsol := isBornGramSolution_bornG h𝒢 hp hθ hlam (fun t x => bornL_sig_probe t x) hj
    (measurable_σs s μ) hrep
  have hXp := isStronglyProgressive_bornFrame eπ hY (measurable_σs s μ) hpv hw
  have heq : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ t,
      gramPair (ambP K R) (bornFrame eπ Y (σs s) pv w t x) =
        bornG (fun t x => gramPair (ambP K R) (Y t x)) (mθ K (σs s)) (glam K R pv) t x :=
    hgood.mono fun x hx t => by rw [bornFrame_eq eπ Y _ pv w hx t, gramPair_mul]; rfl
  have h0 := ae_birth_zero (b := b) hq (κ := SourceNoise (Amb K R)) ρ (M := M)
  exact
    { prob := inferInstance
      entrance_measurable := htseq0
      entrance_sequence := hseq
      entrance_law := map_seqTrace
      births_measurable := hτ0
      births_law := map_τ
      independent := indep_tseq_τ
      initial := by
        filter_upwards [hY.2, hspec, h0, heq] with x hx0 hs hz he
        rw [he 0]
        exact bornG_zero_probe (by show gramPair _ (Y 0 x) = _; rw [hx0]) hs (hherm x) hz
      solution := isBornGramSolution_congr hsol (stronglyMeasurable_gram_of_prog hXp) heq }

end BlockBand.SourceProcess.CoupledFrames
