module

public import BlockBand.SourceProcess.ComplexConstruct.KExt
public import BlockBand.SourceProcess.ModelExist.Result

/-!
# (i) `ComplexModelExists` from the `𝒦`-extension hypothesis

`complexModelExists_of_kExtension (hK : BornKExtension) : ComplexModelExists`. The Gram part is
The construction of `ModelExist.modelExists_of_perpSelection` with **deterministic** births:
* data: the driver space over `S = ℕ → ℝ` with law `ρ` (the transmission sequence), filtration
  `driverAugmented ρ`;
* ambient frame: `Amb K R`, `R = 2K + n + 1` (`n = np`), initial frame `extFrame (tseq) h`, solved
  once from time `0` by `finiteSourceWellPosed_holds`; `𝒢 = gramPair P X`;
* births: probe `j` at the constant time `θ_j = (τ_j - s)⁺ > 0` with squared norm `d_* m_j`, its
  vector chosen by `perpSelectionHolds` (the sorted measurable selection);
* `G = bornG 𝒢 θ λ` is a born Gram solution (`isBornGramSolution_bornG`) with jump process
  `birthJump (τ - s) (d_* m)` and `G₀ = initialGram (tseq) h` (`bornG_zero`).
The `𝒦` process with births `kBirthJump E (τ - s) m` is supplied by `BornKExtension`; it vanishes
at time `0` because no birth time is `≤ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory ProbabilityTheory Filter Set Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.ModelExist BlockBand.SourceProcess.ComplexSourceLaw
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- No `𝒦` birth at time `0`. -/
theorem kBirthJump_zero {E s : ℝ} {np : ℕ} {τ m : Fin np → ℝ} (hsτ : ∀ j, s < τ j) :
    kBirthJump E (fun j => τ j - s) m ((0 : ℝ≥0) : ℝ) = 0 := by
  unfold kBirthJump
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj : ¬ (τ j - s ≤ ((0 : ℝ≥0) : ℝ)) := by
    simp only [NNReal.coe_zero, not_le, sub_pos]
    exact hsτ j
  simp only [hj, ite_false]

/-- **(i) `ComplexModelExists` from `BornKExtension`.** -/
theorem complexModelExists_of_kExtension (hK : BornKExtension) : ComplexModelExists := by
  intro b E np τ m T hD s hs hsτ ρ hρ hρseq h K hh
  obtain ⟨hb0, hb1, hE1, hE2, -, -, hm, -⟩ := hD
  classical
  set n := Fintype.card (Fin np)
  let eπ : Fin np ≃ Fin n := Fintype.equivFin _
  set R := 2 * K + n + 1
  let κ := SourceNoise (Amb K R)
  let tseq : DriverSample (ℕ → ℝ) κ → ℕ → ℝ := fun x => x.1
  have htseq0 : Measurable[driverAugmented (κ := κ) ρ 0] tseq := measurable_fst_driver ρ
  have hseq : ∀ᵐ x ∂driverLaw (κ := κ) ρ, IsTransmissionSequence (tseq x) :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [map_fst_driverLaw]; exact hρseq)
  have hD0 := transportD0_pos' hb0 hE1 hE2
  have hξm := stronglyMeasurable_extFrame (R := R) htseq0 h
  have hξc : ∀ᵐ x ∂driverLaw (κ := κ) ρ,
      TwoProjection (ambP K R) (extSig K R) (extFrame K R (tseq x) h) :=
    hseq.mono fun x hx => twoProjection_extFrame K R (fun k => hx.2.1 k) h
  obtain ⟨X, hX⟩ := (SourceSDE.finiteSourceWellPosed_holds ρ (transportD0 b E) (K + R)
    (ambP K R) (extSig K R) hD0 (isNearProjection_ambP K R) (isSignature_extSig K R) _ hξm
    hξc).1
  set 𝒢 := fun t x => gramPair (ambP K R) (X t x)
  have h𝒢 := GramUniqueness.ambient_isGramMartingaleSolution ρ hD0 (isNearProjection_ambP K R)
    (isSignature_extSig K R) hξm hξc hX
  have hp : IsStronglyProgressive (driverAugmented (κ := κ) ρ) 𝒢 := fun T =>
    (continuous_gramPair _).comp_stronglyMeasurable (hX.1.progressive T)
  have hrank := ae_rank_of_sol hD0 hξm hξc (fun x => principalMinorSum_extFrame_pos K R _ h) hX
  obtain ⟨sel, hselm, hsel⟩ := perpSelectionHolds (ExtCol K R) n (isCur K R)
  set v : Fin np → ℝ := fun j => dStar b * m j
  have hdS : 0 < dStar b := by unfold dStar; exact one_div_pos.2 (by linarith)
  have hv : ∀ j, 0 ≤ v j := fun j => mul_nonneg hdS.le (hm j)
  set σ : Fin np → DriverSample (ℕ → ℝ) κ → ℝ := fun j _ => τ j - s
  have hσ : ∀ j, Measurable[driverAugmented (κ := κ) ρ 0] (σ j) := fun j => measurable_const
  have hθ : ∀ y, Measurable[driverAugmented (κ := κ) ρ 0] (mθ K σ y) := by
    intro y
    rcases y with k | i
    · exact measurable_const
    · exact (hσ i).real_toNNReal
  have hθf : ∀ l, Measurable[driverAugmented (κ := κ) ρ 0] (mθf eπ σ l) := fun l =>
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
  have hspec : ∀ᵐ x ∂driverLaw (κ := κ) ρ, AllSpec K R eπ sel 𝒢 σ v x :=
    hrank.mono fun x hx => allSpec_of_rank hsel hv (by omega) hx
  have hj : ∀ f, 0 ≤ ((probeJump (K := K) v f).1.trace).re := fun f => by
    simp [probeJump, hv f]
  have hrep := hspec.mono fun x hx => bornRepresents_model hx (hherm x)
  have hsol := isBornGramSolution_bornG h𝒢 hp hθ hlam (bornL_sig K R eπ sel 𝒢 σ v) hj hσ hrep
  have h0 : ∀ x i, (σ i x).toNNReal = 0 → v i = 0 := fun x i hz => by
    have : τ i - s ≤ 0 := Real.toNNReal_eq_zero.1 hz
    linarith [hsτ i]
  obtain ⟨Kc, hKc, hK0⟩ := hK b E hb0 hb1 hE1 hE2 (ℕ → ℝ) ρ (Amb K R) (ExtCol K R) (K + R)
    (ambP K R) (extSig K R) (isNearProjection_ambP K R) (isSignature_extSig K R) _ hξm hξc X hX
    K (Fin np) (Fin np) (mθ K σ) (mlam K R eπ sel 𝒢 σ v) hθ hlam (bornL_sig K R eπ sel 𝒢 σ v)
    (probeJump (K := K) v) σ hσ hrep (fun t _ => kBirthJump E (fun j => τ j - s) m (t : ℝ))
    fun t => stronglyMeasurable_const
  refine ⟨DriverSample (ℕ → ℝ) κ, inferInstance, driverAugmented (κ := κ) ρ,
    driverLaw (κ := κ) ρ, tseq, bornG 𝒢 (mθ K σ) (mlam K R eπ sel 𝒢 σ v), Kc, ?_⟩
  exact
    { prob := inferInstance
      entrance_measurable := htseq0
      entrance_sequence := hseq
      entrance_law := by
        rw [show (fun ω => seqTraceMeasure (tseq ω)) =
            seqTraceMeasure ∘ (fun x : DriverSample (ℕ → ℝ) κ => x.1) from rfl,
          ← Measure.map_map measurable_seqTraceMeasure measurable_fst, map_fst_driverLaw]
      initial := by
        filter_upwards [hX.2, hspec] with x hx0 hsx
        refine ⟨bornG_zero ?_ hsx (hherm x) (h0 x), ?_⟩
        · simp only [𝒢]
          rw [hx0]
        · rw [hK0 x]
          exact kBirthJump_zero hsτ
      solution := hsol
      complex := hKc }

end BlockBand.SourceProcess.ComplexConstruct
