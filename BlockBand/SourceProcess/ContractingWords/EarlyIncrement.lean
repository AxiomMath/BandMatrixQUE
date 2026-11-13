module

public import BlockBand.SourceProcess.ContractingWords.EarlyPins
public import BlockBand.SourceProcess.ContractingWords.IncrementHolds

/-!
# The size of one ordinary-word increment, any tag births

`ordinaryIncrementAll_holds`: `OrdinaryIncrementAll`, from the one-step mean and fluctuation bounds
`stepMean_noBirth` and `stepFluct_noBirth` at an index `j` that is not a birth.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open scoped ENNReal

/-- **`OrdinaryIncrementAll`** from the input hypotheses (the birth hypothesis is not needed). -/
theorem ordinaryIncrementAll_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : OrdinaryIncrementAll := by
  intro b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  have hL := layerFreshBound_holds hGA hLp
  obtain ⟨C1, W1, h1⟩ :=
    stepMean_noBirth hMT hGA hLp hSR hL b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  obtain ⟨C2, W2, h2⟩ :=
    stepFluct_noBirth hMT hGA hLp hSR hL b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  refine ⟨max C1 0 + max C2 0, max (max W1 W2) 1, by positivity,
    fun W hW E hE k j hj hjk hjT w hw hlen => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW1'⟩ := hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  obtain ⟨s, hs⟩ := BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb hE1 hE2
  have hZ : IsAdmittedProduct [w] := fun v hv => by
    simp only [List.mem_singleton] at hv; rw [hv]; exact hw.1
  have hd : productDegree [w] ≤ d := by simpa [productDegree] using hlen
  have m1 := h1 W hW1 E hE s hs k [w] hZ hd j hj hjk hjT
  have m2 := h2 W hW2 E hE k [w] hZ hd j hj hjk hjT
  rw [meanFactor_ord b E s hw] at m1
  simp only [one_mul] at m1
  set A := alive b E k q K ε W j
  set μ := growthPathLaw W b
  set Z' : GrowthPath W → ℂ := fun ω => productValue b E k q W (j + 1) ω [w]
  have e : A.indicator (wordInc b E k q W j w) =
      (A.indicator fun ω => Z' ω - μ[Z' | growthSigma W j] ω) +
        A.indicator fun ω => μ[Z' | growthSigma W j] ω - productValue b E k q W j ω [w] := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [Pi.add_apply, Set.indicator_of_mem hω, wordInc, Z', productValue_single]; ring
    · simp [Set.indicator_of_notMem hω]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using hp
  rw [e]
  refine (eLpNorm_add_le hp1).trans ((add_le_add m2 m1).trans ?_)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hsq := Real.sqrt_pos.mpr hW0
  have hWs : 1 / (W : ℝ) ≤ 1 / Real.sqrt W := by
    have h1' : Real.sqrt W ≤ W := by
      rw [Real.sqrt_le_left hW0.le]; nlinarith [(by exact_mod_cast hW1' : (1 : ℝ) ≤ W)]
    exact one_div_le_one_div_of_le hsq h1'
  have hc1 : C1 / W ≤ max C1 0 * (1 / Real.sqrt W) := by
    rw [div_eq_mul_one_div]
    exact (mul_le_mul_of_nonneg_right (le_max_left C1 0) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hWs (le_max_right C1 0))
  have hc2 : C2 / Real.sqrt W ≤ max C2 0 * (1 / Real.sqrt W) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (le_max_left C2 0) (by positivity)
  calc ENNReal.ofReal (C2 / Real.sqrt W) + ENNReal.ofReal (C1 / W) ≤
      ENNReal.ofReal (max C2 0 * (1 / Real.sqrt W)) +
        ENNReal.ofReal (max C1 0 * (1 / Real.sqrt W)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hc2) (ENNReal.ofReal_le_ofReal hc1)
    _ = ENNReal.ofReal ((max C1 0 + max C2 0) / Real.sqrt W) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end BlockBand.SourceProcess.ContractingWords
