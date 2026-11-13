module

public import BlockBand.SourceProcess.FullSourceStops.CurrentNuclear
public import BlockBand.SourceProcess.FullSourceStops.Assembly

/-!
# The full-source stops lemma from the fractional transmission bound

The full-source stops statement follows from a bound on the fractional moment of the
transmission.

* `fullSourceStopsEnergyUniform_holds_of_fractional`, `fullSourceStops_holds_of_fractional`: the
  energy-uniform statement and its fixed-energy form, from `FractionalTransmissionUniform`;
* `fullSourceStops_holds_of_fractionalFixed`, `fullSourceStops_holds_of_law`: the fixed-energy
  statement from the fixed-energy fractional bound, and hence from `TransmissionLawContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform2 BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal

/-- **`FullSourceStopsEnergyUniformContract`** from input hypotheses and
`FractionalTransmissionUniform`.
-/
theorem fullSourceStopsEnergyUniform_holds_of_fractional (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hFr : FractionalTransmissionUniform) :
    FullSourceStopsEnergyUniformContract :=
  fullSourceStopsEnergyUniform_holds_of_current hMT hGA hLp hSR (currentNuclearTail_of hGA hLp hSR hFr)

/-- **The `FullSourceStopsContract`** from input hypotheses and
`FractionalTransmissionUniform`.
-/
theorem fullSourceStops_holds_of_fractional (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hFr : FractionalTransmissionUniform) :
    FullSourceStopsContract :=
  fullSourceStops_holds_of_current hMT hGA hLp hSR (currentNuclearTail_of hGA hLp hSR hFr)

/-- **The field `tail`** of `FullSourceStopsContract` from `TagSupBulk` and the fixed-`E`
current tail. -/
theorem tailFixed_of (hS : TagSupBulk) (hJ : CurrentNuclearTailFixed) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∃ C : ℝ, ∀ K : ℝ, 0 < K →
      limsup (fun W : ℕ => ⨆ k : Fin nT → ℕ, growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧
          (j : ℝ) ≤ T * W ∧ K < traceLoad b E k q W j ω}) atTop ≤ ENNReal.ofReal (C / K) := by
  intro b hb0 hb E h1 h2 nT nI q hq ε T hε hεT
  obtain ⟨hκ, hE⟩ := mem_bulk_self h1 h2
  obtain ⟨Cs, Ws, hCs⟩ := supMoments_of hS b hb0 hb _ hκ nT nI q hq ε T 1 hε hεT one_pos
  obtain ⟨CJ, hCJ⟩ := hJ b hb0 hb E h1 h2 ε T hε hεT
  set Cs' := max Cs 0
  set m : ℝ := (Fintype.card (Fin nT ⊕ Fin nI) : ℝ)
  refine ⟨2 * (m * Cs') + 2 * max CJ 0, fun K hK => ?_⟩
  have hK2 : 0 < K / 2 := by positivity
  set g : ℕ → ℝ≥0∞ := fun W => growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
      K / 2 < nuclearNorm (pathCurrent b E W j ω)}
  set a : ℝ≥0∞ := ENNReal.ofReal (m * Cs' / (K / 2))
  have hev : ∀ᶠ W : ℕ in atTop, (⨆ k : Fin nT → ℕ, growthPathLaw W b {ω | ∃ j : ℕ,
      ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧ K < traceLoad b E k q W j ω}) ≤ a + g W := by
    filter_upwards [eventually_ge_atTop Ws] with W hW
    refine iSup_le fun k => ?_
    set S : Fin nT ⊕ Fin nI → GrowthPath W → ℝ≥0∞ := fun a' ω =>
      ⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W), ‖sourceTrace b E k q W j ω a'‖ₑ
    have hSm : ∀ a', Measurable (S a') := fun a' => Measurable.iSup fun j =>
      Measurable.iSup_Prop _ (measurable_sourceTrace b E k q j a').enorm
    have hsub : {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧ K < traceLoad b E k q W j ω} ⊆
        {ω | ENNReal.ofReal (K / 2) ≤ ∑ a', S a' ω} ∪
          {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
            K / 2 < nuclearNorm (pathCurrent b E W j ω)} := by
      rintro ω ⟨j, hj1, hj2, hjK⟩
      by_cases hν : K / 2 < nuclearNorm (pathCurrent b E W j ω)
      · exact Or.inr ⟨j, hj1, hj2, hν⟩
      · left
        push Not at hν
        have hsum : K / 2 ≤ ∑ a', sourceTrace b E k q W j ω a' := by
          simp only [traceLoad] at hjK; linarith
        show ENNReal.ofReal (K / 2) ≤ ∑ a', S a' ω
        calc ENNReal.ofReal (K / 2) ≤ ENNReal.ofReal (∑ a', |sourceTrace b E k q W j ω a'|) :=
              ENNReal.ofReal_le_ofReal (hsum.trans (Finset.sum_le_sum fun _ _ => le_abs_self _))
          _ = ∑ a', ‖sourceTrace b E k q W j ω a'‖ₑ := by
              rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _]
              simp only [Real.enorm_eq_ofReal_abs]
          _ ≤ ∑ a', S a' ω := Finset.sum_le_sum fun a' _ =>
              le_iSup₂_of_le (f := fun (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W) =>
                ‖sourceTrace b E k q W j ω a'‖ₑ) j ⟨hj1, hj2⟩ le_rfl
    have hint : ∫⁻ ω, ∑ a', S a' ω ∂growthPathLaw W b ≤ ENNReal.ofReal (m * Cs') := by
      rw [lintegral_finsetSum _ fun a' _ => hSm a']
      calc ∑ a', ∫⁻ ω, S a' ω ∂growthPathLaw W b ≤ ∑ _a' : Fin nT ⊕ Fin nI, ENNReal.ofReal Cs' :=
            Finset.sum_le_sum fun a' _ => by
              have := hCs W hW E hE k a'
              simp only [ENNReal.rpow_one] at this
              exact this.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        _ = ENNReal.ofReal (m * Cs') := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hmk : growthPathLaw W b {ω | ENNReal.ofReal (K / 2) ≤ ∑ a', S a' ω} ≤ a := by
      refine (meas_ge_le_lintegral_div (Finset.measurable_sum _ fun a' _ => hSm a').aemeasurable
        (by simpa using hK2) ENNReal.ofReal_ne_top).trans ?_
      rw [show a = ENNReal.ofReal (m * Cs') / ENNReal.ofReal (K / 2) from
        ENNReal.ofReal_div_of_pos hK2]
      gcongr
    calc growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
          K < traceLoad b E k q W j ω}
        ≤ growthPathLaw W b {ω | ENNReal.ofReal (K / 2) ≤ ∑ a', S a' ω} + g W :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ a + g W := by gcongr
  calc limsup (fun W : ℕ => ⨆ k : Fin nT → ℕ, growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧
          (j : ℝ) ≤ T * W ∧ K < traceLoad b E k q W j ω}) atTop
      ≤ limsup (fun W => a + g W) atTop := limsup_le_limsup hev
    _ = a + limsup g atTop := limsup_const_add atTop g a (by isBoundedDefault) (by isBoundedDefault)
    _ ≤ a + ENNReal.ofReal (CJ / (K / 2)) := by gcongr; exact hCJ (K / 2) hK2
    _ ≤ ENNReal.ofReal ((2 * (m * Cs') + 2 * max CJ 0) / K) := by
        have hm : 0 ≤ m := Nat.cast_nonneg _
        have hCs0 : 0 ≤ Cs' := le_max_right _ _
        rw [show (2 * (m * Cs') + 2 * max CJ 0) / K = m * Cs' / (K / 2) + max CJ 0 / (K / 2) by
          field_simp, ENNReal.ofReal_add (by positivity) (by positivity)]
        gcongr
        exact le_max_left _ _

/-- **The `FullSourceStopsContract`** from input hypotheses and the fixed-`E`
`FractionalTransmissionFixed` only.
-/
theorem fullSourceStops_holds_of_fractionalFixed (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hFr : FractionalTransmissionFixed) :
    FullSourceStopsContract where
  tail := tailFixed_of (tagSupBulk_holds hGA hLp hSR) (currentNuclearTailFixed_of hGA hLp hSR hFr)
  supMoments := by
    intro b hb0 hb E h1 h2 nT nI q hq ε T p hε hεT hp
    obtain ⟨hκ, hE⟩ := mem_bulk_self h1 h2
    obtain ⟨C, W₀, hC⟩ := supMoments_of (tagSupBulk_holds hGA hLp hSR) b hb0 hb _ hκ nT nI q hq
      ε T p hε hεT hp
    exact ⟨C, W₀, fun W hW => hC W hW E hE⟩
  compensatorUI := by
    intro b hb0 hb E h1 h2 nT nI q hq Φ hΦ ε T η hε hεT hη
    obtain ⟨hκ, hE⟩ := mem_bulk_self h1 h2
    obtain ⟨M, W₀, hM⟩ := compensatorUI_of (compensatorCoefficientMoments_holds hMT hGA hLp hSR)
      b hb0 hb _ hκ nT nI q hq Φ hΦ ε T η hε hεT hη
    exact ⟨M, W₀, fun W hW => hM W hW E hE⟩

/-- **The `FullSourceStopsContract`** from input hypotheses and
`TransmissionLawContract` (only its field `fractional` is used).
-/
theorem fullSourceStops_holds_of_law (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hTL : TransmissionLawContract) : FullSourceStopsContract :=
  fullSourceStops_holds_of_fractionalFixed hMT hGA hLp hSR (fractionalTransmissionFixed_of_law hTL)

end BlockBand.SourceProcess.FullSourceStops
