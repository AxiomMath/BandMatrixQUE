module

public import BlockBand.SourceProcess.ClosedReduce.StartAE
public import BlockBand.SourceProcess.EigenSelConstruct.Main

/-!
# The edge birth at `n_s − 1` and the unconditional admissible frame

* `tagSampleLaw_lt_closeLen_le`: a tag of a source test is sampled before `n_s = ⌊Ws⌋` with
  probability at most `q(s)/(W·m_W)` (`m_W = gridMass`): only the index `n_s − 1` can carry mass,
  and only when `n_s = Ws`. With `m_W → m > 0` this is `O(1/W)`, so the samples violating
  `StartOK` can be discarded.
* `existsTimeSFrame_holds`: `ExistsTimeSFrame`, with the measurable eigen-selection
  `measurableEigenSelection_holds`.
* `ae_closedGramAt_start_sel`: the start value for the measurable `physSelFrame` built from
  that selection, with no hypothesis beyond the domain.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedReduce

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ClosedSum

theorem cast_div_le_of_le_closeLen {W k : ℕ} {s : ℝ} (hs : 0 ≤ s) (hW : 0 < W)
    (hk : k ≤ closeLen s W) : (k : ℝ) / W ≤ s := by
  have hW' : (0 : ℝ) < W := Nat.cast_pos.2 hW
  rw [div_le_iff₀ hW']
  calc (k : ℝ) ≤ (closeLen s W : ℝ) := Nat.cast_le.2 hk
    _ ≤ W * s := Nat.floor_le (mul_nonneg hW'.le hs)
    _ = s * W := mul_comm _ _

/-- **Edge birth bound.** -/
theorem tagSampleLaw_lt_closeLen_le {W n : ℕ} {q : ℝ → ℝ} {s T : ℝ} (hs : 0 ≤ s)
    (hq : IsSourceTest s T q) (hm : 0 < gridMass W n q) :
    tagSampleLaw W n q {k | k < closeLen s W} ≤
      ENNReal.ofReal (q s / (W * gridMass W n q)) := by
  set X := ENNReal.ofReal (q s / (W * gridMass W n q))
  simp only [tagSampleLaw, hm, ite_true]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
  have hterm : ∀ k ∈ Finset.range n,
      ENNReal.ofReal (q (((k + 1 : ℕ) : ℝ) / W) / (W * gridMass W n q)) *
        {k | k < closeLen s W}.indicator 1 k ≤ if k = closeLen s W - 1 then X else 0 := by
    intro k _
    by_cases hk : k < closeLen s W
    · have hW : 0 < W := by
        rcases Nat.eq_zero_or_pos W with h0 | h0
        · subst h0; simp [closeLen] at hk
        · exact h0
      rw [Set.indicator_of_mem (show k ∈ {k | k < closeLen s W} from hk), Pi.one_apply, mul_one]
      have hle := cast_div_le_of_le_closeLen hs hW (show k + 1 ≤ closeLen s W by omega)
      split_ifs with he
      · refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity))
        rcases hle.lt_or_eq with hlt | heq
        · rw [hq.2.1 _ fun hx => absurd hx.1 (not_le.2 hlt)]; exact hq.1 s
        · rw [heq]
      · have hlt : (((k + 1 : ℕ) : ℝ)) / W < s := by
          have h2 := cast_div_le_of_le_closeLen hs hW (show k + 2 ≤ closeLen s W by omega)
          have hW' : (0 : ℝ) < W := Nat.cast_pos.2 hW
          have : (((k + 1 : ℕ) : ℝ)) / W < ((k + 2 : ℕ) : ℝ) / W :=
            div_lt_div_of_pos_right (by push_cast; linarith) hW'
          linarith
        rw [hq.2.1 _ fun hx => absurd hx.1 (not_le.2 hlt), zero_div, ENNReal.ofReal_zero]
    · rw [Set.indicator_of_notMem (show k ∉ {k | k < closeLen s W} from hk), mul_zero]
      exact bot_le
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite_eq']
  split_ifs <;> simp

/-- `ExistsTimeSFrame`, with the measurable eigen-selection `measurableEigenSelection_holds`. -/
theorem existsTimeSFrame_holds : ExistsTimeSFrame :=
  existsTimeSFrame_of_eigenSel EigenSelConstruct.measurableEigenSelection_holds

/-- **The start value for an admissible frame that exists unconditionally**:
`physSelFrame` built from the measurable eigen-selection. -/
theorem ae_closedGramAt_start_sel {W p K M : ℕ} {b E s T : ℝ} (h : ℝ) (q : Fin p → ℝ → ℝ)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) :
    ∃ Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      IsTimeSFrame b E s h K W Vs ∧ ∀ᵐ ω ∂growthPathLaw W b,
        ∀ (km : (Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ)) (θ : ℝ),
          StartOK s T q W km.1 →
          closedGramAt b E s T h q W (closeLen s W) Vs ((ω, km), θ) =
            initialGram K (Fin p × Fin M) (physTseq b E s W ω) h := by
  obtain ⟨V, hVm, hV⟩ := EigenSelConstruct.measurableEigenSelection_holds (Fin W)
  have hVs := isTimeSFrame_physSelFrame (K := K) hV hVm (s := s) hb hE1 hE2 hW h
  exact ⟨_, hVs, ae_closedGramAt_start_adm q hb hE1 hE2 hW hVs⟩

end BlockBand.SourceProcess.ClosedReduce
