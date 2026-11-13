module

public import BlockBand.Transmission.Dual.GB1RCorner

/-!
# The stage-1 realization from a random start

* `IsGood` (consistency and the random-start Theorem G at `ζ`), the measurable full-measure
  set `good` (`measure_good_compl` from `ae_tendsto_corner`), `measurableSet_good_aug`;
* `zeta_pos` (`ζ > 0` at every `ω`);
* the stage-1 realization: level `Ns = q + 1` before `ζ` and `0` from `ζ` on (on `good`;
  `q + 1` off `good`), flat state `Zs = Z` on `good` and `ξ ∘ fst` off `good`;
  `measurable_Ns`, `measurable_Zs` (`𝓖R`-adapted at every `ω`), `Ns_zero`, `Zs_zero`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {q : ℕ} {D0 : ℝ}
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

namespace B1R

theorem zeta_pos {ξ : S → Fin (q + q) → ℝ} (F : B1R D0 q μ ξ) (ω : ΩR S q) :
    (0 : WithTop ℝ≥0) < F.zeta ω := by
  obtain ⟨n, hn⟩ := exists_nat_gt ‖chartQInv q (ξ ω.1)‖
  refine lt_of_lt_of_le ?_ (F.e_le_zeta n ω)
  refine lt_of_le_of_ne bot_le fun h => ?_
  have h' : exitTimeOf (F.X n) (n : ℝ) ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
    rw [WithTop.coe_zero]; exact h.symm
  have := le_norm_exitTimeOf ((F.strong n).continuous ω) h'
  rw [(F.strong n).init ω] at this
  linarith

variable {ξ : S → Fin ((q + 1) + (q + 1)) → ℝ} (F : B1R D0 (q + 1) μ ξ)

/-- Consistency and the random-start Theorem G at `ζ`. -/
def IsGood (ω : ΩR S (q + 1)) : Prop :=
  F.IsConsAt ω ∧ ∀ ζ : ℝ≥0, F.zeta ω = ζ →
    ∃ c, IsCorner q c ∧ Tendsto (fun t => F.Z t ω) (𝓝[<] ζ) (𝓝 c)

/-- The good set. -/
def good : Set (ΩR S (q + 1)) := (toMeasurable (PR μ (q + 1)) {ω | ¬ F.IsGood ω})ᶜ

theorem measurableSet_good : MeasurableSet F.good := (measurableSet_toMeasurable _ _).compl

theorem measure_good_compl (hD0 : 0 < D0) (hξ : Measurable ξ)
    (hξc : ∀ s, ξ s ∈ flatChamber (q + 1)) : PR μ (q + 1) F.goodᶜ = 0 := by
  rw [good, compl_compl, measure_toMeasurable]
  exact ae_iff.1 (F.ae_tendsto_corner hD0 hξ hξc)

theorem good_spec {ω : ΩR S (q + 1)} (hω : ω ∈ F.good) : F.IsGood ω := by
  by_contra h; exact hω (subset_toMeasurable _ _ h)

theorem measurableSet_good_aug (hD0 : 0 < D0) (hξ : Measurable ξ)
    (hξc : ∀ s, ξ s ∈ flatChamber (q + 1)) (t : ℝ≥0) :
    MeasurableSet[𝓖R μ (q + 1) t] F.good :=
  measurableSet_aug_of_full μ F.measurableSet_good (F.measure_good_compl hD0 hξ hξc) t

open scoped Classical in
/-- The stage-1 level: `0` from `ζ` on (on `good`), `q + 1` otherwise. -/
def Ns (t : ℝ≥0) (ω : ΩR S (q + 1)) : ℕ :=
  if ω ∈ F.good ∧ F.zeta ω ≤ t then 0 else q + 1

open scoped Classical in
/-- The stage-1 flat state. -/
def Zs (t : ℝ≥0) (ω : ΩR S (q + 1)) : Fin ((q + 1) + (q + 1)) → ℝ :=
  if ω ∈ F.good then F.Z t ω else ξ ω.1

theorem Zs_mem (hξc : ∀ s, ξ s ∈ flatChamber (q + 1)) (t : ℝ≥0) (ω : ΩR S (q + 1)) :
    F.Zs t ω ∈ flatChamber (q + 1) := by
  unfold Zs; split_ifs
  · exact F.Z_mem t ω
  · exact hξc _

theorem measurable_Ns (hD0 : 0 < D0) (hξ : Measurable ξ)
    (hξc : ∀ s, ξ s ∈ flatChamber (q + 1)) (t : ℝ≥0) : Measurable[𝓖R μ (q + 1) t] (F.Ns t) :=
  Measurable.ite ((F.measurableSet_good_aug hD0 hξ hξc t).inter (F.measurableSet_zeta_le t))
    measurable_const measurable_const

theorem measurable_Yf_t (n : ℕ) (t : ℝ≥0) : Measurable[𝓖R μ (q + 1) t] (F.Yf n t) :=
  (F.stronglyMeasurable_Yf n t).measurable

theorem measurable_Zs (hD0 : 0 < D0) (hξ : Measurable ξ)
    (hξc : ∀ s, ξ s ∈ flatChamber (q + 1)) (t : ℝ≥0) : Measurable[𝓖R μ (q + 1) t] (F.Zs t) := by
  classical
  set f : ℕ → ΩR S (q + 1) → Fin ((q + 1) + (q + 1)) → ℝ := fun n ω => if ω ∈ F.good then
    (if (t : WithTop ℝ≥0) < F.e n ω then F.Yf n t ω else F.Yf 0 t ω) else ξ ω.1
  have hξ0 : Measurable[𝓖R μ (q + 1) t] fun ω : ΩR S (q + 1) => ξ ω.1 :=
    (measurable_fst_zero μ hξ).mono ((𝓖R μ (q + 1)).mono zero_le) le_rfl
  have hf : ∀ n, StronglyMeasurable[𝓖R μ (q + 1) t] (f n) := fun n => by
    have hs : MeasurableSet[𝓖R μ (q + 1) t] {ω | (t : WithTop ℝ≥0) < F.e n ω} := by
      rw [show {ω | (t : WithTop ℝ≥0) < F.e n ω} = {ω | F.e n ω ≤ t}ᶜ from by
        ext ω; exact lt_iff_not_ge (a := (t : WithTop ℝ≥0)) (b := F.e n ω)]
      exact ((F.isStoppingTime_e n).measurableSet_le t).compl
    exact (Measurable.ite (F.measurableSet_good_aug hD0 hξ hξc t)
      (Measurable.ite hs (F.measurable_Yf_t n t) (F.measurable_Yf_t 0 t)) hξ0).stronglyMeasurable
  refine (stronglyMeasurable_of_tendsto atTop hf (tendsto_pi_nhds.2 fun ω => ?_)).measurable
  by_cases hω : ω ∈ F.good
  · have hc := (F.good_spec hω).1
    by_cases hex : ∃ n, (t : WithTop ℝ≥0) < F.e n ω
    · obtain ⟨n₀, hn₀⟩ := hex
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n₀] with n hn
      have htn : (t : WithTop ℝ≥0) < F.e n ω := hn₀.trans_le (hc n₀ n hn).1
      simp only [f, Zs, hω, ↓reduceIte, htn, F.Z_eq hc htn.le]
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      have htn : ¬(t : WithTop ℝ≥0) < F.e n ω := fun h => hex ⟨n, h⟩
      simp only [f, Zs, hω, ↓reduceIte, htn, F.Z_eq_zero hex]
  · simp only [f, Zs, hω, ↓reduceIte]; exact tendsto_const_nhds

theorem Ns_zero (ω : ΩR S (q + 1)) : F.Ns 0 ω = q + 1 := by
  have := F.zeta_pos ω
  simp only [Ns, WithTop.coe_zero, not_le.2 this, and_false, ↓reduceIte]

theorem Zs_zero (hξc : ∀ s, ξ s ∈ flatChamber (q + 1)) (ω : ΩR S (q + 1)) :
    F.Zs 0 ω = ξ ω.1 := by
  unfold Zs; split_ifs with hω
  · have hc := (F.good_spec hω).1
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 (F.zeta_pos ω)
    rw [F.Z_eq hc (t := 0) (by rw [WithTop.coe_zero]; exact hn.le), F.Yf_zero hξc]
  · rfl

theorem Ns_of_good {ω : ΩR S (q + 1)} (hω : ω ∈ F.good) (t : ℝ≥0) :
    F.Ns t ω = if F.zeta ω ≤ t then 0 else q + 1 := by
  simp only [Ns, hω, true_and]

end B1R

end BlockBand.Transmission.Dual.G
