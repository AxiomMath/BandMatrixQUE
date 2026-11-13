module

public import BlockBand.Transmission.Dual.ExistsP1

/-!
# `exists_` at `p = 1`: the glued deletion process

* `good` is a measurable set of full measure (`measure_good_compl`) on which the family is
  consistent and `S → 0` at a finite `ζ` (`ae_tendsto`);
* `Z` is the glued flat path (`Yf n` on `[0, e_n]`, `Z_eq`);
* the realization: level `Nd = 1` before `ζ` and `0` from `ζ` on (and `1` off `good`);
  coordinates `Xd = Z₀`, `Yd = Z₁` (constant sequences) on `good`, the start `z` off `good`.
* `Nd`, `Xd`, `Yd` are `𝓖₁`-adapted at every `ω` (`measurable_Nd`, `measurable_Zd`);
* `Nd 0 = 1`, `Xd 0 = x`, `Yd 0 = y` at every `ω` (`Nd_zero`, `Zd_zero`);
* on `good` the path is a deletion path (`isDeletionPath_of_good`): the deletion clause at
  `τ = ζ` is the corner limit `S → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.NativeSDE
open scoped NNReal ENNReal

variable {D0 : ℝ} {z : Fin 2 → ℝ}

namespace SolFamily

variable (F : SolFamily D0 z)

/-- The good set: the family is consistent and `S → 0` at a finite `ζ`. -/
def good : Set Ω₁ := (toMeasurable P₁ {ω | ¬(F.IsCons ω ∧ F.IsConv ω)})ᶜ

theorem measurableSet_good : MeasurableSet F.good := (measurableSet_toMeasurable _ _).compl

theorem measure_good_compl (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) : P₁ F.goodᶜ = 0 := by
  rw [good, compl_compl, measure_toMeasurable]; exact ae_iff.1 (F.ae_tendsto hD0 hz)

theorem good_spec {ω : Ω₁} (hω : ω ∈ F.good) : F.IsCons ω ∧ F.IsConv ω := by
  by_contra h; exact hω (subset_toMeasurable _ _ h)

theorem measurableSet_good_aug (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) (t : ℝ≥0) :
    MeasurableSet[𝓖₁ t] F.good :=
  measurableSet_aug_of_full μ₁ F.measurableSet_good (F.measure_good_compl hD0 hz) t

open scoped Classical in
/-- The first index whose exit time is after `t` (`0` if none). -/
def idx (t : ℝ≥0) (ω : Ω₁) : ℕ :=
  if h : ∃ n, (t : WithTop ℝ≥0) < F.e n ω then Nat.find h else 0

/-- The glued flat path. -/
def Z (t : ℝ≥0) (ω : Ω₁) : Fin 2 → ℝ := F.Yf (F.idx t ω) t ω

theorem Z_mem (t : ℝ≥0) (ω : Ω₁) : F.Z t ω ∈ flatChamber 1 := F.Yf_mem _ t ω

theorem lt_zeta_of_le_e {ω : Ω₁} (hc : F.IsCons ω) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : (t : WithTop ℝ≥0) < F.zeta ω := by
  by_cases hζ : F.zeta ω < ⊤
  · exact ht.trans_lt (F.e_lt_zeta hc hζ n)
  · rw [not_lt_top_iff.1 hζ]; exact WithTop.coe_lt_top t

theorem Z_eq {ω : Ω₁} (hc : F.IsCons ω) {n : ℕ} {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) :
    F.Z t ω = F.Yf n t ω := by
  have hex : ∃ m, (t : WithTop ℝ≥0) < F.e m ω := lt_iSup_iff.1 (F.lt_zeta_of_le_e hc ht)
  have hspec := Nat.find_spec hex
  simp only [Z, idx, hex, dite_true]
  rcases le_total n (Nat.find hex) with h | h
  · exact (F.Yf_eq_of_cons hc h ht).symm
  · exact F.Yf_eq_of_cons hc h hspec.le

theorem Z_eq_zero {ω : Ω₁} {t : ℝ≥0} (h : ¬∃ n, (t : WithTop ℝ≥0) < F.e n ω) :
    F.Z t ω = F.Yf 0 t ω := by
  simp only [Z, idx, h, dite_false]

open scoped Classical in
/-- The level: `0` from `ζ` on (on `good`), `1` otherwise. -/
def Nd (t : ℝ≥0) (ω : Ω₁) : ℕ := if ω ∈ F.good ∧ F.zeta ω ≤ t then 0 else 1

open scoped Classical in
/-- The flat coordinates of the realization. -/
def Zd (t : ℝ≥0) (ω : Ω₁) : Fin 2 → ℝ := if ω ∈ F.good then F.Z t ω else z

/-- The `x`-sequence (constant, only index `0` matters). -/
def Xd (t : ℝ≥0) (ω : Ω₁) : ℕ → ℝ := fun _ => F.Zd t ω 0

/-- The `y`-sequence. -/
def Yd (t : ℝ≥0) (ω : Ω₁) : ℕ → ℝ := fun _ => F.Zd t ω 1

theorem Nd_le_one (t : ℝ≥0) (ω : Ω₁) : F.Nd t ω ≤ 1 := by unfold Nd; split_ifs <;> omega

theorem dualCoordOf_d (t : ℝ≥0) (ω : Ω₁) :
    dualCoordOf 1 (F.Xd t ω) (F.Yd t ω) = ofFlat 1 (F.Zd t ω) := by
  ext i
  · simp [dualCoordOf, Xd, Fin.fin_one_eq_zero i]; rfl
  · simp [dualCoordOf, Yd, Fin.fin_one_eq_zero i]; rfl

theorem Zd_mem (hz : z ∈ flatChamber 1) (t : ℝ≥0) (ω : Ω₁) : F.Zd t ω ∈ flatChamber 1 := by
  unfold Zd; split_ifs
  · exact F.Z_mem t ω
  · exact hz

theorem measurableSet_zeta_le (t : ℝ≥0) : MeasurableSet[𝓖₁ t] {ω | F.zeta ω ≤ t} := by
  have : {ω | F.zeta ω ≤ t} = ⋂ n, {ω | F.e n ω ≤ t} := by
    ext ω; rw [mem_iInter]; exact iSup_le_iff (f := fun n => F.e n ω)
  rw [this]
  exact MeasurableSet.iInter fun n => (F.isStoppingTime_e n).measurableSet_le t

theorem measurable_Nd (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) (t : ℝ≥0) :
    Measurable[𝓖₁ t] (F.Nd t) :=
  Measurable.ite ((F.measurableSet_good_aug hD0 hz t).inter (F.measurableSet_zeta_le t))
    measurable_const measurable_const

theorem measurable_Zd (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) (t : ℝ≥0) :
    Measurable[𝓖₁ t] (F.Zd t) := by
  classical
  set f : ℕ → Ω₁ → Fin 2 → ℝ := fun n ω => if ω ∈ F.good then
    (if (t : WithTop ℝ≥0) < F.e n ω then F.Yf n t ω else F.Yf 0 t ω) else z
  have hf : ∀ n, StronglyMeasurable[𝓖₁ t] (f n) := fun n => by
    have hs : MeasurableSet[𝓖₁ t] {ω | (t : WithTop ℝ≥0) < F.e n ω} := by
      rw [show {ω | (t : WithTop ℝ≥0) < F.e n ω} = {ω | F.e n ω ≤ t}ᶜ from by ext ω; exact lt_iff_not_ge (a := (t : WithTop ℝ≥0)) (b := F.e n ω)]
      exact ((F.isStoppingTime_e n).measurableSet_le t).compl
    exact (Measurable.ite (F.measurableSet_good_aug hD0 hz t)
      (Measurable.ite hs (F.measurable_Yf n t) (F.measurable_Yf 0 t))
      (measurable_const (a := z))).stronglyMeasurable
  refine (stronglyMeasurable_of_tendsto atTop hf (tendsto_pi_nhds.2 fun ω => ?_)).measurable
  by_cases hω : ω ∈ F.good
  · have hc := (F.good_spec hω).1
    by_cases hex : ∃ n, (t : WithTop ℝ≥0) < F.e n ω
    · obtain ⟨n₀, hn₀⟩ := hex
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n₀] with n hn
      have htn : (t : WithTop ℝ≥0) < F.e n ω := hn₀.trans_le (hc n₀ n hn).1
      simp only [f, Zd, hω, ite_true, htn, F.Z_eq hc htn.le]
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      have htn : ¬(t : WithTop ℝ≥0) < F.e n ω := fun h => hex ⟨n, h⟩
      simp only [f, Zd, hω, ite_true, htn, ite_false, F.Z_eq_zero hex]
  · simp only [f, Zd, hω, ite_false]; exact tendsto_const_nhds

theorem zeta_pos (ω : Ω₁) : (0 : WithTop ℝ≥0) < F.zeta ω := by
  obtain ⟨n, hn⟩ := exists_nat_gt ‖fromFlat z‖
  refine lt_of_lt_of_le ?_ (F.e_le_zeta n ω)
  refine lt_of_le_of_ne bot_le fun h => ?_
  have h' : exitTimeOf (F.X n) (n : ℝ) ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
    rw [WithTop.coe_zero]; exact h.symm
  have := le_norm_exitTimeOf (F.continuous_X n ω) h'
  rw [F.X_zero] at this
  linarith

theorem Nd_zero (ω : Ω₁) : F.Nd 0 ω = 1 := by
  have := F.zeta_pos ω
  simp only [Nd, WithTop.coe_zero, not_le.2 this, and_false, ite_false]

theorem Zd_zero (hz : z ∈ flatChamber 1) (ω : Ω₁) : F.Zd 0 ω = z := by
  unfold Zd; split_ifs with hω
  · have hc := (F.good_spec hω).1
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 (F.zeta_pos ω)
    rw [F.Z_eq hc (t := 0) (by rw [WithTop.coe_zero]; exact hn.le), F.Yf_zero hz]
  · rfl

/-- The level on `good`. -/
theorem Nd_of_good {ω : Ω₁} (hω : ω ∈ F.good) (t : ℝ≥0) :
    F.Nd t ω = if F.zeta ω ≤ t then 0 else 1 := by
  simp only [Nd, hω, true_and]

end SolFamily

end BlockBand.Transmission.Dual.Exists
