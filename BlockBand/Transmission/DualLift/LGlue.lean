module

public import BlockBand.Transmission.DualLift.LP1

/-!
# The glued realization of the lift

Boundary and random starts; `ζ = sup_n e_n`.
* `Z`: the glued flat path (`Yf n` on `[0, e_n]` on `good`, `Z_eq`);
* the realization: level `Nd = 1` before `ζ` and `0` from `ζ` on (and `1` off `good`); flat
  coordinates `Zd = Z` on `good`, the start `π(ξ)` off `good`; sequences `Xd`, `Yd` (constant
  in the index). Before `ζ`, `Zd` is the read-out `Z̄` used by the continuity lemmas.
* `Nd`, `Zd` are `L𝓖 μ`-adapted at every `ω` (`measurable_Nd`, `measurable_Zd`);
  `Nd 0 = 1` and `Zd 0 = π(ξ)` at every `ω` (`Nd_zero`, `Zd_zero`); `0 < ζ` everywhere.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
  BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ)

theorem Yf_eq_of_good {ω : LΩ S} (h : ω ∈ F.good) {n m : ℕ} (hnm : n ≤ m) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : F.Yf n t ω = F.Yf m t ω := by
  simp only [F.Yf_of_good h, Zp, ((F.good_spec h).2 n m hnm).2 t ht]

open scoped Classical in
/-- The first index whose exit time is after `t` (`0` if none). -/
def idx (t : ℝ≥0) (ω : LΩ S) : ℕ :=
  if h : ∃ n, (t : WithTop ℝ≥0) < F.e n ω then Nat.find h else 0

/-- The glued flat path. -/
def Z (t : ℝ≥0) (ω : LΩ S) : Fin 2 → ℝ := F.Yf (F.idx t ω) t ω

theorem lt_zeta_of_le_e {ω : LΩ S} (hc : ω ∈ F.good) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : (t : WithTop ℝ≥0) < F.zeta ω := by
  by_cases hζ : F.zeta ω < ⊤
  · exact ht.trans_lt (F.e_lt_zeta hc hζ n)
  · rw [not_lt_top_iff.1 hζ]; exact WithTop.coe_lt_top t

theorem Z_eq {ω : LΩ S} (hc : ω ∈ F.good) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : F.Z t ω = F.Yf n t ω := by
  have hex : ∃ m, (t : WithTop ℝ≥0) < F.e m ω := lt_iSup_iff.1 (F.lt_zeta_of_le_e hc ht)
  have hspec := Nat.find_spec hex
  simp only [Z, idx, hex, dite_true]
  rcases le_total n (Nat.find hex) with h | h
  · exact (F.Yf_eq_of_good hc h ht).symm
  · exact F.Yf_eq_of_good hc h hspec.le

theorem Z_eq_zero {ω : LΩ S} {t : ℝ≥0} (h : ¬∃ n, (t : WithTop ℝ≥0) < F.e n ω) :
    F.Z t ω = F.Yf 0 t ω := by
  simp only [Z, idx, h, dite_false]

open scoped Classical in
/-- The level: `0` from `ζ` on (on `good`), `1` otherwise. -/
def Nd (t : ℝ≥0) (ω : LΩ S) : ℕ := if ω ∈ F.good ∧ F.zeta ω ≤ t then 0 else 1

open scoped Classical in
/-- The flat coordinates of the realization (`Z̄` before `ζ`). -/
def Zd (t : ℝ≥0) (ω : LΩ S) : Fin 2 → ℝ := if ω ∈ F.good then F.Z t ω else liftProj (ξ ω)

/-- The `x`-sequence (constant, only index `0` matters). -/
def Xd (t : ℝ≥0) (ω : LΩ S) : ℕ → ℝ := fun _ => F.Zd t ω 0

/-- The `y`-sequence. -/
def Yd (t : ℝ≥0) (ω : LΩ S) : ℕ → ℝ := fun _ => F.Zd t ω 1

theorem Nd_le_one (t : ℝ≥0) (ω : LΩ S) : F.Nd t ω ≤ 1 := by unfold Nd; split_ifs <;> omega

theorem dualCoordOf_d (t : ℝ≥0) (ω : LΩ S) :
    dualCoordOf 1 (F.Xd t ω) (F.Yd t ω) = ofFlat 1 (F.Zd t ω) := by
  ext i
  · simp [dualCoordOf, Xd, Fin.fin_one_eq_zero i]; rfl
  · simp [dualCoordOf, Yd, Fin.fin_one_eq_zero i]; rfl

theorem measurableSet_zeta_le (t : ℝ≥0) : MeasurableSet[L𝓖 μ t] {ω | F.zeta ω ≤ t} := by
  have : {ω | F.zeta ω ≤ t} = ⋂ n, {ω | F.e n ω ≤ t} := by
    ext ω; rw [mem_iInter]; exact iSup_le_iff (f := fun n => F.e n ω)
  rw [this]
  exact MeasurableSet.iInter fun n => (F.isStoppingTime_e n).measurableSet_le t

theorem measurable_Nd (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (t : ℝ≥0) :
    Measurable[L𝓖 μ t] (F.Nd t) :=
  Measurable.ite ((F.measurableSet_good_aug hD0 hξ t).inter (F.measurableSet_zeta_le t))
    measurable_const measurable_const

theorem measurable_Zd (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (t : ℝ≥0) :
    Measurable[L𝓖 μ t] (F.Zd t) := by
  classical
  have h0 : Measurable[L𝓖 μ t] fun ω => liftProj (ξ ω) :=
    contDiff_liftProj.continuous.measurable.comp ((hξ.meas.mono ((L𝓖 μ).mono
      (zero_le : (0 : ℝ≥0) ≤ t))).measurable)
  set f : ℕ → LΩ S → Fin 2 → ℝ := fun n ω => if ω ∈ F.good then
    (if (t : WithTop ℝ≥0) < F.e n ω then F.Yf n t ω else F.Yf 0 t ω) else liftProj (ξ ω)
  have hf : ∀ n, StronglyMeasurable[L𝓖 μ t] (f n) := fun n => by
    have hs : MeasurableSet[L𝓖 μ t] {ω | (t : WithTop ℝ≥0) < F.e n ω} := by
      rw [show {ω | (t : WithTop ℝ≥0) < F.e n ω} = {ω | F.e n ω ≤ t}ᶜ from by
        ext ω; exact lt_iff_not_ge (a := (t : WithTop ℝ≥0)) (b := F.e n ω)]
      exact ((F.isStoppingTime_e n).measurableSet_le t).compl
    exact (Measurable.ite (F.measurableSet_good_aug hD0 hξ t)
      (Measurable.ite hs (F.measurable_Yf hD0 hξ n t) (F.measurable_Yf hD0 hξ 0 t))
      h0).stronglyMeasurable
  refine (stronglyMeasurable_of_tendsto atTop hf (tendsto_pi_nhds.2 fun ω => ?_)).measurable
  by_cases hω : ω ∈ F.good
  · by_cases hex : ∃ n, (t : WithTop ℝ≥0) < F.e n ω
    · obtain ⟨n₀, hn₀⟩ := hex
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n₀] with n hn
      have htn : (t : WithTop ℝ≥0) < F.e n ω :=
        hn₀.trans_le ((F.good_spec hω).2 n₀ n hn).1
      simp only [f, Zd, hω, ite_true, htn, F.Z_eq hω htn.le]
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      have htn : ¬(t : WithTop ℝ≥0) < F.e n ω := fun h => hex ⟨n, h⟩
      simp only [f, Zd, hω, ite_true, htn, ite_false, F.Z_eq_zero hex]
  · simp only [f, Zd, hω, ite_false]; exact tendsto_const_nhds

theorem zeta_pos (ω : LΩ S) : (0 : WithTop ℝ≥0) < F.zeta ω := by
  obtain ⟨n, hn⟩ := exists_nat_gt ‖ξ ω‖
  refine lt_of_lt_of_le ?_ (F.e_le_zeta n ω)
  refine lt_of_le_of_ne bot_le fun h => ?_
  have h' : exitTimeOf (F.X n) (n : ℝ) ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
    rw [WithTop.coe_zero]; exact h.symm
  have := le_norm_exitTimeOf (F.continuous_X n ω) h'
  rw [F.X_zero] at this
  linarith

theorem Nd_zero (ω : LΩ S) : F.Nd 0 ω = 1 := by
  have := F.zeta_pos ω
  simp only [Nd, WithTop.coe_zero, not_le.2 this, and_false, ite_false]

theorem Zd_zero (ω : LΩ S) : F.Zd 0 ω = liftProj (ξ ω) := by
  unfold Zd; split_ifs with hω
  · obtain ⟨n, hn⟩ := lt_iSup_iff.1 (F.zeta_pos ω)
    rw [F.Z_eq hω (t := 0) (by rw [WithTop.coe_zero]; exact hn.le), F.Yf_zero]
  · rfl

theorem Nd_of_good {ω : LΩ S} (hω : ω ∈ F.good) (t : ℝ≥0) :
    F.Nd t ω = if F.zeta ω ≤ t then 0 else 1 := by
  simp only [Nd, hω, true_and]

theorem Zd_mem_strip (hξ : IsLiftStart μ ξ) (t : ℝ≥0) (ω : LΩ S) : F.Zd t ω ∈ flatStrip := by
  unfold Zd Z; split_ifs
  · exact F.Yf_mem_strip hξ _ t ω
  · have hm := hξ.mem ω
    have hy := ly_mem_of_mem hm
    exact ⟨lx_nonneg _, hy.1, hy.2, lS_pos hm⟩

end LiftFamily

end BlockBand.Transmission.DualLift
