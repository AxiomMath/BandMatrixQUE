module

public import BlockBand.Transmission.DualLift.LGlue
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The glued realization is a boundary deletion path

On a path `ω ∈ good` where the corner limit holds (`IsConv`) and the entrance property holds
(`EntrGood`: the flat paths are in the open chamber at every `t ∈ (0, e_n]`), the glued
realization `(Nd, Xd, Yd)` satisfies `IsBoundaryDeletionPath` (`isBoundaryDeletionPath_of_good`):
`chamber` at `t > 0` is `EntrGood`, `cont` is the continuity of the lifted paths (including
`t = 0`), `deletion` at `τ = ζ` is the corner limit, `rightCont` holds since `Nd = 1{t < ζ}`. If
moreover the flat paths are in the chamber at `t = 0` (interior starts), the stronger
`IsDeletionPath` holds (`isDeletionPath_of_good`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ)

/-- The pathwise entrance property (the content of `LiftEntrance` at one `ω`). -/
def EntrGood (ω : LΩ S) : Prop := ∀ n : ℕ, ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) ≤ F.e n ω →
  F.Zp n t ω ∈ flatChamber 1

theorem Nd_of_le {ω : LΩ S} (hω : ω ∈ F.good) {t : ℝ≥0} (h : F.zeta ω ≤ t) : F.Nd t ω = 0 := by
  rw [F.Nd_of_good hω t]; exact ite_eq_left h

theorem Nd_of_lt {ω : LΩ S} (hω : ω ∈ F.good) {t : ℝ≥0} (h : (t : WithTop ℝ≥0) < F.zeta ω) :
    F.Nd t ω = 1 := by
  rw [F.Nd_of_good hω t]; exact ite_eq_right (not_le.2 h)

theorem lt_zeta_of_Nd {ω : LΩ S} (hω : ω ∈ F.good) {t : ℝ≥0} (h : F.Nd t ω = 1) :
    (t : WithTop ℝ≥0) < F.zeta ω := by
  by_contra hc; rw [F.Nd_of_le hω (not_lt.1 hc)] at h; exact absurd h (by norm_num)

theorem Zd_eq {ω : LΩ S} (hω : ω ∈ F.good) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : F.Zd t ω = F.Yf n t ω := by
  simp only [Zd, hω, ite_true]; exact F.Z_eq hω ht

theorem tendsto_Zd (hξ : IsLiftStart μ ξ) {ω : LΩ S} (hω : ω ∈ F.good) (hc : F.IsConv ω)
    {τ : ℝ≥0} (hτ : F.zeta ω = τ) (i : Fin 2) :
    Tendsto (fun u => F.Zd u ω i) (𝓝[<] τ) (𝓝 0) := by
  have hv := hc (by rw [hτ]; exact WithTop.coe_lt_top τ)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨s₀, hs₀, hS⟩ := hv k
  rw [hτ] at hs₀
  filter_upwards [Ioo_mem_nhdsLT (WithTop.coe_lt_coe.1 hs₀)] with u hu
  have hu' : (u : WithTop ℝ≥0) < F.zeta ω := by rw [hτ]; exact WithTop.coe_lt_coe.2 hu.2
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 hu'
  rw [F.Zd_eq hω hm.le]
  have h1 := hS m u hu.1.le hm.le
  obtain ⟨p0, p1, -⟩ := F.Yf_mem_strip hξ m u ω
  simp only [Sp, tot] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by fin_cases i <;> assumption)]
  fin_cases i <;> simp <;> linarith

theorem Zd_mem_of_pos {ω : LΩ S} (hω : ω ∈ F.good) (hE : F.EntrGood ω) {t : ℝ≥0}
    (ht : 0 < t) (hζ : (t : WithTop ℝ≥0) < F.zeta ω) : F.Zd t ω ∈ flatChamber 1 := by
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 hζ
  rw [F.Zd_eq hω hm.le, F.Yf_of_good hω]
  exact hE m t ht hm.le

theorem antitone_Nd {ω : LΩ S} (hω : ω ∈ F.good) : Antitone fun t => F.Nd t ω := fun a b hab => by
  by_cases ha : F.zeta ω ≤ a
  · show F.Nd b ω ≤ F.Nd a ω
    rw [F.Nd_of_le hω ha, F.Nd_of_le hω (ha.trans (WithTop.coe_le_coe.2 hab))]
  · show F.Nd b ω ≤ F.Nd a ω
    rw [F.Nd_of_lt hω (not_le.1 ha)]; exact F.Nd_le_one b ω

theorem rightCont_Nd {ω : LΩ S} (hω : ω ∈ F.good) (t : ℝ≥0) :
    ∀ᶠ u in 𝓝[>] t, F.Nd u ω = F.Nd t ω := by
  by_cases h : F.zeta ω ≤ t
  · refine eventually_nhdsWithin_of_forall fun u hu => ?_
    rw [F.Nd_of_le hω h, F.Nd_of_le hω (h.trans (WithTop.coe_le_coe.2 (le_of_lt hu)))]
  · have hlt : (t : WithTop ℝ≥0) < F.zeta ω := not_le.1 h
    filter_upwards [nhdsWithin_le_nhds
      ((isOpen_lt WithTop.continuous_coe continuous_const).mem_nhds hlt)] with u hu
    rw [F.Nd_of_lt hω hu, F.Nd_of_lt hω hlt]

theorem cont_d {ω : LΩ S} (hω : ω ∈ F.good) (t₁ t₂ : ℝ≥0) (heq : F.Nd t₂ ω = F.Nd t₁ ω)
    (i : ℕ) (hi : i < F.Nd t₁ ω) :
    ContinuousOn (fun u => F.Xd u ω i) (Icc t₁ t₂) ∧
      ContinuousOn (fun u => F.Yd u ω i) (Icc t₁ t₂) := by
  have h2 : (t₂ : WithTop ℝ≥0) < F.zeta ω := F.lt_zeta_of_Nd hω (by
    have := F.Nd_le_one t₁ ω; omega)
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 h2
  have hle : ∀ u ∈ Icc t₁ t₂, (u : WithTop ℝ≥0) ≤ F.e m ω := fun u hu =>
    (WithTop.coe_le_coe.2 hu.2).trans hm.le
  exact ⟨((continuous_apply 0).comp (F.continuous_Yf m ω)).continuousOn.congr fun u hu => by
      simp only [Xd, Function.comp, F.Zd_eq hω (hle u hu)],
    ((continuous_apply 1).comp (F.continuous_Yf m ω)).continuousOn.congr fun u hu => by
      simp only [Yd, Function.comp, F.Zd_eq hω (hle u hu)]⟩

theorem deletion_d (hξ : IsLiftStart μ ξ) {ω : LΩ S} (hω : ω ∈ F.good) (hc : F.IsConv ω)
    (τ : ℝ≥0) (hτ : 0 < τ) (q : ℕ) (hev : ∀ᶠ u in 𝓝[<] τ, F.Nd u ω = q + 1)
    (hne : F.Nd τ ω ≠ q + 1) :
    F.Nd τ ω = q ∧ Tendsto (fun u => F.Xd u ω 0) (𝓝[<] τ) (𝓝 0) ∧
      Tendsto (fun u => F.Yd u ω 0) (𝓝[<] τ) (𝓝 0) ∧
      ∀ i, i < q → Tendsto (fun u => F.Xd u ω (i + 1)) (𝓝[<] τ) (𝓝 (F.Xd τ ω i)) ∧
        Tendsto (fun u => F.Yd u ω (i + 1)) (𝓝[<] τ) (𝓝 (F.Yd τ ω i)) := by
  have hNB : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ⟩
  obtain ⟨u, hu⟩ := hev.exists
  have hq : q = 0 := by have := F.Nd_le_one u ω; omega
  subst hq
  have hζτ : F.zeta ω ≤ τ := by
    by_contra hc'; exact hne (F.Nd_of_lt hω (not_le.1 hc'))
  have hτζ : (τ : WithTop ℝ≥0) ≤ F.zeta ω := by
    by_contra hc'
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt (not_le.1 hc'))
    have hmτ : m < τ := by
      have h' : F.zeta ω < τ := not_le.1 hc'
      rw [← hm] at h'; exact WithTop.coe_lt_coe.1 h'
    obtain ⟨v, hv1, hv2⟩ := (hev.and (Ioo_mem_nhdsLT hmτ)).exists
    have : F.Nd v ω = 0 := F.Nd_of_le hω (by rw [← hm]; exact WithTop.coe_le_coe.2 hv2.1.le)
    omega
  have hζ : F.zeta ω = τ := le_antisymm hζτ hτζ
  exact ⟨F.Nd_of_le hω hζτ, F.tendsto_Zd hξ hω hc hζ 0, F.tendsto_Zd hξ hω hc hζ 1,
    fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- **The glued process is a boundary deletion path** on good paths. -/
theorem isBoundaryDeletionPath_of_good (hξ : IsLiftStart μ ξ) {ω : LΩ S} (hω : ω ∈ F.good)
    (hc : F.IsConv ω) (hE : F.EntrGood ω) :
    IsBoundaryDeletionPath (fun t => F.Nd t ω) (fun t => F.Xd t ω) (fun t => F.Yd t ω) where
  antitone := F.antitone_Nd hω
  chamber := fun t ht => by
    by_cases h : F.zeta ω ≤ t
    · show dualCoordOf (F.Nd t ω) (F.Xd t ω) (F.Yd t ω) ∈ dualChamber (F.Nd t ω)
      rw [F.Nd_of_le hω h]
      exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    · show dualCoordOf (F.Nd t ω) (F.Xd t ω) (F.Yd t ω) ∈ dualChamber (F.Nd t ω)
      rw [F.Nd_of_lt hω (not_le.1 h), F.dualCoordOf_d]
      exact F.Zd_mem_of_pos hω hE ht (not_le.1 h)
  rightCont := F.rightCont_Nd hω
  cont := fun t₁ t₂ _ heq i hi => F.cont_d hω t₁ t₂ heq i hi
  deletion := fun τ hτ q hev hne => F.deletion_d hξ hω hc τ hτ q hev hne

/-- **Interior starts: the glued process is a deletion path** (`IsDeletionPath`) on good paths. -/
theorem isDeletionPath_of_good (hξ : IsLiftStart μ ξ) {ω : LΩ S} (hω : ω ∈ F.good)
    (hc : F.IsConv ω) (hE : F.EntrGood ω) (h0 : liftProj (ξ ω) ∈ flatChamber 1) :
    IsDeletionPath (fun t => F.Nd t ω) (fun t => F.Xd t ω) (fun t => F.Yd t ω) where
  antitone := F.antitone_Nd hω
  chamber := fun t => by
    by_cases h : F.zeta ω ≤ t
    · show dualCoordOf (F.Nd t ω) (F.Xd t ω) (F.Yd t ω) ∈ dualChamber (F.Nd t ω)
      rw [F.Nd_of_le hω h]
      exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    · show dualCoordOf (F.Nd t ω) (F.Xd t ω) (F.Yd t ω) ∈ dualChamber (F.Nd t ω)
      rw [F.Nd_of_lt hω (not_le.1 h), F.dualCoordOf_d]
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
      · rw [← ht, F.Zd_zero]; exact h0
      · exact F.Zd_mem_of_pos hω hE ht (not_le.1 h)
  rightCont := F.rightCont_Nd hω
  cont := fun t₁ t₂ _ heq i hi => F.cont_d hω t₁ t₂ heq i hi
  deletion := fun τ hτ q hev hne => F.deletion_d hξ hω hc τ hτ q hev hne

end LiftFamily

end BlockBand.Transmission.DualLift
