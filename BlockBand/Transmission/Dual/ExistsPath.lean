module

public import BlockBand.Transmission.Dual.ExistsGlue

/-!
# The glued level-one process is a deletion path (the `exists_` field at `p = 1`)

`isDeletionPath_of_good`: deterministically, on the good set of a `SolFamily D₀ z`
(`z ∈ 𝒞₁`), the glued level and coordinates satisfy the clauses of `IsDeletionPath`. The level
is `1` on `[0, ζ)` and `0` on `[ζ, ∞)`; the coordinates are continuous before `ζ`; at the single
jump `τ = ζ` both coordinates tend to `0` from the left (`IsConv`), and there are no survivors.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

variable {D0 : ℝ} {z : Fin 2 → ℝ}

namespace SolFamily

variable (F : SolFamily D0 z)

theorem Nd_of_le {ω : Ω₁} (hω : ω ∈ F.good) {t : ℝ≥0} (h : F.zeta ω ≤ t) : F.Nd t ω = 0 := by
  rw [F.Nd_of_good hω t]; exact ite_eq_left h

theorem Nd_of_lt {ω : Ω₁} (hω : ω ∈ F.good) {t : ℝ≥0} (h : (t : WithTop ℝ≥0) < F.zeta ω) :
    F.Nd t ω = 1 := by
  rw [F.Nd_of_good hω t]; exact ite_eq_right (not_le.2 h)

theorem lt_zeta_of_Nd {ω : Ω₁} (hω : ω ∈ F.good) {t : ℝ≥0} (h : F.Nd t ω = 1) :
    (t : WithTop ℝ≥0) < F.zeta ω := by
  by_contra hc; rw [F.Nd_of_le hω (not_lt.1 hc)] at h; exact absurd h (by norm_num)

theorem Zd_eq {ω : Ω₁} (hω : ω ∈ F.good) {n : ℕ} {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) :
    F.Zd t ω = F.Yf n t ω := by
  simp only [Zd, hω, ite_true]; exact F.Z_eq (F.good_spec hω).1 ht

theorem tendsto_Zd {ω : Ω₁} (hω : ω ∈ F.good) {τ : ℝ≥0} (hτ : F.zeta ω = τ) (i : Fin 2) :
    Tendsto (fun u => F.Zd u ω i) (𝓝[<] τ) (𝓝 0) := by
  have hv := (F.good_spec hω).2 (by rw [hτ]; exact WithTop.coe_lt_top τ)
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
  obtain ⟨p0, p1, -⟩ := mem_flatChamber_one (F.Yf_mem m u ω)
  simp only [Sp, tot] at h1
  rw [Real.dist_eq, sub_zero, abs_of_pos (by fin_cases i <;> assumption)]
  fin_cases i <;> simp <;> linarith

/-- **The glued process is a deletion path on `good`.** -/
theorem isDeletionPath_of_good (hz : z ∈ flatChamber 1) {ω : Ω₁} (hω : ω ∈ F.good) :
    IsDeletionPath (fun t => F.Nd t ω) (fun t => F.Xd t ω) (fun t => F.Yd t ω) where
  antitone := fun a b hab => by
    by_cases ha : F.zeta ω ≤ a
    · show F.Nd b ω ≤ F.Nd a ω
      rw [F.Nd_of_le hω ha, F.Nd_of_le hω (ha.trans (WithTop.coe_le_coe.2 hab))]
    · show F.Nd b ω ≤ F.Nd a ω
      rw [F.Nd_of_lt hω (not_le.1 ha)]; exact F.Nd_le_one b ω
  chamber := fun t => by
    by_cases h : F.zeta ω ≤ t
    · show dualCoordOf (F.Nd t ω) (F.Xd t ω) (F.Yd t ω) ∈ dualChamber (F.Nd t ω)
      rw [F.Nd_of_le hω h]
      exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    · show dualCoordOf (F.Nd t ω) (F.Xd t ω) (F.Yd t ω) ∈ dualChamber (F.Nd t ω)
      rw [F.Nd_of_lt hω (not_le.1 h), F.dualCoordOf_d]
      exact F.Zd_mem hz t ω
  rightCont := fun t => by
    by_cases h : F.zeta ω ≤ t
    · refine eventually_nhdsWithin_of_forall fun u hu => ?_
      show F.Nd u ω = F.Nd t ω
      rw [F.Nd_of_le hω h, F.Nd_of_le hω (h.trans (WithTop.coe_le_coe.2 (le_of_lt hu)))]
    · have hlt : (t : WithTop ℝ≥0) < F.zeta ω := not_le.1 h
      filter_upwards [nhdsWithin_le_nhds
        ((isOpen_lt WithTop.continuous_coe continuous_const).mem_nhds hlt)] with u hu
      show F.Nd u ω = F.Nd t ω
      rw [F.Nd_of_lt hω hu, F.Nd_of_lt hω hlt]
  cont := fun t₁ t₂ h12 heq i hi => by
    have h1 : F.Nd t₁ ω = 1 := le_antisymm (F.Nd_le_one t₁ ω) (by omega)
    have h2 : (t₂ : WithTop ℝ≥0) < F.zeta ω := F.lt_zeta_of_Nd hω (by omega)
    obtain ⟨m, hm⟩ := lt_iSup_iff.1 h2
    have hle : ∀ u ∈ Icc t₁ t₂, (u : WithTop ℝ≥0) ≤ F.e m ω := fun u hu =>
      (WithTop.coe_le_coe.2 hu.2).trans hm.le
    exact ⟨((continuous_apply 0).comp (F.continuous_Yf m ω)).continuousOn.congr fun u hu => by
        simp only [Xd, Function.comp, F.Zd_eq hω (hle u hu)],
      ((continuous_apply 1).comp (F.continuous_Yf m ω)).continuousOn.congr fun u hu => by
        simp only [Yd, Function.comp, F.Zd_eq hω (hle u hu)]⟩
  deletion := fun τ hτ q hev hne => by
    have hNB : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ⟩
    obtain ⟨u, hu⟩ := hev.exists
    have hq : q = 0 := by
      have := F.Nd_le_one u ω; omega
    subst hq
    have hζτ : F.zeta ω ≤ τ := by
      by_contra hc; exact hne (F.Nd_of_lt hω (not_le.1 hc))
    have hτζ : (τ : WithTop ℝ≥0) ≤ F.zeta ω := by
      by_contra hc
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt (not_le.1 hc))
      have hmτ : m < τ := by
        have h' : F.zeta ω < τ := not_le.1 hc
        rw [← hm] at h'; exact WithTop.coe_lt_coe.1 h'
      obtain ⟨v, hv1, hv2⟩ := (hev.and (Ioo_mem_nhdsLT hmτ)).exists
      have : F.Nd v ω = 0 := F.Nd_of_le hω (by rw [← hm]; exact WithTop.coe_le_coe.2 hv2.1.le)
      omega
    have hζ : F.zeta ω = τ := le_antisymm hζτ hτζ
    refine ⟨F.Nd_of_le hω hζτ, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · exact F.tendsto_Zd hω hζ 0
    · exact F.tendsto_Zd hω hζ 1

end SolFamily

end BlockBand.Transmission.Dual.Exists
