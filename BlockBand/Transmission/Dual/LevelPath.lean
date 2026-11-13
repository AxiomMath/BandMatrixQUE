module

public import BlockBand.Transmission.Dual.TestProc
public import BlockBand.Transmission.Dual.Exhaust

/-!
# Pathwise limits for the level step of `conservative`

* `entryTime_lt_pred`: `σ_q < σ_{q-1}` once `σ_q` is finite;
* `hit_le_entry_pred`: the localizing hitting time `θ` of `{P ≤ 1/2}` is `≤ σ_{q-1}`;
* `eventually_lt_hit`: for a smooth exhaustion `u_n` of `𝒞_q` and `σ_q ≤ t < σ_{q-1}`,
  eventually `t < θ_n` (the level-`q` path on `[σ_q, t]` is a compact subset of `𝒞_q`);
* `tendsto_level_gap`: the localized increments `R_{r_n} − R_{σ_q}` (`r_n = ρ ∧ θ_n`) converge
  to `R_{ρ∧σ_{q-1}} − R_{ρ∧σ_q}`;
* `total_le_of_le_hit`: `0 ≤ R ≤ K` up to the hitting time of `{R ≥ K}` when `R₀ < K`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable {q : ℕ} {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ}

theorem coe_untopA_of_ne_top {a : WithTop ℝ≥0} (h : a ≠ ⊤) : (a.untopA : WithTop ℝ≥0) = a := by
  obtain ⟨b, rfl⟩ := WithTop.ne_top_iff_exists.1 h
  rfl

theorem dualTotal_nonneg (hP : IsDeletionPath n x y) (t : ℝ≥0) :
    0 ≤ dualTotal (n t) (x t) (y t) := by
  have hz := hP.chamber t
  refine Finset.sum_nonneg fun i hi => ?_
  have hi' : i < n t := Finset.mem_range.1 hi
  exact (add_pos (hz.2.2.1 ⟨i, hi'⟩) (hz.2.2.2 ⟨i, hi'⟩).1).le

/-- The level at the entrance time `σ_q` (`q ≤ n₀`) is `q`. -/
theorem level_at_entry (hP : IsDeletionPath n x y) (hq0 : q ≤ n 0) {s : ℝ≥0}
    (hs : entryTime n q = s) : n s = q := by
  rcases lt_or_eq_of_le hq0 with hlt | heq
  · exact level_entryTime hP hlt hs
  · have h0 : entryTime n q ≤ (0 : ℝ≥0) := (entryTime_le_iff hP q 0).2 heq.ge
    rw [hs] at h0
    have : s = 0 := le_antisymm (WithTop.coe_le_coe.1 h0) zero_le
    rw [this]; exact heq.symm

theorem entryTime_lt_pred (hP : IsDeletionPath n x y) (hq : 1 ≤ q) (hq0 : q ≤ n 0) {s : ℝ≥0}
    (hs : entryTime n q = s) : (s : WithTop ℝ≥0) < entryTime n (q - 1) := by
  have hns := level_at_entry hP hq0 hs
  by_contra hc
  have := (entryTime_le_iff hP (q - 1) s).1 (not_lt.1 hc)
  omega

theorem hit_le_entry_pred (hP : IsDeletionPath n x y) {h : DualCoord q → ℝ} (hq : 1 ≤ q)
    {e : ℝ≥0} (he : entryTime n (q - 1) = e) :
    (⨅ (t : ℝ≥0) (_ : testVal q h (n t) (x t) (y t) ≤ 1 / 2), (t : WithTop ℝ≥0)) ≤ e := by
  have hle : n e ≤ q - 1 := (entryTime_le_iff hP (q - 1) e).1 he.le
  have h1 : n e ≠ q := by omega
  have h2 : ¬ q < n e := by omega
  refine iInf₂_le e ?_
  simp [testVal, dualLift, h1, h2]

/-- For `σ_q ≤ t < σ_{q-1}`, eventually `t < θ_n`. -/
theorem eventually_lt_hit (hP : IsDeletionPath n x y) {u : ℕ → DualCoord q → ℝ}
    (hcu : ∀ k, Continuous (u k))
    (hex : ∀ L : Set (DualCoord q), IsCompact L → L ⊆ dualChamber q →
      ∃ n₀, ∀ k, n₀ ≤ k → ∀ z ∈ L, u k z = 1)
    {t : ℝ≥0} (ht1 : entryTime n q ≤ t) (ht2 : (t : WithTop ℝ≥0) < entryTime n (q - 1)) :
    ∀ᶠ k in atTop, (t : WithTop ℝ≥0) <
      ⨅ (v : ℝ≥0) (_ : testVal q (u k) (n v) (x v) (y v) ≤ 1 / 2), (v : WithTop ℝ≥0) := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top ht1)
  have hs' : entryTime n q = s := hs.symm
  have hst : s ≤ t := WithTop.coe_le_coe.1 (hs' ▸ ht1)
  have hlev : ∀ v, s ≤ v → v ≤ t → n v = q := fun v hsv hvt => by
    have h1 : n v ≤ q := (entryTime_le_iff hP q v).1 (hs' ▸ WithTop.coe_le_coe.2 hsv)
    have h2 : q - 1 < n v := lt_level_of_lt_entryTime hP
      (lt_of_le_of_lt (WithTop.coe_le_coe.2 hvt) ht2)
    omega
  have hcont : ContinuousOn (fun v => dualCoordOf q (x v) (y v)) (Icc s t) := by
    have hc := hP.cont s t hst ((hlev t hst le_rfl).trans (hlev s le_rfl hst).symm)
    refine ContinuousOn.prodMk (continuousOn_pi.2 fun i => ?_) (continuousOn_pi.2 fun i => ?_)
    · exact (hc i (by rw [hlev s le_rfl hst]; exact i.2)).1
    · exact (hc i (by rw [hlev s le_rfl hst]; exact i.2)).2
  have hL : (fun v => dualCoordOf q (x v) (y v)) '' Icc s t ⊆ dualChamber q := by
    rintro _ ⟨v, hv, rfl⟩
    have := hP.chamber v
    rw [hlev v hv.1 hv.2] at this
    exact this
  obtain ⟨n₀, hn₀⟩ := hex _ (isCompact_Icc.image_of_continuousOn hcont) hL
  filter_upwards [eventually_ge_atTop n₀] with k hk
  by_contra hc
  have hle : hitLe (fun v (_ : Unit) => testVal q (u k) (n v) (x v) (y v)) (1 / 2) () ≤ t :=
    not_lt.1 hc
  obtain ⟨v, hvt, hv⟩ := (hitLe_le_iff (fun t' => tendsto_testVal_right hP (hcu k) t') t).1 hle
  have hone : testVal q (u k) (n v) (x v) (y v) = 1 := by
    rcases lt_or_ge v s with hvs | hsv
    · have h1 : q < n v := lt_level_of_lt_entryTime hP (hs' ▸ WithTop.coe_lt_coe.2 hvs)
      have h2 : n v ≠ q := by omega
      simp [testVal, dualLift, h1, h2]
    · have h1 := hlev v hsv hvt
      have h2 : ¬ q < n v := by omega
      simp only [testVal, dualLift, h1, ↓reduceIte, lt_irrefl, add_zero]
      exact hn₀ k hk _ ⟨v, ⟨hsv, hvt⟩, rfl⟩
  have hv' : testVal q (u k) (n v) (x v) (y v) ≤ 1 / 2 := hv
  linarith

/-- `R` along the path. -/
def pathTotal (n : ℝ≥0 → ℕ) (x y : ℝ≥0 → ℕ → ℝ) (t : ℝ≥0) : ℝ := dualTotal (n t) (x t) (y t)

theorem entryTime_mono_pred (q : ℕ) : entryTime n q ≤ entryTime n (q - 1) :=
  le_iInf₂ fun t ht => iInf₂_le t (ht.trans (Nat.sub_le q 1))

/-- **Convergence of the localized increments.** -/
theorem tendsto_level_gap (hP : IsDeletionPath n x y) (hq : 1 ≤ q) (hq0 : q ≤ n 0)
    (rho : ℝ≥0) (θ : ℕ → WithTop ℝ≥0)
    (hb : ∀ e : ℝ≥0, entryTime n (q - 1) = e → ∀ k, θ k ≤ e)
    (hc : ∀ t : ℝ≥0, entryTime n q ≤ t → (t : WithTop ℝ≥0) < entryTime n (q - 1) →
      ∀ᶠ k in atTop, (t : WithTop ℝ≥0) < θ k) :
    Tendsto (fun k => if entryTime n q ≤ ((min (rho : WithTop ℝ≥0) (θ k)).untopA : WithTop ℝ≥0)
        ∧ entryTime n q < θ k then
          pathTotal n x y (min (rho : WithTop ℝ≥0) (θ k)).untopA -
            pathTotal n x y (entryTime n q).untopA else 0) atTop
      (𝓝 (pathTotal n x y (min (rho : WithTop ℝ≥0) (entryTime n (q - 1))).untopA -
        pathTotal n x y (min (rho : WithTop ℝ≥0) (entryTime n q)).untopA)) := by
  have hR : Continuous (pathTotal n x y) := continuous_total hP
  have hmin_ne : ∀ a : WithTop ℝ≥0, min (rho : WithTop ℝ≥0) a ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  by_cases hE : entryTime n q ≤ rho
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hE)
    have hs' : entryTime n q = s := hs.symm
    have hsρ : s ≤ rho := WithTop.coe_le_coe.1 (hs' ▸ hE)
    have hsE' := entryTime_lt_pred hP hq hq0 hs'
    have hθs := hc s hs'.le hsE'
    have hmE : min (rho : WithTop ℝ≥0) (entryTime n q) = s := by
      rw [hs']; exact min_eq_right (WithTop.coe_le_coe.2 hsρ)
    rw [hmE, untopA_coe', hs', untopA_coe']
    by_cases hrE' : (rho : WithTop ℝ≥0) < entryTime n (q - 1)
    · have hθρ := hc rho hE hrE'
      rw [min_eq_left hrE'.le, untopA_coe']
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hθρ] with k hk
      rw [min_eq_left hk.le, untopA_coe']
      have hc1 : (s : WithTop ℝ≥0) ≤ rho := WithTop.coe_le_coe.2 hsρ
      have hc2 : (s : WithTop ℝ≥0) < θ k := lt_of_le_of_lt hc1 hk
      simp only [hc1, hc2, and_self, ↓reduceIte]
    · obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.1
        (ne_top_of_le_ne_top WithTop.coe_ne_top (not_lt.1 hrE'))
      have he' : entryTime n (q - 1) = e := he.symm
      have heρ : e ≤ rho := WithTop.coe_le_coe.1 (he' ▸ not_lt.1 hrE')
      have hse : s < e := WithTop.coe_lt_coe.1 (he' ▸ hsE')
      rw [he', min_eq_right (WithTop.coe_le_coe.2 heρ), untopA_coe']
      have hθe : ∀ k, θ k ≤ e := hb e he'
      have hmin : ∀ k, min (rho : WithTop ℝ≥0) (θ k) = θ k := fun k =>
        min_eq_right ((hθe k).trans (WithTop.coe_le_coe.2 heρ))
      have hfin : ∀ k, θ k ≠ ⊤ := fun k => ne_top_of_le_ne_top WithTop.coe_ne_top (hθe k)
      have hlim : Tendsto (fun k => (θ k).untopA) atTop (𝓝 e) := by
        refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
        · have h1 : (max a s : WithTop ℝ≥0) < entryTime n (q - 1) := by
            rw [he']; exact WithTop.coe_lt_coe.2 (max_lt ha hse)
          filter_upwards [hc (max a s) (hs'.trans_le (WithTop.coe_le_coe.2 (le_max_right a s)))
            h1] with k hk
          rw [← coe_untopA_of_ne_top (hfin k)] at hk
          exact lt_of_le_of_lt (le_max_left a s) (WithTop.coe_lt_coe.1 hk)
        · refine Eventually.of_forall fun k => lt_of_le_of_lt ?_ ha
          rw [← WithTop.coe_le_coe, coe_untopA_of_ne_top (hfin k)]
          exact hθe k
      refine ((hR.tendsto e).comp hlim |>.sub tendsto_const_nhds).congr' ?_
      filter_upwards [hθs] with k hk
      rw [hmin k]
      have h1 : (s : WithTop ℝ≥0) ≤ ((θ k).untopA : WithTop ℝ≥0) := by
        rw [coe_untopA_of_ne_top (hfin k)]; exact hk.le
      simp only [h1, hk, and_self, ↓reduceIte, Function.comp_apply]
  · have hE' : ¬ entryTime n (q - 1) ≤ rho := fun h => hE ((entryTime_mono_pred q).trans h)
    rw [min_eq_left (not_le.1 hE').le, min_eq_left (not_le.1 hE).le, sub_self]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
    have : ¬ entryTime n q ≤ ((min (rho : WithTop ℝ≥0) (θ k)).untopA : WithTop ℝ≥0) := by
      rw [coe_untopA_of_ne_top (hmin_ne _)]
      exact fun h => hE (h.trans (min_le_left _ _))
    simp only [this, false_and, ↓reduceIte]

/-- `0 ≤ R ≤ K` up to the hitting time of `{R ≥ K}`, when `R₀ < K`. -/
theorem total_le_of_le_hit (hP : IsDeletionPath n x y) {K : ℝ} (h0 : pathTotal n x y 0 < K)
    {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) ≤
      ⨅ (t : ℝ≥0) (_ : -pathTotal n x y t ≤ -K), (t : WithTop ℝ≥0)) :
    pathTotal n x y u ≤ K := by
  have hR : Continuous (pathTotal n x y) := continuous_total hP
  have hlt : ∀ v : ℝ≥0, v < u → pathTotal n x y v < K := fun v hv => by
    by_contra hc
    have : (⨅ (t : ℝ≥0) (_ : -pathTotal n x y t ≤ -K), (t : WithTop ℝ≥0)) ≤ v :=
      iInf₂_le v (by linarith [not_lt.1 hc])
    exact absurd (hu.trans this) (not_le.2 (WithTop.coe_lt_coe.2 hv))
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h | hpos
  · rw [← h]; exact h0.le
  · have : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
    have hT : Tendsto (pathTotal n x y) (𝓝[<] u) (𝓝 (pathTotal n x y u)) :=
      (hR.tendsto u).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hT ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hlt v hv).le

end BlockBand.Transmission.Dual
