module

public import BlockBand.Transmission.Dual.PathLift

/-!
# The localizing test process and the pathwise value of the stopped martingale

Along a deletion path, for a continuous cutoff `h : DualCoord q → [0,1]` vanishing off `𝒞_q`, the
test process `P_t = h(Z_t)1{N_t = q} + 1{N_t > q}` (`testVal`) is right-continuous and lower
semicontinuous (its only downward jump is at `σ_q`), and left-continuous at every `t ≠ σ_q`.

`dualMartingale_eq_of_le_hit`: if `f = R` on an open set containing `{h ≥ 1/2}`, `θ` is a time
before which `P > 1/2`, and `r ≤ θ`, then `dualMartingale D₀ q f` at time `r` equals
`R_r − R_{σ_q}` if `σ_q ≤ r` and `σ_q < θ`, and `0` otherwise. (Before `θ` the level-`q` state
stays where `f = R` and `𝒟_q f = 𝒟_q R = 0`.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable {q : ℕ}

/-- `h(z)1{k = q} + 1{k > q}` at the state `(k; x, y)`. -/
def testVal (q : ℕ) (h : DualCoord q → ℝ) (k : ℕ) (x y : ℕ → ℝ) : ℝ :=
  dualLift h k x y + if q < k then 1 else 0

theorem untopA_coe' (s : ℝ≥0) : (s : WithTop ℝ≥0).untopA = s := rfl

theorem totalFun_dualCoordOf (q : ℕ) (x y : ℕ → ℝ) :
    totalFun q (dualCoordOf q x y) = dualTotal q x y := by
  simp only [totalFun, dualCoordOf, dualTotal]
  exact Fin.sum_univ_eq_sum_range (fun i => x i + y i) q

section PathLemmas

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ}

theorem tendsto_testVal_right (hP : IsDeletionPath n x y) {h : DualCoord q → ℝ}
    (hh : Continuous h) (t : ℝ≥0) :
    Tendsto (fun u => testVal q h (n u) (x u) (y u)) (𝓝[≥] t)
      (𝓝 (testVal q h (n t) (x t) (y t))) := by
  obtain ⟨b, hb, hlev⟩ := exists_right_level hP t
  have hev : ∀ᶠ u in 𝓝[≥] t, n u = n t := mem_of_superset (Ico_mem_nhdsGE hb) hlev
  refine (tendsto_lift_right hP hh t).add (tendsto_const_nhds.congr' ?_)
  filter_upwards [hev] with u hu
  rw [hu]

theorem tendsto_testVal_left (hP : IsDeletionPath n x y) {h : DualCoord q → ℝ}
    (hh : Continuous h) (hh0 : ∀ z ∉ dualChamber q, h z = 0) (hq : 1 ≤ q) {t u₀ : ℝ≥0}
    (hu₀ : u₀ < t) {k : ℕ} (hk : ∀ u ∈ Ico u₀ t, n u = k) :
    Tendsto (fun u => testVal q h (n u) (x u) (y u)) (𝓝[<] t)
      (𝓝 ((if k = n t then dualLift h (n t) (x t) (y t) else 0) +
        if q < k then 1 else 0)) := by
  have hev : ∀ᶠ u in 𝓝[<] t, n u = k :=
    mem_of_superset (Ioo_mem_nhdsLT hu₀) fun u hu => hk u ⟨hu.1.le, hu.2⟩
  refine (tendsto_lift_left hP hh hh0 hq hu₀ hk).add (tendsto_const_nhds.congr' ?_)
  filter_upwards [hev] with u hu
  rw [hu]

theorem lowerSemicontinuous_testVal (hP : IsDeletionPath n x y) {h : DualCoord q → ℝ}
    (hh : Continuous h) (hh0 : ∀ z ∉ dualChamber q, h z = 0) (hh1 : ∀ z, h z ≤ 1)
    (hq : 1 ≤ q) : LowerSemicontinuous fun u => testVal q h (n u) (x u) (y u) := by
  intro t
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | htpos
  · subst h0
    refine lowerSemicontinuousAt_of_one_sided (tendsto_testVal_right hP hh 0)
      (L := testVal q h (n 0) (x 0) (y 0)) (by rw [nhdsLT_zero_nnreal]; exact tendsto_bot) le_rfl
  obtain ⟨k, u₀, hu₀, hk⟩ := exists_left_level hP.antitone htpos
  refine lowerSemicontinuousAt_of_one_sided (tendsto_testVal_right hP hh t)
    (tendsto_testVal_left hP hh hh0 hq hu₀ hk) ?_
  by_cases hkt : k = n t
  · simp [hkt, testVal]
  · have hk1 := (left_jump hP hu₀ hk hkt).1
    have hkq : (if q < k then (1 : ℝ) else 0) = if q < n t + 1 then 1 else 0 := by rw [hk1]
    simp only [hkt, ↓reduceIte, zero_add, testVal, hkq]
    by_cases hnq : n t = q
    · have h1 : dualLift h (n t) (x t) (y t) ≤ 1 := by simp [dualLift, hnq, hh1]
      have h2 : ¬ q < n t := by omega
      have h3 : q < n t + 1 := by omega
      simp only [h2, h3, ↓reduceIte, add_zero]
      exact h1
    · have h1 : dualLift h (n t) (x t) (y t) = 0 := by simp [dualLift, hnq]
      rw [h1, zero_add]
      by_cases h2 : q < n t
      · have h3 : q < n t + 1 := by omega
        simp [h2, h3]
      · simp only [h2, ↓reduceIte]; split_ifs <;> norm_num

theorem tendsto_testVal_left_of_ne (hP : IsDeletionPath n x y) {h : DualCoord q → ℝ}
    (hh : Continuous h) (hh0 : ∀ z ∉ dualChamber q, h z = 0) (hq : 1 ≤ q) {t : ℝ≥0}
    (htpos : 0 < t) (hne : entryTime n q ≠ t) :
    Tendsto (fun u => testVal q h (n u) (x u) (y u)) (𝓝[<] t)
      (𝓝 (testVal q h (n t) (x t) (y t))) := by
  obtain ⟨k, u₀, hu₀, hk⟩ := exists_left_level hP.antitone htpos
  have hL := tendsto_testVal_left hP hh hh0 hq hu₀ hk
  by_cases hkt : k = n t
  · simpa [hkt, testVal] using hL
  · have hnq : n t ≠ q := fun e => hne (entryTime_eq_of_jump_into hP hu₀ hk hkt e)
    have hk1 := (left_jump hP hu₀ hk hkt).1
    have e1 : dualLift h (n t) (x t) (y t) = 0 := by simp [dualLift, hnq]
    have e2 : (if q < k then (1 : ℝ) else 0) = if q < n t then 1 else 0 := by
      rw [hk1]; split_ifs <;> first | rfl | omega
    simp only [hkt, ↓reduceIte, zero_add, e2] at hL
    simpa [testVal, e1] using hL

end PathLemmas

/-- The entrance value in terms of `entryTime` (cf. `continuous_dualMartingale`). -/
theorem dualEntranceValue_eq_of_entryTime {Ω : Type*} {N : ℝ≥0 → Ω → ℕ}
    {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (f : DualCoord q → ℝ) {s : ℝ≥0} (hs : entryTime (fun t => N t ω) q = s) (t : ℝ≥0) :
    dualEntranceValue f N X Y t ω = if s ≤ t then dualLift f (N s ω) (X s ω) (Y s ω) else 0 := by
  have hσ : dualEntrance N q ω = s := by
    refine IsLeast.csInf_eq ⟨(entryTime_le_iff hP q s).1 hs.le, fun u hu => ?_⟩
    exact WithTop.coe_le_coe.1 (hs ▸ (entryTime_le_iff hP q u).2 hu)
  have hiff : (∃ u ≤ t, N u ω ≤ q) ↔ s ≤ t := by
    rw [← WithTop.coe_le_coe, ← hs, entryTime_le_iff hP q t]
    exact ⟨fun ⟨u, hut, hu⟩ => (hP.antitone hut).trans hu, fun h => ⟨t, le_rfl, h⟩⟩
  by_cases hst : s ≤ t
  · simp only [dualEntranceValue, hiff.2 hst, ↓reduceIte, hσ, hst]
  · simp only [dualEntranceValue, mt hiff.1 hst, ↓reduceIte, hst]

/-- **Pathwise value of the localized martingale.** -/
theorem dualMartingale_eq_of_le_hit {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    {ω : Ω} (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (D0 : ℝ) (hq : 1 ≤ q) (hq0 : q ≤ N 0 ω) {h : DualCoord q → ℝ} (hh : Continuous h)
    (hh0 : ∀ z ∉ dualChamber q, h z = 0) {f : DualCoord q → ℝ} {O : Set (DualCoord q)}
    (hO : IsOpen O) (hhO : ∀ z, 1 / 2 ≤ h z → z ∈ O) (hfO : EqOn f (totalFun q) O)
    {θ : WithTop ℝ≥0}
    (hθ : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < θ → 1 / 2 < testVal q h (N u ω) (X u ω) (Y u ω))
    {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) ≤ θ) :
    dualMartingale D0 q f N X Y r ω =
      if entryTime (fun t => N t ω) q ≤ r ∧ entryTime (fun t => N t ω) q < θ then
        dualTotal (N r ω) (X r ω) (Y r ω) - dualTotal (N (entryTime (fun t => N t ω) q).untopA ω)
          (X (entryTime (fun t => N t ω) q).untopA ω) (Y (entryTime (fun t => N t ω) q).untopA ω)
      else 0 := by
  set n : ℝ≥0 → ℕ := fun t => N t ω with hn
  by_cases hE : entryTime n q ≤ r
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hE)
    have hs' : entryTime n q = s := hs.symm
    have hsr : s ≤ r := WithTop.coe_le_coe.1 (hs' ▸ hE)
    have hns : n s = q := by
      rcases lt_or_eq_of_le hq0 with hlt | heq
      · exact level_entryTime hP hlt hs'
      · have h0 : entryTime n q ≤ (0 : ℝ≥0) := (entryTime_le_iff hP q 0).2 heq.ge
        rw [hs'] at h0
        have : s = 0 := le_antisymm (WithTop.coe_le_coe.1 h0) zero_le
        rw [this]; exact heq.symm
    have hent := dualEntranceValue_eq_of_entryTime hP f hs' r
    simp only [hsr, ↓reduceIte] at hent
    rw [hs']
    simp only [untopA_coe', WithTop.coe_le_coe, hsr, true_and]
    by_cases hsθ : (s : WithTop ℝ≥0) < θ
    · simp only [hsθ, ↓reduceIte]
      -- on `[s, r]` the level is `q` and `h ≥ 1/2`
      have key : ∀ u : ℝ≥0, s ≤ u → u ≤ r → n u = q ∧
          1 / 2 ≤ h (dualCoordOf q (X u ω) (Y u ω)) := by
        intro u hsu hur
        have hle : n u ≤ q := (entryTime_le_iff hP q u).1 (hs' ▸ WithTop.coe_le_coe.2 hsu)
        have hP12 : 1 / 2 ≤ testVal q h (n u) (X u ω) (Y u ω) := by
          rcases lt_or_eq_of_le ((WithTop.coe_le_coe.2 hur).trans hr) with hlt | heq
          · exact (hθ u hlt).le
          · have hupos : 0 < u := lt_of_le_of_lt zero_le
              (WithTop.coe_lt_coe.1 (lt_of_lt_of_le hsθ (heq ▸ le_rfl)))
            have hne : entryTime n q ≠ u := by
              rw [hs']; intro e; rw [e] at hsθ; exact (hsθ.ne heq).elim
            have : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hupos⟩
            refine ge_of_tendsto (tendsto_testVal_left_of_ne hP hh hh0 hq hupos hne) ?_
            filter_upwards [self_mem_nhdsWithin] with v hv
            exact (hθ v (lt_of_lt_of_le (WithTop.coe_lt_coe.2 hv) heq.le)).le
        have hnot : ¬ q < n u := not_lt.2 hle
        simp only [testVal, hnot, ↓reduceIte, add_zero] at hP12
        by_cases hnu : n u = q
        · refine ⟨hnu, ?_⟩
          simpa [dualLift, hnu] using hP12
        · simp [dualLift, hnu] at hP12; linarith
      have fR : ∀ u : ℝ≥0, s ≤ u → u ≤ r →
          dualLift f (N u ω) (X u ω) (Y u ω) = dualTotal (N u ω) (X u ω) (Y u ω) := by
        intro u hsu hur
        obtain ⟨h1, h2⟩ := key u hsu hur
        have h1' : N u ω = q := h1
        simp only [dualLift, h1', ↓reduceIte]
        rw [hfO (hhO _ h2), totalFun_dualCoordOf]
      have hint : ∫ u in Ioc (0 : ℝ) r, dualLift (dualGenerator D0 f) (N u.toNNReal ω)
          (X u.toNNReal ω) (Y u.toNNReal ω) = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
        have hur : u.toNNReal ≤ r := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
        by_cases hnu : N u.toNNReal ω = q
        · have hsu : s ≤ u.toNNReal := WithTop.coe_le_coe.1
            (hs' ▸ (entryTime_le_iff hP q _).2 hnu.le)
          obtain ⟨-, h2⟩ := key _ hsu hur
          have hch : dualCoordOf q (X u.toNNReal ω) (Y u.toNNReal ω) ∈ dualChamber q := by
            have := hP.chamber u.toNNReal
            rw [show n u.toNNReal = q from hnu] at this
            exact this
          simp only [dualLift, hnu, ↓reduceIte]
          exact dualGenerator_eq_zero_of_eqOn_total D0 hO hfO (hhO _ h2) hch
        · simp [dualLift, hnu]
      simp only [dualMartingale, hent, hint, sub_zero]
      rw [fR r hsr le_rfl, fR s le_rfl hsr]
    · simp only [hsθ, ↓reduceIte]
      have hrs : r = s := le_antisymm (WithTop.coe_le_coe.1 (hr.trans (not_lt.1 hsθ))) hsr
      subst hrs
      have hint : ∫ u in Ioc (0 : ℝ) r, dualLift (dualGenerator D0 f) (N u.toNNReal ω)
          (X u.toNNReal ω) (Y u.toNNReal ω) = 0 := by
        rw [integral_Ioc_eq_integral_Ioo]
        refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
        have hur : u.toNNReal < r := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
        have : q < n u.toNNReal :=
          lt_level_of_lt_entryTime hP (by rw [hs']; exact WithTop.coe_lt_coe.2 hur)
        have this' : q < N u.toNNReal ω := this
        have hne : N u.toNNReal ω ≠ q := by omega
        simp [dualLift, hne]
      simp only [dualMartingale, hent, hint, sub_self]
  · have hgt : ∀ u ≤ r, q < n u := fun u hu => by
      by_contra hc
      exact hE (((entryTime_le_iff hP q u).2 (not_lt.1 hc)).trans (WithTop.coe_le_coe.2 hu))
    simp only [hE, false_and, ↓reduceIte]
    have h1 : N r ω ≠ q := (hgt r le_rfl).ne'
    have h2 : ¬ ∃ u ≤ r, N u ω ≤ q := fun ⟨u, hu, hle⟩ => absurd hle (not_le.2 (hgt u hu))
    have hint : ∫ u in Ioc (0 : ℝ) r, dualLift (dualGenerator D0 f) (N u.toNNReal ω)
        (X u.toNNReal ω) (Y u.toNNReal ω) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      have hur : u.toNNReal ≤ r := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
      have hne : N u.toNNReal ω ≠ q := (hgt _ hur).ne'
      simp [dualLift, hne]
    simp only [dualMartingale, hint, sub_zero]
    simp [dualLift, h1, dualEntranceValue, h2]

end BlockBand.Transmission.Dual
