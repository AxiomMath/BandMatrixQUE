module

public import BlockBand.Transmission.Dual.Statement

/-!
# Pathwise facts on a deletion path

* `exists_left_level`: an antitone `ℕ`-valued path is constant on some `[u₀, t)`;
* `entryTime n q` (first time `n ≤ q`, `⊤` if never), `entryTime_le_iff`
  (`σ_q ≤ t ↔ n_t ≤ q`), `level_entryTime` (no level is skipped: `n(σ_q) = q`);
* one-sided limits of the coordinates (`tendsto_coord_right`, `tendsto_coord_left_same`,
  and the deletion clause at a jump);
* `continuous_total`: `t ↦ R_t = Σ_{i<n_t}(x_i+y_i)` is continuous (both deleted coordinates
  tend to `0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

/-- First time the level is `≤ q` (`⊤` if never). -/
def entryTime (n : ℝ≥0 → ℕ) (q : ℕ) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : n t ≤ q), (t : WithTop ℝ≥0)

/-- An antitone `ℕ`-valued path is constant on an interval `[u₀, t)` to the left of `t > 0`. -/
theorem exists_left_level {n : ℝ≥0 → ℕ} (hn : Antitone n) {t : ℝ≥0} (ht : 0 < t) :
    ∃ (k : ℕ) (u₀ : ℝ≥0), u₀ < t ∧ ∀ u ∈ Ico u₀ t, n u = k := by
  classical
  have hne : ∃ k, ∃ u < t, n u = k := ⟨n 0, 0, ht, rfl⟩
  let k := Nat.find hne
  obtain ⟨u₀, hu₀, hk⟩ := Nat.find_spec hne
  refine ⟨k, u₀, hu₀, fun u hu => le_antisymm ?_ ?_⟩
  · exact (hn hu.1).trans hk.le
  · exact Nat.find_min' hne ⟨u, hu.2, rfl⟩

section Path

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ}

/-- The level is constant on a right neighbourhood `[t, b)`. -/
theorem exists_right_level (hP : IsDeletionPath n x y) (t : ℝ≥0) :
    ∃ b, t < b ∧ ∀ u ∈ Ico t b, n u = n t := by
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hP.rightCont t)
  refine ⟨b, hb, fun u hu => ?_⟩
  rcases eq_or_lt_of_le hu.1 with h | h
  · rw [h]
  · exact hsub ⟨h, hu.2⟩

theorem entryTime_le_iff (hP : IsDeletionPath n x y) (q : ℕ) (t : ℝ≥0) :
    entryTime n q ≤ t ↔ n t ≤ q := by
  constructor
  · intro h
    by_contra hlt'
    have hlt : q < n t := not_le.1 hlt'
    obtain ⟨b, hb, hsub⟩ := exists_right_level hP t
    have hb' : (b : WithTop ℝ≥0) ≤ entryTime n q := by
      refine le_iInf₂ fun u hu => ?_
      rw [WithTop.coe_le_coe]
      by_contra hub'
      have hub : u < b := not_le.1 hub'
      rcases le_or_gt u t with hut | htu
      · have := hP.antitone hut
        omega
      · have := hsub u ⟨htu.le, hub⟩
        omega
    exact absurd (hb'.trans h) (not_le.2 (WithTop.coe_lt_coe.2 hb))
  · intro h
    exact iInf₂_le t h

theorem entryTime_lt_top_iff (q : ℕ) : entryTime n q < ⊤ ↔ ∃ t, n t ≤ q := by
  constructor
  · intro h
    by_contra hc
    have : entryTime n q = ⊤ := iInf₂_eq_top.2 fun t ht => absurd ⟨t, ht⟩ hc
    exact absurd this h.ne
  · rintro ⟨t, ht⟩
    exact lt_of_le_of_lt (iInf₂_le t ht) (WithTop.coe_lt_top t)

theorem lt_level_of_lt_entryTime (hP : IsDeletionPath n x y) {q : ℕ} {u : ℝ≥0}
    (hu : (u : WithTop ℝ≥0) < entryTime n q) : q < n u := by
  by_contra h'
  exact absurd ((entryTime_le_iff hP q u).2 (not_lt.1 h')) (not_le.2 hu)

/-- **No level is skipped**: at the entrance time into the levels `≤ q < n₀`, the level is
exactly `q`. -/
theorem level_entryTime (hP : IsDeletionPath n x y) {q : ℕ} (hq : q < n 0) {s : ℝ≥0}
    (hs : entryTime n q = s) : n s = q := by
  have h1 : n s ≤ q := (entryTime_le_iff hP q s).1 hs.le
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h | h
    · rw [← h] at h1; omega
    · exact h
  obtain ⟨k, u₀, hu₀, hk⟩ := exists_left_level hP.antitone hspos
  have hkq : q < k := by
    rw [← hk u₀ ⟨le_rfl, hu₀⟩]
    exact lt_level_of_lt_entryTime hP (by rw [hs]; exact WithTop.coe_lt_coe.2 hu₀)
  have hev : ∀ᶠ u in 𝓝[<] s, n u = (k - 1) + 1 :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hu₀) fun u hu => by
      show n u = k - 1 + 1
      rw [hk u ⟨hu.1.le, hu.2⟩]; omega
  have := (hP.deletion s hspos (k - 1) hev (by omega)).1
  omega

/-- Right limits of the coordinates of index `< n_t`. -/
theorem tendsto_coord_right (hP : IsDeletionPath n x y) (t : ℝ≥0) {i : ℕ} (hi : i < n t) :
    Tendsto (fun u => x u i) (𝓝[≥] t) (𝓝 (x t i)) ∧
      Tendsto (fun u => y u i) (𝓝[≥] t) (𝓝 (y t i)) := by
  obtain ⟨b, hb, hlev⟩ := exists_right_level hP t
  obtain ⟨c, htc, hcb⟩ := exists_between hb
  have hc := hP.cont t c htc.le (hlev c ⟨htc.le, hcb⟩) i hi
  have hmem : Icc t c ∈ 𝓝[≥] t := Icc_mem_nhdsGE htc
  exact ⟨(hc.1.continuousWithinAt ⟨le_rfl, htc.le⟩).mono_of_mem_nhdsWithin hmem,
    (hc.2.continuousWithinAt ⟨le_rfl, htc.le⟩).mono_of_mem_nhdsWithin hmem⟩

/-- Left limits of the coordinates when the level does not jump at `t`. -/
theorem tendsto_coord_left_same (hP : IsDeletionPath n x y) {t u₀ : ℝ≥0} (hu₀ : u₀ < t)
    (hk : ∀ u ∈ Ico u₀ t, n u = n t) {i : ℕ} (hi : i < n t) :
    Tendsto (fun u => x u i) (𝓝[<] t) (𝓝 (x t i)) ∧
      Tendsto (fun u => y u i) (𝓝[<] t) (𝓝 (y t i)) := by
  have hc := hP.cont u₀ t hu₀.le (hk u₀ ⟨le_rfl, hu₀⟩).symm i
    (by rw [hk u₀ ⟨le_rfl, hu₀⟩]; exact hi)
  have hmem : Icc u₀ t ∈ 𝓝[<] t :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hu₀) Ioo_subset_Icc_self
  exact ⟨(hc.1.continuousWithinAt ⟨hu₀.le, le_rfl⟩).mono_of_mem_nhdsWithin hmem,
    (hc.2.continuousWithinAt ⟨hu₀.le, le_rfl⟩).mono_of_mem_nhdsWithin hmem⟩

/-- At a jump the left level is `n_t + 1` and the deletion clause applies. -/
theorem left_jump (hP : IsDeletionPath n x y) {t u₀ : ℝ≥0} {k : ℕ} (hu₀ : u₀ < t)
    (hk : ∀ u ∈ Ico u₀ t, n u = k) (hne : k ≠ n t) :
    k = n t + 1 ∧ Tendsto (fun u => x u 0) (𝓝[<] t) (𝓝 0) ∧
      Tendsto (fun u => y u 0) (𝓝[<] t) (𝓝 0) ∧
      ∀ i, i < n t → Tendsto (fun u => x u (i + 1)) (𝓝[<] t) (𝓝 (x t i)) ∧
        Tendsto (fun u => y u (i + 1)) (𝓝[<] t) (𝓝 (y t i)) := by
  have htpos : 0 < t := lt_of_le_of_lt (zero_le) hu₀
  have hge : n t ≤ k := hk u₀ ⟨le_rfl, hu₀⟩ ▸ hP.antitone hu₀.le
  have hev : ∀ᶠ u in 𝓝[<] t, n u = (k - 1) + 1 :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hu₀) fun u hu => by
      show n u = k - 1 + 1
      rw [hk u ⟨hu.1.le, hu.2⟩]; omega
  obtain ⟨h1, h2, h3, h4⟩ := hP.deletion t htpos (k - 1) hev (by omega)
  refine ⟨by omega, h2, h3, fun i hi => h4 i (by omega)⟩

/-- **`R` is continuous along a deletion path.** -/
theorem continuous_total (hP : IsDeletionPath n x y) :
    Continuous fun t => dualTotal (n t) (x t) (y t) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | htpos
    · subst h0
      have : Iio (0 : ℝ≥0) = ∅ := Set.eq_empty_iff_forall_notMem.2 fun u hu =>
        absurd hu (not_lt.2 (zero_le : (0 : ℝ≥0) ≤ u))
      rw [this, ContinuousWithinAt, nhdsWithin_empty]
      exact tendsto_bot
    obtain ⟨k, u₀, hu₀, hk⟩ := exists_left_level hP.antitone htpos
    have hev : ∀ᶠ u in 𝓝[<] t, n u = k :=
      Filter.mem_of_superset (Ioo_mem_nhdsLT hu₀) fun u hu => hk u ⟨hu.1.le, hu.2⟩
    by_cases hkt : k = n t
    · subst hkt
      have hsum : Tendsto (fun u => ∑ i ∈ Finset.range (n t), (x u i + y u i)) (𝓝[<] t)
          (𝓝 (∑ i ∈ Finset.range (n t), (x t i + y t i))) := by
        refine tendsto_finsetSum _ fun i hi => ?_
        obtain ⟨h1, h2⟩ := tendsto_coord_left_same hP hu₀ hk (Finset.mem_range.1 hi)
        exact h1.add h2
      refine hsum.congr' ?_
      filter_upwards [hev] with u hu
      simp [dualTotal, hu]
    · obtain ⟨hk1, hx0, hy0, hrest⟩ := left_jump hP hu₀ hk hkt
      have hsum : Tendsto (fun u => (x u 0 + y u 0) +
          ∑ i ∈ Finset.range (n t), (x u (i + 1) + y u (i + 1))) (𝓝[<] t)
          (𝓝 ((0 + 0) + ∑ i ∈ Finset.range (n t), (x t i + y t i))) := by
        refine (hx0.add hy0).add (tendsto_finsetSum _ fun i hi => ?_)
        obtain ⟨h1, h2⟩ := hrest i (Finset.mem_range.1 hi)
        exact h1.add h2
      simp only [add_zero, zero_add] at hsum
      refine hsum.congr' ?_
      filter_upwards [hev] with u hu
      simp only [dualTotal, hu, hk1, Finset.sum_range_succ']
      ring
  · have hsum : Tendsto (fun u => ∑ i ∈ Finset.range (n t), (x u i + y u i)) (𝓝[≥] t)
        (𝓝 (∑ i ∈ Finset.range (n t), (x t i + y t i))) := by
      refine tendsto_finsetSum _ fun i hi => ?_
      obtain ⟨h1, h2⟩ := tendsto_coord_right hP t (Finset.mem_range.1 hi)
      exact h1.add h2
    obtain ⟨b, hb, hlev⟩ := exists_right_level hP t
    have hev : ∀ᶠ u in 𝓝[≥] t, n u = n t :=
      Filter.mem_of_superset (Ico_mem_nhdsGE hb) fun u hu => hlev u hu
    have : Tendsto (fun u => dualTotal (n u) (x u) (y u)) (𝓝[≥] t)
        (𝓝 (dualTotal (n t) (x t) (y t))) := by
      refine hsum.congr' ?_
      filter_upwards [hev] with u hu
      simp [dualTotal, hu]
    exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

end Path

end BlockBand.Transmission.Dual
