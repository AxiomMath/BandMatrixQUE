module

public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# Path facts for one-pair boundary paths

Setting: an `IsBoundaryDeletionPath n x y` (deterministic path) started at level `n 0 = 1`, as
every path of a boundary realization `IsBoundaryDualProcess … ![x] ![y]` is a.s. No measure is
involved here.
* `level_le_one`, `level_eq_one_or_zero`: the level takes the values `0, 1` only.
* `continuous_ite_level`: `t ↦ 1{n_t = 1} c_t` is continuous on `[0, ∞)` for a coordinate `c`
  continuous on the closed intervals of level one that tends to `0` at the deletion time; hence
  `continuous_truncX`, `continuous_truncY` (`Z̄ = π(ξ)1{t < ζ}` is continuous through `ζ`),
  and **`continuous_dualTotal`** (`R_t = S(Z̄_t)` is continuous on `[0, ∞)`).
* **`dualExtinction_le_iff`**: `ζ ≤ t ↔ n_t = 0` (right-continuity of the level), so
  `{ζ ≤ t}` is a function of the state at the single time `t`.
* `continuousWithinAt_truncDualState`: the truncated state path is right-continuous at every
  time, in particular `Z̄_s → z₀` as `s ↓ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open scoped NNReal ENNReal

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ}

theorem level_le_one (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1) (t : ℝ≥0) :
    n t ≤ 1 :=
  h0 ▸ hP.antitone (zero_le : (0 : ℝ≥0) ≤ t)

theorem level_eq_one_or_zero (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1) (t : ℝ≥0) :
    n t = 1 ∨ n t = 0 := by
  have := level_le_one hP h0 t
  omega

/-- A time of level one lies strictly before another time of level one. -/
theorem exists_gt_level_one (hP : IsBoundaryDeletionPath n x y) {t : ℝ≥0} (ht : n t = 1) :
    ∃ u, t < u ∧ n u = 1 := by
  obtain ⟨u, hu, hnu⟩ := ((hP.rightCont t).and self_mem_nhdsWithin).exists
  exact ⟨u, hnu, hu.trans ht⟩

theorem level_one_of_le (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1) {u v : ℝ≥0}
    (huv : u ≤ v) (hv : n v = 1) : n u = 1 :=
  le_antisymm (level_le_one hP h0 u) (hv ▸ hP.antitone huv)

/-- **Continuity of `1{n_t = 1} c_t`.** -/
theorem continuous_ite_level (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1)
    {c : ℝ≥0 → ℝ} (hcont : ∀ t₂, n t₂ = 1 → ContinuousOn c (Icc 0 t₂))
    (hdel : ∀ t, 0 < t → (∀ u < t, n u = 1) → n t = 0 → Tendsto c (𝓝[<] t) (𝓝 0)) :
    Continuous fun t => if n t = 1 then c t else 0 := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases level_eq_one_or_zero hP h0 t with ht | ht
  · obtain ⟨u, htu, hu⟩ := exists_gt_level_one hP ht
    have hmem : Icc 0 u ∈ 𝓝 t :=
      mem_of_superset (Iio_mem_nhds htu) fun v hv => ⟨(zero_le : (0 : ℝ≥0) ≤ v), (mem_Iio.1 hv).le⟩
    have heq : (fun t => if n t = 1 then c t else 0) =ᶠ[𝓝 t] c :=
      Filter.mem_of_superset hmem fun v hv => by
        simp [level_one_of_le hP h0 hv.2 hu]
    exact (((hcont u hu).continuousAt hmem).congr heq.symm)
  · by_cases hex : ∃ u < t, n u = 0
    · obtain ⟨u, hut, hu⟩ := hex
      have heq : (fun t => if n t = 1 then c t else 0) =ᶠ[𝓝 t] fun _ => 0 :=
        Filter.mem_of_superset (Ioi_mem_nhds hut) fun v hv => by
          have : n v = 0 := Nat.le_zero.1 (hu ▸ hP.antitone (mem_Ioi.1 hv).le)
          simp [this]
      exact continuousAt_const.congr heq.symm
    · push Not at hex
      have hlt : ∀ u < t, n u = 1 := fun u hu =>
        (level_eq_one_or_zero hP h0 u).resolve_right (hex u hu)
      have htpos : 0 < t := pos_iff_ne_zero.2 fun h => by simp [h, h0] at ht
      refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
      · rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt]
        simp only [ht, zero_ne_one, ite_false]
        refine (hdel t htpos hlt ht).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with v hv
        simp [hlt v hv]
      · refine (continuousWithinAt_const (b := (0 : ℝ))).congr (fun v hv => ?_) (by simp [ht])
        have : n v = 0 := Nat.le_zero.1 (ht ▸ hP.antitone hv)
        simp [this]

theorem tendsto_deletion (hP : IsBoundaryDeletionPath n x y) {t : ℝ≥0} (htpos : 0 < t)
    (hlt : ∀ u < t, n u = 1) (ht : n t = 0) :
    Tendsto (fun u => x u 0) (𝓝[<] t) (𝓝 0) ∧ Tendsto (fun u => y u 0) (𝓝[<] t) (𝓝 0) := by
  have hev : ∀ᶠ u in 𝓝[<] t, n u = 0 + 1 := by
    filter_upwards [self_mem_nhdsWithin] with v hv using hlt v hv
  obtain ⟨-, hx, hy, -⟩ := hP.deletion t htpos 0 hev (by rw [ht]; exact zero_ne_one)
  exact ⟨hx, hy⟩

theorem continuousOn_level_one (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1) {t₂ : ℝ≥0}
    (h2 : n t₂ = 1) :
    ContinuousOn (fun u => x u 0) (Icc 0 t₂) ∧ ContinuousOn (fun u => y u 0) (Icc 0 t₂) :=
  hP.cont 0 t₂ (zero_le : (0 : ℝ≥0) ≤ t₂) (h2.trans h0.symm) 0 (by rw [h0]; exact one_pos)

theorem truncDualCoord_level (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1)
    (c : ℝ≥0 → ℕ → ℝ) (t : ℝ≥0) (i : ℕ) :
    truncDualCoord (n t) (c t) i = if n t = 1 ∧ i = 0 then c t 0 else 0 := by
  unfold truncDualCoord
  rcases level_eq_one_or_zero hP h0 t with ht | ht <;> rw [ht]
  · by_cases hi : i = 0
    · subst hi; simp
    · simp [hi]
  · simp

/-- `Z̄_t` (`x`-coordinate) is continuous through the lifetime. -/
theorem continuous_truncX (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1) :
    Continuous fun t => truncDualCoord (n t) (x t) 0 := by
  have e : (fun t => truncDualCoord (n t) (x t) 0) = fun t => if n t = 1 then x t 0 else 0 := by
    funext t; rw [truncDualCoord_level hP h0]; simp
  rw [e]
  exact continuous_ite_level hP h0 (fun t₂ h2 => (continuousOn_level_one hP h0 h2).1)
    fun t ht hlt h => (tendsto_deletion hP ht hlt h).1

/-- `Z̄_t` (`y`-coordinate) is continuous through the lifetime. -/
theorem continuous_truncY (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1) :
    Continuous fun t => truncDualCoord (n t) (y t) 0 := by
  have e : (fun t => truncDualCoord (n t) (y t) 0) = fun t => if n t = 1 then y t 0 else 0 := by
    funext t; rw [truncDualCoord_level hP h0]; simp
  rw [e]
  exact continuous_ite_level hP h0 (fun t₂ h2 => (continuousOn_level_one hP h0 h2).2)
    fun t ht hlt h => (tendsto_deletion hP ht hlt h).2

theorem dualTotal_level (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1) (t : ℝ≥0) :
    dualTotal (n t) (x t) (y t) =
      truncDualCoord (n t) (x t) 0 + truncDualCoord (n t) (y t) 0 := by
  rw [truncDualCoord_level hP h0, truncDualCoord_level hP h0]
  rcases level_eq_one_or_zero hP h0 t with ht | ht <;> simp [dualTotal, ht]

/-- **`R_t = S(Z̄_t)` is continuous on `[0, ∞)`** for a one-pair boundary path. -/
theorem continuous_dualTotal (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1) :
    Continuous fun t => dualTotal (n t) (x t) (y t) := by
  simp_rw [dualTotal_level hP h0]
  exact (continuous_truncX hP h0).add (continuous_truncY hP h0)

/-- **`ζ ≤ t ↔ n_t = 0`**: the extinction event before `t` is read off the state at `t`. -/
theorem dualExtinction_le_iff {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}
    (hP : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (h0 : N 0 ω = 1) (t : ℝ) :
    dualExtinction N ω ≤ ENNReal.ofReal t ↔ N t.toNNReal ω = 0 := by
  have hT : ENNReal.ofReal t = ((t.toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hT]
  constructor
  · intro hle
    by_contra hne
    have h1 : N t.toNNReal ω = 1 :=
      (level_eq_one_or_zero hP h0 t.toNNReal).resolve_right hne
    obtain ⟨u, hu, hnu⟩ := exists_gt_level_one hP h1
    have hge : (u : ℝ≥0∞) ≤ dualExtinction N ω := by
      refine le_iInf₂ fun s hs => ?_
      by_contra hsu
      have hsu' : s < u := by exact_mod_cast not_le.1 hsu
      have : N s ω = 1 := level_one_of_le hP h0 hsu'.le hnu
      omega
    have : (u : ℝ≥0∞) ≤ (t.toNNReal : ℝ≥0∞) := hge.trans hle
    exact absurd (ENNReal.coe_le_coe.1 this) (not_le.2 hu)
  · intro h
    exact iInf₂_le t.toNNReal h

/-- The truncated state path is right-continuous at every time (product topology). -/
theorem continuousWithinAt_truncDualState {Ω : Type*} {N : ℝ≥0 → Ω → ℕ}
    {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}
    (hP : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (h0 : N 0 ω = 1) (t : ℝ≥0) :
    ContinuousWithinAt (fun s => truncDualState N X Y ω s) (Ici t) t := by
  have hn : ContinuousWithinAt (fun s => N s ω) (Ici t) t := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    exact tendsto_const_nhds.congr' ((hP.rightCont t).mono fun u hu => hu.symm)
  have hc : ∀ (c : ℝ≥0 → Ω → ℕ → ℝ), Continuous (fun s => truncDualCoord (N s ω) (c s ω) 0) →
      ContinuousWithinAt (fun s => truncDualCoord (N s ω) (c s ω)) (Ici t) t := by
    intro c hc0
    refine continuousWithinAt_pi.2 fun i => ?_
    by_cases hi : i = 0
    · subst hi; exact hc0.continuousWithinAt
    · have : (fun s => truncDualCoord (N s ω) (c s ω) i) = fun _ => 0 := by
        funext s
        rw [truncDualCoord_level hP h0 (fun s => c s ω) s i]
        simp [hi]
      rw [this]; exact continuousWithinAt_const
  exact hn.prodMk ((hc X (continuous_truncX hP h0)).prodMk (hc Y (continuous_truncY hP h0)))

end BlockBand.Transmission.DualBoundary
