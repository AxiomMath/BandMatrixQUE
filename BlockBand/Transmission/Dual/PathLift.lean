module

public import BlockBand.Transmission.Dual.Path
public import BlockBand.Transmission.Dual.Generator
public import BlockBand.Transmission.Dual.Hitting

/-!
# Lifted tests along a deletion path; continuity of `dualMartingale`

For a test `F` on `DualCoord q` that is continuous and vanishes off `𝒞_q` (`q ≥ 1`), along a
deletion path:
* `tendsto_lift_right`: `u ↦ dualLift F (n_u) (x_u) (y_u)` is right-continuous;
* `tendsto_lift_left`: its left limit at `t` is its value if the level does not jump at `t`,
  and `0` at a jump (the deleted pair tends to the corner `cornerOf`, outside `𝒞_q`);
* `entryTime_eq_of_jump_into`, `ne_of_entryTime_eq`: a jump lands in level `q` exactly at the
  entrance time `σ_q`;
* **`continuous_dualMartingale`**: for `f ∈ C²` with compact support in `𝒞_q`, every path of
  `dualMartingale D₀ q f` along a deletion path is continuous (the jump of
  `f(Z)1{N=q}` at `σ_q` is cancelled by the entrance term).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable {q : ℕ}

/-- The paired corner `(0, x₀, …, x_{q-2}; 0, y₀, …, y_{q-2})` in `DualCoord q`. -/
def cornerOf (q : ℕ) (x y : ℕ → ℝ) : DualCoord q :=
  (fun i => if (i : ℕ) = 0 then 0 else x ((i : ℕ) - 1),
    fun i => if (i : ℕ) = 0 then 0 else y ((i : ℕ) - 1))

theorem cornerOf_notMem (hq : 1 ≤ q) (x y : ℕ → ℝ) : cornerOf q x y ∉ dualChamber q := by
  intro h
  have := h.2.2.1 ⟨0, hq⟩
  simp [cornerOf] at this

section PathLemmas

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ}

theorem tendsto_lift_right (hP : IsDeletionPath n x y) {F : DualCoord q → ℝ}
    (hF : Continuous F) (t : ℝ≥0) :
    Tendsto (fun u => dualLift F (n u) (x u) (y u)) (𝓝[≥] t)
      (𝓝 (dualLift F (n t) (x t) (y t))) := by
  obtain ⟨b, hb, hlev⟩ := exists_right_level hP t
  have hev : ∀ᶠ u in 𝓝[≥] t, n u = n t := mem_of_superset (Ico_mem_nhdsGE hb) hlev
  by_cases h : n t = q
  · have hc : Tendsto (fun u => dualCoordOf q (x u) (y u)) (𝓝[≥] t)
        (𝓝 (dualCoordOf q (x t) (y t))) := by
      refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun i => ?_) (tendsto_pi_nhds.2 fun i => ?_)
      · exact (tendsto_coord_right hP t (by rw [h]; exact i.2)).1
      · exact (tendsto_coord_right hP t (by rw [h]; exact i.2)).2
    have e : dualLift F (n t) (x t) (y t) = F (dualCoordOf q (x t) (y t)) := by
      simp [dualLift, h]
    rw [e]
    refine ((hF.tendsto _).comp hc).congr' ?_
    filter_upwards [hev] with u hu
    simp [dualLift, hu, h]
  · have e : dualLift F (n t) (x t) (y t) = 0 := by simp [dualLift, h]
    rw [e]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with u hu
    simp [dualLift, hu, h]

theorem tendsto_lift_left (hP : IsDeletionPath n x y) {F : DualCoord q → ℝ}
    (hF : Continuous F) (hF0 : ∀ z ∉ dualChamber q, F z = 0) (hq : 1 ≤ q) {t u₀ : ℝ≥0}
    (hu₀ : u₀ < t) {k : ℕ} (hk : ∀ u ∈ Ico u₀ t, n u = k) :
    Tendsto (fun u => dualLift F (n u) (x u) (y u)) (𝓝[<] t)
      (𝓝 (if k = n t then dualLift F (n t) (x t) (y t) else 0)) := by
  have hev : ∀ᶠ u in 𝓝[<] t, n u = k :=
    mem_of_superset (Ioo_mem_nhdsLT hu₀) fun u hu => hk u ⟨hu.1.le, hu.2⟩
  by_cases hkt : k = n t
  · subst hkt
    simp only [↓reduceIte]
    by_cases h : n t = q
    · have hc : Tendsto (fun u => dualCoordOf q (x u) (y u)) (𝓝[<] t)
          (𝓝 (dualCoordOf q (x t) (y t))) := by
        refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun i => ?_)
          (tendsto_pi_nhds.2 fun i => ?_)
        · exact (tendsto_coord_left_same hP hu₀ hk (by rw [h]; exact i.2)).1
        · exact (tendsto_coord_left_same hP hu₀ hk (by rw [h]; exact i.2)).2
      have e : dualLift F (n t) (x t) (y t) = F (dualCoordOf q (x t) (y t)) := by
        simp [dualLift, h]
      rw [e]
      refine ((hF.tendsto _).comp hc).congr' ?_
      filter_upwards [hev] with u hu
      simp [dualLift, hu, h]
    · have e : dualLift F (n t) (x t) (y t) = 0 := by simp [dualLift, h]
      rw [e]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with u hu
      simp [dualLift, hu, h]
  · obtain ⟨hk1, hx0, hy0, hrest⟩ := left_jump hP hu₀ hk hkt
    simp only [hkt, ↓reduceIte]
    by_cases h : k = q
    · have hc : Tendsto (fun u => dualCoordOf q (x u) (y u)) (𝓝[<] t)
          (𝓝 (cornerOf q (x t) (y t))) := by
        refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun i => ?_)
          (tendsto_pi_nhds.2 fun i => ?_)
        · show Tendsto (fun u => x u (i : ℕ)) _
            (𝓝 (if (i : ℕ) = 0 then 0 else x t ((i : ℕ) - 1)))
          rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
          · rw [h0]; simpa using hx0
          · obtain ⟨j, hj⟩ : ∃ j, (i : ℕ) = j + 1 := ⟨(i : ℕ) - 1, by omega⟩
            rw [hj]
            simpa using (hrest j (by have := i.2; omega)).1
        · show Tendsto (fun u => y u (i : ℕ)) _
            (𝓝 (if (i : ℕ) = 0 then 0 else y t ((i : ℕ) - 1)))
          rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
          · rw [h0]; simpa using hy0
          · obtain ⟨j, hj⟩ : ∃ j, (i : ℕ) = j + 1 := ⟨(i : ℕ) - 1, by omega⟩
            rw [hj]
            simpa using (hrest j (by have := i.2; omega)).2
      have e : F (cornerOf q (x t) (y t)) = 0 := hF0 _ (cornerOf_notMem hq _ _)
      rw [← e]
      refine ((hF.tendsto _).comp hc).congr' ?_
      filter_upwards [hev] with u hu
      simp [dualLift, hu, h]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with u hu
      simp [dualLift, hu, h]

/-- A jump landing in level `q` happens exactly at the entrance time `σ_q`. -/
theorem entryTime_eq_of_jump_into (hP : IsDeletionPath n x y) {t u₀ : ℝ≥0} (hu₀ : u₀ < t)
    {k : ℕ} (hk : ∀ u ∈ Ico u₀ t, n u = k) (hkt : k ≠ n t) (hq : n t = q) :
    entryTime n q = t := by
  have hk1 := (left_jump hP hu₀ hk hkt).1
  refine le_antisymm ((entryTime_le_iff hP q t).2 hq.le) (le_iInf₂ fun u hu => ?_)
  rw [WithTop.coe_le_coe]
  by_contra hut'
  have hut : u < t := not_le.1 hut'
  rcases le_or_gt u₀ u with h | h
  · have := hk u ⟨h, hut⟩; omega
  · have h1 := hP.antitone h.le
    have := hk u₀ ⟨le_rfl, hu₀⟩
    omega

/-- At the entrance time `σ_q = t > 0` the level jumps. -/
theorem ne_of_entryTime_eq (hP : IsDeletionPath n x y) {t u₀ : ℝ≥0} (hu₀ : u₀ < t)
    {k : ℕ} (hk : ∀ u ∈ Ico u₀ t, n u = k) (hs : entryTime n q = t) : k ≠ n t := by
  have h1 : q < n u₀ := lt_level_of_lt_entryTime hP (by rw [hs]; exact WithTop.coe_lt_coe.2 hu₀)
  have h2 : n t ≤ q := (entryTime_le_iff hP q t).1 hs.le
  rw [← hk u₀ ⟨le_rfl, hu₀⟩]
  omega

end PathLemmas

theorem nhdsLT_zero_nnreal : 𝓝[<] (0 : ℝ≥0) = ⊥ := by
  have : Iio (0 : ℝ≥0) = ∅ := Set.eq_empty_iff_forall_notMem.2 fun u hu =>
    absurd hu (not_lt.2 (zero_le : (0 : ℝ≥0) ≤ u))
  rw [this, nhdsWithin_empty]

/-- `‖dualLift F‖ ≤ C` when `‖F‖ ≤ C`. -/
theorem norm_dualLift_le {F : DualCoord q → ℝ} {C : ℝ} (hC : ∀ z, ‖F z‖ ≤ C) (k : ℕ)
    (x y : ℕ → ℝ) : ‖dualLift F k x y‖ ≤ C := by
  unfold dualLift
  split_ifs
  · exact hC _
  · simpa using (norm_nonneg _).trans (hC 0)

/-- **Paths of `dualMartingale` are continuous** along a deletion path. -/
theorem continuous_dualMartingale {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    {ω : Ω} (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (D0 : ℝ) (hq : 1 ≤ q) {f : DualCoord q → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ dualChamber q) :
    Continuous fun t => dualMartingale D0 q f N X Y t ω := by
  set n : ℝ≥0 → ℕ := fun t => N t ω
  have hf0 : ∀ z ∉ dualChamber q, f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hfs h)
  -- the integral term
  have hgen := continuous_dualGenerator D0 hf hfs
  obtain ⟨C, hC⟩ := hgen.bounded_above_of_compact_support (hasCompactSupport_dualGenerator D0 hfc)
  have hint := continuous_setIntegral_Ioc (G := fun u => dualLift (dualGenerator D0 f) (N u ω)
    (X u ω) (Y u ω)) (tendsto_lift_right hP hgen) (fun _ => norm_dualLift_le hC _ _ _)
  -- the lift minus the entrance value
  have hφ : Continuous fun t => dualLift f (N t ω) (X t ω) (Y t ω) -
      dualEntranceValue f N X Y t ω := by
    by_cases hE : ∃ u, N u ω ≤ q
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ((entryTime_lt_top_iff (n := n) q).2 hE).ne
      have hs' : entryTime n q = s := hs.symm
      have hσ : dualEntrance N q ω = s := by
        refine IsLeast.csInf_eq ⟨(entryTime_le_iff hP q s).1 hs'.le, fun u hu => ?_⟩
        exact WithTop.coe_le_coe.1 (hs' ▸ (entryTime_le_iff hP q u).2 hu)
      set c := dualLift f (N s ω) (X s ω) (Y s ω)
      have hent : ∀ t, dualEntranceValue f N X Y t ω = if s ≤ t then c else 0 := by
        intro t
        have hiff : (∃ u ≤ t, N u ω ≤ q) ↔ s ≤ t := by
          rw [← WithTop.coe_le_coe, ← hs', entryTime_le_iff hP q t]
          exact ⟨fun ⟨u, hut, hu⟩ => (hP.antitone hut).trans hu, fun h => ⟨t, le_rfl, h⟩⟩
        by_cases hst : s ≤ t
        · simp only [dualEntranceValue, hiff.2 hst, ↓reduceIte, hσ, hst, c]
        · simp only [dualEntranceValue, mt hiff.1 hst, ↓reduceIte, hst]
      refine continuous_iff_continuousAt.2 fun t => ?_
      simp only [ContinuousAt, hent]
      rw [← nhdsLT_sup_nhdsGE]
      refine Tendsto.sup ?_ ?_
      · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | htpos
        · rw [← h0, nhdsLT_zero_nnreal]; exact tendsto_bot
        obtain ⟨k, u₀, hu₀, hk⟩ := exists_left_level hP.antitone htpos
        have hL := tendsto_lift_left hP hf.continuous hf0 hq hu₀ hk
        rcases lt_trichotomy s t with hst | hst | hst
        · -- entrance constant `c` near `t` on the left
          have hlift : (if k = n t then dualLift f (N t ω) (X t ω) (Y t ω) else 0) =
              dualLift f (N t ω) (X t ω) (Y t ω) := by
            by_cases hkt : k = n t
            · simp [hkt]
            · have hnq : n t ≠ q := fun h =>
                absurd (entryTime_eq_of_jump_into hP hu₀ hk hkt h) (by
                  rw [hs']; exact fun e => hst.ne (WithTop.coe_injective e))
              simp [hkt, dualLift, n, hnq]
          rw [hlift] at hL
          refine (hL.sub (tendsto_const_nhds (x := c))).congr' ?_ |>.trans (by simp [hst.le])
          filter_upwards [Ioo_mem_nhdsLT hst] with u hu
          simp [hu.1.le, n]
        · -- `t = σ_q`: both sides tend to `0`
          subst hst
          have hkt := ne_of_entryTime_eq hP hu₀ hk hs'
          simp only [hkt, ↓reduceIte] at hL
          have : dualLift f (N s ω) (X s ω) (Y s ω) - (if s ≤ s then c else 0) = 0 := by
            simp [c]
          rw [this]
          refine (hL.sub (tendsto_const_nhds (x := (0 : ℝ)))).congr' ?_ |>.trans (by simp)
          filter_upwards [self_mem_nhdsWithin] with u hu
          simp [not_le.2 (show u < s from hu), n]
        · -- entrance `0` near `t` on the left
          have hlift : (if k = n t then dualLift f (N t ω) (X t ω) (Y t ω) else 0) =
              dualLift f (N t ω) (X t ω) (Y t ω) := by
            by_cases hkt : k = n t
            · simp [hkt]
            · have hnq : n t ≠ q := fun h =>
                absurd (entryTime_eq_of_jump_into hP hu₀ hk hkt h) (by
                  rw [hs']; exact fun e => hst.ne' (WithTop.coe_injective e))
              simp [hkt, dualLift, n, hnq]
          rw [hlift] at hL
          refine (hL.sub (tendsto_const_nhds (x := (0 : ℝ)))).congr' ?_ |>.trans
            (by simp [not_le.2 hst])
          filter_upwards [self_mem_nhdsWithin] with u hu
          simp [not_le.2 ((show u < t from hu).trans hst), n]
      · have hR := tendsto_lift_right hP hf.continuous t
        by_cases hst : s ≤ t
        · refine (hR.sub (tendsto_const_nhds (x := c))).congr' ?_ |>.trans (by simp [hst, n])
          filter_upwards [self_mem_nhdsWithin] with u hu
          simp [hst.trans (show t ≤ u from hu), n]
        · refine (hR.sub (tendsto_const_nhds (x := (0 : ℝ)))).congr' ?_ |>.trans
            (by simp [hst, n])
          filter_upwards [Ico_mem_nhdsGE (not_le.1 hst)] with u hu
          simp [not_le.2 hu.2, n]
    · have hzero : ∀ t, dualLift f (N t ω) (X t ω) (Y t ω) - dualEntranceValue f N X Y t ω
          = 0 := by
        intro t
        have h1 : N t ω ≠ q := fun h => hE ⟨t, h.le⟩
        have h2 : ¬ ∃ u ≤ t, N u ω ≤ q := fun ⟨u, _, hu⟩ => hE ⟨u, hu⟩
        simp [dualLift, h1, dualEntranceValue, h2]
      simp only [hzero]
      exact continuous_const
  exact hφ.sub hint

end BlockBand.Transmission.Dual
