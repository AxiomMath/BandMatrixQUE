module

public import BlockBand.Transmission.Dual.UniquePad
public import BlockBand.Transmission.Dual.TestProc

/-!
# Uniqueness in law: pathwise facts for the shift at a deletion

* `levelOf`, `unpad`, `unpad_padState`: the truncated state is a measurable function of the
  front-padded state (the level is the number of nonzero `x`-entries, by positivity).
* `isDeletionPath_shift`: a deletion path, shifted by `r` and truncated, is a deletion path.
* `dualMartingale_shift`: if `r ≤ σ_q` (before `r` the path has not entered the levels `≤ q`), the
  level-`q` martingale of the shifted path is `M_{r+s} − M_r`, and `M_r = 0`. This is the shift
  invariance of the lower-level martingale clauses.
* `dualMartingale_empty`: the empty path has zero level-`q` martingales (`q ≥ 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable {p : ℕ}

/-!
## The level read off the padded state
-/

/-- The number of nonzero `x`-entries of a flat state. -/
def levelOf (p : ℕ) (w : Fin (p + p) → ℝ) : ℕ :=
  (Finset.univ.filter fun j : Fin p => (ofFlat p w).1 j ≠ 0).card

/-- The truncated state of a padded flat state. -/
def unpad (p : ℕ) (w : Fin (p + p) → ℝ) : DualState := unpadAt p (levelOf p w) w

theorem card_filter_le_val (c : ℕ) :
    (Finset.univ.filter fun j : Fin p => c ≤ (j : ℕ)).card = p - min p c := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p)))
    (fun j => (j : ℕ) < c)
  rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at h
  have e : (Finset.univ.filter fun j : Fin p => c ≤ (j : ℕ)) =
      Finset.univ.filter fun j : Fin p => ¬ (j : ℕ) < c := by
    ext j; simp
  rw [e]; omega

theorem levelOf_padState {n : ℕ} {x y : ℕ → ℝ} (hn : n ≤ p)
    (hc : dualCoordOf n x y ∈ dualChamber n) : levelOf p (padState p n x y) = n := by
  have e : (Finset.univ.filter fun j : Fin p => (ofFlat p (padState p n x y)).1 j ≠ 0) =
      Finset.univ.filter fun j : Fin p => p - n ≤ (j : ℕ) := by
    ext j
    simp only [ofFlat_padState, padX, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : p - n ≤ (j : ℕ)
    · simp only [hj, ↓reduceIte, iff_true]
      exact (hc.2.2.1 ⟨(j : ℕ) - (p - n), by omega⟩).ne'
    · simp only [hj, ↓reduceIte]
      exact ⟨fun h => absurd rfl h, fun h => h.elim⟩
  rw [levelOf, e, card_filter_le_val]; omega

theorem measurable_levelOf : Measurable (levelOf p) := by
  have hm : ∀ j : Fin p, MeasurableSet {w : Fin (p + p) → ℝ | (ofFlat p w).1 j ≠ 0} := fun j =>
    (measurableSet_singleton (0 : ℝ)).compl.preimage
      ((continuous_apply j).comp (continuous_fst.comp (ofFlat p).continuous)).measurable
  have e : levelOf p = (fun c : Fin p → Bool => (Finset.univ.filter fun j => c j = true).card) ∘
      (fun w j => if (ofFlat p w).1 j ≠ 0 then true else false) := by
    funext w
    simp only [levelOf, Function.comp_apply]
    congr 1; ext j; by_cases h : (ofFlat p w).1 j = 0 <;> simp [h]
  rw [e]
  exact (measurable_of_countable _).comp
    (measurable_pi_iff.2 fun j => Measurable.ite (hm j) measurable_const measurable_const)

theorem measurable_unpad : Measurable (unpad p) := by
  have e : unpad p = (fun z : (Fin (p + p) → ℝ) × ℕ => unpadAt p z.2 z.1) ∘
      fun w => (w, levelOf p w) := rfl
  rw [e]
  exact (measurable_from_prod_countable_left fun n => measurable_unpadAt n).comp
    (measurable_id.prodMk measurable_levelOf)

theorem unpad_padState {n : ℕ} {x y : ℕ → ℝ} (hn : n ≤ p)
    (hc : dualCoordOf n x y ∈ dualChamber n) :
    unpad p (padState p n x y) = (n, truncCoord n x, truncCoord n y) := by
  rw [unpad, levelOf_padState hn hc, unpadAt_padState hn]

/-!
## Shifted deletion paths
-/

section Shift

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ}

theorem tendsto_add_nhdsGT (r t : ℝ≥0) : Tendsto (r + ·) (𝓝[>] t) (𝓝[>] (r + t)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (((continuous_const.add continuous_id : Continuous fun u : ℝ≥0 => r + u).tendsto t).mono_left
      nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun _u hu => (add_lt_add_iff_left r).2 hu)

theorem tendsto_add_nhdsLT (r t : ℝ≥0) : Tendsto (r + ·) (𝓝[<] t) (𝓝[<] (r + t)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (((continuous_const.add continuous_id : Continuous fun u : ℝ≥0 => r + u).tendsto t).mono_left
      nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun _u hu => (add_lt_add_iff_left r).2 hu)

theorem dualCoordOf_trunc (k : ℕ) (x y : ℕ → ℝ) :
    dualCoordOf k (truncCoord k x) (truncCoord k y) = dualCoordOf k x y := by
  ext i <;> simp [dualCoordOf, truncCoord_of_lt _ i.2]

theorem dualLift_trunc {q : ℕ} (f : DualCoord q → ℝ) (k : ℕ) (x y : ℕ → ℝ) :
    dualLift f k (truncCoord k x) (truncCoord k y) = dualLift f k x y := by
  unfold dualLift
  split_ifs with h
  · subst h; rw [dualCoordOf_trunc]
  · rfl

/-- **A shifted, truncated deletion path is a deletion path.** -/
theorem isDeletionPath_shift (hP : IsDeletionPath n x y) (r : ℝ≥0) :
    IsDeletionPath (fun s => n (r + s)) (fun s => truncCoord (n (r + s)) (x (r + s)))
      (fun s => truncCoord (n (r + s)) (y (r + s))) where
  antitone _ _ h := hP.antitone ((add_le_add_iff_left r).2 h)
  chamber t := by
    show dualCoordOf _ (truncCoord _ _) (truncCoord _ _) ∈ _
    rw [dualCoordOf_trunc]; exact hP.chamber (r + t)
  rightCont t := (tendsto_add_nhdsGT r t).eventually (hP.rightCont (r + t))
  cont t₁ t₂ h12 he i hi := by
    have hconst : ∀ u ∈ Icc t₁ t₂, n (r + u) = n (r + t₁) := fun u hu =>
      le_antisymm (hP.antitone ((add_le_add_iff_left r).2 hu.1))
        (he ▸ hP.antitone ((add_le_add_iff_left r).2 hu.2))
    obtain ⟨hcx, hcy⟩ := hP.cont (r + t₁) (r + t₂) ((add_le_add_iff_left r).2 h12) he i hi
    have hmaps : MapsTo (r + ·) (Icc t₁ t₂) (Icc (r + t₁) (r + t₂)) := fun u hu =>
      ⟨(add_le_add_iff_left r).2 hu.1, (add_le_add_iff_left r).2 hu.2⟩
    have hc : ContinuousOn (r + ·) (Icc t₁ t₂) := (continuous_const.add continuous_id).continuousOn
    refine ⟨(hcx.comp hc hmaps).congr fun u hu => ?_, (hcy.comp hc hmaps).congr fun u hu => ?_⟩
    · simp only [Function.comp_apply]; rw [hconst u hu, truncCoord_of_lt _ hi]
    · simp only [Function.comp_apply]; rw [hconst u hu, truncCoord_of_lt _ hi]
  deletion τ hτ q hev hne := by
    obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hτ).1 hev
    have hev' : ∀ᶠ u in 𝓝[<] (r + τ), n u = q + 1 := by
      have hlt : r + a < r + τ := (add_lt_add_iff_left r).2 ha
      filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
      have hru : r ≤ u := le_trans (le_add_right le_rfl) hu.1.le
      have := hsub (show u - r ∈ Ioo a τ from ⟨lt_tsub_iff_left.2 hu.1,
        (tsub_lt_iff_left hru).2 hu.2⟩)
      simpa [add_tsub_cancel_of_le hru] using this
    obtain ⟨h1, hx0, hy0, hs⟩ := hP.deletion (r + τ) (by positivity) q hev' hne
    have hev2 : ∀ᶠ u in 𝓝[<] τ, n (r + u) = q + 1 := hev
    refine ⟨h1, ?_, ?_, fun i hi => ?_⟩
    · refine ((hx0.comp (tendsto_add_nhdsLT r τ))).congr' ?_
      filter_upwards [hev2] with u hu
      simp only [Function.comp_apply]; rw [hu, truncCoord_of_lt _ (Nat.succ_pos q)]
    · refine ((hy0.comp (tendsto_add_nhdsLT r τ))).congr' ?_
      filter_upwards [hev2] with u hu
      simp only [Function.comp_apply]; rw [hu, truncCoord_of_lt _ (Nat.succ_pos q)]
    · obtain ⟨hxs, hys⟩ := hs i hi
      have hi' : i < n (r + τ) := h1 ▸ hi
      rw [truncCoord_of_lt _ hi', truncCoord_of_lt _ hi']
      refine ⟨(hxs.comp (tendsto_add_nhdsLT r τ)).congr' ?_,
        (hys.comp (tendsto_add_nhdsLT r τ)).congr' ?_⟩ <;>
      · filter_upwards [hev2] with u hu
        simp only [Function.comp_apply]; rw [hu, truncCoord_of_lt _ (by omega)]

end Shift

/-!
## The level-`q` martingale after a shift
-/

theorem withTop_eq_of_le_iff {a b : WithTop ℝ≥0} (h : ∀ t : ℝ≥0, a ≤ t ↔ b ≤ t) : a = b := by
  induction b using WithTop.recTopCoe with
  | top =>
    induction a using WithTop.recTopCoe with
    | top => rfl
    | coe a => exact absurd ((h a).1 le_rfl) (not_le.2 (WithTop.coe_lt_top a))
  | coe b =>
    obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top
      ((h b).2 le_rfl))
    exact le_antisymm ((h b).2 le_rfl) (by exact_mod_cast (WithTop.coe_le_coe.1 ((h a).1 le_rfl)))

/-- `∫_{(0,s]} G(r+u) du = ∫_{(0,r+s]} G − ∫_{(0,r]} G` for bounded right-continuous `G`. -/
theorem setIntegral_Ioc_shift {G : ℝ≥0 → ℝ} (hG : ∀ t, Tendsto G (𝓝[≥] t) (𝓝 (G t)))
    {C : ℝ} (hC : ∀ t, ‖G t‖ ≤ C) (r s : ℝ≥0) :
    ∫ u in Ioc (0 : ℝ) s, G (r + u.toNNReal) =
      (∫ u in Ioc (0 : ℝ) (r + s : ℝ≥0), G u.toNNReal) - ∫ u in Ioc (0 : ℝ) r, G u.toNNReal := by
  have hm : Measurable fun u : ℝ => G u.toNNReal :=
    (measurable_of_tendsto_nhdsGE hG).comp measurable_real_toNNReal
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => G u.toNNReal) volume a b := by
    intro a b
    refine ⟨?_, ?_⟩ <;>
    · refine Measure.integrableOn_of_bounded (M := C) (by simp) hm.aestronglyMeasurable ?_
      exact Eventually.of_forall fun u => hC _
  rw [← intervalIntegral.integral_of_le (NNReal.coe_nonneg s),
    ← intervalIntegral.integral_of_le (NNReal.coe_nonneg _),
    ← intervalIntegral.integral_of_le (NNReal.coe_nonneg r),
    intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  have e : ∫ u in (0 : ℝ)..s, G (r + u.toNNReal) = ∫ u in (0 : ℝ)..s, G ((r : ℝ) + u).toNNReal := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by
      rw [uIcc_of_le (NNReal.coe_nonneg s)] at hu; exact hu.1
    rw [Real.toNNReal_add (NNReal.coe_nonneg r) hu0, Real.toNNReal_coe]
  rw [e, intervalIntegral.integral_comp_add_left (fun v : ℝ => G v.toNNReal) (r : ℝ)]
  simp

section Mart

variable {Ω Ω' : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}
  {q : ℕ} {D0 : ℝ} {f : DualCoord q → ℝ}

theorem dualMartingale_empty (hq : 1 ≤ q) {N' : ℝ≥0 → Ω' → ℕ} {X' Y' : ℝ≥0 → Ω' → ℕ → ℝ}
    {ω' : Ω'} (hN : ∀ s, N' s ω' = 0) (t : ℝ≥0) : dualMartingale D0 q f N' X' Y' t ω' = 0 := by
  have h0 : (0 : ℕ) ≠ q := by omega
  simp [dualMartingale, dualEntranceValue, dualLift, hN, h0]

theorem dualEntranceValue_eq_zero_of_lt
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < entryTime (fun t => N t ω) q) :
    dualEntranceValue f N X Y t ω = 0 := by
  have : ¬ ∃ u ≤ t, N u ω ≤ q := fun ⟨u, hut, hu⟩ =>
    absurd (((entryTime_le_iff hP q u).2 hu).trans (WithTop.coe_le_coe.2 hut)) (not_le.2 ht)
  simp only [dualEntranceValue, this, ↓reduceIte]

/-- Before the entrance into the levels `≤ q`, the level-`q` martingale vanishes. -/
theorem dualMartingale_eq_zero_of_le_entry
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) {r : ℝ≥0}
    (hr : (r : WithTop ℝ≥0) ≤ entryTime (fun t => N t ω) q) :
    dualMartingale D0 q f N X Y r ω = 0 := by
  have hint : ∫ u in Ioc (0 : ℝ) r, dualLift (dualGenerator D0 f) (N u.toNNReal ω)
      (X u.toNNReal ω) (Y u.toNNReal ω) = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    have hlt : ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) < entryTime (fun t => N t ω) q := by
      refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) hr
      exact (Real.toNNReal_lt_iff_lt_coe hu.1.le).2 hu.2
    have := lt_level_of_lt_entryTime hP hlt
    simp only [dualLift, show N u.toNNReal ω ≠ q by omega, ↓reduceIte]
  rw [dualMartingale, hint, sub_zero, sub_eq_zero]
  rcases eq_or_lt_of_le hr with h | h
  · rw [dualEntranceValue_eq_of_entryTime hP f h.symm r]; simp
  · rw [dualEntranceValue_eq_zero_of_lt hP h]
    have := lt_level_of_lt_entryTime hP h
    simp only [dualLift, show N r ω ≠ q by omega, ↓reduceIte]

/-- **Shift invariance of the level-`q` clause**: if `r ≤ σ_q`, the level-`q` martingale of the
path shifted by `r` (and truncated) is `M_{r+s} − M_r = M_{r+s}`. -/
theorem dualMartingale_shift
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ dualChamber q)
    {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) ≤ entryTime (fun t => N t ω) q)
    {N' : ℝ≥0 → Ω' → ℕ} {X' Y' : ℝ≥0 → Ω' → ℕ → ℝ} {ω' : Ω'}
    (hN' : ∀ s, N' s ω' = N (r + s) ω)
    (hX' : ∀ s, X' s ω' = truncCoord (N (r + s) ω) (X (r + s) ω))
    (hY' : ∀ s, Y' s ω' = truncCoord (N (r + s) ω) (Y (r + s) ω)) (s : ℝ≥0) :
    dualMartingale D0 q f N' X' Y' s ω' =
      dualMartingale D0 q f N X Y (r + s) ω - dualMartingale D0 q f N X Y r ω := by
  rw [dualMartingale_eq_zero_of_le_entry hP hr, sub_zero]
  have hlift : ∀ (F : DualCoord q → ℝ) (u : ℝ≥0),
      dualLift F (N' u ω') (X' u ω') (Y' u ω') = dualLift F (N (r + u) ω) (X (r + u) ω)
        (Y (r + u) ω) := fun F u => by rw [hN', hX', hY', dualLift_trunc]
  have hgen := continuous_dualGenerator D0 hf hfs
  obtain ⟨C, hC⟩ := hgen.bounded_above_of_compact_support (hasCompactSupport_dualGenerator D0 hfc)
  have hsh := setIntegral_Ioc_shift (G := fun u => dualLift (dualGenerator D0 f) (N u ω) (X u ω)
    (Y u ω)) (tendsto_lift_right hP hgen) (fun _ => norm_dualLift_le hC _ _ _) r s
  have hint0 : ∫ u in Ioc (0 : ℝ) r, dualLift (dualGenerator D0 f) (N u.toNNReal ω)
      (X u.toNNReal ω) (Y u.toNNReal ω) = 0 := by
    have h0 := dualMartingale_eq_zero_of_le_entry (D0 := D0) (f := f) hP hr
    rcases eq_or_lt_of_le hr with h | h
    · rw [dualMartingale, dualEntranceValue_eq_of_entryTime hP f h.symm r] at h0; simpa using h0
    · rw [dualMartingale, dualEntranceValue_eq_zero_of_lt hP h] at h0
      have := lt_level_of_lt_entryTime hP h
      simpa [dualLift, show N r ω ≠ q by omega] using h0
  -- the entrance values agree
  have hP' : IsDeletionPath (fun t => N' t ω') (fun t => X' t ω') (fun t => Y' t ω') := by
    have e1 : (fun t => N' t ω') = fun t => N (r + t) ω := funext hN'
    have e2 : (fun t => X' t ω') = fun t => truncCoord (N (r + t) ω) (X (r + t) ω) := funext hX'
    have e3 : (fun t => Y' t ω') = fun t => truncCoord (N (r + t) ω) (Y (r + t) ω) := funext hY'
    rw [e1, e2, e3]; exact isDeletionPath_shift hP r
  have hEV : dualEntranceValue f N' X' Y' s ω' = dualEntranceValue f N X Y (r + s) ω := by
    induction he : entryTime (fun t => N t ω) q using WithTop.recTopCoe with
    | top =>
      rw [dualEntranceValue_eq_zero_of_lt hP (by rw [he]; exact WithTop.coe_lt_top _)]
      have : ¬ ∃ u ≤ s, N' u ω' ≤ q := fun ⟨u, _, hu⟩ => by
        rw [hN'] at hu
        have := (entryTime_le_iff hP q (r + u)).2 hu
        rw [he] at this; exact absurd this (not_le.2 (WithTop.coe_lt_top _))
      simp only [dualEntranceValue, this, ↓reduceIte]
    | coe e =>
      have hre : r ≤ e := by rw [he] at hr; exact_mod_cast hr
      have he' : entryTime (fun t => N' t ω') q = ((e - r : ℝ≥0) : WithTop ℝ≥0) := by
        refine withTop_eq_of_le_iff fun t => ?_
        rw [entryTime_le_iff hP' q t, hN', ← entryTime_le_iff hP q (r + t), he,
          WithTop.coe_le_coe, WithTop.coe_le_coe, tsub_le_iff_left]
      rw [dualEntranceValue_eq_of_entryTime hP' f he' s, dualEntranceValue_eq_of_entryTime hP f he,
        hlift, add_tsub_cancel_of_le hre]
      congr 1
      exact propext ⟨fun h => by rw [← add_tsub_cancel_of_le hre]; exact (add_le_add_iff_left r).2 h,
        fun h => tsub_le_iff_left.2 h⟩
  rw [dualMartingale, dualMartingale, hEV, hlift]
  congr 1
  rw [show (∫ u in Ioc (0 : ℝ) s, dualLift (dualGenerator D0 f) (N' u.toNNReal ω')
      (X' u.toNNReal ω') (Y' u.toNNReal ω')) = ∫ u in Ioc (0 : ℝ) s,
      dualLift (dualGenerator D0 f) (N (r + u.toNNReal) ω) (X (r + u.toNNReal) ω)
        (Y (r + u.toNNReal) ω) from by simp only [hlift]]
  rw [hsh, hint0, sub_zero]

end Mart

end BlockBand.Transmission.Dual
