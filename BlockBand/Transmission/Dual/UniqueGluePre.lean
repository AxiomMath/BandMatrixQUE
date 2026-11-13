module

public import BlockBand.Transmission.Dual.UniqueShift
public import BlockBand.Transmission.Dual.UniqueStopLaw

/-!
# Uniqueness in law: the pre-deletion path and the gluing approximants

Fix a realization `h : IsDualFrom P 𝓖 D₀ p N X Y`, `p ≥ 1`, and a horizon `T`. Write
`σ = σ_{p−1}`, `c = σ ∧ T` (`cutPt`), `E = {σ ≤ T}`.
* `preP`: the padded state stopped at `c`. It is `𝓖_c`-measurable (`IsDualFrom.measurable_preP`)
  and its law is a function of the law of `V` stopped at `σ` (`IsDualFrom.preP_eq`).
* `postS`: the truncated state path of the post-deletion realization (`IsDualFrom.shift`).
* `exitEst`: a measurable functional of a path with `exitEst (preP ω) = c` on `E`
  (an infimum over dyadic times).
* `glueApprox m`: a measurable functional of `(preP, postS)` that converges, at every `ω` and
  every `t ≤ T`, to the truncated state `dualState N X Y ω t` (`tendsto_glueApprox`; right
  continuity of the truncated state, `tendsto_dualState_right`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime)
open scoped NNReal ENNReal

theorem truncCoord_idem (n : ℕ) (x : ℕ → ℝ) : truncCoord n (truncCoord n x) = truncCoord n x := by
  funext i; unfold truncCoord; split_ifs <;> rfl

/-- Right continuity of the truncated state along a deletion path. -/
theorem tendsto_dualState_right {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ} (hP : IsDeletionPath n x y)
    (t : ℝ≥0) :
    Tendsto (fun u => ((n u, truncCoord (n u) (x u), truncCoord (n u) (y u)) : DualState))
      (𝓝[≥] t) (𝓝 (n t, truncCoord (n t) (x t), truncCoord (n t) (y t))) := by
  obtain ⟨b, hb, hlev⟩ := exists_right_level hP t
  have hev : ∀ᶠ u in 𝓝[≥] t, n u = n t := mem_of_superset (Ico_mem_nhdsGE hb) hlev
  have hc : ∀ (z : ℝ≥0 → ℕ → ℝ), (∀ i, i < n t → Tendsto (fun u => z u i) (𝓝[≥] t) (𝓝 (z t i))) →
      Tendsto (fun u => truncCoord (n u) (z u)) (𝓝[≥] t) (𝓝 (truncCoord (n t) (z t))) :=
    fun z hz => tendsto_pi_nhds.2 fun i => by
      refine Tendsto.congr' (f₁ := fun u => truncCoord (n t) (z u) i) ?_ ?_
      · filter_upwards [hev] with u hu; rw [hu]
      · unfold truncCoord
        split_ifs with hi
        · exact hz i hi
        · exact tendsto_const_nhds
  refine Tendsto.prodMk_nhds (tendsto_const_nhds.congr' (hev.mono fun u hu => hu.symm))
    (Tendsto.prodMk_nhds (hc x fun i hi => (tendsto_coord_right hP t hi).1)
      (hc y fun i hi => (tendsto_coord_right hP t hi).2))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {p : ℕ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- The padded state stopped at `c = σ_{p−1} ∧ T`. -/
def preP (p : ℕ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (T : ℝ≥0) (ω : Ω) :
    ℝ≥0 → Fin (p + p) → ℝ :=
  fun t => padPath p N X Y (min t (cutPt p N T ω)) ω

/-- The truncated state path after the deletion. -/
def postS (p : ℕ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (T : ℝ≥0) (ω : Ω) :
    ℝ≥0 → DualState :=
  dualState (postN p N T) (postC p N T X) (postC p N T Y) ω

omit [MeasurableSpace Ω] in
theorem cutPt_le {T : ℝ≥0} (ω : Ω) : cutPt p N T ω ≤ T := by
  have := cutStop_le (p := p) (N := N) (T := T) ω
  rwa [← coe_untopA_of_ne_top (cutStop_ne_top ω), WithTop.coe_le_coe] at this

theorem IsDualFrom.mem_iff_lt (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) (r : ℝ≥0) (ω : Ω) :
    padPath p N X Y r ω ∈ flatChamber p ↔ (r : WithTop ℝ≥0) < firstDel p N ω := by
  rw [h.padPath_mem_iff, firstDel, ← not_le, entryTime_le_iff (h.paths ω)]
  have := h.level_le r ω; omega

/-- On `E`, `preP ω r ∈ 𝒞_p` iff `r < c`. -/
theorem IsDualFrom.preP_mem_iff (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) {T : ℝ≥0} {ω : Ω}
    (hω : firstDel p N ω ≤ T) (r : ℝ≥0) :
    preP p N X Y T ω r ∈ flatChamber p ↔ r < cutPt p N T ω := by
  rw [preP, h.mem_iff_lt hp, ← coe_cutPt_of_le hω, WithTop.coe_lt_coe, min_lt_iff]
  simp

/-- `{σ ≤ T}` is read off `preP` at time `T`. -/
theorem IsDualFrom.mem_E_iff (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) (T : ℝ≥0) (ω : Ω) :
    firstDel p N ω ≤ T ↔ preP p N X Y T ω T ∉ flatChamber p := by
  rw [preP, min_eq_right (cutPt_le ω), h.mem_iff_lt hp, not_lt]
  constructor
  · intro hω; rw [coe_cutPt_of_le hω]
  · intro hω
    by_contra hc
    have : cutPt p N T ω = T := by
      rw [cutPt, cutStop, min_eq_right (not_le.1 hc).le]; rfl
    rw [this] at hω; exact hc hω

theorem IsDualFrom.dualState_eq_unpadAt (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p)
    {T : ℝ≥0} {ω : Ω} {t : ℝ≥0} (ht : t ≤ T) (hσ : (t : WithTop ℝ≥0) < firstDel p N ω) :
    dualState N X Y ω t = unpadAt p p (preP p N X Y T ω t) := by
  have hN : N t ω = p := by
    have := lt_level_of_lt_entryTime (h.paths ω) hσ; have := h.level_le t ω; omega
  have hct : t ≤ cutPt p N T ω := by
    rw [← WithTop.coe_le_coe, cutPt, coe_untopA_of_ne_top (cutStop_ne_top ω), cutStop]
    exact le_min hσ.le (WithTop.coe_le_coe.2 ht)
  rw [preP, min_eq_left hct, padPath, ← hN, unpadAt_padState le_rfl]
  rfl

omit [MeasurableSpace Ω] in
theorem postS_of_mem {T : ℝ≥0} {ω : Ω} (hω : firstDel p N ω ≤ T) (s : ℝ≥0) :
    postS p N X Y T ω s = dualState N X Y ω (cutPt p N T ω + s) := by
  simp only [postS, dualState, postN, postC, hω, ↓reduceIte, truncCoord_idem]

omit [MeasurableSpace Ω] in
theorem postS_of_notMem {T : ℝ≥0} {ω : Ω} (hω : ¬ firstDel p N ω ≤ T) :
    postS p N X Y T ω = fun _ => ((0, 0, 0) : DualState) := by
  funext s
  simp only [postS, dualState, postN, postC, hω, ↓reduceIte, truncCoord_zero]

theorem IsDualFrom.postS_zero (h : IsDualFrom P 𝓖 D0 p N X Y) {T : ℝ≥0} {ω : Ω}
    (hω : firstDel p N ω ≤ T) : postS p N X Y T ω 0 = unpad p (preP p N X Y T ω T) := by
  rw [postS_of_mem hω, add_zero, preP, min_eq_right (cutPt_le ω), h.unpad_padPath]; rfl

/-- `preP` is a function of `V` stopped at its exit from the flat chamber. -/
theorem IsDualFrom.preP_eq (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) (T : ℝ≥0) (ω : Ω)
    (t : ℝ≥0) : preP p N X Y T ω t = stoppedProcess (padPath p N X Y)
      (exitTimeFrom (flatChamber p) (padPath p N X Y)) (min t T) ω := by
  rw [stoppedProcess_eq_stopTime, h.exitTime_eq hp ω, preP]
  congr 1
  rw [← WithTop.coe_inj, Uniqueness.coe_stopTime, WithTop.coe_min, cutPt,
    coe_untopA_of_ne_top (cutStop_ne_top ω), cutStop, WithTop.coe_min, firstDel]
  rw [min_assoc, min_comm (T : WithTop ℝ≥0), min_comm (t : WithTop ℝ≥0) (min _ _), min_assoc,
    min_comm _ (t : WithTop ℝ≥0)]

theorem IsDualFrom.progressive (h : IsDualFrom P 𝓖 D0 p N X Y) :
    IsStronglyProgressive 𝓖 (padPath p N X Y) :=
  StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => (h.measurable_padPath t).stronglyMeasurable) h.continuous_padPath

/-- `preP` is `𝓖_{σ'}`-measurable. -/
theorem IsDualFrom.measurable_preP (h : IsDualFrom P 𝓖 D0 p N X Y) (T : ℝ≥0) :
    Measurable[postFil h T 0] (preP p N X Y T) := by
  have hτ := isStoppingTime_untopA_add (h.isStoppingTime_cut T) cutStop_ne_top 0
  refine @Measurable.of_eval Ω _ _ (postFil h T 0) _ _ fun t => ?_
  have hm := measurable_stoppedValue h.progressive (hτ.min_const t)
  have e : stoppedValue (padPath p N X Y) (fun ω => min (((cutStop p N T ω).untopA + 0 : ℝ≥0) :
      WithTop ℝ≥0) t) = fun ω => preP p N X Y T ω t := by
    funext ω
    simp only [stoppedValue, add_zero, preP, cutPt, ← WithTop.coe_min, min_comm]
    rfl
  rw [e] at hm
  exact hm.mono (IsStoppingTime.measurableSpace_mono (hτ.min_const t) hτ fun ω => min_le_left _ _)
    le_rfl

/-!
## A measurable exit-time functional and the approximants
-/

/-- Dyadic times `k / 2^m`. -/
def dyad (mk : ℕ × ℕ) : ℝ≥0 := (mk.2 : ℝ≥0) / 2 ^ mk.1

/-- Paths outside the chamber at the dyadic time `mk`, which is `≤ T`. -/
def exitSet (p : ℕ) (T : ℝ≥0) (mk : ℕ × ℕ) : Set (ℝ≥0 → Fin (p + p) → ℝ) :=
  {v | v (dyad mk) ∉ flatChamber p ∧ dyad mk ≤ T}

open scoped Classical in
/-- `inf {d dyadic ≤ T : v d ∉ 𝒞_p}` (and `T` if there is none). -/
def exitEst (p : ℕ) (T : ℝ≥0) (v : ℝ≥0 → Fin (p + p) → ℝ) : ℝ≥0 :=
  ⨅ mk : ℕ × ℕ, if v ∈ exitSet p T mk then dyad mk else T

theorem measurable_exitEst (T : ℝ≥0) : Measurable (exitEst p T) := by
  refine Measurable.iInf fun mk => Measurable.ite ?_ measurable_const measurable_const
  exact ((isOpen_flatChamber p).measurableSet.compl.preimage (measurable_pi_apply _)).inter
    (MeasurableSet.const _)

theorem IsDualFrom.exitEst_preP (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) {T : ℝ≥0} {ω : Ω}
    (hω : firstDel p N ω ≤ T) : exitEst p T (preP p N X Y T ω) = cutPt p N T ω := by
  set c := cutPt p N T ω
  refine le_antisymm ?_ (le_ciInf fun mk => ?_)
  · refine ge_of_tendsto' (f := fun m : ℕ => c + (1 / 2) ^ m) (x := atTop) ?_ fun m => ?_
    · simpa using tendsto_const_nhds.add (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (1 / 2 : ℝ≥0) < 1))
    · refine (ciInf_le (OrderBot.bddBelow _) (m, ⌈c * 2 ^ m⌉₊)).trans ?_
      have hd : dyad (m, ⌈c * 2 ^ m⌉₊) = ceilDyad m c := rfl
      have hnot : preP p N X Y T ω (ceilDyad m c) ∉ flatChamber p := by
        rw [h.preP_mem_iff hp hω, not_lt]; exact le_ceilDyad m c
      split_ifs with hs
      · rw [hd]; exact (ceilDyad_lt m c).le
      · have : ¬ ceilDyad m c ≤ T := fun hT => hs ⟨by rw [hd]; exact hnot, by rw [hd]; exact hT⟩
        exact ((not_le.1 this).trans (ceilDyad_lt m c)).le
  · split_ifs with hs
    · exact not_lt.1 ((h.preP_mem_iff hp hω _).not.1 hs.1)
    · exact cutPt_le ω

open scoped Classical in
/-- The gluing approximant: before the exit read `unpadAt p p` of the stopped path; after it
read the post path at a dyadic time just to the right of `t − exitEst`. -/
def glueApprox (p : ℕ) (T : ℝ≥0) (m : ℕ)
    (z : (ℝ≥0 → Fin (p + p) → ℝ) × (ℝ≥0 → DualState)) (t : ℝ≥0) : DualState :=
  if z.1 t ∈ flatChamber p then unpadAt p p (z.1 t)
  else z.2 (ceilDyad m (t - exitEst p T z.1))

theorem measurable_glueApprox (T : ℝ≥0) (m : ℕ) (t : ℝ≥0) :
    Measurable fun z : (ℝ≥0 → Fin (p + p) → ℝ) × (ℝ≥0 → DualState) => glueApprox p T m z t := by
  have hs : MeasurableSet {z : (ℝ≥0 → Fin (p + p) → ℝ) × (ℝ≥0 → DualState) |
      z.1 t ∈ flatChamber p} :=
    (isOpen_flatChamber p).measurableSet.preimage ((measurable_pi_apply t).comp measurable_fst)
  unfold glueApprox
  refine Measurable.ite hs ((measurable_unpadAt p).comp ((measurable_pi_apply t).comp
    measurable_fst)) ?_
  have e : (fun z : (ℝ≥0 → Fin (p + p) → ℝ) × (ℝ≥0 → DualState) =>
      z.2 (ceilDyad m (t - exitEst p T z.1))) =
      (fun w : (ℝ≥0 → DualState) × ℕ => w.1 ((w.2 : ℝ≥0) / 2 ^ m)) ∘
        fun z => (z.2, ⌈(t - exitEst p T z.1) * 2 ^ m⌉₊) := rfl
  rw [e]
  refine (measurable_from_prod_countable_left fun k =>
    by exact measurable_pi_apply ((k : ℝ≥0) / 2 ^ m)).comp
    (measurable_snd.prodMk (Nat.measurable_ceil.comp ?_))
  exact (measurable_const.sub ((measurable_exitEst T).comp measurable_fst)).mul_const _

theorem tendsto_add_nhdsGE (c a : ℝ≥0) : Tendsto (c + ·) (𝓝[≥] a) (𝓝[≥] (c + a)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (((continuous_const.add continuous_id : Continuous fun u : ℝ≥0 => c + u).tendsto a).mono_left
      nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun _u hu => (add_le_add_iff_left c).2 hu)

/-- **The approximants converge at every `ω`** to the truncated state, for `t ≤ T`. -/
theorem IsDualFrom.tendsto_glueApprox (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) {T : ℝ≥0}
    (ω : Ω) {t : ℝ≥0} (ht : t ≤ T) :
    Tendsto (fun m => glueApprox p T m (preP p N X Y T ω, postS p N X Y T ω) t) atTop
      (𝓝 (dualState N X Y ω t)) := by
  by_cases hσ : (t : WithTop ℝ≥0) < firstDel p N ω
  · have hin : preP p N X Y T ω t ∈ flatChamber p := by
      have hct : t ≤ cutPt p N T ω := by
        rw [← WithTop.coe_le_coe, cutPt, coe_untopA_of_ne_top (cutStop_ne_top ω), cutStop]
        exact le_min hσ.le (WithTop.coe_le_coe.2 ht)
      rw [preP, min_eq_left hct, h.mem_iff_lt hp]; exact hσ
    simp only [glueApprox, hin, ↓reduceIte]
    rw [h.dualState_eq_unpadAt hp ht hσ]
    exact tendsto_const_nhds
  · have hω : firstDel p N ω ≤ T := (not_lt.1 hσ).trans (WithTop.coe_le_coe.2 ht)
    set c := cutPt p N T ω
    have hct : c ≤ t := by
      rw [← WithTop.coe_le_coe, coe_cutPt_of_le hω]; exact not_lt.1 hσ
    have hout : preP p N X Y T ω t ∉ flatChamber p := by
      rw [h.preP_mem_iff hp hω, not_lt]; exact hct
    simp only [glueApprox, hout, ↓reduceIte, h.exitEst_preP hp hω, postS_of_mem hω]
    have hlim : Tendsto (fun m => c + ceilDyad m (t - c)) atTop (𝓝[≥] t) := by
      have := (tendsto_add_nhdsGE c (t - c)).comp (tendsto_ceilDyad (t - c))
      rwa [add_tsub_cancel_of_le hct] at this
    exact (tendsto_dualState_right (h.paths ω) t).comp hlim

end BlockBand.Transmission.Dual
