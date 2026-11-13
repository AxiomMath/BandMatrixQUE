module

public import BlockBand.Transmission.Dual.UniqueShiftMart

/-!
# Uniqueness in law: the post-deletion realization

For a realization `h : IsDualFrom P 𝓖 D₀ p N X Y` (`p ≥ 1`) and a horizon `T`:
* `firstDel p N = σ_{p−1}` (first deletion; `⊤` if none) and `cutStop p N T = σ_{p−1} ∧ T`
  are stopping times (`IsDualFrom.isStoppingTime_entry`, `IsDualFrom.isStoppingTime_cut`);
* `postFil h T = 𝓖_{σ'+·}`, and `E = {σ_{p−1} ≤ T} ∈ 𝓖_{σ'}` (`measurableSet_postE`);
* `postN`, `postC`: the path after `σ'`, truncated, on `E`; the empty path off `E`;
* **`IsDualFrom.shift`**: for `A ⊆ E`, `A ∈ 𝓖_{σ'}`, `P A ≠ 0`, the post path is an
  `IsDualFrom` realization at level `p − 1` under `P[|A]` for `postFil h T`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness (martingale_cond ae_cond_of_ae)
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {p : ℕ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- The first deletion time `σ_{p−1}` (`⊤` if there is none). -/
def firstDel (p : ℕ) (N : ℝ≥0 → Ω → ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  entryTime (fun t => N t ω) (p - 1)

/-- `σ_{p−1} ∧ T`. -/
def cutStop (p : ℕ) (N : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  min (firstDel p N ω) T

omit [MeasurableSpace Ω] in
theorem cutStop_ne_top {T : ℝ≥0} (ω : Ω) : cutStop p N T ω ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)

omit [MeasurableSpace Ω] in
theorem cutStop_le {T : ℝ≥0} (ω : Ω) : cutStop p N T ω ≤ T := min_le_right _ _

/-- The cut time as a real time. -/
def cutPt (p : ℕ) (N : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 := (cutStop p N T ω).untopA

omit [MeasurableSpace Ω] in
theorem coe_cutPt_of_le {T : ℝ≥0} {ω : Ω} (hω : firstDel p N ω ≤ T) :
    (cutPt p N T ω : WithTop ℝ≥0) = firstDel p N ω := by
  rw [cutPt, coe_untopA_of_ne_top (cutStop_ne_top _), cutStop, min_eq_left hω]

theorem entryTime_anti {n : ℝ≥0 → ℕ} {q q' : ℕ} (h : q ≤ q') : entryTime n q' ≤ entryTime n q :=
  le_iInf₂ fun t ht => iInf₂_le t (ht.trans h)

theorem IsDualFrom.isStoppingTime_entry (h : IsDualFrom P 𝓖 D0 p N X Y) (q : ℕ) :
    IsStoppingTime 𝓖 fun ω => entryTime (fun t => N t ω) q := by
  intro t
  have e : {ω | entryTime (fun t => N t ω) q ≤ t} = N t ⁻¹' {k | k ≤ q} := by
    ext ω; exact entryTime_le_iff (h.paths ω) q t
  rw [e]; exact (h.adapted t).1 (MeasurableSet.of_discrete)

theorem IsDualFrom.isStoppingTime_cut (h : IsDualFrom P 𝓖 D0 p N X Y) (T : ℝ≥0) :
    IsStoppingTime 𝓖 (cutStop p N T) :=
  (h.isStoppingTime_entry (p - 1)).min_const T

/-- The post-deletion filtration `𝓖_{σ'+·}`. -/
abbrev postFil (h : IsDualFrom P 𝓖 D0 p N X Y) (T : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
  shiftFil (h.isStoppingTime_cut T) cutStop_ne_top

/-- The post-deletion level (empty path off `{σ_{p−1} ≤ T}`). -/
def postN (p : ℕ) (N : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) : ℝ≥0 → Ω → ℕ := fun s ω =>
  if firstDel p N ω ≤ T then N (cutPt p N T ω + s) ω else 0

/-- The post-deletion coordinates, truncated. -/
def postC (p : ℕ) (N : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) (X : ℝ≥0 → Ω → ℕ → ℝ) :
    ℝ≥0 → Ω → ℕ → ℝ := fun s ω =>
  if firstDel p N ω ≤ T then truncCoord (N (cutPt p N T ω + s) ω) (X (cutPt p N T ω + s) ω)
  else 0

theorem measurableSet_postE (h : IsDualFrom P 𝓖 D0 p N X Y) (T : ℝ≥0) :
    MeasurableSet[postFil h T 0] {ω | firstDel p N ω ≤ T} := by
  have hm := IsStoppingTime.measurableSet_stopping_time_le (h.isStoppingTime_entry (p - 1))
    (isStoppingTime_untopA_add (h.isStoppingTime_cut T) (cutStop_ne_top) 0)
  have e : {ω | entryTime (fun t => N t ω) (p - 1) ≤
      (((cutStop p N T ω).untopA + 0 : ℝ≥0) : WithTop ℝ≥0)} = {ω | firstDel p N ω ≤ T} := by
    ext ω
    simp only [mem_ofPred_eq, add_zero]
    rw [coe_untopA_of_ne_top (cutStop_ne_top ω), cutStop, le_min_iff]
    exact ⟨fun h => h.2, fun h => ⟨le_rfl, h⟩⟩
  rw [← e]; exact hm

theorem IsDualFrom.unpad_padPath (h : IsDualFrom P 𝓖 D0 p N X Y) (r : ℝ≥0) (ω : Ω) :
    unpad p (padPath p N X Y r ω) = (N r ω, truncCoord (N r ω) (X r ω), truncCoord (N r ω) (Y r ω)) :=
  unpad_padState (h.level_le r ω) ((h.paths ω).chamber r)

theorem IsDualFrom.measurable_post (h : IsDualFrom P 𝓖 D0 p N X Y) (T s : ℝ≥0) :
    Measurable[postFil h T s] fun ω => padPath p N X Y (cutPt p N T ω + s) ω :=
  measurable_stoppedValue (StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => (h.measurable_padPath t).stronglyMeasurable) h.continuous_padPath)
    (isStoppingTime_untopA_add (h.isStoppingTime_cut T) (cutStop_ne_top) s)

/-- The post-deletion path is adapted to `𝓖_{σ'+·}`. -/
theorem IsDualFrom.post_adapted (h : IsDualFrom P 𝓖 D0 p N X Y) (T s : ℝ≥0) :
    Measurable[postFil h T s] (postN p N T s) ∧ Measurable[postFil h T s] (postC p N T X s) ∧
      Measurable[postFil h T s] (postC p N T Y s) := by
  set E := {ω | firstDel p N ω ≤ T} with hEdef
  have hEs : MeasurableSet[postFil h T s] E := (postFil h T).mono zero_le _ (measurableSet_postE h T)
  have ePN : postN p N T s =
      fun ω => if ω ∈ E then (unpad p (padPath p N X Y (cutPt p N T ω + s) ω)).1 else 0 :=
    funext fun ω => by simp only [postN, h.unpad_padPath, hEdef, mem_ofPred_eq]
  have ePX : postC p N T X s =
      fun ω => if ω ∈ E then (unpad p (padPath p N X Y (cutPt p N T ω + s) ω)).2.1 else 0 :=
    funext fun ω => by simp only [postC, h.unpad_padPath, hEdef, mem_ofPred_eq]
  have ePY : postC p N T Y s =
      fun ω => if ω ∈ E then (unpad p (padPath p N X Y (cutPt p N T ω + s) ω)).2.2 else 0 :=
    funext fun ω => by simp only [postC, h.unpad_padPath, hEdef, mem_ofPred_eq]
  have hm := h.measurable_post T s
  rw [ePN, ePX, ePY]
  exact ⟨Measurable.ite hEs ((measurable_fst.comp measurable_unpad).comp hm) measurable_const,
    Measurable.ite hEs ((measurable_snd.fst.comp measurable_unpad).comp hm) measurable_const,
    Measurable.ite hEs ((measurable_snd.snd.comp measurable_unpad).comp hm) measurable_const⟩

omit [MeasurableSpace Ω] in
/-- Bounds for the level-`q` martingale on bounded time intervals. -/
theorem abs_dualMartingale_le {q : ℕ} {f : DualCoord q → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ dualChamber q) (K : ℝ≥0) :
    ∃ C, ∀ t ≤ K, ∀ ω, |dualMartingale D0 q f N X Y t ω| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨C₂, hC₂⟩ := (continuous_dualGenerator D0 hf hfs).bounded_above_of_compact_support
    (hasCompactSupport_dualGenerator D0 hfc)
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0)
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ 0)
  refine ⟨C₁ + C₁ + C₂ * K, fun t ht ω => ?_⟩
  have h1 := norm_dualLift_le hC₁ (N t ω) (X t ω) (Y t ω)
  have h2 : ‖dualEntranceValue f N X Y t ω‖ ≤ C₁ := by
    unfold dualEntranceValue; split_ifs
    · exact norm_dualLift_le hC₁ _ _ _
    · simpa using hC₁0
  have h3 : ‖∫ u in Ioc (0 : ℝ) t, dualLift (dualGenerator D0 f) (N u.toNNReal ω)
      (X u.toNNReal ω) (Y u.toNNReal ω)‖ ≤ C₂ * K := by
    refine (norm_setIntegral_le_of_norm_le_const (by simp) fun u _ =>
      norm_dualLift_le hC₂ _ _ _).trans ?_
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by simp)]
    exact mul_le_mul_of_nonneg_left (by simpa using ht) hC₂0
  rw [← Real.norm_eq_abs]
  exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add h1 h2)) h3)

/-- **The post-deletion path is a realization at level `p − 1`**, under `P` conditioned
on any `A ⊆ {σ_{p−1} ≤ T}` in `𝓖_{σ_{p−1} ∧ T}`. -/
theorem IsDualFrom.shift (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) (T : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet[postFil h T 0] A) (hAE : A ⊆ {ω | firstDel p N ω ≤ T}) (hA0 : P A ≠ 0) :
    IsDualFrom (P[|A]) (postFil h T) D0 (p - 1) (postN p N T) (postC p N T X)
      (postC p N T Y) := by
  have := h.prob
  set E := {ω | firstDel p N ω ≤ T} with hEdef
  have hE := measurableSet_postE h T
  have hEs : ∀ s, MeasurableSet[postFil h T s] E := fun s => (postFil h T).mono zero_le _ hE
  have hAm : MeasurableSet A := (postFil h T).le 0 _ hA
  have hcut : ∀ ω ∈ E, (cutPt p N T ω : WithTop ℝ≥0) = entryTime (fun t => N t ω) (p - 1) :=
    fun ω hω => coe_cutPt_of_le hω
  have hpN : ∀ ω ∈ E, ∀ s, postN p N T s ω = N (cutPt p N T ω + s) ω := fun ω hω s => by
    simp only [postN, show firstDel p N ω ≤ T from hω, ↓reduceIte]
  have hpC : ∀ (Z : ℝ≥0 → Ω → ℕ → ℝ), ∀ ω ∈ E, ∀ s, postC p N T Z s ω =
      truncCoord (N (cutPt p N T ω + s) ω) (Z (cutPt p N T ω + s) ω) := fun Z ω hω s => by
    simp only [postC, show firstDel p N ω ≤ T from hω, ↓reduceIte]
  have hnN : ∀ ω ∉ E, ∀ s, postN p N T s ω = 0 := fun ω hω s => by
    simp only [postN, show ¬ firstDel p N ω ≤ T from hω, ↓reduceIte]
  have hnC : ∀ (Z : ℝ≥0 → Ω → ℕ → ℝ), ∀ ω ∉ E, ∀ s, postC p N T Z s ω = 0 := fun Z ω hω s => by
    simp only [postC, show ¬ firstDel p N ω ≤ T from hω, ↓reduceIte]
  refine
    { prob := cond_isProbabilityMeasure hA0
      adapted := fun s => ?_
      start := ?_
      bound := fun ω => ?_
      paths := fun ω => ?_
      martingale := fun q hq hqp f hf hfc hfs => ?_ }
  · exact h.post_adapted T s
  · have h1 : ∀ᵐ ω ∂P, ω ∈ A → postN p N T 0 ω = p - 1 := by
      filter_upwards [h.start] with ω h0 hωA
      rw [hpN ω (hAE hωA), add_zero]
      exact level_entryTime (h.paths ω) (by omega) (hcut ω (hAE hωA)).symm
    filter_upwards [ae_cond_mem hAm, ae_cond_of_ae h1 A] with ω h1 h2 using h2 h1
  · by_cases hω : ω ∈ E
    · rw [hpN ω hω, add_zero]
      exact (entryTime_le_iff (h.paths ω) (p - 1) _).1 (hcut ω hω).ge
    · rw [hnN ω hω]; exact Nat.zero_le _
  · by_cases hω : ω ∈ E
    · have e1 : (fun s => postN p N T s ω) = fun s => N (cutPt p N T ω + s) ω := funext (hpN ω hω)
      have e2 : (fun s => postC p N T X s ω) = fun s => truncCoord (N (cutPt p N T ω + s) ω)
          (X (cutPt p N T ω + s) ω) := funext (hpC X ω hω)
      have e3 : (fun s => postC p N T Y s ω) = fun s => truncCoord (N (cutPt p N T ω + s) ω)
          (Y (cutPt p N T ω + s) ω) := funext (hpC Y ω hω)
      rw [e1, e2, e3]; exact isDeletionPath_shift (h.paths ω) _
    · have e1 : (fun s => postN p N T s ω) = fun _ => 0 := funext (hnN ω hω)
      rw [e1]; exact isDeletionPath_empty _ _
  · have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
    have hM := h.martingale q hq (hqp.trans (Nat.sub_le p 1)) f hf hfc hfs
    have e : dualMartingale D0 q f (postN p N T) (postC p N T X) (postC p N T Y) =
        fun s => E.indicator fun ω => dualMartingale D0 q f N X Y
          ((cutStop p N T ω).untopA + s) ω - dualMartingale D0 q f N X Y (cutStop p N T ω).untopA ω := by
      funext s ω
      by_cases hω : ω ∈ E
      · rw [indicator_of_mem hω]
        have hr : (cutPt p N T ω : WithTop ℝ≥0) ≤ entryTime (fun t => N t ω) q :=
          (hcut ω hω).le.trans (entryTime_anti hqp)
        exact dualMartingale_shift (h.paths ω) hf2 hfc hfs hr (hpN ω hω) (hpC X ω hω)
          (hpC Y ω hω) s
      · rw [indicator_of_notMem hω]
        exact dualMartingale_empty hq (hnN ω hω) s
    rw [e]
    exact martingale_cond (martingale_shift hM
      (fun ω => continuous_dualMartingale (h.paths ω) D0 hq hf2 hfc hfs)
      (abs_dualMartingale_le hf2 hfc hfs) (h.isStoppingTime_cut T) (cutStop_ne_top)
      cutStop_le hE) hA hA0

end BlockBand.Transmission.Dual
