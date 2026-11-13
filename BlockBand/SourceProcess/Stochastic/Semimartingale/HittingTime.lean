module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.Measure
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Raw stopping times equal to hitting times on continuous paths

Setting: `Ω` with an arbitrary (raw) filtration `𝓖 : Filtration ℝ≥0 m₀`; `Y : ℝ≥0 → Ω → E`
adapted (`Measurable[𝓖 t] (Y t)`), `E` a pseudo-emetric space with an opens-measurable
σ-algebra; `F ⊆ E` closed. No continuity of paths is assumed for the stopping-time property.

`rawHit F Y` is a `𝓖`-stopping time (`isStoppingTime_rawHit`) and equals the first hitting
time `hitTime F Y ω = inf {t | Y_t(ω) ∈ F}` on every continuous path (`rawHit_eq_hitTime`);
in particular it is a.s. equal to the hitting time when paths are a.s. continuous
(`exists_stoppingTime_ae_eq_hitTime`). Construction:
`D_t = inf_{dyadic q ≤ t} dist(Y_q, F)`, `s₁ = inf {t | D_t = 0}`, and `rawHit = s₁` if the
infimum defining `D_{s₁}` vanishes, `⊤` otherwise.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory Filter Topology Set Metric
open scoped NNReal ENNReal

variable {Ω E : Type*} [PseudoEMetricSpace E]

/-- First hitting time of `F` (`⊤` if never). -/
def hitTime (F : Set E) (Y : ℝ≥0 → Ω → E) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : Y t ω ∈ F), (t : WithTop ℝ≥0)

/-- Dyadic times `k / 2^j`. -/
abbrev dy (j k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ j

/-- `D_t = inf over dyadic q ≤ t of dist(Y_q, F)`. -/
def dyadInf (F : Set E) (Y : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (j : ℕ) (k : ℕ), if dy j k ≤ t then infEDist (Y (dy j k) ω) F else ⊤

/-- `s₁ = inf {t | D_t = 0}`. -/
def preHit (F : Set E) (Y : ℝ≥0 → Ω → E) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : dyadInf F Y t ω = 0), (t : WithTop ℝ≥0)

open Classical in
/-- The raw stopping time. -/
def rawHit (F : Set E) (Y : ℝ≥0 → Ω → E) (ω : Ω) : WithTop ℝ≥0 :=
  if ∀ m : ℕ, ∃ j k : ℕ, (dy j k : WithTop ℝ≥0) ≤ preHit F Y ω ∧
      infEDist (Y (dy j k) ω) F < (m : ℝ≥0∞)⁻¹ then preHit F Y ω else ⊤

variable {F : Set E} {Y : ℝ≥0 → Ω → E} {ω : Ω}

theorem dyadInf_le {t : ℝ≥0} {j k : ℕ} (h : dy j k ≤ t) :
    dyadInf F Y t ω ≤ infEDist (Y (dy j k) ω) F :=
  (iInf₂_le j k).trans (by simp only [h, ↓reduceIte, le_refl])

theorem dyadInf_anti {t t' : ℝ≥0} (h : t ≤ t') : dyadInf F Y t' ω ≤ dyadInf F Y t ω := by
  refine iInf₂_mono fun j k => ?_
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact le_top
  · exact absurd (h2.trans h) h1
  · exact le_rfl

theorem dyad_eq_dy (j : ℕ) (v : ℝ≥0) : dyad j v = dy j ⌊v * 2 ^ j⌋₊ := rfl

/-- `D_t = 0` iff the path meets `F` before `t`, for a continuous path and closed `F`. -/
theorem dyadInf_eq_zero_iff (hF : IsClosed F) (hY : Continuous fun t => Y t ω) (t : ℝ≥0) :
    dyadInf F Y t ω = 0 ↔ ∃ s ≤ t, Y s ω ∈ F := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    have hpos : ∀ s ∈ Icc (0 : ℝ≥0) t, 0 < infEDist (Y s ω) F := fun s hs => by
      refine pos_iff_ne_zero.2 fun h0 => hno s hs.2 ?_
      rw [← hF.closure_eq]; exact mem_closure_iff_infEDist_zero.2 h0
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, left_mem_Icc.2 zero_le⟩
      ((continuous_infEDist.comp hY).continuousOn (s := Icc (0 : ℝ≥0) t))
    have : infEDist (Y s₀ ω) F ≤ dyadInf F Y t ω := by
      refine le_iInf₂ fun j k => ?_
      split_ifs with hq
      · exact hmin ⟨zero_le, hq⟩
      · exact le_top
    rw [h] at this
    exact absurd (hpos s₀ hs₀) (not_lt.2 this)
  · rintro ⟨s, hst, hs⟩
    have hlim : Tendsto (fun j => infEDist (Y (dyad j s) ω) F) atTop (𝓝 0) := by
      have := ((continuous_infEDist (s := F)).comp hY).tendsto s |>.comp (tendsto_dyad s)
      rw [Function.comp_apply, infEDist_zero_of_mem hs] at this
      exact this
    refine le_antisymm (ge_of_tendsto hlim (Eventually.of_forall fun j => ?_)) zero_le
    exact dyadInf_le ((dyad_le j s).trans hst)

/-- `s₁ < q` iff `D_r = 0` for some dyadic `r < q` (any path). -/
theorem preHit_lt_iff (q : ℝ≥0) :
    preHit F Y ω < q ↔ ∃ j k : ℕ, dy j k < q ∧ dyadInf F Y (dy j k) ω = 0 := by
  constructor
  · intro h
    unfold preHit at h
    simp only [iInf_lt_iff] at h
    obtain ⟨t', ht', hlt⟩ := h
    have hlt' : t' < q := WithTop.coe_lt_coe.1 hlt
    set q' : ℝ≥0 := (t' + q) / 2
    have hq'1 : t' < q' := by
      simp only [q']; rw [lt_div_iff₀ (by norm_num), mul_two]; exact add_lt_add_right hlt' t'
    have hq'2 : q' < q := by
      simp only [q']; rw [div_lt_iff₀ (by norm_num), mul_two]; exact add_lt_add_left hlt' q
    obtain ⟨j, hj⟩ := ((tendsto_dyad q').eventually (lt_mem_nhds hq'1)).exists
    refine ⟨j, ⌊q' * 2 ^ j⌋₊, ((dyad_le j q').trans_lt hq'2), ?_⟩
    exact le_antisymm ((dyadInf_anti hj.le).trans ht'.le) zero_le
  · rintro ⟨j, k, h1, h2⟩
    exact lt_of_le_of_lt (iInf₂_le (dy j k) h2) (WithTop.coe_lt_coe.2 h1)

variable {m₀ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m₀} [MeasurableSpace E]
  [OpensMeasurableSpace E]

theorem measurable_dyadInf (hY : ∀ t, Measurable[𝓖 t] (Y t)) (t : ℝ≥0) :
    Measurable[𝓖 t] (dyadInf F Y t) := by
  refine Measurable.iInf fun j => Measurable.iInf fun k => ?_
  by_cases h : dy j k ≤ t
  · simp only [h, ↓reduceIte]
    exact (continuous_infEDist.measurable.comp (hY _)).mono (𝓖.mono h) le_rfl
  · simp only [h, ↓reduceIte]; exact measurable_const

theorem measurableSet_preHit_lt (hY : ∀ t, Measurable[𝓖 t] (Y t)) (q : ℝ≥0) :
    MeasurableSet[𝓖 q] {ω | preHit F Y ω < q} := by
  have e : {ω | preHit F Y ω < q} =
      ⋃ (j : ℕ) (k : ℕ), {ω | dy j k < q ∧ dyadInf F Y (dy j k) ω = 0} := by
    ext ω; simp only [mem_iUnion]; exact preHit_lt_iff q
  rw [e]
  refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun k => ?_
  by_cases h : dy j k < q
  · have := 𝓖.mono h.le _ ((measurable_dyadInf (F := F) hY (dy j k)) (measurableSet_singleton 0))
    convert this using 1
    ext ω; simp [h]
  · convert MeasurableSet.empty using 1
    ext ω; simp [h]

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
theorem rawHit_le_iff (t : ℝ≥0) : rawHit F Y ω ≤ t ↔ dyadInf F Y t ω = 0 ∧
    ∀ m : ℕ, ∃ j k : ℕ, dy j k ≤ t ∧ (dy j k : WithTop ℝ≥0) ≤ preHit F Y ω ∧
      infEDist (Y (dy j k) ω) F < (m : ℝ≥0∞)⁻¹ := by
  classical
  unfold rawHit
  split_ifs with hc
  · constructor
    · intro h
      have hq : ∀ m : ℕ, ∃ j k : ℕ, dy j k ≤ t ∧ (dy j k : WithTop ℝ≥0) ≤ preHit F Y ω ∧
          infEDist (Y (dy j k) ω) F < (m : ℝ≥0∞)⁻¹ := fun m => by
        obtain ⟨j, k, h1, h2⟩ := hc m
        exact ⟨j, k, WithTop.coe_le_coe.1 (h1.trans h), h1, h2⟩
      refine ⟨le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun m => ?_) zero_le,
        hq⟩
      obtain ⟨j, k, h1, -, h3⟩ := hq m
      exact (dyadInf_le h1).trans h3.le
    · rintro ⟨h1, -⟩
      exact iInf₂_le t h1
  · constructor
    · intro h; exact absurd h (not_le.2 (WithTop.coe_lt_top t))
    · rintro ⟨-, h2⟩
      exact absurd (fun m => by obtain ⟨j, k, -, h⟩ := h2 m; exact ⟨j, k, h⟩) hc

/-- **`rawHit` is a stopping time of the raw filtration.** -/
theorem isStoppingTime_rawHit (hY : ∀ t, Measurable[𝓖 t] (Y t)) :
    IsStoppingTime 𝓖 (rawHit F Y) := by
  intro t
  have e : {ω | rawHit F Y ω ≤ t} = {ω | dyadInf F Y t ω = 0} ∩
      ⋂ m : ℕ, ⋃ (j : ℕ) (k : ℕ), {ω | dy j k ≤ t ∧ (dy j k : WithTop ℝ≥0) ≤ preHit F Y ω ∧
        infEDist (Y (dy j k) ω) F < (m : ℝ≥0∞)⁻¹} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
    exact rawHit_le_iff t
  rw [e]
  refine ((measurable_dyadInf hY t) (measurableSet_singleton 0)).inter
    (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun k => ?_)
  by_cases h : dy j k ≤ t
  · have h1 : MeasurableSet[𝓖 t] {ω | (dy j k : WithTop ℝ≥0) ≤ preHit F Y ω} := by
      have := (𝓖.mono h _ (measurableSet_preHit_lt (F := F) hY (dy j k))).compl
      convert this using 1
      ext ω; simp only [mem_ofPred_eq, mem_compl_iff]; exact not_lt.symm
    have h2 : MeasurableSet[𝓖 t] {ω | infEDist (Y (dy j k) ω) F < (m : ℝ≥0∞)⁻¹} :=
      𝓖.mono h _ (measurableSet_lt (continuous_infEDist.measurable.comp (hY _))
        measurable_const)
    convert h1.inter h2 using 1
    ext ω; simp [h]
  · convert MeasurableSet.empty using 1
    ext ω; simp [h]

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- **On every continuous path `rawHit` is the hitting time.** -/
theorem rawHit_eq_hitTime (hF : IsClosed F) (hY : Continuous fun t => Y t ω) :
    rawHit F Y ω = hitTime F Y ω := by
  classical
  have hpre : preHit F Y ω = hitTime F Y ω := by
    refine le_antisymm (le_iInf₂ fun s hs => iInf₂_le s ((dyadInf_eq_zero_iff hF hY s).2
      ⟨s, le_rfl, hs⟩)) (le_iInf₂ fun t ht => ?_)
    obtain ⟨s, hst, hs⟩ := (dyadInf_eq_zero_iff hF hY t).1 ht
    exact (iInf₂_le s hs).trans (WithTop.coe_le_coe.2 hst)
  set S := {t : ℝ≥0 | Y t ω ∈ F}
  rcases S.eq_empty_or_nonempty with hS | hS
  · have htop : hitTime F Y ω = ⊤ := iInf₂_eq_top.2 fun t ht => by
      have : t ∈ S := ht
      rw [hS] at this; exact absurd this (notMem_empty t)
    unfold rawHit
    split_ifs <;> simp [hpre, htop]
  · have hc : IsClosed S := hF.preimage hY
    have hmem := hc.csInf_mem hS ⟨0, fun _ _ => zero_le⟩
    have heq : hitTime F Y ω = (sInf S : ℝ≥0) := le_antisymm (iInf₂_le _ hmem)
      (le_iInf₂ fun t ht => WithTop.coe_le_coe.2 (csInf_le ⟨0, fun _ _ => zero_le⟩ ht))
    have hcond : ∀ m : ℕ, ∃ j k : ℕ, (dy j k : WithTop ℝ≥0) ≤ preHit F Y ω ∧
        infEDist (Y (dy j k) ω) F < (m : ℝ≥0∞)⁻¹ := by
      intro m
      have hlim : Tendsto (fun j => infEDist (Y (dyad j (sInf S)) ω) F) atTop (𝓝 0) := by
        have := ((continuous_infEDist (s := F)).comp hY).tendsto (sInf S) |>.comp
          (tendsto_dyad (sInf S))
        rw [Function.comp_apply, infEDist_zero_of_mem (show Y (sInf S) ω ∈ F from hmem)] at this
        exact this
      obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.inv_pos.2
        (ENNReal.natCast_ne_top m)))).exists
      refine ⟨j, ⌊sInf S * 2 ^ j⌋₊, ?_, hj⟩
      rw [hpre, heq]
      exact WithTop.coe_le_coe.2 (dyad_le j _)
    unfold rawHit
    exact (ite_eq_left_of_eq_true _ _ (eq_true hcond)).trans hpre

/-- **Hitting times of closed sets agree a.s. with raw stopping times.** -/
theorem exists_stoppingTime_ae_eq_hitTime {Q : Measure Ω} (hY : ∀ t, Measurable[𝓖 t] (Y t))
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω) (hF : IsClosed F) :
    ∃ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ ∧
      (∀ ω, Continuous (fun t => Y t ω) → τ ω = hitTime F Y ω) ∧
      ∀ᵐ ω ∂Q, τ ω = hitTime F Y ω :=
  ⟨rawHit F Y, isStoppingTime_rawHit hY, fun _ h => rawHit_eq_hitTime hF h,
    hc.mono fun _ h => rawHit_eq_hitTime hF h⟩

end BlockBand.SourceProcess.Stochastic.Semimartingale
