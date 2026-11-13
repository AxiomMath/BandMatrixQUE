module

public import BlockBand.Transmission.Dual.GLemmaCSeq

/-!
# Nested stop sequences and their glued path

* `sglue ŵ t = lim_n ŵ_n(t)`, the glued path; it equals `ŵ_N` on `[0, ρ_N]` (`sglue_eq`) and is
  continuous at every `t < ρ_∞` (`tendsto_sglue_of_lt`);
* `LL ŵ c`, the left limit `c` at `ρ_∞` in sequence form; **`tendsto_sglue_iff`**: when every
  `ρ_n < ρ_∞`, `LL ŵ c ↔ sglue ŵ → c` along `𝓝[<] ρ_∞`;
* `llSet`, a **measurable** Cauchy form of "the left limit exists" (dense times), with
  `mem_llSet_iff` (`↔ ∃ c, LL ŵ c` on nested sequences); `zstar ŵ = lim_n ŵ_n(t₀)`;
* `IsExh W U`: an exhaustion of `U` by interior domains with `closure W_n ⊆ W_{n+1}`; then
  `ρ_n < ρ_{n+1}` before `t₀` (`srho_lt_succ`), and at a left limit before `t₀` the limit lies in
  `closure U \ U` (Step 2 of §4: `LL.notMem`, `LL.mem_closure`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stopTime_coe stopTime_top
  stopTime_le exitTimeFrom_attained mem_of_lt_exitTimeFrom)
open scoped NNReal ENNReal

variable {d : ℕ} {W : ℕ → Set (Fin d → ℝ)} {t₀ : ℝ≥0}

/-- `ρ_n ∧ t₀` of the `n`-th path. -/
def srho (W : ℕ → Set (Fin d → ℝ)) (t₀ : ℝ≥0) (ŵ : ℕ → CPath d) (n : ℕ) : ℝ≥0 :=
  stopTime (pexit (W n) (ŵ n)) t₀

theorem coe_stopTime_self (τ : WithTop ℝ≥0) (t₀ : ℝ≥0) :
    ((stopTime τ t₀ : ℝ≥0) : WithTop ℝ≥0) = min τ t₀ := by
  induction τ with
  | top => rw [stopTime_top, min_top_left]
  | coe s => rw [stopTime_coe, WithTop.coe_min, min_comm]

theorem coe_srho (ŵ : ℕ → CPath d) (n : ℕ) :
    (srho W t₀ ŵ n : WithTop ℝ≥0) = min (pexit (W n) (ŵ n)) t₀ := coe_stopTime_self _ _

theorem srho_le (ŵ : ℕ → CPath d) (n : ℕ) : srho W t₀ ŵ n ≤ t₀ := stopTime_le _ _

theorem measurable_srho (hW : ∀ n, IsOpen (W n)) (n : ℕ) :
    Measurable fun ŵ : ℕ → CPath d => srho W t₀ ŵ n :=
  Measurable.untopA (measurable_const.min ((measurable_pexit (hW n)).comp (measurable_pi_apply n)))

theorem pexit_mono {V V' : Set (Fin d → ℝ)} (h : V ⊆ V') (w : CPath d) : pexit V w ≤ pexit V' w :=
  le_iInf₂ fun t ht => iInf₂_le t fun h' => ht (h h')

/-- A nested sequence: every path is the later ones stopped earlier (and itself stopped). -/
def IsNested (W : ℕ → Set (Fin d → ℝ)) (t₀ : ℝ≥0) (ŵ : ℕ → CPath d) : Prop :=
  ∀ k n, k ≤ n → ŵ k = pstop (W k) t₀ (ŵ n)

/-- `ρ_∞ = sup_n ρ_n` (`≤ t₀`). -/
def sinf (W : ℕ → Set (Fin d → ℝ)) (t₀ : ℝ≥0) (ŵ : ℕ → CPath d) : ℝ≥0 := ⨆ n, srho W t₀ ŵ n

theorem bddAbove_srho (ŵ : ℕ → CPath d) : BddAbove (range fun n => srho W t₀ ŵ n) :=
  ⟨t₀, by rintro _ ⟨n, rfl⟩; exact srho_le ŵ n⟩

theorem srho_le_sinf (ŵ : ℕ → CPath d) (n : ℕ) : srho W t₀ ŵ n ≤ sinf W t₀ ŵ :=
  le_ciSup (bddAbove_srho ŵ) n

theorem sinf_le (ŵ : ℕ → CPath d) : sinf W t₀ ŵ ≤ t₀ := ciSup_le fun n => srho_le ŵ n

theorem measurable_sinf (hW : ∀ n, IsOpen (W n)) :
    Measurable fun ŵ : ℕ → CPath d => sinf W t₀ ŵ :=
  Measurable.iSup fun n => measurable_srho hW n

theorem exists_lt_srho {ŵ : ℕ → CPath d} {t : ℝ≥0} (ht : t < sinf W t₀ ŵ) :
    ∃ m, t < srho W t₀ ŵ m :=
  (lt_ciSup_iff (bddAbove_srho ŵ)).1 ht

/-- The glued path `t ↦ lim_n ŵ_n(t)`. -/
def sglue (ŵ : ℕ → CPath d) (t : ℝ≥0) : Fin d → ℝ := limUnder atTop fun n => (ŵ n).1 t

namespace IsNested

variable {ŵ : ℕ → CPath d} (h : IsNested W t₀ ŵ) (hW : ∀ n, IsOpen (W n))
include h hW

theorem coe_srho_eq {k n : ℕ} (hkn : k ≤ n) :
    (srho W t₀ ŵ k : WithTop ℝ≥0) = min (pexit (W k) (ŵ n)) t₀ := by
  rw [coe_srho, h k n hkn, min_pexit_pstop (hW k)]

theorem srho_mono (hmono : Monotone W) {k n : ℕ} (hkn : k ≤ n) : srho W t₀ ŵ k ≤ srho W t₀ ŵ n := by
  rw [← WithTop.coe_le_coe, h.coe_srho_eq hW hkn, coe_srho]
  exact min_le_min (pexit_mono (hmono hkn) _) le_rfl

theorem apply_eq {k n : ℕ} (hkn : k ≤ n) {t : ℝ≥0} (ht : t ≤ srho W t₀ ŵ k) :
    (ŵ n).1 t = (ŵ k).1 t := by
  have e := congrArg (fun w : CPath d => w.1 t) (h k n hkn)
  rw [e, pstop_apply_of_le]
  rw [← h.coe_srho_eq hW hkn]; exact WithTop.coe_le_coe.2 ht

omit hW in
theorem apply_of_ge {n : ℕ} {t : ℝ≥0} (ht : srho W t₀ ŵ n ≤ t) :
    (ŵ n).1 t = (ŵ n).1 (srho W t₀ ŵ n) := by
  have e := congrArg (fun w : CPath d => w.1 t) (h n n le_rfl)
  rw [e]
  show (ŵ n).1 (stopTime (pexit (W n) (ŵ n)) (min t t₀)) = _
  have hs : stopTime (pexit (W n) (ŵ n)) (min t t₀) = srho W t₀ ŵ n := by
    apply WithTop.coe_injective
    rw [coe_stopTime_min, ← coe_srho]
    exact min_eq_right (WithTop.coe_le_coe.2 ht)
  rw [hs]

theorem sglue_eq {N : ℕ} {t : ℝ≥0} (ht : t ≤ srho W t₀ ŵ N) : sglue ŵ t = (ŵ N).1 t := by
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [eventually_ge_atTop N] with n hn using (h.apply_eq hW hn ht).symm

theorem sglue_mem {t : ℝ≥0} (ht : t < sinf W t₀ ŵ) : ∃ m, sglue ŵ t ∈ W m := by
  obtain ⟨m, hm⟩ := exists_lt_srho ht
  refine ⟨m, ?_⟩
  rw [h.sglue_eq hW hm.le]
  have : (t : WithTop ℝ≥0) < pexit (W m) (ŵ m) :=
    lt_of_lt_of_le (WithTop.coe_lt_coe.2 hm) (by rw [coe_srho]; exact min_le_left _ _)
  exact mem_of_lt_exitTimeFrom (Y := cev d) this

/-- The glued path is continuous before `ρ_∞`. -/
theorem tendsto_sglue_of_lt {s : ℝ≥0} (hs : s < sinf W t₀ ŵ) :
    Tendsto (sglue ŵ) (𝓝 s) (𝓝 (sglue ŵ s)) := by
  obtain ⟨m, hm⟩ := exists_lt_srho hs
  have he : (fun t => (ŵ m).1 t) =ᶠ[𝓝 s] sglue ŵ := by
    filter_upwards [Iio_mem_nhds hm] with t ht using (h.sglue_eq hW (le_of_lt ht)).symm
  rw [h.sglue_eq hW hm.le]
  exact ((ŵ m).2.tendsto s).congr' he

end IsNested

/-- The left limit `c` at `ρ_∞`, in sequence form. -/
def LL (W : ℕ → Set (Fin d → ℝ)) (t₀ : ℝ≥0) (ŵ : ℕ → CPath d) (c : Fin d → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n, N ≤ n → ∀ t : ℝ≥0, srho W t₀ ŵ N ≤ t → dist ((ŵ n).1 t) c ≤ ε

theorem IsNested.tendsto_sglue_iff {ŵ : ℕ → CPath d} (h : IsNested W t₀ ŵ)
    (hW : ∀ n, IsOpen (W n)) (hmono : Monotone W) (hstrict : ∀ n, srho W t₀ ŵ n < sinf W t₀ ŵ) (c : Fin d → ℝ) :
    Tendsto (sglue ŵ) (𝓝[<] sinf W t₀ ŵ) (𝓝 c) ↔ LL W t₀ ŵ c := by
  constructor
  · intro hT ε hε
    obtain ⟨s, hs, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' (hstrict 0)).1
      (hT (Metric.closedBall_mem_nhds c hε))
    obtain ⟨N, hN⟩ := exists_lt_srho hs
    refine ⟨N, fun n hn t ht => ?_⟩
    set u := min t (srho W t₀ ŵ n)
    have hu : (ŵ n).1 t = sglue ŵ u := by
      rw [h.sglue_eq hW (min_le_right _ _)]
      rcases le_total t (srho W t₀ ŵ n) with htn | htn
      · rw [min_eq_left htn]
      · rw [min_eq_right htn]; exact h.apply_of_ge htn
    rw [hu]
    have huN : srho W t₀ ŵ N ≤ u := le_min ht (h.srho_mono hW hmono hn)
    exact hsub ⟨hN.trans_le huN, (min_le_right _ _).trans_lt (hstrict n)⟩
  · intro hL
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hL (ε / 2) (half_pos hε)
    filter_upwards [Ioo_mem_nhdsLT (hstrict N)] with t ht
    obtain ⟨m, hm⟩ := exists_lt_srho ht.2
    rw [h.sglue_eq hW (hm.le.trans (h.srho_mono hW hmono (le_max_left m N)))]
    exact (hN _ (le_max_right m N) t ht.1.le).trans_lt (half_lt_self hε)

theorem LL.tendsto {ŵ : ℕ → CPath d} {c : Fin d → ℝ} (hL : LL W t₀ ŵ c) :
    Tendsto (fun n => (ŵ n).1 t₀) atTop (𝓝 c) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := hL (ε / 2) (half_pos hε)
  exact ⟨N, fun n hn => (hN n hn t₀ (srho_le ŵ N)).trans_lt (half_lt_self hε)⟩

/-!
## A measurable form of "the left limit exists"
-/

/-- A fixed dense sequence of times. -/
def dtime : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0

theorem le_of_dtime {f : ℝ≥0 → ℝ} (hf : Continuous f) {a : ℝ≥0} {ε : ℝ}
    (h : ∀ i, a ≤ dtime i → f (dtime i) ≤ ε) {t : ℝ≥0} (ht : a ≤ t) : f t ≤ ε := by
  have hS : IsClosed {t | f t ≤ ε} := isClosed_le hf continuous_const
  have h1 : Ioi a ∩ range dtime ⊆ {t | f t ≤ ε} := by
    rintro _ ⟨hx, i, rfl⟩; exact h i (le_of_lt hx)
  have h2 : Ioi a ⊆ {t | f t ≤ ε} :=
    ((TopologicalSpace.denseRange_denseSeq ℝ≥0).open_subset_closure_inter isOpen_Ioi).trans
      (closure_minimal h1 hS)
  have h3 : closure (Ioi a) ⊆ {t | f t ≤ ε} := closure_minimal h2 hS
  rw [closure_Ioi] at h3
  exact h3 ht

/-- The Cauchy criterion for the left limit at `ρ_∞`, over the dense times. -/
def llSet (W : ℕ → Set (Fin d → ℝ)) (t₀ : ℝ≥0) : Set (ℕ → CPath d) :=
  {ŵ | ∀ k : ℕ, ∃ N, ∀ n, N ≤ n → ∀ i : ℕ, srho W t₀ ŵ N ≤ dtime i →
    dist ((ŵ n).1 (dtime i)) ((ŵ N).1 t₀) ≤ 1 / ((k : ℝ) + 1)}

theorem measurable_eval_seq (n : ℕ) (t : ℝ≥0) :
    Measurable fun ŵ : ℕ → CPath d => (ŵ n).1 t :=
  (measurable_cev t).comp (measurable_pi_apply n)

theorem measurableSet_llSet (hW : ∀ n, IsOpen (W n)) : MeasurableSet (llSet W t₀) := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun k => Measurable.exists fun N =>
    Measurable.forall fun n => Measurable.imp measurable_const (Measurable.forall fun i =>
      Measurable.imp ?_ ?_))
  · exact measurableSet_setOfPred.1 (measurableSet_le (measurable_srho hW N) measurable_const)
  · exact measurableSet_setOfPred.1 (measurableSet_le
      ((measurable_eval_seq n _).dist (measurable_eval_seq N t₀)) measurable_const)

theorem exists_one_div_lt' {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, 1 / ((k : ℝ) + 1) < ε :=
  exists_nat_one_div_lt hε

/-- **On nested sequences, `llSet` is "a left limit exists".** -/
theorem mem_llSet_iff {ŵ : ℕ → CPath d} :
    ŵ ∈ llSet W t₀ ↔ ∃ c, LL W t₀ ŵ c := by
  constructor
  · intro hŵ
    choose N hN using hŵ
    have hN' : ∀ k n, N k ≤ n → ∀ t, srho W t₀ ŵ (N k) ≤ t →
        dist ((ŵ n).1 t) ((ŵ (N k)).1 t₀) ≤ 1 / ((k : ℝ) + 1) := fun k n hn t ht =>
      le_of_dtime (f := fun t => dist ((ŵ n).1 t) ((ŵ (N k)).1 t₀))
        ((ŵ n).2.dist continuous_const) (hN k n hn) ht
    have hc : CauchySeq fun n => (ŵ n).1 t₀ := by
      refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
      obtain ⟨k, hk⟩ := exists_one_div_lt' hε
      exact ⟨N k, fun n hn => (hN' k n hn t₀ (srho_le ŵ _)).trans_lt hk⟩
    obtain ⟨c, hcl⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨c, fun ε hε => ?_⟩
    obtain ⟨k, hk⟩ := exists_one_div_lt' (half_pos hε)
    refine ⟨N k, fun n hn t ht => ?_⟩
    have hd : dist ((ŵ (N k)).1 t₀) c ≤ 1 / ((k : ℝ) + 1) := by
      have ht' : Tendsto (fun m => dist ((ŵ m).1 t₀) ((ŵ (N k)).1 t₀)) atTop
          (𝓝 (dist c ((ŵ (N k)).1 t₀))) := hcl.dist tendsto_const_nhds
      rw [dist_comm]
      refine le_of_tendsto ht' ?_
      filter_upwards [eventually_ge_atTop (N k)] with m hm using hN' k m hm t₀ (srho_le ŵ _)
    calc dist ((ŵ n).1 t) c ≤ dist ((ŵ n).1 t) ((ŵ (N k)).1 t₀) + dist ((ŵ (N k)).1 t₀) c :=
          dist_triangle _ _ _
      _ ≤ 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := add_le_add (hN' k n hn t ht) hd
      _ ≤ ε := by linarith
  · rintro ⟨c, hL⟩ k
    obtain ⟨N, hN⟩ := hL (1 / ((k : ℝ) + 1) / 2) (by positivity)
    refine ⟨N, fun n hn i hi => ?_⟩
    calc dist ((ŵ n).1 (dtime i)) ((ŵ N).1 t₀) ≤ dist ((ŵ n).1 (dtime i)) c + dist c ((ŵ N).1 t₀) :=
          dist_triangle _ _ _
      _ ≤ 1 / ((k : ℝ) + 1) / 2 + 1 / ((k : ℝ) + 1) / 2 := by
          refine add_le_add (hN n hn _ hi) ?_
          rw [dist_comm]; exact hN N le_rfl t₀ (srho_le ŵ N)
      _ = 1 / ((k : ℝ) + 1) := by ring

/-- The left limit at `ρ_∞`, as a measurable function of the sequence. -/
def zstar (t₀ : ℝ≥0) (ŵ : ℕ → CPath d) : Fin d → ℝ := limUnder atTop fun n => (ŵ n).1 t₀

theorem measurable_zstar : Measurable (zstar (d := d) t₀) :=
  (StronglyMeasurable.limUnder fun n =>
    (measurable_eval_seq (d := d) n t₀).stronglyMeasurable).measurable

theorem LL.zstar_eq {ŵ : ℕ → CPath d} {c : Fin d → ℝ} (hL : LL W t₀ ŵ c) : zstar t₀ ŵ = c :=
  hL.tendsto.limUnder_eq

/-!
## Exhaustions
-/

/-- An exhaustion of `U` by interior domains with `closure W_n ⊆ W_{n+1}`. -/
structure IsExh (W : ℕ → Set (Fin d → ℝ)) (U : Set (Fin d → ℝ)) : Prop where
  dom : ∀ n, IsInteriorDomain (W n) U
  succ : ∀ n, closure (W n) ⊆ W (n + 1)
  cover : ∀ x ∈ U, ∃ n, x ∈ W n

variable {U : Set (Fin d → ℝ)}

theorem IsExh.isOpen (hE : IsExh W U) (n : ℕ) : IsOpen (W n) := (hE.dom n).1

theorem IsExh.mono (hE : IsExh W U) : Monotone W :=
  monotone_nat_of_le_succ fun n => subset_closure.trans (hE.succ n)

theorem pexit_eq_of_lt {ŵ : ℕ → CPath d} {n : ℕ} (hn : srho W t₀ ŵ n < t₀) :
    pexit (W n) (ŵ n) = srho W t₀ ŵ n := by
  have e := coe_srho (W := W) (t₀ := t₀) ŵ n
  rcases le_total (pexit (W n) (ŵ n)) t₀ with hle | hle
  · rw [min_eq_left hle] at e; exact e.symm
  · rw [min_eq_right hle] at e; exact absurd (WithTop.coe_injective e) hn.ne

theorem notMem_of_lt (hW : ∀ n, IsOpen (W n)) {ŵ : ℕ → CPath d} {n : ℕ}
    (hn : srho W t₀ ŵ n < t₀) : (ŵ n).1 (srho W t₀ ŵ n) ∉ W n := by
  have he := pexit_eq_of_lt hn
  rcases exitTimeFrom_attained (hW n) (Y := cev d) (ω := ŵ n) (ŵ n).2 with h1 | ⟨s₀, h1, h2⟩
  · exact absurd (h1.symm.trans he) (WithTop.top_ne_coe)
  · have e : s₀ = srho W t₀ ŵ n := WithTop.coe_injective (h1.symm.trans he)
    rw [← e]; exact h2

theorem IsNested.mem_closure_of_lt {ŵ : ℕ → CPath d} (h : IsNested W t₀ ŵ)
    (hW : ∀ n, IsOpen (W n)) (hmono : Monotone W) (h0 : (ŵ 0).1 0 ∈ W 0) {n : ℕ}
    (hn : srho W t₀ ŵ n < t₀) : (ŵ n).1 (srho W t₀ ŵ n) ∈ closure (W n) := by
  have he := pexit_eq_of_lt hn
  have hpos : 0 < srho W t₀ ŵ n := by
    refine lt_of_le_of_ne zero_le fun h00 => notMem_of_lt hW hn ?_
    rw [← h00, h.apply_eq hW (Nat.zero_le n) (zero_le : (0 : ℝ≥0) ≤ srho W t₀ ŵ 0)]
    exact hmono (Nat.zero_le n) h0
  have : (𝓝[<] srho W t₀ ŵ n).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
  refine mem_closure_of_tendsto (((ŵ n).2.tendsto _).mono_left
    (nhdsWithin_le_nhds (s := Iio (srho W t₀ ŵ n)))) ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact mem_of_lt_exitTimeFrom (Y := cev d) (ω := ŵ n)
    (show (u : WithTop ℝ≥0) < pexit (W n) (ŵ n) by rw [he]; exact WithTop.coe_lt_coe.2 hu)

/-- **`ρ_n < ρ_{n+1}` before `t₀`.** -/
theorem IsNested.srho_lt_succ {ŵ : ℕ → CPath d} (h : IsNested W t₀ ŵ) (hE : IsExh W U)
    (h0 : (ŵ 0).1 0 ∈ W 0) {n : ℕ} (hn : srho W t₀ ŵ n < t₀) :
    srho W t₀ ŵ n < srho W t₀ ŵ (n + 1) := by
  have hc := h.mem_closure_of_lt hE.isOpen hE.mono h0 hn
  have hm : (ŵ (n + 1)).1 (srho W t₀ ŵ n) ∈ W (n + 1) := by
    rw [h.apply_eq hE.isOpen (Nat.le_succ n) le_rfl]; exact hE.succ n hc
  refine lt_of_le_of_ne (h.srho_mono hE.isOpen hE.mono (Nat.le_succ n)) fun heq => ?_
  rw [heq] at hm hn
  exact notMem_of_lt hE.isOpen hn hm

theorem IsNested.srho_lt_sinf {ŵ : ℕ → CPath d} (h : IsNested W t₀ ŵ) (hE : IsExh W U)
    (h0 : (ŵ 0).1 0 ∈ W 0) (hlt : sinf W t₀ ŵ < t₀) (n : ℕ) : srho W t₀ ŵ n < sinf W t₀ ŵ :=
  (h.srho_lt_succ hE h0 ((srho_le_sinf ŵ n).trans_lt hlt)).trans_le (srho_le_sinf ŵ (n + 1))

/-- **Step 2 of §4**: a left limit before `t₀` is not in `U`. -/
theorem IsNested.LL_notMem {ŵ : ℕ → CPath d} (h : IsNested W t₀ ŵ) (hE : IsExh W U)
    (hlt : sinf W t₀ ŵ < t₀) {c : Fin d → ℝ} (hL : LL W t₀ ŵ c) : c ∉ U := by
  intro hc
  obtain ⟨m, hm⟩ := hE.cover c hc
  obtain ⟨n, hn1, hn2⟩ := ((hL.tendsto.eventually ((hE.isOpen m).mem_nhds hm)).and
    (eventually_ge_atTop m)).exists
  have hnt : srho W t₀ ŵ n < t₀ := (srho_le_sinf ŵ n).trans_lt hlt
  refine notMem_of_lt hE.isOpen hnt (hE.mono hn2 ?_)
  rwa [← h.apply_of_ge (srho_le ŵ n)]

/-- A left limit before `t₀` lies in `closure U`. -/
theorem IsNested.LL_mem_closure {ŵ : ℕ → CPath d} (h : IsNested W t₀ ŵ) (hE : IsExh W U)
    (h0 : (ŵ 0).1 0 ∈ W 0) (hlt : sinf W t₀ ŵ < t₀) {c : Fin d → ℝ} (hL : LL W t₀ ŵ c) :
    c ∈ closure U := by
  refine mem_closure_of_tendsto hL.tendsto (Eventually.of_forall fun n => ?_)
  have hnt : srho W t₀ ŵ n < t₀ := (srho_le_sinf ŵ n).trans_lt hlt
  rw [h.apply_of_ge (srho_le ŵ n)]
  exact (hE.dom n).2.2 (h.mem_closure_of_lt hE.isOpen hE.mono h0 hnt)

end BlockBand.Transmission.Dual.G
