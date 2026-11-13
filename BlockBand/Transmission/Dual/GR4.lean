module

public import BlockBand.Transmission.Dual.GR4Proc
public import BlockBand.Transmission.Dual.GHLeftCont

/-!
# The boundary classification for a solution from a random start

Setting: a filtered probability space `(Ω, 𝓖, P)`, a `𝓖₀`-measurable start `ξ`, and for each `n`
a process `Z n` with continuous paths (`Z n : Ω → CPath d`) solving the `(b, a)` martingale
problem in `W n`, started at `ξ`. The record is `Φ = useq W Z` (untruncated stopped paths), and
`κ = condKernel (law (ξ, Φ))`, `μ = law ξ`.
* `ae_mart_kernel`: a stopped functional with a martingale version under `P` gives, through the
  cut-off canonical functional and `ae_martingale_condKernel`, a `cfilt`-martingale under `κ z`
  for `μ`-a.e. `z`.
* `ae_start_kernel`: `ŵ_n(0) = z`, `κ z`-a.s., for `μ`-a.e. `z`.
* **`ae_isMPSolutionOn_kernel`**: for `μ`-a.e. `z`, every coordinate process `cY n` solves the
  `(b, a)` martingale problem in `W n` under `κ z` (countably many domains `exh (W n) k`, then
  `exists_mart_of_cover` for all interior domains).
* `ae_isStopSeq_kernel`: the stop-sequence relation passes to `κ z`.
* **`ae_goodSeq_of_randomStart`** (the random-start form of the boundary classification): for
  the box exhaustion of `𝒞_{q+1}` and the flat dual, a.s. on `{ξ ∈ flatBox (q+1) n₀}` the
  truncated stop sequence of `Z` is in `goodSeq` (`map_eq_of_isMPSolutionOn` against a
  `B1Family` from `z`, `gSeq_all_holds`, `ae_of_ae_condKernel`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.Transmission.Dual
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {W : ℕ → Set (Fin d → ℝ)} {Z : ℕ → Ω → CPath d} {ξ : Ω → Fin d → ℝ}

/-- **A martingale of the record passes to the kernel.** -/
theorem ae_mart_kernel (hW : ∀ n, IsOpen (W n))
    (hZa : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t)) (hZ0 : ∀ n x, (Z n x).1 0 = ξ x)
    (hξ : Measurable[𝓖 0] ξ) {n : ℕ} {V : Set (Fin d → ℝ)} (hV : IsInteriorDomain V (W n))
    {G G' : ℝ≥0 → (ℝ≥0 → Fin d → ℝ) → ℝ}
    (hG : ∀ s (y y' : ℝ≥0 → Fin d → ℝ), (∀ u ≤ s, y u = y' u) → G s y = G s y')
    (hG' : IsPathFn (closure V) G')
    (hagree : ∀ s (w : CPath d), (∀ u ≤ s, w.1 u ∈ closure V) → G s w.1 = G' s w.1)
    (hN : ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 P ∧ ∀ t, N t =ᵐ[P]
      stoppedProcess (fun t x => G t (Z n x).1) (exitTimeFrom V (zproc Z n)) t) :
    ∀ᵐ z ∂(jlaw P ξ (useq W Z)).fst,
      Martingale (cfun n V G) (cfilt d) ((jlaw P ξ (useq W Z)).condKernel z) := by
  have he : cfun n V G = cfun n V G' := cfun_congr hV.1 hagree
  obtain ⟨M, hM, hMe⟩ := exists_mart_cfun (W := W) hξ hZ0 hV.1 (subset_closure.trans hV.2.2) hG hN
  rw [he] at hMe ⊢
  exact ae_martingale_condKernel (tr := ctrunc) (𝓕 := cfilt d) measurable_ctrunc cfilt_eq hξ
    (measurable_useq hW hZa) (measurable_ctrunc_useq hW hZa) (measurable_cfilt_cfun hV.1 hG')
    (fun ŵ _ => (continuous_cfun hG' ŵ).continuousWithinAt) (cfun_bdd hV.1 hG') hM hMe

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem useq_zero (hZ0 : ∀ n x, (Z n x).1 0 = ξ x) (x : Ω) (n : ℕ) :
    (useq W Z x n).1 0 = ξ x := by
  rw [show (useq W Z x n).1 0 = (Z n x).1 0 from ustop_apply_of_le (by simp), hZ0]

/-- **The kernel starts at `z`**, for `μ`-a.e. `z`. -/
theorem ae_start_kernel (hW : ∀ n, IsOpen (W n))
    (hZa : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t)) (hZ0 : ∀ n x, (Z n x).1 0 = ξ x)
    (hξ : Measurable[𝓖 0] ξ) :
    ∀ᵐ z ∂(jlaw P ξ (useq W Z)).fst, ∀ n,
      ∀ᵐ ŵ ∂(jlaw P ξ (useq W Z)).condKernel z, (ŵ n).1 0 = z := by
  have hξΦ : Measurable fun x => (ξ x, useq W Z x) :=
    (hξ.mono (𝓖.le 0) le_rfl).prodMk (measurable_useq hW hZa)
  refine ae_all_iff.2 fun n => ?_
  have hS : MeasurableSet {p : (Fin d → ℝ) × CSeq d | (p.2 n).1 0 = p.1} :=
    measurableSet_eq_fun ((measurable_cev 0).comp ((measurable_pi_apply n).comp measurable_snd))
      measurable_fst
  exact ae_ae_condKernel hξΦ hS (ae_of_all _ fun x => useq_zero hZ0 x n)

variable {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}

/-- **The kernel solves the martingale problem in every `W n`**, for `μ`-a.e. start. -/
theorem ae_isMPSolutionOn_kernel (hW : ∀ n, IsOpen (W n))
    (hZ : ∀ n, IsMPSolutionOn P 𝓖 b a (W n) (zproc Z n)) (hZ0 : ∀ n x, (Z n x).1 0 = ξ x)
    (hξ : Measurable[𝓖 0] ξ) (hb : ∀ n, ContinuousOn b (W n)) (ha : ∀ n, ContinuousOn a (W n)) :
    ∀ᵐ z ∂(jlaw P ξ (useq W Z)).fst, ∀ n,
      IsMPSolutionOn ((jlaw P ξ (useq W Z)).condKernel z) (cfilt d) b a (W n) (cY n) ∧
      ∀ᵐ ŵ ∂(jlaw P ξ (useq W Z)).condKernel z, (ŵ n).1 0 = z := by
  have hZa : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t) := fun n t => (hZ n).adapted t
  have hV := fun n k => isInteriorDomain_exh (W n) k
  have hcb : ∀ n k (i : Fin d), ContinuousOn (fun y => b y i) (closure (exh (W n) k)) :=
    fun n k i => (continuous_apply i).comp_continuousOn ((hb n).mono (hV n k).2.2)
  have hca : ∀ n k (i j : Fin d), ContinuousOn (fun y => a y i j) (closure (exh (W n) k)) :=
    fun n k i j => (continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn ((ha n).mono (hV n k).2.2))
  have hD' := fun n k (i : Fin d) => isPathFn_cdrift (hV n k).2.1 (hcb n k i) i
  have hB' := fun n k (i j : Fin d) =>
    isPathFn_cbrk (hV n k).2.1 (hcb n k i) (hcb n k j) (hca n k i j) i j
  have agD : ∀ n k (i : Fin d) s (w : CPath d), (∀ u ≤ s, w.1 u ∈ closure (exh (W n) k)) →
      cdrift (fun y => b y i) i s w.1 =
        cdrift ((closure (exh (W n) k)).indicator fun y => b y i) i s w.1 :=
    fun n k i s w hw => (cdrift_indicator _ i hw).symm
  have agB : ∀ n k (i j : Fin d) s (w : CPath d), (∀ u ≤ s, w.1 u ∈ closure (exh (W n) k)) →
      cbrk (fun y => b y i) (fun y => b y j) (fun y => a y i j) i j s w.1 =
        cbrk ((closure (exh (W n) k)).indicator fun y => b y i)
          ((closure (exh (W n) k)).indicator fun y => b y j)
          ((closure (exh (W n) k)).indicator fun y => a y i j) i j s w.1 :=
    fun n k i j s w hw => (cbrk_indicator _ _ _ i j hw).symm
  have hD : ∀ n k (i : Fin d), ∀ᵐ z ∂(jlaw P ξ (useq W Z)).fst,
      Martingale (cfun n (exh (W n) k) (cdrift (fun y => b y i) i)) (cfilt d)
        ((jlaw P ξ (useq W Z)).condKernel z) := fun n k i =>
    ae_mart_kernel hW hZa hZ0 hξ (hV n k) (fun s _ _ h => cdrift_nonant _ i s h) (hD' n k i)
      (agD n k i) ((hZ n).drift _ (hV n k) i)
  have hB : ∀ n k (i j : Fin d), ∀ᵐ z ∂(jlaw P ξ (useq W Z)).fst,
      Martingale (cfun n (exh (W n) k)
        (cbrk (fun y => b y i) (fun y => b y j) (fun y => a y i j) i j)) (cfilt d)
        ((jlaw P ξ (useq W Z)).condKernel z) := fun n k i j =>
    ae_mart_kernel hW hZa hZ0 hξ (hV n k) (fun s _ _ h => cbrk_nonant _ _ _ i j s h)
      (hB' n k i j) (agB n k i j) ((hZ n).bracket _ (hV n k) i j)
  filter_upwards [ae_all_iff.2 fun n => ae_all_iff.2 fun k => ae_all_iff.2 fun i => hD n k i,
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
      hB n k i j, ae_start_kernel hW hZa hZ0 hξ] with z hd hbr hs n
  have hcov : ∀ K, IsCompact K → K ⊆ W n → ∃ k, K ⊆ exh (W n) k :=
    fun K hK hKU => exists_exh_superset (hW n) hK hKU
  refine ⟨⟨fun t => (measurable_cY n t).stronglyMeasurable, ae_of_all _ fun ŵ => (ŵ n).2,
    fun W' hW' i => ?_, fun W' hW' i j => ?_⟩, hs n⟩
  · exact exists_mart_of_cover (hs n) hcov (cdrift_zero _ i)
      (fun k w h0 => continuous_stop_of_agree (isOpen_exh _ k) (hD' n k i) (agD n k i) h0)
      (fun k => hd n k i) hW'
  · exact exists_mart_of_cover (hs n) hcov (cbrk_zero _ _ _ i j)
      (fun k w h0 => continuous_stop_of_agree (isOpen_exh _ k) (hB' n k i j) (agB n k i j) h0)
      (fun k => hbr n k i j) hW'

theorem pstop_ustop {V : Set (Fin d → ℝ)} (hV : IsOpen V) (t₀ : ℝ≥0) (w : CPath d) :
    pstop V t₀ (ustop V w) = pstop V t₀ w :=
  pstop_congr hV t₀ fun _ hu => ustop_apply_of_le (hu.trans (min_le_left _ _))

/-- The truncated stop sequence of a record. -/
def ctr (W : ℕ → Set (Fin d → ℝ)) (t₀ : ℝ≥0) (ŵ : CSeq d) : ℕ → CPath d :=
  fun n => pstop (W n) t₀ (ŵ n)

theorem measurable_ctr (hW : ∀ n, IsOpen (W n)) (t₀ : ℝ≥0) : Measurable (ctr W t₀) :=
  measurable_pi_iff.2 fun n => (measurable_pstop (hW n) t₀).comp (measurable_pi_apply n)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem ctr_useq (hW : ∀ n, IsOpen (W n)) (t₀ : ℝ≥0) (x : Ω) :
    ctr W t₀ (useq W Z x) = fun n => pstop (W n) t₀ (Z n x) :=
  funext fun n => pstop_ustop (hW n) t₀ (Z n x)

/-- **The stop-sequence relation passes to the kernel.** -/
theorem ae_isStopSeq_kernel (hW : ∀ n, IsOpen (W n))
    (hZa : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t)) (hξ : Measurable[𝓖 0] ξ) (t₀ : ℝ≥0)
    (hst : IsStopSeq P W t₀ fun x n => pstop (W n) t₀ (Z n x)) :
    ∀ᵐ z ∂(jlaw P ξ (useq W Z)).fst,
      IsStopSeq ((jlaw P ξ (useq W Z)).condKernel z) W t₀ (ctr W t₀) := by
  have hξΦ : Measurable fun x => (ξ x, useq W Z x) :=
    (hξ.mono (𝓖.le 0) le_rfl).prodMk (measurable_useq hW hZa)
  have h : ∀ k n, k ≤ n → ∀ᵐ z ∂(jlaw P ξ (useq W Z)).fst,
      ∀ᵐ ŵ ∂(jlaw P ξ (useq W Z)).condKernel z, ctr W t₀ ŵ k = pstop (W k) t₀ (ctr W t₀ ŵ n) := by
    intro k n hkn
    have hS : MeasurableSet {p : (Fin d → ℝ) × CSeq d | ctr W t₀ p.2 k =
        pstop (W k) t₀ (ctr W t₀ p.2 n)} :=
      measurableSet_eq_fun ((measurable_pi_apply k).comp ((measurable_ctr hW t₀).comp
        measurable_snd)) ((measurable_pstop (hW k) t₀).comp ((measurable_pi_apply n).comp
          ((measurable_ctr hW t₀).comp measurable_snd)))
    refine ae_ae_condKernel hξΦ hS ?_
    filter_upwards [hst k n hkn] with x hx
    show ctr W t₀ (useq W Z x) k = pstop (W k) t₀ (ctr W t₀ (useq W Z x) n)
    rw [ctr_useq hW t₀ x]; exact hx
  have h' : ∀ᵐ z ∂(jlaw P ξ (useq W Z)).fst, ∀ k n, k ≤ n →
      ∀ᵐ ŵ ∂(jlaw P ξ (useq W Z)).condKernel z, ctr W t₀ ŵ k = pstop (W k) t₀ (ctr W t₀ ŵ n) := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun n => ?_
    by_cases hkn : k ≤ n
    · filter_upwards [h k n hkn] with z hz _ using hz
    · exact ae_of_all _ fun z h => absurd h hkn
  filter_upwards [h'] with z hz using hz

/-!
## The boundary classification from a random start
-/

/-- A canonical solution started at `z` is a dual stop sequence. -/
theorem isDualStopAt_cY {q : ℕ} {D0 : ℝ} {W : ℕ → Set (Fin (q + q) → ℝ)} {t₀ : ℝ≥0}
    {Q : Measure (CSeq (q + q))} [IsProbabilityMeasure Q] {z : Fin (q + q) → ℝ} {n : ℕ}
    (hmp : IsMPSolutionOn Q (cfilt _) (flatDrift D0 q) (flatDiff D0 q) (W n) (cY n))
    (h0 : ∀ᵐ ŵ ∂Q, (ŵ n).1 0 = z) : IsDualStopAt Q D0 W t₀ z (ctr W t₀) n := by
  refine ⟨cfilt _, cY n, hmp, ?_, fun _ => rfl⟩
  rw [Measure.map_congr (f := cY n 0) (g := fun _ => z) h0, Measure.map_const, measure_univ, one_smul]

/-- **The boundary classification from a random start**: a.s. on `{ξ ∈ flatBox (q+1) n₀}`, the
truncated stop sequence of a level-`(q+1)` flat dual solution from the random start `ξ` is in
`goodSeq`. -/
theorem ae_goodSeq_of_randomStart {D0 : ℝ} (hD0 : 0 < D0) {q n₀ : ℕ}
    {Z : ℕ → Ω → CPath ((q + 1) + (q + 1))} {ξ : Ω → Fin ((q + 1) + (q + 1)) → ℝ}
    (hZ : ∀ n, IsMPSolutionOn P 𝓖 (flatDrift D0 (q + 1)) (flatDiff D0 (q + 1))
      (boxExh (q + 1) n₀ n) (zproc Z n))
    (hZ0 : ∀ n x, (Z n x).1 0 = ξ x) (hξ : Measurable[𝓖 0] ξ) (t₀ : ℝ≥0)
    (hst : IsStopSeq P (boxExh (q + 1) n₀) t₀ fun x n => pstop (boxExh (q + 1) n₀ n) t₀ (Z n x)) :
    ∀ᵐ x ∂P, ξ x ∈ flatBox (q + 1) n₀ →
      (fun n => pstop (boxExh (q + 1) n₀ n) t₀ (Z n x)) ∈ goodSeq q (boxExh (q + 1) n₀) t₀ := by
  set W := boxExh (q + 1) n₀
  have hE := isExh_boxExh (q + 1) n₀
  have hW : ∀ n, IsOpen (W n) := hE.isOpen
  have hZa : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t) := fun n t => (hZ n).adapted t
  have hb : ∀ n, ContinuousOn (flatDrift D0 (q + 1)) (W n) := fun n =>
    (continuousOn_flatDrift D0).mono (subset_closure.trans (hE.dom n).2.2)
  have ha : ∀ n, ContinuousOn (flatDiff D0 (q + 1)) (W n) := fun n =>
    (contDiff_flatDiff D0).continuous.continuousOn
  have hξΦ : Measurable fun x => (ξ x, useq W Z x) :=
    (hξ.mono (𝓖.le 0) le_rfl).prodMk (measurable_useq hW hZa)
  have hgood := measurableSet_goodSeq (q := q) (t₀ := t₀) hW
  have hbox : MeasurableSet (flatBox (q + 1) n₀) := (isInteriorDomain_flatBox _ _).1.measurableSet
  set S := {p : (Fin ((q + 1) + (q + 1)) → ℝ) × CSeq ((q + 1) + (q + 1)) |
    p.1 ∈ flatBox (q + 1) n₀ → ctr W t₀ p.2 ∈ goodSeq q W t₀}
  have hS : MeasurableSet S := by
    have e : S = (Prod.fst ⁻¹' flatBox (q + 1) n₀)ᶜ ∪
        (fun p : (Fin ((q + 1) + (q + 1)) → ℝ) × CSeq ((q + 1) + (q + 1)) =>
          ctr W t₀ p.2) ⁻¹' goodSeq q W t₀ := by
      ext p; simp only [S, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
    rw [e]
    exact (measurable_fst hbox).compl.union (((measurable_ctr hW t₀).comp measurable_snd) hgood)
  have hK : ∀ᵐ z ∂(jlaw P ξ (useq W Z)).fst,
      ∀ᵐ ŵ ∂(jlaw P ξ (useq W Z)).condKernel z, (z, ŵ) ∈ S := by
    filter_upwards [ae_isMPSolutionOn_kernel hW hZ hZ0 hξ hb ha,
      ae_isStopSeq_kernel hW hZa hξ t₀ hst] with z hz hzs
    by_cases hzb : z ∈ flatBox (q + 1) n₀
    · obtain ⟨F⟩ := nonempty_b1Family hD0 z
      obtain ⟨B, hB⟩ := exists_boxRad (q + 1) n₀
      have hr := monotone_majorant B
      have hball : ∀ n, W n ⊆ chartQ (q + 1) '' Metric.ball 0 (majorant B n) := fun n =>
        (hB n).trans (chartQ_ball_mono (le_majorant B n))
      have hz0 : z ∈ W 0 := hzb
      have hz' : z ∈ flatChamber (q + 1) := (hE.dom 0).2.2 (subset_closure hz0)
      have hmap : ((jlaw P ξ (useq W Z)).condKernel z).map (ctr W t₀) =
          (Pq (q + 1)).map (F.stopSeq W t₀ (majorant B)) :=
        map_eq_of_isMPSolutionOn hD0 hE.dom (measurable_ctr hW t₀)
          (F.measurable_stopSeq hW _) hzs (F.isStopSeq_stopSeq hD0 hW hE.mono hr hball)
          (fun n => isDualStopAt_cY (hz n).1 (hz n).2) (F.isDualStopAt hD0 hz' hball)
      have hG := gSeq_all_holds hD0 q z n₀ hzb F (majorant B) hr hball t₀
      rw [ae_mem_iff_map (F.measurable_stopSeq hW _) hgood, ← hmap,
        ← ae_mem_iff_map (measurable_ctr hW t₀) hgood] at hG
      filter_upwards [hG] with ŵ hŵ _ using hŵ
    · exact ae_of_all _ fun ŵ h => absurd h hzb
  filter_upwards [ae_of_ae_condKernel hξΦ hS hK] with x hx hξx
  have := hx hξx
  rwa [ctr_useq hW t₀ x] at this

end BlockBand.Transmission.Dual.G
