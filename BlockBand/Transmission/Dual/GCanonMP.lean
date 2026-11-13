module

public import BlockBand.Transmission.Dual.GCanon

/-!
# Martingale-problem functionals on the canonical sequence space

* `IsPathFn K G`: a path functional `G s y` (time `s`, path `y`) that is measurable on
  `CPath d`, non-anticipating, continuous in `s` along continuous paths, and bounded on bounded
  time sets for paths that stay in `K` up to `s`. Closed under `-` and `*`; coordinates
  (`K` bounded) and `pint g` (`g` bounded measurable) are path functionals.
* `cdrift g i`, `cbrk gi gj h i j`: the compensated coordinate and the compensated product;
  `mpCompensated b Y i t ω = cdrift (b · i) i t (Y · ω)` by definition.
* `cfun n W G t ŵ = 1{ŵ_n(0) ∈ W} · G(t ∧ τ_W(ŵ_n), ŵ_n)`, the canonical stopped functional,
  cut off by the start. For `IsPathFn (closure W) G`: measurable, `cfilt t`-measurable
  (`min_pexit_congr`), continuous in `t`, bounded on bounded time sets — the hypotheses of
  `ae_martingale_condKernel`. `cfun_congr`: `G` may be replaced by a functional that agrees with
  it on paths in `closure W` (this is how the singular drift is cut to a bounded one).
* `ustop W w` (untruncated stopped path) and **`cfun_ustop`**: if `ŵ_n = w^{τ_W}` and
  `W' ⊆ W`, then `cfun n W' G t ŵ = 1{w(0) ∈ W'} · G(t ∧ τ_{W'}(w), w)`; hence the canonical
  functional at the stopped paths of a process is the cut-off stopped process.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {d : ℕ}

/-!
## Path functionals
-/

/-- A path functional usable on the canonical space. -/
structure IsPathFn (K : Set (Fin d → ℝ)) (G : ℝ≥0 → (ℝ≥0 → Fin d → ℝ) → ℝ) : Prop where
  meas : ∀ s, Measurable fun w : CPath d => G s w.1
  nonant : ∀ s (y y' : ℝ≥0 → Fin d → ℝ), (∀ u ≤ s, y u = y' u) → G s y = G s y'
  cont : ∀ w : CPath d, Continuous fun s => G s w.1
  bdd : ∀ T : ℝ≥0, ∃ C, ∀ s ≤ T, ∀ w : CPath d, (∀ u ≤ s, w.1 u ∈ K) → |G s w.1| ≤ C

variable {K : Set (Fin d → ℝ)} {G G' : ℝ≥0 → (ℝ≥0 → Fin d → ℝ) → ℝ}

theorem IsPathFn.sub (hG : IsPathFn K G) (hG' : IsPathFn K G') :
    IsPathFn K fun s y => G s y - G' s y where
  meas s := (hG.meas s).sub (hG'.meas s)
  nonant s y y' h := by rw [hG.nonant s y y' h, hG'.nonant s y y' h]
  cont w := (hG.cont w).sub (hG'.cont w)
  bdd T := by
    obtain ⟨C, hC⟩ := hG.bdd T
    obtain ⟨C', hC'⟩ := hG'.bdd T
    exact ⟨C + C', fun s hs w hw => (abs_sub _ _).trans (add_le_add (hC s hs w hw) (hC' s hs w hw))⟩

theorem IsPathFn.mul (hG : IsPathFn K G) (hG' : IsPathFn K G') :
    IsPathFn K fun s y => G s y * G' s y where
  meas s := (hG.meas s).mul (hG'.meas s)
  nonant s y y' h := by rw [hG.nonant s y y' h, hG'.nonant s y y' h]
  cont w := (hG.cont w).mul (hG'.cont w)
  bdd T := by
    obtain ⟨C, hC⟩ := hG.bdd T
    obtain ⟨C', hC'⟩ := hG'.bdd T
    refine ⟨C * C', fun s hs w hw => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (hC s hs w hw) (hC' s hs w hw) (abs_nonneg _)
      ((abs_nonneg _).trans (hC s hs w hw))

theorem exists_coord_bound (hK : Bornology.IsBounded K) :
    ∃ R, ∀ x ∈ K, ∀ i : Fin d, |x i| ≤ R := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  exact ⟨R, fun x hx i => (Real.norm_eq_abs (x i) ▸ norm_le_pi_norm x i).trans (hR x hx)⟩

/-- The coordinate at the current time. -/
theorem isPathFn_coord (hK : Bornology.IsBounded K) (i : Fin d) :
    IsPathFn K fun s y => y s i where
  meas s := (measurable_pi_apply i).comp (measurable_cev s)
  nonant s y y' h := by rw [h s le_rfl]
  cont w := (continuous_apply i).comp w.2
  bdd T := by
    obtain ⟨R, hR⟩ := exists_coord_bound hK
    exact ⟨R, fun s _ w hw => hR _ (hw s le_rfl) i⟩

/-- The coordinate at time `0`. -/
theorem isPathFn_coord0 (hK : Bornology.IsBounded K) (i : Fin d) :
    IsPathFn K fun _ y => y 0 i where
  meas _ := (measurable_pi_apply i).comp (measurable_cev 0)
  nonant s y y' h := by rw [h 0 zero_le]
  cont _ := continuous_const
  bdd T := by
    obtain ⟨R, hR⟩ := exists_coord_bound hK
    exact ⟨R, fun s _ w hw => hR _ (hw 0 zero_le) i⟩

/-- The time integral `∫_{(0,t]} g(y_s) ds`. -/
def pint (g : (Fin d → ℝ) → ℝ) (t : ℝ≥0) (y : ℝ≥0 → Fin d → ℝ) : ℝ :=
  ∫ s in Ioc (0 : ℝ) t, g (y s.toNNReal)

theorem pint_congr (g : (Fin d → ℝ) → ℝ) {s : ℝ≥0} {y y' : ℝ≥0 → Fin d → ℝ}
    (h : ∀ u ≤ s, y u = y' u) : pint g s y = pint g s y' := by
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  show g (y u.toNNReal) = g (y' u.toNNReal)
  rw [h _ (Real.toNNReal_le_iff_le_coe.2 hu.2)]

/-- `pint` with an integrand that agrees with `g` on a set containing the path. -/
theorem pint_congr_fun {g g' : (Fin d → ℝ) → ℝ} {s : ℝ≥0} {y : ℝ≥0 → Fin d → ℝ}
    (h : ∀ u ≤ s, g (y u) = g' (y u)) : pint g s y = pint g' s y :=
  setIntegral_congr_fun measurableSet_Ioc fun _ hu => h _ (Real.toNNReal_le_iff_le_coe.2 hu.2)

theorem isPathFn_pint {g : (Fin d → ℝ) → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    IsPathFn K (pint g) where
  meas s := by
    have hf : Measurable fun p : CPath d × ℝ => g (p.1.1 p.2.toNNReal) :=
      hg.comp (measurable_eval_cpath.comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
    exact (hf.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Ioc 0 s))).measurable
  nonant s y y' h := pint_congr g h
  cont w := by
    have hm : Measurable fun s : ℝ => g (w.1 s.toNNReal) :=
      hg.comp ((w.2.measurable).comp measurable_real_toNNReal)
    have hi : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => g (w.1 s.toNNReal)) volume a b :=
      fun a b => (intervalIntegrable_const (c := B)).mono_fun' hm.aestronglyMeasurable
        (ae_of_all _ fun s => by show ‖_‖ ≤ B; rw [Real.norm_eq_abs]; exact hB _)
    have he : (fun s : ℝ≥0 => pint g s w.1) =
        fun s : ℝ≥0 => ∫ u in (0 : ℝ)..s, g (w.1 u.toNNReal) := by
      funext s; rw [intervalIntegral.integral_of_le s.coe_nonneg]; rfl
    rw [he]
    exact (intervalIntegral.continuous_primitive hi 0).comp NNReal.continuous_coe
  bdd T := by
    refine ⟨B * T, fun s hs w _ => ?_⟩
    have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
      (s := Ioc (0 : ℝ) s) (f := fun u : ℝ => g (w.1 u.toNNReal)) (C := B) measure_Ioc_lt_top
      (fun u _ => by rw [Real.norm_eq_abs]; exact hB _)
    rw [Real.norm_eq_abs, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal s.coe_nonneg] at h
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    exact h.trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hs) hB0)

/-!
## Compensated coordinates and products
-/

/-- The compensated coordinate `y_t^i − y_0^i − ∫_0^t g(y_s) ds`. -/
def cdrift (g : (Fin d → ℝ) → ℝ) (i : Fin d) (t : ℝ≥0) (y : ℝ≥0 → Fin d → ℝ) : ℝ :=
  y t i - y 0 i - pint g t y

/-- The compensated product `M^i M^j − ∫_0^t h(y_s) ds`. -/
def cbrk (gi gj h : (Fin d → ℝ) → ℝ) (i j : Fin d) (t : ℝ≥0) (y : ℝ≥0 → Fin d → ℝ) : ℝ :=
  cdrift gi i t y * cdrift gj j t y - pint h t y

theorem mpCompensated_eq_cdrift {Ω : Type*} (b : (Fin d → ℝ) → Fin d → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (i : Fin d) (t : ℝ≥0) (ω : Ω) :
    mpCompensated b Y i t ω = cdrift (fun x => b x i) i t (fun s => Y s ω) := rfl

theorem bracket_eq_cbrk {Ω : Type*} (b : (Fin d → ℝ) → Fin d → ℝ)
    (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ) (i j : Fin d)
    (t : ℝ≥0) (ω : Ω) :
    (mpCompensated b Y i t ω * mpCompensated b Y j t ω -
      ∫ s in Set.Ioc (0 : ℝ) t, a (Y s.toNNReal ω) i j) =
      cbrk (fun x => b x i) (fun x => b x j) (fun x => a x i j) i j t (fun s => Y s ω) := rfl

theorem cdrift_zero (g : (Fin d → ℝ) → ℝ) (i : Fin d) (y : ℝ≥0 → Fin d → ℝ) :
    cdrift g i 0 y = 0 := by
  simp [cdrift, pint]

theorem cbrk_zero (gi gj h : (Fin d → ℝ) → ℝ) (i j : Fin d) (y : ℝ≥0 → Fin d → ℝ) :
    cbrk gi gj h i j 0 y = 0 := by
  simp [cbrk, cdrift_zero, pint]

theorem cdrift_nonant (g : (Fin d → ℝ) → ℝ) (i : Fin d) (s : ℝ≥0) {y y' : ℝ≥0 → Fin d → ℝ}
    (h : ∀ u ≤ s, y u = y' u) : cdrift g i s y = cdrift g i s y' := by
  rw [cdrift, cdrift, h s le_rfl, h 0 zero_le, pint_congr g h]

theorem cbrk_nonant (gi gj hh : (Fin d → ℝ) → ℝ) (i j : Fin d) (s : ℝ≥0)
    {y y' : ℝ≥0 → Fin d → ℝ} (h : ∀ u ≤ s, y u = y' u) :
    cbrk gi gj hh i j s y = cbrk gi gj hh i j s y' := by
  rw [cbrk, cbrk, cdrift_nonant gi i s h, cdrift_nonant gj j s h, pint_congr hh h]

/-- Cutting the integrand to `K` changes nothing on paths in `K`. -/
theorem cdrift_indicator (g : (Fin d → ℝ) → ℝ) (i : Fin d) {s : ℝ≥0} {y : ℝ≥0 → Fin d → ℝ}
    (hy : ∀ u ≤ s, y u ∈ K) : cdrift (K.indicator g) i s y = cdrift g i s y := by
  rw [cdrift, cdrift, pint_congr_fun fun u hu => indicator_of_mem (hy u hu) g]

theorem cbrk_indicator (gi gj hh : (Fin d → ℝ) → ℝ) (i j : Fin d) {s : ℝ≥0}
    {y : ℝ≥0 → Fin d → ℝ} (hy : ∀ u ≤ s, y u ∈ K) :
    cbrk (K.indicator gi) (K.indicator gj) (K.indicator hh) i j s y = cbrk gi gj hh i j s y := by
  rw [cbrk, cbrk, cdrift_indicator gi i hy, cdrift_indicator gj j hy,
    pint_congr_fun fun u hu => indicator_of_mem (hy u hu) hh]

/-- A function continuous on a compact set, cut to it, is bounded and measurable. -/
theorem indicator_bdd_meas {g : (Fin d → ℝ) → ℝ} (hK : IsCompact K) (hg : ContinuousOn g K) :
    Measurable (K.indicator g) ∧ ∃ B, ∀ x, |K.indicator g x| ≤ B := by
  classical
  refine ⟨?_, ?_⟩
  · rw [← piecewise_eq_indicator]
    exact hg.measurable_piecewise continuousOn_const hK.isClosed.measurableSet
  · obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hg
    refine ⟨max B 0, fun x => ?_⟩
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, ← Real.norm_eq_abs]; exact (hB x hx).trans (le_max_left _ _)
    · rw [indicator_of_notMem hx, abs_zero]; exact le_max_right _ _

theorem isPathFn_cdrift {g : (Fin d → ℝ) → ℝ} (hK : IsCompact K) (hg : ContinuousOn g K)
    (i : Fin d) : IsPathFn K (cdrift (K.indicator g) i) := by
  obtain ⟨hm, B, hB⟩ := indicator_bdd_meas hK hg
  exact ((isPathFn_coord hK.isBounded i).sub (isPathFn_coord0 hK.isBounded i)).sub
    (isPathFn_pint hm hB)

theorem isPathFn_cbrk {gi gj hh : (Fin d → ℝ) → ℝ} (hK : IsCompact K) (hgi : ContinuousOn gi K)
    (hgj : ContinuousOn gj K) (hh' : ContinuousOn hh K) (i j : Fin d) :
    IsPathFn K (cbrk (K.indicator gi) (K.indicator gj) (K.indicator hh) i j) := by
  obtain ⟨hm, B, hB⟩ := indicator_bdd_meas hK hh'
  exact ((isPathFn_cdrift hK hgi i).mul (isPathFn_cdrift hK hgj j)).sub (isPathFn_pint hm hB)

/-!
## The canonical stopped functional
-/

theorem stopTime_congr {τ τ' : WithTop ℝ≥0} {t : ℝ≥0}
    (h : min τ (t : WithTop ℝ≥0) = min τ' t) : stopTime τ t = stopTime τ' t := by
  unfold stopTime; rw [min_comm, h, min_comm]

theorem coe_stopTime_le_tau (τ : WithTop ℝ≥0) (t : ℝ≥0) : (stopTime τ t : WithTop ℝ≥0) ≤ τ := by
  induction τ with
  | top => exact le_top
  | coe s₀ => rw [stopTime_coe]; exact WithTop.coe_le_coe.2 (min_le_right _ _)

/-- A continuous path started in the open `W` stays in `closure W` up to its exit. -/
theorem mem_closure_of_le_pexit {W : Set (Fin d → ℝ)} (hW : IsOpen W) {w : CPath d}
    (h0 : w.1 0 ∈ W) {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) ≤ pexit W w) : w.1 u ∈ closure W := by
  have := stop_mem_closure (Y := cev d) (ω := w) hW w.2 h0 u
  rwa [show exitTimeFrom W (cev d) w = pexit W w from rfl, stopTime_of_le hu] at this

/-- The canonical stopped functional `1{ŵ_n(0) ∈ W} · G(t ∧ τ_W(ŵ_n), ŵ_n)`. -/
def cfun (n : ℕ) (W : Set (Fin d → ℝ)) (G : ℝ≥0 → (ℝ≥0 → Fin d → ℝ) → ℝ) (t : ℝ≥0) :
    CSeq d → ℝ :=
  {ŵ : CSeq d | (ŵ n).1 0 ∈ W}.indicator fun ŵ => G (stopTime (pexit W (ŵ n)) t) (ŵ n).1

variable {W : Set (Fin d → ℝ)} {n : ℕ}

theorem measurableSet_start (hW : IsOpen W) (n : ℕ) :
    MeasurableSet {ŵ : CSeq d | (ŵ n).1 0 ∈ W} :=
  ((measurable_cev (d := d) 0).comp (measurable_pi_apply n)) hW.measurableSet

/-- Agreement on paths in `closure W` suffices. -/
theorem cfun_congr (hW : IsOpen W)
    (h : ∀ s (w : CPath d), (∀ u ≤ s, w.1 u ∈ closure W) → G s w.1 = G' s w.1) :
    cfun n W G = cfun n W G' := by
  funext t ŵ
  by_cases hŵ : (ŵ n).1 0 ∈ W
  · simp only [cfun, indicator_of_mem (show ŵ ∈ {ŵ : CSeq d | (ŵ n).1 0 ∈ W} from hŵ)]
    refine h _ _ fun u hu => mem_closure_of_le_pexit hW hŵ ?_
    exact (WithTop.coe_le_coe.2 hu).trans (coe_stopTime_le_tau _ _)
  · simp only [cfun, indicator_of_notMem (show ŵ ∉ {ŵ : CSeq d | (ŵ n).1 0 ∈ W} from hŵ)]

theorem measurable_cfun (hW : IsOpen W) (hG : IsPathFn K G) (t : ℝ≥0) :
    Measurable (cfun n W G t) := by
  have hu : Measurable (Function.uncurry fun s (w : CPath d) => G s w.1) :=
    measurable_uncurry_of_continuous_of_measurable hG.cont hG.meas
  have hn : Measurable fun ŵ : CSeq d => ŵ n := measurable_pi_apply n
  have hs : Measurable fun ŵ : CSeq d => stopTime (pexit W (ŵ n)) t :=
    Measurable.untopA (measurable_const.min ((measurable_pexit hW).comp hn))
  exact (hu.comp (hs.prodMk hn)).indicator (measurableSet_start hW n)

theorem cfun_ctrunc (hW : IsOpen W) (hG : IsPathFn K G) (t : ℝ≥0) (ŵ : CSeq d) :
    cfun n W G t (ctrunc t ŵ) = cfun n W G t ŵ := by
  have h0 : (ctrunc t ŵ n).1 0 = (ŵ n).1 0 := by
    show (ŵ n).1 (min 0 t) = _; rw [min_eq_left zero_le]
  have hm : min (pexit W (ctrunc t ŵ n)) t = min (pexit W (ŵ n)) t :=
    min_pexit_congr hW t fun u hu => by
      show (ŵ n).1 (min u t) = _
      rw [min_eq_left (WithTop.coe_le_coe.1 (hu.trans (min_le_right _ _)))]
  have hst := stopTime_congr hm
  have hG' : G (stopTime (pexit W (ctrunc t ŵ n)) t) (ctrunc t ŵ n).1 =
      G (stopTime (pexit W (ŵ n)) t) (ŵ n).1 := by
    rw [hst]
    refine hG.nonant _ _ _ fun u hu => ?_
    show (ŵ n).1 (min u t) = _
    rw [min_eq_left (hu.trans (stopTime_le _ _))]
  unfold cfun
  by_cases hŵ : (ŵ n).1 0 ∈ W
  · rw [indicator_of_mem (show ctrunc t ŵ ∈ {ŵ : CSeq d | (ŵ n).1 0 ∈ W} by
        show (ctrunc t ŵ n).1 0 ∈ W; rw [h0]; exact hŵ),
      indicator_of_mem (show ŵ ∈ {ŵ : CSeq d | (ŵ n).1 0 ∈ W} from hŵ)]
    exact hG'
  · rw [indicator_of_notMem (show ctrunc t ŵ ∉ {ŵ : CSeq d | (ŵ n).1 0 ∈ W} by
        show (ctrunc t ŵ n).1 0 ∉ W; rw [h0]; exact hŵ),
      indicator_of_notMem (show ŵ ∉ {ŵ : CSeq d | (ŵ n).1 0 ∈ W} from hŵ)]

/-- **`cfun` is `cfilt`-adapted.** -/
theorem measurable_cfilt_cfun (hW : IsOpen W) (hG : IsPathFn K G) (t : ℝ≥0) :
    Measurable[cfilt d t] (cfun n W G t) :=
  measurable_cfilt_of_eq (measurable_cfun hW hG t) (cfun_ctrunc hW hG t)

/-- **`cfun` is continuous in time.** -/
theorem continuous_cfun (hG : IsPathFn K G) (ŵ : CSeq d) :
    Continuous fun t => cfun n W G t ŵ := by
  by_cases hŵ : (ŵ n).1 0 ∈ W
  · simp only [cfun, indicator_of_mem (show ŵ ∈ {ŵ : CSeq d | (ŵ n).1 0 ∈ W} from hŵ)]
    exact (hG.cont (ŵ n)).comp (continuous_stopTime _)
  · simp only [cfun, indicator_of_notMem (show ŵ ∉ {ŵ : CSeq d | (ŵ n).1 0 ∈ W} from hŵ)]
    exact continuous_const

/-- **`cfun` is bounded on bounded time sets.** -/
theorem cfun_bdd (hW : IsOpen W) (hG : IsPathFn (closure W) G) (T : ℝ≥0) :
    ∃ C, ∀ t ≤ T, ∀ ŵ : CSeq d, |cfun n W G t ŵ| ≤ C := by
  obtain ⟨C, hC⟩ := hG.bdd T
  refine ⟨max C 0, fun t ht ŵ => ?_⟩
  by_cases hŵ : (ŵ n).1 0 ∈ W
  · simp only [cfun, indicator_of_mem (show ŵ ∈ {ŵ : CSeq d | (ŵ n).1 0 ∈ W} from hŵ)]
    refine (hC _ ((stopTime_le _ _).trans ht) _ fun u hu => ?_).trans (le_max_left _ _)
    exact mem_closure_of_le_pexit hW hŵ ((WithTop.coe_le_coe.2 hu).trans (coe_stopTime_le_tau _ _))
  · simp only [cfun, indicator_of_notMem (show ŵ ∉ {ŵ : CSeq d | (ŵ n).1 0 ∈ W} from hŵ),
      abs_zero]
    exact le_max_right _ _

/-!
## Untruncated stopped paths
-/

/-- The untruncated stopped path `t ↦ w(t ∧ τ_W(w))`. -/
def ustop (W : Set (Fin d → ℝ)) (w : CPath d) : CPath d :=
  ⟨fun t => w.1 (stopTime (pexit W w) t), w.2.comp (continuous_stopTime _)⟩

theorem measurable_ustop (hW : IsOpen W) : Measurable (ustop (d := d) W) := by
  refine Measurable.subtype_mk (measurable_pi_iff.2 fun t => ?_)
  have hs : Measurable fun w : CPath d => stopTime (pexit W w) t :=
    Measurable.untopA (measurable_const.min (measurable_pexit hW))
  exact measurable_eval_cpath.comp (hs.prodMk measurable_id)

theorem exists_between_coe {s : ℝ≥0} {b : WithTop ℝ≥0} (h : (s : WithTop ℝ≥0) < b) :
    ∃ t : ℝ≥0, s < t ∧ (t : WithTop ℝ≥0) ≤ b := by
  induction b with
  | top => exact ⟨s + 1, lt_add_one s, le_top⟩
  | coe s' => exact ⟨s', WithTop.coe_lt_coe.1 h, le_rfl⟩

theorem eq_of_forall_min_eq {a b : WithTop ℝ≥0} (h : ∀ t : ℝ≥0, min a t = min b t) : a = b := by
  have key : ∀ a b : WithTop ℝ≥0, (∀ t : ℝ≥0, min a t = min b t) → ¬ a < b := by
    intro a b h hlt
    obtain ⟨s, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    obtain ⟨t, hst, htb⟩ := exists_between_coe hlt
    have := h t
    rw [min_eq_left (WithTop.coe_le_coe.2 hst.le), min_eq_right htb] at this
    exact absurd (WithTop.coe_inj.1 this) (ne_of_lt hst)
  rcases lt_trichotomy a b with hlt | heq | hlt
  · exact absurd hlt (key a b h)
  · exact heq
  · exact absurd hlt (key b a fun t => (h t).symm)

/-- The exit time depends only on the path up to itself. -/
theorem pexit_congr (hW : IsOpen W) {w w' : CPath d}
    (h : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ pexit W w → w'.1 u = w.1 u) :
    pexit W w' = pexit W w :=
  eq_of_forall_min_eq fun t => min_pexit_congr hW t fun u hu => h u (hu.trans (min_le_left _ _))

theorem pexit_le_of_subset {W W' : Set (Fin d → ℝ)} (hWW : W' ⊆ W) (w : CPath d) :
    pexit W' w ≤ pexit W w :=
  le_iInf₂ fun t ht => iInf₂_le t fun h => ht (hWW h)

theorem ustop_apply_of_le {u : ℝ≥0} {w : CPath d} (hu : (u : WithTop ℝ≥0) ≤ pexit W w) :
    (ustop W w).1 u = w.1 u := by
  show w.1 (stopTime _ u) = _; rw [stopTime_of_le hu]

theorem pexit_ustop {W' : Set (Fin d → ℝ)} (hW' : IsOpen W') (hWW : W' ⊆ W) (w : CPath d) :
    pexit W' (ustop W w) = pexit W' w :=
  pexit_congr hW' fun _ hu => ustop_apply_of_le (hu.trans (pexit_le_of_subset hWW w))

open Classical in
/-- **The canonical functional at untruncated stopped paths.** -/
theorem cfun_ustop {W' : Set (Fin d → ℝ)} (hW' : IsOpen W') (hWW : W' ⊆ W)
    (hG : ∀ s (y y' : ℝ≥0 → Fin d → ℝ), (∀ u ≤ s, y u = y' u) → G s y = G s y')
    {ŵ : CSeq d} {w : CPath d} (hŵ : ŵ n = ustop W w) (t : ℝ≥0) :
    cfun n W' G t ŵ = (if w.1 0 ∈ W' then G (stopTime (pexit W' w) t) w.1 else 0) := by
  have h0 : (ŵ n).1 0 = w.1 0 := by rw [hŵ]; exact ustop_apply_of_le (by simp)
  have hp : pexit W' (ŵ n) = pexit W' w := by rw [hŵ]; exact pexit_ustop hW' hWW w
  unfold cfun
  by_cases hw : w.1 0 ∈ W'
  · rw [indicator_of_mem (show ŵ ∈ {ŵ : CSeq d | (ŵ n).1 0 ∈ W'} by
        show (ŵ n).1 0 ∈ W'; rw [h0]; exact hw), ite_eq_left hw, hp]
    refine hG _ _ _ fun u hu => ?_
    rw [hŵ]
    exact ustop_apply_of_le ((WithTop.coe_le_coe.2 hu).trans
      ((coe_stopTime_le_tau _ _).trans (pexit_le_of_subset hWW w)))
  · rw [indicator_of_notMem (show ŵ ∉ {ŵ : CSeq d | (ŵ n).1 0 ∈ W'} by
        show (ŵ n).1 0 ∉ W'; rw [h0]; exact hw), ite_eq_right hw]

end BlockBand.Transmission.Dual.G
