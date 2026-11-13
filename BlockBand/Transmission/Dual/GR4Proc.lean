module

public import BlockBand.Transmission.Dual.GCanonMP
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.OptionalMain

/-!
# Martingales to the conditional kernel: the process side and the kernel-side localization

* `exh U k`: a countable exhaustion of an open `U ⊆ ℝ^d` by interior domains
  (`isInteriorDomain_exh`); every compact subset of `U` lies in some `exh U k`
  (`exists_exh_superset`).
* Process side. `Z n : Ω → CPath d` are the paths of solutions in `W n` (all paths continuous),
  started at the `𝓖₀`-measurable `ξ`; `useq W Z x n = (Z n x)^{τ_{W n}}` is the record of
  untruncated stopped paths. `measurable_ctrunc_useq`: its truncation at `s` is
  `𝓖 s`-measurable (stopped process of a continuous adapted process). **`exists_mart_cfun`**:
  a martingale version of a stopped functional for the domain `V ⊆ W n` gives one for the
  canonical functional at `useq` (cut off by `1{ξ ∈ V}`, `Martingale.indicator_zero`).
* Kernel side. **`exists_mart_of_cover`**: if the canonical functionals for countably many `V k`
  (covering every compact subset of `U`) are martingales under `Q` and `ŵ_n(0) = z` `Q`-a.s.,
  then the stopped functional is a martingale for *every* interior domain `W'` of `U` (optional
  stopping at `τ_{W'} ≤ τ_{V k}`, `exists_martingale_stoppedProcess`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal ENNReal

variable {d : ℕ}

instance (d : ℕ) : Nonempty (CPath d) := ⟨⟨fun _ => 0, continuous_const⟩⟩

/-!
## A countable exhaustion of an open set
-/

/-- `{‖x‖ < k, d(x, Uᶜ) > 1/(k+1)}`. -/
def exh (U : Set (Fin d → ℝ)) (k : ℕ) : Set (Fin d → ℝ) :=
  {x | ‖x‖ < k ∧ ENNReal.ofReal (1 / ((k : ℝ) + 1)) < infEDist x Uᶜ}

theorem isOpen_exh (U : Set (Fin d → ℝ)) (k : ℕ) : IsOpen (exh U k) :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const continuous_infEDist)

theorem closure_exh_subset (U : Set (Fin d → ℝ)) (k : ℕ) : closure (exh U k) ⊆
    {x | ‖x‖ ≤ k ∧ ENNReal.ofReal (1 / ((k : ℝ) + 1)) ≤ infEDist x Uᶜ} :=
  closure_minimal (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
    ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const continuous_infEDist))

theorem isInteriorDomain_exh (U : Set (Fin d → ℝ)) (k : ℕ) :
    IsInteriorDomain (exh U k) U := by
  refine ⟨isOpen_exh U k, ?_, fun x hx => ?_⟩
  · refine (ProperSpace.isCompact_closedBall (0 : Fin d → ℝ) k).of_isClosed_subset
      isClosed_closure fun x hx => ?_
    rw [mem_closedBall_zero_iff]; exact (closure_exh_subset U k hx).1
  · have h := (closure_exh_subset U k hx).2
    by_contra hxU
    have h0 : infEDist x Uᶜ = 0 := infEDist_zero_of_mem hxU
    rw [h0] at h
    exact absurd (le_zero_iff.1 h) (ENNReal.ofReal_pos.2 (by positivity)).ne'

theorem exists_exh_superset {U : Set (Fin d → ℝ)} (hU : IsOpen U) {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) : ∃ k, K ⊆ exh U k := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨k₁, hk₁⟩ := exists_nat_gt R
  obtain ⟨k₂, hk₂⟩ := exists_nat_one_div_lt hδ
  have hk₁' : (k₁ : ℝ) ≤ (max k₁ k₂ : ℕ) := Nat.cast_le.2 (le_max_left _ _)
  refine ⟨max k₁ k₂, fun x hx => ⟨(hR x hx).trans_lt (hk₁.trans_le hk₁'), ?_⟩⟩
  have hk₂' : ((k₂ : ℝ) + 1) ≤ ((max k₁ k₂ : ℕ) : ℝ) + 1 := by
    have := Nat.cast_le (α := ℝ) |>.2 (le_max_right k₁ k₂); linarith
  have hle : (1 / ((max k₁ k₂ : ℕ) + 1 : ℝ)) < δ :=
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hk₂') hk₂
  refine (ENNReal.ofReal_lt_ofReal_iff hδ).2 hle |>.trans_le ?_
  refine le_infEDist.2 fun y hy => ?_
  by_contra hlt
  push Not at hlt
  exact hy (hδU (mem_cthickening_of_edist_le y x δ K hx (by rw [edist_comm]; exact hlt.le)))

/-!
## The process side
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {W : ℕ → Set (Fin d → ℝ)} {Z : ℕ → Ω → CPath d} {ξ : Ω → Fin d → ℝ}

/-- The process of the `n`-th paths. -/
def zproc (Z : ℕ → Ω → CPath d) (n : ℕ) : ℝ≥0 → Ω → Fin d → ℝ := fun t x => (Z n x).1 t

/-- The record of untruncated stopped paths. -/
def useq (W : ℕ → Set (Fin d → ℝ)) (Z : ℕ → Ω → CPath d) (x : Ω) : CSeq d :=
  fun n => ustop (W n) (Z n x)

theorem measurable_useq_eval (hW : ∀ n, IsOpen (W n))
    (hZ : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t)) (n : ℕ) (t : ℝ≥0) :
    Measurable[𝓖 t] fun x => (useq W Z x n).1 t := by
  have hρ : IsStoppingTime 𝓖 (rawHit (W n)ᶜ (zproc Z n)) :=
    isStoppingTime_rawHit fun t => (hZ n t).measurable
  have hs := (StronglyAdapted.stoppedProcess (f := 𝓖) (u := zproc Z n) (hZ n)
    (fun x => (Z n x).2) hρ) t
  have e : stoppedProcess (zproc Z n) (rawHit (W n)ᶜ (zproc Z n)) t =
      fun x => (useq W Z x n).1 t := funext fun x => by
    rw [stoppedProcess_eq_stopTime, rawHit_compl_eq_exitTimeFrom (hW n) (Z n x).2]; rfl
  rw [← e]; exact hs.measurable

theorem measurable_ctrunc_useq (hW : ∀ n, IsOpen (W n))
    (hZ : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t)) (s : ℝ≥0) :
    Measurable[𝓖 s] fun x => ctrunc s (useq W Z x) := by
  refine (@measurable_pi_iff _ _ _ (𝓖 s) _ _).2 fun n =>
    Measurable.subtype_mk ((@measurable_pi_iff _ _ _ (𝓖 s) _ _).2 fun t => ?_)
  exact (measurable_useq_eval hW hZ n (min t s)).mono (𝓖.mono (min_le_right t s)) le_rfl

theorem measurable_useq (hW : ∀ n, IsOpen (W n))
    (hZ : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t)) : Measurable (useq W Z) :=
  measurable_pi_iff.2 fun n => Measurable.subtype_mk (measurable_pi_iff.2 fun t =>
    (measurable_useq_eval hW hZ n t).mono (𝓖.le t) le_rfl)

/-- **The canonical functional at the record has a martingale version.** -/
theorem exists_mart_cfun (hξ : Measurable[𝓖 0] ξ) (hZ0 : ∀ n x, (Z n x).1 0 = ξ x) {n : ℕ}
    {V : Set (Fin d → ℝ)} (hV : IsOpen V) (hVW : V ⊆ W n)
    {G : ℝ≥0 → (ℝ≥0 → Fin d → ℝ) → ℝ}
    (hG : ∀ s (y y' : ℝ≥0 → Fin d → ℝ), (∀ u ≤ s, y u = y' u) → G s y = G s y')
    (hN : ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 P ∧ ∀ t, N t =ᵐ[P]
      stoppedProcess (fun t x => G t (Z n x).1) (exitTimeFrom V (zproc Z n)) t) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 P ∧ ∀ t, M t =ᵐ[P] fun x => cfun n V G t (useq W Z x) := by
  classical
  obtain ⟨N, hN, hNe⟩ := hN
  have hS : MeasurableSet[𝓖 0] {x | ξ x ∈ V} := hξ hV.measurableSet
  refine ⟨fun t => {x | ξ x ∈ V}.indicator (N t), Martingale.indicator_zero hN hS, fun t => ?_⟩
  filter_upwards [hNe t] with x hx
  rw [cfun_ustop hV hVW hG (show useq W Z x n = ustop (W n) (Z n x) from rfl) t, hZ0 n x]
  by_cases h : ξ x ∈ V
  · rw [indicator_of_mem (show x ∈ {x | ξ x ∈ V} from h), ite_eq_left h, hx]; rfl
  · rw [indicator_of_notMem (show x ∉ {x | ξ x ∈ V} from h), ite_eq_right h]

/-!
## The kernel side: from countably many domains to all
-/

/-- The coordinate processes of the canonical space. -/
def cY (n : ℕ) : ℝ≥0 → CSeq d → Fin d → ℝ := fun t ŵ => (ŵ n).1 t

theorem measurable_cY (n : ℕ) (t : ℝ≥0) : Measurable[cfilt d t] (cY n t) :=
  measurable_cfilt_of_eq ((measurable_cev t).comp (measurable_pi_apply n)) fun ŵ => by
    show (ŵ n).1 (min t t) = _; rw [min_self]; rfl

/-- A stopped functional is continuous when it agrees with a path functional on `closure V`. -/
theorem continuous_stop_of_agree {V K : Set (Fin d → ℝ)} (hV : IsOpen V)
    {G G' : ℝ≥0 → (ℝ≥0 → Fin d → ℝ) → ℝ} (hG' : IsPathFn K G')
    (h : ∀ s (w : CPath d), (∀ u ≤ s, w.1 u ∈ closure V) → G s w.1 = G' s w.1)
    {w : CPath d} (h0 : w.1 0 ∈ V) : Continuous fun t => G (stopTime (pexit V w) t) w.1 := by
  have e : (fun t => G (stopTime (pexit V w) t) w.1) = fun t => G' (stopTime (pexit V w) t) w.1 :=
    funext fun t => h _ _ fun u hu => mem_closure_of_le_pexit hV h0
      ((WithTop.coe_le_coe.2 hu).trans (coe_stopTime_le_tau _ _))
  rw [e]; exact (hG'.cont w).comp (continuous_stopTime _)

/-- **Every interior domain, by optional stopping from a countable cover.** -/
theorem exists_mart_of_cover {Q : Measure (CSeq d)} [IsProbabilityMeasure Q] {n : ℕ}
    {z : Fin d → ℝ} (h0 : ∀ᵐ ŵ ∂Q, (ŵ n).1 0 = z) {U : Set (Fin d → ℝ)}
    {V : ℕ → Set (Fin d → ℝ)} (hcov : ∀ K, IsCompact K → K ⊆ U → ∃ k, K ⊆ V k)
    {G : ℝ≥0 → (ℝ≥0 → Fin d → ℝ) → ℝ} (hG0 : ∀ y, G 0 y = 0)
    (hGc : ∀ k (w : CPath d), w.1 0 ∈ V k →
      Continuous fun t => G (stopTime (pexit (V k) w) t) w.1)
    (hmart : ∀ k, Martingale (cfun n (V k) G) (cfilt d) Q) {W' : Set (Fin d → ℝ)}
    (hW' : IsInteriorDomain W' U) :
    ∃ N : ℝ≥0 → CSeq d → ℝ, Martingale N (cfilt d) Q ∧ ∀ t,
      N t =ᵐ[Q] stoppedProcess (fun t ŵ => G t (ŵ n).1) (exitTimeFrom W' (cY n)) t := by
  by_cases hz : z ∈ W'
  · obtain ⟨k, hk⟩ := hcov _ hW'.2.1 hW'.2.2
    have hsub : W' ⊆ V k := subset_closure.trans hk
    have hzk : z ∈ V k := hsub hz
    set Xk := stoppedProcess (fun t (ŵ : CSeq d) => G t (ŵ n).1) (exitTimeFrom (V k) (cY n))
    have hMX : ∀ t, cfun n (V k) G t =ᵐ[Q] Xk t := fun t => by
      filter_upwards [h0] with ŵ h
      rw [cfun, indicator_of_mem (show ŵ ∈ {ŵ : CSeq d | (ŵ n).1 0 ∈ V k} by
        show (ŵ n).1 0 ∈ V k; rw [h]; exact hzk)]
      rfl
    have hc : ∀ᵐ ŵ ∂Q, Continuous fun t => Xk t ŵ := by
      filter_upwards [h0] with ŵ h
      exact hGc k (ŵ n) (by rw [h]; exact hzk)
    have hρ : IsStoppingTime (cfilt d) (rawHit W'ᶜ (cY n)) :=
      isStoppingTime_rawHit fun t => measurable_cY n t
    obtain ⟨M', hM', hM'e⟩ := exists_martingale_stoppedProcess (hmart k) hMX hc hρ
    refine ⟨M', hM', fun t => (hM'e t).trans (Eventually.of_forall fun ŵ => ?_)⟩
    show Xk (stopTime (rawHit W'ᶜ (cY n) ŵ) t) ŵ = G (stopTime (exitTimeFrom W' (cY n) ŵ) t) (ŵ n).1
    rw [rawHit_compl_eq_exitTimeFrom hW'.1 (ŵ n).2]
    show G (stopTime (pexit (V k) (ŵ n)) (stopTime (pexit W' (ŵ n)) t)) (ŵ n).1 =
      G (stopTime (pexit W' (ŵ n)) t) (ŵ n).1
    rw [stopTime_of_le ((coe_stopTime_le_tau _ _).trans (pexit_le_of_subset hsub (ŵ n)))]
  · refine ⟨0, martingale_zero ℝ _ _, fun t => ?_⟩
    filter_upwards [h0] with ŵ h
    have hτ : exitTimeFrom W' (cY n) ŵ ≤ 0 :=
      iInf₂_le (0 : ℝ≥0) (show (ŵ n).1 0 ∉ W' by rw [h]; exact hz)
    have hs : stopTime (exitTimeFrom W' (cY n) ŵ) t = 0 :=
      le_antisymm (WithTop.coe_le_coe.1 ((coe_stopTime_le_tau _ _).trans hτ)) zero_le
    show (0 : ℝ) = G (stopTime (exitTimeFrom W' (cY n) ŵ) t) (ŵ n).1
    rw [hs, hG0]

end BlockBand.Transmission.Dual.G
