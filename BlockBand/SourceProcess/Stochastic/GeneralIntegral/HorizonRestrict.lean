module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.StopIdentity
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Consistency of the general integral across horizons

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, `h : IsL2Integrator Q 𝓖 N α`,
horizons `T ≤ T'`, `ν_T = bracketMeasure Q α T ≤ ν_{T'}` (`bracketMeasure_mono`).

* `predRestrict hle : PredL2 𝓖 μ' →L[ℝ] PredL2 𝓖 μ` for measures `μ ≤ μ'`: the same
  representative, read in `L²(μ)` (norm `≤ 1`; predictability is kept).
* `Rect.clip r T`: the rectangle `r ∩ ((-∞,T] × Ω)` of `Rect 𝓖 T'`, as a rectangle of any
  horizon `T₀ ≥ T` (empty if `r` starts after `T`).
* `stochIntegral_predRestrict`: `∫_0^T (H|_{ν_T}) dN = ∫_0^{T'} 1_{s ≤ T} H dN` in `L²(Q)`
  (uniqueness on rectangles of horizon `T'` and `rectSpan_dense`).
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Restrict

variable (𝓖 : Filtration ℝ≥0 mΩ) {μ μ' : Measure (ℝ × Ω)} (hle : μ ≤ μ')

/-- Reading an `L²(μ')` class in `L²(μ)`, `μ ≤ μ'` (linear map). -/
def restrLin : Lp ℝ 2 μ' →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := ((Lp.memLp f).mono_measure hle).toLp f
  map_add' f g :=
    (MemLp.toLp_congr _ (((Lp.memLp f).mono_measure hle).add ((Lp.memLp g).mono_measure hle))
      ((Lp.coeFn_add f g).filter_mono (ae_mono hle))).trans (MemLp.toLp_add _ _)
  map_smul' c f :=
    (MemLp.toLp_congr _ (((Lp.memLp f).mono_measure hle).const_smul c)
      ((Lp.coeFn_smul c f).filter_mono (ae_mono hle))).trans (MemLp.toLp_const_smul _ _)

theorem norm_restrLin_le (f : Lp ℝ 2 μ') : ‖restrLin hle f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).mono_measure hle).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure _ hle)

/-- Reading an `L²(μ')` class in `L²(μ)` (continuous linear map). -/
def restrCLM : Lp ℝ 2 μ' →L[ℝ] Lp ℝ 2 μ :=
  (restrLin hle).mkContinuous 1 fun f => (norm_restrLin_le hle f).trans_eq (one_mul _).symm

theorem restrCLM_coeFn (f : Lp ℝ 2 μ') : (restrCLM hle f : ℝ × Ω → ℝ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_measure hle)

theorem restrCLM_mem (f : PredL2 𝓖 μ') :
    restrCLM hle (f : Lp ℝ 2 μ') ∈ lpMeas ℝ ℝ (predictableSpace (toCF 𝓖)) 2 μ := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  obtain ⟨g, hg, hfg⟩ := lpMeas.aestronglyMeasurable f
  exact ⟨g, hg, (restrCLM_coeFn hle _).trans (hfg.filter_mono (ae_mono hle))⟩

/-- Restriction of predictable classes to a smaller measure. -/
def predRestrict : PredL2 𝓖 μ' →L[ℝ] PredL2 𝓖 μ :=
  ((restrCLM hle).comp (lpMeas ℝ ℝ (predictableSpace (toCF 𝓖)) 2 μ').subtypeL).codRestrict _
    (restrCLM_mem 𝓖 hle)

theorem predRestrict_coeFn (f : PredL2 𝓖 μ') :
    (((predRestrict 𝓖 hle f : PredL2 𝓖 μ) : Lp ℝ 2 μ) : ℝ × Ω → ℝ) =ᵐ[μ]
      ((f : Lp ℝ 2 μ') : ℝ × Ω → ℝ) :=
  restrCLM_coeFn hle _

theorem predRestrict_predInd {R : Set (ℝ × Ω)} (hR : MeasurableSet[predictableSpace (toCF 𝓖)] R)
    (f : PredL2 𝓖 μ') :
    predRestrict 𝓖 hle (predInd 𝓖 R hR f) = predInd 𝓖 R hR (predRestrict 𝓖 hle f) := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [predRestrict_coeFn 𝓖 hle (predInd 𝓖 R hR f),
    (predInd_coeFn 𝓖 R hR f).filter_mono (ae_mono hle),
    predInd_coeFn 𝓖 R hR (predRestrict 𝓖 hle f), predRestrict_coeFn 𝓖 hle f] with p h1 h2 h3 h4
  rw [h1, h2, h3]
  by_cases hp : p ∈ R
  · rw [indicator_of_mem hp, indicator_of_mem hp, h4]
  · rw [indicator_of_notMem hp, indicator_of_notMem hp]

end Restrict

theorem timeProbMeasure_eq_restrict (Q : Measure Ω) [SFinite Q] {T T' : ℝ≥0} (hT : T ≤ T') :
    timeProbMeasure T Q = (timeProbMeasure T' Q).restrict (Ioc (0 : ℝ) T ×ˢ univ) := by
  rw [timeProbMeasure, timeProbMeasure, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 hT))]

theorem bracketMeasure_mono (Q : Measure Ω) [SFinite Q] (α : ℝ≥0 → Ω → ℝ) {T T' : ℝ≥0}
    (hT : T ≤ T') :
    bracketMeasure Q α T ≤ bracketMeasure Q α T' := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [bracketMeasure, bracketMeasure, withDensity_apply _ hs, withDensity_apply _ hs]
  refine lintegral_mono' (Measure.restrict_mono subset_rfl ?_) le_rfl
  rw [timeProbMeasure_eq_restrict Q hT]
  exact Measure.restrict_le_self

variable {𝓖 : Filtration ℝ≥0 mΩ}

/-- The rectangle `r ∩ ((-∞,T] × Ω)` as a rectangle of horizon `T₀ ≥ T`. -/
def Rect.clip {T' : ℝ≥0} (r : Rect 𝓖 T') (T T₀ : ℝ≥0) (hT : T ≤ T₀) : Rect 𝓖 T₀ :=
  if hs : r.s ≤ T then ⟨r.s, min r.t T, r.A, le_min r.hst hs, (min_le_right _ _).trans hT, r.hA⟩
  else ⟨0, 0, ∅, le_rfl, zero_le, @MeasurableSet.empty Ω (𝓖 0)⟩

theorem Rect.clip_set {T' : ℝ≥0} (r : Rect 𝓖 T') (T T₀ : ℝ≥0) (hT : T ≤ T₀) :
    (r.clip T T₀ hT).set = r.set ∩ (Iic (T : ℝ) ×ˢ univ) := by
  unfold Rect.clip
  split_ifs with hs
  · ext p
    simp only [Rect.set, mem_prod, mem_Ioc, mem_inter_iff, mem_Iic, mem_univ, and_true,
      NNReal.coe_min, le_min_iff]
    tauto
  · ext p
    simp only [Rect.set, Ioc_self, empty_prod, mem_empty_iff_false, false_iff, mem_inter_iff,
      mem_prod, mem_Ioc, mem_Iic, mem_univ, and_true, not_and]
    intro h1 h2
    exact hs (by exact_mod_cast (h1.1.1.trans_le h2).le)

variable {Q : Measure Ω} [IsFiniteMeasure Q] {N α : ℝ≥0 → Ω → ℝ}

namespace IsL2Integrator

variable (h : IsL2Integrator Q 𝓖 N α) {T T' : ℝ≥0} (hT : T ≤ T')

/-- **Horizon restriction of the terminal integral.** -/
theorem stochIntegral_predRestrict (K : PredL2 𝓖 (bracketMeasure Q α T')) :
    h.stochIntegral T (predRestrict 𝓖 (bracketMeasure_mono Q α hT) K) =
      h.stochIntegral T' (predInd 𝓖 _ (measurableSet_Iic_prod_univ 𝓖 T) K) := by
  have := h.isFiniteMeasure_bracketMeasure T
  have := h.isFiniteMeasure_bracketMeasure T'
  have hle := bracketMeasure_mono Q α hT
  let L₁ := (h.stochIntegral T).toContinuousLinearMap.comp (predRestrict 𝓖 hle)
  let L₂ := (h.stochIntegral T').toContinuousLinearMap.comp
    (predInd 𝓖 _ (measurableSet_Iic_prod_univ 𝓖 T))
  suffices hL : L₁ = L₂ from congrArg (fun L => L K) hL
  refine ContinuousLinearMap.ext_on (s := range (rectL2 𝓖 T' (bracketMeasure Q α T')))
    (rectSpan_dense 𝓖 T' (bracketMeasure_ae_mem Q α T')) ?_
  rintro _ ⟨r, rfl⟩
  have h1 : predRestrict 𝓖 hle (rectL2 𝓖 T' (bracketMeasure Q α T') r) =
      rectL2 𝓖 T (bracketMeasure Q α T) (r.clip T T le_rfl) := by
    refine predL2_ext 𝓖 ?_
    filter_upwards [predRestrict_coeFn 𝓖 hle (rectL2 𝓖 T' (bracketMeasure Q α T') r),
      (indicatorConstLp_coeFn (p := 2) (hs := r.measurableSet) (c := (1 : ℝ))
        (hμs := measure_ne_top (bracketMeasure Q α T') _)).filter_mono (ae_mono hle),
      indicatorConstLp_coeFn (p := 2) (hs := (r.clip T T le_rfl).measurableSet) (c := (1 : ℝ))
        (hμs := measure_ne_top (bracketMeasure Q α T) _), bracketMeasure_ae_mem Q α T]
      with p h1 h2 h3 hp
    rw [h1, rectL2_coe, rectL2_coe, indLp, indLp, h2, h3, Rect.clip_set]
    have hpT : p ∈ Iic (T : ℝ) ×ˢ (univ : Set Ω) := ⟨hp.2, mem_univ _⟩
    by_cases hr : p ∈ r.set
    · rw [indicator_of_mem hr, indicator_of_mem
        (show p ∈ r.set ∩ (Iic (T : ℝ) ×ˢ (univ : Set Ω)) from ⟨hr, hpT⟩)]
    · rw [indicator_of_notMem hr, indicator_of_notMem fun hh => hr hh.1]
  have h2 : predInd 𝓖 _ (measurableSet_Iic_prod_univ 𝓖 T) (rectL2 𝓖 T' (bracketMeasure Q α T') r) =
      rectL2 𝓖 T' (bracketMeasure Q α T') (r.clip T T' hT) := by
    refine predL2_ext 𝓖 ?_
    filter_upwards [predInd_coeFn 𝓖 _ (measurableSet_Iic_prod_univ 𝓖 T)
        (rectL2 𝓖 T' (bracketMeasure Q α T') r),
      indicatorConstLp_coeFn (p := 2) (hs := r.measurableSet) (c := (1 : ℝ))
        (hμs := measure_ne_top (bracketMeasure Q α T') _),
      indicatorConstLp_coeFn (p := 2) (hs := (r.clip T T' hT).measurableSet) (c := (1 : ℝ))
        (hμs := measure_ne_top (bracketMeasure Q α T') _)] with p h1 h2 h3
    rw [h1, rectL2_coe, rectL2_coe, indLp, indLp, h3, Rect.clip_set]
    by_cases hpT : p ∈ Iic (T : ℝ) ×ˢ (univ : Set Ω)
    · rw [indicator_of_mem hpT, h2]
      by_cases hr : p ∈ r.set
      · rw [indicator_of_mem hr, indicator_of_mem
          (show p ∈ r.set ∩ (Iic (T : ℝ) ×ˢ (univ : Set Ω)) from ⟨hr, hpT⟩)]
      · rw [indicator_of_notMem hr, indicator_of_notMem fun hh => hr hh.1]
    · rw [indicator_of_notMem hpT, indicator_of_notMem fun hh => hpT hh.2]
  change h.stochIntegral T (predRestrict 𝓖 hle (rectL2 𝓖 T' (bracketMeasure Q α T') r)) =
    h.stochIntegral T' (predInd 𝓖 _ (measurableSet_Iic_prod_univ 𝓖 T)
      (rectL2 𝓖 T' (bracketMeasure Q α T') r))
  rw [h1, h2]
  refine Lp.ext ((h.stochIntegral_rect T _).trans ((h.stochIntegral_rect T' _).trans ?_).symm)
  unfold Rect.clip
  split_ifs <;> rfl

/-- **Horizon consistency**: for `t ≤ T ≤ T'`, `∫_0^t H dN` is the same a.s. at horizon `T'`
and at horizon `T` (integrand `H` read in `L²(ν_T)`). -/
theorem contIntegral_horizon (H : PredL2 𝓖 (bracketMeasure Q α T')) {t : ℝ≥0} (ht : t ≤ T) :
    h.contIntegral T' H t =ᵐ[Q]
      h.contIntegral T (predRestrict 𝓖 (bracketMeasure_mono Q α hT) H) t := by
  have hle := bracketMeasure_mono Q α hT
  have e1 := h.stochIntegral_predInd_Iic T' H t
  have e2 := h.stochIntegral_predInd_Iic T (predRestrict 𝓖 hle H) t
  have hset : Iic (T : ℝ) ×ˢ (univ : Set Ω) ∩ Iic (t : ℝ) ×ˢ univ = Iic (t : ℝ) ×ˢ univ := by
    rw [prod_inter_prod, inter_univ, inter_eq_right.2 (Iic_subset_Iic.2 (by exact_mod_cast ht))]
  have e3 : predInd 𝓖 _ (measurableSet_Iic_prod_univ 𝓖 t) H =
      predInd 𝓖 _ (measurableSet_Iic_prod_univ 𝓖 T)
        (predInd 𝓖 _ (measurableSet_Iic_prod_univ 𝓖 t) H) := by
    rw [predInd_predInd]
    exact predInd_congr 𝓖 _ _ (by rw [hset]) H
  rw [e3, ← h.stochIntegral_predRestrict hT, predRestrict_predInd] at e1
  exact e1.symm.trans e2

/-- Horizon consistency a.s. simultaneously for all `t ≤ T`. -/
theorem contIntegral_horizon_all (H : PredL2 𝓖 (bracketMeasure Q α T')) :
    ∀ᵐ ω ∂Q, ∀ t ≤ T, h.contIntegral T' H t ω =
      h.contIntegral T (predRestrict 𝓖 (bracketMeasure_mono Q α hT) H) t ω := by
  have hall := ae_forall_eq_of_continuous
    (X := fun t => h.contIntegral T' H (min t T))
    (Y := fun t => h.contIntegral T (predRestrict 𝓖 (bracketMeasure_mono Q α hT) H) (min t T))
    (by filter_upwards [h.contIntegral_continuous T' H] with ω hω
        exact hω.comp (continuous_id.min continuous_const))
    (by filter_upwards [h.contIntegral_continuous T _] with ω hω
        exact hω.comp (continuous_id.min continuous_const))
    (fun t => h.contIntegral_horizon hT H (min_le_right t T))
  filter_upwards [hall] with ω hω t ht
  simpa only [min_eq_left ht] using hω t

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
