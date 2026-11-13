module

public import BlockBand.Transmission.LawDuality.GridDual

/-!
# Duality strip, forward side: the forward steps at a fixed dual point, over the strip

For a fixed realization `ω'` of the dual process, the forward ratio steps of `μ` are evaluated at
the dual point `Z_r(ω')` and integrated over the strip `S_η`.

* `fwdInteg_of_lt`: on `{r < τ}`, `fwdInteg = K_r · ratioDrift(u, Z_r, ν)`;
* **`forward_step`**: on `{r < τ}` (pointwise in `ω'`), for `r ∈ [0, t − a₀]`:
  `1{r<τ}(U(t−r, r) − U(i(r), r))K_r = ∫_{i(r)}^{t−r} A(u, r) du`
  (`integral_ratio_sub_eq` at `z = Z_r(ω')`, then Fubini on `Ω × ℝ`);
* **`integral_forward_strip`**:
  `∫_0^{t−a₀} E'[1{r<τ}(U(t−r, r) − U(i(r), r))K_r] dr = E'∫∫_{S_η} A`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- `U(s, r, ω') = E F_{Z_{r∧τ}(ω')}(μ̌_s)`. -/
def ratioAvg {Ω Ω' : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) (a0 t : ℝ) (N : ℝ≥0 → Ω' → ℕ)
    (X Y : ℝ≥0 → Ω' → ℕ → ℝ) (τ : Ω' → WithTop ℝ≥0) (s r : ℝ) (ω' : Ω') : ℝ :=
  ∫ ω, ratioStop (μ (clampT a0 t s) ω) N X Y τ r ω' ∂P

/-- `A(u, r, ω') = E fwdInteg(u, μ̌_u, r, ω')`. -/
def fwdAvg {Ω Ω' : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) (a0 t D0 E : ℝ) (κ k : ℝ → ℝ)
    (N : ℝ≥0 → Ω' → ℕ) (X Y : ℝ≥0 → Ω' → ℕ → ℝ) (τ : Ω' → WithTop ℝ≥0) (u r : ℝ) (ω' : Ω') : ℝ :=
  ∫ ω, fwdInteg D0 E κ k N X Y τ u (μ (clampT a0 t u) ω) r ω' ∂P

theorem fwdInteg_of_lt {Ω : Type*} (D0 E : ℝ) (κ k : ℝ → ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (τ : Ω → WithTop ℝ≥0) (u : ℝ) (ν : FiniteMeasure unitInterval)
    {v : ℝ} {ω : Ω} (hv : (v.toNNReal : WithTop ℝ≥0) < τ ω) :
    fwdInteg D0 E κ k N X Y τ u ν v ω = killFac k N X Y τ v ω *
      ratioDrift D0 E κ u (dualCoordOf (N v.toNNReal ω) (X v.toNNReal ω) (Y v.toNNReal ω)) ν := by
  have h1 : killInd (τ ω) v = 1 := ite_eq_left_iff.2 fun h' => absurd hv h'
  unfold fwdInteg ratioDrift pathGen pathRatio ratioOn dualTotal
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun i => X v.toNNReal ω i + Y v.toNNReal ω i)]
  simp only [mul_one, dualCoordOf]

theorem fwdInteg_of_not_lt {Ω : Type*} (D0 E : ℝ) (κ k : ℝ → ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (τ : Ω → WithTop ℝ≥0) (u : ℝ) (ν : FiniteMeasure unitInterval)
    {v : ℝ} {ω : Ω} (hv : ¬ (v.toNNReal : WithTop ℝ≥0) < τ ω) :
    fwdInteg D0 E κ k N X Y τ u ν v ω = 0 := by
  have h1 : killInd (τ ω) v = 0 := ite_eq_right_iff.2 fun h' => absurd h' hv
  unfold fwdInteg; rw [h1]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {Ω' : Type*} [m' : MeasurableSpace Ω'] {P' : Measure Ω'} {𝓖 : Filtration ℝ≥0 m'} {D0 : ℝ}
  {p : ℕ} {x y : Fin p → ℝ} {N : ℝ≥0 → Ω' → ℕ} {X Y : ℝ≥0 → Ω' → ℕ → ℝ}
  (h : IsDualDeletionProcess P' 𝓖 D0 x y N X Y)
  (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  (hstart : ∀ ω, N 0 ω = p) {τ : Ω' → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
  {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hU : StaysIn N X Y τ M ε)
  {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ v, 0 ≤ k v)
  {E : ℝ} {κ : ℝ → ℝ} (hκ : Continuous κ) {Ch : ℝ} (hhC : ∀ u, |absorptionRate E κ u| ≤ Ch)
  (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hcont : ∀ ω, ContinuousOn (fun t => μ t ω) (Ioi 0))
  {a0 t : ℝ} (ha0 : 0 < a0) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
  (hCm : ∀ s, Integrable (fun ω => (μ (clampT a0 t s) ω : Measure unitInterval).real univ) P ∧
    ∫ ω, (μ (clampT a0 t s) ω : Measure unitInterval).real univ ∂P ≤ Cm)

include hmeas hcont ha0 h hpath hstart hτ hk hκ in
theorem measurable_fwdInteg_avgArg :
    Measurable fun z : Ω × ((ℝ × ℝ) × Ω') =>
      fwdInteg D0 E κ k N X Y τ z.2.1.1 (μ (clampT a0 t z.2.1.1) z.1) z.2.1.2 z.2.2 :=
  (measurable_fwdInteg_joint h hpath hstart hτ hκ hk).comp
    (f := fun z : Ω × ((ℝ × ℝ) × Ω') =>
      (z.2.1.1, (μ (clampT a0 t z.2.1.1) z.1, (z.2.1.2, z.2.2))))
    ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
      (((measurable_muClamp hmeas hcont ha0).comp (f := fun z : Ω × ((ℝ × ℝ) × Ω') =>
        (z.2.1.1, z.1)) ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
          measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))))

include hmeas hcont ha0 h hpath hstart hτ hk hκ in
theorem measurable_fwdAvg :
    Measurable fun q : (ℝ × ℝ) × Ω' => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1.1 q.1.2 q.2 :=
  ((measurable_fwdInteg_avgArg h hpath hstart hτ hk hκ hmeas hcont
    ha0).stronglyMeasurable.integral_prod_left' (μ := P)).measurable

omit m' in
include hpath hstart hM hε hε1 hU hk0 hhC hCm in
theorem abs_fwdAvg_le (u r : ℝ) (ω' : Ω') :
    |fwdAvg P μ a0 t D0 E κ k N X Y τ u r ω'| ≤ genC D0 p M ε * Cm + Ch * (p * (M + 1)) := by
  have hi : Integrable (fun ω => genC D0 p M ε *
      (μ (clampT a0 t u) ω : Measure unitInterval).real univ + Ch * (p * (M + 1))) P :=
    ((hCm u).1.const_mul _).add (integrable_const _)
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hi (ae_of_all _ fun ω => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact abs_fwdInteg_le hpath hstart hM hε hε1 hU D0 E κ hk0 hhC u _ r ω'
  · rw [integral_add ((hCm u).1.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    have := mul_le_mul_of_nonneg_left (hCm u).2 (genC_nonneg D0 p M ε)
    linarith

include hmeas hcont ha0 hCm in
theorem integrable_massBound_prod (a b c C : ℝ) :
    Integrable (fun z : Ω × ℝ => c * (μ (clampT a0 t z.2) z.1 : Measure unitInterval).real univ + C)
      (P.prod (volume.restrict (Ioc a b))) := by
  have : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hm : Measurable fun z : Ω × ℝ => (μ (clampT a0 t z.2) z.1 : Measure unitInterval).real univ :=
    measurable_mass.comp ((measurable_muClamp hmeas hcont ha0).comp
      (f := fun z : Ω × ℝ => (z.2, z.1)) (measurable_snd.prodMk measurable_fst))
  refine Integrable.add (Integrable.const_mul ?_ c) (integrable_const C)
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun u => (hCm u).1, Integrable.of_bound (C := Cm)
    (hm.norm.stronglyMeasurable.integral_prod_left' (μ := P)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)⟩
  simp_rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  rw [abs_of_nonneg (integral_nonneg fun _ => measureReal_nonneg)]
  exact (hCm u).2

include h hpath hstart hτ hM hε hε1 hU hk hk0 hκ hhC hmeas hcont ha0 hCm in

/-- **The forward step at a fixed dual point** (pointwise in `ω'`). -/
theorem forward_step (hMart : IsRatioMartingale D0 E κ P μ) {η : ℝ}
    (hη : 0 ≤ η) {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ t - a0) (ω' : Ω') :
    killInd (τ ω') r * ((ratioAvg P μ a0 t N X Y τ (t - r) r ω' -
        ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω') * killFac k N X Y τ r ω') =
      ∫ u in max a0 (t - η - r)..t - r, fwdAvg P μ a0 t D0 E κ k N X Y τ u r ω' := by
  set i := max a0 (t - η - r) with hi
  have hi0 : 0 < i := lt_of_lt_of_le ha0 (le_max_left _ _)
  have hit : i ≤ t - r := max_le (by linarith) (by linarith)
  by_cases hlt : (r.toNNReal : WithTop ℝ≥0) < τ ω'
  · have h1 : killInd (τ ω') r = 1 := ite_eq_left_iff.2 fun h' => absurd hlt h'
    set z := dualCoordOf (N r.toNNReal ω') (X r.toNNReal ω') (Y r.toNNReal ω') with hzdef
    have hz : z ∈ dualChamber _ := (hpath ω').chamber r.toNNReal
    have hU' : ∀ s ∈ Icc a0 t, ratioAvg P μ a0 t N X Y τ s r ω' =
        ∫ ω, transmissionRatio z.1 z.2 (μ s ω) ∂P := fun s hs => by
      unfold ratioAvg; rw [clampT_of_mem hs]
      exact integral_congr_ae (ae_of_all _ fun ω => ratioStop_of_lt _ hlt)
    rw [h1, one_mul, hU' (t - r) ⟨by linarith, by linarith⟩, hU' i ⟨le_max_left _ _, by linarith⟩,
      integral_ratio_sub_eq hmeas hMart hz hi0 hit, ← integral_mul_const]
    have e : ∀ ω, (∫ u in i..t - r, ratioDrift D0 E κ u z (μ u ω)) * killFac k N X Y τ r ω' =
        ∫ u in i..t - r, fwdInteg D0 E κ k N X Y τ u (μ (clampT a0 t u) ω) r ω' := fun ω => by
      rw [← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hit] at hu
      rw [clampT_of_mem ⟨le_trans (le_max_left _ _) hu.1, by linarith [hu.2]⟩,
        fwdInteg_of_lt D0 E κ k N X Y τ u _ hlt, mul_comm]
    rw [integral_congr_ae (ae_of_all _ e)]
    simp_rw [intervalIntegral.integral_of_le hit]
    unfold fwdAvg
    refine integral_integral_swap (Integrable.mono'
      (integrable_massBound_prod hmeas hcont ha0 hCm i (t - r) (genC D0 p M ε) (Ch * (p * (M + 1))))
      ((measurable_fwdInteg_avgArg h hpath hstart hτ hk hκ hmeas hcont ha0).comp
        (f := fun z : Ω × ℝ => (z.1, ((z.2, r), ω')))
        (measurable_fst.prodMk ((measurable_snd.prodMk measurable_const).prodMk
          measurable_const))).aestronglyMeasurable
      (ae_of_all _ fun z => ?_))
    rw [Real.norm_eq_abs]
    exact abs_fwdInteg_le hpath hstart hM hε hε1 hU D0 E κ hk0 hhC z.2 _ r ω'
  · have h1 : killInd (τ ω') r = 0 := ite_eq_right_iff.2 fun h' => absurd h' hlt
    have : ∀ u, fwdAvg P μ a0 t D0 E κ k N X Y τ u r ω' = 0 := fun u => by
      unfold fwdAvg; simp [fwdInteg_of_not_lt D0 E κ k N X Y τ u _ hlt]
    simp [h1, this]

include h hpath hstart hτ hM hε hε1 hU hk hk0 hκ hhC hmeas hcont ha0 hCm0 hCm in
/-- **The forward steps (before `τ`) integrated over the strip.** -/
theorem integral_forward_strip (hMart : IsRatioMartingale D0 E κ P μ) (hat : a0 ≤ t) {η : ℝ}
    (hη : 0 ≤ η) :
    ∫ r in (0 : ℝ)..t - a0, (∫ ω', killInd (τ ω') r * ((ratioAvg P μ a0 t N X Y τ (t - r) r ω' -
        ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω') * killFac k N X Y τ r ω') ∂P') =
      ∫ ω', (∫ q, (stripSet a0 t η).indicator
        (fun q => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1 q.2 ω') q ∂(volume.prod volume)) ∂P' := by
  have := h.prob
  have hL : 0 ≤ t - a0 := by linarith
  set S := stripSet a0 t η
  set Cd := genC D0 p M ε * Cm + Ch * (p * (M + 1)) with hCd
  have hCh : 0 ≤ Ch := (abs_nonneg _).trans (hhC 0)
  have hCd0 : 0 ≤ Cd := add_nonneg (mul_nonneg (genC_nonneg D0 p M ε) hCm0)
    (mul_nonneg hCh (by positivity))
  have hDb : ∀ u r ω', |fwdAvg P μ a0 t D0 E κ k N X Y τ u r ω'| ≤ Cd := fun u r ω' =>
    abs_fwdAvg_le (P := P) (μ := μ) hpath hstart hM hε hε1 hU hk0 hhC hCm u r ω'
  have hDm := measurable_fwdAvg (P := P) (t := t) (E := E) (κ := κ) h hpath hstart hτ hk hκ hmeas hcont ha0
  set FA : (ℝ × ℝ) × Ω' → ℝ := fun q => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1.1 q.1.2 q.2
  set H : ℝ → Ω' → ℝ := fun r ω' =>
    ∫ u, S.indicator (fun q => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1 q.2 ω') (u, r) with hH
  have step1 : ∀ r ∈ uIcc 0 (t - a0), (∫ ω', killInd (τ ω') r *
      ((ratioAvg P μ a0 t N X Y τ (t - r) r ω' - ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω') *
        killFac k N X Y τ r ω') ∂P') = ∫ ω', H r ω' ∂P' := by
    intro r hr
    rw [uIcc_of_le hL] at hr
    refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
    beta_reduce
    rw [forward_step h hpath hstart hτ hM hε hε1 hU hk hk0 hκ hhC hmeas hcont ha0 hCm hMart hη
      hr.1 hr.2 ω']
    exact integral_fiber_fwd (fun q => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1 q.2 ω') hr.1 hr.2 hη
  have hHz : ∀ r, r ∉ Icc 0 (t - a0) → ∀ ω', H r ω' = 0 := fun r hr ω' => by
    have : ∀ u, S.indicator (fun q => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1 q.2 ω') (u, r) = 0 :=
      fun u => indicator_of_notMem (notMem_stripSet_fwd hr) _
    simp [hH, this]
  have hG : Measurable fun z : (ℝ × Ω') × ℝ =>
      (S ×ˢ (univ : Set Ω')).indicator FA ((z.2, z.1.1), z.1.2) :=
    (hDm.indicator ((measurableSet_stripSet a0 t η).prod MeasurableSet.univ)).comp
      ((measurable_snd.prodMk (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst))
  have hHm : Measurable (Function.uncurry H) := by
    have e : Function.uncurry H = fun z : ℝ × Ω' =>
        ∫ u, (S ×ˢ (univ : Set Ω')).indicator FA ((u, z.1), z.2) := funext fun z => by
      simp only [Function.uncurry, hH]
      exact integral_congr_ae (ae_of_all _ fun u => indicator_prod_univ S FA (u, z.1) z.2)
    rw [e]; exact (hG.stronglyMeasurable.integral_prod_right').measurable
  have hHi : Integrable (Function.uncurry H) (volume.prod P') :=
    Integrable.mono' ((integrable_indicator_Icc_const 0 (t - a0) (Cd * η)).comp_fst P')
      hHm.aestronglyMeasurable (ae_of_all _ fun z =>
        norm_integral_fiber_fwd_le hCd0 (fun q _ => hDb _ _ _) hη z.1)
  rw [intervalIntegral.integral_congr step1, intervalIntegral.integral_of_le hL,
    setIntegral_eq_integral_of_ae_compl_eq_zero ?_]
  · rw [integral_integral_swap hHi]
    refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
    exact (integral_prod_symm _ (integrable_strip (hDm.comp (measurable_id.prodMk measurable_const))
      (fun q => hDb _ _ _) a0 t η)).symm
  · have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with r hr hrI
    have : r ∉ Icc 0 (t - a0) := fun h' => hrI ⟨lt_of_le_of_ne h'.1 (Ne.symm hr), h'.2⟩
    simp only [hHz r this, integral_zero]

end BlockBand.Transmission.LawDuality
