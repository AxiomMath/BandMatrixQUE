module

public import BlockBand.Transmission.LawDuality.GridBound
public import BlockBand.Transmission.LawDuality.GridStripSet

/-!
# The strip estimate, dual side: the dual steps integrated over the strip

Forward process `μ` (all paths continuous, mass bound), normalized dual stopped at `τ` with
`StaysIn N X Y τ M ε`, killing `0 ≤ k ≤ C_k`, forward time clamped to `[a₀, t]`. With
`V(s, r) = E'[(E F_{Z_{r∧τ}}(μ̌_s))K_r]` (`stripV`) and `D(s, v, ω') = E dualInteg(μ̌_s, v, ω')`
(`dualAvg`):
* `integral_ratioKill_sub`: `integral_killed_dual` between two dual times, fixed `ν`;
* **`stripV_sub`**: `V(s, r) − V(s, r') = E'∫_{r'}^r D(s, v) dv` (Fubini on `Ω × Ω' × ℝ`);
* **`integral_stripV_dual`**: `∫_{a₀}^t [V(s, t−s) − V(s, m(s))] ds = E'∫∫_{S_η} D`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- `V(s, r) = E'[(E F_{Z_{r∧τ}}(μ̌_s)) K_r]`. -/
def stripV {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) (a0 t : ℝ) (P' : Measure Ω') (k : ℝ → ℝ)
    (N : ℝ≥0 → Ω' → ℕ) (X Y : ℝ≥0 → Ω' → ℕ → ℝ) (τ : Ω' → WithTop ℝ≥0) (s r : ℝ) : ℝ :=
  ∫ ω', (∫ ω, ratioStop (μ (clampT a0 t s) ω) N X Y τ r ω' ∂P) * killFac k N X Y τ r ω' ∂P'

/-- `D(s, v, ω') = E dualInteg(μ̌_s, v, ω')`. -/
def dualAvg {Ω Ω' : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) (a0 t D0 : ℝ) (k : ℝ → ℝ) (N : ℝ≥0 → Ω' → ℕ)
    (X Y : ℝ≥0 → Ω' → ℕ → ℝ) (τ : Ω' → WithTop ℝ≥0) (s v : ℝ) (ω' : Ω') : ℝ :=
  ∫ ω, dualInteg D0 k N X Y τ (μ (clampT a0 t s) ω) v ω' ∂P

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {Ω' : Type*} [m' : MeasurableSpace Ω'] {P' : Measure Ω'} {𝓖 : Filtration ℝ≥0 m'} {D0 : ℝ}
  {p : ℕ} {x y : Fin p → ℝ} {N : ℝ≥0 → Ω' → ℕ} {X Y : ℝ≥0 → Ω' → ℕ → ℝ}
  (h : IsDualDeletionProcess P' 𝓖 D0 x y N X Y)
  (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  (hstart : ∀ ω, N 0 ω = p) {τ : Ω' → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
  {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hU : StaysIn N X Y τ M ε)
  {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ v, 0 ≤ k v) {Ck : ℝ} (hkC : ∀ v, k v ≤ Ck)

section PerNu

include h hpath hstart hτ hM hε hε1 hU hk hk0 hkC

omit hM hε hε1 hU hk0 hkC in
theorem measurable_dualInteg_nu (ν : FiniteMeasure unitInterval) :
    Measurable fun z : Ω' × ℝ => dualInteg D0 k N X Y τ ν z.2 z.1 :=
  (measurable_dualInteg_joint h hpath hstart hτ hk).comp
    (f := fun z : Ω' × ℝ => (ν, (z.2, z.1)))
    (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))

theorem intervalIntegrable_dualInteg (ν : FiniteMeasure unitInterval) (ω' : Ω') (a b : ℝ) :
    IntervalIntegrable (fun v => dualInteg D0 k N X Y τ ν v ω') volume a b :=
  intervalIntegrable_of_bdd ((measurable_dualInteg_nu h hpath hstart hτ hk
    ν).comp (measurable_const.prodMk measurable_id))
    (fun v => abs_dualInteg_le hpath hstart hM hε hε1 hU D0 hk0 hkC ν v ω') a b

/-- `integral_killed_dual` between two dual times, at a fixed forward measure. -/
theorem integral_ratioKill_sub (ν : FiniteMeasure unitInterval) {r r' : ℝ} (hr' : 0 ≤ r')
    (hrr : r' ≤ r) :
    ∫ ω', ratioStop ν N X Y τ r ω' * killFac k N X Y τ r ω' ∂P' -
        ∫ ω', ratioStop ν N X Y τ r' ω' * killFac k N X Y τ r' ω' ∂P' =
      ∫ ω', (∫ v in r'..r, dualInteg D0 k N X Y τ ν v ω') ∂P' := by
  have := h.prob
  set Cν := genC D0 p M ε * (ν : Measure unitInterval).real univ + Ck * (p * (M + 1))
  have hA : ∀ r, Integrable (fun ω' => ratioStop ν N X Y τ r ω' * killFac k N X Y τ r ω') P' :=
    fun r => Integrable.of_bound (((measurable_ratioStop_joint h hpath hτ).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).mul
      ((measurable_killFac_joint h hpath hτ hk).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable 1
      (ae_of_all _ fun ω' => by
        have hK := killFac_mem (τ := τ) (hpath ω') hk0 r
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hK.1]
        exact (mul_le_mul (abs_pathRatio_le (hpath ω') ν _) hK.2 hK.1.le zero_le_one).trans
          (le_of_eq (one_mul 1)))
  have hB : ∀ r, 0 ≤ r →
      Integrable (fun ω' => ∫ v in (0 : ℝ)..r, dualInteg D0 k N X Y τ ν v ω') P' := by
    intro r hr
    have hm : StronglyMeasurable fun ω' => ∫ v in Ioc (0 : ℝ) r, dualInteg D0 k N X Y τ ν v ω' :=
      (measurable_dualInteg_nu h hpath hstart hτ hk
        ν).stronglyMeasurable.integral_prod_right'
    refine Integrable.of_bound (C := Cν * (r - 0)) ?_ (ae_of_all _ fun ω' => ?_)
    · simp_rw [intervalIntegral.integral_of_le hr]; exact hm.aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_integral_le_of_abs_le hr fun v _ =>
        abs_dualInteg_le hpath hstart hM hε hε1 hU D0 hk0 hkC ν v ω'
  have e1 := integral_killed_dual h hpath hstart ν hτ hM hε hε1 hU hk hk0 hkC (hr'.trans hrr)
  have e2 := integral_killed_dual h hpath hstart ν hτ hM hε hε1 hU hk hk0 hkC hr'
  rw [integral_sub (hA r) (hA 0)] at e1
  rw [integral_sub (hA r') (hA 0)] at e2
  have e3 : ∫ ω', (∫ v in r'..r, dualInteg D0 k N X Y τ ν v ω') ∂P' =
      ∫ ω', (∫ v in (0 : ℝ)..r, dualInteg D0 k N X Y τ ν v ω') ∂P' -
        ∫ ω', (∫ v in (0 : ℝ)..r', dualInteg D0 k N X Y τ ν v ω') ∂P' := by
    rw [← integral_sub (hB r (hr'.trans hrr)) (hB r' hr')]
    refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
    exact (intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_dualInteg h hpath hstart hτ hM hε hε1 hU hk hk0 hkC ν ω' 0 r)
      (intervalIntegrable_dualInteg h hpath hstart hτ hM hε hε1 hU hk hk0 hkC ν ω' 0 r')).symm
  have e1' : ∫ ω', ratioStop ν N X Y τ r ω' * killFac k N X Y τ r ω' ∂P' -
      ∫ ω', ratioStop ν N X Y τ 0 ω' * killFac k N X Y τ 0 ω' ∂P' =
      ∫ ω', (∫ v in (0 : ℝ)..r, dualInteg D0 k N X Y τ ν v ω') ∂P' := e1
  have e2' : ∫ ω', ratioStop ν N X Y τ r' ω' * killFac k N X Y τ r' ω' ∂P' -
      ∫ ω', ratioStop ν N X Y τ 0 ω' * killFac k N X Y τ 0 ω' ∂P' =
      ∫ ω', (∫ v in (0 : ℝ)..r', dualInteg D0 k N X Y τ ν v ω') ∂P' := e2
  rw [e3]; linarith

end PerNu

section Avg

variable (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hcont : ∀ ω, ContinuousOn (fun t => μ t ω) (Ioi 0))
  {a0 t : ℝ} (ha0 : 0 < a0) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
  (hCm : ∀ s, Integrable (fun ω => (μ (clampT a0 t s) ω : Measure unitInterval).real univ) P ∧
    ∫ ω, (μ (clampT a0 t s) ω : Measure unitInterval).real univ ∂P ≤ Cm)

include hmeas hcont ha0 h hpath hstart hτ hk in
theorem measurable_dualInteg_avgArg :
    Measurable fun z : Ω × ((ℝ × ℝ) × Ω') =>
      dualInteg D0 k N X Y τ (μ (clampT a0 t z.2.1.1) z.1) z.2.1.2 z.2.2 :=
  (measurable_dualInteg_joint h hpath hstart hτ hk).comp
    (f := fun z : Ω × ((ℝ × ℝ) × Ω') => (μ (clampT a0 t z.2.1.1) z.1, (z.2.1.2, z.2.2)))
    (((measurable_muClamp hmeas hcont ha0).comp (f := fun z : Ω × ((ℝ × ℝ) × Ω') => (z.2.1.1, z.1))
      ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))

include hmeas hcont ha0 h hpath hstart hτ hk in
theorem measurable_dualAvg :
    Measurable fun q : (ℝ × ℝ) × Ω' => dualAvg P μ a0 t D0 k N X Y τ q.1.1 q.1.2 q.2 :=
  ((measurable_dualInteg_avgArg h hpath hstart hτ hk hmeas hcont ha0).stronglyMeasurable.integral_prod_left'
    (μ := P)).measurable

omit m' in
include hpath hstart hM hε hε1 hU hk0 hkC hCm in
theorem abs_dualAvg_le (s v : ℝ) (ω' : Ω') :
    |dualAvg P μ a0 t D0 k N X Y τ s v ω'| ≤ genC D0 p M ε * Cm + Ck * (p * (M + 1)) := by
  have hi : Integrable (fun ω => genC D0 p M ε *
      (μ (clampT a0 t s) ω : Measure unitInterval).real univ + Ck * (p * (M + 1))) P :=
    ((hCm s).1.const_mul _).add (integrable_const _)
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hi (ae_of_all _ fun ω => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact abs_dualInteg_le hpath hstart hM hε hε1 hU D0 hk0 hkC _ v ω'
  · rw [integral_add ((hCm s).1.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    have := mul_le_mul_of_nonneg_left (hCm s).2 (genC_nonneg D0 p M ε)
    linarith

include h hpath hstart hτ hM hε hε1 hU hk hk0 hkC hmeas hcont ha0 hCm in
/-- **The dual step, averaged over the forward process.** -/
theorem stripV_sub (s : ℝ) {r r' : ℝ} (hr' : 0 ≤ r') (hrr : r' ≤ r) :
    stripV P μ a0 t P' k N X Y τ s r - stripV P μ a0 t P' k N X Y τ s r' =
      ∫ ω', (∫ v in r'..r, dualAvg P μ a0 t D0 k N X Y τ s v ω') ∂P' := by
  have := h.prob
  set ν : Ω → FiniteMeasure unitInterval := fun ω => μ (clampT a0 t s) ω with hνdef
  have hν : Measurable ν := hmeas _ (lt_of_lt_of_le ha0 (le_max_left _ _))
  have hAj : ∀ r : ℝ, Measurable fun z : Ω × Ω' =>
      ratioStop (ν z.1) N X Y τ r z.2 * killFac k N X Y τ r z.2 := fun r =>
    ((measurable_ratioStop_joint h hpath hτ).comp (f := fun z : Ω × Ω' => (ν z.1, (r, z.2)))
      ((hν.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))).mul
      ((measurable_killFac_joint h hpath hτ hk).comp (f := fun z : Ω × Ω' => (r, z.2))
        (measurable_const.prodMk measurable_snd))
  have hAb : ∀ (r : ℝ) (z : Ω × Ω'),
      ‖ratioStop (ν z.1) N X Y τ r z.2 * killFac k N X Y τ r z.2‖ ≤ 1 := fun r z => by
    have hK := killFac_mem (τ := τ) (hpath z.2) hk0 r
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hK.1]
    exact (mul_le_mul (abs_pathRatio_le (hpath z.2) _ _) hK.2 hK.1.le zero_le_one).trans
      (le_of_eq (one_mul 1))
  have hAi : ∀ r : ℝ, Integrable (fun z : Ω × Ω' =>
      ratioStop (ν z.1) N X Y τ r z.2 * killFac k N X Y τ r z.2) (P.prod P') := fun r =>
    Integrable.of_bound (hAj r).aestronglyMeasurable 1 (ae_of_all _ (hAb r))
  have hV : ∀ r : ℝ, stripV P μ a0 t P' k N X Y τ s r =
      ∫ ω, ∫ ω', ratioStop (ν ω) N X Y τ r ω' * killFac k N X Y τ r ω' ∂P' ∂P := fun r => by
    unfold stripV
    simp_rw [← integral_mul_const]
    exact (integral_integral_swap (f := fun ω ω' =>
      ratioStop (ν ω) N X Y τ r ω' * killFac k N X Y τ r ω') (hAi r)).symm
  have hIi : ∀ r : ℝ, Integrable (fun ω =>
      ∫ ω', ratioStop (ν ω) N X Y τ r ω' * killFac k N X Y τ r ω' ∂P') P := fun r =>
    Integrable.of_bound ((hAj r).stronglyMeasurable.integral_prod_right').aestronglyMeasurable 1
      (ae_of_all _ fun ω => (norm_integral_le_of_norm_le_const (C := 1)
        (ae_of_all _ fun ω' => hAb r (ω, ω'))).trans (by simp))
  rw [hV r, hV r', ← integral_sub (hIi r) (hIi r')]
  rw [integral_congr_ae (ae_of_all _ fun ω => integral_ratioKill_sub h hpath hstart hτ hM hε hε1 hU
    hk hk0 hkC (ν ω) hr' hrr)]
  -- the swap `∫_ω ∫_{ω'} ∫_v = ∫_{ω'} ∫_v ∫_ω`
  have : IsFiniteMeasure (volume.restrict (Ioc r' r)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  simp_rw [intervalIntegral.integral_of_le hrr]
  set F : Ω → Ω' × ℝ → ℝ := fun ω z => dualInteg D0 k N X Y τ (ν ω) z.2 z.1 with hF
  have hFm : Measurable (Function.uncurry F) :=
    (measurable_dualInteg_joint h hpath hstart hτ hk).comp
      (f := fun z : Ω × (Ω' × ℝ) => (ν z.1, (z.2.2, z.2.1)))
      ((hν.comp measurable_fst).prodMk ((measurable_snd.comp measurable_snd).prodMk
        (measurable_fst.comp measurable_snd)))
  set C := Ck * (p * (M + 1))
  have hFb : ∀ z : Ω × (Ω' × ℝ), ‖Function.uncurry F z‖ ≤
      genC D0 p M ε * (ν z.1 : Measure unitInterval).real univ + C := fun z => by
    rw [Real.norm_eq_abs]; exact abs_dualInteg_le hpath hstart hM hε hε1 hU D0 hk0 hkC _ _ _
  have hFi : Integrable (Function.uncurry F) (P.prod (P'.prod (volume.restrict (Ioc r' r)))) :=
    Integrable.mono' ((((hCm s).1.const_mul (genC D0 p M ε)).add (integrable_const C)).comp_fst _)
      hFm.aestronglyMeasurable (ae_of_all _ hFb)
  have hFi' : ∀ ω, Integrable (F ω) (P'.prod (volume.restrict (Ioc r' r))) := fun ω =>
    Integrable.of_bound (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (genC D0 p M ε * (ν ω : Measure unitInterval).real univ + C)
      (ae_of_all _ fun z => hFb (ω, z))
  have hD : Integrable (fun z : Ω' × ℝ => dualAvg P μ a0 t D0 k N X Y τ s z.2 z.1)
      (P'.prod (volume.restrict (Ioc r' r))) :=
    Integrable.of_bound ((measurable_dualAvg h hpath hstart hτ hk hmeas hcont ha0).comp
      (f := fun z : Ω' × ℝ => ((s, z.2), z.1))
      ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aestronglyMeasurable _
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]
        exact abs_dualAvg_le hpath hstart hM hε hε1 hU hk0 hkC hCm s z.2 z.1)
  calc ∫ ω, (∫ ω', (∫ v in Ioc r' r, dualInteg D0 k N X Y τ (ν ω) v ω') ∂P') ∂P
      = ∫ ω, ∫ z, F ω z ∂(P'.prod (volume.restrict (Ioc r' r))) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => (integral_prod (F ω) (hFi' ω)).symm)
    _ = ∫ z, ∫ ω, F ω z ∂P ∂(P'.prod (volume.restrict (Ioc r' r))) := integral_integral_swap hFi
    _ = ∫ ω', (∫ v in Ioc r' r, dualAvg P μ a0 t D0 k N X Y τ s v ω') ∂P' := integral_prod _ hD

include h hpath hstart hτ hM hε hε1 hU hk hk0 hkC hmeas hcont ha0 hCm0 hCm in
/-- **The dual steps integrated over the strip.** -/
theorem integral_stripV_dual (hat : a0 ≤ t) {η : ℝ} (hη : 0 ≤ η) :
    ∫ s in a0..t, (stripV P μ a0 t P' k N X Y τ s (t - s) -
        stripV P μ a0 t P' k N X Y τ s (max 0 (t - η - s))) =
      ∫ ω', (∫ q, (stripSet a0 t η).indicator
        (fun q => dualAvg P μ a0 t D0 k N X Y τ q.1 q.2 ω') q ∂(volume.prod volume)) ∂P' := by
  have := h.prob
  set S := stripSet a0 t η
  set Cd := genC D0 p M ε * Cm + Ck * (p * (M + 1)) with hCd
  have hCk : 0 ≤ Ck := (hk0 0).trans (hkC 0)
  have hCd0 : 0 ≤ Cd := add_nonneg (mul_nonneg (genC_nonneg D0 p M ε) hCm0)
    (mul_nonneg hCk (by positivity))
  have hDb : ∀ s v ω', |dualAvg P μ a0 t D0 k N X Y τ s v ω'| ≤ Cd := fun s v ω' =>
    abs_dualAvg_le (P := P) (μ := μ) hpath hstart hM hε hε1 hU hk0 hkC hCm s v ω'
  have hDm := measurable_dualAvg (P := P) (t := t) h hpath hstart hτ hk hmeas hcont ha0
  set FA : (ℝ × ℝ) × Ω' → ℝ := fun q => dualAvg P μ a0 t D0 k N X Y τ q.1.1 q.1.2 q.2
  set H : ℝ → Ω' → ℝ := fun s ω' =>
    ∫ v, S.indicator (fun q => dualAvg P μ a0 t D0 k N X Y τ q.1 q.2 ω') (s, v) with hH
  have step1 : ∀ s ∈ uIcc a0 t, stripV P μ a0 t P' k N X Y τ s (t - s) -
      stripV P μ a0 t P' k N X Y τ s (max 0 (t - η - s)) = ∫ ω', H s ω' ∂P' := by
    intro s hs
    rw [uIcc_of_le hat] at hs
    rw [stripV_sub h hpath hstart hτ hM hε hε1 hU hk hk0 hkC hmeas hcont ha0 hCm s
      (le_max_left _ _) (max_le (by linarith [hs.2]) (by linarith))]
    exact integral_congr_ae (ae_of_all _ fun ω' =>
      integral_fiber_dual (fun q => dualAvg P μ a0 t D0 k N X Y τ q.1 q.2 ω') hs.1 hs.2 hη)
  have hHz : ∀ s, s ∉ Icc a0 t → ∀ ω', H s ω' = 0 := fun s hs ω' => by
    have : ∀ v, S.indicator (fun q => dualAvg P μ a0 t D0 k N X Y τ q.1 q.2 ω') (s, v) = 0 :=
      fun v => indicator_of_notMem (notMem_stripSet_dual hs) _
    simp [hH, this]
  have hG : Measurable fun z : (ℝ × Ω') × ℝ =>
      (S ×ˢ (univ : Set Ω')).indicator FA ((z.1.1, z.2), z.1.2) :=
    (hDm.indicator ((measurableSet_stripSet a0 t η).prod MeasurableSet.univ)).comp
      (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))
  have hHm : Measurable (Function.uncurry H) := by
    have e : Function.uncurry H = fun z : ℝ × Ω' =>
        ∫ v, (S ×ˢ (univ : Set Ω')).indicator FA ((z.1, v), z.2) := funext fun z => by
      simp only [Function.uncurry, hH]
      exact integral_congr_ae (ae_of_all _ fun v => indicator_prod_univ S FA (z.1, v) z.2)
    rw [e]; exact (hG.stronglyMeasurable.integral_prod_right').measurable
  have hHi : Integrable (Function.uncurry H) (volume.prod P') :=
    Integrable.mono' ((integrable_indicator_Icc_const a0 t (Cd * η)).comp_fst P')
      hHm.aestronglyMeasurable (ae_of_all _ fun z =>
        norm_integral_fiber_le hCd0 (fun q _ _ => hDb _ _ _) hη z.1)
  rw [intervalIntegral.integral_congr step1, intervalIntegral.integral_of_le hat,
    setIntegral_eq_integral_of_ae_compl_eq_zero ?_]
  · rw [integral_integral_swap hHi]
    refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
    exact (integral_prod _ (integrable_strip (hDm.comp (measurable_id.prodMk measurable_const))
      (fun q => hDb _ _ _) a0 t η)).symm
  · have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ a0 := by rw [ae_iff]; simp
    filter_upwards [hne] with s hs hsI
    have : s ∉ Icc a0 t := fun h' => hsI ⟨lt_of_le_of_ne h'.1 (Ne.symm hs), h'.2⟩
    simp only [hHz s this, integral_zero]

end Avg

end BlockBand.Transmission.LawDuality
