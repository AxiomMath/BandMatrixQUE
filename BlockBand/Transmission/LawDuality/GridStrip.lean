module

public import BlockBand.Transmission.LawDuality.GridPost

/-!
# The strip estimate

Combines the dual steps (`integral_stripV_dual`), the forward steps before `τ`
(`integral_forward_strip`), the stopped steps after `τ` (`abs_integral_post_le`) and the curve
identity (`strip_curve_identity`):
* `fwdAvg_sub_dualAvg`: for `v > 0` the two averaged integrands differ by
  `K_v R_v1{v<τ} (k(v) − h(s)) E F_{Z_v}(μ̌_s)`;
* **`strip_estimate`**: if `|k(v) − h(s)| ≤ ε'` on the strip `S_η`, then
  `|∫_{t−η}^t V(s, 0) ds − ∫_{L−η}^L V(a₀, r) dr| ≤ p(M+1)ε'ηL + 2ηP'(τ ≤ L)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {Ω' : Type*} [m' : MeasurableSpace Ω'] {P' : Measure Ω'} {𝓖 : Filtration ℝ≥0 m'} {D0 : ℝ}
  {p : ℕ} {x y : Fin p → ℝ} {N : ℝ≥0 → Ω' → ℕ} {X Y : ℝ≥0 → Ω' → ℕ → ℝ}
  (h : IsDualDeletionProcess P' 𝓖 D0 x y N X Y)
  (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  (hstart : ∀ ω, N 0 ω = p) {τ : Ω' → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
  {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hU : StaysIn N X Y τ M ε)
  {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ v, 0 ≤ k v) {Ck : ℝ} (hkC : ∀ v, k v ≤ Ck)
  {E : ℝ} {κ : ℝ → ℝ} (hκ : Continuous κ) {Ch : ℝ} (hhC : ∀ u, |absorptionRate E κ u| ≤ Ch)
  (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hcont : ∀ ω, ContinuousOn (fun t => μ t ω) (Ioi 0))
  {a0 t : ℝ} (ha0 : 0 < a0) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
  (hCm : ∀ s, Integrable (fun ω => (μ (clampT a0 t s) ω : Measure unitInterval).real univ) P ∧
    ∫ ω, (μ (clampT a0 t s) ω : Measure unitInterval).real univ ∂P ≤ Cm)

include h hpath hstart hτ hM hε hε1 hU hk hk0 hkC hκ hhC hmeas hcont ha0 hCm in
theorem fwdAvg_sub_dualAvg (s : ℝ) {v : ℝ} (hv : 0 < v) (ω' : Ω') :
    fwdAvg P μ a0 t D0 E κ k N X Y τ s v ω' - dualAvg P μ a0 t D0 k N X Y τ s v ω' =
      killFac k N X Y τ v ω' * (dualTotal (N v.toNNReal ω') (X v.toNNReal ω') (Y v.toNNReal ω') *
        killInd (τ ω') v) * (∫ ω, pathRatio (μ (clampT a0 t s) ω) N X Y v.toNNReal ω' ∂P) *
        (k v - absorptionRate E κ s) := by
  have hb : Integrable (fun ω => genC D0 p M ε *
      (μ (clampT a0 t s) ω : Measure unitInterval).real univ + (Ck + Ch) * (p * (M + 1))) P :=
    ((hCm s).1.const_mul _).add (integrable_const _)
  have hpM : 0 ≤ (p : ℝ) * (M + 1) := by positivity
  have hCk : 0 ≤ Ck := (hk0 0).trans (hkC 0)
  have hCh : 0 ≤ Ch := (abs_nonneg _).trans (hhC 0)
  have hf : Integrable (fun ω => fwdInteg D0 E κ k N X Y τ s (μ (clampT a0 t s) ω) v ω') P :=
    Integrable.mono' hb ((measurable_fwdInteg_avgArg h hpath hstart hτ hk hκ hmeas hcont ha0).comp
      (f := fun ω => (ω, ((s, v), ω'))) (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        refine (abs_fwdInteg_le hpath hstart hM hε hε1 hU D0 E κ hk0 hhC s _ v ω').trans ?_
        nlinarith)
  have hd : Integrable (fun ω => dualInteg D0 k N X Y τ (μ (clampT a0 t s) ω) v ω') P :=
    Integrable.mono' hb ((measurable_dualInteg_avgArg h hpath hstart hτ hk hmeas hcont ha0).comp
      (f := fun ω => (ω, ((s, v), ω'))) (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        refine (abs_dualInteg_le hpath hstart hM hε hε1 hU D0 hk0 hkC _ v ω').trans ?_
        nlinarith)
  unfold fwdAvg dualAvg
  rw [← integral_sub hf hd, integral_congr_ae (ae_of_all _ fun ω =>
    fwdInteg_sub_dualInteg D0 E κ k N X Y τ s (μ (clampT a0 t s) ω) hv ω'),
    integral_mul_const, integral_const_mul]

include h hpath hstart hτ hM hε hε1 hU hk hk0 hkC hκ hhC hmeas hcont ha0 hCm0 hCm in
/-- **The strip estimate.** -/
theorem strip_estimate (hMart : IsRatioMartingale D0 E κ P μ) (hat : a0 ≤ t) {η ε' : ℝ}
    (hη : 0 ≤ η) (hηL : η ≤ t - a0) (hε' : 0 ≤ ε')
    (hδ : ∀ q ∈ stripSet a0 t η, |k q.2 - absorptionRate E κ q.1| ≤ ε') :
    |(∫ s in t - η..t, stripV P μ a0 t P' k N X Y τ s 0) -
        ∫ r in t - a0 - η..t - a0, stripV P μ a0 t P' k N X Y τ a0 r| ≤
      p * (M + 1) * ε' * η * (t - a0) +
        2 * η * P'.real {ω' | τ ω' ≤ ((t - a0).toNNReal : WithTop ℝ≥0)} := by
  have := h.prob
  have hpM : 0 ≤ (p : ℝ) * (M + 1) := by positivity
  have hCk : 0 ≤ Ck := (hk0 0).trans (hkC 0)
  have hCh : 0 ≤ Ch := (abs_nonneg _).trans (hhC 0)
  have hRA := measurable_ratioAvg (P := P) (t := t) h hpath hτ hmeas hcont ha0
  have hKF := measurable_killFac_joint h hpath hτ hk
  have hRω : ∀ s r, Measurable fun ω' => ratioAvg P μ a0 t N X Y τ s r ω' := fun s r =>
    hRA.comp (f := fun ω' => ((s, r), ω')) (measurable_const.prodMk measurable_id)
  have hKω : ∀ r, Measurable fun ω' => killFac k N X Y τ r ω' := fun r =>
    hKF.comp (f := fun ω' => (r, ω')) (measurable_const.prodMk measurable_id)
  have hRK : ∀ s r ω', |ratioAvg P μ a0 t N X Y τ s r ω' * killFac k N X Y τ r ω'| ≤ 1 :=
    fun s r ω' => by
      have hK := killFac_mem (τ := τ) (hpath ω') hk0 r
      rw [abs_mul, abs_of_pos hK.1]
      exact (mul_le_mul (abs_ratioAvg_le hpath s r ω') hK.2 hK.1.le zero_le_one).trans
        (le_of_eq (one_mul 1))
  -- `V` is bounded and jointly measurable
  have hVm : Measurable (Function.uncurry (stripV P μ a0 t P' k N X Y τ)) := by
    have hm : Measurable fun z : (ℝ × ℝ) × Ω' =>
        ratioAvg P μ a0 t N X Y τ z.1.1 z.1.2 z.2 * killFac k N X Y τ z.1.2 z.2 :=
      hRA.mul (hKF.comp (f := fun z : (ℝ × ℝ) × Ω' => (z.1.2, z.2))
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := P')).measurable
  have hVb : ∀ s r, |stripV P μ a0 t P' k N X Y τ s r| ≤ 1 := fun s r => by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun ω' => ?_)).trans (by simp)
    rw [Real.norm_eq_abs]; exact hRK s r ω'
  rw [← strip_curve_identity hVm hVb hη hηL]
  -- split the forward steps at `τ`
  have hI : ∀ r, Measurable fun ω' => killInd (τ ω') r := fun r =>
    (measurable_killInd_joint hτ).comp (f := fun ω' => (r, ω')) (measurable_const.prodMk measurable_id)
  have hpt3 : ∀ r ω', |killInd (τ ω') r * ((ratioAvg P μ a0 t N X Y τ (t - r) r ω' -
      ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω') * killFac k N X Y τ r ω')| ≤ 2 := by
    intro r ω'
    have hi := killInd_mem (τ ω') r
    rw [abs_mul, abs_of_nonneg hi.1, sub_mul]
    have := abs_sub (ratioAvg P μ a0 t N X Y τ (t - r) r ω' * killFac k N X Y τ r ω')
      (ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω' * killFac k N X Y τ r ω')
    have h1 := hRK (t - r) r ω'
    have h2 := hRK (max a0 (t - η - r)) r ω'
    nlinarith [abs_nonneg (ratioAvg P μ a0 t N X Y τ (t - r) r ω' * killFac k N X Y τ r ω' -
      ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω' * killFac k N X Y τ r ω')]
  have hsplit : ∀ r, stripV P μ a0 t P' k N X Y τ (t - r) r -
      stripV P μ a0 t P' k N X Y τ (max a0 (t - η - r)) r =
      (∫ ω', killInd (τ ω') r * ((ratioAvg P μ a0 t N X Y τ (t - r) r ω' -
        ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω') * killFac k N X Y τ r ω') ∂P') +
      ∫ ω', postInteg P μ a0 t η k N X Y τ r ω' ∂P' := fun r => by
    have i1 : ∀ s, Integrable (fun ω' => ratioAvg P μ a0 t N X Y τ s r ω' *
        killFac k N X Y τ r ω') P' := fun s =>
      Integrable.of_bound ((hRω s r).mul (hKω r)).aestronglyMeasurable 1
        (ae_of_all _ fun ω' => by rw [Real.norm_eq_abs]; exact hRK s r ω')
    have i3 : Integrable (fun ω' => killInd (τ ω') r * ((ratioAvg P μ a0 t N X Y τ (t - r) r ω' -
        ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω') * killFac k N X Y τ r ω')) P' :=
      Integrable.of_bound ((hI r).mul (((hRω _ r).sub (hRω _ r)).mul (hKω r))).aestronglyMeasurable 2
        (ae_of_all _ fun ω' => by rw [Real.norm_eq_abs]; exact hpt3 r ω')
    have i4 : Integrable (fun ω' => postInteg P μ a0 t η k N X Y τ r ω') P' :=
      Integrable.of_bound ((measurable_postInteg (P := P) (t := t) h hpath hτ hk hmeas hcont ha0
        η).comp (f := fun ω' => (r, ω')) (measurable_const.prodMk measurable_id)).aestronglyMeasurable 2
        (ae_of_all _ fun ω' => by rw [Real.norm_eq_abs]; exact abs_postInteg_le hpath hk0 η r ω')
    show (∫ ω', ratioAvg P μ a0 t N X Y τ (t - r) r ω' * killFac k N X Y τ r ω' ∂P') -
      (∫ ω', ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω' * killFac k N X Y τ r ω' ∂P') = _
    rw [← integral_sub (i1 _) (i1 _), ← integral_add i3 i4]
    refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
    simp only [postInteg]; ring
  have hW1m : Measurable fun r => ∫ ω', killInd (τ ω') r * ((ratioAvg P μ a0 t N X Y τ (t - r) r ω' -
      ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω') * killFac k N X Y τ r ω') ∂P' := by
    have hm : Measurable fun z : ℝ × Ω' => killInd (τ z.2) z.1 *
        ((ratioAvg P μ a0 t N X Y τ (t - z.1) z.1 z.2 -
          ratioAvg P μ a0 t N X Y τ (max a0 (t - η - z.1)) z.1 z.2) * killFac k N X Y τ z.1 z.2) :=
      (measurable_killInd_joint hτ).mul (((hRA.comp (f := fun z : ℝ × Ω' => ((t - z.1, z.1), z.2))
        (((measurable_const.sub measurable_fst).prodMk measurable_fst).prodMk measurable_snd)).sub
        (hRA.comp (f := fun z : ℝ × Ω' => ((max a0 (t - η - z.1), z.1), z.2))
          (((measurable_const.max (measurable_const.sub measurable_fst)).prodMk
            measurable_fst).prodMk measurable_snd))).mul hKF)
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := P')).measurable
  have hW2m : Measurable fun r => ∫ ω', postInteg P μ a0 t η k N X Y τ r ω' ∂P' :=
    ((measurable_postInteg (P := P) (t := t) h hpath hτ hk hmeas hcont ha0
      η).stronglyMeasurable.integral_prod_right' (ν := P')).measurable
  have hW1b : ∀ r, |∫ ω', killInd (τ ω') r * ((ratioAvg P μ a0 t N X Y τ (t - r) r ω' -
      ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω') * killFac k N X Y τ r ω') ∂P'| ≤ 2 :=
    fun r => by
      rw [← Real.norm_eq_abs]
      exact (norm_integral_le_of_norm_le_const (C := 2) (ae_of_all _ fun ω' => by
        rw [Real.norm_eq_abs]; exact hpt3 r ω')).trans (by simp)
  have hW2b : ∀ r, |∫ ω', postInteg P μ a0 t η k N X Y τ r ω' ∂P'| ≤ 2 := fun r => by
    rw [← Real.norm_eq_abs]
    exact (norm_integral_le_of_norm_le_const (C := 2) (ae_of_all _ fun ω' => by
      rw [Real.norm_eq_abs]; exact abs_postInteg_le hpath hk0 η r ω')).trans (by simp)
  rw [intervalIntegral.integral_congr (fun r _ => hsplit r), intervalIntegral.integral_add
    (intervalIntegrable_of_bdd hW1m hW1b _ _) (intervalIntegrable_of_bdd hW2m hW2b _ _),
    integral_forward_strip h hpath hstart hτ hM hε hε1 hU hk hk0 hκ hhC hmeas hcont ha0 hCm0 hCm
      hMart hat hη,
    integral_stripV_dual h hpath hstart hτ hM hε hε1 hU hk hk0 hkC hmeas hcont ha0 hCm0 hCm hat hη]
  have hB := abs_integral_post_le (P := P) (μ := μ) h hpath hτ hk hk0 hmeas hcont ha0 hat hη
  set S := stripSet a0 t η with hS
  set CA := genC D0 p M ε * Cm + Ch * (p * (M + 1))
  set CD := genC D0 p M ε * Cm + Ck * (p * (M + 1))
  have hCA0 : 0 ≤ CA := add_nonneg (mul_nonneg (genC_nonneg D0 p M ε) hCm0) (mul_nonneg hCh hpM)
  have hCD0 : 0 ≤ CD := add_nonneg (mul_nonneg (genC_nonneg D0 p M ε) hCm0) (mul_nonneg hCk hpM)
  have hfA : ∀ z : (ℝ × ℝ) × Ω', |fwdAvg P μ a0 t D0 E κ k N X Y τ z.1.1 z.1.2 z.2| ≤ CA := fun z =>
    abs_fwdAvg_le (P := P) (μ := μ) hpath hstart hM hε hε1 hU hk0 hhC hCm _ _ _
  have hfD : ∀ z : (ℝ × ℝ) × Ω', |dualAvg P μ a0 t D0 k N X Y τ z.1.1 z.1.2 z.2| ≤ CD := fun z =>
    abs_dualAvg_le (P := P) (μ := μ) hpath hstart hM hε hε1 hU hk0 hkC hCm _ _ _
  have hAm := measurable_fwdAvg (P := P) (t := t) (E := E) (κ := κ) h hpath hstart hτ hk hκ hmeas
    hcont ha0
  have hDm := measurable_dualAvg (P := P) (t := t) h hpath hstart hτ hk hmeas hcont ha0
  have hint : ∀ {F : (ℝ × ℝ) × Ω' → ℝ}, Measurable F → ∀ {C : ℝ}, 0 ≤ C → (∀ z, |F z| ≤ C) →
      Integrable (fun ω' => ∫ q, S.indicator (fun q => F (q, ω')) q ∂(volume.prod volume)) P' := by
    intro F hF C hC0 hC
    refine Integrable.of_bound (C := C * η * (t - a0)) ?_ (ae_of_all _ fun ω' => ?_)
    · have e : (fun ω' => ∫ q, S.indicator (fun q => F (q, ω')) q ∂(volume.prod volume)) =
          fun ω' => ∫ q, (S ×ˢ (univ : Set Ω')).indicator F (q, ω') ∂(volume.prod volume) :=
        funext fun ω' => integral_congr_ae (ae_of_all _ fun q => indicator_prod_univ S F q ω')
      rw [e]
      exact ((hF.indicator ((measurableSet_stripSet a0 t η).prod
        MeasurableSet.univ)).stronglyMeasurable.integral_prod_left'
          (μ := volume.prod volume)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_integral_strip_le (hF.comp (f := fun q : ℝ × ℝ => (q, ω'))
        (measurable_id.prodMk measurable_const))
        (fun q => hC (q, ω')) hC0 (fun q _ _ => hC (q, ω')) hat hη
  have iA := hint hAm hCA0 hfA
  have iD := hint hDm hCD0 hfD
  have hAT : |(∫ ω', (∫ q, S.indicator (fun q => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1 q.2 ω') q
      ∂(volume.prod volume)) ∂P') - ∫ ω', (∫ q, S.indicator
        (fun q => dualAvg P μ a0 t D0 k N X Y τ q.1 q.2 ω') q ∂(volume.prod volume)) ∂P'| ≤
      p * (M + 1) * ε' * η * (t - a0) := by
    rw [← integral_sub iA iD, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := p * (M + 1) * ε' * η * (t - a0))
      (ae_of_all _ fun ω' => ?_)).trans (by simp)
    have hAω : Measurable fun q : ℝ × ℝ => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1 q.2 ω' :=
      hAm.comp (f := fun q : ℝ × ℝ => (q, ω')) (measurable_id.prodMk measurable_const)
    have hDω : Measurable fun q : ℝ × ℝ => dualAvg P μ a0 t D0 k N X Y τ q.1 q.2 ω' :=
      hDm.comp (f := fun q : ℝ × ℝ => (q, ω')) (measurable_id.prodMk measurable_const)
    rw [Real.norm_eq_abs, ← integral_sub (integrable_strip hAω (fun q => hfA (q, ω')) a0 t η)
      (integrable_strip hDω (fun q => hfD (q, ω')) a0 t η)]
    have e : ∀ q, S.indicator (fun q => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1 q.2 ω') q -
        S.indicator (fun q => dualAvg P μ a0 t D0 k N X Y τ q.1 q.2 ω') q =
        S.indicator (fun q => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1 q.2 ω' -
          dualAvg P μ a0 t D0 k N X Y τ q.1 q.2 ω') q := fun q => by
      by_cases hq : q ∈ S
      · simp only [indicator_of_mem hq]
      · simp only [indicator_of_notMem hq, sub_zero]
    rw [← hS, integral_congr_ae (ae_of_all _ e)]
    refine abs_integral_strip_le (hAω.sub hDω) (B := CA + CD) (fun q => (abs_sub _ _).trans
      (add_le_add (hfA (q, ω')) (hfD (q, ω')))) (by positivity) (fun q hq hq2 => ?_) hat hη
    show |fwdAvg P μ a0 t D0 E κ k N X Y τ q.1 q.2 ω' - dualAvg P μ a0 t D0 k N X Y τ q.1 q.2 ω'| ≤ _
    rw [fwdAvg_sub_dualAvg h hpath hstart hτ hM hε hε1 hU hk hk0 hkC hκ hhC hmeas hcont ha0 hCm
      q.1 hq2 ω']
    have hK := killFac_mem (τ := τ) (hpath ω') hk0 q.2
    have hR := totalInd_mem hpath hstart hM hε hU ω' q.2
    have hF : |∫ ω, pathRatio (μ (clampT a0 t q.1) ω) N X Y q.2.toNNReal ω' ∂P| ≤ 1 := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun ω => ?_)).trans (by simp)
      rw [Real.norm_eq_abs]; exact abs_pathRatio_le (hpath ω') _ _
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hK.1, abs_of_nonneg hR.1]
    calc _ ≤ 1 * (p * (M + 1)) * 1 * ε' := mul_le_mul (mul_le_mul (mul_le_mul hK.2 hR.2 hR.1
          zero_le_one) hF (abs_nonneg _) (by positivity)) (hδ q hq) (abs_nonneg _) (by positivity)
      _ = p * (M + 1) * ε' := by ring
  calc _ = |((∫ ω', (∫ q, S.indicator (fun q => fwdAvg P μ a0 t D0 E κ k N X Y τ q.1 q.2 ω') q
      ∂(volume.prod volume)) ∂P') - ∫ ω', (∫ q, S.indicator
        (fun q => dualAvg P μ a0 t D0 k N X Y τ q.1 q.2 ω') q ∂(volume.prod volume)) ∂P') +
      ∫ r in (0 : ℝ)..t - a0, (∫ ω', postInteg P μ a0 t η k N X Y τ r ω' ∂P')| := by
        congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hAT hB)

end BlockBand.Transmission.LawDuality
