module

public import BlockBand.Transmission.LawDuality.GridStrip

/-!
# Duality strip: the limit `η → 0`

Letting the strip width `η → 0` in the strip estimate gives
`|E F_{x,y}(μ_t) − V(a₀, t − a₀)| ≤ 2P'(τ ≤ t − a₀)` (`abs_ratio_sub_stripV_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

theorem pathRatio_zero_eq {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {p : ℕ}
    {x y : Fin p → ℝ} {ω : Ω} (hst : N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i)
    (ν : FiniteMeasure unitInterval) : pathRatio ν N X Y 0 ω = transmissionRatio x y ν := by
  unfold pathRatio
  have key : ∀ n (_ : n = p) (a b : ℕ → ℝ), (∀ i : Fin p, a i = x i ∧ b i = y i) →
      ratioOn ν (dualCoordOf n a b) = transmissionRatio x y ν := by
    rintro n rfl a b hab
    show transmissionRatio (fun i : Fin n => a i) (fun i => b i) ν = _
    congr 1 <;> funext i
    exacts [(hab i).1, (hab i).2]
  exact key _ hst.1 _ _ hst.2

theorem ratioStop_zero {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (τ : Ω → WithTop ℝ≥0) (ν : FiniteMeasure unitInterval) (ω : Ω) :
    ratioStop ν N X Y τ 0 ω = pathRatio ν N X Y 0 ω := by
  have : stopAt τ (0 : ℝ).toNNReal ω = 0 := by
    unfold stopAt; rw [Real.toNNReal_zero, WithTop.coe_zero, min_eq_left zero_le]; rfl
  unfold ratioStop; rw [this]

theorem killFac_zero {Ω : Type*} (k : ℝ → ℝ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) : killFac k N X Y τ 0 ω = 1 := by
  simp [killFac, killExp]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {Ω' : Type*} [m' : MeasurableSpace Ω'] {P' : Measure Ω'} {𝓖 : Filtration ℝ≥0 m'} {D0 : ℝ}
  {p : ℕ} {x y : Fin p → ℝ} {N : ℝ≥0 → Ω' → ℕ} {X Y : ℝ≥0 → Ω' → ℕ → ℝ}
  (h : IsDualDeletionProcess P' 𝓖 D0 x y N X Y)
  (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  {τ : Ω' → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
  {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ v, 0 ≤ k v)
  (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hcont : ∀ ω, ContinuousOn (fun t => μ t ω) (Ioi 0))
  {a0 t : ℝ} (ha0 : 0 < a0)

omit [IsProbabilityMeasure P] in
include h in
theorem stripV_zero (hst : ∀ ω, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i)
    (s : ℝ) : stripV P μ a0 t P' k N X Y τ s 0 =
      ∫ ω, transmissionRatio x y (μ (clampT a0 t s) ω) ∂P := by
  have := h.prob
  unfold stripV
  simp_rw [killFac_zero, mul_one, ratioStop_zero, pathRatio_zero_eq (hst _)]
  rw [integral_const, probReal_univ, one_smul]

include h hpath hτ hk hmeas hcont ha0 in
theorem measurable_stripV : Measurable (Function.uncurry (stripV P μ a0 t P' k N X Y τ)) := by
  have := h.prob
  have hm : Measurable fun z : (ℝ × ℝ) × Ω' =>
      ratioAvg P μ a0 t N X Y τ z.1.1 z.1.2 z.2 * killFac k N X Y τ z.1.2 z.2 :=
    (measurable_ratioAvg (P := P) (t := t) h hpath hτ hmeas hcont ha0).mul
      ((measurable_killFac_joint h hpath hτ hk).comp (f := fun z : (ℝ × ℝ) × Ω' => (z.1.2, z.2))
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := P')).measurable

include h hpath hk0 in
theorem abs_stripV_le (s r : ℝ) : |stripV P μ a0 t P' k N X Y τ s r| ≤ 1 := by
  have := h.prob
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun ω' => ?_)).trans (by simp)
  have hK := killFac_mem (τ := τ) (hpath ω') hk0 r
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hK.1]
  exact (mul_le_mul (abs_ratioAvg_le hpath s r ω') hK.2 hK.1.le zero_le_one).trans
    (le_of_eq (one_mul 1))

include h hpath hτ hk hk0 hmeas hcont ha0 in
theorem continuous_stripV_right (s : ℝ) :
    Continuous fun r => stripV P μ a0 t P' k N X Y τ s r := by
  have := h.prob
  have hν : Measurable fun ω => μ (clampT a0 t s) ω := hmeas _ (lt_of_lt_of_le ha0 (le_max_left _ _))
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun r => ?_) (fun r => ?_)
    (integrable_const 1) (ae_of_all _ fun ω' => ?_)
  · exact (((measurable_ratioAvg (P := P) (t := t) h hpath hτ hmeas hcont ha0).comp
      (f := fun ω' => ((s, r), ω')) (measurable_const.prodMk measurable_id)).mul
      ((measurable_killFac_joint h hpath hτ hk).comp (f := fun ω' => (r, ω'))
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · refine ae_of_all _ fun ω' => ?_
    have hK := killFac_mem (τ := τ) (hpath ω') hk0 r
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hK.1]
    exact (mul_le_mul (abs_ratioAvg_le hpath s r ω') hK.2 hK.1.le zero_le_one).trans
      (le_of_eq (one_mul 1))
  · refine Continuous.mul ?_ (continuous_killFac (hpath ω') hk)
    refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun r => ?_) (fun r => ?_)
      (integrable_const 1) (ae_of_all _ fun ω => continuous_ratioStop (hpath ω') _)
    · exact ((measurable_ratioStop_joint h hpath hτ).comp
        (f := fun ω => (μ (clampT a0 t s) ω, (r, ω'))) (hν.prodMk measurable_const)).aestronglyMeasurable
    · exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact abs_pathRatio_le (hpath ω') _ _

include h hpath hτ hk hk0 hmeas hcont ha0 in
/-- **`|E F_{x,y}(μ_t) − V(a₀, t − a₀)| ≤ 2P'(τ ≤ t − a₀)`.** -/
theorem abs_ratio_sub_stripV_le {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hU : StaysIn N X Y τ M ε) {Ck : ℝ} (hkC : ∀ v, k v ≤ Ck) {E : ℝ} {κ : ℝ → ℝ}
    (hκ : Continuous κ) {Ch : ℝ} (hhC : ∀ u, |absorptionRate E κ u| ≤ Ch)
    (hkh : ∀ v, k v = absorptionRate E κ (t - v)) (hMart : IsRatioMartingale D0 E κ P μ)
    (hmass : HasLocalMassBound P μ) (hxy : IsRatioParameter x y)
    (hst : ∀ ω, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i) (hat : a0 < t) :
    |∫ ω, transmissionRatio x y (μ t ω) ∂P - stripV P μ a0 t P' k N X Y τ a0 (t - a0)| ≤
      2 * P'.real {ω' | τ ω' ≤ ((t - a0).toNNReal : WithTop ℝ≥0)} := by
  have hstart : ∀ ω, N 0 ω = p := fun ω => (hst ω).1
  obtain ⟨Cm, hCm0, hCm⟩ := exists_mass_bound hmeas hmass ha0 hat.le
  have hL : 0 < t - a0 := by linarith
  have hVm := measurable_stripV (P := P) (t := t) (k := k) h hpath hτ hk hmeas hcont ha0
  have hVb : ∀ s r, |stripV P μ a0 t P' k N X Y τ s r| ≤ 1 := abs_stripV_le h hpath hk0
  have hf1m : Measurable fun s => stripV P μ a0 t P' k N X Y τ s 0 :=
    hVm.comp (f := fun s => (s, (0 : ℝ))) (measurable_id.prodMk measurable_const)
  have hf2m : Measurable fun r => stripV P μ a0 t P' k N X Y τ a0 r :=
    hVm.comp (f := fun r => (a0, r)) (measurable_const.prodMk measurable_id)
  have hG : ContinuousOn (fun u => ∫ ω, transmissionRatio x y (μ u ω) ∂P) (Ioi 0) :=
    continuousOn_integral_ratio hmeas (ae_of_all _ hcont) (IsRatioParameter.isRatioRange hxy)
  have hf1c : ContinuousAt (fun s => stripV P μ a0 t P' k N X Y τ s 0) t := by
    have : (fun s => stripV P μ a0 t P' k N X Y τ s 0) =
        (fun u => ∫ ω, transmissionRatio x y (μ u ω) ∂P) ∘ clampT a0 t :=
      funext fun s => stripV_zero h hst s
    rw [this]
    exact (hG.comp_continuous (continuous_clampT a0 t)
      fun s => lt_of_lt_of_le ha0 (le_max_left _ _)).continuousAt
  have hf2c : ContinuousAt (fun r => stripV P μ a0 t P' k N X Y τ a0 r) (t - a0) :=
    (continuous_stripV_right h hpath hτ hk hk0 hmeas hcont ha0 a0).continuousAt
  have hf1t : stripV P μ a0 t P' k N X Y τ t 0 = ∫ ω, transmissionRatio x y (μ t ω) ∂P := by
    rw [stripV_zero h hst, clampT_of_mem ⟨hat.le, le_rfl⟩]
  rw [← hf1t]
  have hhc : Continuous (absorptionRate E κ) := by
    unfold absorptionRate; exact continuous_const.mul hκ
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous (hhc.continuousOn (s := Icc a0 t))
  refine le_of_forall_pos_le_add fun e he => ?_
  have hpM : 0 ≤ (p : ℝ) * (M + 1) := by positivity
  have hA : 0 ≤ (p : ℝ) * (M + 1) * (t - a0) := by positivity
  set ε' := e / (2 * (p * (M + 1) * (t - a0) + 1)) with hε'def
  have hden : 0 < 2 * ((p : ℝ) * (M + 1) * (t - a0) + 1) := by positivity
  have hε'0 : 0 < ε' := div_pos he hden
  have hε'eq : ε' * (2 * (p * (M + 1) * (t - a0) + 1)) = e := by
    rw [hε'def]; field_simp
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.uniformContinuousOn_iff.1 huc ε' hε'0
  obtain ⟨δ2, hδ2, hδ2'⟩ := abs_integral_left_sub_le hf1c (ε := e / 4) (by positivity)
  obtain ⟨δ3, hδ3, hδ3'⟩ := abs_integral_left_sub_le hf2c (ε := e / 4) (by positivity)
  set η := min (min δ1 δ2) (min δ3 (t - a0)) / 2 with hηdef
  have hm0 : 0 < min (min δ1 δ2) (min δ3 (t - a0)) := lt_min (lt_min hδ1 hδ2) (lt_min hδ3 hL)
  have hη0 : 0 < η := half_pos hm0
  have hηm : η < min (min δ1 δ2) (min δ3 (t - a0)) := half_lt_self hm0
  have hη1 : η < δ1 := hηm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hη2 : η < δ2 := hηm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hη3 : η < δ3 := hηm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηL : η ≤ t - a0 := (hηm.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hδ : ∀ q ∈ stripSet a0 t η, |k q.2 - absorptionRate E κ q.1| ≤ ε' := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hq
    rw [hkh]
    have ha : t - q.2 ∈ Icc a0 t := ⟨by linarith, by linarith⟩
    have hb : q.1 ∈ Icc a0 t := ⟨h1, by linarith⟩
    have hd : dist (t - q.2) q.1 < δ1 := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hδ1' _ ha _ hb hd
    rw [Real.dist_eq] at this; exact this.le
  have hest := strip_estimate h hpath hstart hτ hM hε hε1 hU hk hk0 hkC hκ hhC hmeas hcont ha0 hCm0
    hCm hMart hat.le hη0.le hηL hε'0.le hδ
  have e2 := hδ2' η hη0 hη2 (intervalIntegrable_of_bdd hf1m (fun s => hVb s 0) _ _)
  have e3 := hδ3' η hη0 hη3 (intervalIntegrable_of_bdd hf2m (fun r => hVb a0 r) _ _)
  have hle : η * ((p : ℝ) * (M + 1) * ε' * (t - a0)) ≤ η * (e / 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hη0.le
  have h1 := abs_le.1 hest
  have h2 := abs_le.1 e2
  have h3 := abs_le.1 e3
  have key : |η * (stripV P μ a0 t P' k N X Y τ t 0 - stripV P μ a0 t P' k N X Y τ a0 (t - a0))| ≤
      η * (2 * P'.real {ω' | τ ω' ≤ ((t - a0).toNNReal : WithTop ℝ≥0)} + e) :=
    abs_le.2 ⟨by nlinarith, by nlinarith⟩
  rw [abs_mul, abs_of_pos hη0] at key
  exact le_of_mul_le_mul_left key hη0

end BlockBand.Transmission.LawDuality
