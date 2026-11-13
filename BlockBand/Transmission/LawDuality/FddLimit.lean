module

public import BlockBand.Transmission.LawDuality.FddStrip

/-!
# Conditional strip: `η → 0` and `K → ∞` under `RatioIncFrom`

The limits `η → 0` and `K → ∞` of the strip argument, assuming only forward increments after `a₀`:
`ratio_eq_stripV_top_from` is the unstopped backward identity
`E F_{x,y}(μ_t) = V(a₀, t − a₀)` under `RatioIncFrom … a₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

section Eta

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

include h hpath hτ hk hk0 hmeas hcont ha0 in
/-- **`abs_ratio_sub_stripV_le` under `RatioIncFrom … a₀`.** -/
theorem abs_ratio_sub_stripV_le_from {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hU : StaysIn N X Y τ M ε) {Ck : ℝ} (hkC : ∀ v, k v ≤ Ck) {E : ℝ} {κ : ℝ → ℝ}
    (hκ : Continuous κ) {Ch : ℝ} (hhC : ∀ u, |absorptionRate E κ u| ≤ Ch)
    (hkh : ∀ v, k v = absorptionRate E κ (t - v)) (hInc : RatioIncFrom D0 E κ P μ a0)
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
  have hest := strip_estimate_from h hpath hstart hτ hM hε hε1 hU hk hk0 hkC hκ hhC hmeas hcont ha0
    hCm0 hCm hInc hat.le hη0.le hηL hε'0.le hδ
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

end Eta

section Top

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {Ω' : Type*} [m' : MeasurableSpace Ω'] {P' : Measure Ω'} {𝓖 : Filtration ℝ≥0 m'} {D0 : ℝ}
  {p : ℕ} {x y : Fin p → ℝ} {N : ℝ≥0 → Ω' → ℕ} {X Y : ℝ≥0 → Ω' → ℕ → ℝ}
  (h : IsDualDeletionProcess P' 𝓖 D0 x y N X Y)
  (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ v, 0 ≤ k v)
  (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hcont : ∀ ω, ContinuousOn (fun t => μ t ω) (Ioi 0))
  {a0 t : ℝ} (ha0 : 0 < a0)

include h hpath hk hk0 hmeas hcont ha0 in
/-- **The unstopped backward identity at `a₀`, from forward increments after `a₀` only.** -/
theorem ratio_eq_stripV_top_from {Ck : ℝ} (hkC : ∀ v, k v ≤ Ck) {E : ℝ} {κ : ℝ → ℝ}
    (hκ : Continuous κ) {Ch : ℝ} (hhC : ∀ u, |absorptionRate E κ u| ≤ Ch)
    (hkh : ∀ v, k v = absorptionRate E κ (t - v)) (hInc : RatioIncFrom D0 E κ P μ a0)
    (hmass : HasLocalMassBound P μ) (hxy : IsRatioParameter x y)
    (hst : ∀ ω, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i) (hat : a0 < t) :
    ∫ ω, transmissionRatio x y (μ t ω) ∂P =
      stripV P μ a0 t P' k N X Y (fun _ => ⊤) a0 (t - a0) := by
  set V0 := ∑ i : Fin p, capFun (x i, y i)
  have hL : 0 ≤ t - a0 := by linarith
  have hev : ∀ᶠ K : ℝ in atTop, |∫ ω, transmissionRatio x y (μ t ω) ∂P -
      stripV P μ a0 t P' k N X Y (fun _ => ⊤) a0 (t - a0)| ≤
        4 * P'.real {ω' | capTau N X Y K ω' ≤ ((t - a0).toNNReal : WithTop ℝ≥0)} := by
    filter_upwards [eventually_gt_atTop (max V0 0)] with K hK
    have hK0 : 0 ≤ K := (le_max_right _ _).trans hK.le
    have h0 : ∀ ω, capV N X Y 0 ω < K := fun ω => by
      rw [capV_zero_eq (hst ω)]; exact lt_of_le_of_lt (le_max_left _ _) hK
    have hτ := isStoppingTime_capTau h hpath K
    have hε : 0 < 1 / (1 + K) := by positivity
    have hε1 : 1 / (1 + K) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have e1 := abs_ratio_sub_stripV_le_from h hpath hτ hk hk0 hmeas hcont ha0 hK0 hε hε1
      (staysIn_capTau hpath hK0 h0) hkC hκ hhC hkh hInc hmass hxy hst hat
    have e2 := abs_stripV_sub_top_le (P := P) (t := t) h hpath hk hk0 hmeas hcont ha0 hτ a0 hL
    have := abs_sub_le (∫ ω, transmissionRatio x y (μ t ω) ∂P)
      (stripV P μ a0 t P' k N X Y (capTau N X Y K) a0 (t - a0))
      (stripV P μ a0 t P' k N X Y (fun _ => ⊤) a0 (t - a0))
    linarith
  have hT := (tendsto_measureReal_capTau_le h hpath (t - a0).toNNReal).const_mul 4
  rw [mul_zero] at hT
  have := ge_of_tendsto hT hev
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

end Top

end BlockBand.Transmission.LawDuality
