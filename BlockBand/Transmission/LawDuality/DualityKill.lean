module

public import BlockBand.Transmission.LawDuality.GridLimit

/-!
# Duality with killing: the limit `K → ∞`

Removing the capacity stopping time `capTau … K` by letting `K → ∞` gives the unstopped backward
identity `ratio_eq_stripV_top`: for a ratio martingale with local mass bound and `0 < a₀ < t`,
`E F_{x,y}(μ_t)` equals the strip value `V(a₀, t − a₀)` of the unstopped dual process.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

theorem isStoppingTime_top {Ω : Type*} {m : MeasurableSpace Ω} (𝓖 : Filtration ℝ≥0 m) :
    IsStoppingTime 𝓖 (fun _ : Ω => (⊤ : WithTop ℝ≥0)) := fun i => by simp

theorem killFac_eq_top_of_lt {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    {τ : Ω → WithTop ℝ≥0} (k : ℝ → ℝ) {ω : Ω} {r : ℝ} (hr : 0 ≤ r)
    (hlt : (r.toNNReal : WithTop ℝ≥0) < τ ω) :
    killFac k N X Y τ r ω = killFac k N X Y (fun _ => ⊤) r ω := by
  simp only [killFac, killExp]
  congr 2
  rw [max_eq_left hr]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le hr] at hv
  have h1 : killInd (τ ω) v = 1 := ite_eq_left_iff.2 fun h' =>
    absurd (lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hv.2)) hlt) h'
  have h2 : killInd (⊤ : WithTop ℝ≥0) v = 1 :=
    ite_eq_left_iff.2 fun h' => absurd (WithTop.coe_lt_top _) h'
  simp only [h1, h2]

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
theorem abs_stripV_sub_top_le {τ : Ω' → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (s : ℝ) {r : ℝ}
    (hr : 0 ≤ r) :
    |stripV P μ a0 t P' k N X Y τ s r - stripV P μ a0 t P' k N X Y (fun _ => ⊤) s r| ≤
      2 * P'.real {ω' | τ ω' ≤ (r.toNNReal : WithTop ℝ≥0)} := by
  have := h.prob
  have hS : MeasurableSet {ω' | τ ω' ≤ (r.toNNReal : WithTop ℝ≥0)} := 𝓖.le _ _ (hτ r.toNNReal)
  have hint : ∀ σ : Ω' → WithTop ℝ≥0, IsStoppingTime 𝓖 σ → Integrable (fun ω' =>
      ratioAvg P μ a0 t N X Y σ s r ω' * killFac k N X Y σ r ω') P' := fun σ hσ =>
    Integrable.of_bound (((measurable_ratioAvg (P := P) (t := t) h hpath hσ hmeas hcont ha0).comp
      (f := fun ω' => ((s, r), ω')) (measurable_const.prodMk measurable_id)).mul
      ((measurable_killFac_joint h hpath hσ hk).comp (f := fun ω' => (r, ω'))
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable 1
      (ae_of_all _ fun ω' => by
        have hK := killFac_mem (τ := σ) (hpath ω') hk0 r
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hK.1]
        exact (mul_le_mul (abs_ratioAvg_le hpath s r ω') hK.2 hK.1.le zero_le_one).trans
          (le_of_eq (one_mul 1)))
  show |(∫ ω', ratioAvg P μ a0 t N X Y τ s r ω' * killFac k N X Y τ r ω' ∂P') -
    ∫ ω', ratioAvg P μ a0 t N X Y (fun _ => ⊤) s r ω' * killFac k N X Y (fun _ => ⊤) r ω' ∂P'| ≤ _
  rw [← integral_sub (hint τ hτ) (hint _ (isStoppingTime_top 𝓖)), ← Real.norm_eq_abs]
  have hg : Integrable (fun ω' => (2 : ℝ) * {ω' | τ ω' ≤ (r.toNNReal : WithTop ℝ≥0)}.indicator (1 : Ω' → ℝ) ω') P' :=
    ((integrable_const (1 : ℝ)).indicator hS).const_mul _
  refine (norm_integral_le_of_norm_le hg (ae_of_all _ fun ω' => ?_)).trans
    (le_of_eq (by rw [integral_const_mul, integral_indicator_one hS]))
  rw [Real.norm_eq_abs]
  by_cases hω : τ ω' ≤ (r.toNNReal : WithTop ℝ≥0)
  · rw [indicator_of_mem (show ω' ∈ {ω' | τ ω' ≤ (r.toNNReal : WithTop ℝ≥0)} from hω),
      Pi.one_apply, mul_one]
    have b := fun σ : Ω' → WithTop ℝ≥0 => (show |ratioAvg P μ a0 t N X Y σ s r ω' *
        killFac k N X Y σ r ω'| ≤ 1 from by
      have hK := killFac_mem (τ := σ) (hpath ω') hk0 r
      rw [abs_mul, abs_of_pos hK.1]
      exact (mul_le_mul (abs_ratioAvg_le hpath s r ω') hK.2 hK.1.le zero_le_one).trans
        (le_of_eq (one_mul 1)))
    have := abs_sub (ratioAvg P μ a0 t N X Y τ s r ω' * killFac k N X Y τ r ω')
      (ratioAvg P μ a0 t N X Y (fun _ => ⊤) s r ω' * killFac k N X Y (fun _ => ⊤) r ω')
    linarith [b τ, b (fun _ => ⊤)]
  · have hlt : (r.toNNReal : WithTop ℝ≥0) < τ ω' := not_le.1 hω
    rw [indicator_of_notMem (show ω' ∉ {ω' | τ ω' ≤ (r.toNNReal : WithTop ℝ≥0)} from hω), mul_zero,
      killFac_eq_top_of_lt k hr hlt]
    have : ratioAvg P μ a0 t N X Y τ s r ω' = ratioAvg P μ a0 t N X Y (fun _ => ⊤) s r ω' :=
      integral_congr_ae (ae_of_all _ fun ω => by
        beta_reduce
        rw [ratioStop_of_lt _ hlt, ratioStop_of_lt (τ := fun _ => ⊤) _ (WithTop.coe_lt_top _)])
    rw [this, sub_self, abs_zero]

include h hpath hk hk0 hmeas hcont ha0 in
/-- **The unstopped backward identity at a positive forward time `a₀`.** -/
theorem ratio_eq_stripV_top {Ck : ℝ} (hkC : ∀ v, k v ≤ Ck) {E : ℝ} {κ : ℝ → ℝ}
    (hκ : Continuous κ) {Ch : ℝ} (hhC : ∀ u, |absorptionRate E κ u| ≤ Ch)
    (hkh : ∀ v, k v = absorptionRate E κ (t - v)) (hMart : IsRatioMartingale D0 E κ P μ)
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
    have e1 := abs_ratio_sub_stripV_le h hpath hτ hk hk0 hmeas hcont ha0 hK0 hε hε1
      (staysIn_capTau hpath hK0 h0) hkC hκ hhC hkh hMart hmass hxy hst hat
    have e2 := abs_stripV_sub_top_le (P := P) (t := t) h hpath hk hk0 hmeas hcont ha0 hτ a0 hL
    have := abs_sub_le (∫ ω, transmissionRatio x y (μ t ω) ∂P)
      (stripV P μ a0 t P' k N X Y (capTau N X Y K) a0 (t - a0))
      (stripV P μ a0 t P' k N X Y (fun _ => ⊤) a0 (t - a0))
    linarith
  have hT := (tendsto_measureReal_capTau_le h hpath (t - a0).toNNReal).const_mul 4
  rw [mul_zero] at hT
  have := ge_of_tendsto hT hev
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

end BlockBand.Transmission.LawDuality
