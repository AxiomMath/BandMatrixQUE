module

public import BlockBand.Endpoints.Transmission.AlongRatioMart
public import BlockBand.Transmission.LawForced.MassBound
public import BlockBand.Transmission.LawFinite.LawFiniteAll

/-!
# The ratio martingale problem along moving energies

This file shows that every transmission sub-limit along a moving energy solves the ratio martingale
problem at the base energy, with the entrance condition and locally bounded mean mass.

Fix `0 < b < 1/2`, `-2 < E < 2`, an admissible profile `κ`, a moving energy `e` with
`IsMovingEnergy E Ce e` (`|e W - E| ≤ Ce/W²`) and `φ → ∞`. Every `(Ω, P, μ)` with
`IsTransmissionSubLimitAlong b e κ φ P μ` satisfies:

* `IsRatioMartingale (transportD0 b E) E κ P μ`, at the base energy `E` (proved in the sibling
  module, `isRatioMartingale_along`);
* `hasRatioEntrance_along`: `HasRatioEntrance P μ`. The proof follows
  `LawDuality.hasRatioEntrance_of`, with the width-`W` process at `e W_n`, and uses the
  bulk-uniform entrance bound `LawFinite.transmissionEntranceBulk_of_baseContracts` at `E := e W_n` once
  `e W_n` is in the bulk (`LawFinite.eventually_mem_bulkInterval`);
* `hasLocalMassBound_along`: `HasLocalMassBound P μ`. The proof follows
  `LawForced.hasLocalMassBound_of_baseContracts`, with the bulk-uniform input
  `Absorbed.absorbedConductance_bulk`;
* `subLimitRatioMP_along`: the conjunction of the three.

The hypotheses are `MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient`
and `GaussianPoincare` (the last used only for the martingale property).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Transmission

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.LawDuality BlockBand.Transmission.LawForced
open BlockBand.Transmission.LawFinite BlockBand.Transmission.Absorbed
open scoped NNReal ENNReal BoundedContinuousFunction

/-- **Every sub-limit along a moving energy has the entrance**. -/
theorem hasRatioEntrance_along (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b E Ce : ℝ} {e : ℕ → ℝ}
    {κ : ℝ → ℝ} {φ : ℕ → ℕ} (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (he : IsMovingEnergy E Ce e) (hκ : IsAbsorptionProfile κ) (hφ : Tendsto φ atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (h : IsTransmissionSubLimitAlong b e κ φ P μ) : HasRatioEntrance P μ := by
  intro p hp z hz
  have hr : IsRatioRange z.1 z.2 := IsRatioParameter.isRatioRange hz
  set i0 : Fin p := ⟨0, hp⟩
  set c := z.1 i0 / (1 + z.1 i0) + z.2 i0
  have hc : 0 < c := by
    have := (hz.2.2.2 i0).1; have := (hz.2.2.1 i0).le; positivity
  obtain ⟨hκI, -⟩ := mem_bulkInterval_half hE1 hE2
  obtain ⟨C, hC⟩ := transmissionEntranceBulk_of_baseContracts hMT hGA hLp b hb hb2 _ hκI κ hκ
  have := h.prob
  have key : ∀ s, 0 < s → s ≤ 1 → ∀ K, 0 < K →
      ∫ ω, transmissionRatio z.1 z.2 (μ s ω) ∂P ≤ |C| * (1 + K) * s + Real.exp (-c * K) := by
    intro s hs hs1 K hK
    refine le_of_forall_pos_le_add fun θ hθ => ?_
    obtain ⟨W₀, hW₀⟩ := hC K s θ hK hs hs1 hθ
    have hlim := h.fdd 1 ![s] (fun i => by fin_cases i; simpa using hs) (ratioTestVec hr)
    refine le_of_tendsto hlim ?_
    filter_upwards [hφ.eventually_ge_atTop (max W₀ ⌈1 / s⌉₊),
      hφ.eventually (eventually_mem_bulkInterval hE1 hE2 he)] with n hn hEI
    have hn1 : -2 < e (φ n) := by linarith [hEI.1]
    have hn2 : e (φ n) < 2 := by linarith [hEI.2]
    have hWs : 1 ≤ (φ n : ℝ) * s := by
      have h1 : (⌈1 / s⌉₊ : ℝ) ≤ φ n := by exact_mod_cast le_of_max_le_right hn
      have h2 : 1 / s ≤ (⌈1 / s⌉₊ : ℝ) := Nat.le_ceil _
      rw [← div_le_iff₀ hs]; linarith
    have hfin := integral_ratio_finite_le (W := φ n) (b := b) (E := e (φ n)) (κ := κ) (K := K)
      hκ.2.1 (by linarith) hn1 hn2 hr i0 hc.le hWs
    have hP : (growthPathLaw (φ n) b (entranceEvent b (e (φ n)) κ K s (φ n))).toReal ≤
        |C| * (1 + K) * s + θ :=
      ENNReal.toReal_le_of_le_ofReal (by positivity)
        ((hW₀ (φ n) (le_of_max_le_left hn) (e (φ n)) hEI).trans (ENNReal.ofReal_le_ofReal (by
          have : C * (1 + K) * s ≤ |C| * (1 + K) * s := by
            gcongr; exact le_abs_self C
          linarith)))
    change ∫ ω, transmissionRatio z.1 z.2 (transmissionProcess b (e (φ n)) κ (φ n) s ω)
      ∂growthPathLaw (φ n) b ≤ _
    linarith
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun s => lt_of_lt_of_le ha
    (integral_nonneg fun ω => (transmissionRatio_mem_vec hr _).1.le), fun a ha => ?_⟩
  obtain ⟨K, hK, hKa⟩ : ∃ K, 0 < K ∧ Real.exp (-c * K) < a / 2 := by
    have ht : Tendsto (fun K => Real.exp (-c * K)) atTop (𝓝 0) := by
      refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hc)).congr fun K => ?_
      simp [neg_mul]
    obtain ⟨K, hK1, hK2⟩ := ((ht.eventually (gt_mem_nhds (half_pos ha))).and
      (eventually_gt_atTop 0)).exists
    exact ⟨K, hK2, hK1⟩
  have hδ : 0 < min 1 (a / (2 * ((|C| + 1) * (1 + K)))) := lt_min one_pos (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
  have hs1 : s ≤ 1 := hs.2.le.trans (min_le_left _ _)
  have hk := key s hs.1 hs1 K hK
  have h2 : (|C| + 1) * (1 + K) * s < a / 2 := by
    have := hs.2.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have h3 : |C| * (1 + K) * s ≤ (|C| + 1) * (1 + K) * s := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + K) hs.1]
  linarith

/-- **Every sub-limit along a moving energy has locally bounded mean mass**. -/
theorem hasLocalMassBound_along (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b E Ce : ℝ} {e : ℕ → ℝ}
    {κ : ℝ → ℝ} {φ : ℕ → ℕ} (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (he : IsMovingEnergy E Ce e) (hκ : IsAbsorptionProfile κ) (hφ : Tendsto φ atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (h : IsTransmissionSubLimitAlong b e κ φ P μ) : HasLocalMassBound P μ := by
  have := h.prob
  obtain ⟨hκI, -⟩ := mem_bulkInterval_half hE1 hE2
  have hEv : ∀ᶠ n in atTop, e (φ n) ∈ bulkInterval ((2 - |E|) / 2) :=
    hφ.eventually (eventually_mem_bulkInterval hE1 hE2 he)
  obtain ⟨-, hκ0, K, hK⟩ := hκ
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hκK : ∀ s, 0 ≤ κ s ∧ κ s ≤ max K 0 := fun s => ⟨hκ0 s, (hK s).trans (le_max_left _ _)⟩
  intro ε T hε
  obtain ⟨C, hC⟩ := absorbedConductance_bulk hMT hGA hLp b hb hb2 _ (ε / 2) 2 (max K 0) hκI
    (by positivity) (by norm_num) hK0
  obtain ⟨W₀, hW₀⟩ := hC T
  refine ⟨1 + max C 0, fun t ht => ?_⟩
  have ht0 : 0 < t := hε.trans_le ht.1
  -- measurable versions of the finite-`W` one-time states
  set X : ∀ n, GrowthPath (φ n) → St1 := fun n ω _ =>
    stateAt b (e (φ n)) κ (φ n) ⌊((φ n : ℕ) : ℝ) * t⌋₊ ω
  have hX : ∀ n, Measurable (X n) := fun n =>
    measurable_pi_iff.mpr fun _ => measurable_stateAt' b (e (φ n)) κ _
  have hXe : ∀ᶠ n in atTop, ∀ᵐ ω ∂growthPathLaw (φ n) b,
      (fun _ : Fin 1 => transmissionProcess b (e (φ n)) κ (φ n) t ω) = X n ω := by
    filter_upwards [hEv] with n hn
    have hn1 : -2 < e (φ n) := by linarith [hn.1]
    have hn2 : e (φ n) < 2 := by linarith [hn.2]
    filter_upwards [ae_stateAt_eq (W := φ n) hκ0 (by linarith : b < 1) hn1 hn2] with ω hω
    funext i
    simp only [X, hω]
    rfl
  have hY : Measurable fun ω => (fun _ : Fin 1 => μ t ω) :=
    measurable_pi_iff.mpr fun _ => h.measurable t ht0
  have hconv : ∀ Φ : BoundedContinuousFunction St1 ℝ,
      Tendsto (fun n => ∫ ω, Φ (X n ω) ∂growthPathLaw (φ n) b) atTop
        (𝓝 (∫ ω, Φ ((fun ω => (fun _ : Fin 1 => μ t ω)) ω) ∂P)) := by
    intro Φ
    have hf := h.fdd 1 (fun _ => t) (fun _ => ht0) Φ
    refine hf.congr' ?_
    filter_upwards [hXe] with n hn
    refine integral_congr_ae ?_
    filter_upwards [hn] with ω hω
    rw [← hω]
  -- the finite-`W` second moments, eventually in `n`
  have hev : ∀ᶠ n in atTop, W₀ ≤ φ n ∧ 4 / ε ≤ (φ n : ℝ) := by
    have h1 := hφ.eventually_ge_atTop W₀
    have h2 := (tendsto_natCast_atTop_atTop.comp hφ).eventually_ge_atTop (4 / ε)
    filter_upwards [h1, h2] with n hn1 hn2 using ⟨hn1, hn2⟩
  have hCn : ∀ᶠ n in atTop, ∫⁻ ω, ‖massOne (X n ω)‖ₑ ^ 2 ∂growthPathLaw (φ n) b ≤
      ENNReal.ofReal C := by
    filter_upwards [hev, hEv, hXe] with n ⟨hn1, hn2⟩ hEI hXn
    have hE1n : -2 < e (φ n) := by linarith [hEI.1]
    have hE2n : e (φ n) < 2 := by linarith [hEI.2]
    set Wn := φ n
    have hWpos : (0 : ℝ) < Wn := lt_of_lt_of_le (by positivity) hn2
    set r := ⌊(Wn : ℝ) * t⌋₊
    have hWt : 0 ≤ (Wn : ℝ) * t := by positivity
    have hr1 : (ε / 2) * Wn ≤ r := by
      have hfl := Nat.lt_floor_add_one ((Wn : ℝ) * t)
      have h4 : 4 ≤ ε * Wn := by rw [div_le_iff₀ hε] at hn2; linarith
      have : ε * Wn ≤ t * Wn := mul_le_mul_of_nonneg_right ht.1 hWpos.le
      nlinarith
    have hr2 : (r : ℝ) ≤ T * Wn := by
      have := Nat.floor_le hWt
      have : (Wn : ℝ) * t ≤ Wn * T := mul_le_mul_of_nonneg_left ht.2 hWpos.le
      nlinarith
    have hb' := hW₀ Wn hn1 (e (φ n)) hEI κ hκK r hr1 hr2
    refine le_trans (le_of_eq ?_) hb'
    have hm := mass_transmissionProcess (W := Wn) hκ0 (by linarith : b < 1) hE1n hE2n
    refine lintegral_congr_ae ?_
    filter_upwards [hXn, hm] with ω hω hmω
    rw [← hω, massOne_eq_real, hmω t, ENNReal.rpow_two]
    rfl
  have hlim := (BlockBand.Transmission.Generator.tendsto_integral_of_sq_bound
    (μ := fun n => growthPathLaw (φ n) b) hX hY hconv continuous_massOne hCn).1
  calc ∫⁻ ω, (μ t ω : Measure unitInterval) univ ∂P
      = ∫⁻ ω, ‖massOne ((fun ω => (fun _ : Fin 1 => μ t ω)) ω)‖ₑ ∂P :=
        lintegral_congr fun ω => measure_univ_eq_enorm (μ t ω)
    _ ≤ ∫⁻ ω, (1 + ‖massOne ((fun ω => (fun _ : Fin 1 => μ t ω)) ω)‖ₑ ^ 2) ∂P :=
        lintegral_mono fun ω => BlockBand.Transmission.Generator.enorm_le_one_add_sq _
    _ = 1 + ∫⁻ ω, ‖massOne ((fun ω => (fun _ : Fin 1 => μ t ω)) ω)‖ₑ ^ 2 ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal C := add_le_add le_rfl hlim
    _ = ENNReal.ofReal (1 + max C 0) := by
        rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one,
          BlockBand.Transmission.Generator.ofReal_max_zero]

/-- **The ratio martingale problem along moving energies**: every sub-limit
along `e` is a ratio martingale at the base energy `E`, has the entrance, and has locally
bounded mean mass. -/
theorem subLimitRatioMP_along (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    {b E Ce : ℝ} {e : ℕ → ℝ} {κ : ℝ → ℝ} {φ : ℕ → ℕ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (he : IsMovingEnergy E Ce e) (hκ : IsAbsorptionProfile κ)
    (hφ : Tendsto φ atTop atTop) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (h : IsTransmissionSubLimitAlong b e κ φ P μ) :
    IsRatioMartingale (transportD0 b E) E κ P μ ∧ HasRatioEntrance P μ ∧
      HasLocalMassBound P μ :=
  ⟨isRatioMartingale_along hMT hGA hLp hP hb0 hb hE1 hE2 he hκ hφ h,
    hasRatioEntrance_along hMT hGA hLp hb0 hb hE1 hE2 he hκ hφ h,
    hasLocalMassBound_along hMT hGA hLp hb0 hb hE1 hE2 he hκ hφ h⟩

end BlockBand.Endpoints.Transmission
