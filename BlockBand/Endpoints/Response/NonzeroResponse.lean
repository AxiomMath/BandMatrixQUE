module

public import BlockBand.Endpoints.Response.NonzeroResponseRepresentation
public import BlockBand.Endpoints.Response.ResponseVariancePass

/-!
# Nonzero response in every Fourier mode

For every `τ > 0` and every integer `m ≠ 0` there is a finite `x > 0` with `J_{τ,m}(x, 0) > 0`,
where `J_{τ,m}` is the signed response of the response-variance theorem. This file states the
proposition (`NonzeroResponseStatement`) and proves it (`nonzeroResponse`) from
`DualBoundaryStartContract`, `LifetimeBridgeStatement` and the bridge-occupation lemma.

In Lean, `NonzeroResponseStatement` says: for every `D₀ > 0`, `τ > 0`, `m ∈ ℤ∖{0}` there are
`x > 0` and `J > 0` with `IsSignedResponse D₀ τ q_m x 0 J`, `q_m = rvCosineTest τ m`
(`cos(2πms/τ)`), a functional of the `p = 1` boundary dual. The hypotheses are
`DualBoundaryStartContract` (fields `exists_` and `firstMoment`), `LifetimeBridgeStatement` and
`BridgeOccupationStatement`. The last two are inconsistent together
(`not_bridgeOccupationStatement_of_lifetimeBridge`); the same proof with the measurable variant
`BridgeOccupationMeasStatement` is `nonzeroResponse_of_occMeas`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-- The nonzero-response proposition: for every `D₀ > 0`, `τ > 0` and `m ≠ 0` there is `x > 0`
such that the signed response `J_{τ,m}(x, 0)` of the `p = 1` boundary dual is positive. -/
def NonzeroResponseStatement : Prop :=
  ∀ D0 : ℝ, 0 < D0 → ∀ τ : ℝ, 0 < τ → ∀ m : ℤ, m ≠ 0 →
    ∃ x : ℝ, 0 < x ∧ ∃ J : ℝ, 0 < J ∧ IsSignedResponse D0 τ (rvCosineTest τ m) x 0 J

/-!
### Elementary facts
-/

/-- `q_m(s) = cos(2πms/τ) ≥ 1/2` for `0 ≤ s ≤ τ/(6|m|)`. -/
theorem nzr_cos_ge_half {τ : ℝ} (hτ : 0 < τ) {m : ℤ} (hm : m ≠ 0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ τ / (6 * |(m : ℝ)|)) : 1 / 2 ≤ rvCosineTest τ m s := by
  unfold rvCosineTest
  have hm' : 0 < |(m : ℝ)| := abs_pos.2 (by exact_mod_cast hm)
  have hθ : |2 * Real.pi * m * s / τ| ≤ Real.pi / 3 := by
    rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
    have h1 : |2 * Real.pi * m * s| = 2 * Real.pi * |(m : ℝ)| * s := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos Real.pi_pos, abs_of_nonneg hs0]
    rw [h1]
    have h2 : s * (6 * |(m : ℝ)|) ≤ τ := (le_div_iff₀ (by positivity)).1 hs
    nlinarith [Real.pi_pos]
  rw [← Real.cos_abs, ← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    (by linarith [Real.pi_pos]) hθ

/-- A radius `r₀ ≥ r₁, 1` with `C(e^{-δr₀/τ} + r₀e^{-r₀}) < 1/3`. -/
theorem nzr_choose_radius {δ τ C : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) (r₁ : ℝ) :
    ∃ r₀ : ℝ, r₁ ≤ r₀ ∧ 1 ≤ r₀ ∧
      C * (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀)) < 1 / 3 := by
  have h1 : Tendsto (fun r : ℝ => Real.exp (-(δ * r / τ))) atTop (𝓝 0) := by
    have : Tendsto (fun r : ℝ => δ / τ * r) atTop atTop :=
      tendsto_id.const_mul_atTop (div_pos hδ hτ)
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).congr fun r => ?_
    simp only [Function.comp]
    congr 1
    ring
  have h2 : Tendsto (fun r : ℝ => r * Real.exp (-r)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h3 : Tendsto (fun r : ℝ => C * (Real.exp (-(δ * r / τ)) + r * Real.exp (-r))) atTop
      (𝓝 0) := by
    simpa using (h1.add h2).const_mul C
  obtain ⟨r₀, hr₀⟩ := ((h3.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))).and
    ((eventually_ge_atTop r₁).and (eventually_ge_atTop 1))).exists
  exact ⟨r₀, hr₀.2.1, hr₀.2.2, hr₀.1⟩

/-!
### The pointwise comparison at a fixed lifetime
-/

/-- At every lifetime `t ∈ (0, τ]`, `A_{q⁻}(t) < A_{q⁺}(t)`: if `q ≥ 1/2` on `(0, δ]`, `|q| ≤ 1`,
and the late occupation after `δ` is at most `ε < 1/3` times the (finite, positive) full
occupation. -/
theorem nzr_inner_lt {τ δ ε t : ℝ} (hδ : 0 < δ) {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    {q : ℝ → ℝ} (hq1 : ∀ s, |q s| ≤ 1) (hqδ : ∀ s ∈ Ioc 0 δ, 1 / 2 ≤ q s) (ht : t ∈ Ioc 0 τ)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 3) (hfin : bridgeOccupation p z t 0 t ≠ ⊤)
    (hpos : 0 < bridgeOccupation p z t 0 t)
    (hlate : bridgeOccupation p z t δ t ≤ ENNReal.ofReal ε * bridgeOccupation p z t 0 t) :
    nzr_inner τ p z (nzr_neg q) t < nzr_inner τ p z (nzr_pos q) t := by
  classical
  set M : ℝ → ℝ≥0∞ := fun s => bridgeMeanTotal p z t s with hM
  set full := bridgeOccupation p z t 0 t
  set late := bridgeOccupation p z t δ t
  set early := ∫⁻ s in Ioo 0 t ∩ Iic δ, M s
  have hsplit : early + late = full := by
    have hset : Ioo 0 t \ Iic δ = Ioo δ t := by
      ext s
      simp only [Set.mem_sdiff, mem_Ioo, mem_Iic, not_le]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hδ.trans h1, h2⟩, h1⟩
    have := lintegral_inter_add_sdiff (μ := volume) M (Ioo 0 t) (measurableSet_Iic (a := δ))
    rw [hset] at this
    exact this
  -- `A_{q⁺} ≥ ½ early`
  have hplus : ENNReal.ofReal (1 / 2) * early ≤ nzr_inner τ p z (nzr_pos q) t := by
    unfold nzr_inner
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator (measurableSet_Ioo.inter measurableSet_Iic),
      ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_mono fun s => ?_
    by_cases hs : s ∈ Ioo 0 t ∩ Iic δ
    · have hsτ : s ∈ Ioc 0 τ := ⟨hs.1.1, hs.1.2.le.trans ht.2⟩
      rw [indicator_of_mem hs, indicator_of_mem hsτ, ite_eq_left hs.1.2]
      refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
      exact (hqδ s ⟨hs.1.1, hs.2⟩).trans (le_max_left _ _)
    · rw [indicator_of_notMem hs]
      exact bot_le
  -- `A_{q⁻} ≤ late`
  have hminus : nzr_inner τ p z (nzr_neg q) t ≤ late := by
    unfold nzr_inner
    simp only [late, bridgeOccupation]
    rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_mono fun s => ?_
    by_cases hs : s ∈ Ioc 0 τ
    · rw [indicator_of_mem hs]
      by_cases hsδ : s ≤ δ
      · have : nzr_neg q s = 0 := by
          unfold nzr_neg
          have := hqδ s ⟨hs.1, hsδ⟩
          exact max_eq_right (by linarith)
        rw [this, ENNReal.ofReal_zero, zero_mul]
        exact bot_le
      · by_cases hst : s < t
        · rw [ite_eq_left hst, indicator_of_mem (show s ∈ Ioo δ t from ⟨not_le.1 hsδ, hst⟩)]
          calc ENNReal.ofReal (nzr_neg q s) * bridgeMeanTotal p z t s
              ≤ 1 * bridgeMeanTotal p z t s :=
                mul_le_mul_left (ENNReal.ofReal_le_one.2 (nzr_neg_bounds hq1 s).2) _
            _ = _ := one_mul _
        · rw [ite_eq_right hst, mul_zero]
          exact bot_le
    · rw [indicator_of_notMem hs]
      exact bot_le
  -- `late < ½ early`
  have hearly_fin : early ≠ ⊤ := ne_top_of_le_ne_top hfin (hsplit ▸ le_self_add)
  have hlate_fin : late ≠ ⊤ := ne_top_of_le_ne_top hfin (hsplit ▸ le_add_self)
  have hmid : late < ENNReal.ofReal (1 / 2) * early := by
    rw [← ENNReal.toReal_lt_toReal hlate_fin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hearly_fin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
    have hF : full.toReal = early.toReal + late.toReal := by
      rw [← hsplit, ENNReal.toReal_add hearly_fin hlate_fin]
    have hL : late.toReal ≤ ε * full.toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hlate
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε0] at this
    have hFpos : 0 < full.toReal := ENNReal.toReal_pos hpos.ne' hfin
    nlinarith
  exact (hminus.trans_lt hmid).trans_le hplus

/-!
### The theorem
-/

/-- **Nonzero response**, from `DualBoundaryStartContract`, `LifetimeBridgeStatement` and
`BridgeOccupationStatement`.
-/
theorem nonzeroResponse (hBdry : DualBoundaryStartContract) (hLB : LifetimeBridgeStatement)
    (hOcc : BridgeOccupationStatement) : NonzeroResponseStatement := by
  intro D0 hD0 τ hτ m hm
  obtain ⟨p, hpd, hpm, -, hstart⟩ := hLB D0 hD0
  obtain ⟨c, hc, C, hC, r₁, hO'⟩ := hOcc (D0 * τ) (mul_pos hD0 hτ)
  have hO := hO' D0 τ hD0 hτ rfl
  have hm' : 0 < |(m : ℝ)| := abs_pos.2 (by exact_mod_cast hm)
  have hm1 : 1 ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hm
  set δ := τ / (6 * |(m : ℝ)|) with hδdef
  have hδ : 0 < δ := by positivity
  have hδτ : δ < τ := by
    rw [hδdef, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨r₀, hr₁, hr₀1, hsmall⟩ := nzr_choose_radius (C := C) hδ hτ r₁
  set x := (Real.cosh r₀ - 1) / 2 with hxdef
  have hx : 0 < x := by
    have := Real.one_lt_cosh.2 (show r₀ ≠ 0 by linarith)
    rw [hxdef]; linarith
  have hds : IsDualStart ![x] ![0] :=
    isDualStart_one hx.le le_rfl zero_le_one (fun h => hx.ne' h.1)
  obtain ⟨hpos, -, hdis⟩ := hstart x 0 hds
  set q := rvCosineTest τ m
  have hq := rvCosineTest_continuous τ m
  have hq1 := rvCosineTest_abs_le τ m
  have hqδ : ∀ s ∈ Ioc 0 δ, 1 / 2 ≤ q s := fun s hs => nzr_cos_ge_half hτ hm hs.1.le hs.2
  set ε := C * (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀))
  have hε0 : 0 ≤ ε := mul_nonneg hC (by positivity)
  have hz : bridgeStart r₀ = (x, 0) := rfl
  -- a realization, and the representation
  obtain ⟨Ω, mΩ, 𝓖, P, N, X, Y, hR⟩ := hBdry.exists_ D0 hD0 x 0 hds
  have hrep := nzr_response_eq hτ hq hq1 hpm hBdry hD0 hds hR (hdis Ω mΩ 𝓖 P N X Y hR).2
  have hKp : nzr_kernelPart D0 τ p (x, 0) (nzr_pos q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrep.1
  have hKm : nzr_kernelPart D0 τ p (x, 0) (nzr_neg q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrep.2.1
  -- strict comparison of the kernel parts
  have hlt : nzr_kernelPart D0 τ p (x, 0) (nzr_neg q) <
      nzr_kernelPart D0 τ p (x, 0) (nzr_pos q) := by
    have hpt : ∀ t ∈ Ioc 0 τ, nzr_inner τ p (x, 0) (nzr_neg q) t <
        nzr_inner τ p (x, 0) (nzr_pos q) t := by
      intro t ht
      obtain ⟨hfin, hlow, hlate⟩ := hO p hpd r₀ hr₁ t ht
      rw [hz] at hfin hlow hlate
      have hpos' : 0 < bridgeOccupation p (x, 0) t 0 t := by
        refine lt_of_lt_of_le ?_ hlow
        exact ENNReal.ofReal_pos.2 (by have := ht.1; positivity)
      exact nzr_inner_lt hδ hq1 hqδ ht hε0 hsmall hfin hpos' (hlate δ ⟨hδ, hδτ⟩)
    have hρ : ∀ t ∈ Ioc 0 τ, nzr_cut τ t * ENNReal.ofReal (cornerLifetimeDensity D0 p (x, 0) t) ≠ 0 ∧
        nzr_cut τ t * ENNReal.ofReal (cornerLifetimeDensity D0 p (x, 0) t) ≠ ⊤ := by
      intro t ht
      have hcut : nzr_cut τ t = 1 := by
        unfold nzr_cut; rw [indicator_of_mem (show t ∈ Iic τ from ht.2)]
      rw [hcut, one_mul]
      refine ⟨(ENNReal.ofReal_pos.2 ?_).ne', ENNReal.ofReal_ne_top⟩
      unfold cornerLifetimeDensity
      have := hpos t ht.1
      simp only [add_zero]
      positivity
    unfold nzr_kernelPart
    refine lintegral_strict_mono_of_ae_le_of_ae_lt_on (s := Ioc 0 τ) ?_ hKm ?_ ?_ ?_
    · exact (((nzr_cut_measurable τ).mul (nzr_rho_measurable hpm D0 (x, 0))).mul
        (nzr_inner_measurable hpm τ (x, 0) (nzr_pos_continuous hq).measurable)).aemeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
      by_cases htτ : t ≤ τ
      · have h := hρ t ⟨ht0, htτ⟩
        exact ((ENNReal.mul_lt_mul_iff_right h.1 h.2).2 (hpt t ⟨ht0, htτ⟩)).le
      · have hcut : nzr_cut τ t = 0 := by
          unfold nzr_cut; rw [indicator_of_notMem (show t ∉ Iic τ from htτ)]
        simp [hcut]
    · rw [Measure.restrict_apply measurableSet_Ioc,
        inter_eq_left.2 Ioc_subset_Ioi_self, Real.volume_Ioc]
      exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
    · exact ae_of_all _ fun t ht => by
        have h := hρ t ht
        exact (ENNReal.mul_lt_mul_iff_right h.1 h.2).2 (hpt t ht)
  refine ⟨x, hx, _, (ENNReal.toReal_lt_toReal hKm hKp).2 hlt |> sub_pos.2, ?_⟩
  refine Or.inr ⟨fun h => hx.ne' h.1, ⟨Ω, mΩ, 𝓖, P, N, X, Y, hR⟩, ?_⟩
  intro Ω' m' 𝓖' P' N' X' Y' hR'
  exact (nzr_response_eq hτ hq hq1 hpm hBdry hD0 hds hR' (hdis Ω' m' 𝓖' P' N' X' Y' hR').2).2.2

/-- Every value of the signed response at the detecting start is positive (uniqueness of the
value, `rv_isSignedResponse_unique`). -/
theorem nonzeroResponse_all (hBdry : DualBoundaryStartContract) (hLB : LifetimeBridgeStatement)
    (hOcc : BridgeOccupationStatement) {D0 τ : ℝ} (hD0 : 0 < D0) (hτ : 0 < τ) {m : ℤ}
    (hm : m ≠ 0) : ∃ x : ℝ, 0 < x ∧ (∃ J, IsSignedResponse D0 τ (rvCosineTest τ m) x 0 J) ∧
      ∀ J, IsSignedResponse D0 τ (rvCosineTest τ m) x 0 J → 0 < J := by
  obtain ⟨x, hx, J, hJ, hS⟩ := nonzeroResponse hBdry hLB hOcc D0 hD0 τ hτ m hm
  exact ⟨x, hx, ⟨J, hS⟩, fun J' hS' => (rv_isSignedResponse_unique hS hS').symm ▸ hJ⟩

/-- The instance `D₀ = transportD0 b E` (fixed `0 < b`, bulk `E`), the `J_{τ,m}` of
`responseVariance`. -/
theorem nonzeroResponse_transport (hBdry : DualBoundaryStartContract)
    (hLB : LifetimeBridgeStatement) (hOcc : BridgeOccupationStatement) {b E : ℝ} (hb : 0 < b)
    (hE1 : -2 < E) (hE2 : E < 2) {τ : ℝ} (hτ : 0 < τ) {m : ℤ} (hm : m ≠ 0) :
    ∃ x : ℝ, 0 < x ∧ (∃ J, IsSignedResponse (transportD0 b E) τ (rvCosineTest τ m) x 0 J) ∧
      ∀ J, IsSignedResponse (transportD0 b E) τ (rvCosineTest τ m) x 0 J → 0 < J :=
  nonzeroResponse_all hBdry hLB hOcc (transportD0_pos hb hE1 hE2) hτ hm

end BlockBand.Endpoints
