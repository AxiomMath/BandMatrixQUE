module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Main
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.PredInd
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Initial value, uniqueness by rectangles and the rectangle multiplier identity

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, `h : IsL2Integrator Q 𝓖 N α`,
horizon `T`, `ν_T = bracketMeasure Q α T`, `H ∈ PredL2 𝓖 ν_T`, `Z = h.contIntegral T H`.

* `eq_stochIntegral_of_rect`: a continuous linear map `PredL2 𝓖 ν_T → L²(Q)` sending every
  rectangle `1_{(s,t] × A}` to `1_A (N_t - N_s)` (a.s.) is `stochIntegral h T`.
* `stochIntegral_predInd_rect`: for `q₁ ≤ q₂` (arbitrary, not bounded by `T`) and
  `C ∈ 𝓖_{q₁}`, `∫_0^T 1_{(q₁,q₂] × C} H dN = 1_C (Z_{q₂} - Z_{q₁})` a.s.
  Proof for `q₂ ≤ T`: on the fast simple approximations `x_k` the identity is exact
  (`elemFun_restrict`, `elemProc_restrict`); both sides converge in `L²(Q)` at rate `4⁻ᵏ`
  (isometry and `‖1_R‖ ≤ 1` on the left, the `L²` rate of `contIntegral` on the right).
  The case `q₂ > T` reduces to `q₂ = T` (`ν_T` lives on `(0,T]`, `Z` is constant after `T`).
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {N α : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure Q] in
/-- Two `L²(Q)`-functions whose `L²` distance is `O(4⁻ᵏ)` for every `k` agree a.s. -/
theorem ae_eq_of_eLpNorm_le_geom {f g : Ω → ℝ} (c : ℝ)
    (hb : ∀ k : ℕ, eLpNorm (fun ω => f ω - g ω) 2 Q ≤ ENNReal.ofReal (c * (1 / 4 : ℝ) ^ k)) :
    f =ᵐ[Q] g := by
  have h0 := le_antisymm (ge_of_tendsto' (IsL2Integrator.tendsto_ofReal_geom c) hb) zero_le
  rw [eLpNorm_eq_zero_iff two_ne_zero] at h0
  filter_upwards [h0] with ω hω
  simpa [sub_eq_zero] using hω

theorem elemProc_zero {T : ℝ≥0} (X : ℝ≥0 → Ω → ℝ) (x : Rect 𝓖 T →₀ ℝ) : elemProc X x 0 = 0 := by
  funext ω
  simp [elemProc_apply, rectProc, Rect.clamp]

namespace IsL2Integrator

variable (h : IsL2Integrator Q 𝓖 N α) (T : ℝ≥0)

/-- **Initial value**: `∫_0^0 H dN = 0`, pointwise. -/
theorem contIntegral_zero (H : PredL2 𝓖 (bracketMeasure Q α T)) : h.contIntegral T H 0 = 0 := by
  funext ω
  simp only [contIntegral, approxProc, elemProc_zero, Pi.zero_apply]
  exact tendsto_const_nhds.limUnder_eq

/-- **Uniqueness by rectangles.** -/
theorem eq_stochIntegral_of_rect [IsFiniteMeasure (bracketMeasure Q α T)]
    (L : PredL2 𝓖 (bracketMeasure Q α T) →L[ℝ] Lp ℝ 2 Q)
    (hL : ∀ r : Rect 𝓖 T, (L (rectL2 𝓖 T _ r) : Ω → ℝ) =ᵐ[Q]
      r.A.indicator fun ω => N r.t ω - N r.s ω) :
    L = (h.stochIntegral T).toContinuousLinearMap := by
  refine ContinuousLinearMap.ext_on (s := range (rectL2 𝓖 T (bracketMeasure Q α T)))
    (rectSpan_dense 𝓖 T (bracketMeasure_ae_mem Q α T)) ?_
  rintro _ ⟨r, rfl⟩
  exact Lp.ext ((hL r).trans (h.stochIntegral_rect T r).symm)

/-- Multiplying a simple integrand by `1_{(q₁,q₂] × C}` restricts its rectangles. -/
theorem predInd_integrandLin {q₁ q₂ : ℝ≥0} (hq : q₁ ≤ q₂) (hqT : q₂ ≤ T) {C : Set Ω}
    (hC : MeasurableSet[𝓖 q₁] C) (x : Rect 𝓖 T →₀ ℝ) :
    predInd 𝓖 _ (measurableSet_rect_pred 𝓖 (q₂ := q₂) hC) (h.integrandLin T x) =
      h.integrandLin T (restrictLin hq hqT hC x) := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [predInd_coeFn 𝓖 _ (measurableSet_rect_pred 𝓖 (q₂ := q₂) hC)
      (h.integrandLin T x), integrandLin_ae h x, integrandLin_ae h (restrictLin hq hqT hC x)]
    with p h1 h2 h3
  rw [h1, h3, elemFun_restrict]
  by_cases hp : p ∈ Ioc (q₁ : ℝ) q₂ ×ˢ C
  · rw [indicator_of_mem hp, indicator_of_mem hp, h2, Pi.one_apply, one_mul]
  · rw [indicator_of_notMem hp, indicator_of_notMem hp, zero_mul]

variable (H : PredL2 𝓖 (bracketMeasure Q α T))

theorem stochIntegral_predInd_rect_of_le {q₁ q₂ : ℝ≥0} (hq : q₁ ≤ q₂) (hqT : q₂ ≤ T)
    {C : Set Ω} (hC : MeasurableSet[𝓖 q₁] C) :
    (h.stochIntegral T (predInd 𝓖 _ (measurableSet_rect_pred 𝓖 (q₂ := q₂) hC) H) : Ω → ℝ)
      =ᵐ[Q] C.indicator fun ω => h.contIntegral T H q₂ ω - h.contIntegral T H q₁ ω := by
  have hR := measurableSet_rect_pred 𝓖 (q₂ := q₂) hC
  set R := Ioc (q₁ : ℝ) q₂ ×ˢ C
  set F := h.stochIntegral T (predInd 𝓖 R hR H)
  have hCm : MeasurableSet C := 𝓖.le _ _ hC
  refine ae_eq_of_eLpNorm_le_geom 5 fun k => ?_
  set Fk := h.stochIntegral T (predInd 𝓖 R hR (h.integrandLin T (h.approx T H k)))
  have hFk : (Fk : Ω → ℝ) =ᵐ[Q]
      C.indicator fun ω => h.approxProc T H k q₂ ω - h.approxProc T H k q₁ ω := by
    simp only [Fk, R]
    rw [h.predInd_integrandLin T hq hqT hC]
    refine (h.stochIntegral_integrandLin_ae T _).trans ?_
    rw [elemProc_restrict]
    rfl
  set a : Ω → ℝ := fun ω => h.approxProc T H k q₂ ω - h.contIntegral T H q₂ ω
  set b : Ω → ℝ := fun ω => h.approxProc T H k q₁ ω - h.contIntegral T H q₁ ω
  have hsplit : (fun ω => F ω - C.indicator (fun ω => h.contIntegral T H q₂ ω -
      h.contIntegral T H q₁ ω) ω) =ᵐ[Q]
      (fun ω => F ω - Fk ω) + (fun ω => C.indicator a ω - C.indicator b ω) := by
    filter_upwards [hFk] with ω hω
    simp only [Pi.add_apply, hω]
    by_cases hωC : ω ∈ C
    · simp only [indicator_of_mem hωC, a, b]; ring
    · simp only [indicator_of_notMem hωC]; ring
  have e1 : eLpNorm (fun ω => F ω - Fk ω) 2 Q ≤ ENNReal.ofReal (1 * (1 / 4 : ℝ) ^ k) := by
    have hae : (fun ω => F ω - Fk ω) =ᵐ[Q] ⇑(F - Fk) := (Lp.coeFn_sub F Fk).symm
    rw [eLpNorm_congr_ae hae, eLpNorm_Lp_eq, one_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [F, Fk]
    rw [← map_sub, LinearIsometry.norm_map, ← map_sub]
    refine (norm_predInd_le 𝓖 R hR _).trans ?_
    rw [norm_sub_rev]
    exact (h.approx_spec T H k).le
  have ea : eLpNorm (C.indicator a) 2 Q ≤ ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) :=
    (eLpNorm_indicator_le _ hCm.nullMeasurableSet).trans
      (h.eLpNorm_approxProc_sub_contIntegral_le T H k q₂)
  have eb : eLpNorm (C.indicator b) 2 Q ≤ ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) :=
    (eLpNorm_indicator_le _ hCm.nullMeasurableSet).trans
      (h.eLpNorm_approxProc_sub_contIntegral_le T H k q₁)
  rw [eLpNorm_congr_ae hsplit]
  calc _ ≤ eLpNorm (fun ω => F ω - Fk ω) 2 Q +
        eLpNorm (fun ω => C.indicator a ω - C.indicator b ω) 2 Q :=
        eLpNorm_add_le one_le_two
    _ ≤ ENNReal.ofReal (1 * (1 / 4 : ℝ) ^ k) +
        (ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) + ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k)) :=
        add_le_add e1 ((eLpNorm_sub_le one_le_two).trans (add_le_add ea eb))
    _ = ENNReal.ofReal (5 * (1 / 4 : ℝ) ^ k) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **Rectangle multiplier identity**: `∫_0^T 1_{(q₁,q₂] × C} H dN = 1_C (Z_{q₂} - Z_{q₁})`
a.s., for all `q₁ ≤ q₂` and `C ∈ 𝓖_{q₁}`. -/
theorem stochIntegral_predInd_rect {q₁ q₂ : ℝ≥0} (hq : q₁ ≤ q₂) {C : Set Ω}
    (hC : MeasurableSet[𝓖 q₁] C) :
    (h.stochIntegral T (predInd 𝓖 _ (measurableSet_rect_pred 𝓖 (q₂ := q₂) hC) H) : Ω → ℝ)
      =ᵐ[Q] C.indicator fun ω => h.contIntegral T H q₂ ω - h.contIntegral T H q₁ ω := by
  rcases le_total q₂ T with hqT | hTq
  · exact h.stochIntegral_predInd_rect_of_le T H hq hqT hC
  rcases le_total q₁ T with h1T | hT1
  · have hset : (Ioc (q₁ : ℝ) q₂ ×ˢ C : Set (ℝ × Ω)) =ᵐ[bracketMeasure Q α T]
        (Ioc (q₁ : ℝ) T ×ˢ C : Set (ℝ × Ω)) := by
      filter_upwards [bracketMeasure_ae_mem Q α T] with p hp
      have hpT : p.1 ≤ T := hp.2
      have hq2 : (T : ℝ) ≤ q₂ := by exact_mod_cast hTq
      simp only [eq_iff_iff, mem_prod, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨⟨h1, hpT⟩, h3⟩
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨⟨h1, hpT.trans hq2⟩, h3⟩
    rw [predInd_congr 𝓖 _ (measurableSet_rect_pred 𝓖 (q₂ := T) hC) hset]
    refine (h.stochIntegral_predInd_rect_of_le T H h1T le_rfl hC).trans ?_
    rw [h.contIntegral_of_le T H hTq]
  · have hnull : bracketMeasure Q α T (Ioc (q₁ : ℝ) q₂ ×ˢ C) = 0 := by
      refine measure_mono_null (fun p hp => ?_) (ae_iff.1 (bracketMeasure_ae_mem Q α T))
      have h1 : (T : ℝ) < p.1 := lt_of_le_of_lt (by exact_mod_cast hT1) hp.1.1
      exact fun hm => absurd hm.2 (not_le.2 h1)
    rw [predInd_null 𝓖 _ hnull, map_zero]
    refine (Lp.coeFn_zero _ _ _).trans (Eventually.of_forall fun ω => ?_)
    rw [h.contIntegral_of_le T H hTq, h.contIntegral_of_le T H hT1]
    simp

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
