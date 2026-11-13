module

public import BlockBand.DeterminantScore.BrascampLiebExhaustion

/-!
# The Brascamp–Lieb inequality on an open convex set

`brascampLieb` proves `BrascampLiebStatement` from `BlockBand.External.Prekopa.SourceContract`
(Prékopa 1973, Theorem 6), taken as the explicit hypothesis `hP`; nothing else is assumed.

## Proof (via Prékopa's theorem rather than the `L²`/Bochner method)

1. `variance_le_of_convexOn_tilt`: if `𝒰 - t f + t²Φ/2` is jointly convex on `(-t₀,t₀) × P`, then
   Prékopa gives `Z(t) Z(-t) ≤ Z(0)²` for `Z(t) = ∫_P e^{-𝒰 + t f - t²Φ/2}`, and a third-order
   Taylor bound gives `Var f ≤ E Φ` (bounded `f, Φ`).
2. `variance_le_piece`: on an open convex `P` with compact closure inside `D`, the choice
   `Φ ≈ q + δ`, `q = sup_b (2 ∇f·b - ∇²𝒰[b,b]) ≤ Σ_j (∂_j f)²/w_j`, smoothed by
   Stone–Weierstrass, makes the tilt jointly convex; hence `Var f ≤ E q` for the normalized law
   on `P`.
3. Exhaust `D` by such `P_n`; the centred second moments on `P_n` are bounded by the energy, the
   centres stay bounded, and Fatou gives `E(f - c)² ≤ energy` on `D` for a limit centre `c`; hence
   `evariance f ≤ energy`. In particular a measurable `f`, smooth on `D`, of finite weighted
   energy is in `L²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

set_option maxHeartbeats 1000000 in
/-- **`BrascampLiebStatement`**, from the Prékopa hypothesis. -/
theorem brascampLieb (hP : BlockBand.External.Prekopa.SourceContract) :
    BrascampLiebStatement := by
  intro m D hDo hDc 𝒰 w h𝒰 hw hH hprob f hfm hfC hfin
  classical
  set μ := gibbsOn D 𝒰 with hμ
  -- a measurable version of `𝒰`
  set 𝒰' : (Fin m → ℝ) → ℝ := D.piecewise 𝒰 0 with h𝒰'def
  have h𝒰'm : Measurable 𝒰' := ContinuousOn.measurable_piecewise h𝒰.continuousOn
    continuousOn_const hDo.measurableSet
  have h𝒰'eq : ∀ x ∈ D, 𝒰' x = 𝒰 x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have hμ' : gibbsOn D 𝒰' = μ := by
    rw [hμ, gibbsOn, gibbsOn]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hDo.measurableSet] with x hx
    rw [h𝒰'eq x hx]
  have h𝒰'C : ContDiffOn ℝ 2 𝒰' D := h𝒰.congr h𝒰'eq
  have hH' : ∀ x ∈ D, ∀ a, ∑ j, w x j * a j ^ 2 ≤ fderiv ℝ (fderiv ℝ 𝒰') x a a := by
    intro x hx a
    have hev : 𝒰' =ᶠ[𝓝 x] 𝒰 := eventuallyEq_of_mem (hDo.mem_nhds hx) h𝒰'eq
    rw [hev.fderiv.fderiv_eq]
    have := hH x hx a
    rwa [iteratedFDeriv_two_apply] at this
  have hf2 : ContDiffOn ℝ 2 f D := hfC.of_le (WithTop.coe_le_coe.2 le_top)
  -- the exhaustion
  set P : ℕ → Set (Fin m → ℝ) := fun n => interior (layer D n) with hPdef
  have hPm : ∀ n, MeasurableSet (P n) := fun n => isOpen_interior.measurableSet
  have hPmono : Monotone P := fun n n' h => interior_mono (layer_mono D h)
  have hPD : ∀ n, P n ⊆ D := fun n => interior_subset.trans (layer_subset D n)
  have hae : ∀ᵐ x ∂μ, x ∈ D := ae_mem_gibbsOn hDo.measurableSet 𝒰
  have hcov : ∀ᵐ x ∂μ, ∃ n, x ∈ P n := hae.mono fun x hx => exists_mem_interior_layer hDo hx
  obtain ⟨n₀, h0⟩ : ∃ n₀, μ (P n₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 : μ (⋃ n, P n) = 0 := measure_iUnion_null hall
    have h2 : μ (⋃ n, P n)ᶜ = 0 := by
      rw [← ae_iff.1 hcov]
      congr 1
      ext x
      simp
    have := measure_univ_le_add_compl (μ := μ) (⋃ n, P n)
    rw [h1, h2, add_zero, measure_univ] at this
    exact absurd this (by norm_num)
  obtain ⟨B₀, hB₀⟩ := (isCompact_layer D n₀).exists_bound_of_continuousOn
    (hf2.continuousOn.mono (layer_subset D n₀))
  set V := ∫⁻ x, ENNReal.ofReal (energyDensity f w x) ∂μ with hVdef
  have hV : V ≠ ⊤ := hfin
  -- centred second moments on each piece
  have hc : ∀ n, ∃ c : ℝ, ∫⁻ x in P n, ENNReal.ofReal ((f x - c) ^ 2) ∂μ ≤ V := by
    intro n
    by_cases hn : μ (P n) = 0
    · exact ⟨0, by rw [Measure.restrict_eq_zero.2 hn, lintegral_zero_measure]; exact bot_le⟩
    have hfinμ : μ (P n) ≠ ⊤ := measure_ne_top _ _
    set t := (μ (P n)).toReal with htdef
    have ht : 0 < t := ENNReal.toReal_pos hn hfinμ
    have hμPt : μ (P n) = ENNReal.ofReal t := (ENNReal.ofReal_toReal hfinμ).symm
    set V𝒰 : (Fin m → ℝ) → ℝ := fun x => 𝒰' x + Real.log t with hV𝒰
    have hV𝒰m : Measurable V𝒰 := h𝒰'm.add_const _
    set ν := gibbsOn (P n) V𝒰 with hν
    have hνint : ∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
        ∫⁻ x in P n, g x ∂μ = ENNReal.ofReal t * ∫⁻ x, g x ∂ν := by
      intro g hg
      have hgP : Measurable ((P n).indicator g) := hg.indicator (hPm n)
      have hd : Measurable fun x => ENNReal.ofReal (Real.exp (-𝒰' x)) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h𝒰'm.neg)
      rw [← lintegral_indicator (hPm n), ← hμ', lintegral_gibbsOn hDo.measurableSet h𝒰'm hgP,
        hν, lintegral_gibbsOn (hPm n) hV𝒰m hg]
      have hpt : ∀ x, D.indicator (fun x => ENNReal.ofReal (Real.exp (-𝒰' x)) *
          (P n).indicator g x) x = ENNReal.ofReal t * (P n).indicator
          (fun x => ENNReal.ofReal (Real.exp (-V𝒰 x)) * g x) x := by
        intro x
        by_cases hx : x ∈ P n
        · rw [Set.indicator_of_mem (hPD n hx), Set.indicator_of_mem hx,
            Set.indicator_of_mem hx, ← mul_assoc, ← ENNReal.ofReal_mul ht.le]
          congr 2
          rw [hV𝒰, neg_add, Real.exp_add, Real.exp_neg (Real.log t), Real.exp_log ht]
          field_simp
        · simp [Set.indicator, hx]
      rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    -- `ν` is a probability measure
    have hνprob : IsProbabilityMeasure ν := by
      constructor
      have h1 := hνint (fun _ => 1) measurable_const
      rw [setLIntegral_one, lintegral_one, hμPt] at h1
      have h2 : ENNReal.ofReal t⁻¹ * ENNReal.ofReal t = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 ht.le), inv_mul_cancel₀ ht.ne', ENNReal.ofReal_one]
      calc ν Set.univ = ENNReal.ofReal t⁻¹ * (ENNReal.ofReal t * ν Set.univ) := by
            rw [← mul_assoc, h2, one_mul]
        _ = 1 := by rw [← h1, h2]
    -- Brascamp–Lieb on the piece
    have hV𝒰C : ContDiffOn ℝ 2 V𝒰 D := h𝒰'C.add contDiffOn_const
    have hHV : ∀ x ∈ D, ∀ a, ∑ j, w x j * a j ^ 2 ≤ fderiv ℝ (fderiv ℝ V𝒰) x a a := by
      intro x hx a
      have e : fderiv ℝ V𝒰 = fderiv ℝ 𝒰' := by
        funext y; exact fderiv_add_const (Real.log t)
      rw [e]
      exact hH' x hx a
    obtain ⟨q, hqm, hqE, hvar⟩ := variance_le_piece hP hDo (isCompact_layer D n)
      (layer_subset D n) isOpen_interior (convex_layer hDc n).interior interior_subset hV𝒰C hf2
      hfm hw hHV hνprob
    -- `f` is bounded on the piece, hence in `L²(ν)`
    obtain ⟨B, hB⟩ := (isCompact_layer D n).exists_bound_of_continuousOn
      (hf2.continuousOn.mono (layer_subset D n))
    have haeν : ∀ᵐ x ∂ν, x ∈ P n := ae_mem_gibbsOn (hPm n) V𝒰
    have hL2 : MemLp f 2 ν := MemLp.of_bound hfm.aestronglyMeasurable B
      (haeν.mono fun x hx => hB x (interior_subset hx))
    refine ⟨∫ x, f x ∂ν, ?_⟩
    have hgm : Measurable fun x => ENNReal.ofReal ((f x - ∫ x, f x ∂ν) ^ 2) :=
      ((hfm.sub_const _).pow_const 2).ennreal_ofReal
    calc ∫⁻ x in P n, ENNReal.ofReal ((f x - ∫ x, f x ∂ν) ^ 2) ∂μ
        = ENNReal.ofReal t * evariance f ν := by
          rw [hνint _ hgm, evariance_eq_lintegral_ofReal]
      _ = ENNReal.ofReal t * ENNReal.ofReal (variance f ν) := by rw [hL2.ofReal_variance_eq]
      _ ≤ ENNReal.ofReal t * ∫⁻ x, ENNReal.ofReal (q x) ∂ν := by gcongr
      _ = ∫⁻ x in P n, ENNReal.ofReal (q x) ∂μ := (hνint _ hqm.ennreal_ofReal).symm
      _ ≤ ∫⁻ x in P n, ENNReal.ofReal (energyDensity f w x) ∂μ := by
          refine setLIntegral_mono' (hPm n) fun x hx => ?_
          exact ENNReal.ofReal_le_ofReal (hqE x (hPD n hx))
      _ ≤ V := setLIntegral_le_lintegral _ _
  obtain ⟨c, hcV⟩ := exists_center_lintegral_le hfm hPm hPmono hcov hV h0
    (fun x hx => hB₀ x (interior_subset hx)) hc
  exact (evariance_le_lintegral_sq hfm c).trans hcV

end BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb
