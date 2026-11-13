module

public import BlockBand.SourceProcess.ComplexUnique.Bridge

/-!
# The restarted real martingale problem: the clauses and the main theorem

The clauses of the restarted process (`rs_cC`, `rs_cB`, `rs_cB'`), with bounded
`𝓖_a`-measurable weights (`exists_factor`), give `isMPSolutionOn_rsY`: the restarted real process
solves the real martingale problem in `{t < h}` for the shifted filtration.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.BornRestart BlockBand.SourceProcess.Stochastic.GramUniqueness
open scoped NNReal

variable {κ : Type*} [Fintype κ] {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {β : (κ → ℂ) → κ → ℂ} {Γ Γ' : (κ → ℂ) → κ → κ → ℂ} {c : ℝ≥0 → κ → ℂ}
  {X : ℝ≥0 → Ω → κ → ℂ} {σ : ℝ → Ω → WithTop ℝ≥0}

omit [MeasurableSpace Ω] in
theorem ind_mul_ind (E : Set Ω) (ω : Ω) :
    E.indicator (fun _ => (1 : ℂ)) ω * E.indicator (fun _ => (1 : ℂ)) ω =
      E.indicator (fun _ => (1 : ℂ)) ω := by
  by_cases h : ω ∈ E <;> simp [h]

omit [MeasurableSpace Ω] in
theorem star_ind (E : Set Ω) (ω : Ω) :
    star (E.indicator (fun _ => (1 : ℂ)) ω) = E.indicator (fun _ => (1 : ℂ)) ω := by
  by_cases h : ω ∈ E <;> simp [h]

/-- A bounded `𝓖_a`-measurable version of `1_{evK} lComp_p(a)`. -/
theorem exists_factor (hX : IsCLocSol Q 𝓖 β Γ Γ' c X σ) (hβ : Continuous β) (hc : Measurable c)
    {C : ℝ} (hC : ∀ t, ‖c t‖ ≤ C) (a : ℝ≥0) (k : ℕ) (p : κ) :
    ∃ ζ : Ω → ℂ, StronglyMeasurable[𝓖 a] ζ ∧ (∃ B, ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ B) ∧
      ζ =ᵐ[Q] fun ω => (evK X a k).indicator (fun _ => (1 : ℂ)) ω * lComp β c X p a ω := by
  have hXm : ∀ t, Measurable[𝓖 t] (X t) := fun t => (hX.adapted t).measurable
  obtain ⟨L, hL⟩ := hX.loc k
  obtain ⟨N, hN, hNX⟩ := hX.drift L p
  obtain ⟨M, hM, hMX⟩ := exists_martingale_restrict_complex hN hNX
    (hX.continuous.mono fun ω hx => continuous_lComp hβ hx hc hC p) (isStoppingTime_hitK hXm k) hL
    (Eventually.of_forall fun _ => rfl)
  obtain ⟨B, hB⟩ := exists_bound_lComp (X := X) hβ hC a k
  have hEm := measurableSet_evK hXm a k
  refine ⟨fun ω => (evK X a k).indicator (fun _ => (1 : ℂ)) ω * M a ω,
    (stronglyMeasurable_const.indicator hEm).mul (hM.1 a), ⟨max B 0, ?_⟩, ?_⟩
  · filter_upwards [hMX a, hX.continuous] with ω h hx
    by_cases hω : ω ∈ evK X a k
    · rw [Set.indicator_of_mem hω, one_mul, h, stoppedProcess_eq_stopTime, stopTime_of_lt hω]
      exact (hB ω hx hω p).trans (le_max_left _ _)
    · simp [hω]
  · filter_upwards [hMX a] with ω h
    by_cases hω : ω ∈ evK X a k
    · simp only [Set.indicator_of_mem hω, one_mul]
      rw [h, stoppedProcess_eq_stopTime, stopTime_of_lt hω]
    · simp [hω]

theorem exists_level (C : ℝ) {W : Set (Fin (rDim κ) → ℝ)} (hW : IsCompact (closure W)) :
    ∃ Rz : ℝ, ∃ K0 : ℕ, (∀ y ∈ W, ‖zOf y‖ ≤ Rz) ∧ ∀ k : ℕ, Rz + C < ((k + K0 : ℕ) : ℝ) := by
  obtain ⟨Rz, -, hRz⟩ := exists_bound_closure hW (continuous_zOf (κ := κ))
  obtain ⟨K0, hK0⟩ := exists_nat_gt (Rz + C)
  exact ⟨Rz, K0, fun y hy => hRz y (subset_closure hy), fun k => by push_cast; linarith [k.cast_nonneg (α := ℝ)]⟩

omit [IsProbabilityMeasure Q] in
theorem eventually_evK_add (hX : IsCLocSol Q 𝓖 β Γ Γ' c X σ) (a : ℝ≥0) (K0 : ℕ) :
    ∀ᵐ ω ∂Q, ∀ᶠ k : ℕ in atTop, ω ∈ evK X a (k + K0) := by
  filter_upwards [hX.continuous] with ω hx
  exact (tendsto_add_atTop_nat K0).eventually (eventually_mem_evK hx a)

variable {C : ℝ} {a h : ℝ≥0} {W : Set (Fin (rDim κ) → ℝ)}

theorem rs_cC (hX : IsCLocSol Q 𝓖 β Γ Γ' c X σ) (hβ : Continuous β) (hc : Measurable c)
    (hC : ∀ t, ‖c t‖ ≤ C) (hseg : ∀ t, a ≤ t → t < a + h → c t = c a)
    (hW : IsInteriorDomain W {y | tOf y < h}) (p : κ) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (shiftFil 𝓖 a) Q ∧
      ∀ u, N u =ᵐ[Q] stoppedProcess (cC β (rsY X c a h) p) (exitTimeFrom W (rsY X c a h)) u := by
  obtain ⟨Rz, K0, hRz, hk⟩ := exists_level C hW.2.1
  refine exists_martingale_of_ind (E := fun k => evK X a (k + K0)) (fun k => ?_)
    (eventually_evK_add hX a K0) (fun u => ?_)
  · obtain ⟨M, hM, hMX⟩ := restart_clause hX (fun L => hX.drift L p)
      (hX.continuous.mono fun ω hx => continuous_lComp hβ hx hc hC p) hC a h hW hRz (hk k)
    refine ⟨M, hM, fun u => ?_⟩
    filter_upwards [hMX u, hX.continuous] with ω h1 hx
    rw [h1, stoppedProcess_eq_stopTime, cC_rsY hβ hx hc hC hseg (stop_le_h hx hW u)]
  · obtain ⟨B, -, hB⟩ := exists_bound_cC (Y := rsY X c a h) hW.1 hW.2.1 hβ u
    exact ⟨B, by filter_upwards [hX.continuous] with ω hx using hB ω (continuous_rsY hx a h) p⟩

theorem rs_cB (hX : IsCLocSol Q 𝓖 β Γ Γ' c X σ) (hβ : Continuous β) (hΓ : Continuous Γ)
    (hc : Measurable c) (hC : ∀ t, ‖c t‖ ≤ C) (hseg : ∀ t, a ≤ t → t < a + h → c t = c a)
    (hW : IsInteriorDomain W {y | tOf y < h}) (p q : κ) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (shiftFil 𝓖 a) Q ∧
      ∀ u, N u =ᵐ[Q] stoppedProcess (cB β Γ (rsY X c a h) p q) (exitTimeFrom W (rsY X c a h)) u := by
  obtain ⟨Rz, K0, hRz, hk⟩ := exists_level C hW.2.1
  refine exists_martingale_of_ind (E := fun k => evK X a (k + K0)) (fun k => ?_)
    (eventually_evK_add hX a K0) (fun u => ?_)
  · have hcp := hX.continuous.mono fun ω hx => continuous_lComp hβ hx hc hC p
    have hcq := hX.continuous.mono fun ω hx => continuous_lComp hβ hx hc hC q
    obtain ⟨M1, hM1, hM1X⟩ := restart_clause hX (fun L => hX.bracket L p q)
      (hX.continuous.mono fun ω hx => continuous_lBr hβ hΓ hx hc hC p q) hC a h hW hRz (hk k)
    obtain ⟨M2, hM2, hM2X⟩ := restart_clause hX (fun L => hX.drift L q) hcq hC a h hW hRz (hk k)
    obtain ⟨M3, hM3, hM3X⟩ := restart_clause hX (fun L => hX.drift L p) hcp hC a h hW hRz (hk k)
    obtain ⟨ζp, hζp, ⟨Bp, hBp⟩, hζpX⟩ := exists_factor hX hβ hc hC a (k + K0) p
    obtain ⟨ζq, hζq, ⟨Bq, hBq⟩, hζqX⟩ := exists_factor hX hβ hc hC a (k + K0) q
    rw [← shiftFil_zero] at hζp hζq
    refine ⟨fun u ω => M1 u ω - ζp ω * M2 u ω - ζq ω * M3 u ω,
      (hM1.sub (martingale_const_mul hM2 hζp hBp)).sub (martingale_const_mul hM3 hζq hBq),
      fun u => ?_⟩
    filter_upwards [hM1X u, hM2X u, hM3X u, hζpX, hζqX, hX.continuous] with ω h1 h2 h3 h4 h5 hx
    rw [h1, h2, h3, h4, h5, stoppedProcess_eq_stopTime,
      cB_rsY hβ hΓ hx hc hC hseg (stop_le_h hx hW u)]
    linear_combination (-1 : ℂ) * (lComp β c X p a ω * (lComp β c X q (a + stopTime (exitTimeFrom W
      (rsY X c a h) ω) u) ω - lComp β c X q a ω) + lComp β c X q a ω * (lComp β c X p (a +
      stopTime (exitTimeFrom W (rsY X c a h) ω) u) ω - lComp β c X p a ω)) *
      (ind_mul_ind (evK X a (k + K0)) ω)
  · obtain ⟨B, hB⟩ := exists_bound_cB (Y := rsY X c a h) hW.1 hW.2.1 hβ hΓ u
    exact ⟨B, by filter_upwards [hX.continuous] with ω hx using (hB ω (continuous_rsY hx a h) p q).1⟩

theorem rs_cB' (hX : IsCLocSol Q 𝓖 β Γ Γ' c X σ) (hβ : Continuous β) (hΓ' : Continuous Γ')
    (hc : Measurable c) (hC : ∀ t, ‖c t‖ ≤ C) (hseg : ∀ t, a ≤ t → t < a + h → c t = c a)
    (hW : IsInteriorDomain W {y | tOf y < h}) (p q : κ) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (shiftFil 𝓖 a) Q ∧
      ∀ u, N u =ᵐ[Q] stoppedProcess (cB' β Γ' (rsY X c a h) p q)
        (exitTimeFrom W (rsY X c a h)) u := by
  obtain ⟨Rz, K0, hRz, hk⟩ := exists_level C hW.2.1
  refine exists_martingale_of_ind (E := fun k => evK X a (k + K0)) (fun k => ?_)
    (eventually_evK_add hX a K0) (fun u => ?_)
  · have hcp := hX.continuous.mono fun ω hx => continuous_lComp hβ hx hc hC p
    have hcq := hX.continuous.mono fun ω hx => continuous_lComp hβ hx hc hC q
    obtain ⟨M1, hM1, hM1X⟩ := restart_clause hX (fun L => hX.cbracket L p q)
      (hX.continuous.mono fun ω hx => continuous_lBr' hβ hΓ' hx hc hC p q) hC a h hW hRz (hk k)
    obtain ⟨M2, hM2, hM2X⟩ := restart_clause hX (fun L => hX.drift L q) hcq hC a h hW hRz (hk k)
    obtain ⟨M3, hM3, hM3X⟩ := restart_clause hX (fun L => hX.drift L p) hcp hC a h hW hRz (hk k)
    obtain ⟨ζp, hζp, ⟨Bp, hBp⟩, hζpX⟩ := exists_factor hX hβ hc hC a (k + K0) p
    obtain ⟨ζq, hζq, ⟨Bq, hBq⟩, hζqX⟩ := exists_factor hX hβ hc hC a (k + K0) q
    rw [← shiftFil_zero] at hζp hζq
    have hM2s := martingale_clm hM2 (Complex.conjCLE : ℂ →L[ℝ] ℂ)
    have hζqs : StronglyMeasurable[shiftFil 𝓖 a 0] fun ω => star (ζq ω) :=
      Complex.continuous_conj.comp_stronglyMeasurable hζq
    have hBqs : ∀ᵐ ω ∂Q, ‖star (ζq ω)‖ ≤ Bq := by
      filter_upwards [hBq] with ω h using by rwa [norm_star]
    refine ⟨fun u ω => M1 u ω - ζp ω * (Complex.conjCLE : ℂ →L[ℝ] ℂ) (M2 u ω) -
        star (ζq ω) * M3 u ω,
      (hM1.sub (martingale_const_mul hM2s hζp hBp)).sub (martingale_const_mul hM3 hζqs hBqs),
      fun u => ?_⟩
    filter_upwards [hM1X u, hM2X u, hM3X u, hζpX, hζqX, hX.continuous] with ω h1 h2 h3 h4 h5 hx
    simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
    rw [h1, h2, h3, h4, h5, stoppedProcess_eq_stopTime,
      cB'_rsY hβ hΓ' hx hc hC hseg (stop_le_h hx hW u)]
    have hs := star_ind (evK X a (k + K0)) ω
    have hii := ind_mul_ind (evK X a (k + K0)) ω
    simp only [← Complex.star_def, star_mul', star_sub, hs]
    set v := stopTime (exitTimeFrom W (rsY X c a h) ω) u
    linear_combination (-1 : ℂ) * (lComp β c X p a ω * (star (lComp β c X q (a + v) ω) -
      star (lComp β c X q a ω)) + star (lComp β c X q a ω) * (lComp β c X p (a + v) ω -
      lComp β c X p a ω)) * hii
  · obtain ⟨B, hB⟩ := exists_bound_cB (Y := rsY X c a h) hW.1 hW.2.1 hβ hΓ' u
    exact ⟨B, by filter_upwards [hX.continuous] with ω hx using (hB ω (continuous_rsY hx a h) p q).2⟩

/-- **The restarted real martingale problem.** -/
theorem isMPSolutionOn_rsY (hX : IsCLocSol Q 𝓖 β Γ Γ' c X σ) (hβ : Continuous β)
    (hΓ : Continuous Γ) (hΓ' : Continuous Γ') (hc : Measurable c) (hC : ∀ t, ‖c t‖ ≤ C)
    (hseg : ∀ t, a ≤ t → t < a + h → c t = c a) :
    IsMPSolutionOn Q (shiftFil 𝓖 a) (realDrift β) (realCov Γ Γ') {y | tOf y < h}
      (rsY X c a h) := by
  refine isMPSolutionOn_of_complex hβ hΓ hΓ' (stronglyMeasurable_rsY hX.adapted a h)
    (hX.continuous.mono fun ω hx => continuous_rsY hx a h) (fun W hW => ?_)
    (fun W hW p => rs_cC hX hβ hc hC hseg hW p) (fun W hW p q => rs_cB hX hβ hΓ hc hC hseg hW p q)
    (fun W hW p q => rs_cB' hX hβ hΓ' hc hC hseg hW p q)
  filter_upwards [hX.continuous] with ω hx u
  rw [tOf_rsY, tOf_rsY, min_eq_left (stop_le_h hx hW u), min_eq_left (zero_le : (0 : ℝ≥0) ≤ h),
    NNReal.coe_zero, sub_zero]

end BlockBand.SourceProcess.ComplexUnique
