module

public import BlockBand.DeterminantScore.GelfandTsetlinLaw

/-!
# Continuity of the Gelfand–Tsetlin marginal

For every `k`, `λ ↦ gtMarginal k λ = ∫ 1_{GT}(λ, y) e^{Σ_r k_r d_r} dy` is finite and continuous on
`ℝ^m` (`continuous_gtMarginal`, `gtMarginal_ne_top`). Induction on `m` through the recursion
`gtMarginal_succ`: near `λ₀`, the integrand `1_{[λ_i, λ_{i+1}]}(μ) e^{k_n(Σλ - Σμ)} Φ(μ)` is
dominated by a constant on a compact box (the previous marginal `Φ` is continuous and finite,
hence bounded on compacts) and converges pointwise off the Lebesgue-null hyperplanes
`μ_i ∈ {λ₀_i, λ₀_{i+1}}` (`ae_ne_boxBoundary`); dominated convergence concludes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.GelfandTsetlin

open MeasureTheory Filter Topology Metric
open BlockBand.DeterminantScore.EigenDensity
open BlockBand.DeterminantScore.WeylIntegration (interlaceBox)
open scoped ENNReal

variable {n : ℕ}

theorem continuous_topWeight (c : ℝ) :
    Continuous fun q : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => topWeight c q.1 q.2 := by
  unfold topWeight
  refine ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
  fun_prop

theorem isOpen_setOf_mem_interlaceBox (μ : Fin n → ℝ) :
    IsOpen {lam : Fin (n + 1) → ℝ | μ ∈ interlaceBox lam} := by
  have : {lam : Fin (n + 1) → ℝ | μ ∈ interlaceBox lam} =
      ⋂ i : Fin n, ({lam | lam i.castSucc < μ i} ∩ {lam | μ i < lam i.succ}) := by
    ext lam
    simp [interlaceBox, Set.mem_pi]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt (continuous_apply _) continuous_const).inter
      (isOpen_lt continuous_const (continuous_apply _))

theorem isClosed_setOf_mem_closedBox (μ : Fin n → ℝ) :
    IsClosed {lam : Fin (n + 1) → ℝ | μ ∈ closedBox lam} := by
  have : {lam : Fin (n + 1) → ℝ | μ ∈ closedBox lam} =
      ⋂ i : Fin n, ({lam | lam i.castSucc ≤ μ i} ∩ {lam | μ i ≤ lam i.succ}) := by
    ext lam
    simp only [closedBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, Set.mem_ofPred_eq,
      Set.mem_iInter, Set.mem_inter_iff]
  rw [this]
  exact isClosed_iInter fun i =>
    (isClosed_le (continuous_apply _) continuous_const).inter
      (isClosed_le continuous_const (continuous_apply _))

/-- Near `λ₀`, the closed interlacing boxes stay in a fixed compact cube. -/
theorem closedBox_subset_cube {lam lam0 : Fin (n + 1) → ℝ} (h : lam ∈ ball lam0 1) :
    closedBox lam ⊆ Set.univ.pi fun _ : Fin n => Set.Icc (-(‖lam0‖ + 1)) (‖lam0‖ + 1) := by
  have hn : ‖lam‖ < ‖lam0‖ + 1 := by
    have h1 := norm_sub_norm_le lam lam0
    rw [mem_ball, dist_eq_norm] at h
    linarith
  have hj : ∀ j, |lam j| ≤ ‖lam0‖ + 1 := fun j => by
    have := norm_le_pi_norm lam j
    rw [Real.norm_eq_abs] at this
    linarith
  intro μ hμ i _
  obtain ⟨h1, h2⟩ := hμ i (Set.mem_univ _)
  constructor
  · linarith [neg_abs_le (lam i.castSucc), hj i.castSucc]
  · linarith [le_abs_self (lam i.succ), hj i.succ]

/-- **The inductive step**: if the marginal of size `n` is continuous and finite, the integral in
`gtMarginal_succ` is continuous at every `λ₀` and finite there. -/
theorem tendsto_succ_integral (c : ℝ) {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦm : Measurable Φ)
    (hΦc : Continuous Φ) (hΦf : ∀ μ, Φ μ ≠ ⊤) (lam0 : Fin (n + 1) → ℝ) :
    Tendsto (fun lam => ∫⁻ μ, (closedBox lam).indicator (topWeight c lam) μ * Φ μ) (𝓝 lam0)
        (𝓝 (∫⁻ μ, (closedBox lam0).indicator (topWeight c lam0) μ * Φ μ)) ∧
      ∫⁻ μ, (closedBox lam0).indicator (topWeight c lam0) μ * Φ μ ≠ ⊤ := by
  set R := ‖lam0‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  set Q : Set (Fin n → ℝ) := Set.univ.pi fun _ : Fin n => Set.Icc (-R) R with hQ
  have hQc : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hQne : Q.Nonempty := ⟨0, fun i _ => ⟨by simp; linarith, by simp; linarith⟩⟩
  have hQm : MeasurableSet Q := (isClosed_set_pi fun _ _ => isClosed_Icc).measurableSet
  -- bounds
  obtain ⟨x0, hx0, hmax0⟩ := hQc.exists_isMaxOn hQne hΦc.continuousOn
  set B := Φ x0
  set K : Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) := closedBall lam0 1 ×ˢ Q
  have hKc : IsCompact K := (isCompact_closedBall lam0 1).prod hQc
  have hKne : K.Nonempty := ⟨(lam0, x0), mem_closedBall_self zero_le_one, hx0⟩
  obtain ⟨q1, -, hmax1⟩ := hKc.exists_isMaxOn hKne (continuous_topWeight (n := n) c).continuousOn
  set B2 := topWeight c q1.1 q1.2
  set bound : (Fin n → ℝ) → ℝ≥0∞ := Q.indicator fun _ => B2 * B
  have hbfin : ∫⁻ μ, bound μ ≠ ⊤ := by
    rw [lintegral_indicator_const hQm]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hΦf x0))
      hQc.measure_lt_top.ne
  have hbd : ∀ lam ∈ ball lam0 1, ∀ μ,
      (closedBox lam).indicator (topWeight c lam) μ * Φ μ ≤ bound μ := by
    intro lam hlam μ
    by_cases hμ : μ ∈ closedBox lam
    · have hμQ : μ ∈ Q := closedBox_subset_cube hlam hμ
      rw [Set.indicator_of_mem hμ, show bound μ = B2 * B from Set.indicator_of_mem hμQ _]
      have h1 : topWeight c lam μ ≤ B2 :=
        isMaxOn_iff.1 hmax1 (lam, μ) ⟨ball_subset_closedBall hlam, hμQ⟩
      have h2 : Φ μ ≤ B := isMaxOn_iff.1 hmax0 μ hμQ
      exact mul_le_mul' h1 h2
    · rw [Set.indicator_of_notMem hμ, zero_mul]
      exact bot_le
  refine ⟨?_, ?_⟩
  · refine tendsto_lintegral_filter_of_dominated_convergence bound ?_ ?_ hbfin ?_
    · exact Eventually.of_forall fun lam =>
        ((measurable_topWeight_right c lam).indicator
          (isClosed_closedBox lam).measurableSet).mul hΦm
    · exact Filter.eventually_of_mem (ball_mem_nhds lam0 one_pos) fun lam hlam =>
        ae_of_all _ (hbd lam hlam)
    · refine (ae_ne_boxBoundary lam0).mono fun μ hμ => ?_
      by_cases h0 : μ ∈ closedBox lam0
      · have hev : ∀ᶠ lam in 𝓝 lam0, μ ∈ closedBox lam := by
          filter_upwards [(isOpen_setOf_mem_interlaceBox μ).mem_nhds
            ((mem_closedBox_iff_of_ne hμ).1 h0)] with lam hlam
          exact Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self) hlam
        rw [Set.indicator_of_mem h0]
        have htw : Tendsto (fun lam => topWeight c lam μ) (𝓝 lam0) (𝓝 (topWeight c lam0 μ)) :=
          ((continuous_topWeight c).comp (continuous_id.prodMk continuous_const)).tendsto lam0
        refine (ENNReal.Tendsto.mul_const htw (Or.inr (hΦf μ))).congr' ?_
        exact hev.mono fun lam hlam => by dsimp only; rw [Set.indicator_of_mem hlam]
      · have hev : ∀ᶠ lam in 𝓝 lam0, μ ∉ closedBox lam :=
          (isClosed_setOf_mem_closedBox μ).isOpen_compl.mem_nhds h0
        rw [Set.indicator_of_notMem h0, zero_mul]
        refine tendsto_const_nhds.congr' ?_
        exact hev.mono fun lam hlam => by dsimp only; rw [Set.indicator_of_notMem hlam, zero_mul]
  · refine ne_top_of_le_ne_top hbfin (lintegral_mono fun μ => ?_)
    exact hbd lam0 (mem_ball_self one_pos) μ

/-- **Finiteness and continuity of the Gelfand–Tsetlin marginal.** -/
theorem continuous_gtMarginal_and_ne_top (m : ℕ) (k : Fin m → ℝ) :
    Continuous (gtMarginal k) ∧ ∀ lam, gtMarginal k lam ≠ ⊤ := by
  induction m with
  | zero =>
    have h : gtMarginal k = fun _ => 1 := funext (gtMarginal_zero k)
    rw [h]
    exact ⟨continuous_const, fun _ => ENNReal.one_ne_top⟩
  | succ n ih =>
    obtain ⟨hc, hf⟩ := ih (fun r => k r.castSucc)
    have hfun : gtMarginal k = fun lam => ∫⁻ μ, (closedBox lam).indicator
        (topWeight (k (Fin.last n)) lam) μ * gtMarginal (fun r => k r.castSucc) μ :=
      funext (gtMarginal_succ k)
    have hstep := tendsto_succ_integral (k (Fin.last n)) (measurable_gtMarginal _) hc hf
    rw [hfun]
    exact ⟨continuous_iff_continuousAt.2 fun lam0 => (hstep lam0).1, fun lam0 => (hstep lam0).2⟩

theorem continuous_gtMarginal {m : ℕ} (k : Fin m → ℝ) : Continuous (gtMarginal k) :=
  (continuous_gtMarginal_and_ne_top m k).1

theorem gtMarginal_ne_top {m : ℕ} (k : Fin m → ℝ) (lam : Fin m → ℝ) : gtMarginal k lam ≠ ⊤ :=
  (continuous_gtMarginal_and_ne_top m k).2 lam

end BlockBand.DeterminantScore.GelfandTsetlin
