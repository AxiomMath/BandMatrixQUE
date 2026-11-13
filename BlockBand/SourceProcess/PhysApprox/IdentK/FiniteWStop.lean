module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWPath

/-!
# The finite-`W` tested increment at fixed `W` and `R`

* `norm_genObs_le`: `|M_W(v)| ≤ C + v C_Λ` (the constant is independent of `R`);
* `norm_stop_le` (pathwise): `|1_cap D − Σ_j 1_{A'_j} dStep_j| ≤ 2 C_st 1_bad`, `bad` the event
  that the trace reaches `R` on the cap before `n'`;
* **`enorm_capIncW_le`**: the tested increment `capIncW` is bounded by the time-grid error,
  `2 C_st ‖ψ‖ μ(bad)`, and the summed per-step bounds (`enorm_step_le` off the births,
  `lint_birth_le` at the births).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Finset Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate ENNReal Topology NNReal

variable {W np K : ℕ} {b E s h : ℝ} {τ m : Fin np → ℝ}
  {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}

/-- **The prelimit process is bounded**, `|M_W(v)| ≤ C + v C_Λ`. -/
theorem norm_genObs_le {χ ξ : ℝ → ℝ} {κ : KTest K np} {C CΛ : ℝ}
    (hC : TayB χ ξ κ (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) C)
    (hCΛ : ∀ (J : GSt K np) (z : ZK K np), (∀ e, ‖gramEntry e J‖ ≤ cJump b m) →
      Adm (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) z →
      ‖κ.lam χ ξ b E (J, z)‖ ≤ CΛ) (v : ℝ≥0) (y : ProbedPath W np × ℝ) :
    ‖genObs b E s τ m (b3ObsAll b E s h τ m W Vs) (κ.fn χ ξ) (κ.lam χ ξ b E) v y‖ ≤
      C + v * CΛ := by
  unfold genObs
  refine (norm_sub_le _ _).trans (add_le_add ((hC.2.1 _ (adm_stZKObs b E s h τ m W Vs v y)).1)
    ?_)
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc (0 : ℝ) v)
    (f := fun r => κ.lam χ ξ b E (gramJ b s τ m r.toNNReal,
      stZKObs b E s τ m (b3ObsAll b E s h τ m W Vs) r.toNNReal y)) (C := CΛ) measure_Ioc_lt_top
    fun r _ => hCΛ _ _ (norm_gramEntry_gramJ_le b s τ m _) (adm_stZKObs b E s h τ m W Vs _ y)
  rw [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg v)] at h1
  linarith

/-- The bad event: on the Borel cap event, the trace reaches `R` at some `n_s ≤ i ≤ n'`. -/
def badSet (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W n' : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    Set (ProbedPath W np × ℝ) :=
  {y | y.1.1 ∈ ClosedIdent.physCapEventM b E s h K W ∧ ∃ i, closeLen s W ≤ i ∧ i ≤ n' ∧
    R ≤ ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re}

/-- **Pathwise**: the stopped sum differs from the capped unstopped one only on `bad`. -/
theorem norm_stop_le {χ ξ : ℝ → ℝ} {κ : KTest K np} {C CΛ : ℝ}
    (hC : TayB χ ξ κ (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) C)
    (hCΛ : ∀ (J : GSt K np) (z : ZK K np), (∀ e, ‖gramEntry e J‖ ≤ cJump b m) →
      Adm (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) z →
      ‖κ.lam χ ξ b E (J, z)‖ ≤ CΛ) (R : ℝ) {n n' : ℕ} (y : ProbedPath W np × ℝ) :
    ‖((ClosedIdent.physCapEventM b E s h K W).indicator (fun _ => (1 : ℂ)) y.1.1) *
        ∑ j ∈ Ico n n', dStep b E s h τ m W Vs χ ξ κ j y -
      ∑ j ∈ Ico n n', (b3AliveM b E s h τ m R W j Vs).indicator
        (dStep b E s h τ m W Vs χ ξ κ j) y‖ ≤
      2 * (2 * C + ((n' - n : ℕ) : ℝ) * (CΛ / W)) *
        (badSet b E s h τ m R W n' Vs).indicator (fun _ => (1 : ℝ)) y := by
  classical
  set a : ℕ → ℂ := fun j => κ.fn χ ξ (zeta b E s h τ m W Vs j y)
  set c : ℕ → ℂ := fun j =>
    (W : ℂ)⁻¹ * κ.lam χ ξ b E (b3JumpAt b s τ m W j, zeta b E s h τ m W Vs j y)
  have ha : ∀ j, ‖a j‖ ≤ C := fun j => (hC.2.1 _ (adm_zeta b E s h τ m W Vs j y)).1
  have hc : ∀ j, ‖c j‖ ≤ CΛ / W := fun j => by
    simp only [c, norm_mul]
    calc _ ≤ (1 / W) * CΛ := mul_le_mul (norm_inv_natCast_le W)
          (hCΛ _ _ (norm_gramEntry_b3JumpAt_le b s τ m W j) (adm_zeta b E s h τ m W Vs j y))
          (norm_nonneg _) (by positivity)
      _ = CΛ / W := by ring
  have hsc : ∑ j ∈ Ico n n', ‖c j‖ ≤ ((n' - n : ℕ) : ℝ) * (CΛ / W) := by
    have := Finset.sum_le_card_nsmul (Ico n n') (fun j => ‖c j‖) (CΛ / W) (fun j _ => hc j)
    simpa [nsmul_eq_mul] using this
  have hD : ‖∑ j ∈ Ico n n', dStep b E s h τ m W Vs χ ξ κ j y‖ ≤
      2 * C + ((n' - n : ℕ) : ℝ) * (CΛ / W) := by
    have := norm_sum_stopped_le a c (p := fun _ => True) (fun _ _ => trivial) ha n n'
    simp only [ite_true] at this
    exact this.trans (by linarith)
  have hdec : ∀ j, y ∈ b3AliveM b E s h τ m R W (j + 1) Vs → y ∈ b3AliveM b E s h τ m R W j Vs :=
    fun j hy => ⟨hy.1, fun i h1 h2 => hy.2 i h1 (by omega)⟩
  have hSR : ‖∑ j ∈ Ico n n', (b3AliveM b E s h τ m R W j Vs).indicator
      (dStep b E s h τ m W Vs χ ξ κ j) y‖ ≤ 2 * C + ((n' - n : ℕ) : ℝ) * (CΛ / W) := by
    have := norm_sum_stopped_le a c (p := fun j => y ∈ b3AliveM b E s h τ m R W j Vs) hdec ha n n'
    simp only [Set.indicator_apply]
    exact this.trans (by linarith)
  have hcst : 0 ≤ 2 * C + ((n' - n : ℕ) : ℝ) * (CΛ / W) := (norm_nonneg _).trans hD
  by_cases hcap : y.1.1 ∈ ClosedIdent.physCapEventM b E s h K W
  · by_cases hall : ∀ j ∈ Ico n n', y ∈ b3AliveM b E s h τ m R W j Vs
    · have : ∑ j ∈ Ico n n', (b3AliveM b E s h τ m R W j Vs).indicator
          (dStep b E s h τ m W Vs χ ξ κ j) y = ∑ j ∈ Ico n n', dStep b E s h τ m W Vs χ ξ κ j y :=
        sum_congr rfl fun j hj => Set.indicator_of_mem (hall j hj) _
      rw [this, Set.indicator_of_mem hcap, one_mul, sub_self, norm_zero]
      exact mul_nonneg (by linarith) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · push Not at hall
      obtain ⟨j, hj, hjA⟩ := hall
      have hbad : y ∈ badSet b E s h τ m R W n' Vs := by
        refine ⟨hcap, ?_⟩
        simp only [b3AliveM, b3TraceOK, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and,
          not_forall, not_lt] at hjA
        obtain ⟨i, h1, h2, h3⟩ := hjA hcap
        exact ⟨i, h1, by have := (mem_Ico.1 hj).2; omega, h3⟩
      rw [Set.indicator_of_mem hbad, mul_one, Set.indicator_of_mem hcap, one_mul]
      refine (norm_sub_le _ _).trans ?_
      linarith
  · have h0 : ∀ j, y ∉ b3AliveM b E s h τ m R W j Vs := fun j hy => hcap hy.1
    rw [Set.indicator_of_notMem hcap, zero_mul,
      sum_eq_zero fun j _ => Set.indicator_of_notMem (h0 j) _, sub_zero, norm_zero]
    exact mul_nonneg (by linarith) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem measurable_dStep (hV : Measurable[growthSigma W (closeLen s W)] Vs) {χ ξ : ℝ → ℝ}
    (hχ : ContDiff ℝ 3 χ) (hξ : ContDiff ℝ 3 ξ) (κ : KTest K np) {j : ℕ}
    (hjs : closeLen s W ≤ j) : Measurable (dStep b E s h τ m W Vs χ ξ κ j) := by
  obtain ⟨hχc, hχd, hχdd⟩ := cut_continuity hχ
  obtain ⟨hξc, hξd, hξdd⟩ := cut_continuity hξ
  have hF := κ.continuous_fn hχc hξc
  have hΛ := κ.continuous_lam hχc hχd hχdd hξc hξd hξdd b E
  have h1 := (measurable_comp_zeta (b := b) (E := E) (h := h) (τ := τ) (m := m) (Vs := Vs)
    (by omega : closeLen s W ≤ j + 1) hV hF).mono (gen_sigma_le W (j + 1) np) le_rfl
  have h2 := (measurable_comp_zeta (b := b) (E := E) (h := h) (τ := τ) (m := m) (Vs := Vs)
    hjs hV hF).mono (gen_sigma_le W j np) le_rfl
  have hc3 : Continuous fun z : ZK K np => κ.lam χ ξ b E (b3JumpAt b s τ m W j, z) :=
    hΛ.comp (continuous_const.prodMk continuous_id)
  have h3 := (measurable_comp_zeta (b := b) (E := E) (h := h) (τ := τ) (m := m) (Vs := Vs)
    hjs hV hc3).mono (gen_sigma_le W j np) le_rfl
  exact (h1.sub h2).sub (measurable_const.mul h3)

theorem norm_dStep_le {χ ξ : ℝ → ℝ} {κ : KTest K np} {C CΛ : ℝ}
    (hC : TayB χ ξ κ (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) C)
    (hCΛ : ∀ (J : GSt K np) (z : ZK K np), (∀ e, ‖gramEntry e J‖ ≤ cJump b m) →
      Adm (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) z →
      ‖κ.lam χ ξ b E (J, z)‖ ≤ CΛ) (j : ℕ) (y : ProbedPath W np × ℝ) :
    ‖dStep b E s h τ m W Vs χ ξ κ j y‖ ≤ 2 * C + CΛ / W := by
  unfold dStep
  have h3 : ‖(W : ℂ)⁻¹ * κ.lam χ ξ b E (b3JumpAt b s τ m W j, zeta b E s h τ m W Vs j y)‖ ≤
      CΛ / W := by
    rw [norm_mul]
    have hl := hCΛ _ _ (norm_gramEntry_b3JumpAt_le b s τ m W j) (adm_zeta b E s h τ m W Vs j y)
    calc _ ≤ (1 / W) * CΛ := mul_le_mul (norm_inv_natCast_le W) hl (norm_nonneg _)
          (by positivity)
      _ = CΛ / W := by ring
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) h3)
  linarith [(hC.2.1 _ (adm_zeta b E s h τ m W Vs (j + 1) y)).1,
    (hC.2.1 _ (adm_zeta b E s h τ m W Vs j y)).1]

/-- **The finite-`W` tested increment at fixed `W` and level `R`.** -/
theorem enorm_capIncW_le (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hs : 0 ≤ s)
    (hτ : ∀ j, s < τ j) (hW : 0 < W) (hV : Measurable[growthSigma W (closeLen s W)] Vs)
    {χ ξ : ℝ → ℝ} (hχ : ContDiff ℝ 3 χ) (hξ : ContDiff ℝ 3 ξ) (κ : KTest K np) {C CΛ : ℝ}
    (hC : TayB χ ξ κ (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) C)
    (hCΛ0 : 0 ≤ CΛ)
    (hCΛ : ∀ (J : GSt K np) (z : ZK K np), (∀ e, ‖gramEntry e J‖ ≤ cJump b m) →
      Adm (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) z →
      ‖κ.lam χ ξ b E (J, z)‖ ≤ CΛ) (R : ℝ) {t t' : ℝ≥0} (htt : t ≤ t')
    (hGt : b3JumpAt (K := K) b s τ m W (limLenAll s W t) = gramJ b s τ m t)
    (hKt : b3KJumpAt E s τ m W (limLenAll s W t) = kJ E s τ m t)
    (hGt' : b3JumpAt (K := K) b s τ m W (limLenAll s W t') = gramJ b s τ m t')
    (hKt' : b3KJumpAt E s τ m W (limLenAll s W t') = kJ E s τ m t') {r : ℕ}
    (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0) (hu : ∀ l, u l ≤ t)
    (ψ : BoundedContinuousFunction (Fin r → ℂ) ℝ)
    (hL2 : ∀ j ∈ Ico (limLenAll s W t) (limLenAll s W t'), ¬ IsBirthStep τ W j →
      ∀ c, MemLp ((b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs c)) 2
        (closedLaw b W np)) :
    ‖capIncW b E s h τ m W Vs (κ.fn χ ξ) (κ.lam χ ξ b E) i u ψ t t'‖ₑ ≤
      ENNReal.ofReal (‖ψ‖ * (2 * (CΛ * (2 + 2 * np) / W))) +
      ENNReal.ofReal (‖ψ‖ * (2 * (2 * C + ((limLenAll s W t' - limLenAll s W t : ℕ) : ℝ) *
        (CΛ / W)))) * closedLaw b W np (badSet b E s h τ m R W (limLenAll s W t') Vs) +
      ∑ j ∈ (Ico (limLenAll s W t) (limLenAll s W t')).filter (fun j => ¬ IsBirthStep τ W j),
        (ENNReal.ofReal (‖ψ‖ * C) * (∑ i, pinE1 b E s h τ m R W Vs j i +
          ∑ i, ∑ i', pinE2 b E s h τ m R W Vs j i i') +
        ENNReal.ofReal ‖ψ‖ * (ENNReal.ofReal C * ∫⁻ y, (b3AliveM b E s h τ m R W j Vs).indicator
          (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W Vs j y) ^ 3)) y
            ∂closedLaw b W np)) +
      ∑ j ∈ (Ico (limLenAll s W t) (limLenAll s W t')).filter (fun j => IsBirthStep τ W j),
        ENNReal.ofReal ‖ψ‖ * (ENNReal.ofReal (3 * C) *
          ∑ i : BI K np, genBirthStep b E s h τ m R W j Vs (cOf i) + ENNReal.ofReal (CΛ / W)) := by
  classical
  set μ := closedLaw b W np
  set n := limLenAll s W t
  set n' := limLenAll s W t'
  have hV' : Measurable Vs := hV.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  obtain ⟨hχc, hχd, hχdd⟩ := cut_continuity hχ
  obtain ⟨hξc, hξd, hξdd⟩ := cut_continuity hξ
  have hFc := κ.continuous_fn hχc hξc
  have hΛc := κ.continuous_lam hχc hχd hχdd hξc hξd hξdd b E
  have hC0 : 0 ≤ C := hC.1
  have hn0 : closeLen s W ≤ n := le_limLenAll s W t
  have hnn : n ≤ n' :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (by simpa using htt) (Nat.cast_nonneg W))
  have hun : ∀ l, limLenAll s W (u l) ≤ n := fun l =>
    Nat.floor_mono (mul_le_mul_of_nonneg_left (by simpa using hu l) (Nat.cast_nonneg W))
  -- the test
  set ψW : ProbedPath W np × ℝ → ℂ := fun y =>
    ((ψ (fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y) : ℝ) : ℂ)
  have hψj : ∀ j, n ≤ j → Measurable[b3Sigma W j np] ψW := fun j hj =>
    Complex.measurable_ofReal.comp (measurable_test_past hV i u (fun l => (hun l).trans hj) ψ)
  have hψm : Measurable ψW := (hψj n le_rfl).mono (gen_sigma_le W n np) le_rfl
  have hψb : ∀ y, ‖ψW y‖ ≤ ‖ψ‖ := fun y => by
    simp only [ψW, Complex.norm_real]; exact ψ.norm_coe_le_norm _
  have hψ0 : 0 ≤ ‖ψ‖ := norm_nonneg _
  -- the processes
  set M : ℝ≥0 → ProbedPath W np × ℝ → ℂ :=
    genObs b E s τ m (b3ObsAll b E s h τ m W Vs) (κ.fn χ ξ) (κ.lam χ ξ b E)
  set D : ProbedPath W np × ℝ → ℂ := fun y => ∑ j ∈ Ico n n', dStep b E s h τ m W Vs χ ξ κ j y
  set SR : ProbedPath W np × ℝ → ℂ := fun y => ∑ j ∈ Ico n n',
    (b3AliveM b E s h τ m R W j Vs).indicator (dStep b E s h τ m W Vs χ ξ κ j) y
  set capM : ProbedPath W np × ℝ → ℂ := fun y =>
    (ClosedIdent.physCapEventM b E s h K W).indicator (fun _ => (1 : ℂ)) y.1.1
  have hcapm : Measurable capM := (measurable_const.indicator
    (ClosedIdent.measurableSet_physCapEventM b E s h K W)).comp
      (measurable_fst.comp measurable_fst)
  have hcapb : ∀ y, ‖capM y‖ ≤ 1 := fun y => by
    simp only [capM, Set.indicator_apply]; split_ifs <;> simp
  have hMm : ∀ v, Measurable (M v) := fun v =>
    (stronglyMeasurable_genObs_b3ObsAll hV' hFc hΛc v).measurable
  have hdm : ∀ j ∈ Ico n n', Measurable (dStep b E s h τ m W Vs χ ξ κ j) := fun j hj =>
    measurable_dStep hV hχ hξ κ (hn0.trans (mem_Ico.1 hj).1)
  have hAm : ∀ j, MeasurableSet (b3AliveM b E s h τ m R W j Vs) := fun j =>
    measurableSet_b3AliveM b E s h τ m R W j hV'
  have hDm : Measurable D := Finset.measurable_sum _ hdm
  have hSRm : Measurable SR :=
    Finset.measurable_sum _ fun j hj => (hdm j hj).indicator (hAm j)
  set Cd := 2 * C + CΛ / W
  have hCd : 0 ≤ Cd := by positivity
  have hdb : ∀ j y, ‖dStep b E s h τ m W Vs χ ξ κ j y‖ ≤ Cd := fun j y =>
    norm_dStep_le hC hCΛ j y
  have hDb : ∀ y, ‖D y‖ ≤ ((n' - n : ℕ) : ℝ) * Cd := fun y => by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul (Ico n n') (fun j => ‖dStep b E s h τ m W Vs χ ξ κ j y‖) Cd
      (fun j _ => hdb j y)
    simpa [nsmul_eq_mul] using this
  have hSRb : ∀ y, ‖SR y‖ ≤ ((n' - n : ℕ) : ℝ) * Cd := fun y => by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul (Ico n n') (fun j => ‖(b3AliveM b E s h τ m R W j Vs).indicator
      (dStep b E s h τ m W Vs χ ξ κ j) y‖) Cd (fun j _ => by
        exact (norm_indicator_le_norm_self _ _).trans (hdb j y))
    simpa [nsmul_eq_mul] using this
  have hMb : ∀ v y, ‖M v y‖ ≤ C + v * CΛ := fun v y => norm_genObs_le hC hCΛ v y
  -- the decomposition of the integrand
  have hcapC : (fun y : ProbedPath W np × ℝ =>
      (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1) =ᵐ[μ] fun y =>
      (ClosedIdent.physCapEventM b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 := by
    have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1) μ
        (growthPathLaw W b) :=
      (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
        (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
    have h1 := hq.ae_eq_comp (indicator_ae_eq_of_ae_eq_set (f := fun _ => (1 : ℝ))
      (ClosedIdent.physCapEvent_ae_eq hb hE1 hE2 s h K (W := W)))
    exact h1
  set T1 : ProbedPath W np × ℝ → ℂ := fun y => ψW y * (capM y * D y - SR y)
  set T2 : ProbedPath W np × ℝ → ℂ := fun y => ψW y * SR y
  set T3 : ProbedPath W np × ℝ → ℂ := fun y => capM y * ψW y * ((M t' y - M t y) - D y)
  have hdec : capIncW b E s h τ m W Vs (κ.fn χ ξ) (κ.lam χ ξ b E) i u ψ t t' =
      ∫ y, (T1 y + T2 y + T3 y) ∂μ := by
    unfold capIncW
    refine integral_congr_ae (hcapC.mono fun y hy => ?_)
    simp only at hy
    dsimp only
    rw [Complex.real_smul, hy]
    simp only [T1, T2, T3, capM, ψW, M, D]
    have : (((ClosedIdent.physCapEventM b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
        ψ (fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y) : ℝ) : ℂ) =
        (ClosedIdent.physCapEventM b E s h K W).indicator (fun _ => (1 : ℂ)) y.1.1 *
          ((ψ (fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y) : ℝ) : ℂ) := by
      push_cast
      simp only [Set.indicator_apply]
      split_ifs <;> simp
    rw [this]
    ring
  -- integrability
  have i1 : Integrable T1 μ := Integrable.of_bound
    (hψm.mul ((hcapm.mul hDm).sub hSRm)).aestronglyMeasurable
    (‖ψ‖ * (((n' - n : ℕ) : ℝ) * Cd + ((n' - n : ℕ) : ℝ) * Cd)) (Eventually.of_forall fun y => by
      simp only [T1, norm_mul]
      refine mul_le_mul (hψb y) ((norm_sub_le _ _).trans (add_le_add ?_ (hSRb y)))
        (norm_nonneg _) hψ0
      rw [norm_mul]
      exact (mul_le_mul (hcapb y) (hDb y) (norm_nonneg _) zero_le_one).trans (by simp))
  have i2 : Integrable T2 μ := Integrable.of_bound (hψm.mul hSRm).aestronglyMeasurable
    (‖ψ‖ * (((n' - n : ℕ) : ℝ) * Cd)) (Eventually.of_forall fun y => by
      simp only [T2, norm_mul]
      exact mul_le_mul (hψb y) (hSRb y) (norm_nonneg _) hψ0)
  have hT3b : ∀ y, ‖T3 y‖ ≤ ‖ψ‖ * (2 * (CΛ * (2 + 2 * np) / W)) := fun y => by
    simp only [T3, norm_mul]
    have h1 := genObs_sub_eq (h := h) (Vs := Vs) hs hτ hW hV' hχ hξ κ hCΛ htt hGt hKt hGt' hKt' y
    calc ‖capM y‖ * ‖ψW y‖ * ‖M t' y - M t y - D y‖ ≤ 1 * ‖ψ‖ * (2 * (CΛ * (2 + 2 * np) / W)) :=
          mul_le_mul (mul_le_mul (hcapb y) (hψb y) (norm_nonneg _) zero_le_one) h1
            (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have i3 : Integrable T3 μ := Integrable.of_bound
    (((hcapm.mul hψm).mul (((hMm t').sub (hMm t)).sub hDm))).aestronglyMeasurable _
    (Eventually.of_forall hT3b)
  have i12 : Integrable (fun y => T1 y + T2 y) μ := i1.add i2
  rw [hdec, integral_add i12 i3, integral_add i1 i2]
  -- the three bounds
  have b3' : ‖∫ y, T3 y ∂μ‖ₑ ≤ ENNReal.ofReal (‖ψ‖ * (2 * (CΛ * (2 + 2 * np) / W))) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ y, ‖T3 y‖ₑ ∂μ ≤ ∫⁻ _, ENNReal.ofReal (‖ψ‖ * (2 * (CΛ * (2 + 2 * np) / W))) ∂μ :=
          lintegral_mono fun y => by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hT3b y)
      _ = _ := by simp
  have b1 : ‖∫ y, T1 y ∂μ‖ₑ ≤ ENNReal.ofReal (‖ψ‖ * (2 * (2 * C +
      ((n' - n : ℕ) : ℝ) * (CΛ / W)))) * μ (badSet b E s h τ m R W n' Vs) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine (lintegral_mono fun y => ?_).trans (lintegral_indicator_const_le _ _)
    have h1 := norm_stop_le (s := s) (τ := τ) (h := h) (Vs := Vs) hC hCΛ R (n := n) (n' := n') y
    by_cases hy : y ∈ badSet b E s h τ m R W n' Vs
    · rw [Set.indicator_of_mem hy, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [T1, norm_mul]
      rw [Set.indicator_of_mem hy, mul_one] at h1
      exact mul_le_mul (hψb y) h1 (norm_nonneg _) hψ0
    · rw [Set.indicator_of_notMem hy, mul_zero] at h1
      rw [Set.indicator_of_notMem hy]
      have : capM y * D y - SR y = 0 := norm_eq_zero.1 (le_antisymm h1 (norm_nonneg _))
      simp [T1, this]
  have b2 : ‖∫ y, T2 y ∂μ‖ₑ ≤
      ∑ j ∈ (Ico n n').filter (fun j => ¬ IsBirthStep τ W j),
        (ENNReal.ofReal (‖ψ‖ * C) * (∑ i, pinE1 b E s h τ m R W Vs j i +
          ∑ i, ∑ i', pinE2 b E s h τ m R W Vs j i i') +
        ENNReal.ofReal ‖ψ‖ * (ENNReal.ofReal C * ∫⁻ y, (b3AliveM b E s h τ m R W j Vs).indicator
          (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W Vs j y) ^ 3)) y ∂μ)) +
      ∑ j ∈ (Ico n n').filter (fun j => IsBirthStep τ W j),
        ENNReal.ofReal ‖ψ‖ * (ENNReal.ofReal (3 * C) *
          ∑ i : BI K np, genBirthStep b E s h τ m R W j Vs (cOf i) + ENNReal.ofReal (CΛ / W)) := by
    have hij : ∀ j ∈ Ico n n', Integrable (fun y => ψW y *
        (b3AliveM b E s h τ m R W j Vs).indicator (dStep b E s h τ m W Vs χ ξ κ j) y) μ :=
      fun j hj => Integrable.of_bound (hψm.mul ((hdm j hj).indicator (hAm j))).aestronglyMeasurable
        (‖ψ‖ * Cd) (Eventually.of_forall fun y => by
          rw [norm_mul]
          refine mul_le_mul (hψb y) ?_ (norm_nonneg _) hψ0
          exact (norm_indicator_le_norm_self _ _).trans (hdb j y))
    have e2 : ∫ y, T2 y ∂μ = ∑ j ∈ Ico n n', ∫ y, ψW y *
        (b3AliveM b E s h τ m R W j Vs).indicator (dStep b E s h τ m W Vs χ ξ κ j) y ∂μ := by
      rw [← integral_finsetSum _ hij]
      exact integral_congr_ae (Eventually.of_forall fun y => by simp only [T2, SR, mul_sum])
    rw [e2]
    refine (enorm_sum_le _ _).trans ?_
    rw [← sum_filter_add_sum_filter_not (Ico n n') (fun j => ¬ IsBirthStep τ W j)]
    simp only [not_not]
    refine add_le_add (sum_le_sum fun j hj => ?_) (sum_le_sum fun j hj => ?_)
    · obtain ⟨hjm, hjb⟩ := mem_filter.1 hj
      exact enorm_step_le hb hE1 hE2 hV hχ hξ κ hC (hn0.trans (mem_Ico.1 hjm).1) hjb
        (hL2 j hjm hjb) (hψj j (mem_Ico.1 hjm).1).stronglyMeasurable hψ0 hψb
    · obtain ⟨hjm, hjb⟩ := mem_filter.1 hj
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      calc ∫⁻ y, ‖ψW y * (b3AliveM b E s h τ m R W j Vs).indicator
            (dStep b E s h τ m W Vs χ ξ κ j) y‖ₑ ∂μ ≤
          ∫⁻ y, ENNReal.ofReal ‖ψ‖ * (b3AliveM b E s h τ m R W j Vs).indicator
            (fun y => ‖dStep b E s h τ m W Vs χ ξ κ j y‖ₑ) y ∂μ := by
            refine lintegral_mono fun y => ?_
            rw [enorm_mul, ← enorm_indicator_eq_indicator_enorm]
            refine mul_le_mul' ?_ le_rfl
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hψb y)
        _ = ENNReal.ofReal ‖ψ‖ * ∫⁻ y, (b3AliveM b E s h τ m R W j Vs).indicator
            (fun y => ‖dStep b E s h τ m W Vs χ ξ κ j y‖ₑ) y ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ _ := mul_le_mul' le_rfl (lint_birth_le hb hE1 hE2 hV'
            (hn0.trans (mem_Ico.1 hjm).1) hC hCΛ0 hCΛ)
  calc _ ≤ ‖∫ y, T1 y ∂μ‖ₑ + ‖∫ y, T2 y ∂μ‖ₑ + ‖∫ y, T3 y ∂μ‖ₑ :=
        (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
    _ ≤ _ := by
        have := add_le_add (add_le_add b1 b2) b3'
        refine this.trans (le_of_eq ?_)
        ring

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
