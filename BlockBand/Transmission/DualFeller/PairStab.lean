module

public import BlockBand.Transmission.DualFeller.PairGen
public import BlockBand.Transmission.DualFeller.Super
public import BlockBand.SourceProcess.Stochastic.ItoNative.Pair
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionCalculus
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionCoord
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
public import BlockBand.SourceProcess.Stochastic.Bridges.NativeIto

/-!
# Stability of two lifted solutions with different random starts

Setting: any `S : Type`, probability `μ` on `S`, driver space `LΩ S`, law `LP μ`, augmented
filtration `L𝓖 μ`; two admissible starts `ξ, ξ'` (no relation between them) and two lifted
families `F, F'` on the same driver space; a radius `m`; a `𝓖₀`-event `A` on which
`‖ξ‖, ‖ξ'‖ ≤ m` and `pairDist(ξ, ξ') ≤ B`. `jointStop` is the first exit of either copy from
the radius-`m` ball on `A`, and `0` off `A`. Let `c ≥ 0` be a Lyapunov constant of the pair on
the radius-`m` ball (`exists_gen_pairDist_le`).

* `lintegral_pair_le`: for every stopping time `θ` and `T`, with `u = T ∧ θ ∧ jointStop`,
  `∫_A e^{−cu}(1 + B⁻¹ pairDist(X_u, X'_u)) ≤ 2`. Route: the pair is an Itô process
  (`IsNativeItoProcess.prod`), read in coordinates (`IsNativeItoProcess.map_equiv`); Itô's formula with
  `φ = lyapFun` (`e^{−ct}(1 + Φ)`, `Φ = B⁻¹ pairDist`), stopping at `θ ∧ jointStop`, and
  `lintegral_le_of_nonpos_drift_pos` (drift `≤ 0` at positive times; off `A` the process is
  killed at time `0`).

The maximal form, `e^{−cT}(r/B) · P(A ∩ {∃ t ≤ T ∧ e_m ∧ e'_m, pairDist(X_t, X'_t) ≥ r}) ≤ 2`,
follows by the hitting time of `{pairDist ≥ r}`; it is proved in the sibling module,
`measure_pair_sup_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.DualLift
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ ξ' : LΩ S → Fin 6 → ℝ}

open Classical in
/-- First exit of either copy from the radius-`m` ball on `A`; `0` off `A`. -/
def jointStop (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ') (m : ℕ) (A : Set (LΩ S))
    (ω : LΩ S) : WithTop ℝ≥0 :=
  if ω ∈ A then min (F.e m ω) (F'.e m ω) else 0

theorem isStoppingTime_jointStop (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ') (m : ℕ)
    {A : Set (LΩ S)} (hA : MeasurableSet[L𝓖 μ 0] A) :
    IsStoppingTime (L𝓖 μ) (jointStop F F' m A) := by
  intro t
  have h1 := ((F.isStoppingTime_e m).min (F'.isStoppingTime_e m)) t
  have hAt : MeasurableSet[L𝓖 μ t] A := (L𝓖 μ).mono (zero_le : (0 : ℝ≥0) ≤ t) _ hA
  have : {ω | jointStop F F' m A ω ≤ t} =
      (A ∩ {ω | min (F.e m ω) (F'.e m ω) ≤ t}) ∪ Aᶜ := by
    ext ω
    by_cases hω : ω ∈ A
    · simp [jointStop, hω]
    · simp only [jointStop, hω, ite_false, mem_ofPred_eq, mem_union, mem_inter_iff, false_and,
        mem_compl_iff, not_false_eq_true, or_true, iff_true]
      exact bot_le
  rw [this]
  exact (hAt.inter h1).union hAt.compl

theorem jointStop_le_e {F : LiftFamily μ D0 ξ} {F' : LiftFamily μ D0 ξ'} {m : ℕ}
    {A : Set (LΩ S)} {ω : LΩ S} (hω : ω ∈ A) :
    jointStop F F' m A ω ≤ F.e m ω ∧ jointStop F F' m A ω ≤ F'.e m ω := by
  simp only [jointStop, hω, ite_true]
  exact ⟨min_le_left _ _, min_le_right _ _⟩

theorem mem_of_pos_le_jointStop {F : LiftFamily μ D0 ξ} {F' : LiftFamily μ D0 ξ'} {m : ℕ}
    {A : Set (LΩ S)} {ω : LΩ S} {s : ℝ≥0} (hs : 0 < s)
    (h : (s : WithTop ℝ≥0) ≤ jointStop F F' m A ω) : ω ∈ A := by
  by_contra hA
  simp only [jointStop, hA, ite_false, nonpos_iff_eq_zero, WithTop.coe_eq_zero] at h
  exact hs.ne' h

/-- **Discounted supermartingale bound for the coupled pair.** -/
theorem lintegral_pair_le (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ')
    (m : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ y : P6, ‖y.1‖ ≤ m → ‖y.2‖ ≤ m →
      sdeGenerator (pairDrift D0) (pairSigma D0) pairDist y ≤ c * pairDist y)
    {A : Set (LΩ S)} (hA : MeasurableSet[L𝓖 μ 0] A)
    (hAm : ∀ ω ∈ A, ‖ξ ω‖ ≤ m ∧ ‖ξ' ω‖ ≤ m) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ ω ∈ A, pairDist (ξ ω, ξ' ω) ≤ B) {θ : LΩ S → WithTop ℝ≥0}
    (hθ : IsStoppingTime (L𝓖 μ) θ) (T : ℝ≥0) :
    Measurable (fun ω => exp (-c * (min (T : WithTop ℝ≥0) (min (θ ω)
        (jointStop F F' m A ω))).untopA) * (1 + B⁻¹ * pairDist (F.X m (min (T : WithTop ℝ≥0)
        (min (θ ω) (jointStop F F' m A ω))).untopA ω, F'.X m (min (T : WithTop ℝ≥0)
        (min (θ ω) (jointStop F F' m A ω))).untopA ω))) ∧
    ∫⁻ ω in A, ENNReal.ofReal (exp (-c * (min (T : WithTop ℝ≥0) (min (θ ω)
        (jointStop F F' m A ω))).untopA) * (1 + B⁻¹ * pairDist (F.X m (min (T : WithTop ℝ≥0)
        (min (θ ω) (jointStop F F' m A ω))).untopA ω, F'.X m (min (T : WithTop ℝ≥0)
        (min (θ ω) (jointStop F F' m A ω))).untopA ω))) ∂LP μ ≤ ENNReal.ofReal 2 := by
  set θ' : LΩ S → WithTop ℝ≥0 := fun ω => min (θ ω) (jointStop F F' m A ω) with hθ'def
  have hθ' : IsStoppingTime (L𝓖 μ) θ' := hθ.min (isStoppingTime_jointStop F F' m hA)
  set L := coordEquiv P6
  set Φ : P6 → ℝ := fun q => B⁻¹ * pairDist q with hΦdef
  have hΦ : ContDiff ℝ 2 Φ := contDiff_const.mul contDiff_pairDist
  have hΦ0 : ∀ q, 0 ≤ Φ q := fun q => mul_nonneg (inv_nonneg.2 hB0.le) (pairDist_nonneg q)
  have hP := (F.strong m).sol.1.prod (F'.strong m).sol.1
  have hY := IsNativeItoProcess.map_equiv hP L
  have hS := hY.isContinuousSemimartingale
  have hφ := contDiff_lyapFun L c hΦ
  have hZ := SemimartingaleIto.semimartingaleItoFormula_holds _ (LΩ S) (LP μ) (L𝓖 μ) _ _ _ hS
    univ isOpen_univ (Eventually.of_forall fun _ _ => mem_univ _) (lyapFun L Φ c)
    hφ.continuous.measurable hφ.contDiffOn
  have H3 := Semimartingale.stoppedSemimartingale_holds 1 (LΩ S) (LP μ) (L𝓖 μ) _ _ _ hZ θ' hθ'
  have hval : ∀ (s : ℝ≥0) ω, lyapFun L Φ c ((s : ℝ), L (F.X m s ω, F'.X m s ω)) =
      exp (-c * s) * (1 + B⁻¹ * pairDist (F.X m s ω, F'.X m s ω)) := fun s ω => by
    simp only [lyapFun, ContinuousLinearEquiv.symm_apply_apply, hΦdef]
  have h0 : ∀ ω, (min ((0 : ℝ≥0) : WithTop ℝ≥0) (θ' ω)).untopA = 0 := fun ω => by
    rw [min_eq_left (by rw [WithTop.coe_zero]; exact bot_le)]; rfl
  have hgen : ∀ x : P6, ‖x.1‖ ≤ m → ‖x.2‖ ≤ m →
      sdeGenerator (pairDrift D0) (pairSigma D0) Φ x ≤ c * (1 + Φ x) := by
    intro x h1 h2
    have e1 := ((genAt_pairDist (pairDrift D0) (pairSigma D0) x).const_mul B⁻¹).gen
    have e2 := (genAt_pairDist (pairDrift D0) (pairSigma D0) x).gen
    rw [hΦdef, e1, ← e2]
    have := mul_le_mul_of_nonneg_left (hc x h1 h2) (inv_nonneg.2 hB0.le)
    nlinarith [hΦ0 x]
  have h := lintegral_le_of_nonpos_drift_pos H3 ?_ ?_ hA (B := 2) ?_ T
  · have hm : Measurable fun ω => stoppedProcess (fun (t : ℝ≥0) (ω : LΩ S) (_ : Fin 1) =>
        lyapFun L Φ c ((t : ℝ), L (F.X m t ω, F'.X m t ω))) θ' T ω 0 :=
      (measurable_pi_apply 0).comp (((H3.adapted T).mono ((L𝓖 μ).le T)).measurable)
    simp only [stoppedProcess, hval] at hm h
    refine ⟨hm, h.trans ?_⟩
    calc _ ≤ ∫⁻ _ in A, ENNReal.ofReal 2 ∂LP μ := by
          refine setLIntegral_mono measurable_const fun ω hω => ENNReal.ofReal_le_ofReal ?_
          simp only [h0, NNReal.coe_zero, mul_zero, exp_zero, one_mul, F.X_zero, F'.X_zero]
          have := mul_le_mul_of_nonneg_left (hB ω hω) (inv_nonneg.2 hB0.le)
          rw [inv_mul_cancel₀ hB0.ne'] at this
          linarith
      _ ≤ ENNReal.ofReal 2 := by
          rw [setLIntegral_const]
          exact mul_le_of_le_one_right zero_le prob_le_one
  · -- the drift is nonpositive at positive times
    refine Eventually.of_forall fun ω s hs => ?_
    unfold switchAfter
    split_ifs with hsθ
    · have hsj : (s : WithTop ℝ≥0) ≤ jointStop F F' m A ω := hsθ.trans (min_le_right _ _)
      have hωA : ω ∈ A := mem_of_pos_le_jointStop hs hsj
      have hse := hsj.trans (jointStop_le_e hωA).1
      have hse' := hsj.trans (jointStop_le_e hωA).2
      have hb1 : switchOff (exitTime (F.X m) m) (fun t x => liftDrift D0 (F.X m t x)) s ω =
          liftDrift D0 (F.X m s ω) := ite_eq_left hse
      have hb2 : switchOff (exitTime (F'.X m) m) (fun t x => liftDrift D0 (F'.X m t x)) s ω =
          liftDrift D0 (F'.X m s ω) := ite_eq_left hse'
      have hs1 : ∀ a, switchOff (exitTime (F.X m) m) (fun t x => liftSigma D0 a (F.X m t x)) s ω =
          liftSigma D0 a (F.X m s ω) := fun a => ite_eq_left hse
      have hs2 : ∀ a, switchOff (exitTime (F'.X m) m)
          (fun t x => liftSigma D0 a (F'.X m t x)) s ω = liftSigma D0 a (F'.X m s ω) :=
        fun a => ite_eq_left hse'
      dsimp only
      simp only [hb1, hb2, hs1, hs2]
      have hx1 : ‖F.X m s ω‖ ≤ m := (F.norm_X_le m s ω).trans (max_le le_rfl (hAm ω hωA).1)
      have hx2 : ‖F'.X m s ω‖ ≤ m := (F'.norm_X_le m s ω).trans (max_le le_rfl (hAm ω hωA).2)
      exact itoDrift_lyapFun_nonpos_on L c hΦ (b := pairDrift D0) (σ := pairSigma D0) le_rfl
        (x := (F.X m s ω, F'.X m s ω)) (hΦ0 _) (hgen _ hx1 hx2) s
    · exact le_rfl
  · refine Eventually.of_forall fun ω t => ?_
    simp only [stoppedProcess, hval]
    exact mul_nonneg (exp_pos _).le (by linarith [hΦ0 (F.X m (min (t : WithTop ℝ≥0)
      (θ' ω)).untopA ω, F'.X m (min (t : WithTop ℝ≥0) (θ' ω)).untopA ω)])
  · intro ω hω
    simp only [stoppedProcess, h0, F.X_zero, F'.X_zero, NNReal.coe_zero, lyapFun,
      ContinuousLinearEquiv.symm_apply_apply, hΦdef, mul_zero, exp_zero, one_mul]
    have := mul_le_mul_of_nonneg_left (hB ω hω) (inv_nonneg.2 hB0.le)
    rw [inv_mul_cancel₀ hB0.ne'] at this
    linarith

end BlockBand.Transmission.DualFeller
