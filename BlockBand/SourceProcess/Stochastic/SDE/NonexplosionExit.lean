module
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionCoord
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionCalculus
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionSuper
public import BlockBand.SourceProcess.Stochastic.Bridges.NativeIto
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Exit times escape to infinity under a Lyapunov condition

* `lintegral_lyap_le`: for a strong exit-time solution `X` (radius `R`) staying in `K`, and an
  `F_0 ∨ N`-event `A` on which `Φ(ξ) ≤ B`,
  `∫_A e^{-ct} (1 + Φ(X_t)) dP ≤ 1 + B`, for `c ≥ max C 0`. Route: coordinates
  (`IsNativeItoProcess.map_equiv`), bridge (`isContinuousSemimartingale`), the contract
  with `U = univ` and `φ = lyapFun`, the drift bound (`itoDrift_lyapFun_nonpos_*`), and
  `lintegral_le_of_nonpos_drift`.
* `measure_exitTime_le_mul_le`: if `Φ ≥ M` on `K` outside the `R`-ball,
  `P(A ∩ {exit_R ≤ t}) · e^{-ct}(1 + M) ≤ 1 + B` (the exit level is attained and `X` is stopped).
* `ae_exists_lt_exitTime`: for strong exit-time solutions `X^n` of radius `n` staying in `K`,
  almost surely every time `T` is before some exit time `exit_n(X^n)`.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.Transmission

variable {S κ : Type} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Discounted Lyapunov bound** on an `F_0 ∨ N`-event. -/
theorem lintegral_lyap_le (hIto : SemimartingaleItoFormula (Module.finrank ℝ E))
    {b : E → E} {σ : κ → E → E} {ξ : DriverSample S κ → E} {K : Set E} {Φ : E → ℝ} {C c : ℝ}
    (hc0 : 0 ≤ c) (hCc : C ≤ c) (hΦ : ContDiff ℝ 2 Φ) (hΦK : ∀ y ∈ K, 0 ≤ Φ y)
    (hgen : ∀ y ∈ K, sdeGenerator b σ Φ y ≤ C * (1 + Φ y)) {R : ℝ}
    {X : ℝ≥0 → DriverSample S κ → E} (hX : IsStrongExitSolution μ b σ ξ R X)
    (hXK : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X t x ∈ K) {A : Set (DriverSample S κ)}
    (hA : MeasurableSet[driverAugmented (κ := κ) μ 0] A) {B : ℝ} (hB : ∀ x ∈ A, Φ (ξ x) ≤ B)
    (t : ℝ≥0) :
    ∫⁻ x in A, ENNReal.ofReal (Real.exp (-c * t) * (1 + Φ (X t x))) ∂driverLaw (κ := κ) μ ≤
      ENNReal.ofReal (1 + B) := by
  set L := coordEquiv E
  set e := exitTime X R
  have hY := IsNativeItoProcess.map_equiv hX.sol.1 L
  have hS := hY.isContinuousSemimartingale
  have hφ := contDiff_lyapFun L c hΦ
  have hZ := hIto (DriverSample S κ) (driverLaw (κ := κ) μ) (driverAugmented (κ := κ) μ) _ _ _ hS
    univ isOpen_univ (Eventually.of_forall fun _ _ => mem_univ _) (lyapFun L Φ c)
    hφ.continuous.measurable hφ.contDiffOn
  have hval : ∀ (s : ℝ≥0) x, lyapFun L Φ c ((s : ℝ), L (X s x)) =
      Real.exp (-c * s) * (1 + Φ (X s x)) := fun s x => by
    simp only [lyapFun, ContinuousLinearEquiv.symm_apply_apply]
  have h := lintegral_le_of_nonpos_drift hZ ?_ ?_ hA (B := 1 + B) ?_ t
  · simp only [hval] at h
    refine h.trans ?_
    calc ∫⁻ x in A, ENNReal.ofReal (Real.exp (-c * ((0 : ℝ≥0) : ℝ)) * (1 + Φ (X 0 x)))
          ∂driverLaw (κ := κ) μ
        ≤ ∫⁻ _x in A, ENNReal.ofReal (1 + B) ∂driverLaw (κ := κ) μ := by
          refine setLIntegral_mono measurable_const fun x hx => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          simp only [NNReal.coe_zero, mul_zero, Real.exp_zero, one_mul, hX.init x]
          linarith [hB x hx]
      _ ≤ ENNReal.ofReal (1 + B) := by
          rw [setLIntegral_const]
          exact mul_le_of_le_one_right zero_le prob_le_one
  · -- the drift is nonpositive
    filter_upwards [hXK] with x hx s
    change itoDrift (lyapFun L Φ c) (L (X s x)) s (L (switchOff e (fun t x => b (X t x)) s x))
      (Matrix.of fun i j => ∑ a, L (switchOff e (fun t x => σ a (X t x)) s x) i *
        L (switchOff e (fun t x => σ a (X t x)) s x) j) ≤ 0
    by_cases hs : (s : WithTop ℝ≥0) ≤ e x
    · have h1 : switchOff e (fun t x => b (X t x)) s x = b (X s x) := ite_eq_left hs
      have h2 : ∀ a, switchOff e (fun t x => σ a (X t x)) s x = σ a (X s x) := fun a =>
        ite_eq_left hs
      simp only [h1, h2]
      exact itoDrift_lyapFun_nonpos_on L c hΦ hCc (hΦK _ (hx s)) (hgen _ (hx s)) s
    · have h1 : switchOff e (fun t x => b (X t x)) s x = 0 := ite_eq_right hs
      have h2 : ∀ a, switchOff e (fun t x => σ a (X t x)) s x = 0 := fun a => ite_eq_right hs
      simp only [h1, h2, map_zero]
      exact itoDrift_lyapFun_nonpos_off (κ := κ) L c hΦ hc0
        (by rw [ContinuousLinearEquiv.symm_apply_apply]; exact hΦK _ (hx s)) s
  · filter_upwards [hXK] with x hx s
    rw [hval]
    exact mul_nonneg (Real.exp_pos _).le (by linarith [hΦK _ (hx s)])
  · intro x hx
    rw [hval]
    simp only [NNReal.coe_zero, mul_zero, Real.exp_zero, one_mul, hX.init x]
    linarith [hB x hx]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Exit probability bound** from the Lyapunov bound and coercivity. -/
theorem measure_exitTime_le_mul_le (hIto : SemimartingaleItoFormula (Module.finrank ℝ E))
    {b : E → E} {σ : κ → E → E} {ξ : DriverSample S κ → E} {K : Set E} {Φ : E → ℝ} {C c : ℝ}
    (hc0 : 0 ≤ c) (hCc : C ≤ c) (hΦ : ContDiff ℝ 2 Φ) (hΦK : ∀ y ∈ K, 0 ≤ Φ y)
    (hgen : ∀ y ∈ K, sdeGenerator b σ Φ y ≤ C * (1 + Φ y)) {R M : ℝ}
    (hcoer : ∀ y ∈ K, R ≤ ‖y‖ → M ≤ Φ y)
    {X : ℝ≥0 → DriverSample S κ → E} (hX : IsStrongExitSolution μ b σ ξ R X)
    (hXK : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X t x ∈ K) {A : Set (DriverSample S κ)}
    (hA : MeasurableSet[driverAugmented (κ := κ) μ 0] A) {B : ℝ} (hB : ∀ x ∈ A, Φ (ξ x) ≤ B)
    (t : ℝ≥0) :
    driverLaw (κ := κ) μ (A ∩ {x | exitTime X R x ≤ t}) *
      ENNReal.ofReal (Real.exp (-c * t) * (1 + M)) ≤ ENNReal.ofReal (1 + B) := by
  have hEm : MeasurableSet {x | exitTime X R x ≤ t} :=
    (driverAugmented (κ := κ) μ).le t _ (hX.stopping.measurableSet_le t)
  refine le_trans ?_ (lintegral_lyap_le hIto hc0 hCc hΦ hΦK hgen hX hXK hA hB t)
  rw [mul_comm, inter_comm, ← Measure.restrict_apply hEm, ← lintegral_indicator_const hEm]
  refine lintegral_mono_ae (ae_restrict_of_ae ?_)
  filter_upwards [hXK] with x hx
  by_cases hxe : exitTime X R x ≤ t
  · rw [Set.indicator_of_mem (show x ∈ {x | exitTime X R x ≤ t} from hxe)]
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hxe)
    have hXt : X t x = X m x := by
      rw [← hX.stopped t x, stoppedProcess_eq_of_ge hxe, ← hm]
      rfl
    have hR : R ≤ ‖X t x‖ := by
      rw [hXt]
      exact le_norm_exitTimeOf (hX.continuous x) hm.symm
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    linarith [hcoer _ (hx t) hR]
  · rw [Set.indicator_of_notMem (show x ∉ {x | exitTime X R x ≤ t} from hxe)]
    exact zero_le

/-- An `ℝ≥0∞` number `p ≠ ⊤` with `p · a(1 + M) ≤ D` for all `M ≥ 0` (`a > 0`) is zero. -/
theorem eq_zero_of_forall_mul_le {p : ℝ≥0∞} (hp : p ≠ ⊤) {a D : ℝ} (ha : 0 < a)
    (h : ∀ M : ℝ, 0 ≤ M → p * ENNReal.ofReal (a * (1 + M)) ≤ ENNReal.ofReal D) : p = 0 := by
  by_contra hp0
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set M := (|D| + 1) / (p.toReal * a)
  have hM : 0 ≤ M := div_nonneg (by positivity) (by positivity)
  have h1 := h M hM
  rw [← ENNReal.ofReal_toReal hp, ← ENNReal.ofReal_mul hq.le,
    ENNReal.ofReal_le_ofReal_iff'] at h1
  have h2 : p.toReal * (a * (1 + M)) = p.toReal * a + (|D| + 1) := by
    simp only [M]
    field_simp
  rcases h1 with h1 | h1
  · rw [h2] at h1
    linarith [le_abs_self D, mul_pos hq ha]
  · linarith [mul_pos hq (mul_pos ha (by linarith : (0 : ℝ) < 1 + M))]

/-- **Exit times escape**: almost surely every time precedes some exit time. -/
theorem ae_exists_lt_exitTime (hIto : SemimartingaleItoFormula (Module.finrank ℝ E))
    {b : E → E} {σ : κ → E → E} {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) {K : Set E} {Φ : E → ℝ} {C : ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (hΦK : ∀ y ∈ K, 0 ≤ Φ y)
    (hcoer : ∀ M : ℝ, ∃ R : ℝ, ∀ y ∈ K, R ≤ ‖y‖ → M ≤ Φ y)
    (hgen : ∀ y ∈ K, sdeGenerator b σ Φ y ≤ C * (1 + Φ y))
    {X : ℕ → ℝ≥0 → DriverSample S κ → E} (hX : ∀ n : ℕ, IsStrongExitSolution μ b σ ξ n (X n))
    (hXK : ∀ n, ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X n t x ∈ K) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ T : ℕ, ∃ n : ℕ,
      ((T : ℝ≥0) : WithTop ℝ≥0) < exitTime (X n) n x := by
  rw [ae_all_iff]
  intro T
  set c := max C 0
  set Bad := {x : DriverSample S κ | ∀ n : ℕ, exitTime (X n) n x ≤ ((T : ℝ≥0) : WithTop ℝ≥0)}
  have hBad : ∀ r : ℕ, driverLaw (κ := κ) μ ({x | ‖ξ x‖ ≤ r} ∩ Bad) = 0 := by
    intro r
    have hA : MeasurableSet[driverAugmented (κ := κ) μ 0] {x | ‖ξ x‖ ≤ (r : ℝ)} :=
      (measurable_norm.comp hξ.measurable) measurableSet_Iic
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) r).exists_bound_of_continuousOn
      hΦ.continuous.continuousOn
    have hBA : ∀ x ∈ {x | ‖ξ x‖ ≤ (r : ℝ)}, Φ (ξ x) ≤ B := fun x hx =>
      (le_abs_self _).trans (hB _ (mem_closedBall_zero_iff.2 hx))
    refine eq_zero_of_forall_mul_le (measure_ne_top _ _) (Real.exp_pos (-c * T)) (D := 1 + B)
      fun M _ => ?_
    obtain ⟨R, hR⟩ := hcoer M
    set n := ⌈R⌉₊
    have hcoer' : ∀ y ∈ K, ((n : ℕ) : ℝ) ≤ ‖y‖ → M ≤ Φ y := fun y hy h =>
      hR y hy ((Nat.le_ceil R).trans h)
    refine le_trans (mul_le_mul_left ?_ _)
      (measure_exitTime_le_mul_le hIto (le_max_right C 0) (le_max_left C 0) hΦ hΦK hgen hcoer'
        (hX n) (hXK n) hA hBA T)
    exact measure_mono (inter_subset_inter_right _ fun x hx => hx n)
  have hnull : driverLaw (κ := κ) μ Bad = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hBad)
    obtain ⟨r, hr⟩ := exists_nat_ge ‖ξ x‖
    exact mem_iUnion.2 ⟨r, hr, hx⟩
  refine measure_mono_null (fun x hx => ?_) hnull
  exact fun n => not_lt.1 fun h => hx ⟨n, h⟩

end BlockBand.SourceProcess.Stochastic.NativeSDE
