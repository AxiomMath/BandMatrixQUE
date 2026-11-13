module

public import BlockBand.Transmission.DualLift.SphereGen
public import BlockBand.SourceProcess.Stochastic.SourceSDE.Preservation

/-!
# Invariance of the manifold `liftM` (sphere and `s = 1/S̃`)

Probability space: the driver space `DriverSample S (Fin 5)` (`S : Type u`, any
probability `μ` on `S`), law `driverLaw μ`, augmented filtration. Start `ξ`: any
augmented-`𝓕₀`-measurable random point that lies a.s. in `liftM` (random starts allowed).

* `strongExit_mem_defectSetR`: a strong exit-time solution of radius `R` started in `liftM`
  stays in `closedBall 0 R ∪ liftM` (pathwise).
* `ae_mem_liftM_of_strongExit`: for every strong exit-time solution `X` of the lifted SDE and
  every `t`, a.s. `X_t ∈ liftM`. Proof (as for the preservation of projections of the source
  SDE): `𝓛̃(λΦ) ≤ c(1 + λΦ)` on `closedBall 0 R ∪ liftM` for every `λ ≥ 0`
  (`sdeGenerator_liftDefect_le`), the discounted Lyapunov bound `lintegral_lyap_leU` on the
  event `{ξ ∈ liftM}` with `B = 0`, hence `E[Φ(X_t); ξ ∈ liftM] = 0`.
* **`ae_forall_mem_liftM`**: almost surely `X_t ∈ liftM` for all `t` (continuity of paths).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic.Integral
open scoped NNReal ENNReal

universe u
variable {S : Type u} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

/-- `K_R = closedBall 0 R ∪ liftM`. -/
def defectSetR (R : ℝ) : Set (Fin 6 → ℝ) := Metric.closedBall 0 R ∪ liftM

theorem strongExit_mem_defectSetR {b : (Fin 6 → ℝ) → Fin 6 → ℝ}
    {σ : Fin 5 → (Fin 6 → ℝ) → Fin 6 → ℝ} {ξ : DriverSample S (Fin 5) → Fin 6 → ℝ} {R : ℝ}
    {X : ℝ≥0 → DriverSample S (Fin 5) → Fin 6 → ℝ} (hX : IsStrongExitSolution μ b σ ξ R X)
    {x : DriverSample S (Fin 5)} (hx : ξ x ∈ liftM) (t : ℝ≥0) : X t x ∈ defectSetR R := by
  have hc := hX.continuous x
  have h0 : X 0 x ∈ defectSetR R := Or.inr (by rw [hX.init]; exact hx)
  by_cases ht : (t : WithTop ℝ≥0) ≤ exitTime X R x
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h]; exact h0
    · exact Or.inl (mem_closedBall_zero_iff.2 (norm_le_of_le_exitTimeOf hc h ht))
  · rw [not_le] at ht
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt ht)
    have hXt : X t x = X m x := by
      rw [← hX.stopped t x, stoppedProcess_eq_of_ge ht.le, ← hm]
      rfl
    rw [hXt]
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ m) with h | h
    · rw [← h]; exact h0
    · exact Or.inl (mem_closedBall_zero_iff.2 (norm_le_of_le_exitTimeOf hc h (le_of_eq hm)))

variable {D0 : ℝ}

/-- The Lyapunov hypothesis of `lintegral_lyap_leU` for every multiple of the defect. -/
theorem defect_gen_le (hD0 : 0 ≤ D0) (R : ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ lam : ℝ, 0 ≤ lam →
    ∀ y ∈ defectSetR R, sdeGenerator (liftDrift D0) (liftSigma D0) (fun q => lam * liftDefect q) y
      ≤ c * (1 + lam * liftDefect y) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin 6 → ℝ) R).exists_bound_of_continuousOn
    (continuous_defectRate D0).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun lam hlam y hy => ?_⟩
  have hΦ2 : ContDiff ℝ 2 liftDefect := contDiff_liftDefect.of_le le_top
  rw [sdeGenerator_const_mul _ _ hΦ2]
  have hb := sdeGenerator_liftDefect_le hD0 y
  have hΦ0 := liftDefect_nonneg y
  have hr0 := defectRate_nonneg D0 y
  have hc0 : 0 ≤ max C 0 := le_max_right _ _
  rcases hy with hy | hy
  · have hr : defectRate D0 y ≤ max C 0 := by
      have := hC y hy
      rw [Real.norm_eq_abs, abs_of_nonneg hr0] at this
      exact this.trans (le_max_left _ _)
    have h1 : sdeGenerator (liftDrift D0) (liftSigma D0) liftDefect y ≤ max C 0 * liftDefect y :=
      hb.trans (mul_le_mul_of_nonneg_right hr hΦ0)
    nlinarith [mul_le_mul_of_nonneg_left h1 hlam, mul_nonneg hlam hΦ0]
  · have hz : liftDefect y = 0 := (liftDefect_eq_zero_iff y).2 hy
    rw [hz, mul_zero] at hb
    rw [hz, mul_zero, add_zero, mul_one]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hlam hb]

/-- **Invariance of `liftM` at a fixed time.** -/
theorem ae_mem_liftM_of_strongExit (hD0 : 0 < D0) {ξ : DriverSample S (Fin 5) → Fin 6 → ℝ}
    (hξ : StronglyMeasurable[driverAugmented (κ := Fin 5) μ 0] ξ)
    (hξ0 : ∀ᵐ x ∂driverLaw (κ := Fin 5) μ, ξ x ∈ liftM) {R : ℝ}
    {X : ℝ≥0 → DriverSample S (Fin 5) → Fin 6 → ℝ}
    (hX : IsStrongExitSolution μ (liftDrift D0) (liftSigma D0) ξ R X) (t : ℝ≥0) :
    ∀ᵐ x ∂driverLaw (κ := Fin 5) μ, X t x ∈ liftM := by
  set Φ := liftDefect with hΦdef
  have hΦ2 : ContDiff ℝ 2 Φ := contDiff_liftDefect.of_le le_top
  have hΦc : Continuous Φ := hΦ2.continuous
  set A := {x : DriverSample S (Fin 5) | ξ x ∈ liftM} with hAdef
  have hMc : IsClosed liftM := by
    have : liftM = liftDefect ⁻¹' {0} := by
      ext y; simp [liftDefect_eq_zero_iff]
    rw [this]; exact isClosed_singleton.preimage hΦc
  have hA : MeasurableSet[driverAugmented (κ := Fin 5) μ 0] A :=
    hξ.measurable hMc.measurableSet
  have hAm : MeasurableSet A := (driverAugmented (κ := Fin 5) μ).le 0 _ hA
  obtain ⟨cc, hcc0, hgen⟩ := defect_gen_le hD0.le R
  have hK : ∀ᵐ x ∂driverLaw (κ := Fin 5) μ, ∀ s, X s x ∈ defectSetR R :=
    hξ0.mono fun x hx s => strongExit_mem_defectSetR hX hx s
  set a := Real.exp (-cc * t)
  have ha : 0 < a := Real.exp_pos _
  have hXm : Measurable (X t) :=
    ((hX.sol.1.adapted t).mono ((driverAugmented (κ := Fin 5) μ).le t)).measurable
  set I := ∫⁻ x in A, ENNReal.ofReal (Φ (X t x)) ∂driverLaw (κ := Fin 5) μ
  have hbound : ∀ lam : ℝ, 0 ≤ lam → ENNReal.ofReal (a * lam) * I ≤ ENNReal.ofReal 1 := by
    intro lam hlam
    have h := lintegral_lyap_leU (SemimartingaleIto.semimartingaleItoFormulaU_holds _)
      hcc0 le_rfl ((contDiff_const (c := lam)).mul hΦ2)
      (fun y _ => mul_nonneg hlam (liftDefect_nonneg y)) (hgen lam hlam) hX hK hA (B := 0)
      (fun x hx => by
        change ξ x ∈ liftM at hx
        rw [hΦdef, (liftDefect_eq_zero_iff _).2 hx, mul_zero]) t
    rw [add_zero] at h
    refine le_trans ?_ h
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hAm fun x _ => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [liftDefect_nonneg (X t x), mul_nonneg hlam (liftDefect_nonneg (X t x))]
  have hItop : I ≠ ⊤ := by
    intro hI
    have h := hbound 1 zero_le_one
    rw [hI, ENNReal.mul_top (by simpa using ha)] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
  have hI0 : I = 0 := by
    refine eq_zero_of_forall_mul_le hItop ha (D := 1) fun M hM => ?_
    rw [mul_comm]
    exact hbound (1 + M) (by linarith)
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (Φ (X t x)))
      ((driverLaw (κ := Fin 5) μ).restrict A) :=
    (ENNReal.measurable_ofReal.comp (hΦc.measurable.comp hXm)).aemeasurable
  have hae := (lintegral_eq_zero_iff' hmeas).1 hI0
  rw [Filter.EventuallyEq, ae_restrict_iff' hAm] at hae
  filter_upwards [hae, hξ0] with x hx hx0
  have h := hx hx0
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h
  exact (liftDefect_eq_zero_iff _).1 (le_antisymm h (liftDefect_nonneg _))

/-- **The manifold `liftM` is invariant**, almost surely for all times. -/
theorem ae_forall_mem_liftM (hD0 : 0 < D0) {ξ : DriverSample S (Fin 5) → Fin 6 → ℝ}
    (hξ : StronglyMeasurable[driverAugmented (κ := Fin 5) μ 0] ξ)
    (hξ0 : ∀ᵐ x ∂driverLaw (κ := Fin 5) μ, ξ x ∈ liftM) {R : ℝ}
    {X : ℝ≥0 → DriverSample S (Fin 5) → Fin 6 → ℝ}
    (hX : IsStrongExitSolution μ (liftDrift D0) (liftSigma D0) ξ R X) :
    ∀ᵐ x ∂driverLaw (κ := Fin 5) μ, ∀ t, X t x ∈ liftM := by
  have hc : Continuous liftDefect := (contDiff_liftDefect.of_le (m := 0) le_top).continuous
  have h := indistinguishable_of_continuous (X := fun t x => liftDefect (X t x))
    (Y := fun _ _ => (0 : ℝ)) (Eventually.of_forall fun x => hc.comp (hX.continuous x))
    (Eventually.of_forall fun _ => continuous_const)
    (fun t => (ae_mem_liftM_of_strongExit hD0 hξ hξ0 hX t).mono fun x hx =>
      (liftDefect_eq_zero_iff _).2 hx)
  filter_upwards [h] with x hx t
  exact (liftDefect_eq_zero_iff _).1 (hx t)

end BlockBand.Transmission.DualLift
