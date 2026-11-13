module
public import BlockBand.SourceProcess.Stochastic.SourceSDE.DefectBridge
public import BlockBand.SourceProcess.Stochastic.Assembly.NonexplosionExitU
public import BlockBand.SourceProcess.Stochastic.SDE.ExportStop
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Projection preservation for exit-time solutions

Projection preservation in the proof of the finite Gram law. Measure
`driverLaw μ = μ ⊗ Wiener^κ` on `DriverSample S (SourceNoise ι)`, augmented filtration `F_t ∨ N`;
`S : Type u`, `ι : Type v` arbitrary (the Itô formula in the form `SemimartingaleItoFormulaU`).
Hypotheses: `0 ≤ D₀`, `IsNearProjection P Naux`, `𝖣ᴴ = 𝖣`, `ξ` augmented-`F_0`-measurable with
`TwoProjection P 𝖣 ξ` a.s. (no integrability).

* `strongExit_mem_defectSet`: a strong exit-time solution of radius `R` started on the
  constraint stays in `K_R = closedBall 0 R ∪ {Φ = 0}` (`Φ = defectLyapunov`).
* `ae_defect_eq_zero_of_strongExit`: on `K_R`, `𝓛(λΦ) ≤ c(1 + λΦ)` with
  `c = max C_R 0` (`defect_generator_le` and the fderiv bridge `sdeGenerator_defectLyapunov`;
  on `{Φ = 0}` the bound `𝓛Φ ≤ C·Φ = 0` at radius `‖y‖`); the discounted Lyapunov bound
  `lintegral_lyap_leU` on `A = {Φ(ξ) = 0}` with `B = 0` gives
  `e^{-ct} λ ∫_A Φ(X_t) ≤ 1` for every `λ`, so `Φ(X_t) = 0` a.s.; continuity gives all `t`.
* `exitSolution_twoProjection`: every exit-time solution (in the sense of
  `IsSDESolutionUntil … (exitTime X R) X`) satisfies `TwoProjection` at all times a.s.
  (uniqueness until the exit time). This is the invariance hypothesis of `NonexplosionFor`.
-/

namespace BlockBand.SourceProcess.Stochastic.SourceSDE
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal Topology
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic.Integral

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

theorem sdeGenerator_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*}
    [Fintype κ] (b : E → E) (σ : κ → E → E) {Φ : E → ℝ} (hΦ : ContDiff ℝ 2 Φ) (lam : ℝ) (y : E) :
    sdeGenerator b σ (fun q => lam * Φ q) y = lam * sdeGenerator b σ Φ y := by
  rw [sdeGenerator_eq_vecGen, sdeGenerator_eq_vecGen]
  have h := vecGen_clm b σ (lam • ContinuousLinearMap.id ℝ ℝ) hΦ y
  simpa only [_root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using h

universe u v w
variable {S : Type u} {ι : Type v} {c : Type w} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
  [Fintype c]
variable {μ : Measure S} [IsProbabilityMeasure μ]

/-- `K_R = closedBall 0 R ∪ {Φ = 0}`. -/
def defectSet (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (R : ℝ) : Set (Matrix ι c ℂ) :=
  Metric.closedBall 0 R ∪ {y | defectLyapunov P D y = 0}

omit [DecidableEq ι] in
theorem strongExit_mem_defectSet {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {b : Matrix ι c ℂ → Matrix ι c ℂ} {σ : SourceNoise ι → Matrix ι c ℂ → Matrix ι c ℂ}
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ} {R : ℝ}
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsStrongExitSolution μ b σ ξ R X) {x : DriverSample S (SourceNoise ι)}
    (hx : defectLyapunov P D (ξ x) = 0) (t : ℝ≥0) : X t x ∈ defectSet P D R := by
  have hc := hX.continuous x
  by_cases ht : (t : WithTop ℝ≥0) ≤ exitTime X R x
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
    · right
      rw [← h0]
      change defectLyapunov P D (X 0 x) = 0
      rw [hX.init]
      exact hx
    · left
      rw [mem_closedBall_zero_iff]
      exact norm_le_of_le_exitTimeOf hc h0 ht
  · rw [not_le] at ht
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt ht)
    have hXt : X t x = X m x := by
      rw [← hX.stopped t x, stoppedProcess_eq_of_ge ht.le, ← hm]
      rfl
    rw [hXt]
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ m) with h0 | h0
    · right
      rw [← h0]
      change defectLyapunov P D (X 0 x) = 0
      rw [hX.init]
      exact hx
    · left
      rw [mem_closedBall_zero_iff]
      exact norm_le_of_le_exitTimeOf hc h0 (le_of_eq hm)

/-- **Projection preservation at a fixed time** for strong exit-time solutions. -/
theorem ae_defect_eq_zero_of_strongExit {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hDH : Dᴴ = D)
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξ0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, defectLyapunov P D (ξ x) = 0) {R : ℝ}
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsStrongExitSolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ R X)
    (t : ℝ≥0) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, defectLyapunov P D (X t x) = 0 := by
  set Φ := defectLyapunov (c := c) P D with hΦdef
  have hΦ2 : ContDiff ℝ 2 Φ := contDiff_defectLyapunov P D
  have hΦc : Continuous Φ := hΦ2.continuous
  have hΦ0 : ∀ y, 0 ≤ Φ y := defectLyapunov_nonneg P D
  set A := {x : DriverSample S (SourceNoise ι) | Φ (ξ x) = 0} with hAdef
  have hA : MeasurableSet[driverAugmented (κ := SourceNoise ι) μ 0] A :=
    (hΦc.measurable.comp hξ.measurable) (measurableSet_singleton 0)
  have hAm : MeasurableSet A := (driverAugmented (κ := SourceNoise ι) μ).le 0 _ hA
  obtain ⟨C, hC⟩ := defect_generator_le hD0 hP hDH R
  set cc := max C 0
  have hK : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ s, X s x ∈ defectSet P D R :=
    hξ0.mono fun x hx s => strongExit_mem_defectSet hX hx s
  have hgen : ∀ lam : ℝ, 0 ≤ lam → ∀ y ∈ defectSet P D R,
      sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) (fun q => lam * Φ q) y ≤
        cc * (1 + lam * Φ y) := by
    intro lam hlam y hy
    rw [sdeGenerator_const_mul _ _ hΦ2, hΦdef, sdeGenerator_defectLyapunov]
    have hcc : 0 ≤ cc := le_max_right _ _
    have hCc : C ≤ cc := le_max_left _ _
    rcases hy with hy | hy
    · have h1 := hC y (mem_closedBall_zero_iff.1 hy)
      have h2 := hΦ0 y
      have h3 : C * Φ y ≤ cc * Φ y := mul_le_mul_of_nonneg_right hCc h2
      nlinarith [mul_nonneg hlam h2, mul_le_mul_of_nonneg_left (h1.trans h3) hlam]
    · obtain ⟨C', hC'⟩ := defect_generator_le hD0 hP hDH ‖y‖
      have h1 := hC' y le_rfl
      have hy' : defectLyapunov P D y = 0 := hy
      rw [hy', mul_zero] at h1
      rw [hy', mul_zero, add_zero, mul_one]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hlam h1]
  set a := Real.exp (-cc * t)
  have ha : 0 < a := Real.exp_pos _
  have hXm : Measurable (X t) :=
    ((hX.sol.1.adapted t).mono ((driverAugmented (κ := SourceNoise ι) μ).le t)).measurable
  set I := ∫⁻ x in A, ENNReal.ofReal (Φ (X t x)) ∂driverLaw (κ := SourceNoise ι) μ
  have hbound : ∀ lam : ℝ, 0 ≤ lam → ENNReal.ofReal (a * lam) * I ≤ ENNReal.ofReal 1 := by
    intro lam hlam
    have h := lintegral_lyap_leU (SemimartingaleIto.semimartingaleItoFormulaU_holds _)
      (le_max_right C 0) le_rfl ((contDiff_const (c := lam)).mul hΦ2)
      (fun y _ => mul_nonneg hlam (hΦ0 y)) (hgen lam hlam) hX hK hA (B := 0)
      (fun x hx => by
        change Φ (ξ x) = 0 at hx
        rw [hx, mul_zero]) t
    rw [add_zero] at h
    refine le_trans ?_ h
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hAm fun x _ => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [hΦ0 (X t x), mul_nonneg hlam (hΦ0 (X t x))]
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
      ((driverLaw (κ := SourceNoise ι) μ).restrict A) :=
    (ENNReal.measurable_ofReal.comp (hΦc.measurable.comp hXm)).aemeasurable
  have hae := (lintegral_eq_zero_iff' hmeas).1 hI0
  rw [Filter.EventuallyEq, ae_restrict_iff' hAm] at hae
  filter_upwards [hae, hξ0] with x hx hx0
  have h := hx hx0
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h
  exact le_antisymm h (hΦ0 _)

/-- **Projection preservation** for strong exit-time solutions, all times. -/
theorem ae_twoProjection_of_strongExit {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hDH : Dᴴ = D)
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξ0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x)) {R : ℝ}
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsStrongExitSolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ R X) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, TwoProjection P D (X t x) := by
  have hξ0' : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, defectLyapunov P D (ξ x) = 0 :=
    hξ0.mono fun x hx => (defectLyapunov_eq_zero_iff hP.1 hDH _).2 hx
  have hc : Continuous (defectLyapunov (c := c) P D) :=
    (contDiff_defectLyapunov (k := 0) P D).continuous
  have h := indistinguishable_of_continuous (X := fun t x => defectLyapunov P D (X t x))
    (Y := fun _ _ => (0 : ℝ)) (Eventually.of_forall fun x => hc.comp (hX.continuous x))
    (Eventually.of_forall fun _ => continuous_const)
    (fun t => ae_defect_eq_zero_of_strongExit hD0 hP hDH hξ hξ0' hX t)
  filter_upwards [h] with x hx t
  exact (defectLyapunov_eq_zero_iff hP.1 hDH _).1 (hx t)

/-- **Invariance of the constraint under exit-time solutions** (the invariance hypothesis of
`NonexplosionFor`). -/
theorem exitSolution_twoProjection {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hDH : Dᴴ = D)
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξ0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x)) (R : ℝ)
    (Y : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ)
    (hY : IsSDESolutionUntil μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ
      (exitTime Y R) Y) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, TwoProjection P D (Y t x) := by
  have hb := locallyLipschitz_sourceDrift (c := c) D0 Naux P
  have hσ := locallyLipschitz_sourceDiffusion D0 P D
  obtain ⟨X, hX⟩ := exists_solutionUntil_exitTime_strong hb hσ hξ R
  filter_upwards [ae_eq_of_isSDESolutionUntil_exitTime hb hσ hX.sol hY,
    ae_twoProjection_of_strongExit hD0 hP hDH hξ hξ0 hX] with x h1 h2 t
  rw [← h1 t]
  exact h2 t

end BlockBand.SourceProcess.Stochastic.SourceSDE
