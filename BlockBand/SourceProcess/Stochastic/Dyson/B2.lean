module

public import BlockBand.SourceProcess.Stochastic.Dyson.B2Local

/-!
# Dyson Brownian motion: the semimartingale clause from non-collision and the Itô contracts

The semimartingale clause (b2) of `DysonBrownianMotion`, for the vector Dyson Brownian motion and
its pair generator.

`dysonBM_b2_of_b1`: assuming the Itô formula (a1) `SemimartingaleItoFormula` and the stopping
statement (a2) `StoppedSemimartingale` (explicit hypotheses `hIto`, `hStop`), and the non-collision
clause (b1) (explicit hypothesis `hb1`), for every `s > 0` and `q` the joint process
`u ↦ (λ(F + G_{s+u}), X^q(F + G_{s+u}))` is a continuous semimartingale for `u ↦ 𝓖_{s+u}` with
drift `dysonStateDrift` and covariance `dysonStateCov`, localized by `dysonRho`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

/-- Second countability of real square matrices (local instance). -/
theorem secondCountableTopology_matrix_real (M : ℕ) :
    SecondCountableTopology (Matrix (Fin M) (Fin M) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin M → Fin M → ℝ))

/-- Pseudo-metrizability of real square matrices (local instance). -/
theorem pseudoMetrizable_matrix_real (M : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin M) (Fin M) ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin M → Fin M → ℝ))

attribute [local instance] secondCountableTopology_matrix_real pseudoMetrizable_matrix_real

theorem IsStronglyProgressive.comp_measurable' {Ω E β : Type*} [MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace β]
    {Y : ℝ≥0 → Ω → E} (hY : IsStronglyProgressive 𝓕 Y) {g : E → β} (hg : Measurable g) :
    IsStronglyProgressive 𝓕 (fun t ω => g (Y t ω)) := fun t =>
  (hg.comp (hY t).measurable).stronglyMeasurable

/-- **Clause (b2) of `DysonBrownianMotion`**, from (a1), (a2) and clause (b1). -/
theorem dysonBM_b2_of_b1 (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : ∀ d, StoppedSemimartingale d) {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {N : ℕ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
    (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian)
    (hb1 : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω))
    (s : ℝ≥0) (hs : 0 < s) (q : Fin N → ℂ) :
    IsContinuousSemimartingale Q (shiftFiltration 𝓖 s)
      (fun u ω => dysonState N q (F ω + G (s + u) ω))
      (fun u ω => dysonStateDrift N (dysonState N q (F ω + G (s + u) ω)))
      (fun u ω => dysonStateCov N (dysonState N q (F ω + G (s + u) ω))) := by
  have hb1' : ∀ᵐ ω ∂Q, NoCollision N G F ω := hb1
  have hY : IsContinuousSemimartingale Q (shiftFiltration 𝓖 s) (Ypath N G F s) (fun _ _ => 0)
      (fun _ _ => gueCovVec N) := isContinuousSemimartingale_hermVec hG hF s
  have hYU : ∀ᵐ ω ∂Q, ∀ t, Ypath N G F s t ω ∈ simpleSet N :=
    hb1'.mono fun ω hω t => hermVec_mem_simpleSet hG hFh hs hω t
  have hmS : Measurable fun y : Fin (N * N) → ℝ => dysonState N q (vecHerm N y) :=
    (measurable_dysonState q).comp continuous_vecHerm.measurable
  have hmg : ∀ k, Measurable (stateFn N q k) := fun k => (measurable_pi_apply k).comp hmS
  have hρ := isStoppingTime_dysonRho hG hF s
  -- single components
  have hk : ∀ n k, HasMartingaleModification Q (shiftFiltration 𝓖 s)
        (stoppedProcess (locComp (Ypath N G F s) (stateFn N q k) (driftK N q k))
          (dysonRho G F s n)) ∧
      HasMartingaleModification Q (shiftFiltration 𝓖 s)
        (stoppedProcess (locSq (Ypath N G F s) (stateFn N q k) (driftK N q k) (covKL N q k k))
          (dysonRho G F s n)) := fun n k =>
    localized_hasMM hIto hStop hY isOpen_simpleSet hYU (hmg k)
      (fun y hy => contDiffAt_stateFn hy q k) (fun y hy t => itoDrift_dysonState hy q k t)
      (fun y hy t => itoBracket_dysonState hy q k t) (hρ n) (hdom_single hG hFh hs hb1' q n k)
  -- pairs
  have hkl : ∀ n k l, HasMartingaleModification Q (shiftFiltration 𝓖 s)
      (stoppedProcess (locSq (Ypath N G F s) (fun y => stateFn N q k y + stateFn N q l y)
        (fun y => driftK N q k y + driftK N q l y)
        (fun y => covKL N q k k y + 2 * covKL N q k l y + covKL N q l l y))
        (dysonRho G F s n)) := fun n k l =>
    (localized_hasMM hIto hStop hY isOpen_simpleSet hYU ((hmg k).add (hmg l))
      (fun y hy => (contDiffAt_stateFn hy q k).add (contDiffAt_stateFn hy q l))
      (fun y hy t => itoDrift_dysonState_add hy q k l t)
      (fun y hy t => itoBracket_dysonState_add hy q k l t) (hρ n)
      (hdom_pair hG hFh hs hb1' q n k l)).2
  have hcomp : ∀ k, locComp (Ypath N G F s) (stateFn N q k) (driftK N q k) =
      smCompensated (Xpath N q G F s) (fun u ω => dysonStateDrift N (Xpath N q G F s u ω)) k := by
    intro k; funext t ω; exact locComp_stateFn hG hFh q s k t ω
  refine
    { adapted := fun t => ((measurable_dysonState q).comp
        (measurable_hermBM_add hG hF (s + t))).stronglyMeasurable
      progressive := ?_
      continuous := hb1'.mono fun ω hω => continuous_state_path hG hs hω q
      drift_progressive := ?_
      cov_progressive := ?_
      integrable := hb1'.mono fun ω hω t =>
        ⟨fun i => ((continuous_apply i).comp (continuous_drift_path hG hs hω q)).integrableOn_Ioc,
          fun i j => ((continuous_apply j).comp ((continuous_apply i).comp
            (continuous_cov_path hG hs hω q))).integrableOn_Ioc⟩
      localizing := ⟨dysonRho G F s, hρ, hb1'.mono fun ω hω => tendsto_dysonRho hG hs hω,
        fun n => ⟨fun k => ?_, fun k l => ?_⟩⟩ }
  · have e : (fun u ω => dysonState N q (F ω + G (s + u) ω)) =
        fun t ω => dysonState N q (vecHerm N (Ypath N G F s t ω)) := by
      funext t ω; rw [vecHerm_Ypath hG hFh]
    rw [e]
    exact IsStronglyProgressive.comp_measurable' hY.progressive hmS
  · have e : (fun u ω => dysonStateDrift N (dysonState N q (F ω + G (s + u) ω))) =
        fun t ω => dysonStateDrift N (dysonState N q (vecHerm N (Ypath N G F s t ω))) := by
      funext t ω; rw [vecHerm_Ypath hG hFh]
    rw [e]
    exact IsStronglyProgressive.comp_measurable' hY.progressive
      (measurable_dysonStateDrift.comp hmS)
  · have e : (fun u ω => dysonStateCov N (dysonState N q (F ω + G (s + u) ω))) =
        fun t ω => dysonStateCov N (dysonState N q (vecHerm N (Ypath N G F s t ω))) := by
      funext t ω; rw [vecHerm_Ypath hG hFh]
    rw [e]
    exact IsStronglyProgressive.comp_measurable' hY.progressive
      (measurable_dysonStateCov.comp hmS)
  · have h := (hk n k).1
    rw [hcomp k] at h
    exact h
  · have h := hasMM_const_mul (1 / 2 : ℝ) (hasMM_sub (hasMM_sub (hkl n k l) (hk n k).2) (hk n l).2)
    refine hasMM_congr h fun t => ?_
    filter_upwards [hb1'] with ω hω
    simp only [stoppedProcess]
    rw [← two_mul_target hG hFh hs hω q k l]
    set w := (min (t : WithTop ℝ≥0) (dysonRho G F s n ω)).untopA
    have e1 : ∀ j, smCompensated (fun u ω => dysonState N q (F ω + G (s + u) ω))
        (fun u ω => dysonStateDrift N (dysonState N q (F ω + G (s + u) ω))) j w ω =
        locComp (Ypath N G F s) (stateFn N q j) (driftK N q j) w ω := fun j =>
      (locComp_stateFn hG hFh q s j w ω).symm
    rw [e1, e1]
    simp only [covKL, vecHerm_Ypath hG hFh]
    ring

end BlockBand.SourceProcess.Stochastic.Dyson
