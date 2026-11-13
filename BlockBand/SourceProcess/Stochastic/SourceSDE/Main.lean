module
public import BlockBand.SourceProcess.Stochastic.SourceSDE.Preservation
public import BlockBand.SourceProcess.Stochastic.SourceSDE.TraceBound
public import BlockBand.SourceProcess.Stochastic.SourceSDE.GlobalAgree
public import BlockBand.SourceProcess.Stochastic.Assembly.NonexplosionMainU
public import BlockBand.SourceProcess.Stochastic.SDE.NativeWellPosed
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Well-posedness of the finite source equation

`finiteSourceWellPosed_holds : FiniteSourceWellPosed μ D₀ Naux P 𝖣` — the well-posedness part of
the finite Gram law — for every old-state space `S`, ambient index `ι`,
frame index `c` (arbitrary universes), probability `μ`, `D₀`, `Naux`, `P`, `𝖣`. Measure
`driverLaw μ = μ ⊗ Wiener^(SourceNoise ι)`; augmented filtration `F_t ∨ N`; Frobenius norm on
`Matrix ι c ℂ`; no integrability of `ξ`. Under `0 < D₀`, `IsNearProjection P Naux`,
`IsSignature 𝖣`, for every augmented-`F_0` initial frame `ξ` with `TwoProjection P 𝖣 ξ` a.s.:

1. **existence** of a global solution: nonexplosion (`nonexplosionFor_holdsU`, universe-
   polymorphic) with `K = {TwoProjection}` (closed: `defectLyapunov_eq_zero_iff`), invariance
   of `K` under exit-time solutions (`exitSolution_twoProjection`), and the Lyapunov function
   `‖V‖² = Tr M` with `𝓛‖V‖² ≤ C ‖V‖²` on `K` (`sdeGenerator_normSq_le`);
2. **pathwise uniqueness** of global solutions: local well-posedness (`localWellPosednessFor_holds`);
3. **projection preservation** for every global solution (`isSDESolution_twoProjection`): it
   agrees with the strong exit-time solutions of radii `n + 1` until their exit times
   (`ae_eq_strongExit_of_isSDESolution`), which keep the constraint
   (`ae_twoProjection_of_strongExit`), and these exit times increase to `⊤` along its continuous
   modification.
-/

namespace BlockBand.SourceProcess.Stochastic.SourceSDE
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal Topology
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

/-- **Clause (3): every global solution keeps the constraint at all times a.s.** -/
theorem isSDESolution_twoProjection {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hDH : Dᴴ = D)
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξ0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x))
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, TwoProjection P D (X t x) := by
  have hb := locallyLipschitz_sourceDrift (c := c) D0 Naux P
  have hσ := locallyLipschitz_sourceDiffusion D0 P D
  obtain ⟨X', hX'a, hX'c, hXX'⟩ := exists_continuous_modification hX.1.adapted hX.1.continuous
  choose Z hZ using fun n : ℕ =>
    exists_solutionUntil_exitTime_strong hb hσ hξ ((n + 1 : ℕ) : ℝ)
  have h1 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ n : ℕ,
      exitTime (Z n) ((n + 1 : ℕ) : ℝ) x = exitTimeOf X' ((n + 1 : ℕ) : ℝ) x ∧
        ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ exitTime (Z n) ((n + 1 : ℕ) : ℝ) x → X t x = Z n t x :=
    ae_all_iff.2 fun n =>
      ae_eq_strongExit_of_isSDESolution hb hσ (by positivity) hX (hZ n) hX'a hX'c hXX'
  have h2 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ n : ℕ, ∀ t, TwoProjection P D (Z n t x) :=
    ae_all_iff.2 fun n => ae_twoProjection_of_strongExit hD0 hP hDH hξ hξ0 (hZ n)
  filter_upwards [h1, h2] with x h1 h2 t
  have htop := (tendsto_exitTimeOf_top (hX'c x)).comp (tendsto_add_atTop_nat 1)
  obtain ⟨n, hn⟩ := ((WithTop.tendsto_nhds_top_iff _).1 htop t).exists
  have hn' : (t : WithTop ℝ≥0) ≤ exitTime (Z n) ((n + 1 : ℕ) : ℝ) x := by
    rw [(h1 n).1]
    exact hn.le
  rw [(h1 n).2 t hn']
  exact h2 n t

omit [DecidableEq ι] in
theorem isClosed_twoProjection {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} (hPH : Pᴴ = P)
    (hDH : Dᴴ = D) : IsClosed {V : Matrix ι c ℂ | TwoProjection P D V} := by
  have h : {V : Matrix ι c ℂ | TwoProjection P D V} = {V | defectLyapunov P D V = 0} :=
    Set.ext fun V => (defectLyapunov_eq_zero_iff hPH hDH V).symm
  rw [h]
  exact isClosed_eq (contDiff_defectLyapunov (k := 0) P D).continuous continuous_const

/-- **The finite source equation is well posed.** -/
theorem finiteSourceWellPosed_holds (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) :
    FiniteSourceWellPosed μ D0 Naux P D := by
  intro hD0 hP hD ξ hξ hξ0
  have hb := locallyLipschitz_sourceDrift (c := c) D0 Naux P
  have hσ := locallyLipschitz_sourceDiffusion D0 P D
  refine ⟨?_, fun X Y hX hY =>
      (localWellPosednessFor_holds (κ := SourceNoise ι) μ (Matrix ι c ℂ) _ _ hb hσ ξ hξ).2.2
        X Y hX hY,
    fun X hX => isSDESolution_twoProjection μ hD0.le hP hD.1 hξ hξ0 hX⟩
  set Cn : ℝ := Fintype.card (SourceNoise ι) * (Real.sqrt D0 / 2 * Naux) ^ 2
  have hCn : 0 ≤ Cn := by positivity
  refine nonexplosionFor_holdsU (κ := SourceNoise ι) μ (Matrix ι c ℂ) _ _ hb hσ ξ hξ
    {V | TwoProjection P D V} (isClosed_twoProjection hP.1 hD.1) hξ0
    (fun R X hX => exitSolution_twoProjection hD0.le hP hD.1 hξ hξ0 R X hX)
    (fun V => ‖V‖ ^ 2) Cn contDiff_normSq (fun y _ => sq_nonneg _) ?_ ?_
  · intro M
    refine ⟨max M 1, fun y _ hy => ?_⟩
    have h1 := le_max_left M 1
    have h2 := le_max_right M 1
    nlinarith
  · intro y hy
    refine le_trans (sdeGenerator_normSq_le hD0.le hP (show TwoProjection P D y from hy)) ?_
    change Cn * ‖y‖ ^ 2 ≤ Cn * (1 + ‖y‖ ^ 2)
    nlinarith [sq_nonneg ‖y‖]

end BlockBand.SourceProcess.Stochastic.SourceSDE
