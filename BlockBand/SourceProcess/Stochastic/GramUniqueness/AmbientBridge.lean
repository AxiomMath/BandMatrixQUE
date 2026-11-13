module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AmbientReal
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AmbientMP
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AmbientBound
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AmbientFeasible
public import BlockBand.SourceProcess.Stochastic.SourceSDE.Main
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankStepIto
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Bridge: the ambient Gram process solves the Gram martingale problem

`ambient_isGramMartingaleSolution`: for `0 < D₀`, `IsNearProjection P Naux`, a signature `𝖣`, an
augmented-`F₀` constrained initial frame and a global solution `X` of the finite source equation,
the
Gram process `t ↦ gramPair P (X_t)` is an `IsGramMartingaleSolution` on
`(driverLaw μ, driverAugmented μ)`.

* feasibility: the constraint at all times (by `FiniteSourceWellPosed`) and
  `gramFeasible_of_twoProjection`;
* martingale clauses: the real coordinates form a continuous semimartingale
  (`ambient_isContinuousSemimartingale`) with characteristics `gramRealDrift`, `gramRealCov` a.s.
  (`ambient_drift_eq`, `ambient_cov_eq`). Their compensated coordinates and products, stopped at
  the raw trace stop `ρ` (`= σ_K` a.s.), are dominated (`gram_stopped_bound`) and so have
  martingale modifications (`hasMM_mpCompensated_stopped`, `hasMM_mpBracket_stopped`). The complex
  Gram clauses are combinations `x₀ + i x₁` and `(B₀₀ − B₁₁) + i (B₀₁ + B₁₀)` of these
  (`mpCompensated_gramReal`, `mpBracket_gramReal`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic.SourceAlgebra
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

theorem complex_of_reIm (z : ℂ) :
    Complex.ofRealCLM (reImCLM 0 z) + (Complex.I • Complex.ofRealCLM) (reImCLM 1 z) = z := by
  apply Complex.ext <;> simp [reImCLM_apply, reIm]

theorem complex_of_realCov (z z' : ℂ) :
    Complex.ofRealCLM (realCovL 0 0 z + realCovL' 0 0 z' - (realCovL 1 1 z + realCovL' 1 1 z')) +
      (Complex.I • Complex.ofRealCLM) (realCovL 0 1 z + realCovL' 0 1 z' +
        (realCovL 1 0 z + realCovL' 1 0 z')) = z := by
  apply Complex.ext <;> simp [realCovL, realCovL'] <;> ring

/-- **The ambient Gram process is a feasible Gram martingale-problem solution.** -/
theorem ambient_isGramMartingaleSolution {D0 : ℝ} (hD0 : 0 < D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    (hP : IsNearProjection P Naux) {D : Matrix c c ℂ} (hD : IsSignature D)
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξm : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξc : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x))
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X) :
    IsGramMartingaleSolution (driverLaw (κ := SourceNoise ι) μ)
      (driverAugmented (κ := SourceNoise ι) μ) D0 D (fun t x => gramPair P (X t x)) := by
  have hcon := (SourceSDE.finiteSourceWellPosed_holds μ D0 Naux P D hD0 hP hD ξ hξm hξc).2.2 X hX
  set G : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c c ℂ × Matrix c c ℂ :=
    fun t x => gramPair P (X t x) with hGdef
  set Y : ℝ≥0 → DriverSample S (SourceNoise ι) → Fin (gramDim c) → ℝ :=
    fun t x => toGramReal (G t x) with hYdef
  have hS := ambient_isContinuousSemimartingale μ hX
  have hGn := GramChar.gramPair_nativeIto μ hX
  have hβ : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t,
      toGramReal (gramDrift D0 Naux P D (X t x)) = gramRealDrift D0 D (Y t x) := by
    filter_upwards [hcon] with x h t
    exact ambient_drift_eq hD0.le hP (h t)
  have hα : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t,
      (Matrix.of fun i j => ∑ a, toGramReal (gramNoise D0 P D a (X t x)) i *
        toGramReal (gramNoise D0 P D a (X t x)) j) = gramRealCov D0 D (Y t x) := by
    filter_upwards [hcon] with x h t
    exact ambient_cov_eq hD0.le hP hD (h t)
  have hgood : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      (Continuous fun t => G t x) ∧ ∀ t, GramFeasible D (G t x) := by
    filter_upwards [hGn.continuous, hcon] with x hc h
    exact ⟨hc, fun t => gramFeasible_of_twoProjection hP.1 hP.2.1 (h t)⟩
  have hYm : ∀ t, Measurable[driverAugmented (κ := SourceNoise ι) μ t] (Y t) := fun t =>
    (hS.adapted t).measurable
  have hρ : ∀ K : ℝ, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (rawHit (traceSuperLevel K) Y) := fun K => isStoppingTime_rawHit hYm
  have hρσ : ∀ K : ℝ, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      rawHit (traceSuperLevel K) Y x = gramTraceStop G K x := fun K => by
    filter_upwards [hgood] with x h
    rw [rawHit_eq_hitTime (Y := Y) (isClosed_traceSuperLevel K) (continuous_toGramReal.comp h.1)]
    exact hitTime_traceSuperLevel G K x
  have hbd : ∀ (K : ℝ) (i j : Fin (gramDim c)) (t : ℝ≥0), ∃ C, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      ∀ s ≤ t, |stoppedProcess (mpCompensated (gramRealDrift D0 D) Y i)
        (rawHit (traceSuperLevel K) Y) s x| ≤ C ∧
      |stoppedProcess (mpBracketProc D0 D Y i j) (rawHit (traceSuperLevel K) Y) s x| ≤ C := by
    intro K i j t
    obtain ⟨C, hC⟩ := gram_stopped_bound (DriverSample S (SourceNoise ι)) D0 D K t i j
    refine ⟨C, ?_⟩
    filter_upwards [hρσ K, hgood] with x hr h s hs
    simp only [stoppedProcess_eq_stopTime, hr]
    exact hC G x h.1 h.2 s hs
  have hdr : ∀ (K : ℝ) (i : Fin (gramDim c)), HasMartingaleModification
      (driverLaw (κ := SourceNoise ι) μ) (driverAugmented (κ := SourceNoise ι) μ)
      (stoppedProcess (mpCompensated (gramRealDrift D0 D) Y i) (rawHit (traceSuperLevel K) Y)) :=
    fun K i => hasMM_mpCompensated_stopped hS hβ (continuous_gramRealDrift D0 D) (hρ K) i
      fun t => by
        obtain ⟨C, hC⟩ := hbd K i i t
        exact ⟨C, by filter_upwards [hC] with x h s hs; exact (h s hs).1⟩
  have hbr : ∀ (K : ℝ) (i j : Fin (gramDim c)), HasMartingaleModification
      (driverLaw (κ := SourceNoise ι) μ) (driverAugmented (κ := SourceNoise ι) μ)
      (stoppedProcess (mpBracketProc D0 D Y i j) (rawHit (traceSuperLevel K) Y)) :=
    fun K i j => hasMM_mpBracket_stopped hS hβ hα (continuous_gramRealDrift D0 D)
      (continuous_gramRealCov D0 D) (hρ K) i j fun t => by
        obtain ⟨C, hC⟩ := hbd K i j t
        exact ⟨C, by filter_upwards [hC] with x h s hs; exact (h s hs).2⟩
  refine ⟨hGn.adapted, hGn.continuous, ?_, fun K e => ?_, fun K e e' => ?_⟩
  · filter_upwards [hgood] with x h
    exact h.2
  · obtain ⟨M0, hM0, hM0X⟩ := hdr K (gramRealEquiv c (e, 0))
    obtain ⟨M1, hM1, hM1X⟩ := hdr K (gramRealEquiv c (e, 1))
    refine ⟨fun t x => Complex.ofRealCLM (M0 t x) + (Complex.I • Complex.ofRealCLM) (M1 t x),
      (martingale_clm hM0 _).add (martingale_clm hM1 _), fun t => ?_⟩
    filter_upwards [hM0X t, hM1X t, hρσ K, hgood] with x h0 h1 hr hg
    rw [h0, h1]
    simp only [stoppedProcess_eq_stopTime, hr]
    rw [hYdef]
    simp only [mpCompensated_gramReal hg.1, qi, Equiv.symm_apply_apply]
    exact complex_of_reIm _
  · have hM := fun r r' => hbr K (gramRealEquiv c (e, r)) (gramRealEquiv c (e', r'))
    obtain ⟨M00, hM00, hM00X⟩ := hM 0 0
    obtain ⟨M01, hM01, hM01X⟩ := hM 0 1
    obtain ⟨M10, hM10, hM10X⟩ := hM 1 0
    obtain ⟨M11, hM11, hM11X⟩ := hM 1 1
    refine ⟨fun t x => Complex.ofRealCLM (M00 t x - M11 t x) +
      (Complex.I • Complex.ofRealCLM) (M01 t x + M10 t x),
      (martingale_clm (hM00.sub hM11) _).add (martingale_clm (hM01.add hM10) _), fun t => ?_⟩
    filter_upwards [hM00X t, hM01X t, hM10X t, hM11X t, hρσ K, hgood] with x h00 h01 h10 h11 hr hg
    rw [h00, h01, h10, h11]
    have hf : ∀ s, (G s x).1ᴴ = (G s x).1 ∧ (G s x).2ᴴ = (G s x).2 := fun s =>
      herm_of_feasible (hg.2 s)
    simp only [stoppedProcess_eq_stopTime, hr, mpBracketProc]
    rw [hYdef]
    simp only [mpBracket_gramReal hD.1 hg.1 hf, qi, Equiv.symm_apply_apply]
    exact complex_of_realCov _ _

end BlockBand.SourceProcess.Stochastic.GramUniqueness
