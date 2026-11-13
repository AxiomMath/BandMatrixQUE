module

public import BlockBand.SourceProcess.Stochastic.Bridges.NativeIto
public import BlockBand.SourceProcess.Stochastic.ItoNative.CoordRepBuild
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.MartingaleTools

/-!
# Closing stopped Itô processes in `L²`

For an Itô process `W` in `ℝ^d` and an augmented stopping time `τ` whose stopped coordinate
integrands `σ^i 1{s ≤ τ}` are integrands (`L²(dt ⊗ P)` on every horizon), the stopped
compensated coordinates and the stopped compensated products
`(N^i N^j - ∫ Σ_a σ_a^i σ_a^j)^τ` have martingale modifications (`hmm_coord`, `hmm_coord_pair`).
No bound on the process itself is needed: this is the `L²` closure of the `𝒦` martingales,
which are not bounded before the Gram trace stop. `exists_martingale_re_im` assembles a complex
martingale from real and imaginary modifications.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Integral BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.GramUniqueness

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]
  {d : ℕ}

/-- **Stopped compensated coordinate.** -/
theorem hmm_coord {W b : ℝ≥0 → DriverSample S κ → Fin d → ℝ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ} (hW : IsNativeItoProcess μ W b σ)
    {τ : DriverSample S κ → WithTop ℝ≥0} (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    (i : Fin d)
    (hG : ∀ T, NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand (coordFun i) σ))) :
    HasMartingaleModification (driverLaw (κ := κ) μ) (driverAugmented (κ := κ) μ)
      (stoppedProcess (smCompensated W b i) τ) :=
  hasMartingaleModification_of_raw fun T =>
    ⟨nativeAdaptedLimit μ T (hG T).family, nativeAdaptedLimit_martingale μ T _,
      fun _ hu => stoppedProcess_smCompensated_ae_eq hW hτ i (hG T) hu⟩

/-- **Stopped compensated product of two coordinates.** -/
theorem hmm_coord_pair {W b : ℝ≥0 → DriverSample S κ → Fin d → ℝ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ} (hW : IsNativeItoProcess μ W b σ)
    {τ : DriverSample S κ → WithTop ℝ≥0} (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    (i j : Fin d)
    (hGi : ∀ T, NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand (coordFun i) σ)))
    (hGj : ∀ T, NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand (coordFun j) σ))) :
    HasMartingaleModification (driverLaw (κ := κ) μ) (driverAugmented (κ := κ) μ)
      (stoppedProcess (fun t ω => smCompensated W b i t ω * smCompensated W b j t ω -
        ∫ s in Ioc (0 : ℝ) t, ∑ a, σ a s.toNNReal ω i * σ a s.toNNReal ω j) τ) := by
  refine hasMartingaleModification_of_raw fun T => ?_
  obtain ⟨N, hN, hNe⟩ := bracket_martingale (hGi T) (hGj T)
  exact ⟨N, hN, fun _ hu => stoppedProcess_bracket_ae_eq hW hτ i j (hGi T) (hGj T) hNe hu⟩

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem hmm_add {X Y : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X)
    (hY : HasMartingaleModification Q 𝓖 Y) :
    HasMartingaleModification Q 𝓖 (fun t ω => X t ω + Y t ω) := by
  obtain ⟨M, hM, e⟩ := hX
  obtain ⟨M', hM', e'⟩ := hY
  exact ⟨fun t ω => M t ω + M' t ω, hM.add hM', fun t => (e t).add (e' t)⟩

theorem hmm_sub {X Y : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X)
    (hY : HasMartingaleModification Q 𝓖 Y) :
    HasMartingaleModification Q 𝓖 (fun t ω => X t ω - Y t ω) := by
  obtain ⟨M, hM, e⟩ := hX
  obtain ⟨M', hM', e'⟩ := hY
  exact ⟨fun t ω => M t ω - M' t ω, hM.sub hM', fun t => (e t).sub (e' t)⟩

theorem hmm_congr {X Y : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X)
    (h : ∀ t, X t =ᵐ[Q] Y t) : HasMartingaleModification Q 𝓖 Y := by
  obtain ⟨M, hM, e⟩ := hX
  exact ⟨M, hM, fun t => (e t).trans (h t)⟩

/-- A complex martingale from martingale modifications of the real and imaginary parts. -/
theorem exists_martingale_re_im {F : ℝ≥0 → Ω → ℂ}
    (hre : HasMartingaleModification Q 𝓖 (fun t ω => (F t ω).re))
    (him : HasMartingaleModification Q 𝓖 (fun t ω => (F t ω).im)) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t, N t =ᵐ[Q] F t := by
  obtain ⟨M0, hM0, e0⟩ := hre
  obtain ⟨M1, hM1, e1⟩ := him
  refine ⟨fun t ω => Complex.ofRealCLM (M0 t ω) + (Complex.I • Complex.ofRealCLM) (M1 t ω),
    (martingale_clm hM0 _).add (martingale_clm hM1 _), fun t => ?_⟩
  filter_upwards [e0 t, e1 t] with ω h0 h1
  simp only [Complex.ofRealCLM_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    h0, h1]
  rw [mul_comm]
  exact Complex.re_add_im _

end BlockBand.SourceProcess.ComplexCoupled
