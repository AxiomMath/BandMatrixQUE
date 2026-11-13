module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeGlobalSol
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Time-dependent Picard map

Time-inhomogeneous version of the Picard map. `Ω = DriverSample S κ`,
`P = driverLaw μ`, horizon `N`, `ν = timeProbMeasure N P`, augmented filtration `F_t ∨ N`.
Coefficients `b(t, y)`, `σ_a(t, y)` (`TLipCoeff`) are jointly continuous in `(t, y)`,
`K`-Lipschitz in `y` uniformly in `t` and bounded by `C`. The Picard space is the one of the
homogeneous theory (`NativeSDE.PicardSpace`).

For `Z` in the Picard space (thought of as `X − ξ`):
* drift `D_Z(t) = ∫_0^{t∧N} b(s, ξ + Z_s) ds` (`tPicardDrift`);
* noise `M_Z^j = ∫ ℓ_j(σ(s, ξ + Z_s)) dW` (`tPicardNoise`, the continuous stopped integral);
* the Picard process `D_Z + ∑_j M_Z^j e_j` (`tPicardProc`).

The only new measurability input is that the clock `(s, x) ↦ s` is a.e. raw predictable
(`aesm_clock`), obtained from `aesm_processFun` for the deterministic process `t ↦ t`.
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.NativeSDE

/-- Time-dependent coefficients: jointly continuous, uniformly Lipschitz in space, bounded. -/
structure TLipCoeff (κ E : Type*) [NormedAddCommGroup E] where
  b : ℝ≥0 → E → E
  σ : κ → ℝ≥0 → E → E
  K : ℝ≥0
  C : ℝ
  cont_b : Continuous fun q : ℝ≥0 × E => b q.1 q.2
  cont_σ : ∀ a, Continuous fun q : ℝ≥0 × E => σ a q.1 q.2
  lip_b : ∀ t, LipschitzWith K (b t)
  lip_σ : ∀ a t, LipschitzWith K (σ a t)
  bd_b : ∀ t y, ‖b t y‖ ≤ C
  bd_σ : ∀ a t y, ‖σ a t y‖ ≤ C

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The clock `(s, x) ↦ s⁺` is a.e. raw predictable on `ν`. -/
theorem aesm_clock {N : ℝ≥0} :
    AEStronglyMeasurable[rawPredictable S κ] (fun p : ℝ × DriverSample S κ => p.1.toNNReal)
      (timeProbMeasure N (driverLaw (κ := κ) μ)) := by
  have h := aesm_processFun (S := S) (κ := κ) (μ := μ) (T := N) (E := ℝ) (Y := fun t _ => (t : ℝ))
    (fun _ => stronglyMeasurable_const) (Eventually.of_forall fun _ => NNReal.continuous_coe)
  have h2 := continuous_real_toNNReal.comp_aestronglyMeasurable h
  refine h2.congr (Eventually.of_forall fun p => ?_)
  simp only [Real.toNNReal_coe]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Composition of a jointly continuous coefficient with the clock and an a.e. raw
predictable function. -/
theorem aesm_coeff_comp {N : ℝ≥0} {f : ℝ≥0 → E → E} (hf : Continuous fun q : ℝ≥0 × E => f q.1 q.2)
    {g : ℝ × DriverSample S κ → E}
    (hg : AEStronglyMeasurable[rawPredictable S κ] g (timeProbMeasure N (driverLaw (κ := κ) μ))) :
    AEStronglyMeasurable[rawPredictable S κ] (fun p => f p.1.toNNReal (g p))
      (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
  hf.comp_aestronglyMeasurable (aesm_clock.prodMk hg)

/-- Drift of the Picard map, clamped at the horizon. -/
def tPicardDrift (c : TLipCoeff κ E) {N : ℝ≥0} (ξ : DriverSample S κ → E)
    (Z : PicardSpace (κ := κ) μ N E) (t : ℝ≥0) (x : DriverSample S κ) : E :=
  ∫ s in Ioc (0 : ℝ) ((min t N : ℝ≥0) : ℝ), c.b s.toNNReal (ξ x + rep Z (s, x))

/-- Noise integrands of the Picard map (coordinate `j`). -/
def tPicardNoiseFun (c : TLipCoeff κ E) {N : ℝ≥0} (ξ : DriverSample S κ → E)
    (Z : PicardSpace (κ := κ) μ N E) (j : Fin (Module.finrank ℝ E)) :
    κ → ℝ × DriverSample S κ → ℝ :=
  fun a p => coordCLM E j (c.σ a p.1.toNNReal (ξ p.2 + rep Z p))

omit [MeasurableSpace E] [BorelSpace E] in
theorem nativeIntegrand_tPicardNoiseFun (c : TLipCoeff κ E) {N : ℝ≥0}
    {ξ : DriverSample S κ → E} (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ)
    (Z : PicardSpace (κ := κ) μ N E) (j : Fin (Module.finrank ℝ E)) :
    NativeIntegrand μ N (tPicardNoiseFun c ξ Z j) := by
  intro a
  have hm : AEStronglyMeasurable[rawPredictable S κ] (tPicardNoiseFun c ξ Z j a)
      (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
    (coordCLM E j).continuous.comp_aestronglyMeasurable
      (aesm_coeff_comp (c.cont_σ a) ((aesm_initial (N := N) hξ).add (aesm_rep Z)))
  refine ⟨hm, MemLp.of_bound (hm.mono (predictableSpace_le _)) (‖coordCLM E j‖ * c.C)
    (Eventually.of_forall fun p => ?_)⟩
  exact ((coordCLM E j).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (c.bd_σ a _ _) (norm_nonneg _))

/-- Noise processes of the Picard map (the continuous stochastic integrals). -/
def tPicardNoise (c : TLipCoeff κ E) {N : ℝ≥0} {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) (Z : PicardSpace (κ := κ) μ N E)
    (j : Fin (Module.finrank ℝ E)) : ℝ≥0 → DriverSample S κ → ℝ :=
  nativeAdaptedLimit μ N (nativeIntegrand_tPicardNoiseFun c hξ Z j).family

/-- The Picard process `D_Z + ∑_j M_Z^j e_j`. -/
def tPicardProc (c : TLipCoeff κ E) {N : ℝ≥0} {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) (Z : PicardSpace (κ := κ) μ N E)
    (t : ℝ≥0) (x : DriverSample S κ) : E :=
  tPicardDrift c ξ Z t x + ∑ j, tPicardNoise c hξ Z j t x • Module.finBasis ℝ E j

end BlockBand.SourceProcess.Stochastic.RotationFlow
