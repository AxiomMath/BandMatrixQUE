module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.TGlobal
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Global solutions are Itô processes, time-dependent coefficients

`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`, `c : TLipCoeff κ E`.

`TGlobalSol.isNativeItoProcess`: a global solution (`TGlobalSol`) is an Itô process
(`IsNativeItoProcess`) with drift `t, x ↦ b(t, X_t x)` and diffusion `t, x ↦ σ_a(t, X_t x)`.
The localizing sequence is the constant `⊤`: the stopped diffusion functionals are bounded,
hence integrands (`nativeIntegrand_coeff_stopped`).

`exists_isNativeItoProcess_tcoeff`: for every `F_0 ∨ N`-measurable `ξ` such a process exists,
with everywhere continuous paths and `X_0 = ξ` everywhere.
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.NativeSDE

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [IsProbabilityMeasure μ] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A jointly continuous time-dependent coefficient of a progressive process is progressive. -/
theorem isStronglyProgressive_coeff {f : ℝ≥0 → E → E}
    (hf : Continuous fun q : ℝ≥0 × E => f q.1 q.2) {X : ℝ≥0 → DriverSample S κ → E}
    (hX : IsStronglyProgressive (driverAugmented (κ := κ) μ) X) :
    IsStronglyProgressive (driverAugmented (κ := κ) μ) fun t x => f t (X t x) := fun i =>
  hf.comp_stronglyMeasurable
    (((measurable_subtype_coe.comp measurable_fst).stronglyMeasurable).prodMk (hX i))

/-- Stopped bounded coefficient functionals are integrands. -/
theorem nativeIntegrand_coeff_stopped {σ : κ → ℝ≥0 → E → E}
    (hσ : ∀ a, Continuous fun q : ℝ≥0 × E => σ a q.1 q.2) {C : ℝ}
    (hC : ∀ a t y, ‖σ a t y‖ ≤ C) {X : ℝ≥0 → DriverSample S κ → E}
    (hXa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t))
    (hXc : ∀ x, Continuous fun t => X t x) (ℓ : E →L[ℝ] ℝ) (T : ℝ≥0) :
    NativeIntegrand μ T (stopIntegrand (fun _ => ⊤)
      (functionalIntegrand ℓ fun a t x => σ a t (X t x))) := by
  intro a
  have hm : AEStronglyMeasurable[rawPredictable S κ]
      (fun p : ℝ × DriverSample S κ => ℓ (σ a p.1.toNNReal (X p.1.toNNReal p.2)))
      (timeProbMeasure T (driverLaw (κ := κ) μ)) :=
    ℓ.continuous.comp_aestronglyMeasurable
      (aesm_coeff_comp (hσ a) (aesm_processFun hXa (Eventually.of_forall hXc)))
  have he : stopIntegrand (fun _ => ⊤) (functionalIntegrand ℓ fun a t x => σ a t (X t x)) a =
      fun p : ℝ × DriverSample S κ => ℓ (σ a p.1.toNNReal (X p.1.toNNReal p.2)) := by
    funext p
    simp only [stopIntegrand, le_top, ite_true, functionalIntegrand]
  rw [he]
  refine ⟨hm, MemLp.of_bound (hm.mono (predictableSpace_le _)) (‖ℓ‖ * C)
    (Eventually.of_forall fun p => ?_)⟩
  exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC a _ _) (norm_nonneg _))

/-- **Global solutions are Itô processes.** -/
theorem TGlobalSol.isNativeItoProcess {c : TLipCoeff κ E} {ξ : DriverSample S κ → E}
    {X : ℝ≥0 → DriverSample S κ → E} (hX : TGlobalSol μ c ξ X) :
    IsNativeItoProcess μ X (fun t x => c.b t (X t x)) (fun a t x => c.σ a t (X t x)) := by
  obtain ⟨hXa, hXc, -, hXid⟩ := hX
  have hprog : IsStronglyProgressive (driverAugmented (κ := κ) μ) X :=
    StronglyAdapted.isStronglyProgressive_of_continuous hXa hXc
  refine ⟨hXa, hprog, Eventually.of_forall hXc, isStronglyProgressive_coeff c.cont_b hprog,
    fun a => isStronglyProgressive_coeff (c.cont_σ a) hprog, ?_, ?_, ?_⟩
  · refine Eventually.of_forall fun x t => ?_
    refine Integrable.mono' (g := fun _ => c.C) (integrableOn_const (by simp))
      (aesm_coeff_path c.cont_b (hXc x) _) (Eventually.of_forall fun s => c.bd_b _ _)
  · exact ⟨fun _ _ => ⊤, fun _ => isStoppingTime_top, Eventually.of_forall fun _ =>
      tendsto_const_nhds, fun _ ℓ T => nativeIntegrand_coeff_stopped c.cont_σ c.bd_σ hXa hXc ℓ T⟩
  · intro ℓ τ hτ T _ t ht
    exact hXid T τ hτ ℓ t ht

/-- **Existence** of an Itô process solving the time-dependent equation. -/
theorem exists_isNativeItoProcess_tcoeff [MeasurableSpace E] [BorelSpace E] (c : TLipCoeff κ E) {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) :
    ∃ X : ℝ≥0 → DriverSample S κ → E,
      IsNativeItoProcess μ X (fun t x => c.b t (X t x)) (fun a t x => c.σ a t (X t x)) ∧
      (∀ x, Continuous fun t => X t x) ∧ ∀ x, X 0 x = ξ x := by
  obtain ⟨X, hX⟩ := exists_tGlobalSol c hξ
  exact ⟨X, hX.isNativeItoProcess, hX.2.1, hX.2.2.1⟩

end BlockBand.SourceProcess.Stochastic.RotationFlow
