module

public import BlockBand.SourceProcess.Stochastic.Angular.CondInst
public import BlockBand.SourceProcess.Stochastic.Angular.Degenerate
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularMain

/-!
# Complex angular martingale problem: `GenericConditioning N` for `0 < N`

* **`genericConditioning (hN : 0 < N) : GenericConditioning N`**. The variable `coordVar` is
  `Ms_u - Ms_0` with `Ms = Mc^{σ_n}` (`coordVar_eq_Dq`). Integrability and orthogonality to
  `𝓖_s ⊔ σ(W)` come from `CondHyp.ohyp` and the orthogonality chain (`OHyp.integrable_D`,
  `OHyp.orth_sigma`). Every set of `𝓖_s ⊔ eigenPathSigma` is a.e. equal to a set of
  `𝓖_s ⊔ σ(W)` (`CondHyp.aesm_lam`), and `integral_mul_eq_zero_of_aeClosure` finishes.
* **`complexAngularContract_holds : ComplexAngularContract`**: the complex angular martingale
  problem for all `N, r`, from `complexAngularContract_of_pos` (which needs
  `GenericConditioning N` only for `0 < N`; `GenericConditioning 0` is false).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Dyson BlockBand.SourceProcess.Stochastic.Dyson.Angular
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stopTime_zero
  stoppedProcess_eq_stopTime)

variable {N : ℕ}

/-- `coordVar` is the increment `Ms_u - Ms_0` of `Ms = Mc^{σ_n}`. -/
theorem coordVar_eq_Dq {Ω : Type} (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (n : ℕ) (φ A : (Fin (N * N) → ℝ) → ℝ)
    (u : ℝ≥0) :
    coordVar F G s n φ A u = Dq (stoppedProcess (Mc φ A G F s) (sig N G F s n)) u := by
  funext ω
  simp only [coordVar, Dq, stoppedProcess_eq_stopTime, Mc, ycd, stopTime_zero,
    NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure, sub_zero]
  ring

/-- **`GenericConditioning N` holds for every `0 < N`.** -/
theorem genericConditioning (hN : 0 < N) : GenericConditioning N := by
  intro Ω _ Q _ 𝓖 G F hG hF hFh s hs n hn φ A hφm hφ hAm hA hΔ hx hφb hAb u
  have H : CondHyp Q 𝓖 G F s n φ A :=
    ⟨hN, hG, hF, hFh, hs, hn, hφm, hφ, hAm, hA, hΔ, hx, hφb, hAb⟩
  have HO := H.ohyp
  rw [coordVar_eq_Dq]
  refine ⟨HO.integrable_D u, fun S hS => ?_⟩
  have hlam : ∀ v : ℝ≥0, Measurable fun ω => dysonEigenvalue N (F ω + G (s + v) ω) := fun v =>
    (measurable_pi_iff.2 fun i => measurable_dysonEigenvalue i).comp
      ((measurable_hermBM_add hG hF (s + v)).mono ((𝓖).le (s + v)) le_rfl)
  have h0 : 𝓖 s ≤ aeClosure inferInstance (sigB (shiftFiltration 𝓖 s 0) (Yst N 0 G F s)) Q :=
    fun T hT => ⟨𝓖.le s T hT, T, (le_sup_left : (shiftFiltration 𝓖 s 0 : MeasurableSpace Ω) ≤
      sigB (shiftFiltration 𝓖 s 0) (Yst N 0 G F s)) T
      (show MeasurableSet[𝓖 (s + 0)] T by rwa [add_zero]), EventuallyEq.rfl⟩
  have hsig : 𝓖 s ⊔ eigenPathSigma N F G s ≤
      aeClosure inferInstance (sigB (shiftFiltration 𝓖 s 0) (Yst N 0 G F s)) Q :=
    sup_le h0 (iSup_le fun v => comap_le_aeClosure (hlam v) (H.aesm_lam v))
  have hSm : MeasurableSet S :=
    (sup_le (𝓖.le s) (iSup_le fun v => (hlam v).comap_le)) S hS
  have hΛ : StronglyMeasurable[aeClosure inferInstance
      (sigB (shiftFiltration 𝓖 s 0) (Yst N 0 G F s)) Q] (S.indicator fun _ => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator (hsig S hS)
  have K := integral_mul_eq_zero_of_aeClosure (HO.integrable_D u)
    (fun S' hS' => HO.orth_sigma u hS') hΛ (C := 1) (fun ω => by
      by_cases h : ω ∈ S <;> simp [h])
  rw [← integral_indicator hSm, ← K]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  by_cases h : ω ∈ S <;> simp [h]

/-- **The complex angular martingale problem**, unconditionally. -/
theorem complexAngularContract_holds : ComplexAngularContract :=
  complexAngularContract_of_pos fun _ hN => genericConditioning hN

end BlockBand.SourceProcess.Stochastic.ComplexAngular
