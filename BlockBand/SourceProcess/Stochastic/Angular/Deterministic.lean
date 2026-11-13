module

public import BlockBand.SourceProcess.Stochastic.Angular.Regularity

/-!
# Complex angular martingale problem: deterministic tests

`deterministicAngular_of : ArrayLaplacian N r → GenericConditioning N →
DeterministicAngular N r`. On the a.s. event where `H_{s+v}` has simple spectrum for every
`v`, the stopped variable of the martingale problem for any selection `ev` equals `coordVar` for
the scalar `φ = arrayFn V f₀` and the density `A = arrGen V f₀` *for every* such `ω` (selection
independence of the test, `phaseInv_ev`, and of the generator, `complexAngularGenerator_ev`).
The hypotheses of `GenericConditioning` are the regularity and bounds of `arrayFn` and the
Laplacian identity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory Filter Topology Matrix Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

variable {N r : ℕ}

theorem hermVec_mem_simpleSet' {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) : hermVec N H ∈ simpleSet N := by
  show HasSimpleSpectrum N (vecHerm N (hermVec N H)); rwa [vecHerm_hermVec hH]

/-- At a simple Hermitian `H`, the test and the generator along any selection are the
coordinate functions `arrayFn`, `arrGen`. -/
theorem arrayFn_hermVec {f₀ : AngularArray N r → ℝ} (hp : IsPhaseInvariant f₀)
    (V : Matrix (Fin N) (Fin r) ℂ) {ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ}
    (hev : IsEigenSelection N ev) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) :
    f₀ (angularArray V (ev H)) = arrayFn V f₀ (hermVec N H) ∧
      complexAngularGenerator N r (dysonEigenvalue N H) f₀ (angularArray V (ev H)) =
        arrGen V f₀ (hermVec N H) := by
  have hy := hermVec_mem_simpleSet' hH hs
  have hZ : arrZ V (hermVec N H) = angularArray V (canonEv N H) := by
    rw [arrZ, vecHerm_hermVec hH]
  have hlam : (fun i => lam N i (hermVec N H)) = dysonEigenvalue N H := by
    funext i; simp only [lam, vecHerm_hermVec hH]
  refine ⟨?_, ?_⟩
  · rw [arrayFn_of_mem hy, hZ]
    exact phaseInv_ev hp hev (isEigenSelection_canonEv N) hH hs V
  · rw [arrGen_of_mem hy, hZ, hlam]
    exact complexAngularGenerator_ev hp _ hev (isEigenSelection_canonEv N) hH hs V

/-- **Deterministic tests from `ArrayLaplacian` and `GenericConditioning`.** -/
theorem deterministicAngular_of (hL : ArrayLaplacian N r) (hC : GenericConditioning N) :
    DeterministicAngular N r := by
  intro Ω _ Q _ 𝓖 G F hG hF hFh ev hev s hsimple V n hn f₀ hf hp u
  have hherm : ∀ t ω, (F ω + G t ω).IsHermitian := fun t ω => (hFh ω).add (hG.hermitian t ω)
  obtain ⟨hI, hS⟩ := hC Ω Q 𝓖 G F hG hF hFh s hsimple n hn (arrayFn V f₀) (arrGen V f₀)
    (measurable_arrayFn hf hp) (fun y hy => contDiffAt_arrayFn hf hp hy)
    (measurable_arrGen hf hp) (continuousOn_arrGen hf hp)
    (fun y hy => (hL V f₀ hf hp y hy).1) (fun y hy => (hL V f₀ hf hp y hy).2)
    (abs_arrayFn_le hf) (abs_arrGen_le hf hn) u
  have heq : angVar F G ev s V n (fun _ => f₀) u =ᵐ[Q] coordVar F G s n (arrayFn V f₀)
      (arrGen V f₀) u := by
    filter_upwards [hsimple] with ω hω
    have hpt := fun v => arrayFn_hermVec hp V hev (hherm (s + v) ω) (hω v)
    simp only [angVar, coordVar, stoppedProcess]
    rw [(hpt _).1, (hpt 0).1]
    congr 2
    funext w
    exact (hpt _).2
  refine ⟨hI.congr heq.symm, fun S hSm => ?_⟩
  rw [integral_congr_ae (ae_restrict_of_ae heq)]
  exact hS S hSm

end BlockBand.SourceProcess.Stochastic.ComplexAngular
