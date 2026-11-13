module

public import BlockBand.SourceProcess.ComplexConstruct.KAmbEsc
public import BlockBand.SourceProcess.ComplexConstruct.KInt
public import BlockBand.SourceProcess.ComplexUnique.NoiseLip
public import BlockBand.SourceProcess.CoupledFrames.NativeCongr
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionGlue

/-!
# The ambient `𝒦` noise integral exists

`ambientKIntegral_holds : AmbientKIntegral`. Proof:
* the joint equation for `(X, 𝒴)` on `Matrix ι c' ℂ × Matrix c' c' ℂ` with coefficients
  `(sourceDrift, 0)` and `(sourceDiffusion_a, kNoise_a)` (`jb`, `jσ`), locally Lipschitz
  (`locallyLipschitz_sourceDrift`, `locallyLipschitz_sourceDiffusion`, `contDiff_kNoise`), has strong
  exit-time solutions of every radius (`exists_solutionUntil_exitTime_strong`);
* they escape (`ae_escape`), so `exists_isSDESolution_of_family` glues a global solution `W`;
* the frame part of `W` is a global solution of the frame equation, hence equal to `X`
  (`ae_eq_of_isSDESolution`); the noise part is an Itô process with drift `0` and
  diffusion `kNoise(W.1) = kNoise(X)` a.s. (`isNativeItoProcess_congr_coeff`);
* it is set to `0` off a full `𝓖₀`-measurable set where `W₀ = (ξ, 0)`
  (`isNativeItoProcess_congr_proc`), so that `𝒴₀ = 0` everywhere.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.ComplexUnique
open BlockBand.SourceProcess.Stochastic.SourceSDE BlockBand.SourceProcess.CoupledFrames

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace

/-- **`AmbientKIntegral` holds.** -/
theorem ambientKIntegral_holds : AmbientKIntegral := by
  intro b E _ _ _ _ S _ μ _ ι c' _ _ _ _ Naux P D' _ _ ξ hξ _ X hX
  classical
  set D0 := transportD0 b E
  set η := etaZ b E
  have hb := locallyLipschitz_sourceDrift (c := c') D0 Naux P
  have hσ := locallyLipschitz_sourceDiffusion D0 P D'
  have hk : ∀ a, LocallyLipschitz (fun V : Matrix ι c' ℂ => kNoise D0 η P D' a V) := fun a =>
    (contDiff_kNoise D0 η P D' a (k := 1)).locallyLipschitz
  have hξJ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0]
      (fun x => (ξ x, (0 : Matrix c' c' ℂ))) := hξ.prodMk stronglyMeasurable_const
  choose Z hZ using fun n : ℕ => exists_solutionUntil_exitTime_strong (μ := μ)
    (locallyLipschitz_jb (E₂ := Matrix c' c' ℂ) hb) (locallyLipschitz_jσ hσ hk) hξJ (n : ℝ)
  obtain ⟨X', hX'a, hX'c, hXX'⟩ := exists_continuous_modification hX.1.adapted hX.1.continuous
  have hesc := ae_escape hb hσ (fun a => (hk a).continuous) hX hX'a hX'c hXX' hZ
  obtain ⟨W, hW⟩ := exists_isSDESolution_of_family (locallyLipschitz_jb hb)
    (locallyLipschitz_jσ hσ hk) hξJ hZ hesc
  have hW1 : IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D') ξ
      (fun t x => (W t x).1) := ⟨fst_nativeIto hW.1, hW.2.mono fun x hx => by simp only [hx]⟩
  have hEq := ae_eq_of_isSDESolution hb hσ hW1 hX
  have hY0 : IsNativeItoProcess μ (fun t x => (W t x).2) (fun _ _ => 0)
      (fun a t x => kNoise D0 η P D' a (X t x)) :=
    isNativeItoProcess_congr_coeff (snd_nativeIto hW.1) (m := 0) (θ := Fin.elim0)
      (fun i => i.elim0) (isStronglyProgressive_const _ _)
      (fun a T => (hk a).continuous.comp_stronglyMeasurable (hX.1.progressive T)) (by
        filter_upwards [hEq] with x hx t _
        exact ⟨rfl, fun a => by simp only [switchOff, le_top, ite_true, hx t]⟩)
  obtain ⟨G, hGm, hG0, hG⟩ := exists_good_set (μ := μ) hW.2
  have hGt : ∀ t, MeasurableSet[driverAugmented (κ := SourceNoise ι) μ t] G :=
    measurableSet_aug_of_full μ hGm hG0
  have hGae : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, x ∈ G := by
    rw [ae_iff]; simpa only [compl_def] using hG0
  refine ⟨fun t x => G.indicator (fun x => (W t x).2) x,
    isNativeItoProcess_congr_proc hY0 (fun t => (hY0.adapted t).indicator (hGt t)) (fun T => ?_)
      (by filter_upwards [hGae] with x hx t; exact indicator_of_mem hx _), fun x => ?_⟩
  · have h := (hY0.progressive T).indicator (s := univ ×ˢ G) (MeasurableSet.univ.prod (hGt T))
    convert h using 1
    funext p
    simp only [indicator, mem_prod, mem_univ, true_and]
  · by_cases hx : x ∈ G
    · simp only [indicator_of_mem hx, hG x hx]
    · exact indicator_of_notMem hx _

end BlockBand.SourceProcess.ComplexConstruct
