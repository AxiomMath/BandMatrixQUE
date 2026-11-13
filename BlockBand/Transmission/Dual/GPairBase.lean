module

public import BlockBand.Transmission.Dual.GPairCoord
public import BlockBand.Transmission.Dual.GReindex
public import BlockBand.Transmission.Dual.ExistsSDE
public import BlockBand.Transmission.Dual.GLemma1Mart
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionHolds
public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblemConverse

/-!
# The pair base process

On the driver space `Ω₁` (law `P₁`, augmented filtration `𝓖₁`), for `D₀ > 0` and any
start `z` with `0 < z₀`, `0 < z₁ < 1`:
* `exists_pairBase_sde`: the `(u, v)`-SDE `(uvBaseDrift, uvDiff)` from `fromFlat z` has a
  **global** solution (`nonexplosionFor_holds` with `lyapBase`);
* `isCSM_pairBase`: its image `toFlat ∘ X` is a continuous semimartingale with the flat base
  characteristics `(flatBaseDrift D₀ 1, flatDiff D₀ 1)` (Itô for `toFlat`);
* `isMPSolutionOn_pairBase`: hence it solves the flat base martingale problem on all of
  `ℝ²` (semimartingale ⇒ martingale problem), stays in the flat chamber `𝒞₁` at every
  time and `ω`, and starts at `z` almost surely;
* `pairPath`: the indistinguishable version that is the constant `z` off a null set of the
  augmented `𝓖₁ 0`, so that it is continuous and starts at `z` at **every** `ω`
  (`isMPSolutionOn_pairPath`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {D0 : ℝ}

/-- **Global existence** for the pair base SDE in `(u, v)` coordinates. -/
theorem exists_pairBase_sde (hD0 : 0 < D0) (z : Fin 2 → ℝ) :
    ∃ X : ℝ≥0 → Ω₁ → Fin 2 → ℝ,
      IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X :=
  nonexplosionFor_holds μ₁ (Fin 2 → ℝ) (uvBaseDrift D0) (uvDiff D0)
    (locallyLipschitz_uvBaseDrift D0) (locallyLipschitz_uvDiff hD0) _ stronglyMeasurable_const
    univ isClosed_univ (Eventually.of_forall fun _ => mem_univ _)
    (fun _ _ _ => Eventually.of_forall fun _ _ => mem_univ _) lyapBase (3 * D0)
    (contDiff_lyapBase.of_le (by simp)) (fun y _ => lyapBase_nonneg y)
    (fun M => ⟨M, fun y _ hy => hy.trans (norm_le_lyapBase y)⟩)
    (fun y _ => sdeGenerator_lyapBase_le hD0 y)

theorem switchOff_top {G : Type*} [Zero G] (f : ℝ≥0 → Ω₁ → G) :
    switchOff (fun _ => (⊤ : WithTop ℝ≥0)) f = f := by
  funext t ω; simp only [switchOff, le_top, ite_true]

variable {z : Fin 2 → ℝ} {X : ℝ≥0 → Ω₁ → Fin 2 → ℝ}

/-- **The flat pair base path is a continuous semimartingale** with the flat base
characteristics. -/
theorem isCSM_pairBase (hD0 : 0 < D0)
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) :
    IsContinuousSemimartingale P₁ 𝓖₁ (fun t ω => toFlat (X t ω))
      (fun t ω => flatBaseDrift D0 1 (toFlat (X t ω)))
      (fun t ω => flatDiff D0 1 (toFlat (X t ω))) := by
  have hφ : ContDiff ℝ 2 fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2 :=
    (contDiff_toFlat.of_le (by simp)).comp contDiff_snd
  have hY := ItoNative.itoFormulaFor_native (κ := Fin 2) (μ := μ₁) (E := Fin 2 → ℝ)
    (F := Fin 2 → ℝ) _ _ _ hX.1 _ hφ
  have H := hY.isContinuousSemimartingale
  have hd : ∀ w : Fin 2 → ℝ, DifferentiableAt ℝ toFlat w := fun w =>
    contDiff_toFlat.differentiable (by simp) w
  have hc : ∀ w : Fin 2 → ℝ, ContDiffAt ℝ 2 toFlat w := fun w =>
    (contDiff_toFlat.of_le (by simp)).contDiffAt
  simp only [switchOff_top] at H
  have e1 : (fun (t : ℝ≥0) (ω : Ω₁) =>
      timeDeriv (fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2) ((t : ℝ), X t ω) +
      spaceDeriv (fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2) ((t : ℝ), X t ω)
        (uvBaseDrift D0 (X t ω)) +
      (1 / 2 : ℝ) • ∑ a, spaceDeriv2 (fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2) ((t : ℝ), X t ω)
        (uvDiff D0 a (X t ω)) (uvDiff D0 a (X t ω))) =
      fun t ω => flatBaseDrift D0 1 (toFlat (X t ω)) := by
    funext t ω
    simp only [timeDeriv, spaceDeriv, spaceDeriv2, fderiv_comp_snd_time (hd _),
      fderiv_comp_snd_apply (hd _), fderiv_fderiv_comp_snd_apply (hc _), zero_add]
    exact toFlat_baseDrift hD0 _
  have e2 : (fun (t : ℝ≥0) (ω : Ω₁) => Matrix.of fun i j => ∑ a,
      spaceDeriv (fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2) ((t : ℝ), X t ω)
        (uvDiff D0 a (X t ω)) i *
      spaceDeriv (fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2) ((t : ℝ), X t ω)
        (uvDiff D0 a (X t ω)) j) =
      fun t ω => flatDiff D0 1 (toFlat (X t ω)) := by
    funext t ω
    simp only [spaceDeriv, fderiv_comp_snd_apply (hd _)]
    exact toFlat_cov hD0 _
  rw [e1, e2] at H
  exact H

/-- **The flat pair base path solves the flat base martingale problem** on `ℝ²`. -/
theorem isMPSolutionOn_pairBase (hD0 : 0 < D0)
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) :
    IsMPSolutionOn P₁ 𝓖₁ (flatBaseDrift D0 1) (flatDiff D0 1) univ
      (fun t ω => toFlat (X t ω)) :=
  (isCSM_pairBase hD0 hX).isMPSolutionOn (continuous_flatBaseDrift D0).continuousOn
    (contDiff_flatDiff D0).continuous.continuousOn

theorem ae_pairBase_zero (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X)
    (h0 : 0 < z 0) (h1 : 0 < z 1) (h2 : z 1 < 1) : ∀ᵐ ω ∂P₁, toFlat (X 0 ω) = z := by
  filter_upwards [hX.2] with ω hω
  rw [hω]; exact toFlat_fromFlat h0 h1 h2

/-- The good set: continuous path with the right start (a full set of `𝓖₁ 0`). -/
def pairGood (z : Fin 2 → ℝ) (X : ℝ≥0 → Ω₁ → Fin 2 → ℝ) : Set Ω₁ :=
  (toMeasurable P₁ {ω | ¬((Continuous fun t => X t ω) ∧ X 0 ω = fromFlat z)})ᶜ

open Classical in
/-- The pair base path, made constant `z` off the good set. -/
def pairPath (z : Fin 2 → ℝ) (X : ℝ≥0 → Ω₁ → Fin 2 → ℝ) (t : ℝ≥0) (ω : Ω₁) : Fin 2 → ℝ :=
  toFlat (if ω ∈ pairGood z X then X t ω else fromFlat z)

theorem measure_pairGood_compl
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) :
    P₁ (pairGood z X)ᶜ = 0 := by
  rw [pairGood, compl_compl, measure_toMeasurable]
  have : ∀ᵐ ω ∂P₁, (Continuous fun t => X t ω) ∧ X 0 ω = fromFlat z := by
    filter_upwards [hX.1.continuous, hX.2] with ω h1 h2 using ⟨h1, h2⟩
  exact ae_iff.1 this

theorem pairGood_spec {ω : Ω₁} (h : ω ∈ pairGood z X) :
    (Continuous fun t => X t ω) ∧ X 0 ω = fromFlat z := by
  by_contra h'; exact h (subset_toMeasurable _ _ h')

theorem continuous_pairPath (ω : Ω₁) : Continuous fun t => pairPath z X t ω := by
  by_cases h : ω ∈ pairGood z X
  · simp only [pairPath, h, ite_true]; exact contDiff_toFlat.continuous.comp (pairGood_spec h).1
  · simp only [pairPath, h, ite_false]; exact continuous_const

theorem pairPath_zero (h0 : 0 < z 0) (h1 : 0 < z 1) (h2 : z 1 < 1) (ω : Ω₁) :
    pairPath z X 0 ω = z := by
  unfold pairPath
  split_ifs with h
  · rw [(pairGood_spec h).2]; exact toFlat_fromFlat h0 h1 h2
  · exact toFlat_fromFlat h0 h1 h2

theorem stronglyMeasurable_pairPath
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) (t : ℝ≥0) :
    StronglyMeasurable[𝓖₁ t] (pairPath z X t) := by
  have hG : MeasurableSet[𝓖₁ t] (pairGood z X) :=
    measurableSet_aug_of_full μ₁ (measurableSet_toMeasurable _ _).compl
      (measure_pairGood_compl hX) t
  classical
  exact (contDiff_toFlat.continuous.measurable.comp (Measurable.ite hG
    (hX.1.adapted t).measurable measurable_const)).stronglyMeasurable

/-- **The modified pair base path solves the flat base martingale problem** on `ℝ²`. -/
theorem isMPSolutionOn_pairPath (hD0 : 0 < D0)
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) :
    IsMPSolutionOn P₁ 𝓖₁ (flatBaseDrift D0 1) (flatDiff D0 1) univ (pairPath z X) := by
  refine isMPSolutionOn_congr_indist (isMPSolutionOn_pairBase hD0 hX)
    (stronglyMeasurable_pairPath hX) ?_
  have : ∀ᵐ ω ∂P₁, ω ∈ pairGood z X := ae_iff.2 (measure_pairGood_compl hX)
  filter_upwards [this] with ω hω t
  simp only [pairPath, hω, ite_true]

end BlockBand.Transmission.Dual.G
