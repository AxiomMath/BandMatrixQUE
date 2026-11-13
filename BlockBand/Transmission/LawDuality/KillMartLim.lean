module

public import BlockBand.Transmission.LawDuality.KillOrth
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded pointwise limits of martingales are martingales

Generic (imports Mathlib and `KillOrth`).

**`integral_mul_increment_eq_zero_of_tendsto`** (the form consumed by `integral_killed_eq`):
if `M k` are martingales, `M k t → L t` a.e. for every `t`, `|M k t| ≤ C t` a.e., then
`E[A(L_t − L_s)] = 0` for `s ≤ t` and bounded `𝓖_s`-measurable `A`. No completeness of `𝓖` is
needed (the stopped martingales of `exists_martingale_stoppedProcess` are only a.e. equal to the
stopped processes).

**`martingale_of_tendsto`**: if `M n` are martingales for a filtration `𝓖` (index `ℝ≥0`) on a
finite measure space, `M n t ω → L t ω` for every `ω` and `t`, and `|M n t| ≤ C t` a.e. for all
`n`, then `L` is a martingale. The proof of `RatioDualityPrinciple` uses it to pass from the
stopped level-`q` martingales of the cutoff tests `u_{k+1}·F_·(ν)` (the dual martingale clause) to
the limit process that crosses the deletion at the end of level `q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {𝓖 : Filtration ℝ≥0 m}

/-- **A bounded pointwise limit of martingales is a martingale.** -/
theorem martingale_of_tendsto {M : ℕ → ℝ≥0 → Ω → ℝ} {L : ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) 𝓖 P)
    (hlim : ∀ t ω, Tendsto (fun n => M n t ω) atTop (𝓝 (L t ω)))
    (hb : ∀ t, ∃ C : ℝ, ∀ n, ∀ᵐ ω ∂P, |M n t ω| ≤ C) : Martingale L 𝓖 P := by
  have hsm : ∀ t, StronglyMeasurable[𝓖 t] (L t) := fun t =>
    stronglyMeasurable_of_tendsto atTop (fun n => (hM n).1 t) (tendsto_pi_nhds.2 (hlim t))
  have hbL : ∀ t, ∃ C : ℝ, ∀ᵐ ω ∂P, |L t ω| ≤ C := fun t => by
    obtain ⟨C, hC⟩ := hb t
    refine ⟨C, ?_⟩
    filter_upwards [ae_all_iff.2 hC] with ω hω
    exact le_of_tendsto ((continuous_abs.tendsto _).comp (hlim t ω)) (Eventually.of_forall hω)
  have hint : ∀ t, Integrable (L t) P := fun t => by
    obtain ⟨C, hC⟩ := hbL t
    exact Integrable.of_bound ((hsm t).mono (𝓖.le t)).aestronglyMeasurable C
      (by filter_upwards [hC] with ω hω; rwa [Real.norm_eq_abs])
  -- set integrals pass to the limit
  have hset : ∀ t (s : Set Ω), MeasurableSet s →
      Tendsto (fun n => ∫ ω in s, M n t ω ∂P) atTop (𝓝 (∫ ω in s, L t ω ∂P)) := by
    intro t s hs
    obtain ⟨C, hC⟩ := hb t
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (((hM n).1 t).mono (𝓖.le t)).aestronglyMeasurable.restrict)
      (integrable_const C) (fun n => ae_restrict_of_ae (by
        filter_upwards [hC n] with ω hω; rwa [Real.norm_eq_abs]))
      (ae_restrict_of_ae (Eventually.of_forall fun ω => hlim t ω))
  refine ⟨fun t => hsm t, fun i j hij => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le i) (hint j)
    (fun s _ _ => (hint i).integrableOn) (fun s hs _ => ?_)
    (hsm i).aestronglyMeasurable).symm
  have e : (fun n => ∫ ω in s, M n i ω ∂P) = fun n => ∫ ω in s, M n j ω ∂P :=
    funext fun n => (hM n).setIntegral_eq hij hs
  have h1 := hset i s (𝓖.le i s hs)
  rw [e] at h1
  exact tendsto_nhds_unique h1 (hset j s (𝓖.le i s hs))

/-- **Orthogonality of increments passes to a.e. bounded limits of martingales.** -/
theorem integral_mul_increment_eq_zero_of_tendsto {M : ℕ → ℝ≥0 → Ω → ℝ} {L : ℝ≥0 → Ω → ℝ}
    (hM : ∀ k, Martingale (M k) 𝓖 P)
    (hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun k => M k t ω) atTop (𝓝 (L t ω)))
    (hb : ∀ t, ∃ C : ℝ, ∀ k, ∀ᵐ ω ∂P, |M k t ω| ≤ C) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Ω → ℝ} (hA : StronglyMeasurable[𝓖 s] A) {CA : ℝ} (hAb : ∀ ω, |A ω| ≤ CA) :
    ∫ ω, A ω * (L t ω - L s ω) ∂P = 0 := by
  obtain ⟨Ct, hCt⟩ := hb t
  obtain ⟨Cs, hCs⟩ := hb s
  have hAm : AEStronglyMeasurable A P := (hA.mono (𝓖.le s)).aestronglyMeasurable
  have hmeas : ∀ k, AEStronglyMeasurable (fun ω => A ω * (M k t ω - M k s ω)) P := fun k =>
    hAm.mul (((((hM k).1 t).mono (𝓖.le t)).aestronglyMeasurable).sub
      ((((hM k).1 s).mono (𝓖.le s)).aestronglyMeasurable))
  have hlim' := tendsto_integral_of_dominated_convergence (fun _ => CA * (Ct + Cs)) hmeas
    (integrable_const _) (fun k => by
      filter_upwards [hCt k, hCs k] with ω h1 h2
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hAb ω) ((abs_sub _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
        ((abs_nonneg _).trans (hAb ω)))
    (by
      filter_upwards [hlim t, hlim s] with ω h1 h2
      exact tendsto_const_nhds.mul (h1.sub h2))
  have hzero : (fun k => ∫ ω, A ω * (M k t ω - M k s ω) ∂P) = fun _ => 0 :=
    funext fun k => integral_mul_increment_eq_zero (hM k) hst hA hAb
  rw [hzero] at hlim'
  exact tendsto_nhds_unique hlim' tendsto_const_nhds

end BlockBand.Transmission.LawDuality
