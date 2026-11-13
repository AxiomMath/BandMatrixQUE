module

public import BlockBand.SourceProcess.CoupledFrames.NativeSum
public import BlockBand.SourceProcess.CoupledFrames.StopMult

/-!
# Changing the coefficients of an Itô process at finitely many random times

`isNativeItoProcess_congr_coeff`: if `X` is an Itô process with drift `b` and diffusion `σ`,
`b'`, `σ'` are progressive and, for `P`-a.e. `x`, `b' = b` and `σ' = σ` at every time `t` different
from the measurable random times `θ_0(x), …, θ_{m−1}(x)`, then `X` is an Itô process with
drift `b'` and diffusion `σ'`. The exceptional set is `dt`-null on every path (finite) and
`ν`-null (`ae_timeProb_ne`), so the drift integrals and integrals do not change.
`isNativeItoProcess_congr_proc`: replacing `X` by an adapted progressive process indistinguishable
from it.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.Stochastic.Integral BlockBand.SourceProcess.Stochastic.ItoNative
open BlockBand.SourceProcess.Stochastic.Semimartingale

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [MeasurableSpace S] [Fintype κ] in
/-- On a path, almost every time in `(0,t]` avoids finitely many random times. -/
theorem ae_ne_times {m : ℕ} (θ : Fin m → DriverSample S κ → WithTop ℝ≥0) (x : DriverSample S κ)
    (t : ℝ) : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) t)),
      ∀ i, ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≠ θ i x := by
  have hfin : (Set.range fun i : Fin m => (((θ i x).untopA : ℝ≥0) : ℝ)).Countable :=
    (Set.finite_range _).countable
  have h0 : volume (Set.range fun i : Fin m => (((θ i x).untopA : ℝ≥0) : ℝ)) = 0 :=
    hfin.measure_zero volume
  have h1 : ∀ᵐ s ∂volume, s ∉ Set.range fun i : Fin m => (((θ i x).untopA : ℝ≥0) : ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem measurableSet_Ioc] with s hs hmem i heq
  apply hs
  refine ⟨i, ?_⟩
  show (((θ i x).untopA : ℝ≥0) : ℝ) = s
  rw [← heq]
  exact Real.coe_toNNReal _ hmem.1.le

omit [Fintype κ] [IsProbabilityMeasure μ] in
theorem measurableSet_ne_times {m : ℕ} {θ : Fin m → DriverSample S κ → WithTop ℝ≥0}
    (hθ : ∀ i, Measurable (θ i)) :
    MeasurableSet {p : ℝ × DriverSample S κ |
      ∀ i, ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≠ θ i p.2} := by
  have hc : Measurable fun p : ℝ × DriverSample S κ => ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) :=
    WithTop.measurable_coe.comp (measurable_real_toNNReal.comp measurable_fst)
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => ?_
  have e : {p : ℝ × DriverSample S κ | ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≠ θ i p.2} =
      ({p | ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ θ i p.2} ∩
        {p | θ i p.2 ≤ ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0)})ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff, ne_eq, le_antisymm_iff]
  rw [e]
  exact ((measurableSet_le hc ((hθ i).comp measurable_snd)).inter
    (measurableSet_le ((hθ i).comp measurable_snd) hc)).compl

/-- `ν`-almost every `(s, x)` avoids the random times. -/
theorem ae_timeProb_ne {m : ℕ} {θ : Fin m → DriverSample S κ → WithTop ℝ≥0}
    (hθ : ∀ i, Measurable (θ i)) (T : ℝ≥0) :
    ∀ᵐ p ∂timeProbMeasure T (driverLaw (κ := κ) μ),
      ∀ i, ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≠ θ i p.2 := by
  unfold timeProbMeasure
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_ne_times hθ)]
  exact (Measure.ae_ae_comm (p := fun (s : ℝ) (x : DriverSample S κ) => ∀ i, ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≠ θ i x)
    (measurableSet_ne_times hθ)).2 (ae_of_all _ fun x => ae_ne_times θ x T)

/-- **Coefficient congruence off finitely many random times.** -/
theorem isNativeItoProcess_congr_coeff
    {X b b' : ℝ≥0 → DriverSample S κ → E} {σ σ' : κ → ℝ≥0 → DriverSample S κ → E}
    (h : IsNativeItoProcess μ X b σ) {m : ℕ} {θ : Fin m → DriverSample S κ → WithTop ℝ≥0}
    (hθ : ∀ i, Measurable (θ i))
    (hb' : IsStronglyProgressive (driverAugmented (κ := κ) μ) b')
    (hσ' : ∀ a, IsStronglyProgressive (driverAugmented (κ := κ) μ) (σ' a))
    (heq : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t : ℝ≥0, (∀ i, (t : WithTop ℝ≥0) ≠ θ i x) →
      b' t x = b t x ∧ ∀ a, σ' a t x = σ a t x) :
    IsNativeItoProcess μ X b' σ' := by
  have hpath : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t : ℝ≥0,
      (fun s : ℝ => b' s.toNNReal x) =ᵐ[volume.restrict (Ioc (0 : ℝ) t)] fun s => b s.toNNReal x := by
    filter_upwards [heq] with x hx t
    filter_upwards [ae_ne_times θ x t] with s hs
    exact (hx _ hs).1
  have hnu : ∀ (T : ℝ≥0) (ℓ : E →L[ℝ] ℝ) (ρ : DriverSample S κ → WithTop ℝ≥0) (c : κ),
      stopIntegrand ρ (functionalIntegrand ℓ σ') c
        =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] stopIntegrand ρ (functionalIntegrand ℓ σ) c := by
    intro T ℓ ρ c
    filter_upwards [ae_timeProb_ne hθ T, ae_timeProb_of_ae (T := T) heq] with p hp hq
    simp only [stopIntegrand, functionalIntegrand, ((hq _ hp).2 c)]
  obtain ⟨τ, hτs, hτl, hloc⟩ := h.localizing
  refine ⟨h.adapted, h.progressive, h.continuous, hb', hσ', ?_,
    ⟨τ, hτs, hτl, fun n ℓ T => NativeIntegrand.congr (hloc n ℓ T) fun c => (hnu T ℓ (τ n) c).symm⟩, ?_⟩
  · filter_upwards [h.drift_integrable, hpath] with x hx hp t
    exact (hx t).congr_fun_ae (hp t).symm
  · intro ℓ ρ hρ T hG t ht
    obtain ⟨hs, hid⟩ := h.identity ℓ ρ hρ T (NativeIntegrand.congr hG fun c => hnu T ℓ ρ c) t ht
    have hs' := NativeIntegrand.congr hs fun c => (hnu T ℓ _ c).symm
    refine ⟨hs', ?_⟩
    rw [nativeIntegralOf_congr hs' hs fun c => hnu T ℓ _ c]
    filter_upwards [hid, hpath] with x hx hp
    rw [← hx]
    congr 2
    unfold stoppedDrift
    refine integral_congr_ae ?_
    filter_upwards [hp t] with s hs
    simp only [hs]

/-- **Process congruence.** -/
theorem isNativeItoProcess_congr_proc
    {X X' b : ℝ≥0 → DriverSample S κ → E} {σ : κ → ℝ≥0 → DriverSample S κ → E}
    (h : IsNativeItoProcess μ X b σ)
    (ha : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X' t))
    (hp : IsStronglyProgressive (driverAugmented (κ := κ) μ) X')
    (heq : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X' t x = X t x) :
    IsNativeItoProcess μ X' b σ := by
  refine ⟨ha, hp, ?_, h.drift_progressive, h.diffusion_progressive, h.drift_integrable,
    h.localizing, ?_⟩
  · filter_upwards [h.continuous, heq] with x hx he
    have : (fun t => X' t x) = fun t => X t x := funext he
    rw [this]; exact hx
  · intro ℓ ρ hρ T hG t ht
    obtain ⟨hs, hid⟩ := h.identity ℓ ρ hρ T hG t ht
    refine ⟨hs, ?_⟩
    filter_upwards [hid, heq] with x hx he
    rw [← hx, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, he, he]

end BlockBand.SourceProcess.CoupledFrames
