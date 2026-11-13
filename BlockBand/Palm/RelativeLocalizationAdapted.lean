module

public import BlockBand.Palm.RelativeLocalizationPicard
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Probability.Process.Filtration

/-!
# Relative localization: adapted measurable solutions of the mass equation

Setting: an arbitrary filtration `𝓖` on `ℝ≥0` (raw), a coefficient field
`Lc : ℝ≥0 → Ω → Fin N → Fin N → ℝ` adapted (`Lc t` is `𝓖 t`-measurable) and continuous in time
for **every** sample, and an `𝓖 0`-measurable datum `v₀`. Then `adaptedMass Lc v₀`
(the pointwise limit of the Picard iterates) satisfies:

* `adaptedMass_solution` : for every sample and every `T ≥ 0`, it is a solution of
  `ForwardMassSolution` on `[0, T]` with coefficients `r ↦ Lc r₊ ω` and datum `v₀ ω`;
* `adaptedMass_measurable` : `adaptedMass Lc v₀ t` is `𝓖 t`-measurable for every `t : ℝ≥0`;
* `adaptedMass_continuous` : `t ↦ adaptedMass Lc v₀ t ω` is continuous on `ℝ≥0` for every sample.

`measurable_intervalIntegral_of_continuous` (Carathéodory + Fubini measurability) is the
measurability step for one Picard iterate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Set Filter Topology MeasureTheory BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal

variable {N : ℕ}

/-- `ω ↦ ∫₀ᵗ g(r, ω) dr` is measurable when `g` is continuous in `r` and measurable in `ω`. -/
theorem measurable_intervalIntegral_of_continuous {β : Type*} [MeasurableSpace β]
    (g : ℝ → β → (Fin N → ℝ)) (hc : ∀ ω, Continuous fun r => g r ω)
    (hm : ∀ r, Measurable (g r)) (t : ℝ) :
    Measurable fun ω => ∫ r in (0 : ℝ)..t, g r ω := by
  have hu : Measurable (Function.uncurry g) := measurable_uncurry_of_continuous_of_measurable hc hm
  have hsw : StronglyMeasurable (Function.uncurry fun (ω : β) (r : ℝ) => g r ω) :=
    (hu.comp measurable_swap).stronglyMeasurable
  have h1 := hsw.integral_prod_right (ν := volume.restrict (Set.Ioc (0 : ℝ) t))
  have h2 := hsw.integral_prod_right (ν := volume.restrict (Set.Ioc t (0 : ℝ)))
  have : (fun ω => ∫ r in (0 : ℝ)..t, g r ω) =
      fun ω => (∫ r in Set.Ioc (0 : ℝ) t, g r ω) - ∫ r in Set.Ioc t (0 : ℝ), g r ω := by
    funext ω; rfl
  rw [this]
  exact h1.measurable.sub h2.measurable

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Coefficients as a function of real time. -/
def realCoeff (Lc : ℝ≥0 → Ω → Fin N → Fin N → ℝ) (ω : Ω) : ℝ → Fin N → Fin N → ℝ :=
  fun r => Lc (Real.toNNReal r) ω

omit [MeasurableSpace Ω] in
theorem realCoeff_continuous {Lc : ℝ≥0 → Ω → Fin N → Fin N → ℝ}
    (hLc : ∀ ω, Continuous fun t => Lc t ω) (ω : Ω) : Continuous (realCoeff Lc ω) :=
  (hLc ω).comp continuous_real_toNNReal

/-- Picard iterates of the sample `ω`. -/
def adaptedIter (Lc : ℝ≥0 → Ω → Fin N → Fin N → ℝ) (v₀ : Ω → Fin N → ℝ) (n : ℕ) (r : ℝ)
    (ω : Ω) : Fin N → ℝ :=
  picardIter (realCoeff Lc ω) (v₀ ω) n r

/-- The adapted solution: the limit of the Picard iterates. -/
def adaptedMass (Lc : ℝ≥0 → Ω → Fin N → Fin N → ℝ) (v₀ : Ω → Fin N → ℝ) (r : ℝ) (ω : Ω) :
    Fin N → ℝ :=
  limUnder atTop fun n => adaptedIter Lc v₀ n r ω

theorem adaptedIter_measurable (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    {Lc : ℝ≥0 → Ω → Fin N → Fin N → ℝ} (hLm : ∀ t, Measurable[𝓖 t] (Lc t))
    (hLc : ∀ ω, Continuous fun t => Lc t ω) {v₀ : Ω → Fin N → ℝ} (hv₀ : Measurable[𝓖 0] v₀)
    (n : ℕ) : ∀ t : ℝ≥0, Measurable[𝓖 t] (fun ω => adaptedIter Lc v₀ n t ω) := by
  induction n with
  | zero => intro t; exact hv₀.mono (𝓖.mono (zero_le (a := t))) le_rfl
  | succ n ih =>
    intro t
    set c : ℝ → ℝ := fun r => min (max r 0) t with hc
    set g : ℝ → Ω → Fin N → ℝ := fun r ω =>
      matAct (realCoeff Lc ω (c r)) (adaptedIter Lc v₀ n (c r) ω) with hg
    have hcc : Continuous c := by fun_prop
    have hgc : ∀ ω, Continuous fun r => g r ω := fun ω =>
      continuous_matAct ((realCoeff_continuous hLc ω).comp hcc)
        ((picardIter_continuous (realCoeff_continuous hLc ω) (v₀ ω) n).comp hcc)
    have hgm : ∀ r, Measurable[𝓖 t] (g r) := by
      intro r
      have hc0 : 0 ≤ c r := le_min (le_max_right _ _) t.2
      have hct : Real.toNNReal (c r) ≤ t := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hc0]; exact min_le_right _ _
      have hL : Measurable[𝓖 t] (fun ω => realCoeff Lc ω (c r)) :=
        (hLm (Real.toNNReal (c r))).mono (𝓖.mono hct) le_rfl
      have hI : Measurable[𝓖 t] (fun ω => adaptedIter Lc v₀ n (c r) ω) := by
        have := (ih (Real.toNNReal (c r))).mono (𝓖.mono hct) le_rfl
        rwa [Real.coe_toNNReal _ hc0] at this
      refine @measurable_pi_iff Ω (Fin N) (fun _ => ℝ) (𝓖 t) _ _ |>.mpr fun k => ?_
      refine Finset.measurable_sum _ fun l _ => ?_
      exact ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp hL)).mul
        ((measurable_pi_apply l).comp hI)
    have hint := @measurable_intervalIntegral_of_continuous N Ω (𝓖 t) g hgc hgm t
    have heq : (fun ω => adaptedIter Lc v₀ (n + 1) t ω) =
        fun ω => v₀ ω + ∫ r in (0 : ℝ)..t, g r ω := by
      funext ω
      simp only [adaptedIter, picardIter]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hr
      have : c r = r := by simp only [hc]; rw [max_eq_left hr.1, min_eq_left hr.2]
      simp only [hg, this, adaptedIter]
    rw [heq]
    exact (hv₀.mono (𝓖.mono (zero_le (a := t))) le_rfl).add hint

omit [MeasurableSpace Ω] in
/-- For every sample and `T ≥ 0`, the adapted mass agrees on `[0,T]` with any solution. -/
theorem adaptedMass_eq {Lc : ℝ≥0 → Ω → Fin N → Fin N → ℝ}
    (hLc : ∀ ω, Continuous fun t => Lc t ω) (v₀ : Ω → Fin N → ℝ) (ω : Ω) {T : ℝ}
    {w : ℝ → Fin N → ℝ} (hw : ForwardMassSolution (realCoeff Lc ω) 0 T (v₀ ω) w) {r : ℝ}
    (hr : r ∈ Icc 0 T) : adaptedMass Lc v₀ r ω = w r := by
  have ht := tendsto_picardIter (realCoeff_continuous hLc ω) hw hr
  exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨_, ht⟩) ht

omit [MeasurableSpace Ω] in
theorem adaptedMass_solution {Lc : ℝ≥0 → Ω → Fin N → Fin N → ℝ}
    (hLc : ∀ ω, Continuous fun t => Lc t ω) (v₀ : Ω → Fin N → ℝ) (ω : Ω) {T : ℝ} (hT : 0 ≤ T) :
    ForwardMassSolution (realCoeff Lc ω) 0 T (v₀ ω) (fun r => adaptedMass Lc v₀ r ω) := by
  obtain ⟨w, hw⟩ := forwardMass_exists hT (realCoeff_continuous hLc ω).continuousOn (v₀ ω)
  have heq : EqOn (fun r => adaptedMass Lc v₀ r ω) w (Icc 0 T) :=
    fun r hr => adaptedMass_eq hLc v₀ ω hw hr
  obtain ⟨h0, hc, hd⟩ := hw
  refine ⟨by rw [heq ⟨le_rfl, hT⟩, h0], hc.congr heq, fun x hx => ?_⟩
  have hev : (fun r => adaptedMass Lc v₀ r ω) =ᶠ[𝓝 x] w :=
    Filter.eventuallyEq_of_mem (Icc_mem_nhds hx.1 hx.2) heq
  have := (hd x hx).congr_of_eventuallyEq hev
  rwa [show w x = adaptedMass Lc v₀ x ω from (heq ⟨hx.1.le, hx.2.le⟩).symm] at this

theorem adaptedMass_measurable (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    {Lc : ℝ≥0 → Ω → Fin N → Fin N → ℝ} (hLm : ∀ t, Measurable[𝓖 t] (Lc t))
    (hLc : ∀ ω, Continuous fun t => Lc t ω) {v₀ : Ω → Fin N → ℝ} (hv₀ : Measurable[𝓖 0] v₀)
    (t : ℝ≥0) : Measurable[𝓖 t] (fun ω => adaptedMass Lc v₀ t ω) := by
  refine @measurable_of_tendsto_metrizable Ω (Fin N → ℝ) (𝓖 t) _ _ _ _
    (fun n ω => adaptedIter Lc v₀ n t ω) _
    (fun n => adaptedIter_measurable 𝓖 hLm hLc hv₀ n t) ?_
  rw [tendsto_pi_nhds]
  intro ω
  obtain ⟨w, hw⟩ := forwardMass_exists t.2 (realCoeff_continuous hLc ω).continuousOn (v₀ ω)
  have ht := tendsto_picardIter (realCoeff_continuous hLc ω) hw ⟨t.2, le_rfl⟩
  rwa [← adaptedMass_eq hLc v₀ ω hw ⟨t.2, le_rfl⟩] at ht

omit [MeasurableSpace Ω] in
theorem adaptedMass_continuous {Lc : ℝ≥0 → Ω → Fin N → Fin N → ℝ}
    (hLc : ∀ ω, Continuous fun t => Lc t ω) (v₀ : Ω → Fin N → ℝ) (ω : Ω) :
    Continuous fun t : ℝ≥0 => adaptedMass Lc v₀ t ω := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hT : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
  have hsol := adaptedMass_solution hLc v₀ ω hT
  have hon : ContinuousOn (fun s : ℝ≥0 => adaptedMass Lc v₀ s ω) (Iio (t + 1)) := by
    refine hsol.2.1.comp NNReal.continuous_coe.continuousOn fun s hs => ⟨s.2, ?_⟩
    have : (s : ℝ) < (t : ℝ) + 1 := by exact_mod_cast hs
    exact this.le
  exact hon.continuousAt (Iio_mem_nhds (by simp))

end BlockBand.Palm.RelativeLocalization
