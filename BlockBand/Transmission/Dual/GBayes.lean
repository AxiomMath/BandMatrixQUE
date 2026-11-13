module

public import BlockBand.SourceProcess.Stochastic.Levy.Product
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bayes' rule for a tilted measure

`IsDensity P 𝓖 M g`: `M` is a `P`-martingale and `g ≥ 0` an integrable terminal density with
`M_t = E[g | 𝓖_t]` a.s. for every `t`. Put `P̃ = tilt P g = g · P`.
* `setIntegral_tilt_eq`: for `f` bounded and `𝓖_t`-measurable and `A ∈ 𝓖_t`,
  `∫_A f dP̃ = ∫_A M_t f dP`.
* **`hasMM_tilt`** (Bayes' rule): if `X_t` is a.s. bounded for each `t` and `X M` has a
  `P`-martingale modification `N`, then `X` has a `P̃`-martingale modification, namely `N / M`
  (with `x / 0 = 0`; `P̃(M_t = 0) = 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Levy
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- `M` is the density martingale of the terminal density `g`. -/
structure IsDensity (P : Measure Ω) (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0) : Prop where
  mart : Martingale M 𝓖 P
  meas : Measurable g
  integrable : Integrable (fun ω => (g ω : ℝ)) P
  condExp : ∀ t, M t =ᵐ[P] P[fun ω => (g ω : ℝ) | 𝓖 t]

/-- The tilted measure `g · P`. -/
def tilt (P : Measure Ω) (g : Ω → ℝ≥0) : Measure Ω := P.withDensity fun ω => (g ω : ℝ≥0∞)

theorem tilt_ac (g : Ω → ℝ≥0) : tilt P g ≪ P := withDensity_absolutelyContinuous _ _

variable {M : ℝ≥0 → Ω → ℝ} {g : Ω → ℝ≥0}

theorem IsDensity.isFiniteMeasure (h : IsDensity P 𝓖 M g) : IsFiniteMeasure (tilt P g) := by
  refine isFiniteMeasure_withDensity (ne_of_lt ?_)
  have := h.integrable.2
  simpa [HasFiniteIntegral] using this

theorem IsDensity.setIntegral_tilt (h : IsDensity P 𝓖 M g) (f : Ω → ℝ) {A : Set Ω}
    (hA : MeasurableSet A) : ∫ ω in A, f ω ∂tilt P g = ∫ ω in A, (g ω : ℝ) * f ω ∂P := by
  rw [tilt, setIntegral_withDensity_eq_setIntegral_smul h.meas f hA]
  rfl

variable [IsProbabilityMeasure P]

/-- **`∫_A f dP̃ = ∫_A M_t f dP`** for `f` bounded `𝓖_t`-measurable and `A ∈ 𝓖_t`. -/
theorem IsDensity.setIntegral_tilt_eq (h : IsDensity P 𝓖 M g) {t : ℝ≥0} {f : Ω → ℝ}
    (hf : StronglyMeasurable[𝓖 t] f) {C : ℝ} (hC : ∀ᵐ ω ∂P, |f ω| ≤ C) {A : Set Ω}
    (hA : MeasurableSet[𝓖 t] A) : ∫ ω in A, f ω ∂tilt P g = ∫ ω in A, M t ω * f ω ∂P := by
  rw [h.setIntegral_tilt f (𝓖.le t A hA)]
  have hfg : Integrable (f * fun ω => (g ω : ℝ)) P :=
    h.integrable.bdd_mul (hf.mono (𝓖.le t)).aestronglyMeasurable
      (hC.mono fun ω hω => by rwa [Real.norm_eq_abs])
  have e1 := setIntegral_condExp (𝓖.le t) hfg hA
  have e2 := condExp_mul_of_stronglyMeasurable_left hf hfg h.integrable
  have e3 : ∫ ω in A, (g ω : ℝ) * f ω ∂P = ∫ ω in A, (f * fun ω => (g ω : ℝ)) ω ∂P :=
    setIntegral_congr_fun (𝓖.le t A hA) fun ω _ => by simp [mul_comm]
  rw [e3, ← e1, setIntegral_congr_ae (𝓖.le t A hA) (e2.mono fun ω hω _ => hω)]
  refine setIntegral_congr_ae (𝓖.le t A hA) ?_
  filter_upwards [h.condExp t] with ω hω _
  simp only [Pi.mul_apply, hω]
  ring

/-- `P̃(M_t = 0) = 0`. -/
theorem IsDensity.tilt_zero (h : IsDensity P 𝓖 M g) (t : ℝ≥0) :
    tilt P g {ω | M t ω = 0} = 0 := by
  have := h.isFiniteMeasure
  have hS : MeasurableSet[𝓖 t] {ω | M t ω = 0} :=
    (h.mart.1 t).measurable (measurableSet_singleton 0)
  have e := h.setIntegral_tilt_eq (f := fun _ => (1 : ℝ)) stronglyMeasurable_const
    (C := 1) (Eventually.of_forall fun _ => by simp) hS
  have e0 : ∫ ω in {ω | M t ω = 0}, M t ω * 1 ∂P = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun ω hω => by simp [show M t ω = 0 from hω]
  rw [e0, setIntegral_const, smul_eq_mul, mul_one] at e
  simpa [measureReal_def, ENNReal.toReal_eq_zero_iff, measure_ne_top] using e

/-- **Bayes' rule.** -/
theorem IsDensity.hasMM_tilt (h : IsDensity P 𝓖 M g) {X : ℝ≥0 → Ω → ℝ}
    (hXb : ∀ t, ∃ C, ∀ᵐ ω ∂P, |X t ω| ≤ C)
    (hXM : HasMartingaleModification P 𝓖 (fun t ω => X t ω * M t ω)) :
    HasMartingaleModification (tilt P g) 𝓖 X := by
  have := h.isFiniteMeasure
  obtain ⟨N, hN, hNe⟩ := hXM
  choose C hC using hXb
  set N' : ℝ≥0 → Ω → ℝ := fun t ω => N t ω / M t ω with hN'
  have key : ∀ t, ∀ᵐ ω ∂P, N' t ω * M t ω = N t ω ∧ |N' t ω| ≤ max (C t) 0 ∧
      (M t ω ≠ 0 → N' t ω = X t ω) := by
    intro t
    filter_upwards [hNe t, hC t] with ω hω hc
    rw [hω]
    by_cases hm : M t ω = 0
    · simp [hN', hm, hω]
    · simp only [hN', hω, mul_div_assoc, div_self hm, mul_one, ne_eq, hm, not_false_eq_true,
        forall_const, and_true]
      exact ⟨trivial, hc.trans (le_max_left _ _)⟩
  have hm : ∀ t, StronglyMeasurable[𝓖 t] (N' t) := fun t =>
    ((hN.1 t).measurable.div (h.mart.1 t).measurable).stronglyMeasurable
  have hsi : ∀ t (A : Set Ω), MeasurableSet[𝓖 t] A →
      ∫ ω in A, N' t ω ∂tilt P g = ∫ ω in A, N t ω ∂P := fun t A hA => by
    rw [h.setIntegral_tilt_eq (hm t) ((key t).mono fun ω hω => hω.2.1) hA]
    refine setIntegral_congr_ae (𝓖.le t A hA) ?_
    filter_upwards [key t] with ω hω _
    rw [mul_comm]; exact hω.1
  refine ⟨N', martingale_of_setIntegral_eq hm (fun t => ?_) fun s t hst S hS => ?_, fun t => ?_⟩
  · exact Integrable.of_bound ((hm t).mono (𝓖.le t)).aestronglyMeasurable (max (C t) 0)
      (tilt_ac g ((key t).mono fun ω hω => by rw [Real.norm_eq_abs]; exact hω.2.1))
  · rw [hsi t S (𝓖.mono hst S hS), hsi s S hS]
    exact (hN.setIntegral_eq hst hS).symm
  · have h0 : ∀ᵐ ω ∂tilt P g, M t ω ≠ 0 := by
      rw [ae_iff]; simpa using h.tilt_zero t
    filter_upwards [tilt_ac g (key t), h0] with ω hω h0
    exact hω.2.2 h0

end BlockBand.Transmission.Dual.G
