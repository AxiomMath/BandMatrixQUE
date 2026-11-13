module

public import BlockBand.Transmission.DualBoundary.LawLift

/-!
# Right-continuity of `t ↦ dualTransform`

Setting: any one-pair boundary realization `IsBoundaryDualProcess P 𝓖 D₀ ![x] ![y] N X Y`
with `x, y ≥ 0`, an absorption profile `κ`, any energy `E`.

* `continuous_dualIntegral_param`: `t ↦ I_t = ∫_0^t h(t−s) R_s ds` is continuous along every
  path with continuous `R` (`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`).
* **`continuousWithinAt_dualTransform`**: `K(t) = dualTransform E κ t P N X Y` is
  right-continuous at every `t₀ ≥ 0` (dominated convergence with bound `1`;
  `1{ζ ≤ t} → 1{ζ ≤ t₀}` as `t ↓ t₀` because `{ζ ≤ ·}` is closed on the right).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open scoped NNReal ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ}
  {x y : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- `t ↦ I_t` is continuous along a path with continuous `R`. -/
theorem continuous_dualIntegral_param {E : ℝ} {κ : ℝ → ℝ} (hκ : Continuous κ) {ω : Ω}
    (hR : Continuous fun s : ℝ≥0 => dualTotal (N s ω) (X s ω) (Y s ω)) :
    Continuous fun t => dualIntegral E κ t N X Y ω := by
  unfold dualIntegral absorptionRate
  have hf : Continuous fun p : ℝ × ℝ =>
      4 * Real.pi * Parameters.semicircleDensity E * κ (p.1 - p.2) *
        dualTotal (N p.2.toNNReal ω) (X p.2.toNNReal ω) (Y p.2.toNNReal ω) :=
    (continuous_const.mul (hκ.comp (continuous_fst.sub continuous_snd))).mul
      (hR.comp (continuous_real_toNNReal.comp continuous_snd))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hf
    continuous_id

/-- **`t ↦ dualTransform E κ t P N X Y` is right-continuous on `[0, ∞)`.** -/
theorem continuousWithinAt_dualTransform (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    (hx : 0 ≤ x) (hy : 0 ≤ y) {E : ℝ} {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) :
    ContinuousWithinAt (fun t => dualTransform E κ t P N X Y) (Ici t₀) t₀ := by
  have := h.prob
  simp only [dualTransform_eq_integral]
  refine continuousWithinAt_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const 1) ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : t₀ ≤ t)
    exact aestronglyMeasurable_dualIntegrand h E hκ.1 (ht₀.trans ht)
  · filter_upwards [self_mem_nhdsWithin] with t (ht : t₀ ≤ t)
    exact ae_norm_dualIntegrand_le h hx hy hκ (ht₀.trans ht)
  · filter_upwards [ae_path h] with ω hω
    have hI := continuous_dualIntegral_param (E := E) hκ.1 (continuous_dualTotal hω.2 hω.1)
    by_cases hd : dualExtinction N ω ≤ ENNReal.ofReal t₀
    · refine (Real.continuous_exp.comp hI.neg).continuousWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with t (ht : t₀ ≤ t)
        simp only [dualIntegrand, hd.trans (ENNReal.ofReal_le_ofReal ht), ite_true,
          Function.comp, Pi.neg_apply]
      · simp only [dualIntegrand, hd, ite_true, Function.comp, Pi.neg_apply]
    · have hlt : ENNReal.ofReal t₀ < dualExtinction N ω := not_le.1 hd
      have hev : ∀ᶠ t in 𝓝 t₀, ENNReal.ofReal t < dualExtinction N ω :=
        (ENNReal.continuous_ofReal.tendsto t₀).eventually (gt_mem_nhds hlt)
      refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds hev] with t ht
        simp only [dualIntegrand, not_le.2 ht, ite_false]
      · simp only [dualIntegrand, hd, ite_false]

end BlockBand.Transmission.DualBoundary
