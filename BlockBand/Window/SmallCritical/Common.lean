module

public import BlockBand.Window.SmallCritical.WindowBridge
public import BlockBand.Model.Construction.PhysicalSpectralLawInvariant

/-!
# Fixed data and critical-sequence asymptotics for the small-ratio critical theorem

A reference window, a bulk margin, eventual bounds along critical sequences, and the spectral
stationarity of critical marked limits.

* `refPsi`: a fixed smooth bump (`ContDiffBump` centred at `1/2`, radii `1, 2`), `≥ 1` on
  `[0,1]`; `refWeight = refPsi / ∫ refPsi` is the unit-mass window used in
  the window transfer theorem.
* `exists_bulk_margin`: for `E² < 4` a margin `0 < ϑ < 1/2` with `ϑ < F_sc(E) < 1 - ϑ`.
* `critical_eventually`: along every critical sequence `n/W → τ > 0`, eventually
  `n/W < T'` (any `T' > τ`), `n/W < 2τ`, `n ≥ N₀` and `a_{n,W}/√n ≤ 2`
  (`critical_refined_scale_ratio_tendsto`).
* `stationary_of_criticalLimit`: every `P ∈ 𝔏_{τ,b,E}` is invariant under all global spectral
  translations (`criticalSequence_marked_weakLimit_spectral_law_invariant`, the translation
  clause of the stationarity proposition).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction BlockBand.Internal.Contracts.WindowAngular
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal

/-!
### Reference window
-/

/-- The fixed bump `ψ`: centre `1/2`, equal to `1` on `[-1/2, 3/2]`, supported in `[-3/2, 5/2]`. -/
def refBump : ContDiffBump (1 / 2 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- `ψ` as a real function. -/
def refPsi : ℝ → ℝ := fun u => refBump u

theorem continuous_refPsi : Continuous refPsi := refBump.continuous

theorem hasCompactSupport_refPsi : HasCompactSupport refPsi := refBump.hasCompactSupport

theorem refPsi_nonneg (u : ℝ) : 0 ≤ refPsi u := refBump.nonneg

theorem refPsi_ge_one (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : 1 ≤ refPsi u := by
  refine le_of_eq (refBump.one_of_mem_closedBall ?_).symm
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -1 ≤ u - 1 / 2 ∧ u - 1 / 2 ≤ 1
  constructor <;> linarith [hu.1, hu.2]

/-- `c_ψ = ∫ ψ > 0`. -/
def refMass : ℝ := ∫ u, refPsi u

theorem refMass_pos : 0 < refMass := refBump.integral_pos

/-- The unit-mass reference window `w₀ = ψ / c_ψ`. -/
def refWeight : ℝ → ℝ := fun u => refPsi u / refMass

theorem continuous_refWeight : Continuous refWeight := continuous_refPsi.div_const _

theorem hasCompactSupport_refWeight : HasCompactSupport refWeight := by
  have := hasCompactSupport_refPsi.mul_right (f' := fun _ : ℝ => refMass⁻¹)
  convert this using 1
  funext u
  simp [refWeight, div_eq_mul_inv]

theorem refWeight_nonneg (u : ℝ) : 0 ≤ refWeight u :=
  div_nonneg (refPsi_nonneg u) refMass_pos.le

theorem integral_refWeight : ∫ u, refWeight u = 1 := by
  unfold refWeight
  rw [integral_div]
  exact div_self refMass_pos.ne'

theorem refPsi_eq (u : ℝ) : refPsi u = refMass * refWeight u := by
  unfold refWeight
  field_simp [refMass_pos.ne']

/-!
### Bulk margin
-/

theorem exists_bulk_margin {E : ℝ} (hE : E ^ 2 < 4) :
    ∃ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 / 2 ∧ ϑ < semicircleCDF E ∧ semicircleCDF E < 1 - ϑ := by
  have hE2 : -2 < E ∧ E < 2 := by constructor <;> nlinarith
  have hpos : ∀ x ∈ Ioo (-2 : ℝ) 2, 0 < Parameters.semicircleDensity x := by
    intro x hx
    apply Parameters.semicircleDensity_pos_of_sq_lt_four
    nlinarith [hx.1, hx.2]
  have hF0 : 0 < semicircleCDF E := by
    unfold semicircleCDF
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (BlockBand.Window.Transfer.semicircleDensity_intervalIntegrable _ _)
      (fun x hx => hpos x ⟨hx.1, lt_trans hx.2 hE2.2⟩) hE2.1
  have hF1 : semicircleCDF E < 1 := by
    have h := BlockBand.Window.Transfer.semicircleCDF_sub 2 E
    rw [BlockBand.Window.Transfer.semicircleCDF_two] at h
    have : 0 < ∫ t in E..2, Parameters.semicircleDensity t :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        (BlockBand.Window.Transfer.semicircleDensity_intervalIntegrable _ _)
        (fun x hx => hpos x ⟨lt_trans hE2.1 hx.1, hx.2⟩) hE2.2
    linarith
  refine ⟨min (semicircleCDF E) (1 - semicircleCDF E) / 2, ?_, ?_, ?_, ?_⟩
  · exact div_pos (lt_min hF0 (by linarith)) (by norm_num)
  · have := min_le_left (semicircleCDF E) (1 - semicircleCDF E)
    have := min_le_right (semicircleCDF E) (1 - semicircleCDF E)
    linarith
  · have := min_le_left (semicircleCDF E) (1 - semicircleCDF E)
    linarith
  · have := min_le_right (semicircleCDF E) (1 - semicircleCDF E)
    linarith

/-!
### Critical-sequence asymptotics
-/

/-- Along every critical sequence with ratio `τ > 0`, eventually `n/W < T'` (for `T' > τ`),
`n/W < 2τ`, `n ≥ N₀` and `a_{n,W}/√n ≤ 2`. -/
theorem critical_eventually {τ : ℝ} (s : CriticalSequence τ) (hτ : 0 < τ) (b : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) {T' : ℝ} (hT' : τ < T') (N₀ : ℝ) :
    ∀ᶠ j in atTop, (s.n j : ℝ) / s.W j < T' ∧ (s.n j : ℝ) / s.W j < 2 * τ ∧
      N₀ ≤ (s.n j : ℝ) ∧ countScale (s.n j) (s.W j) / Real.sqrt (s.n j) ≤ 2 := by
  have h1 := s.ratio_tendsto.eventually (gt_mem_nhds hT')
  have h2 := s.ratio_tendsto.eventually (gt_mem_nhds (by linarith : τ < 2 * τ))
  have h3 := (criticalSequence_n_real_tendsto_atTop s hτ).eventually (eventually_ge_atTop N₀)
  have h4 := (BlockBand.Window.Transfer.critical_refined_scale_ratio_tendsto s hτ b hb hb').eventually
    (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [h1, h2, h3, h4] with j hj1 hj2 hj3 hj4
  exact ⟨hj1, hj2, hj3, hj4⟩

/-- Every critical marked limit is invariant under all global spectral translations. -/
theorem stationary_of_criticalLimit {τ b E : ℝ} {hb : 0 < b} {hb' : b < 1 / 2} (hτ : 0 < τ)
    (hE : E ^ 2 < 4) {P : ProbabilityMeasure MarkedPointMeasure}
    (hP : IsCriticalMarkedLimit τ b E hb hb' P) (t : ℝ) :
    globalMarkedTranslationLaw t P = P := by
  obtain ⟨s, R, φ, hφ, hlim⟩ := hP
  exact criticalSequence_marked_weakLimit_spectral_law_invariant s hτ b E hb hb' hE R φ hφ P hlim t

/-!
### Elementary algebra
-/

/-- `min(1, D x)^{1-η} ≤ D min(1, x^{1-η})` for `D ≥ 1`, `x ≥ 0`, `0 < η < 1`. -/
theorem min_rpow_le {D x η : ℝ} (hD : 1 ≤ D) (hx : 0 ≤ x) (hη : 0 < η) (hη1 : η < 1) :
    (min 1 (D * x)) ^ (1 - η) ≤ D * min 1 (x ^ (1 - η)) := by
  have he : 0 ≤ 1 - η := by linarith
  have hm0 : 0 ≤ min 1 (D * x) := le_min zero_le_one (by positivity)
  rcases le_or_gt x 1 with h | h
  · have hx1 : x ^ (1 - η) ≤ 1 := Real.rpow_le_one hx h he
    rw [min_eq_right hx1]
    calc (min 1 (D * x)) ^ (1 - η) ≤ (D * x) ^ (1 - η) :=
          Real.rpow_le_rpow hm0 (min_le_right _ _) he
      _ = D ^ (1 - η) * x ^ (1 - η) := Real.mul_rpow (by linarith) hx
      _ ≤ D ^ (1 : ℝ) * x ^ (1 - η) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hD (by linarith))
            (Real.rpow_nonneg hx _)
      _ = D * x ^ (1 - η) := by rw [Real.rpow_one]
  · have hx1 : 1 ≤ x ^ (1 - η) := Real.one_le_rpow h.le he
    rw [min_eq_left hx1, mul_one]
    calc (min 1 (D * x)) ^ (1 - η) ≤ 1 := Real.rpow_le_one hm0 (min_le_left _ _) he
      _ ≤ D := hD

end BlockBand.Window.SmallCritical
