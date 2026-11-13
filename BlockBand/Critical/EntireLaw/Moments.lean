module

public import BlockBand.Internal.Contracts.CriticalEntire

/-!
# The entire law: passage of the mixed inverse moments to weak limits

On laws whose inverse values on the positive imaginary cone lie in the closed unit disk, the mixed
inverse moments are integrals of the bounded continuous test `momentTest`
(`mixedInverseMoment_eq_integral`), hence pass to weak limits (`tendsto_mixedInverseMoment`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CriticalEntire
open scoped ComplexConjugate

/-- Bounded continuous extension of the factor `w ↦ w⁻¹` (`σ = 1`) or `conj(w⁻¹)` (`σ = -1`)
from `{|w| ≥ 1}` to `ℂ`: `conj w / max(1,|w|²)`, resp. `w / max(1,|w|²)`. -/
def clampFactor (σ : ℤˣ) (w : ℂ) : ℂ :=
  (if σ = 1 then conj w else w) / ((max 1 (‖w‖ ^ 2) : ℝ) : ℂ)

theorem clampFactor_eq {σ : ℤˣ} {w : ℂ} (hw : 1 ≤ ‖w‖) : clampFactor σ w = mixedInverseFactor σ w := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; linarith
  have hmax : max 1 (‖w‖ ^ 2) = ‖w‖ ^ 2 := max_eq_right (by nlinarith)
  unfold clampFactor mixedInverseFactor
  rw [hmax]
  have hn : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn]
  have hc : conj w ≠ 0 := (map_ne_zero _).mpr hw0
  split_ifs
  · field_simp
  · rw [map_inv₀]; field_simp

theorem continuous_clampFactor (σ : ℤˣ) : Continuous (clampFactor σ) := by
  unfold clampFactor
  refine Continuous.div ?_ (Complex.continuous_ofReal.comp
    (continuous_const.max (continuous_norm.pow 2))) fun w => ?_
  · split_ifs
    · exact Complex.continuous_conj
    · exact continuous_id
  · rw [Complex.ofReal_ne_zero]
    exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'

theorem norm_clampFactor_le (σ : ℤˣ) (w : ℂ) : ‖clampFactor σ w‖ ≤ 1 := by
  unfold clampFactor
  have hm : 0 < max 1 (‖w‖ ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hm.le, div_le_one hm]
  have hnum : ‖(if σ = 1 then conj w else w)‖ = ‖w‖ := by split_ifs <;> simp
  rw [hnum]
  by_cases h : ‖w‖ ≤ 1
  · exact h.trans (le_max_left _ _)
  · push Not at h
    exact (by nlinarith : ‖w‖ ≤ ‖w‖ ^ 2).trans (le_max_right _ _)

/-- The bounded continuous test `F ↦ Π_j clampFactor σ_j (F(i y^{(j)}))` on entire functions. -/
def momentTest {m J : ℕ} (y : Fin J → Fin m → ℝ) (σ : Fin J → ℤˣ) :
    BoundedContinuousFunction (EntireFunction m) ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun F => ∏ j, clampFactor (σ j) (F (conePoint (y j))),
      continuous_finsetProd _ fun j _ =>
        (continuous_clampFactor (σ j)).comp (EntireFunction.continuous_eval_const _)⟩ 2
    (fun F G => by
      have h : ∀ F : EntireFunction m, ‖∏ j, clampFactor (σ j) (F (conePoint (y j)))‖ ≤ 1 :=
        fun F => by
          rw [norm_prod]
          exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => norm_clampFactor_le _ _
      simp only [ContinuousMap.coe_mk]
      rw [dist_eq_norm]
      calc _ ≤ _ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (h F) (h G)
        _ = 2 := by norm_num)

/-- On cone-bounded laws the mixed inverse moment is the integral of the bounded test. -/
theorem mixedInverseMoment_eq_integral {m J : ℕ} {μ : RandomEntire m} (hμ : HasInverseConeBound μ)
    (y : Fin J → Fin m → ℝ) (σ : Fin J → ℤˣ) (hy : ∀ j a, 0 ≤ y j a) :
    mixedInverseMoment μ y σ = ∫ F, momentTest y σ F ∂(μ : Measure (EntireFunction m)) := by
  unfold mixedInverseMoment
  refine integral_congr_ae ?_
  have hall : ∀ᵐ F ∂(μ : Measure (EntireFunction m)), ∀ j, 1 ≤ ‖F (conePoint (y j))‖ :=
    ae_all_iff.mpr fun j => hμ (y j) (hy j)
  filter_upwards [hall] with F hF
  simp only [momentTest, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
  exact Finset.prod_congr rfl fun j _ => (clampFactor_eq (hF j)).symm

/-- **Moments pass to weak limits on cone-bounded laws** (bounded moment
convergence), along any filter. -/
theorem tendsto_mixedInverseMoment {m J : ℕ} {ι : Type*} {L : Filter ι}
    {μs : ι → RandomEntire m} {μ : RandomEntire m} (h : Tendsto μs L (𝓝 μ))
    (hμs : ∀ i, HasInverseConeBound (μs i)) (hμ : HasInverseConeBound μ)
    (y : Fin J → Fin m → ℝ) (σ : Fin J → ℤˣ) (hy : ∀ j a, 0 ≤ y j a) :
    Tendsto (fun i => mixedInverseMoment (μs i) y σ) L (𝓝 (mixedInverseMoment μ y σ)) := by
  simp_rw [mixedInverseMoment_eq_integral (hμs _) y σ hy, mixedInverseMoment_eq_integral hμ y σ hy]
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h _

end BlockBand.Critical.EntireLaw
