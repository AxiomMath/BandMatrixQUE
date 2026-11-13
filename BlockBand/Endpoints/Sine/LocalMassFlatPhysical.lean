module

public import BlockBand.Endpoints.Sine.LocalMassFlatDefs
public import BlockBand.QUE.Fourier.PhysicalWeightedMass

/-!
# The physical side of strong local mass flatness

* `lmf_minOne`: the bounded test `x ↦ min(x, 1)` on `[0,∞)`.
* `lmf_blockFlatness_eq` (the one-block identity): with `x = n p_{αk} ≥ 0`, the identity
  `|x - 1| = x + 1 - 2 min(x, 1)` and the exact cyclic identity
  `E Σ_α w(u_α) n p_{αk} = E Σ_α w(u_α)` (`canonical_weighted_mass_identity`, from the cyclic
  law), `E Σ_α w(u_α)|n p_{αk} - 1| = 2 E Σ_α w(u_α) - 2 E Σ_α w(u_α) min(n p_{αk}, 1)`, for `w`
  continuous with compact support (possibly signed).
* `lmf_pairFlatness_le` (the pair): for `w ≥ 0`, the pair statistic is at most the average of the
  two block statistics, since `(n/2)‖P_Sψ‖² - 1 = ((n p_i - 1) + (n p_{i+1} - 1))/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.Clocks
open scoped BoundedContinuousFunction ENNReal

/-!
## The bounded test `min(x, 1)`
-/

/-- `x ↦ min(x, 1)` as a bounded continuous function on `[0,∞)`. -/
def lmf_minOne : Set.Ici (0 : ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (x : ℝ) 1, by fun_prop⟩ 1 (by
      intro x y
      have hx : (0 : ℝ) ≤ x := x.2
      have hy : (0 : ℝ) ≤ y := y.2
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]
      have h1 := min_le_right (x : ℝ) 1
      have h2 : (0 : ℝ) ≤ min (y : ℝ) 1 := le_min hy zero_le_one
      have h3 := min_le_right (y : ℝ) 1
      have h4 : (0 : ℝ) ≤ min (x : ℝ) 1 := le_min hx zero_le_one
      constructor <;> linarith)

@[simp] theorem lmf_minOne_apply (x : Set.Ici (0 : ℝ)) : lmf_minOne x = min (x : ℝ) 1 := rfl

/-- On a nonnegative argument the clamp is the identity. -/
theorem lmf_minOne_projIci {y : ℝ} (hy : 0 ≤ y) : lmf_minOne (Set.projIci 0 y) = min y 1 := by
  rw [lmf_minOne_apply, Set.coe_projIci, max_eq_right hy]

/-- `|x - 1| = x + 1 - 2 min(x, 1)` (for every real `x`). -/
theorem lmf_abs_sub_one_eq (x : ℝ) : |x - 1| = x + 1 - 2 * min x 1 := by
  rcases le_total x 1 with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- The clamp `y ↦ projIci 0 y` is continuous. -/
theorem lmf_continuous_projIci_zero : Continuous (fun y : ℝ => Set.projIci (0 : ℝ) y) :=
  continuous_induced_rng.2 (by
    simpa [Function.comp_def, Set.coe_projIci] using (continuous_const.max continuous_id :
      Continuous fun y : ℝ => max 0 y))

/-!
## Integrability
-/

section Integrability

variable (p : Parameters) (model : p.GaussianRingModel) (E : ℝ) (w : ℝ → ℝ)

theorem lmf_measurable_window_eig (hw : Continuous w) (α : Fin p.N) :
    Measurable (fun H : p.SiteMatrix => w (microCoord p E (physicalOrderedEigenvalue p H α))) := by
  unfold microCoord
  exact hw.measurable.comp (measurable_const.mul
    ((measurable_physicalOrderedEigenvalue p α).sub measurable_const))

theorem lmf_window_eig_eq (α : Fin p.N) (H : p.SiteMatrix) :
    w (microCoord p E (physicalOrderedEigenvalue p H α)) =
      w (BlockBand.QUE.Fourier.canonicalMicroscopic p E α H) := rfl

theorem lmf_integrable_window_eig (hw : Continuous w) (hwc : HasCompactSupport w)
    (α : Fin p.N) :
    Integrable (fun H : p.SiteMatrix => w (microCoord p E (physicalOrderedEigenvalue p H α)))
      (model.law : Measure p.SiteMatrix) := by
  obtain ⟨M, hM⟩ := hw.bounded_above_of_compact_support hwc
  exact BlockBand.QUE.Fourier.integrable_canonicalMicroscopic_test p model E α w hw.measurable M
    (fun u => by simpa [Real.norm_eq_abs] using hM u)

theorem lmf_integrable_window_mass (hw : Continuous w) (hwc : HasCompactSupport w)
    (α : Fin p.N) (k : ZMod p.n) :
    Integrable (fun H : p.SiteMatrix => w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      physicalOrderedBlockMass p H α k) (model.law : Measure p.SiteMatrix) := by
  obtain ⟨M, hM⟩ := hw.bounded_above_of_compact_support hwc
  exact BlockBand.QUE.Fourier.integrable_canonicalWeightedMass p model E α k w hw.measurable M
    (fun u => by simpa [Real.norm_eq_abs] using hM u)

theorem lmf_integrable_window_test (hw : Continuous w) (hwc : HasCompactSupport w)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (α : Fin p.N) (k : ZMod p.n) :
    Integrable (fun H : p.SiteMatrix => w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      Φ (Set.projIci 0 ((p.n : ℝ) * physicalOrderedBlockMass p H α k)))
      (model.law : Measure p.SiteMatrix) := by
  have hm : Measurable (fun H : p.SiteMatrix =>
      Φ (Set.projIci 0 ((p.n : ℝ) * physicalOrderedBlockMass p H α k))) :=
    Φ.continuous.measurable.comp (lmf_continuous_projIci_zero.measurable.comp
      (measurable_const.mul (measurable_physicalOrderedBlockMass p α k)))
  refine ((lmf_integrable_window_eig p model E w hw hwc α).norm.mul_const ‖Φ‖).mono'
    ((lmf_measurable_window_eig p E w hw α).mul hm).aestronglyMeasurable
    (Eventually.of_forall fun H => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (Φ.norm_coe_le_norm _) (norm_nonneg _)

/-- The block-flatness integrand, as an integrable combination. -/
theorem lmf_blockIntegrand_eq (k : ZMod p.n) (H : p.SiteMatrix) :
    (∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
        |(p.n : ℝ) * physicalOrderedBlockMass p H α k - 1|) =
      (p.n : ℝ) * (∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
          physicalOrderedBlockMass p H α k) +
        (∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α))) -
        2 * ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
          lmf_minOne (Set.projIci 0 ((p.n : ℝ) * physicalOrderedBlockMass p H α k)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hx : 0 ≤ (p.n : ℝ) * physicalOrderedBlockMass p H α k :=
    mul_nonneg (Nat.cast_nonneg _) (physicalOrderedBlockMass_nonneg p H α k)
  rw [lmf_minOne_projIci hx, lmf_abs_sub_one_eq]
  ring

theorem lmf_integrable_blockIntegrand (hw : Continuous w) (hwc : HasCompactSupport w)
    (k : ZMod p.n) :
    Integrable (fun H : p.SiteMatrix => ∑ α : Fin p.N,
      w (microCoord p E (physicalOrderedEigenvalue p H α)) *
        |(p.n : ℝ) * physicalOrderedBlockMass p H α k - 1|) (model.law : Measure p.SiteMatrix) := by
  simp_rw [lmf_blockIntegrand_eq p E w k]
  refine (((integrable_finsetSum _ fun α _ =>
      lmf_integrable_window_mass p model E w hw hwc α k).const_mul _).add
    (integrable_finsetSum _ fun α _ => lmf_integrable_window_eig p model E w hw hwc α)).sub
    ((integrable_finsetSum _ fun α _ =>
      lmf_integrable_window_test p model E w hw hwc lmf_minOne α k).const_mul _)

end Integrability

/-!
## The one-block identity
-/

/-- The one-block identity in the proof of local mass flatness:
`E Σ_α w(u_α)|n p_{αk} - 1| = 2 E Σ_α w(u_α) - 2 E Σ_α w(u_α) min(n p_{αk}, 1)`. Physical law,
every admissible `p`, model, real `E`, block `k`; `w` continuous with compact support. -/
theorem lmf_blockFlatness_eq (p : Parameters) (model : p.GaussianRingModel) (E : ℝ)
    (w : ℝ → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) (k : ZMod p.n) :
    lmf_blockFlatness p model E w k =
      2 * (∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α))
          ∂(model.law : Measure p.SiteMatrix)) -
        2 * lmf_physicalTagSide p model E w lmf_minOne k := by
  obtain ⟨M, hM⟩ := hw.bounded_above_of_compact_support hwc
  have hM' : ∀ u, |w u| ≤ M := fun u => by simpa [Real.norm_eq_abs] using hM u
  have hA := integrable_finsetSum (s := (Finset.univ : Finset (Fin p.N))) fun α _ =>
    lmf_integrable_window_mass p model E w hw hwc α k
  have hB := integrable_finsetSum (s := (Finset.univ : Finset (Fin p.N))) fun α _ =>
    lmf_integrable_window_eig p model E w hw hwc α
  have hC := integrable_finsetSum (s := (Finset.univ : Finset (Fin p.N))) fun α _ =>
    lmf_integrable_window_test p model E w hw hwc lmf_minOne α k
  have hlin : (∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
        physicalOrderedBlockMass p H α k ∂(model.law : Measure p.SiteMatrix)) =
      (p.n : ℝ)⁻¹ * ∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α))
        ∂(model.law : Measure p.SiteMatrix) := by
    rw [integral_finsetSum _ fun α _ => lmf_integrable_window_mass p model E w hw hwc α k,
      integral_finsetSum _ fun α _ => lmf_integrable_window_eig p model E w hw hwc α,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact BlockBand.QUE.Fourier.canonical_weighted_mass_identity p model E α k w hw.measurable M hM'
  unfold lmf_blockFlatness lmf_physicalTagSide
  simp_rw [lmf_blockIntegrand_eq p E w k]
  have hAB : Integrable (fun H : p.SiteMatrix => (p.n : ℝ) * (∑ α : Fin p.N,
      w (microCoord p E (physicalOrderedEigenvalue p H α)) * physicalOrderedBlockMass p H α k) +
      ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)))
      (model.law : Measure p.SiteMatrix) := (hA.const_mul _).add hB
  rw [integral_sub hAB (hC.const_mul _), integral_add (hA.const_mul _) hB,
    integral_const_mul, integral_const_mul, hlin, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne p.n)), one_mul]
  ring

/-!
## The pair
-/

/-- `|(n/2)(a + b) - 1| ≤ (|na - 1| + |nb - 1|)/2`. -/
theorem lmf_abs_pair_le (n a b : ℝ) : |n / 2 * (a + b) - 1| ≤ (|n * a - 1| + |n * b - 1|) / 2 := by
  have : n / 2 * (a + b) - 1 = ((n * a - 1) + (n * b - 1)) / 2 := by ring
  rw [this, abs_div, abs_two]
  exact div_le_div_of_nonneg_right (abs_add_le _ _) zero_le_two

/-- The pair bound in the proof of local mass flatness: for `w ≥ 0` continuous with compact
support, the pair statistic of `S = {i, i+1}` is at most the average of the two one-block
statistics. Physical law, every admissible `p`, model, real `E`. -/
theorem lmf_pairFlatness_le (p : Parameters) (model : p.GaussianRingModel) (E : ℝ) (w : ℝ → ℝ)
    (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ u, 0 ≤ w u) (i : ZMod p.n) :
    lmf_pairFlatness p model E w i ≤
      (lmf_blockFlatness p model E w i + lmf_blockFlatness p model E w (i + 1)) / 2 := by
  have hi := lmf_integrable_blockIntegrand p model E w hw hwc i
  have hi1 := lmf_integrable_blockIntegrand p model E w hw hwc (i + 1)
  unfold lmf_pairFlatness lmf_blockFlatness
  rw [← integral_add hi hi1, ← integral_div]
  refine integral_mono_of_nonneg (Eventually.of_forall fun H => ?_) ((hi.add hi1).div_const 2)
    (Eventually.of_forall fun H => ?_)
  · exact Finset.sum_nonneg fun α _ => mul_nonneg (hw0 _) (abs_nonneg _)
  · dsimp only
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun α _ => ?_
    have h := lmf_abs_pair_le (p.n : ℝ) (physicalOrderedBlockMass p H α i)
      (physicalOrderedBlockMass p H α (i + 1))
    unfold BlockBand.Internal.Contracts.CoareaPalm.pairMass
    calc _ ≤ w (microCoord p E (physicalOrderedEigenvalue p H α)) *
          ((|(p.n : ℝ) * physicalOrderedBlockMass p H α i - 1| +
            |(p.n : ℝ) * physicalOrderedBlockMass p H α (i + 1) - 1|) / 2) :=
          mul_le_mul_of_nonneg_left h (hw0 _)
      _ = _ := by ring

end BlockBand.Endpoints
