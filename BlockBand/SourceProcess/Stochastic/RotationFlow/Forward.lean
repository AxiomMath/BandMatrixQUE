module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.MassEq
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The forward mass equation

Notation as for `secondMoment`; `M` a rotation flow started at `s`.

* `hasDerivAt_secondMoment`: for `t₀ > 0`, `u ↦ m_{u⁺}(k,j)` has derivative
  `∑_l L(t₀)_kl m_{t₀}(l,j)` at `t₀` (fundamental theorem of calculus applied to the integrated
  mass equation `secondMoment_eq`, whose integrand is continuous).
* `forwardMassSolution_of_isRotationFlow`: for `s ∈ [a,c]` and every `v₀`,
  `v_k(x) = E ∑_j |M_{x-s}(k,j)|² v₀_j` solves `ForwardMassSolution (massGenerator r κ) s c v₀`.
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionFlow

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {N : ℕ} {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
variable {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c s : ℝ}

theorem continuous_secondMoment_real (hs : ∀ x k l, r x k l = r x l k)
    (hr : ∀ x k l, 0 ≤ r x k l) (hk : ∀ x k, 0 ≤ κ x k)
    {M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ} (hM : IsRotationFlow μ r κ a c s M)
    (k j : Fin N) : Continuous fun u : ℝ => secondMoment μ M u.toNNReal k j :=
  (continuous_secondMoment hM.1.adapted hM.1.continuous (isRotationFlow_norm_le hs hr hk hM)
    k j).comp continuous_real_toNNReal

section
variable (hac : a ≤ c) (hrc : ContinuousOn r (Set.Icc a c))
  (hκc : ContinuousOn κ (Set.Icc a c)) (hs : ∀ x k l, r x k l = r x l k)
  (hr : ∀ x k l, 0 ≤ r x k l) (hk : ∀ x k, 0 ≤ κ x k)
  {M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ} (hM : IsRotationFlow μ r κ a c s M)
include hac hrc hκc hs hr hk hM

/-- **Derivative of the second moments** at positive flow times. -/
theorem hasDerivAt_secondMoment (k j : Fin N) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun u : ℝ => secondMoment μ M u.toNNReal k j)
      (∑ l, massGenerator r κ (clampTime a c (s + t₀.toNNReal)) k l *
        secondMoment μ M t₀.toNNReal l j) t₀ := by
  set f : ℝ → ℝ := fun u => ∑ l, massGenerator r κ (clampTime a c (s + u.toNNReal)) k l *
    secondMoment μ M u.toNNReal l j with hfdef
  have hL := continuous_clamped hac (continuousOn_massGenerator hrc hκc) s
  have hf : Continuous f := by
    refine continuous_finsetSum _ fun l _ => ?_
    have h1 : Continuous fun u : ℝ => massGenerator r κ (clampTime a c (s + u.toNNReal)) k l :=
      (continuous_apply l).comp ((continuous_apply k).comp (hL.comp continuous_real_toNNReal))
    exact h1.mul (continuous_secondMoment_real hs hr hk hM l j)
  have hder : HasDerivAt (fun u => (if k = j then (1 : ℝ) else 0) + ∫ v in (0 : ℝ)..u, f v)
      (f t₀) t₀ :=
    (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt).const_add _
  refine hder.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht₀] with u hu
  rw [secondMoment_eq hac hrc hκc hs hr hk hM, Real.coe_toNNReal _ (le_of_lt hu),
    intervalIntegral.integral_of_le (le_of_lt hu)]

end

/-- **Forward mass equation of the rotation flow.** -/
theorem forwardMassSolution_of_isRotationFlow (hac : a ≤ c) (hrc : ContinuousOn r (Set.Icc a c))
    (hκc : ContinuousOn κ (Set.Icc a c)) (hs : ∀ x k l, r x k l = r x l k)
    (hr : ∀ x k l, 0 ≤ r x k l) (hk : ∀ x k, 0 ≤ κ x k) (hsI : s ∈ Set.Icc a c)
    {M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ} (hM : IsRotationFlow μ r κ a c s M)
    (v₀ : Fin N → ℝ) :
    ForwardMassSolution (massGenerator r κ) s c v₀ (fun x k =>
      ∫ ω, ∑ j, ‖M (x - s).toNNReal ω k j‖ ^ 2 * v₀ j
        ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) := by
  have hb := isRotationFlow_norm_le hs hr hk hM
  have hV : (fun x k => ∫ ω, ∑ j, ‖M (x - s).toNNReal ω k j‖ ^ 2 * v₀ j
      ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) =
      fun x k => ∑ j, secondMoment μ M (x - s).toNNReal k j * v₀ j := by
    funext x k
    rw [integral_finsetSum _ fun j _ => (integrable_entry_sq hM.1.adapted hb _ k j).mul_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_mul_const _ _
  rw [hV]
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · funext k
    simp only [sub_self, Real.toNNReal_zero, secondMoment_zero hM.2, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · refine Continuous.continuousOn (continuous_pi fun k => continuous_finsetSum _ fun j _ => ?_)
    exact ((continuous_secondMoment_real hs hr hk hM k j).comp
      (continuous_sub_right s)).mul continuous_const
  · have ht₀ : 0 < x - s := sub_pos.2 hx.1
    have hxI : x ∈ Set.Icc a c := ⟨hsI.1.trans hx.1.le, hx.2.le⟩
    have hcl : clampTime a c (s + ((x - s).toNNReal : ℝ)) = x := by
      rw [Real.coe_toNNReal _ ht₀.le, add_sub_cancel, clampTime_of_mem hxI]
    refine hasDerivAt_pi.2 fun k => ?_
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      ((hasDerivAt_secondMoment hac hrc hκc hs hr hk hM k j ht₀).comp_sub_const x s).mul_const
        (v₀ j)
    convert h using 1
    simp only [hcl, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring

end BlockBand.SourceProcess.Stochastic.RotationFlow
