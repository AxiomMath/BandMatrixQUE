module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Forward
public import BlockBand.SourceProcess.Stochastic.RotationFlow.BackwardODE
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The backward propagator of the rotation flow

`backwardPropagator_of_isRotationFlow`: for rotation flows `M^x` started at each `x ∈ [a, c]`,
the second moments `x ↦ E|M^x_{c-x}(k,j)|²` form a backward propagator of the mass generator.
Notation as for `secondMoment`; the coefficients `r` (continuous, symmetric, `≥ 0`) and `κ`
(continuous, `≥ 0`) are read at the clamped time.

* `exists_backwardPropagator`: a backward propagator `Q` of `massGenerator r κ` on `[a,c]` exists.
  It is obtained by time reflection: with `r̃(y) = r(a+c-y)`, `κ̃(y) = κ(a+c-y)` and a rotation
  flow `M̃` for `(r̃, κ̃)` started at `a`, `Q(x)_kl = E|M̃_{c-x}(l,k)|²`; this uses that
  `massGenerator r̃ κ̃ y = massGenerator r κ (a+c-y)` and that `massGenerator` is symmetric.
* `backwardPropagator_of_isRotationFlow`: for every family of rotation flows `Mf x` started at
  `x ∈ [a,c]`, `P(x)_kj = E|Mf_x(c-x)(k,j)|²` is a backward propagator (`backward_of_forward`
  with the forward fundamental solutions `Φ x u = m^{(x)}_{u-x}`).
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionFlow

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {N : ℕ} {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
variable {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c : ℝ}

theorem reflect_mem {a c y : ℝ} (hy : y ∈ Icc a c) : a + c - y ∈ Icc a c :=
  ⟨by linarith [hy.2], by linarith [hy.1]⟩

/-- **A backward propagator exists** (time reflection of a forward flow). -/
theorem exists_backwardPropagator (μ : Measure S) [IsProbabilityMeasure μ] (hac : a ≤ c)
    (hrc : ContinuousOn r (Icc a c)) (hκc : ContinuousOn κ (Icc a c))
    (hs : ∀ x k l, r x k l = r x l k) (hr : ∀ x k l, 0 ≤ r x k l) (hk : ∀ x k, 0 ≤ κ x k) :
    ∃ Q, BackwardPropagator (massGenerator r κ) a c Q := by
  set rr : ℝ → Fin N → Fin N → ℝ := fun y => r (a + c - y)
  set kk : ℝ → Fin N → ℝ := fun y => κ (a + c - y)
  have hmaps : MapsTo (fun y : ℝ => a + c - y) (Icc a c) (Icc a c) := fun y hy => reflect_mem hy
  have hcont : Continuous fun y : ℝ => a + c - y := continuous_const.sub continuous_id
  have hrrc : ContinuousOn rr (Icc a c) := hrc.comp hcont.continuousOn hmaps
  have hkkc : ContinuousOn kk (Icc a c) := hκc.comp hcont.continuousOn hmaps
  have hrs : ∀ x k l, rr x k l = rr x l k := fun x k l => hs _ k l
  have hrr : ∀ x k l, 0 ≤ rr x k l := fun x k l => hr _ k l
  have hkk : ∀ x k, 0 ≤ kk x k := fun x k => hk _ k
  obtain ⟨M, hM⟩ := exists_isRotationFlow (μ := μ) hac hrrc hkkc hrs hrr hkk a
  refine ⟨fun x k l => secondMoment μ M (c - x).toNNReal l k, ?_, ?_, fun x hx => ?_⟩
  · funext k l
    simp only [sub_self, Real.toNNReal_zero, secondMoment_zero hM.2, eq_comm]
  · refine Continuous.continuousOn (continuous_pi fun k => continuous_pi fun l => ?_)
    exact (continuous_secondMoment_real hrs hrr hkk hM l k).comp (continuous_const.sub continuous_id)
  · have ht₀ : 0 < c - x := sub_pos.2 hx.2
    have hcl : clampTime a c (a + ((c - x).toNNReal : ℝ)) = a + c - x := by
      rw [Real.coe_toNNReal _ ht₀.le, clampTime_of_mem ⟨by linarith [hx.2], by linarith [hx.1]⟩]
      ring
    have hgen : ∀ l p, massGenerator rr kk (a + c - x) l p = massGenerator r κ x p l := by
      intro l p
      have e : massGenerator rr kk (a + c - x) l p = massGenerator r κ (a + c - (a + c - x)) l p :=
        rfl
      rw [e, sub_sub_cancel, massGenerator_symm κ hs]
    refine hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun l => ?_
    have h := (hasDerivAt_secondMoment hac hrrc hkkc hrs hrr hkk hM l k ht₀).comp_const_sub c x
    convert h using 1
    simp only [hcl, hgen]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun p _ => ?_)
    ring

/-- **Backward propagator of the rotation flow.** -/
theorem backwardPropagator_of_isRotationFlow (hac : a ≤ c) (hrc : ContinuousOn r (Icc a c))
    (hκc : ContinuousOn κ (Icc a c)) (hs : ∀ x k l, r x k l = r x l k)
    (hr : ∀ x k l, 0 ≤ r x k l) (hk : ∀ x k, 0 ≤ κ x k)
    (Mf : ℝ → ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ)
    (hMf : ∀ x ∈ Icc a c, IsRotationFlow μ r κ a c x (Mf x)) :
    BackwardPropagator (massGenerator r κ) a c (fun x k j =>
      ∫ ω, ‖Mf x (c - x).toNNReal ω k j‖ ^ 2 ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) := by
  obtain ⟨Q, hQ⟩ := exists_backwardPropagator μ hac hrc hκc hs hr hk
  have h := backward_of_forward hac (Φ := fun x u k j => secondMoment μ (Mf x) (u - x).toNNReal k j)
    (fun x hx => by
      funext k l
      simp only [sub_self, Real.toNNReal_zero, secondMoment_zero (hMf x hx).2])
    (fun x hx => Continuous.continuousOn (continuous_pi fun k => continuous_pi fun j =>
      (continuous_secondMoment_real hs hr hk (hMf x hx) k j).comp (continuous_sub_right x)))
    (fun x hx u hu => by
      have ht₀ : 0 < u - x := sub_pos.2 hu.1
      have huI : u ∈ Icc a c := ⟨hx.1.trans hu.1.le, hu.2.le⟩
      have hcl : clampTime a c (x + ((u - x).toNNReal : ℝ)) = u := by
        rw [Real.coe_toNNReal _ ht₀.le, add_sub_cancel, clampTime_of_mem huI]
      refine hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun j => ?_
      have h := (hasDerivAt_secondMoment hac hrc hκc hs hr hk (hMf x hx) k j ht₀).comp_sub_const
        u x
      convert h using 1
      simp only [hcl]) hQ
  exact h

end BlockBand.SourceProcess.Stochastic.RotationFlow
