module
public import BlockBand.SourceProcess.Stochastic.Representation.Integrator
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Integrating a stopped unit coordinate; matrix identities

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, `h : IsL2IntegratorVec Q 𝓖 Z a`
(finite index `ι`), horizon `T`, a raw stopping time `τ`.

* `contIntegral_zero_ae`: `∫_0^· 0 dN = 0` a.s. for all times.
* **`vecCont_unitStop`**: integrating the vector integrand `1_{[[0,τ]]} e_{j₀}` gives
  `Z^{j₀}_{t ∧ τ} - Z^{j₀}_0`, a.s. for all `t ≤ T`.
* `stopTime_stopTime`: stopping twice at the same time.
* `inv_cov_inv`: `∑_{ij} (A⁻¹)_{ki} (A⁻¹)_{lj} (A Aᵀ)_{ij} = δ_{kl}` for invertible `A`;
  `mul_inv_entry`: `∑_k A_{ik} (A⁻¹)_{kj} = δ_{ij}`.
-/

namespace BlockBand.SourceProcess.Stochastic.Representation
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

theorem stopTime_stopTime (e : WithTop ℝ≥0) (t : ℝ≥0) :
    stopTime e (stopTime e t) = stopTime e t := by
  have h1 : ((stopTime e t : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) e := coe_untopA_min t e
  show ((min ((stopTime e t : ℝ≥0) : WithTop ℝ≥0) e).untopA : ℝ≥0) = stopTime e t
  apply WithTop.coe_injective
  rw [coe_untopA_min, h1, min_assoc, min_self]

theorem inv_cov_inv {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : IsUnit A.det) (k l : Fin d) :
    ∑ i, ∑ j, A⁻¹ k i * A⁻¹ l j * (A * A.transpose) i j = if k = l then 1 else 0 := by
  have hAt : IsUnit A.transpose.det := by rwa [Matrix.det_transpose]
  have e : A⁻¹ * (A * A.transpose) * A⁻¹.transpose = 1 := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA, Matrix.one_mul,
      Matrix.transpose_nonsing_inv, Matrix.mul_nonsing_inv _ hAt]
  have e2 := congrFun (congrFun e k) l
  rw [Matrix.one_apply] at e2
  rw [← e2]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem mul_inv_entry {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : IsUnit A.det) (i j : Fin d) :
    ∑ k, A i k * A⁻¹ k j = if i = j then 1 else 0 := by
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv A hA) i) j
  rw [Matrix.one_apply, Matrix.mul_apply] at e
  exact e

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ}

theorem contIntegral_zero_ae {N α : ℝ≥0 → Ω → ℝ} (hN : IsL2Integrator Q 𝓖 N α) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q, ∀ t, hN.contIntegral T 0 t ω = 0 := by
  refine ae_forall_eq_of_continuous (Y := fun _ _ => 0) (hN.contIntegral_continuous T 0)
    (ae_of_all _ fun _ => continuous_const) fun t => ?_
  have e := hN.contIntegral_elem T 0 t
  rw [map_zero] at e
  refine e.trans (Eventually.of_forall fun ω => ?_)
  simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : ι → ℝ≥0 → Ω → ℝ}
  {a : ι → ι → ℝ≥0 → Ω → ℝ}

omit [Fintype ι] in
/-- The stopped unit coordinate `1_{[[0,τ]]} e_{j₀}` as a bounded predictable vector integrand. -/
theorem isBddPred_unitStop {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (j₀ j : ι) :
    IsBddPred 𝓖 fun p => if j = j₀ then (stopSet τ).indicator (fun _ => (1 : ℝ)) p else 0 := by
  by_cases hj : j = j₀
  · simp only [hj, ite_true]
    exact (IsBddPred.const 1).indicator (measurableSet_stopSet 𝓖 hτ)
  · simp only [hj, ite_false]
    exact IsBddPred.const 0

/-- **Integrating the stopped unit coordinate**: `∫_0^t 1_{[[0,τ]]} e_{j₀} dZ = Z^{j₀}_{t∧τ} -
Z^{j₀}_0`, a.s. for all `t ≤ T`. -/
theorem vecCont_unitStop (h : IsL2IntegratorVec Q 𝓖 Z a) (T : ℝ≥0)
    [IsFiniteMeasure (barMeasure Q a T)] {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (j₀ : ι) :
    ∀ᵐ ω ∂Q, ∀ t ≤ T, h.vecCont T (fun j => bpL2 _ (isBddPred_unitStop hτ j₀ j)) t ω =
      Z j₀ (stopTime (τ ω) t) ω - Z j₀ 0 ω := by
  set μ := barMeasure Q a T
  have hS := measurableSet_stopSet 𝓖 hτ
  -- the zero coordinates
  have hzero (j : ι) (hj : j ≠ j₀) : bpL2 μ (isBddPred_unitStop hτ j₀ j) = 0 := by
    refine predL2_ext 𝓖 ?_
    filter_upwards [bpL2_coeFn (μ := μ) (isBddPred_unitStop hτ j₀ j), Lp.coeFn_zero ℝ 2 μ]
      with p h1 h2
    rw [h1]
    simp only [hj, ite_false]
    exact h2.symm
  -- the active coordinate
  have hone : bpL2 μ (isBddPred_unitStop hτ j₀ j₀) =
      predInd 𝓖 (stopSet τ) hS (bpL2 μ (IsBddPred.const (𝓖 := 𝓖) 1)) := by
    rw [← bpL2_indicator]
    exact bpL2_congr _ _ (Eventually.of_forall fun p => by simp)
  let r₀ : Rect 𝓖 T := ⟨0, T, univ, zero_le, le_rfl, MeasurableSet.univ⟩
  have hrestr : h.restr T j₀ (bpL2 μ (IsBddPred.const (𝓖 := 𝓖) 1)) =
      (h.coord j₀).integrandLin T (Finsupp.single r₀ 1) := by
    refine predL2_ext 𝓖 ?_
    filter_upwards [h.restr_coeFn T j₀ (bpL2 μ (IsBddPred.const (𝓖 := 𝓖) 1)),
      (bpL2_coeFn (μ := μ) (IsBddPred.const (𝓖 := 𝓖) 1)).filter_mono
        (ae_mono (h.coord_le_bar T j₀)),
      integrandLin_ae (h.coord j₀) (Finsupp.single r₀ 1),
      IsL2Integrator.bracketMeasure_ae_mem Q (a j₀ j₀) T] with p h1 h2 h3 h4
    rw [h1, h2, h3, elemFun_single]
    have hp : p ∈ r₀.set := by
      simp only [Rect.set, r₀, mem_prod, mem_univ, and_true, NNReal.coe_zero]; exact h4
    simp [indicator_of_mem hp]
  set F := (h.coord j₀).integrandLin T (Finsupp.single r₀ 1)
  have hF : ∀ᵐ ω ∂Q, ∀ v, (h.coord j₀).contIntegral T F v ω =
      Z j₀ (min v T) ω - Z j₀ 0 ω := by
    refine ae_forall_eq_of_continuous ((h.coord j₀).contIntegral_continuous T F) ?_ fun v => ?_
    · filter_upwards [(h.coord j₀).continuous] with ω hω
      exact (hω.comp (continuous_id.min continuous_const)).sub continuous_const
    · refine ((h.coord j₀).contIntegral_elem T _ v).trans (Eventually.of_forall fun ω => ?_)
      simp [elemProc_apply, rectProc, r₀, Rect.clamp]
  have hstop := (h.coord j₀).contIntegral_predInd_stopSet_all T F hτ
  have hz (j : ι) : ∀ᵐ ω ∂Q, ∀ t, (h.coord j).contIntegral T (h.restr T j 0) t ω = 0 := by
    rw [map_zero]; exact contIntegral_zero_ae (h.coord j) T
  filter_upwards [hF, hstop, ae_all_iff.2 hz] with ω h1 h2 h3 t ht
  simp only [IsL2IntegratorVec.vecCont]
  rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [hzero j hj]; exact h3 j t)
    (by simp), hone, restr_predInd, hrestr, h2 t, stoppedProcess_eq_stopTime, h1,
    min_eq_left ((stopTime_le _ _).trans ht)]

end BlockBand.SourceProcess.Stochastic.Representation
