module

public import BlockBand.SourceProcess.Stochastic.Dyson.ItoIdentities

/-!
# Dyson Brownian motion: continuity of the characteristics and additivity of the Itô drift

* `continuousAt_dysonStateDrift`, `continuousAt_dysonStateCov`: the characteristics are continuous
  at every state with pairwise distinct eigenvalue coordinates;
* `continuousOn_drift_state`, `continuousOn_cov_state`: hence continuous in `H` on simple spectrum;
* `itoDrift_dysonState_add`: the Itô drift of `ψ_k + ψ_l` is `b_k + b_l`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix Filter Topology
open scoped Matrix NNReal
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

theorem continuousAt_coupling {y : Fin (N + N) → ℝ} {i j : Fin N}
    (hN : (N : ℝ) ≠ 0) (hij : y (finSumFinEquiv (Sum.inl i)) ≠ y (finSumFinEquiv (Sum.inl j))) :
    ContinuousAt (fun y : Fin (N + N) → ℝ =>
      dysonCoupling N (fun a => y (finSumFinEquiv (Sum.inl a))) i j) y := by
  unfold dysonCoupling
  have hc : Continuous fun y : Fin (N + N) → ℝ =>
      (y (finSumFinEquiv (Sum.inl i)) - y (finSumFinEquiv (Sum.inl j))) ^ 2 := by fun_prop
  refine continuousAt_const.div (continuousAt_const.mul hc.continuousAt) ?_
  exact mul_ne_zero hN (pow_ne_zero 2 (sub_ne_zero.mpr hij))

theorem continuousAt_dysonStateDrift {y : Fin (N + N) → ℝ}
    (hy : ∀ i j : Fin N, i ≠ j →
      y (finSumFinEquiv (Sum.inl i)) ≠ y (finSumFinEquiv (Sum.inl j))) :
    ContinuousAt (dysonStateDrift N) y := by
  refine continuousAt_pi.2 fun k => ?_
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with i | i
  · have e : (fun y => dysonStateDrift N y (finSumFinEquiv (Sum.inl i))) =
        fun y => dysonDrift N (fun a => y (finSumFinEquiv (Sum.inl a))) i := by
      funext y; exact dysonStateDrift_inl y i
    rw [e]
    unfold dysonDrift
    refine continuousAt_const.mul (tendsto_finsetSum _ fun j hj => ?_)
    have hc : Continuous fun y : Fin (N + N) → ℝ =>
        y (finSumFinEquiv (Sum.inl i)) - y (finSumFinEquiv (Sum.inl j)) := by fun_prop
    exact continuousAt_const.div hc.continuousAt
      (sub_ne_zero.mpr (hy i j (Finset.ne_of_mem_erase hj).symm))
  · have hN : (N : ℝ) ≠ 0 := by have := Fin.pos i; positivity
    have e : (fun y => dysonStateDrift N y (finSumFinEquiv (Sum.inr i))) =
        fun y => ∑ j ∈ Finset.univ.erase i, dysonCoupling N (fun a => y (finSumFinEquiv (Sum.inl a)))
          i j * (y (finSumFinEquiv (Sum.inr j)) - y (finSumFinEquiv (Sum.inr i))) := by
      funext y; exact dysonStateDrift_inr y i
    rw [e]
    refine tendsto_finsetSum _ fun j hj => ?_
    have hc : Continuous fun y : Fin (N + N) → ℝ =>
        y (finSumFinEquiv (Sum.inr j)) - y (finSumFinEquiv (Sum.inr i)) := by fun_prop
    exact (continuousAt_coupling hN (hy i j (Finset.ne_of_mem_erase hj).symm)).mul hc.continuousAt

theorem continuousAt_dysonStateCov {y : Fin (N + N) → ℝ}
    (hy : ∀ i j : Fin N, i ≠ j →
      y (finSumFinEquiv (Sum.inl i)) ≠ y (finSumFinEquiv (Sum.inl j))) :
    ContinuousAt (dysonStateCov N) y := by
  refine continuousAt_pi.2 fun k => continuousAt_pi.2 fun l => ?_
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  obtain ⟨l, rfl⟩ := finSumFinEquiv.surjective l
  rcases k with i | i <;> rcases l with j | j
  · simp_rw [dysonStateCov_inl_inl]; exact continuousAt_const
  · simp_rw [dysonStateCov_inl_inr]; exact continuousAt_const
  · simp_rw [dysonStateCov_inr_inl]; exact continuousAt_const
  · have hN : (N : ℝ) ≠ 0 := by have := Fin.pos i; positivity
    simp_rw [dysonStateCov_inr_inr]
    split_ifs with hij
    · refine continuousAt_const.mul (tendsto_finsetSum _ fun m hm => ?_)
      exact ((continuousAt_coupling hN (hy i m (Finset.ne_of_mem_erase hm).symm)).mul
        (continuous_apply _).continuousAt).mul (continuous_apply _).continuousAt
    · exact ((continuousAt_const.mul (continuousAt_coupling hN (hy i j hij))).mul
        (continuous_apply _).continuousAt).mul (continuous_apply _).continuousAt

theorem dysonState_distinct {H : Matrix (Fin N) (Fin N) ℂ} (hs : HasSimpleSpectrum N H)
    (q : Fin N → ℂ) : ∀ i j : Fin N, i ≠ j →
      dysonState N q H (finSumFinEquiv (Sum.inl i)) ≠ dysonState N q H (finSumFinEquiv (Sum.inl j)) := by
  intro i j hij
  rw [dysonState_inl, dysonState_inl]
  exact HasSimpleSpectrum.ne hs hij

theorem continuousOn_drift_state (q : Fin N → ℂ) :
    ContinuousOn (fun H => dysonStateDrift N (dysonState N q H)) {H | HasSimpleSpectrum N H} :=
  fun H hH => (continuousAt_dysonStateDrift (dysonState_distinct hH q)).comp_continuousWithinAt
    (continuousOn_dysonState q H hH)

theorem continuousOn_cov_state (q : Fin N → ℂ) :
    ContinuousOn (fun H => dysonStateCov N (dysonState N q H)) {H | HasSimpleSpectrum N H} :=
  fun H hH => (continuousAt_dysonStateCov (dysonState_distinct hH q)).comp_continuousWithinAt
    (continuousOn_dysonState q H hH)

/-- Second derivatives of a sum. -/
theorem fderiv2_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f h : E → ℝ} {y : E}
    (hf : ContDiffAt ℝ 2 f y) (hh : ContDiffAt ℝ 2 h y) :
    fderiv ℝ (fderiv ℝ fun y => f y + h y) y = fderiv ℝ (fderiv ℝ f) y + fderiv ℝ (fderiv ℝ h) y := by
  have hev : fderiv ℝ (fun y => f y + h y) =ᶠ[𝓝 y] fun y' => fderiv ℝ f y' + fderiv ℝ h y' := by
    filter_upwards [hf.eventually (by simp), hh.eventually (by simp)] with y' h1 h2
    exact fderiv_fun_add (h1.differentiableAt (by norm_num)) (h2.differentiableAt (by norm_num))
  rw [hev.fderiv_eq]
  exact fderiv_fun_add ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

/-- **Itô drift of a sum of two components**. -/
theorem itoDrift_dysonState_add {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (q : Fin N → ℂ)
    (k l : Fin (N + N)) (t : ℝ≥0) :
    itoDrift (fun p : ℝ × (Fin (N * N) → ℝ) => stateFn N q k p.2 + stateFn N q l p.2) y t 0
        (gueCovVec N) =
      dysonStateDrift N (dysonState N q (vecHerm N y)) k +
        dysonStateDrift N (dysonState N q (vecHerm N y)) l := by
  have hk := contDiffAt_stateFn (n := 2) hy q k
  have hl := contDiffAt_stateFn (n := 2) hy q l
  rw [← itoDrift_dysonState hy q k t, ← itoDrift_dysonState hy q l t, gueCovVec_eq,
    itoDrift_comp_snd (g := fun y => stateFn N q k y + stateFn N q l y) (hk.add hl),
    itoDrift_comp_snd hk, itoDrift_comp_snd hl, fderiv2_add hk hl]
  simp only [FunLike.coe_add, Pi.add_apply, Finset.sum_add_distrib]
  ring

end BlockBand.SourceProcess.Stochastic.Dyson
