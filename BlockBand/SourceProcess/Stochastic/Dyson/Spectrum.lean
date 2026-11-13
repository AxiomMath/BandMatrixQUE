module

public import BlockBand.Internal.Contracts.Transmission
public import BlockBand.Model.Construction.OrderedEigenvalues

/-!
# Dyson Brownian motion: continuity and measurability of the spectral maps

Deterministic infrastructure, no law:
* the ordered eigenvalues `dysonEigenvalue N · i` are `N`-Lipschitz for the entrywise sup
  metric on all complex matrices (Weyl, through the Hermitian part), hence continuous;
* the simple-spectrum set is open, and the minimal gap is continuous;
* the maps `dysonProjection`, `dysonOverlap`, `dysonState`, `dysonStateDrift`, `dysonStateCov`
  (defined in the transmission contract) are Borel measurable, and the projection, overlap and
  state are continuous on the simple-spectrum set.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory Filter Topology
open scoped Matrix
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- Second countability of square complex matrices (the `Pi` instance through `Matrix`);
used as a local instance (Borel arithmetic on matrices). -/
theorem secondCountableTopology_matrix : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))

attribute [local instance] secondCountableTopology_matrix

/-- Entry bound for the Hermitian part: `‖(H + Hᴴ - H' - H'ᴴ) a b‖ ≤ 2 dist H H'`. -/
theorem norm_hermPart_sub_le (H H' : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) :
    ‖(H + Hᴴ) a b - (H' + H'ᴴ) a b‖ ≤ 2 * @dist (Fin N → Fin N → ℂ) _ H H' := by
  have h1 : ‖H a b - H' a b‖ ≤ @dist (Fin N → Fin N → ℂ) _ H H' := by
    rw [← dist_eq_norm]
    exact (dist_le_pi_dist (H a) (H' a) b).trans (dist_le_pi_dist (show Fin N → Fin N → ℂ from H) H' a)
  have h2 : ‖H b a - H' b a‖ ≤ @dist (Fin N → Fin N → ℂ) _ H H' := by
    rw [← dist_eq_norm]
    exact (dist_le_pi_dist (H b) (H' b) a).trans (dist_le_pi_dist (show Fin N → Fin N → ℂ from H) H' b)
  have e : (H + Hᴴ) a b - (H' + H'ᴴ) a b = (H a b - H' a b) + star (H b a - H' b a) := by
    simp only [Matrix.add_apply, Matrix.conjTranspose_apply, star_sub]; ring
  rw [e]
  calc ‖(H a b - H' a b) + star (H b a - H' b a)‖
      ≤ ‖H a b - H' a b‖ + ‖star (H b a - H' b a)‖ := norm_add_le _ _
    _ = ‖H a b - H' a b‖ + ‖H b a - H' b a‖ := by rw [norm_star]
    _ ≤ 2 * @dist (Fin N → Fin N → ℂ) _ H H' := by linarith

/-- Weyl for `dysonEigenvalue`: `|λ_i(H) - λ_i(H')| ≤ N · dist H H'` (entrywise sup metric). -/
theorem abs_dysonEigenvalue_sub_le (H H' : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    |dysonEigenvalue N H i - dysonEigenvalue N H' i| ≤
      (N : ℝ) * @dist (Fin N → Fin N → ℂ) _ H H' := by
  unfold dysonEigenvalue
  have h := (Matrix.isHermitian_add_transpose_self H).abs_eigenvalues₀_sub_le_of_entry_le
    (Matrix.isHermitian_add_transpose_self H') (norm_hermPart_sub_le H H')
    (Fin.cast (Fintype.card_fin N).symm i)
  have h2 := h.trans_eq (by rw [Fintype.card_fin])
  rw [← sub_div, abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith [h2]

/-- Each ordered eigenvalue is continuous on all complex matrices. -/
theorem continuous_dysonEigenvalue (i : Fin N) :
    Continuous fun H : Matrix (Fin N) (Fin N) ℂ => dysonEigenvalue N H i := by
  let _ : PseudoMetricSpace (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (PseudoMetricSpace (Fin N → Fin N → ℂ))
  exact (LipschitzWith.of_dist_le_mul (K := (N : NNReal)) fun H H' => by
    rw [Real.dist_eq]; exact_mod_cast abs_dysonEigenvalue_sub_le H H' i).continuous

/-- The ordered spectrum is continuous as a vector-valued map. -/
theorem continuous_dysonEigenvalue_pi :
    Continuous fun H : Matrix (Fin N) (Fin N) ℂ => dysonEigenvalue N H :=
  continuous_pi continuous_dysonEigenvalue

theorem measurable_dysonEigenvalue (i : Fin N) :
    Measurable fun H : Matrix (Fin N) (Fin N) ℂ => dysonEigenvalue N H i :=
  (continuous_dysonEigenvalue i).measurable

/-- The simple-spectrum set is described by finitely many strict inequalities. -/
theorem hasSimpleSpectrum_iff (H : Matrix (Fin N) (Fin N) ℂ) :
    HasSimpleSpectrum N H ↔ ∀ i j : Fin N, i < j → dysonEigenvalue N H j < dysonEigenvalue N H i :=
  Iff.rfl

/-- The set of matrices whose Hermitian part has simple spectrum is open. -/
theorem isOpen_hasSimpleSpectrum : IsOpen {H : Matrix (Fin N) (Fin N) ℂ | HasSimpleSpectrum N H} := by
  have : {H : Matrix (Fin N) (Fin N) ℂ | HasSimpleSpectrum N H} =
      ⋂ i : Fin N, ⋂ j : Fin N, {H | i < j → dysonEigenvalue N H j < dysonEigenvalue N H i} := by
    ext H; simp [hasSimpleSpectrum_iff]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  by_cases hij : i < j
  · simpa [hij] using isOpen_lt (continuous_dysonEigenvalue j) (continuous_dysonEigenvalue i)
  · simp [hij]

/-- Simple spectrum means pairwise distinct ordered eigenvalues. -/
theorem HasSimpleSpectrum.ne {H : Matrix (Fin N) (Fin N) ℂ} (h : HasSimpleSpectrum N H)
    {i j : Fin N} (hij : i ≠ j) : dysonEigenvalue N H i ≠ dysonEigenvalue N H j :=
  fun e => hij (h.injective e)

/-- Factor of the Lagrange product defining `dysonProjection`. -/
def projFactor (N : ℕ) (i j : Fin N) (H : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ((dysonEigenvalue N H i - dysonEigenvalue N H j)⁻¹ : ℂ) •
    (H - (dysonEigenvalue N H j : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))

theorem dysonProjection_eq (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    dysonProjection N H i =
      (((List.finRange N).filter fun j => j ≠ i).map fun j => projFactor N i j H).prod := rfl

theorem continuous_eigenvalue_complex (j : Fin N) :
    Continuous fun H : Matrix (Fin N) (Fin N) ℂ => (dysonEigenvalue N H j : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_dysonEigenvalue j)

theorem continuous_sub_eigenvalue_smul_one (j : Fin N) :
    Continuous fun H : Matrix (Fin N) (Fin N) ℂ =>
      H - (dysonEigenvalue N H j : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) :=
  continuous_id.sub ((continuous_eigenvalue_complex j).smul continuous_const)

theorem measurable_projFactor (i j : Fin N) :
    Measurable (projFactor N i j) := by
  unfold projFactor
  refine Measurable.smul (M := ℂ) ?_ (continuous_sub_eigenvalue_smul_one j).measurable
  exact ((continuous_eigenvalue_complex i).measurable.sub
    (continuous_eigenvalue_complex j).measurable).inv

theorem continuousOn_projFactor {i j : Fin N} (hij : j ≠ i) :
    ContinuousOn (projFactor N i j) {H | HasSimpleSpectrum N H} := by
  unfold projFactor
  refine ContinuousOn.smul (M := ℂ) ?_ (continuous_sub_eigenvalue_smul_one j).continuousOn
  refine ContinuousOn.inv₀ ((continuous_eigenvalue_complex i).sub
    (continuous_eigenvalue_complex j)).continuousOn fun H hH => ?_
  rw [sub_ne_zero]
  exact_mod_cast HasSimpleSpectrum.ne (N := N) hH hij.symm

theorem measurable_dysonProjection (i : Fin N) :
    Measurable fun H : Matrix (Fin N) (Fin N) ℂ => dysonProjection N H i := by
  simp only [dysonProjection_eq]
  have := List.measurable_fun_prod
    (((List.finRange N).filter fun j => j ≠ i).map fun j => projFactor N i j)
    (by simp only [List.mem_map]; rintro _ ⟨j, -, rfl⟩; exact measurable_projFactor i j)
  simpa [List.map_map, Function.comp_def] using this

theorem continuousOn_dysonProjection (i : Fin N) :
    ContinuousOn (fun H : Matrix (Fin N) (Fin N) ℂ => dysonProjection N H i)
      {H | HasSimpleSpectrum N H} := by
  simp only [dysonProjection_eq]
  refine continuousOn_list_prod _ fun j hj => continuousOn_projFactor ?_
  simpa using (List.mem_filter.mp hj).2

/-- Continuity of the quadratic form `P ↦ N Re(q* P q)`. -/
theorem continuous_overlapForm (q : Fin N → ℂ) :
    Continuous fun P : Matrix (Fin N) (Fin N) ℂ => (N : ℝ) * (star q ⬝ᵥ (P *ᵥ q)).re := by
  refine continuous_const.mul (Complex.continuous_re.comp ?_)
  exact continuous_const.dotProduct (Continuous.matrix_mulVec continuous_id continuous_const)

theorem measurable_dysonOverlap (q : Fin N → ℂ) (i : Fin N) :
    Measurable fun H : Matrix (Fin N) (Fin N) ℂ => dysonOverlap N q H i :=
  (continuous_overlapForm q).measurable.comp (measurable_dysonProjection i)

theorem continuousOn_dysonOverlap (q : Fin N → ℂ) (i : Fin N) :
    ContinuousOn (fun H : Matrix (Fin N) (Fin N) ℂ => dysonOverlap N q H i)
      {H | HasSimpleSpectrum N H} :=
  (continuous_overlapForm q).comp_continuousOn (continuousOn_dysonProjection i)

theorem dysonState_inl (q : Fin N → ℂ) (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    dysonState N q H (finSumFinEquiv (Sum.inl i)) = dysonEigenvalue N H i := by
  simp only [dysonState, Equiv.symm_apply_apply]

theorem dysonState_inr (q : Fin N → ℂ) (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    dysonState N q H (finSumFinEquiv (Sum.inr i)) = dysonOverlap N q H i := by
  simp only [dysonState, Equiv.symm_apply_apply]

theorem measurable_dysonState (q : Fin N → ℂ) : Measurable (dysonState N q) := by
  refine measurable_pi_iff.mpr fun k => ?_
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with i | i
  · simpa only [dysonState_inl] using measurable_dysonEigenvalue i
  · simpa only [dysonState_inr] using measurable_dysonOverlap q i

theorem continuousOn_dysonState (q : Fin N → ℂ) :
    ContinuousOn (dysonState N q) {H | HasSimpleSpectrum N H} := by
  refine continuousOn_pi.mpr fun k => ?_
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with i | i
  · simpa only [dysonState_inl] using (continuous_dysonEigenvalue i).continuousOn
  · simpa only [dysonState_inr] using continuousOn_dysonOverlap q i

theorem measurable_dysonCoupling (i j : Fin N) :
    Measurable fun lam : Fin N → ℝ => dysonCoupling N lam i j := by
  unfold dysonCoupling; fun_prop

theorem dysonStateDrift_inl (y : Fin (N + N) → ℝ) (i : Fin N) :
    dysonStateDrift N y (finSumFinEquiv (Sum.inl i)) =
      dysonDrift N (fun a => y (finSumFinEquiv (Sum.inl a))) i := by
  simp only [dysonStateDrift, Equiv.symm_apply_apply]

theorem dysonStateDrift_inr (y : Fin (N + N) → ℝ) (i : Fin N) :
    dysonStateDrift N y (finSumFinEquiv (Sum.inr i)) =
      ∑ j ∈ Finset.univ.erase i, dysonCoupling N (fun a => y (finSumFinEquiv (Sum.inl a))) i j *
        (y (finSumFinEquiv (Sum.inr j)) - y (finSumFinEquiv (Sum.inr i))) := by
  simp only [dysonStateDrift, Equiv.symm_apply_apply]

theorem dysonStateCov_inl_inl (y : Fin (N + N) → ℝ) (i j : Fin N) :
    dysonStateCov N y (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) =
      if i = j then 1 / (N : ℝ) else 0 := by
  rw [dysonStateCov, Matrix.of_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem dysonStateCov_inl_inr (y : Fin (N + N) → ℝ) (i j : Fin N) :
    dysonStateCov N y (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = 0 := by
  rw [dysonStateCov, Matrix.of_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem dysonStateCov_inr_inl (y : Fin (N + N) → ℝ) (i j : Fin N) :
    dysonStateCov N y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
  rw [dysonStateCov, Matrix.of_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem dysonStateCov_inr_inr (y : Fin (N + N) → ℝ) (i j : Fin N) :
    dysonStateCov N y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) =
      if i = j then 2 * ∑ m ∈ Finset.univ.erase i,
          dysonCoupling N (fun a => y (finSumFinEquiv (Sum.inl a))) i m *
            y (finSumFinEquiv (Sum.inr i)) * y (finSumFinEquiv (Sum.inr m))
      else -2 * dysonCoupling N (fun a => y (finSumFinEquiv (Sum.inl a))) i j *
            y (finSumFinEquiv (Sum.inr i)) * y (finSumFinEquiv (Sum.inr j)) := by
  rw [dysonStateCov, Matrix.of_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem measurable_dysonStateDrift : Measurable (dysonStateDrift N) := by
  refine measurable_pi_iff.mpr fun k => ?_
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with i | i
  · simp only [dysonStateDrift_inl]; unfold dysonDrift; fun_prop
  · simp only [dysonStateDrift_inr]; unfold dysonCoupling; fun_prop

theorem measurable_dysonStateCov : Measurable (dysonStateCov N) := by
  refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun l => ?_
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  obtain ⟨l, rfl⟩ := finSumFinEquiv.surjective l
  rcases k with i | i <;> rcases l with j | j
  · simp only [dysonStateCov_inl_inl]; exact measurable_const
  · simp only [dysonStateCov_inl_inr]; exact measurable_const
  · simp only [dysonStateCov_inr_inl]; exact measurable_const
  · simp only [dysonStateCov_inr_inr]
    split_ifs
    · unfold dysonCoupling; fun_prop
    · unfold dysonCoupling; fun_prop

end BlockBand.SourceProcess.Stochastic.Dyson
