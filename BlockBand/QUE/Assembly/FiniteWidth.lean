module

public import BlockBand.QUE.PhysicalAdapter
public import BlockBand.Foundations.Spectral.OrderedEigenpairs

/-!
# Finite-width payment for prescribed-rank QUE

The physical QUE statistic is at most `4` at every width and rank (`queStatistic_le_four`), so
for `W` below a fixed cutoff `W₀` it is bounded by `W₀ n/W`; combined with a large-width estimate
this covers all widths with one enlarged constant (`all_width_payment_of_large_width`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.Assembly

open MeasureTheory
open scoped BigOperators

/-- A real test bounded by one has weighted mean bounded by one against every finite
nonnegative unit-mass vector. -/
theorem abs_weighted_test_le_one {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (hmass : ∀ x, 0 ≤ mass x)
    (htotal : ∑ x, mass x = 1) (v : ι → ℝ) (hv : ∀ x, |v x| ≤ 1) :
    |∑ x, v x * mass x| ≤ 1 := by
  calc
    |∑ x, v x * mass x| ≤ ∑ x, |v x * mass x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |v x| * mass x := by
      simp_rw [abs_mul, abs_of_nonneg (hmass _)]
    _ ≤ ∑ x, mass x := by
      apply Finset.sum_le_sum
      intro x _
      simpa using mul_le_mul_of_nonneg_right (hv x) (hmass x)
    _ = 1 := htotal

/-- Uniform baseline bound for a test on a nonempty finite site set. -/
theorem abs_uniform_test_le_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ) (hv : ∀ x, |v x| ≤ 1) :
    |(Fintype.card ι : ℝ)⁻¹ * ∑ x, v x| ≤ 1 := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  rw [abs_mul, abs_inv, abs_of_pos hcard]
  calc
    (Fintype.card ι : ℝ)⁻¹ * |∑ x, v x| ≤
        (Fintype.card ι : ℝ)⁻¹ * ∑ x, |v x| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hcard.le)
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _x : ι, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hcard.le)
      exact Finset.sum_le_sum (fun x _ => hv x)
    _ = 1 := by simp [hcard.ne']

/-- The selected eigenvector of the physical model has total site mass one almost surely. -/
theorem physicalSiteMass_total_ae {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (α : Fin p.N) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∑ x, physicalSiteMass spectral α H x = 1 := by
  filter_upwards [spectral.orthonormal_ae] with H hH
  exact BlockBand.Foundations.Spectral.sum_norm_sq_eq_one_of_inner_sum_eq_one
    (spectral.eigenvector H α) (by simpa using hH α α)

/-- The physical QUE statistic is at most four at every finite width and rank (with no bulk-rank
restriction). -/
theorem queStatistic_le_four {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (α : Fin p.N)
    (v : p.Site → ℝ) (hv : ∀ x, |v x| ≤ 1) :
    spectral.queStatistic α v ≤ 4 := by
  have hcard : Fintype.card p.Site = p.N := by
    simp [Parameters.Site, Parameters.N]
  have hbaseline : |(p.N : ℝ)⁻¹ * ∑ x, v x| ≤ 1 := by
    rw [← hcard]
    exact abs_uniform_test_le_one v hv
  have hpoint : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      |(∑ x, v x * ‖spectral.eigenvector H α x‖ ^ 2) -
        (p.N : ℝ)⁻¹ * ∑ x, v x| ^ 2 ≤ (4 : ℝ) := by
    filter_upwards [physicalSiteMass_total_ae spectral α] with H hH
    have hweighted := abs_weighted_test_le_one
      (physicalSiteMass spectral α H) (fun x => sq_nonneg _) hH v hv
    have habs : |(∑ x, v x * ‖spectral.eigenvector H α x‖ ^ 2) -
        (p.N : ℝ)⁻¹ * ∑ x, v x| ≤ 2 := by
      calc
        _ ≤ |∑ x, v x * ‖spectral.eigenvector H α x‖ ^ 2| +
            |(p.N : ℝ)⁻¹ * ∑ x, v x| := abs_sub _ _
        _ ≤ 2 := by change |∑ x, v x * physicalSiteMass spectral α H x| + _ ≤ 2; linarith
    nlinarith [abs_nonneg ((∑ x, v x * ‖spectral.eigenvector H α x‖ ^ 2) -
      (p.N : ℝ)⁻¹ * ∑ x, v x)]
  unfold Parameters.SpectralRealization.queStatistic
  calc
    _ ≤ ∫ _H, (4 : ℝ) ∂(model.law : Measure p.SiteMatrix) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun H => sq_nonneg _))
        (integrable_const 4) hpoint
    _ = 4 := by simp

end BlockBand.QUE.Assembly

namespace BlockBand.QUE.Assembly

/-- If `W` is below a fixed cutoff `W₀`, the physical statistic is bounded by `W₀ n/W` (since
`n ≥ 4`); this is the finite-width clause of the QUE theorem. -/
theorem small_width_payment {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (α : Fin p.N)
    (v : p.Site → ℝ) (hv : ∀ x, |v x| ≤ 1)
    {W0 : ℝ} (hwidth : (p.W : ℝ) ≤ W0) :
    spectral.queStatistic α v ≤
      W0 * ((p.n : ℝ) / p.W + ((p.n : ℝ) / p.W) ^ (3 / 2 : ℝ)) +
        1 / ((p.W : ℝ) + 1) := by
  have hW : 0 < (p.W : ℝ) := by exact_mod_cast p.W_pos
  have hW0 : 0 < W0 := lt_of_lt_of_le hW hwidth
  have hn : (4 : ℝ) ≤ p.n := by exact_mod_cast p.n_ge_four
  have hratio : 0 ≤ (p.n : ℝ) / p.W := by positivity
  have hfour : (4 : ℝ) ≤ W0 * ((p.n : ℝ) / p.W) := by
    calc
      (4 : ℝ) ≤ (p.n : ℝ) := hn
      _ = (p.W : ℝ) * ((p.n : ℝ) / p.W) := by field_simp
      _ ≤ W0 * ((p.n : ℝ) / p.W) :=
        mul_le_mul_of_nonneg_right hwidth hratio
  have hpower : 0 ≤ ((p.n : ℝ) / p.W) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hratio _
  have hremain : 0 ≤ 1 / ((p.W : ℝ) + 1) := by positivity
  have hpaid := mul_nonneg hW0.le hpower
  have hstat := queStatistic_le_four spectral α v hv
  nlinarith

/-- Given a large-width estimate with constant `C`, the finitely many remaining widths are
covered with one enlarged constant `max(C, W₀)`. The large-width estimate is a hypothesis. -/
theorem all_width_payment_of_large_width {p : Parameters}
    {model : p.GaussianRingModel} (spectral : p.SpectralRealization model)
    (α : Fin p.N) (v : p.Site → ℝ) (hv : ∀ x, |v x| ≤ 1)
    (C W0 : ℝ)
    (hlarge : W0 < (p.W : ℝ) →
      spectral.queStatistic α v ≤
        C * ((p.n : ℝ) / p.W + ((p.n : ℝ) / p.W) ^ (3 / 2 : ℝ)) +
          1 / ((p.W : ℝ) + 1)) :
    spectral.queStatistic α v ≤
      max C W0 * ((p.n : ℝ) / p.W + ((p.n : ℝ) / p.W) ^ (3 / 2 : ℝ)) +
        1 / ((p.W : ℝ) + 1) := by
  have hscale : 0 ≤ (p.n : ℝ) / p.W + ((p.n : ℝ) / p.W) ^ (3 / 2 : ℝ) := by
    positivity
  by_cases hwidth : (p.W : ℝ) ≤ W0
  · exact le_trans (small_width_payment spectral α v hv hwidth)
      (add_le_add (mul_le_mul_of_nonneg_right (le_max_right C W0) hscale) le_rfl)
  · exact le_trans (hlarge (lt_of_not_ge hwidth))
      (add_le_add (mul_le_mul_of_nonneg_right (le_max_left C W0) hscale) le_rfl)

end BlockBand.QUE.Assembly
