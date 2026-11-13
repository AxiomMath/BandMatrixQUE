module

public import BlockBand.Palm.RegularityScalar
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# The starting root at height one

At height `η = 1` the finite Dyson map is a contraction on the unit upper half-disk, which gives a
root with positive imaginary part (`certificate_height_one_zero_exists`); a Ward-type lower
bound on the Jacobian at every root (`certificate_dyson_jacobian_norm_lower`) makes the Newton
steps uniform in the spectrum.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- The finite Dyson map. -/
def certificateDysonMap (spectrum : ι → ℝ) (s : ℝ) (z m : ℂ) : ℂ :=
  certificateAverage (fun i => certificateScalarResolvent (spectrum i) (z + s * m))

/-- `|(d - a)⁻¹| ≤ 1` when `Im a ≥ 1`, for every real `d`. -/
theorem certificate_scalar_norm_le_one (d : ℝ) {a : ℂ} (ha : 1 ≤ a.im) :
    ‖certificateScalarResolvent d a‖ ≤ 1 := by
  have hnorm : 1 ≤ ‖(d : ℂ) - a‖ := by
    have hi := Complex.abs_im_le_norm ((d : ℂ) - a)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
      abs_of_pos (by linarith : 0 < a.im)] at hi
    exact ha.trans hi
  unfold certificateScalarResolvent
  rw [norm_inv]
  have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1) hnorm
  simpa using h

/-- At height one the finite Dyson map is `s`-Lipschitz on the unit upper half-disk. -/
theorem certificate_height_one_map_lipschitz [Nonempty ι]
    (spectrum : ι → ℝ) {s : ℝ} {z m n : ℂ}
    (hs : 0 ≤ s) (hz : z.im = 1) (hm : 0 ≤ m.im) (hn : 0 ≤ n.im) :
    ‖certificateDysonMap spectrum s z m - certificateDysonMap spectrum s z n‖ ≤
      s * ‖m - n‖ := by
  have hma : 1 ≤ (z + s * m).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [hz]
    linarith [mul_nonneg hs hm]
  have hna : 1 ≤ (z + s * n).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [hz]
    linarith [mul_nonneg hs hn]
  unfold certificateDysonMap certificateAverage
  rw [← Finset.expect_sub_distrib]
  apply (certificateAverage_norm_le _).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro i _
  rw [certificate_scalar_resolvent_sub _ (by linarith : (z + s * m).im ≠ 0)
    (by linarith : (z + s * n).im ≠ 0), norm_mul, norm_mul]
  have heq : z + s * m - (z + s * n) = (s : ℂ) * (m - n) := by ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have hra := certificate_scalar_norm_le_one (spectrum i) hma
  have hrb := certificate_scalar_norm_le_one (spectrum i) hna
  calc
    _ ≤ (s * ‖m - n‖) * 1 * 1 := by gcongr
    _ = _ := by ring

/-- A root of the finite Dyson equation in the upper half-plane at `η = 1`, with
spectrum-independent bounds. -/
theorem certificate_height_one_zero_exists [Nonempty ι]
    (spectrum : ι → ℝ) {s : ℝ} {z : ℂ}
    (hs : 0 < s) (hs1 : s < 1) (hz : z.im = 1) :
    ∃ m : ℂ, 0 < m.im ∧ ‖m‖ ≤ 1 ∧ certificateDysonResidual spectrum s z m = 0 := by
  let T := certificateDysonMap spectrum s z
  let K : Set ℂ := {m | 0 ≤ m.im ∧ ‖m‖ ≤ 1}
  have hclosed : IsClosed K := by
    dsimp [K]
    exact (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le continuous_norm continuous_const)
  have hmap : Set.MapsTo T K K := by
    intro m hm
    have hma : 1 ≤ (z + s * m).im := by
      have hmi : 0 ≤ m.im := hm.1
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      rw [hz]
      linarith [mul_nonneg hs.le hmi]
    constructor
    · dsimp [T, certificateDysonMap]
      rw [certificateAverage_im]
      apply Finset.expect_nonneg
      intro i _
      rw [certificate_scalar_ward]
      exact mul_nonneg (by linarith) (Complex.normSq_nonneg _)
    · apply (certificateAverage_norm_le _).trans
      apply Finset.expect_le Finset.univ_nonempty
      intro i _
      exact certificate_scalar_norm_le_one _ hma
  have hcontract : ContractingWith (⟨s, hs.le⟩ : NNReal) (hmap.restrict T K K) := by
    constructor
    · exact hs1
    · apply LipschitzWith.of_dist_le_mul
      intro m n
      change dist (T m) (T n) ≤ s * dist (m : ℂ) (n : ℂ)
      rw [dist_eq_norm, dist_eq_norm]
      exact certificate_height_one_map_lipschitz spectrum hs.le hz m.property.1 n.property.1
  have hK0 : (0 : ℂ) ∈ K := by simp [K]
  obtain ⟨m, hm, hfix, _⟩ := ContractingWith.exists_fixedPoint' hclosed.isComplete hmap hcontract
    hK0 (edist_ne_top (0 : ℂ) (T 0))
  have hma : 0 < (z + s * m).im := by
    have hmi : 0 ≤ m.im := hm.1
    simpa [hz] using add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 1) (mul_nonneg hs.le hmi)
  have hpositive : 0 < (T m).im := by
    dsimp [T, certificateDysonMap]
    rw [certificateAverage_im]
    apply Finset.expect_pos _ Finset.univ_nonempty
    intro i _
    rw [certificate_scalar_ward]
    apply mul_pos hma
    apply Complex.normSq_pos.mpr
    unfold certificateScalarResolvent
    apply inv_ne_zero
    intro heq
    have him := congrArg Complex.im heq
    have ha0 : (z + s * m).im = 0 := by
      simpa only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] using him
    exact hma.ne' ha0
  refine ⟨m, ?_, hm.2, ?_⟩
  · rw [hfix.eq] at hpositive
    exact hpositive
  · apply (certificateDysonResidual_eq_zero_iff spectrum s z m).mpr
    exact hfix.eq.symm

/-- Lower bound on the Jacobian at every root with positive imaginary part, at positive height
(Ward stability); it gives a spectrum-uniform Newton step. -/
theorem certificate_dyson_jacobian_norm_lower
    (spectrum : ι → ℝ) {s : ℝ} {z m : ℂ}
    (hs : 0 < s) (hz : 0 < z.im) (hmi : 0 < m.im)
    (hm : certificateDysonResidual spectrum s z m = 0) :
    z.im / (z.im + s * m.im) ≤ ‖certificateDysonJacobian spectrum s z m‖ := by
  let A : ℝ := certificateRealAverage (fun i => Complex.normSq
    (certificateScalarResolvent (spectrum i) (z + s * m)))
  let T : ℂ := (s : ℂ) * certificateAverage (fun i =>
    certificateScalarResolvent (spectrum i) (z + s * m) ^ 2)
  have hnorm : ‖T‖ ≤ s * A := by
    dsimp [T]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    apply mul_le_mul_of_nonneg_left _ hs.le
    apply (certificateAverage_norm_le _).trans
    apply Finset.expect_le_expect
    intro i _
    rw [norm_pow, Complex.normSq_eq_norm_sq]
  have hward : m.im = (z.im + s * m.im) * A := certificate_dyson_ward spectrum s z m hm
  have hden : 0 < z.im + s * m.im := add_pos hz (mul_pos hs hmi)
  have htr : 1 - ‖T‖ ≤ ‖certificateDysonJacobian spectrum s z m‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) T
    simpa only [norm_one, T, certificateDysonJacobian] using hh
  have hratio : z.im / (z.im + s * m.im) ≤ 1 - ‖T‖ := by
    rw [div_le_iff₀ hden]
    have hmul := mul_le_mul_of_nonneg_left hnorm hden.le
    nlinarith
  exact hratio.trans htr

end BlockBand.Palm
