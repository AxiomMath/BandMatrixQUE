module

public import BlockBand.Palm.RegularityScalar
public import BlockBand.Palm.RegularityCovariance
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Quantitative solution of the finite scalar Dyson equation

Bounds on the scalar resolvents `(d - a)⁻¹` and their spectral averages, and a quantitative
Newton (Banach fixed-point) construction of a zero of the finite reciprocal Dyson equation near a
reference value, with explicit scalar conditions (`certificate_local_zero_exists`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- A complete spectral average inherits a pointwise norm bound. -/
theorem certificateAverage_norm_le_const [Nonempty ι]
    (f : ι → ℂ) (B : ℝ) (hf : ∀ i, ‖f i‖ ≤ B) :
    ‖certificateAverage f‖ ≤ B := by
  apply (certificateAverage_norm_le f).trans
  exact Finset.expect_le Finset.univ_nonempty (fun i _ => hf i)

/-- Reciprocal bound depending only on the imaginary part, uniformly in the real spectral
coordinate. -/
theorem certificateScalarResolvent_norm_le (d : ℝ) {H : ℝ} {a : ℂ}
    (hH : 0 < H) (ha : H ≤ a.im) :
    ‖certificateScalarResolvent d a‖ ≤ H⁻¹ := by
  have hnorm : H ≤ ‖(d : ℂ) - a‖ := by
    have hi := Complex.abs_im_le_norm ((d : ℂ) - a)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
      abs_of_pos (hH.trans_le ha)] at hi
    exact ha.trans hi
  unfold certificateScalarResolvent
  rw [norm_inv]
  exact inv_anti₀ hH hnorm

/-- Reciprocal difference bound with no real-coordinate restriction. -/
theorem certificateScalarResolvent_lipschitz (d : ℝ) {H : ℝ} {a b : ℂ}
    (hH : 0 < H) (ha : H ≤ a.im) (hb : H ≤ b.im) :
    ‖certificateScalarResolvent d a - certificateScalarResolvent d b‖ ≤
      ‖a - b‖ * H⁻¹ ^ 2 := by
  rw [certificate_scalar_resolvent_sub d (hH.trans_le ha).ne' (hH.trans_le hb).ne',
    norm_mul, norm_mul]
  have hra := certificateScalarResolvent_norm_le d hH ha
  have hrb := certificateScalarResolvent_norm_le d hH hb
  calc
    _ ≤ ‖a - b‖ * H⁻¹ * H⁻¹ := by gcongr
    _ = _ := by ring

/-- Variation of a product of scalar resolvents, in terms of the imaginary-part lower bound and
the displacement of the scalar parameter. -/
theorem certificateScalarResolvent_product_sub_sq_norm_le
    (d : ℝ) {H L : ℝ} {a b a₀ : ℂ}
    (hH : 0 < H) (ha : H ≤ a.im) (hb : H ≤ b.im) (ha₀ : H ≤ a₀.im)
    (haL : ‖a - a₀‖ ≤ L) (hbL : ‖b - a₀‖ ≤ L) :
    ‖certificateScalarResolvent d a * certificateScalarResolvent d b -
        certificateScalarResolvent d a₀ ^ 2‖ ≤ 2 * L * H⁻¹ ^ 3 := by
  have hL : 0 ≤ L := (norm_nonneg _).trans haL
  have hbR := certificateScalarResolvent_norm_le d hH hb
  have ha₀R := certificateScalarResolvent_norm_le d hH ha₀
  have haD := (certificateScalarResolvent_lipschitz d hH ha ha₀).trans
    (mul_le_mul_of_nonneg_right haL (by positivity))
  have hbD := (certificateScalarResolvent_lipschitz d hH hb ha₀).trans
    (mul_le_mul_of_nonneg_right hbL (by positivity))
  have heq : certificateScalarResolvent d a * certificateScalarResolvent d b -
      certificateScalarResolvent d a₀ ^ 2 =
      (certificateScalarResolvent d a - certificateScalarResolvent d a₀) *
        certificateScalarResolvent d b + certificateScalarResolvent d a₀ *
          (certificateScalarResolvent d b - certificateScalarResolvent d a₀) := by ring
  rw [heq]
  calc
    _ ≤ ‖(certificateScalarResolvent d a - certificateScalarResolvent d a₀) *
        certificateScalarResolvent d b‖ + ‖certificateScalarResolvent d a₀ *
          (certificateScalarResolvent d b - certificateScalarResolvent d a₀)‖ := norm_add_le _ _
    _ = ‖certificateScalarResolvent d a - certificateScalarResolvent d a₀‖ *
        ‖certificateScalarResolvent d b‖ + ‖certificateScalarResolvent d a₀‖ *
          ‖certificateScalarResolvent d b - certificateScalarResolvent d a₀‖ := by rw [norm_mul, norm_mul]
    _ ≤ (L * H⁻¹ ^ 2) * H⁻¹ + H⁻¹ * (L * H⁻¹ ^ 2) := by gcongr
    _ = _ := by ring

/-- Explicit variation bound for the finite secant coefficient. -/
theorem certificate_secant_variation [Nonempty ι]
    (spectrum : ι → ℝ) {H L c s : ℝ} {a b a₀ : ℂ}
    (hH : 0 < H) (hc : 0 ≤ c)
    (ha : H ≤ a.im) (hb : H ≤ b.im) (ha₀ : H ≤ a₀.im)
    (haL : ‖a - a₀‖ ≤ L) (hbL : ‖b - a₀‖ ≤ L) :
    ‖(s : ℂ) * certificateAverage (fun i => certificateScalarResolvent (spectrum i) a *
        certificateScalarResolvent (spectrum i) b) -
      (c : ℂ) * certificateAverage (fun i => certificateScalarResolvent (spectrum i) a₀ ^ 2)‖ ≤
      |s - c| * H⁻¹ ^ 2 + 2 * c * L * H⁻¹ ^ 3 := by
  have hAB : ‖certificateAverage (fun i => certificateScalarResolvent (spectrum i) a *
      certificateScalarResolvent (spectrum i) b)‖ ≤ H⁻¹ ^ 2 := by
    apply certificateAverage_norm_le_const
    intro i
    rw [norm_mul]
    calc
      _ ≤ H⁻¹ * H⁻¹ := by
        gcongr
        · exact certificateScalarResolvent_norm_le _ hH ha
        · exact certificateScalarResolvent_norm_le _ hH hb
      _ = _ := by ring
  have hD : ‖certificateAverage (fun i => certificateScalarResolvent (spectrum i) a *
        certificateScalarResolvent (spectrum i) b) -
      certificateAverage (fun i => certificateScalarResolvent (spectrum i) a₀ ^ 2)‖ ≤
      2 * L * H⁻¹ ^ 3 := by
    unfold certificateAverage
    rw [← Finset.expect_sub_distrib]
    apply certificateAverage_norm_le_const
    intro i
    exact certificateScalarResolvent_product_sub_sq_norm_le _ hH ha hb ha₀ haL hbL
  let A := certificateAverage (fun i => certificateScalarResolvent (spectrum i) a *
    certificateScalarResolvent (spectrum i) b)
  let B := certificateAverage (fun i => certificateScalarResolvent (spectrum i) a₀ ^ 2)
  change ‖(s : ℂ) * A - (c : ℂ) * B‖ ≤ _
  have heq : (s : ℂ) * A - (c : ℂ) * B = ((s - c : ℝ) : ℂ) * A + c * (A - B) := by
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖((s - c : ℝ) : ℂ) * A‖ + ‖(c : ℂ) * (A - B)‖ := norm_add_le _ _
    _ = |s - c| * ‖A‖ + c * ‖A - B‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ |s - c| * H⁻¹ ^ 2 + c * (2 * L * H⁻¹ ^ 3) := by gcongr
    _ = _ := by ring

/-- The Newton map with the Jacobian evaluated at the reference point. -/
def certificateNewtonMap (spectrum : ι → ℝ) (c s : ℝ) (E : ℝ) (z μ m : ℂ) : ℂ :=
  m - (certificateDysonJacobian spectrum c (E : ℂ) μ)⁻¹ *
    certificateDysonResidual spectrum s z m

/-- The difference of two Newton map values, from the reciprocal equations. -/
theorem certificateNewtonMap_sub (spectrum : ι → ℝ) (c s E : ℝ) (z μ : ℂ) {m n : ℂ}
    (hmz : (z + s * m).im ≠ 0) (hnz : (z + s * n).im ≠ 0)
    (hJ : certificateDysonJacobian spectrum c (E : ℂ) μ ≠ 0) :
    certificateNewtonMap spectrum c s E z μ m - certificateNewtonMap spectrum c s E z μ n =
      (m - n) * (certificateDysonJacobian spectrum c (E : ℂ) μ)⁻¹ *
        ((s : ℂ) * certificateAverage (fun i => certificateScalarResolvent (spectrum i) (z + s * m) *
          certificateScalarResolvent (spectrum i) (z + s * n)) -
          (c : ℂ) * certificateAverage (fun i =>
            certificateScalarResolvent (spectrum i) ((E : ℂ) + c * μ) ^ 2)) := by
  have hh := certificate_dyson_sub spectrum s z hmz hnz
  unfold certificateNewtonMap
  calc
    _ = (m - n) - (certificateDysonJacobian spectrum c (E : ℂ) μ)⁻¹ *
      (certificateDysonResidual spectrum s z m - certificateDysonResidual spectrum s z n) := by ring
    _ = _ := by
      rw [hh]
      have heq : m - n = (m - n) * (certificateDysonJacobian spectrum c (E : ℂ) μ)⁻¹ *
          certificateDysonJacobian spectrum c (E : ℂ) μ := by
        rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
      conv_lhs => lhs; rw [heq]
      unfold certificateDysonJacobian
      ring

/-- A quantitative Newton/Banach construction of a zero of the finite reciprocal Dyson equation.
Every condition is an explicit scalar inequality, and the constants for the imaginary-part
bound, the reference and the Jacobian are independent of the spectrum. -/
theorem certificate_local_zero_exists [Nonempty ι]
    (spectrum : ι → ℝ) (c s E : ℝ) (z μ : ℂ) {H ρ k : ℝ}
    (hH : 0 < H) (hρ : 0 ≤ ρ) (hk : 0 < k) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hheight : 2 * H ≤ ((E : ℂ) + c * μ).im)
    (hshift : ‖z + s * μ - ((E : ℂ) + c * μ)‖ + s * ρ ≤ H)
    (hJ : k ≤ ‖certificateDysonJacobian spectrum c (E : ℂ) μ‖)
    (hcon : (|s - c| * H⁻¹ ^ 2 +
      2 * c * (‖z + s * μ - ((E : ℂ) + c * μ)‖ + s * ρ) * H⁻¹ ^ 3) * k⁻¹ ≤ 1 / 2)
    (hres : ‖certificateDysonResidual spectrum s z μ‖ * k⁻¹ ≤ ρ / 2) :
    ∃ m : ℂ, ‖m - μ‖ ≤ ρ ∧ certificateDysonResidual spectrum s z m = 0 ∧
      ‖m - μ‖ ≤ 2 * ‖certificateDysonResidual spectrum s z μ‖ * k⁻¹ := by
  let T := certificateNewtonMap spectrum c s E z μ
  let a₀ : ℂ := (E : ℂ) + c * μ
  let L : ℝ := ‖z + s * μ - a₀‖ + s * ρ
  have hJnz : certificateDysonJacobian spectrum c (E : ℂ) μ ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hJ
    linarith
  have hJinv : ‖(certificateDysonJacobian spectrum c (E : ℂ) μ)⁻¹‖ ≤ k⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hk hJ
  have hball : ∀ m : ℂ, ‖m - μ‖ ≤ ρ → ‖z + s * m - a₀‖ ≤ L := by
    intro m hm
    have heq : z + s * m - a₀ = (z + s * μ - a₀) + (s : ℂ) * (m - μ) := by ring
    rw [heq]
    calc
      _ ≤ ‖z + s * μ - a₀‖ + ‖(s : ℂ) * (m - μ)‖ := norm_add_le _ _
      _ = ‖z + s * μ - a₀‖ + s * ‖m - μ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
      _ ≤ L := by dsimp [L]; gcongr
  have habsorb : ∀ m : ℂ, ‖m - μ‖ ≤ ρ → H ≤ (z + s * m).im := by
    intro m hm
    have hi := Complex.abs_im_le_norm (z + s * m - a₀)
    have hlo := (abs_le.mp (hi.trans (hball m hm))).1
    simp only [Complex.sub_im] at hlo
    change L ≤ H at hshift
    change 2 * H ≤ a₀.im at hheight
    linarith
  have hLip : ∀ m n : ℂ, ‖m - μ‖ ≤ ρ → ‖n - μ‖ ≤ ρ →
      ‖T m - T n‖ ≤ (1 / 2 : ℝ) * ‖m - n‖ := by
    intro m n hm hn
    have hma := habsorb m hm
    have hna := habsorb n hn
    have h₀a : H ≤ a₀.im := by linarith
    have hsec := certificate_secant_variation spectrum (s := s) hH hc hma hna h₀a (hball m hm) (hball n hn)
    dsimp [T]
    rw [certificateNewtonMap_sub spectrum c s E z μ (hH.trans_le hma).ne'
      (hH.trans_le hna).ne' hJnz, norm_mul, norm_mul]
    calc
      _ ≤ ‖m - n‖ * k⁻¹ *
          (|s - c| * H⁻¹ ^ 2 + 2 * c * L * H⁻¹ ^ 3) := by gcongr
      _ = ((|s - c| * H⁻¹ ^ 2 + 2 * c * L * H⁻¹ ^ 3) * k⁻¹) * ‖m - n‖ := by ring
      _ ≤ (1 / 2 : ℝ) * ‖m - n‖ := mul_le_mul_of_nonneg_right hcon (norm_nonneg _)
  have hcenter : ‖T μ - μ‖ ≤ ‖certificateDysonResidual spectrum s z μ‖ * k⁻¹ := by
    dsimp [T, certificateNewtonMap]
    have heq : μ - (certificateDysonJacobian spectrum c (E : ℂ) μ)⁻¹ *
        certificateDysonResidual spectrum s z μ - μ =
        -((certificateDysonJacobian spectrum c (E : ℂ) μ)⁻¹ *
          certificateDysonResidual spectrum s z μ) := by ring
    rw [heq, norm_neg, norm_mul]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hJinv (norm_nonneg (certificateDysonResidual spectrum s z μ))
  have hmap : Set.MapsTo T (Metric.closedBall μ ρ) (Metric.closedBall μ ρ) := by
    intro m hm
    rw [Metric.mem_closedBall, dist_eq_norm] at hm ⊢
    calc
      ‖T m - μ‖ ≤ ‖T m - T μ‖ + ‖T μ - μ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (1 / 2 : ℝ) * ‖m - μ‖ + ρ / 2 :=
        add_le_add (hLip m μ hm (by simp; exact hρ)) (hcenter.trans hres)
      _ ≤ ρ := by linarith
  have hcontract : ContractingWith (1 / 2 : NNReal)
      (hmap.restrict T (Metric.closedBall μ ρ) (Metric.closedBall μ ρ)) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro m n
      change dist (T m) (T n) ≤ ((1 / 2 : NNReal) : ℝ) * dist (m : ℂ) (n : ℂ)
      rw [dist_eq_norm, dist_eq_norm]
      norm_num
      exact hLip m n (by simpa only [Metric.mem_closedBall, dist_eq_norm] using m.property)
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using n.property)
  obtain ⟨m, hm, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    (Metric.isClosed_closedBall.isComplete) hmap hcontract (Metric.mem_closedBall_self hρ)
      (edist_ne_top μ (T μ))
  have hmnorm : ‖m - μ‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hm
  have hzroot : certificateDysonResidual spectrum s z m = 0 := by
    have hh := hfix.eq
    change m - (certificateDysonJacobian spectrum c (E : ℂ) μ)⁻¹ *
      certificateDysonResidual spectrum s z m = m at hh
    have hmul : (certificateDysonJacobian spectrum c (E : ℂ) μ)⁻¹ *
        certificateDysonResidual spectrum s z m = 0 := by linear_combination -hh
    exact (mul_eq_zero.mp hmul).resolve_left (inv_ne_zero hJnz)
  refine ⟨m, hmnorm, hzroot, ?_⟩
  have hdist : ‖m - μ‖ ≤ (1 / 2 : ℝ) * ‖m - μ‖ +
      ‖certificateDysonResidual spectrum s z μ‖ * k⁻¹ := by
    calc
      _ ≤ ‖m - T μ‖ + ‖T μ - μ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖T m - T μ‖ + ‖T μ - μ‖ := by rw [hfix.eq]
      _ ≤ _ := add_le_add (hLip m μ hmnorm (by simp; exact hρ)) hcenter
  linarith

end BlockBand.Palm
