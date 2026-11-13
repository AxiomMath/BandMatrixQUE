module
public import BlockBand.Palm.RegularityGeneralReference
public import BlockBand.Palm.RegularityHeight
public import BlockBand.Palm.RegularityGlobal
/-!
# Finite positive-height Newton descent

Starting from the root at height `1`, a finite grid of uniform Newton steps produces a root of
the finite Dyson equation with positive imaginary part at every height `η ∈ [α, 1]`
(`certificate_positive_height_zero_exists`), with constants independent of the spectrum.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Scalar constants of the Newton descent. -/
structure CertificateDescentPlan (c α : ℝ) where
  H : ℝ
  k : ℝ
  ρ : ℝ
  δ : ℝ
  H_pos : 0 < H
  k_pos : 0 < k
  ρ_pos : 0 < ρ
  δ_pos : 0 < δ
  H_eq : H = α / 2
  k_eq : k = α / (α + 1)
  ρ_H : ρ ≤ H / 2
  ρ_stable : ρ ≤ k * H ^ 3 / (16 * c)
  δ_H : δ ≤ H / 4
  δ_stable : δ ≤ k * H ^ 3 / (16 * c)
  δ_res : δ ≤ k * ρ * H ^ 2 / 4

/-- The radius and step size of the Newton descent. -/
def certificateDescentPlan {c α : ℝ} (hc : 0 < c) (hα : 0 < α) : CertificateDescentPlan c α := by
  let H := α / 2
  let k := α / (α + 1)
  let ρ := min (H / 2) (k * H ^ 3 / (16 * c))
  let δ := min (H / 4) (min (k * H ^ 3 / (16 * c)) (k * ρ * H ^ 2 / 4))
  have hH : 0 < H := by dsimp [H]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine {
    H := H
    k := k
    ρ := ρ
    δ := δ
    H_pos := hH
    k_pos := hk
    ρ_pos := hρ
    δ_pos := hδ
    H_eq := rfl
    k_eq := rfl
    ρ_H := min_le_left _ _
    ρ_stable := min_le_right _ _
    δ_H := min_le_left _ _
    δ_stable := (min_le_right _ _).trans (min_le_left _ _)
    δ_res := (min_le_right _ _).trans (min_le_right _ _) }

/-- Residual bound after a shift of the spectral parameter, from the reciprocal identity. -/
theorem certificate_residual_shift_of_zero (spectrum : ι → ℝ) {s H δ : ℝ} {z₀ z μ : ℂ}
    (hH : 0 < H) (hheight : 2 * H ≤ (z₀ + s * μ).im)
    (hδ : δ ≤ H / 4) (hshift : ‖z - z₀‖ ≤ δ)
    (hzero : certificateDysonResidual spectrum s z₀ μ = 0) :
    ‖certificateDysonResidual spectrum s z μ‖ ≤ δ * H⁻¹ ^ 2 := by
  let a₀ : ℂ := z₀ + s * μ
  let a : ℂ := z + s * μ
  have hdiff : a - a₀ = z - z₀ := by dsimp [a, a₀]; ring
  change 2 * H ≤ a₀.im at hheight
  have h₀ : H ≤ a₀.im := by linarith
  have ha : H ≤ a.im := by
    have hi := Complex.abs_im_le_norm (a - a₀)
    rw [hdiff] at hi
    have hlo := (abs_le.mp (hi.trans hshift)).1
    have heq : (z - z₀).im = a.im - a₀.im := by
      dsimp [a, a₀]
      ring
    rw [heq] at hlo
    change 2 * H ≤ a₀.im at hheight
    linarith
  have hmean := (certificateDysonResidual_eq_zero_iff spectrum s z₀ μ).mp hzero
  have heq : certificateDysonResidual spectrum s z μ =
      certificateAverage (fun i => certificateScalarResolvent (spectrum i) a₀) -
        certificateAverage (fun i => certificateScalarResolvent (spectrum i) a) := by
    change μ - certificateAverage (fun i => certificateScalarResolvent (spectrum i) a) = _
    exact congrArg (fun w : ℂ => w - certificateAverage (fun i => certificateScalarResolvent (spectrum i) a)) hmean
  rw [heq]
  unfold certificateAverage
  rw [← Finset.expect_sub_distrib]
  apply certificateAverage_norm_le_const
  intro i
  have h := certificateScalarResolvent_lipschitz (spectrum i) hH h₀ ha
  rw [norm_sub_rev a₀ a, hdiff] at h
  exact h.trans (mul_le_mul_of_nonneg_right hshift (by positivity))

/-- A zero with `Im(z + s m) > 0` has `Im m > 0`. -/
theorem certificate_zero_im_pos_of_absorber
    (spectrum : ι → ℝ) (s : ℝ) (z m : ℂ)
    (ha : 0 < (z + s * m).im) (hm : certificateDysonResidual spectrum s z m = 0) :
    0 < m.im := by
  have hA : 0 < certificateRealAverage (fun i => Complex.normSq
      (certificateScalarResolvent (spectrum i) (z + s * m))) := by
    apply Finset.expect_pos _ Finset.univ_nonempty
    intro i _
    apply Complex.normSq_pos.mpr
    unfold certificateScalarResolvent
    apply inv_ne_zero
    intro heq
    have him := congrArg Complex.im heq
    have hz : (z + s * m).im = 0 := by
      simpa only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] using him
    exact ha.ne' hz
  have hward := certificate_dyson_ward spectrum s z m hm
  have hheight : (z + s * m).im = z.im + s * m.im := by simp
  rw [hheight] at ha
  rw [hward]
  exact mul_pos ha hA

/-- One Newton step above height `α`, uniform in the spectrum. -/
theorem certificate_descent_step (spectrum : ι → ℝ) {c α s : ℝ} {z₀ z μ : ℂ}
    (hc : 0 < c) (hc1 : c < 1) (hα : 0 < α) (hs : 0 < s) (hsc : s ≤ c)
    (p : CertificateDescentPlan c α)
    (hz₀ : α ≤ z₀.im) (hμ : 0 < μ.im)
    (hzero : certificateDysonResidual spectrum s z₀ μ = 0) (hshift : ‖z - z₀‖ ≤ p.δ) :
    ∃ m : ℂ, 0 < m.im ∧ certificateDysonResidual spectrum s z m = 0 := by
  have hH := p.H_pos
  have hk := p.k_pos
  have hρ := p.ρ_pos
  have hδ := p.δ_pos
  have hs1 : s ≤ 1 := hsc.trans hc1.le
  have hz₀pos : 0 < z₀.im := hα.trans_le hz₀
  have hsm := certificate_dyson_s_mul_norm_le_one spectrum hs hs1 hz₀pos.le hμ hzero
  have hsmi : s * μ.im ≤ 1 := (mul_le_mul_of_nonneg_left (Complex.im_le_norm μ) hs.le).trans hsm
  have hden : 0 < z₀.im + s * μ.im := add_pos hz₀pos (mul_pos hs hμ)
  have hJfloor : p.k ≤ z₀.im / (z₀.im + s * μ.im) := by
    rw [p.k_eq, div_le_div_iff₀ (by positivity : 0 < α + 1) hden]
    have hmul := mul_le_mul_of_nonneg_left hsmi hα.le
    nlinarith
  have hJ := hJfloor.trans (certificate_dyson_jacobian_norm_lower spectrum hs hz₀pos hμ hzero)
  have hheight : 2 * p.H ≤ (z₀ + s * μ).im := by
    rw [p.H_eq]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    nlinarith [mul_pos hs hμ]
  have hshift' : ‖z + s * μ - (z₀ + s * μ)‖ ≤ p.δ := by simpa using hshift
  have hsρ : s * p.ρ ≤ p.ρ := by nlinarith [p.ρ_pos]
  have hshiftρ : ‖z + s * μ - (z₀ + s * μ)‖ + s * p.ρ ≤ p.H := by
    calc
      _ ≤ p.δ + p.ρ := add_le_add hshift' hsρ
      _ ≤ p.H := by linarith [p.δ_H, p.ρ_H]
  have hδS : 2 * s * p.δ * p.H⁻¹ ^ 3 ≤ p.k / 8 := by
    calc
      _ ≤ 2 * c * (p.k * p.H ^ 3 / (16 * c)) * p.H⁻¹ ^ 3 := by gcongr; exact p.δ_stable
      _ = _ := by field_simp [p.H_pos.ne', hc.ne']; ring
  have hρS : 2 * s * p.ρ * p.H⁻¹ ^ 3 ≤ p.k / 8 := by
    calc
      _ ≤ 2 * c * (p.k * p.H ^ 3 / (16 * c)) * p.H⁻¹ ^ 3 := by gcongr; exact p.ρ_stable
      _ = _ := by field_simp [p.H_pos.ne', hc.ne']; ring
  have hcoef : 2 * s * (‖z + s * μ - (z₀ + s * μ)‖ + s * p.ρ) * p.H⁻¹ ^ 3 ≤ p.k / 2 := by
    have hh : 2 * s * (‖z + s * μ - (z₀ + s * μ)‖ + s * p.ρ) * p.H⁻¹ ^ 3 ≤
        2 * s * (p.δ + p.ρ) * p.H⁻¹ ^ 3 := by gcongr
    nlinarith [p.k_pos]
  have hcon : (|s - s| * p.H⁻¹ ^ 2 +
      2 * s * (‖z + s * μ - (z₀ + s * μ)‖ + s * p.ρ) * p.H⁻¹ ^ 3) * p.k⁻¹ ≤ 1 / 2 := by
    simp only [sub_self, abs_zero, zero_mul, zero_add]
    calc
      _ ≤ (p.k / 2) * p.k⁻¹ := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by field_simp [p.k_pos.ne']
  have hraw := certificate_residual_shift_of_zero spectrum p.H_pos hheight p.δ_H hshift hzero
  have hδR : p.δ * p.H⁻¹ ^ 2 ≤ p.k * p.ρ / 4 := by
    calc
      _ ≤ (p.k * p.ρ * p.H ^ 2 / 4) * p.H⁻¹ ^ 2 := mul_le_mul_of_nonneg_right p.δ_res (by positivity)
      _ = _ := by field_simp [p.H_pos.ne']
  have hres : ‖certificateDysonResidual spectrum s z μ‖ * p.k⁻¹ ≤ p.ρ / 2 := by
    calc
      _ ≤ (p.k * p.ρ / 4) * p.k⁻¹ := mul_le_mul_of_nonneg_right (hraw.trans hδR) (by positivity)
      _ = p.ρ / 4 := by field_simp [p.k_pos.ne']
      _ ≤ p.ρ / 2 := by linarith [p.ρ_pos]
  obtain ⟨m, hmρ, hmzero, _⟩ := certificate_general_local_zero_exists spectrum s s z₀ z μ
    p.H_pos p.ρ_pos.le p.k_pos hs.le hs.le hheight hshiftρ hJ hcon hres
  have hma : 0 < (z + s * m).im := by
    have hdiff : ‖z + s * m - (z₀ + s * μ)‖ ≤ p.δ + s * p.ρ := by
      have heq : z + s * m - (z₀ + s * μ) = (z - z₀) + (s : ℂ) * (m - μ) := by ring
      rw [heq]
      calc
        _ ≤ ‖z - z₀‖ + ‖(s : ℂ) * (m - μ)‖ := norm_add_le _ _
        _ = ‖z - z₀‖ + s * ‖m - μ‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
        _ ≤ _ := by gcongr
    have hi := (abs_le.mp ((Complex.abs_im_le_norm (z + s * m - (z₀ + s * μ))).trans hdiff)).1
    simp only [Complex.sub_im] at hi
    linarith [p.H_pos, p.δ_H, p.ρ_H]
  exact ⟨m, certificate_zero_im_pos_of_absorber spectrum s z m hma hmzero, hmzero⟩

/-- Roots at every height in `[α, 1]`, by a finite grid of uniform Newton steps. -/
theorem certificate_positive_height_zero_exists (spectrum : ι → ℝ) {c α s x η : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hα : 0 < α) (hs : 0 < s) (hsc : s ≤ c)
    (hηlo : α ≤ η) (hηhi : η ≤ 1) :
    ∃ m : ℂ, 0 < m.im ∧ certificateDysonResidual spectrum s ((x : ℂ) + Complex.I * η) m = 0 := by
  let p := certificateDescentPlan hc hα
  have hδ := p.δ_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / p.δ)
  have hNpos : 0 < (N : ℝ) := (by positivity : 0 < 1 / p.δ).trans hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  let t : ℝ := (1 - η) / (N : ℝ)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hηhi) hNpos.le
  have htδ : t ≤ p.δ := by
    rw [div_lt_iff₀ p.δ_pos] at hN
    dsimp [t]
    rw [div_le_iff₀ hNpos]
    nlinarith
  let height : ℕ → ℝ := fun j => 1 - (j : ℝ) * t
  let energy : ℕ → ℂ := fun j => (x : ℂ) + Complex.I * height j
  have hNt : (N : ℝ) * t = 1 - η := by dsimp [t]; field_simp [hNne]
  have henergyim : ∀ j : ℕ, (energy j).im = height j := by
    intro j
    simp [energy]
  have hfloor : ∀ j : ℕ, j ≤ N → α ≤ (energy j).im := by
    intro j hj
    have hjreal : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
    have hh := mul_le_mul_of_nonneg_right hjreal ht0
    rw [hNt] at hh
    rw [henergyim]
    dsimp [height]
    linarith
  have hstep : ∀ j : ℕ, ‖energy (j + 1) - energy j‖ ≤ p.δ := by
    intro j
    have heq : energy (j + 1) - energy j = -Complex.I * t := by dsimp [energy, height]; push_cast; ring
    rw [heq, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact htδ
  have hroots : ∀ j : ℕ, j ≤ N → ∃ m : ℂ, 0 < m.im ∧ certificateDysonResidual spectrum s (energy j) m = 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨m, hm, _, hz⟩ := certificate_height_one_zero_exists spectrum (z := energy 0) hs (hsc.trans_lt hc1)
        (by rw [henergyim]; simp [height])
      exact ⟨m, hm, hz⟩
    | succ j ih =>
      intro hj
      obtain ⟨μ, hμ, hzero⟩ := ih (Nat.le_of_succ_le hj)
      exact certificate_descent_step spectrum hc hc1 hα hs hsc p
        (hfloor j (Nat.le_of_succ_le hj)) hμ hzero (hstep j)
  obtain ⟨m, hm, hz⟩ := hroots N le_rfl
  have hlast : height N = η := by dsimp [height]; rw [hNt]; ring
  exact ⟨m, hm, by simpa only [energy, hlast] using hz⟩
end BlockBand.Palm
