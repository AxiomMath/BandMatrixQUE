module

public import BlockBand.Palm.RegularityContinuation

/-!
# Roots on a low-height rectangle from the trace certificate

From the trace certificate `χ` alone, with radii chosen from `c, V` before the dimension, `F`,
`E` and `μ`, the finite Dyson equation has a root with uniformly positive imaginary part on a
whole low-height rectangle of variances, energies and heights, and the root at the reference
energy is within a multiple of `‖χ‖` of `μ`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Scalar radii and constants of the local construction. -/
structure CertificateLocalPlan (c V : ℝ) where
  H : ℝ
  k : ℝ
  ρ : ℝ
  δ : ℝ
  ε : ℝ
  r : ℝ
  s₀ : ℝ
  H_pos : 0 < H
  k_pos : 0 < k
  ρ_pos : 0 < ρ
  δ_pos : 0 < δ
  ε_pos : 0 < ε
  r_pos : 0 < r
  s₀_pos : 0 < s₀
  H_eq : H = c * V / 2
  k_eq : k = c * V ^ 2 / 4
  ρ_V : ρ ≤ V / 4
  ρ_H : ρ ≤ H / 2
  ρ_stable : ρ ≤ k * H ^ 3 / (16 * c)
  δ_H : δ ≤ H / 4
  δ_stable : δ ≤ k * H ^ 3 / (16 * c)
  δ_J : δ ≤ k * H ^ 2 / 4
  δ_res : δ ≤ k * ρ * H ^ 2 / 4
  ε_V : ε ≤ V / 2
  ε_stable : ε ≤ c * V ^ 3 / 4
  ε_res : ε ≤ k * ρ / 4
  r_δ : r ≤ δ / 4
  r_one : r ≤ 1 / 4
  s₀_c : s₀ ≤ c / 4
  s₀_δ : s₀ ≤ δ / 4

/-- Explicit positive radii, independent of the dimension, `F`, `E` and `μ`. -/
def certificateLocalPlan {c V : ℝ} (hc : 0 < c) (hV : 0 < V) : CertificateLocalPlan c V := by
  let H := c * V / 2
  let k := c * V ^ 2 / 4
  let ρ := min (V / 4) (min (H / 2) (k * H ^ 3 / (16 * c)))
  let δ := min (H / 4) (min (k * H ^ 3 / (16 * c)) (min (k * H ^ 2 / 4) (k * ρ * H ^ 2 / 4)))
  let ε := min (V / 2) (min (c * V ^ 3 / 4) (k * ρ / 4))
  let r := min (δ / 4) (1 / 4)
  let s₀ := min (c / 4) (δ / 4)
  have hH : 0 < H := by dsimp [H]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine {
    H := H
    k := k
    ρ := ρ
    δ := δ
    ε := ε
    r := r
    s₀ := s₀
    H_pos := hH
    k_pos := hk
    ρ_pos := hρ
    δ_pos := hδ
    ε_pos := hε
    r_pos := ?_
    s₀_pos := ?_
    H_eq := rfl
    k_eq := rfl
    ρ_V := min_le_left _ _
    ρ_H := (min_le_right _ _).trans (min_le_left _ _)
    ρ_stable := (min_le_right _ _).trans (min_le_right _ _)
    δ_H := min_le_left _ _
    δ_stable := (min_le_right _ _).trans (min_le_left _ _)
    δ_J := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    δ_res := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    ε_V := min_le_left _ _
    ε_stable := (min_le_right _ _).trans (min_le_left _ _)
    ε_res := (min_le_right _ _).trans (min_le_right _ _)
    r_δ := min_le_left _ _
    r_one := min_le_right _ _
    s₀_c := min_le_left _ _
    s₀_δ := min_le_right _ _ }
  · dsimp [r]; positivity
  · dsimp [s₀]; positivity

/-- On the local rectangle in `x, η, s`, the shift of the scalar spectral parameter is controlled,
using only `|μ| ≤ 1`. -/
theorem certificate_local_rectangle_shift {c V E x η s : ℝ} {μ : ℂ}
    (p : CertificateLocalPlan c V) (hμ : ‖μ‖ ≤ 1)
    (hslo : c - p.s₀ ≤ s) (hshi : s ≤ c) (hx : |x - E| ≤ p.r)
    (hη : 0 ≤ η) (hηr : η ≤ p.r) :
    ‖(x : ℂ) + Complex.I * η + s * μ - ((E : ℂ) + c * μ)‖ ≤ p.δ ∧
      |s - c| ≤ p.δ := by
  have hsc : |s - c| ≤ p.s₀ := by rw [abs_of_nonpos (sub_nonpos.mpr hshi)]; linarith
  have hscδ : |s - c| ≤ p.δ := by linarith [p.s₀_δ, p.δ_pos]
  refine ⟨?_, hscδ⟩
  have heq : (x : ℂ) + Complex.I * η + s * μ - ((E : ℂ) + c * μ) =
      ((x - E : ℝ) : ℂ) + Complex.I * η + ((s - c : ℝ) : ℂ) * μ := by push_cast; ring
  rw [heq]
  calc
    _ ≤ ‖((x - E : ℝ) : ℂ)‖ + ‖Complex.I * η‖ + ‖((s - c : ℝ) : ℂ) * μ‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = |x - E| + η + |s - c| * ‖μ‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hη]
    _ ≤ p.r + p.r + p.s₀ := by
      apply add_le_add
      · exact add_le_add hx hηr
      · exact (mul_le_mul_of_nonneg_left hμ (abs_nonneg _)).trans (by simpa using hsc)
    _ ≤ p.δ := by linarith [p.r_δ, p.s₀_δ, p.δ_pos]

/-- Perturbation estimate for the residual on the local rectangle. -/
theorem certificate_local_residual_bound
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E s H δ : ℝ} {μ z : ℂ}
    (hH : 0 < H) (hheight : 2 * H ≤ ((E : ℂ) + c * μ).im)
    (hδ : δ ≤ H / 4) (hshift : ‖z + s * μ - ((E : ℂ) + c * μ)‖ ≤ δ)
    (hc : 0 < c) (hμ : 0 < μ.im) :
    ‖certificateDysonResidual hF.eigenvalues s z μ‖ ≤ ‖certificateChi F c E μ‖ + δ * H⁻¹ ^ 2 := by
  let a₀ : ℂ := (E : ℂ) + c * μ
  let a : ℂ := z + s * μ
  change 2 * H ≤ a₀.im at hheight
  have h₀ : H ≤ a₀.im := by linarith
  have ha : H ≤ a.im := by
    have hi := Complex.abs_im_le_norm (a - a₀)
    have hlo := (abs_le.mp (hi.trans hshift)).1
    simp only [Complex.sub_im] at hlo
    change 2 * H ≤ a₀.im at hheight
    linarith
  have havg : ‖certificateAverage (fun i => certificateScalarResolvent (hF.eigenvalues i) a₀) -
      certificateAverage (fun i => certificateScalarResolvent (hF.eigenvalues i) a)‖ ≤ δ * H⁻¹ ^ 2 := by
    unfold certificateAverage
    rw [← Finset.expect_sub_distrib]
    apply certificateAverage_norm_le_const
    intro i
    have h := certificateScalarResolvent_lipschitz (hF.eigenvalues i) hH h₀ ha
    rw [norm_sub_rev a₀ a] at h
    exact h.trans (mul_le_mul_of_nonneg_right hshift (by positivity))
  have hchi := certificateChi_eq_neg_residual F hF (E := E) hc hμ
  have heq : certificateDysonResidual hF.eigenvalues s z μ =
      -certificateChi F c E μ +
        (certificateAverage (fun i => certificateScalarResolvent (hF.eigenvalues i) a₀) -
          certificateAverage (fun i => certificateScalarResolvent (hF.eigenvalues i) a)) := by
    rw [hchi]
    unfold certificateDysonResidual
    dsimp [a, a₀]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (by simp) havg)

/-- A root with uniformly positive imaginary part on the whole low-height rectangle, from `χ`
alone. -/
theorem certificate_uniform_local_zero
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c V E s : ℝ} {μ z : ℂ}
    (hc : 0 < c) (hV : 0 < V) (hVμ : V ≤ μ.im)
    (p : CertificateLocalPlan c V)
    (hchi : ‖certificateChi F c E μ‖ ≤ p.ε)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hshift : ‖z + s * μ - ((E : ℂ) + c * μ)‖ ≤ p.δ) (hsc : |s - c| ≤ p.δ) :
    ∃ m : ℂ, 3 * V / 4 ≤ m.im ∧ certificateDysonResidual hF.eigenvalues s z m = 0 ∧
      ‖m - μ‖ ≤ p.ρ ∧ ‖m - μ‖ ≤ 2 * ‖certificateDysonResidual hF.eigenvalues s z μ‖ * p.k⁻¹ := by
  have hH := p.H_pos
  have hk := p.k_pos
  have hρ := p.ρ_pos
  have hδ := p.δ_pos
  have hμ : 0 < μ.im := hV.trans_le hVμ
  have hsmallV : ‖certificateChi F c E μ‖ ≤ μ.im / 2 := by linarith [p.ε_V]
  have hsmallS : ‖certificateChi F c E μ‖ ≤ c * μ.im ^ 3 / 4 := by
    apply (hchi.trans p.ε_stable).trans
    gcongr
  have hJac := certificate_jacobian_stable F hF hc hμ hsmallV hsmallS
  have hJ : p.k ≤ ‖certificateDysonJacobian hF.eigenvalues c (E : ℂ) μ‖ := by
    apply le_trans _ ((Complex.re_le_norm _).trans' hJac)
    rw [p.k_eq]
    gcongr
  have hheight : 2 * p.H ≤ ((E : ℂ) + c * μ).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero, zero_add]
    rw [p.H_eq]
    nlinarith
  have hsρ : s * p.ρ ≤ p.ρ := by nlinarith [p.ρ_pos]
  have hshiftρ : ‖z + s * μ - ((E : ℂ) + c * μ)‖ + s * p.ρ ≤ p.H := by
    calc
      _ ≤ p.δ + p.ρ := add_le_add hshift hsρ
      _ ≤ p.H := by linarith [p.ρ_H, p.δ_H]
  have hδJ : p.δ * p.H⁻¹ ^ 2 ≤ p.k / 4 := by
    calc
      _ ≤ (p.k * p.H ^ 2 / 4) * p.H⁻¹ ^ 2 := mul_le_mul_of_nonneg_right p.δ_J (by positivity)
      _ = _ := by field_simp [p.H_pos.ne']
  have hδS : 2 * c * p.δ * p.H⁻¹ ^ 3 ≤ p.k / 8 := by
    calc
      _ ≤ 2 * c * (p.k * p.H ^ 3 / (16 * c)) * p.H⁻¹ ^ 3 := by gcongr; exact p.δ_stable
      _ = _ := by field_simp [p.H_pos.ne', hc.ne']; ring
  have hρS : 2 * c * p.ρ * p.H⁻¹ ^ 3 ≤ p.k / 8 := by
    calc
      _ ≤ 2 * c * (p.k * p.H ^ 3 / (16 * c)) * p.H⁻¹ ^ 3 := by gcongr; exact p.ρ_stable
      _ = _ := by field_simp [p.H_pos.ne', hc.ne']; ring
  have hcoef : |s - c| * p.H⁻¹ ^ 2 +
      2 * c * (‖z + s * μ - ((E : ℂ) + c * μ)‖ + s * p.ρ) * p.H⁻¹ ^ 3 ≤ p.k / 2 := by
    have h₁ := (mul_le_mul_of_nonneg_right hsc (by positivity)).trans hδJ
    have h₂ : 2 * c * (‖z + s * μ - ((E : ℂ) + c * μ)‖ + s * p.ρ) * p.H⁻¹ ^ 3 ≤
        2 * c * (p.δ + p.ρ) * p.H⁻¹ ^ 3 := by gcongr
    nlinarith
  have hcon : (|s - c| * p.H⁻¹ ^ 2 +
      2 * c * (‖z + s * μ - ((E : ℂ) + c * μ)‖ + s * p.ρ) * p.H⁻¹ ^ 3) * p.k⁻¹ ≤ 1 / 2 := by
    calc
      _ ≤ (p.k / 2) * p.k⁻¹ := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by field_simp [p.k_pos.ne']
  have hδR : p.δ * p.H⁻¹ ^ 2 ≤ p.k * p.ρ / 4 := by
    calc
      _ ≤ (p.k * p.ρ * p.H ^ 2 / 4) * p.H⁻¹ ^ 2 := mul_le_mul_of_nonneg_right p.δ_res (by positivity)
      _ = _ := by field_simp [p.H_pos.ne']
  have hresraw := certificate_local_residual_bound F hF p.H_pos hheight p.δ_H hshift hc hμ
  have hres : ‖certificateDysonResidual hF.eigenvalues s z μ‖ * p.k⁻¹ ≤ p.ρ / 2 := by
    have hsum : ‖certificateChi F c E μ‖ + p.δ * p.H⁻¹ ^ 2 ≤ p.k * p.ρ / 2 := by
      linarith [hchi.trans p.ε_res]
    calc
      _ ≤ (p.k * p.ρ / 2) * p.k⁻¹ := mul_le_mul_of_nonneg_right (hresraw.trans hsum) (by positivity)
      _ = _ := by field_simp [p.k_pos.ne']
  obtain ⟨m, hmρ, hmzero, hmdist⟩ := certificate_local_zero_exists hF.eigenvalues c s E z μ
    p.H_pos p.ρ_pos.le p.k_pos hc.le hs hheight hshiftρ hJ hcon hres
  refine ⟨m, ?_, hmzero, hmρ, hmdist⟩
  have hi := (abs_le.mp ((Complex.abs_im_le_norm (m - μ)).trans hmρ)).1
  simp only [Complex.sub_im] at hi
  linarith [p.ρ_V]

/-- The low-height rectangle statement, with all constants chosen from `c, V` before the
dimension, `F`, `E`, `μ` and the point. -/
theorem certificate_chi_only_local_rectangle {c V : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hV : 0 < V) :
    ∃ ε r s₀ ρ : ℝ, 0 < ε ∧ 0 < r ∧ 0 < s₀ ∧ s₀ < c / 2 ∧
      0 < ρ ∧ ρ ≤ V / 4 ∧ r ≤ 1 / 4 ∧
      ∀ (F : Matrix ι ι ℂ) (hF : F.IsHermitian) (E : ℝ) (μ : ℂ),
        V ≤ μ.im → ‖μ‖ ≤ 1 → ‖certificateChi F c E μ‖ ≤ ε →
        ∀ s : ℝ, c - s₀ ≤ s → s ≤ c →
        ∀ x : ℝ, |x - E| ≤ r → ∀ η : ℝ, 0 ≤ η → η ≤ r →
        ∃ m : ℂ, 3 * V / 4 ≤ m.im ∧
          certificateDysonResidual hF.eigenvalues s ((x : ℂ) + Complex.I * η) m = 0 ∧
          ‖m - μ‖ ≤ ρ := by
  let p := certificateLocalPlan hc hV
  refine ⟨p.ε, p.r, p.s₀, p.ρ, p.ε_pos, p.r_pos, p.s₀_pos, ?_, p.ρ_pos,
    p.ρ_V, p.r_one, ?_⟩
  · linarith [p.s₀_c]
  · intro F hF E μ hVμ hμnorm hchi s hslo hshi x hx η hη hηr
    have hs : 0 ≤ s := by linarith [p.s₀_c]
    have hs1 : s ≤ 1 := hshi.trans hc1.le
    obtain ⟨hshift, hsc⟩ := certificate_local_rectangle_shift p hμnorm hslo hshi hx hη hηr
    obtain ⟨m, him, hmzero, hmρ, _⟩ := certificate_uniform_local_zero F hF hc hV hVμ p hchi hs hs1 hshift hsc
    exact ⟨m, him, hmzero, hmρ⟩

/-- At the real reference energy, a root within a multiple of `‖χ‖` of `μ`. -/
theorem certificate_chi_only_reference_zero
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c V E : ℝ} {μ : ℂ}
    (hc : 0 < c) (hc1 : c < 1) (hV : 0 < V) (hVμ : V ≤ μ.im)
    (hchi : ‖certificateChi F c E μ‖ ≤ (certificateLocalPlan hc hV).ε) :
    ∃ m : ℂ, 3 * V / 4 ≤ m.im ∧ certificateDysonResidual hF.eigenvalues c (E : ℂ) m = 0 ∧
      ‖m - μ‖ ≤ (certificateLocalPlan hc hV).ρ ∧
      ‖m - μ‖ ≤ 8 / (c * V ^ 2) * ‖certificateChi F c E μ‖ := by
  let p := certificateLocalPlan hc hV
  obtain ⟨m, him, hmzero, hmρ, hmdist⟩ := certificate_uniform_local_zero F hF (s := c) (z := (E : ℂ)) hc hV hVμ p hchi hc.le hc1.le
    (by simp; exact p.δ_pos.le) (by simp; exact p.δ_pos.le)
  refine ⟨m, him, hmzero, hmρ, ?_⟩
  have hχ := certificateChi_eq_neg_residual F hF (E := E) hc (hV.trans_le hVμ)
  have hnorm : ‖certificateDysonResidual hF.eigenvalues c (E : ℂ) μ‖ = ‖certificateChi F c E μ‖ := by
    rw [hχ, norm_neg]
  rw [hnorm, p.k_eq] at hmdist
  convert hmdist using 1
  field_simp [hc.ne', hV.ne']
  ring

end BlockBand.Palm
