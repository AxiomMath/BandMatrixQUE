module

public import BlockBand.Density.Smooth
public import BlockBand.Counting.PoissonUnsmoothingAnalysis
public import BlockBand.Wegner.PoissonRepresentationMatrix

/-!
# Stieltjes transform of the mean density from diagonal resolvent means

Law: the physical law of any admissible `p` and any realization. `z = e + iη`, `η > 0`,
`G = (H - z)⁻¹`.
* `trace_resolvent_eq_sum` (deterministic, Hermitian `A`): `Tr (A - z)⁻¹ = Σ_j (λ_j - z)⁻¹`;
* `norm_resolvent_apply_le`: `‖G_ab‖ ≤ η⁻¹` for Hermitian `A`;
* `sum_integral_im_resolvent`: `Σ_x Im E G_xx = π N (P_η ∗ ρ_{n,W})(e)`;
* `abs_poissonSmoothTest_sub_le`: if `‖E G_xx - m‖ ≤ ε` for every site `x`, then
  `|(P_η ∗ ρ_{n,W})(e) - π⁻¹ Im m| ≤ ε/π`.
No hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory Set Filter BlockBand.Counting BlockBand.External Matrix
open scoped ENNReal NNReal Topology ComplexOrder

section Deterministic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sum_eigenvalues_eq_sum_increasing {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    ∑ i, f (hA.eigenvalues i) =
      ∑ j : Fin (Fintype.card ι), f (Foundations.Spectral.increasingEigenvalue hA j) := by
  unfold Matrix.IsHermitian.eigenvalues Foundations.Spectral.increasingEigenvalue
  rw [Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => f (hA.eigenvalues₀ k))]
  exact (Equiv.sum_comp Fin.revPerm (fun k => f (hA.eigenvalues₀ k))).symm

/-- `Tr (A - z)⁻¹ = Σ_j (λ_j - z)⁻¹` for Hermitian `A` and nonreal `z`. -/
theorem trace_resolvent_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ((A - z • (1 : Matrix ι ι ℂ))⁻¹).trace =
      ∑ j : Fin (Fintype.card ι),
        (((Foundations.Spectral.increasingEigenvalue hA j : ℝ) : ℂ) - z)⁻¹ := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU1 : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hU2 : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  set lam : ι → ℂ := fun i => ((hA.eigenvalues i : ℝ) : ℂ)
  have hspec : A = U * Matrix.diagonal lam * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hne : ∀ i, lam i - z ≠ 0 := by
    intro i h
    have := congrArg Complex.im h
    simp [lam] at this
    exact hz this
  have hshift : A - z • (1 : Matrix ι ι ℂ) =
      U * Matrix.diagonal (fun i => lam i - z) * star U := by
    have : Matrix.diagonal (fun i => lam i - z) = Matrix.diagonal lam - z • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, ← hspec, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hU1]
  have hinv : (A - z • (1 : Matrix ι ι ℂ))⁻¹ =
      U * Matrix.diagonal (fun i => (lam i - z)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    rw [hshift]
    calc U * Matrix.diagonal (fun i => lam i - z) * star U *
          (U * Matrix.diagonal (fun i => (lam i - z)⁻¹) * star U)
        = U * (Matrix.diagonal (fun i => lam i - z) * (star U * U) *
            Matrix.diagonal (fun i => (lam i - z)⁻¹)) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU2, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          have : (fun i => (lam i - z) * (lam i - z)⁻¹) = fun _ => (1 : ℂ) := by
            funext i
            exact mul_inv_cancel₀ (hne i)
          rw [this, Matrix.diagonal_one, Matrix.mul_one, hU1]
  rw [hinv, Matrix.trace_mul_cycle, hU2, Matrix.one_mul, Matrix.trace_diagonal]
  exact sum_eigenvalues_eq_sum_increasing hA (fun t => ((t : ℂ) - z)⁻¹)

theorem im_inv_sub (t e η : ℝ) (hη : 0 < η) :
    (((t : ℂ) - ((e : ℂ) + (η : ℂ) * Complex.I))⁻¹).im = Real.pi * Counting.poissonKernel η (t - e) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_add, add_zero, zero_sub, Counting.poissonKernel]
  have : (t - e) * (t - e) + -η * -η ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (t - e), mul_pos hη hη])
  have hπ := Real.pi_pos
  field_simp

/-- `‖(A - z)⁻¹ a b‖ ≤ η⁻¹` for Hermitian `A`, `z = e + iη`, `η > 0`. -/
theorem norm_resolvent_apply_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (e : ℝ) {η : ℝ}
    (hη : 0 < η) (a b : ι) :
    ‖(A - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))⁻¹ a b‖ ≤ η⁻¹ := by
  set B : Matrix ι ι ℂ := (e : ℂ) • (1 : Matrix ι ι ℂ) - A
  have h1 : ((e : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  have hB : B.IsHermitian := h1.sub hA
  set N' := Wegner.absorbedPencil B 0 η 0
  have hN' : Wegner.HasImMargin η N' :=
    Wegner.hasImMargin_absorbedPencil hB Matrix.PosSemidef.zero η (by simp)
  have hrel : A - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) = -N' := by
    simp only [N', Wegner.absorbedPencil, B, zero_smul, add_zero, add_smul]
    abel
  have hinv : (A - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))⁻¹ = -N'⁻¹ := by
    rw [hrel]
    apply Matrix.inv_eq_left_inv
    rw [neg_mul_neg, Matrix.nonsing_inv_mul _ (hN'.isUnit_det hη)]
  rw [hinv, Matrix.neg_apply, norm_neg]
  exact hN'.norm_inv_apply_le hη a b

theorem measurable_resolvent_apply (z : ℂ) (a b : ι) :
    Measurable fun H : Matrix ι ι ℂ => (H - z • (1 : Matrix ι ι ℂ))⁻¹ a b := by
  have hfun : (fun H : Matrix ι ι ℂ => (H - z • (1 : Matrix ι ι ℂ))⁻¹ a b) =
      fun H => ((H - z • (1 : Matrix ι ι ℂ)).det)⁻¹ *
        (H - z • (1 : Matrix ι ι ℂ)).adjugate a b := by
    funext H
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  have hc1 : Continuous fun H : Matrix ι ι ℂ => (H - z • (1 : Matrix ι ι ℂ)).det :=
    (continuous_id.sub continuous_const).matrix_det
  have hc2 : Continuous fun H : Matrix ι ι ℂ => (H - z • (1 : Matrix ι ι ℂ)).adjugate a b :=
    (continuous_id.sub continuous_const).matrix_adjugate.matrix_elem a b
  rw [hfun]
  exact (hc1.measurable.inv).mul hc2.measurable

end Deterministic

/-- Resolvent entries are integrable under the physical law (bounded by `η⁻¹` a.s.). -/
theorem integrable_resolvent_apply (p : Parameters) (model : p.GaussianRingModel) (e : ℝ)
    {η : ℝ} (hη : 0 < η) (a b : p.Site) :
    Integrable (fun H : p.SiteMatrix =>
      (H - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : p.SiteMatrix))⁻¹ a b)
      (model.law : Measure p.SiteMatrix) :=
  (integrable_const (η⁻¹)).mono' (measurable_resolvent_apply _ a b).aestronglyMeasurable
    (by filter_upwards [model.isPhysical.1] with H hH using norm_resolvent_apply_le hH e hη a b)

/-- `∫ Σ_j F(λ_j) dP = N ∫ ρ_{n,W} F` for bounded continuous `F`. -/
theorem integral_sum_physicalEigenvalue (p : Parameters) (model : p.GaussianRingModel)
    (F : ℝ → ℝ) (hF : Continuous F) {B : ℝ} (hB : ∀ x, |F x| ≤ B) :
    ∫ H, ∑ j, F (physicalEigenvalue p H j) ∂(model.law : Measure p.SiteMatrix) =
      (p.N : ℝ) * ∫ x, meanDensity p model x * F x := by
  have hFint : ∀ (Q : Measure ℝ) [IsFiniteMeasure Q], Integrable F Q := fun Q _ =>
    (integrable_const B).mono' hF.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hμ := congrArg (fun m : Measure ℝ => ∫ x, F x ∂m)
    (meanEmpiricalMeasure_eq_withDensity p model)
  have hden : (fun e => ENNReal.ofReal (meanDensity p model e)) =
      fun e => (((meanDensity p model e).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hden, integral_withDensity_eq_integral_smul (f := fun e => (meanDensity p model e).toNNReal)
    (measurable_real_toNNReal.comp (contDiff_meanDensity p model).continuous.measurable) F] at hμ
  have hsm : ∀ x, (meanDensity p model x).toNNReal • F x = meanDensity p model x * F x := by
    intro x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (meanDensity_pos p model x).le, smul_eq_mul]
  simp_rw [hsm] at hμ
  rw [← hμ]
  unfold Internal.Contracts.Inputs.meanEmpiricalMeasure
  have hI := integral_finiteSpectralIntensity (model.law : Measure p.SiteMatrix)
    (fun H i => physicalEigenvalue p H i) (fun i => measurable_physicalEigenvalue p i) F (hFint _)
  simp only [physicalEigenvalue] at hI ⊢
  rw [integral_smul_measure, hI]
  have hN : (p.N : ℝ) ≠ 0 := by exact_mod_cast p.N_pos.ne'
  rw [smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← mul_assoc, mul_inv_cancel₀ hN,
    one_mul]

theorem poissonKernel_le (η : ℝ) (hη : 0 < η) (t : ℝ) : Counting.poissonKernel η t ≤ 1 / (Real.pi * η) := by
  unfold Counting.poissonKernel
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg t, Real.pi_pos, mul_pos Real.pi_pos hη]

/-- `Σ_x Im E G_xx(e+iη) = π N (P_η ∗ ρ_{n,W})(e)`. -/
theorem sum_integral_im_resolvent (p : Parameters) (model : p.GaussianRingModel) (e : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∑ x, (∫ H, (H - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : p.SiteMatrix))⁻¹ x x
      ∂(model.law : Measure p.SiteMatrix)).im =
      Real.pi * (p.N : ℝ) * poissonSmoothTest η (meanDensity p model) e := by
  set z : ℂ := (e : ℂ) + (η : ℂ) * Complex.I
  have hz : z.im ≠ 0 := by simp [z, hη.ne']
  have hint := integrable_resolvent_apply p model e hη
  have hsum_int : ∫ H, ∑ x, (H - z • (1 : p.SiteMatrix))⁻¹ x x ∂(model.law : Measure p.SiteMatrix) =
      ∑ x, ∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ x x ∂(model.law : Measure p.SiteMatrix) :=
    integral_finsetSum _ (fun x _ => hint x x)
  have him : (∫ H, ∑ x, (H - z • (1 : p.SiteMatrix))⁻¹ x x ∂(model.law : Measure p.SiteMatrix)).im =
      ∫ H, (∑ x, (H - z • (1 : p.SiteMatrix))⁻¹ x x).im ∂(model.law : Measure p.SiteMatrix) :=
    (integral_im (integrable_finsetSum _ (fun x _ => hint x x))).symm
  rw [← Complex.im_sum, ← hsum_int, him]
  have hae : (fun H : p.SiteMatrix => (∑ x, (H - z • (1 : p.SiteMatrix))⁻¹ x x).im) =ᵐ[
      (model.law : Measure p.SiteMatrix)]
      fun H => ∑ j, Real.pi * Counting.poissonKernel η (physicalEigenvalue p H j - e) := by
    filter_upwards [model.isPhysical.1] with H hH
    have htr : ∑ x, (H - z • (1 : p.SiteMatrix))⁻¹ x x = ((H - z • (1 : p.SiteMatrix))⁻¹).trace :=
      rfl
    rw [htr, trace_resolvent_eq_sum hH hz]
    change (∑ j, (((Foundations.Spectral.increasingEigenvalue hH j : ℝ) : ℂ) - z)⁻¹).im = _
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [im_inv_sub _ e η hη]
    have hj : physicalEigenvalue p H j = Foundations.Spectral.increasingEigenvalue hH j :=
      congrFun (increasingEigenvalue_congr (p.gaussianReconstruction_gaussianExtraction H hH)
        (p.physicalHermitianVersion H).2 hH) j
    rw [hj]
  rw [integral_congr_ae hae]
  have hF : Continuous fun t => Real.pi * Counting.poissonKernel η (t - e) :=
    continuous_const.mul ((Counting.continuous_poissonKernel hη).comp
      (continuous_id.sub continuous_const))
  rw [integral_sum_physicalEigenvalue p model _ hF (B := Real.pi * (1 / (Real.pi * η)))
    (fun t => by
      rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le (poissonKernel_nonneg hη _))]
      exact mul_le_mul_of_nonneg_left (poissonKernel_le η hη _) Real.pi_pos.le)]
  unfold poissonSmoothTest
  have hsub := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun t => Counting.poissonKernel η t * meanDensity p model (e + t)) e
  simp only [add_sub_cancel] at hsub
  rw [← hsub]
  have : ∀ x, meanDensity p model x * (Real.pi * Counting.poissonKernel η (x - e)) =
      Real.pi * (Counting.poissonKernel η (x - e) * meanDensity p model x) := fun x => by ring
  simp_rw [this]
  rw [integral_const_mul]
  ring

/-- **Averaging the imaginary part.** If every diagonal resolvent mean is within `ε` of `m`,
then `|(P_η ∗ ρ_{n,W})(e) - π⁻¹ Im m| ≤ ε/π`. -/
theorem abs_poissonSmoothTest_sub_le (p : Parameters) (model : p.GaussianRingModel) (e : ℝ)
    {η ε : ℝ} (hη : 0 < η) (m : ℂ)
    (hx : ∀ x : p.Site, ‖(∫ H, (H - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : p.SiteMatrix))⁻¹ x x
      ∂(model.law : Measure p.SiteMatrix)) - m‖ ≤ ε) :
    |poissonSmoothTest η (meanDensity p model) e - m.im / Real.pi| ≤ ε / Real.pi := by
  have hS := sum_integral_im_resolvent p model e hη
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hcard : (Finset.univ : Finset p.Site).card = p.N := by
    rw [Finset.card_univ, p.card_site]
  have hsum : Real.pi * (p.N : ℝ) * (poissonSmoothTest η (meanDensity p model) e - m.im / Real.pi) =
      ∑ x : p.Site, ((∫ H, (H - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : p.SiteMatrix))⁻¹ x x
        ∂(model.law : Measure p.SiteMatrix)) - m).im := by
    rw [mul_sub, ← hS]
    simp only [Complex.sub_im, Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  have hbound : |∑ x : p.Site, ((∫ H, (H - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : p.SiteMatrix))⁻¹ x x
      ∂(model.law : Measure p.SiteMatrix)) - m).im| ≤ (p.N : ℝ) * ε := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => (Complex.abs_im_le_norm _).trans (hx x)).trans ?_
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  rw [← hsum, abs_mul, abs_of_pos (by positivity)] at hbound
  rw [le_div_iff₀ Real.pi_pos]
  have : Real.pi * (p.N : ℝ) * |poissonSmoothTest η (meanDensity p model) e - m.im / Real.pi| ≤
      (p.N : ℝ) * ε := hbound
  nlinarith

end BlockBand.Density
