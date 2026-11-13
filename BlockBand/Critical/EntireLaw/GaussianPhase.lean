module

public import BlockBand.Coarea.ProjectiveHaar

/-!
# The entire law: Gaussian integrals of Hermitian phases

For a standard circular Gaussian vector `g` and a Hermitian matrix `A` with eigenvalues `λ_k`,
`E exp(-i s g^*Ag) = Π_k (1 + i s λ_k)⁻¹` (`integral_circularVectorLaw_hermitian_phase`), and
`det(1 + c A) = Π_k (1 + c λ_k)`. These identify the Gaussian phase averages with inverse
determinants in the finite-width moment identity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.ProjectiveHaar
open scoped ComplexConjugate NNReal

/-- One real coordinate: `E exp(-i s x²) = π^{-1/2} (π/(1 + i s))^{1/2}` for `x ~ N(0, 1/2)`. -/
theorem integral_gaussianHalf_phase (s : ℝ) :
    ∫ x, Complex.exp (-(Complex.I * s) * ((x : ℂ) ^ 2)) ∂gaussianReal 0 (1 / 2 : ℝ≥0) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 + Complex.I * s)) ^ (1 / 2 : ℂ) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num),
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 _)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [gaussianPDF_half]
  have hb : 0 < (1 + Complex.I * s).re := by simp
  rw [← integral_gaussian_complex hb, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  push_cast
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- One circular coordinate: `E exp(-i s |w|²) = (1 + i s)⁻¹`. -/
theorem integral_circularLawOne_phase (s : ℝ) :
    ∫ w, Complex.exp (-(Complex.I * s) * (Complex.normSq w : ℂ)) ∂circularLawOne =
      (1 + Complex.I * s)⁻¹ := by
  unfold circularLawOne
  rw [integral_map Complex.measurableEquivPi.symm.measurable.aemeasurable
    (by fun_prop)]
  have h : ∀ x : Fin 2 → ℝ, Complex.exp (-(Complex.I * s) *
      (Complex.normSq (Complex.measurableEquivPi.symm x) : ℂ)) =
      ∏ k, Complex.exp (-(Complex.I * s) * ((x k : ℂ) ^ 2)) := by
    intro x
    rw [Fin.prod_univ_two, ← Complex.exp_add]
    congr 1
    simp only [Complex.measurableEquivPi_symm_apply, Complex.normSq_apply]
    simp
    ring
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (fun (_ : Fin 2) (x : ℝ) => Complex.exp (-(Complex.I * s) * ((x : ℂ) ^ 2))),
    Fin.prod_univ_two, integral_gaussianHalf_phase]
  have hb : (1 + Complex.I * s) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this
  have hsq : (((Real.pi : ℂ) / (1 + Complex.I * s)) ^ (1 / 2 : ℂ)) ^ 2 =
      (Real.pi : ℂ) / (1 + Complex.I * s) := by
    rw [← Complex.cpow_nat_mul]; norm_num
  have hpi : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = Real.pi := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  calc _ = (((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2)⁻¹ *
        (((Real.pi : ℂ) / (1 + Complex.I * s)) ^ (1 / 2 : ℂ)) ^ 2 := by
          ring
    _ = _ := by rw [hsq, hpi]; field_simp

/-- Diagonal quadratic form: `E exp(-i s Σ_k d_k |g_k|²) = Π_k (1 + i s d_k)⁻¹`. -/
theorem integral_circularVectorLaw_diag_phase {ι : Type*} [Fintype ι] (s : ℝ) (d : ι → ℝ) :
    ∫ g, Complex.exp (-(Complex.I * s) * ∑ k, (d k : ℂ) * (Complex.normSq (g k) : ℂ))
        ∂circularVectorLaw ι = ∏ k, (1 + Complex.I * ((s * d k : ℝ) : ℂ))⁻¹ := by
  rw [circularVectorLaw_eq_pi]
  have h : ∀ g : ι → ℂ, Complex.exp (-(Complex.I * s) * ∑ k, (d k : ℂ) * (Complex.normSq (g k) : ℂ)) =
      ∏ k, Complex.exp (-(Complex.I * ((s * d k : ℝ) : ℂ)) * (Complex.normSq (g k) : ℂ)) := by
    intro g
    rw [← Complex.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun (k : ι) (w : ℂ) => Complex.exp (-(Complex.I * ((s * d k : ℝ) : ℂ)) * (Complex.normSq w : ℂ)))]
  exact Finset.prod_congr rfl fun k _ => integral_circularLawOne_phase _

/-- Hermitian quadratic form: `E exp(-i s g^*Ag) = Π_k (1 + i s λ_k)⁻¹` (`λ` the eigenvalues). -/
theorem integral_circularVectorLaw_hermitian_phase {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (s : ℝ) :
    ∫ g, Complex.exp (-(Complex.I * s) * (star g ⬝ᵥ (A *ᵥ g))) ∂circularVectorLaw ι =
      ∏ k, (1 + Complex.I * ((s * hA.eigenvalues k : ℝ) : ℂ))⁻¹ := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : U ∈ Matrix.unitaryGroup ι ℂ := hA.eigenvectorUnitary.2
  have hD : star U * A * U = Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    have := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [U] using this
  have hm : Measurable (fun g : ι → ℂ => U *ᵥ g) :=
    (Matrix.toLin' U).continuous_of_finiteDimensional.measurable
  rw [← circularVectorLaw_map_unitary hU, integral_map hm.aemeasurable (by fun_prop)]
  rw [← integral_circularVectorLaw_diag_phase s hA.eigenvalues]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  congr 2
  have h1 : star (U *ᵥ g) ⬝ᵥ (A *ᵥ (U *ᵥ g)) = star g ⬝ᵥ ((star U * A * U) *ᵥ g) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  rw [h1, hD]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def]
  rw [mul_left_comm]
  rfl

/-- `det(1 + c A) = Π_k (1 + c λ_k)` for Hermitian `A`. -/
theorem det_one_add_smul_of_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℂ) :
    ((1 : Matrix ι ι ℂ) + c • A).det = ∏ k, (1 + c * (hA.eigenvalues k : ℂ)) := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hsU : star U * U = 1 := Unitary.coe_star_mul_self _
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hAeq : A = U * D * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have h1 : (1 : Matrix ι ι ℂ) + c • A = U * (1 + c • D) * star U := by
    rw [hAeq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, Matrix.mul_smul,
      Matrix.smul_mul]
  have h2 : (1 : Matrix ι ι ℂ) + c • D = Matrix.diagonal fun k => 1 + c * (hA.eigenvalues k : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [D]
    · simp [D, hij, Matrix.one_apply_ne hij]
  rw [h1, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hUU, Matrix.det_one,
    one_mul, h2, Matrix.det_diagonal]

end BlockBand.Critical.EntireLaw
