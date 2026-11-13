module

public import BlockBand.Coarea.ProjectiveHaar
public import BlockBand.Endpoints.Clock.SmallBall
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The circular Gaussian Laplace identity `E_h exp(-h*Ah) = det(I + A)⁻¹`

Law: `h ~ CN(0, I_ι)`, the contract `circularVectorLaw ι` (independent real and imaginary parts
of variance `1/2`, `E|h_a|² = 1`) on an arbitrary finite index type `ι`.

Proved here (unconditional; no contract is consumed):
* `integral_exp_neg_mul_normSq_circularLawOne`: `E exp(-t|z|²) = (1+t)⁻¹`, `t ≥ 0`;
* `integral_exp_neg_quadForm_circular` (**the Gaussian Laplace identity**): for every
  positive semidefinite `A`, `E_h exp(-Re h*Ah) = (Re det(I + A))⁻¹`, with
  `det(I + A) = ∏ (1 + λ_a)` real (`CommonPortRatios.det_one_add_eq_prod_eigenvalues`);
* `integral_exp_neg_quadForm_conjTranspose_mul_self_eq` (duality through Sylvester's identity):
  for every rectangular `B : ι × κ`, `E_g exp(-‖Bg‖²) = E_h exp(-‖Bᴴh‖²)`;
* `integral_exp_neg_quadForm_mulVec_eq` (transfer of a probe): for `F = BᴴB` and every
  `L : ι × κ`, `E_g exp(-Re (Lg)*F(Lg)) = E_h exp(-Re (Bᴴh)*(LLᴴ)(Bᴴh))`;
* `integral_exp_neg_quadForm_le_inv_one_add_trace`: `E_h exp(-Re h*Ah) ≤ (1 + Re Tr A)⁻¹`;
  (in clock units, `integral_exp_neg_clock_div_le` in `CommonPortRatiosFamily`:
  `E_h exp(-X̃₀/u) ≤ u` for `X̃₀ = Re h*Ph/Re Tr P`; the indicator bound `P(X̃₀ < u) ≤ e u` is
  used only in the exponential form `1_{x<u} ≤ e·e^{-x/u}`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.ProjectiveHaar
open scoped ENNReal NNReal ComplexOrder Matrix

/-!
## 1. One coordinate
-/

/-- `E exp(-t x²) = (1+t)^{-1/2}` for `x ~ N(0,1/2)` and `t ≥ 0`. -/
theorem integral_exp_neg_mul_sq_gaussianReal_half {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, Real.exp (-(t * x ^ 2)) ∂gaussianReal 0 (1 / 2 : ℝ≥0) = Real.sqrt (1 + t)⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have hfun : (fun x : ℝ => gaussianPDFReal 0 (1 / 2 : ℝ≥0) x • Real.exp (-(t * x ^ 2))) =
      fun x => (Real.sqrt Real.pi)⁻¹ * Real.exp (-(1 + t) * x ^ 2) := by
    funext x
    rw [gaussianPDFReal, smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    · push_cast; ring_nf
    · push_cast; ring
  rw [hfun, integral_const_mul, integral_gaussian]
  have hpi := Real.pi_pos
  have h1t : 0 < 1 + t := by linarith
  rw [Real.sqrt_div hpi.le, Real.sqrt_inv, ← mul_div_assoc, inv_mul_cancel₀ (by positivity),
    one_div]

/-- `E exp(-t|z|²) = (1+t)⁻¹` for the one-coordinate standard circular law and `t ≥ 0`. -/
theorem integral_exp_neg_mul_normSq_circularLawOne {t : ℝ} (ht : 0 ≤ t) :
    ∫ z, Real.exp (-(t * Complex.normSq z)) ∂circularLawOne = (1 + t)⁻¹ := by
  unfold circularLawOne
  rw [integral_map_equiv]
  have hfun : (fun x : Fin 2 → ℝ => Real.exp (-(t * Complex.normSq
      (Complex.measurableEquivPi.symm x)))) =
      fun x => ∏ i : Fin 2, Real.exp (-(t * x i ^ 2)) := by
    funext x
    rw [Fin.prod_univ_two, ← Real.exp_add]
    congr 1
    simp [Complex.measurableEquivPi_symm_apply, Complex.normSq_apply]
    ring
  rw [hfun, integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun _ (x : ℝ) => Real.exp (-(t * x ^ 2))),
    Fin.prod_univ_two, integral_exp_neg_mul_sq_gaussianReal_half ht,
    Real.mul_self_sqrt (by positivity)]

/-!
## 2. Diagonal forms and the spectral reduction
-/

/-- `E exp(-Σ_a λ_a |h_a|²) = ∏_a (1 + λ_a)⁻¹` for `λ ≥ 0`. -/
theorem integral_exp_neg_sum_normSq_circular {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    (hlam : ∀ a, 0 ≤ lam a) :
    ∫ h, Real.exp (-∑ a, lam a * Complex.normSq (h a)) ∂circularVectorLaw ι =
      ∏ a, (1 + lam a)⁻¹ := by
  rw [circularVectorLaw_eq_pi]
  have hfun : (fun h : ι → ℂ => Real.exp (-∑ a, lam a * Complex.normSq (h a))) =
      fun h => ∏ a, Real.exp (-(lam a * Complex.normSq (h a))) := by
    funext h
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
  rw [hfun, integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (fun a (z : ℂ) => Real.exp (-(lam a * Complex.normSq z)))]
  exact Finset.prod_congr rfl fun a _ => integral_exp_neg_mul_normSq_circularLawOne (hlam a)

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Spectral form `A = U diag(λ) Uᴴ` with the Mathlib eigenvector unitary. -/
theorem CommonPortRatios.spectral_eq_conj {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

/-- `Re h*Ah = Σ_a λ_a |(Uᴴh)_a|²` for Hermitian `A = U diag(λ) Uᴴ`. -/
theorem CommonPortRatios.quadForm_eq_sum_eigenvalues {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (h : ι → ℂ) :
    quadForm A h = ∑ a, hA.eigenvalues a *
      Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ h) a) := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set w := Uᴴ *ᵥ h
  have hq : star h ⬝ᵥ (A *ᵥ h) = star w ⬝ᵥ (diagonal (fun i => (hA.eigenvalues i : ℂ)) *ᵥ w) := by
    conv_lhs => rw [CommonPortRatios.spectral_eq_conj hA]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    congr 1
    rw [Matrix.star_mulVec, conjTranspose_conjTranspose]
  unfold quadForm
  rw [hq]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, mul_left_comm, mul_comm (starRingEnd ℂ (w a)), Complex.mul_conj,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `det(I + A) = ∏_a (1 + λ_a)` for Hermitian `A`. -/
theorem CommonPortRatios.det_one_add_eq_prod_eigenvalues {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (1 + A).det = ((∏ a, (1 + hA.eigenvalues a) : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  have hU1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hU2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have h1 : 1 + A = U * diagonal (fun i => ((1 + hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have hd : diagonal (fun i => ((1 + hA.eigenvalues i : ℝ) : ℂ)) =
        1 + diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU2, ← CommonPortRatios.spectral_eq_conj hA]
  rw [h1, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, hU1, det_one, one_mul,
    det_diagonal, Complex.ofReal_prod]

/-- `Re det(I + A) = ∏ (1 + λ_a) ≥ 1` for `A ⪰ 0`. -/
theorem CommonPortRatios.one_le_re_det_one_add {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : 1 ≤ (1 + A).det.re := by
  rw [CommonPortRatios.det_one_add_eq_prod_eigenvalues hA.isHermitian, Complex.ofReal_re]
  exact Finset.one_le_prod₀ fun a _ => by linarith [hA.eigenvalues_nonneg a]

/-- **Gaussian Laplace identity.** For every positive semidefinite `A` on a finite index type,
`E_h exp(-Re h*Ah) = (Re det(I + A))⁻¹`, `h ~ CN(0, I)`. -/
theorem integral_exp_neg_quadForm_circular {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    ∫ h, Real.exp (-quadForm A h) ∂circularVectorLaw ι = ((1 + A).det.re)⁻¹ := by
  have hH := hA.isHermitian
  set U : Matrix ι ι ℂ := ↑hH.eigenvectorUnitary
  have hUmem : Uᴴ ∈ unitaryGroup ι ℂ := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hH.eigenvectorUnitary.2
  have hmap := circularVectorLaw_map_unitary hUmem
  have hf : Continuous (fun w : ι → ℂ =>
      Real.exp (-∑ a, hH.eigenvalues a * Complex.normSq (w a))) := by fun_prop
  have hlin : Measurable (fun g : ι → ℂ => Uᴴ *ᵥ g) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  calc ∫ h, Real.exp (-quadForm A h) ∂circularVectorLaw ι
      = ∫ h, (fun w : ι → ℂ => Real.exp (-∑ a, hH.eigenvalues a * Complex.normSq (w a)))
          (Uᴴ *ᵥ h) ∂circularVectorLaw ι := by
        simp_rw [CommonPortRatios.quadForm_eq_sum_eigenvalues hH]; rfl
    _ = ∫ w, Real.exp (-∑ a, hH.eigenvalues a * Complex.normSq (w a))
          ∂((circularVectorLaw ι).map (fun g => Uᴴ *ᵥ g)) :=
        (integral_map hlin.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∏ a, (1 + hH.eigenvalues a)⁻¹ := by
        rw [hmap]; exact integral_exp_neg_sum_normSq_circular _ hA.eigenvalues_nonneg
    _ = ((1 + A).det.re)⁻¹ := by
        rw [CommonPortRatios.det_one_add_eq_prod_eigenvalues hH, Complex.ofReal_re, Finset.prod_inv_distrib]

end Spectral

/-!
## 3. Quadratic-form algebra, duality, small denominators
-/

section Algebra

open scoped Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `Re (Mv)* Q (Mv) = Re v*(MᴴQM)v`. -/
theorem CommonPortRatios.quadForm_conj (Q : Matrix ι ι ℂ) (M : Matrix ι κ ℂ) (v : κ → ℂ) :
    quadForm (Mᴴ * Q * M) v = quadForm Q (M *ᵥ v) := by
  unfold quadForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

/-- The quadratic form is additive in the matrix. -/
theorem CommonPortRatios.quadForm_add (P Q : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm (P + Q) v = quadForm P v + quadForm Q v := by
  unfold quadForm; rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]

/-- The quadratic form is real-homogeneous in the matrix. -/
theorem CommonPortRatios.quadForm_smul_real (c : ℝ) (Q : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm ((c : ℂ) • Q) v = c * quadForm Q v := by
  unfold quadForm; rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- Finite sums of real multiples. -/
theorem CommonPortRatios.quadForm_sum_smul {n : Type*} [Fintype n] (c : n → ℝ) (Q : n → Matrix ι ι ℂ)
    (v : ι → ℂ) : quadForm (∑ i, (c i : ℂ) • Q i) v = ∑ i, c i * quadForm (Q i) v := by
  classical
  unfold quadForm
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- `Re v*Qv ≥ 0` for `Q ⪰ 0`. -/
theorem CommonPortRatios.quadForm_nonneg_of_posSemidef {Q : Matrix ι ι ℂ} (hQ : Q.PosSemidef) (v : ι → ℂ) :
    0 ≤ quadForm Q v :=
  (Complex.nonneg_iff.mp (hQ.dotProduct_mulVec_nonneg v)).1

/-- `Re v*v = ‖v‖²` (contract `l2Norm`). -/
theorem CommonPortRatios.quadForm_one [DecidableEq ι] (v : ι → ℂ) : quadForm (1 : Matrix ι ι ℂ) v = l2Norm v ^ 2 := by
  unfold quadForm
  rw [Matrix.one_mulVec, l2Norm_sq_eq_sum_normSq]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]

/-- `|Re v*Mv| ≤ ‖M‖ ‖v‖²` (Euclidean operator norm). -/
theorem CommonPortRatios.abs_quadForm_le [DecidableEq ι] (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    |quadForm M v| ≤ ‖M‖ * l2Norm v ^ 2 := by
  have hnorm : ∀ x : ι → ℂ, ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = l2Norm x := by
    intro x
    rw [EuclideanSpace.norm_eq, l2Norm]
  have hdot : star v ⬝ᵥ (M *ᵥ v) =
      inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ ι) (WithLp.toLp 2 (M *ᵥ v)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  have hop := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 v)
  unfold quadForm
  calc |(star v ⬝ᵥ (M *ᵥ v)).re| ≤ ‖star v ⬝ᵥ (M *ᵥ v)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ *
          ‖(WithLp.toLp 2 (M *ᵥ v) : EuclideanSpace ℂ ι)‖ := by
        rw [hdot]; exact norm_inner_le_norm _ _
    _ ≤ l2Norm v * (‖M‖ * l2Norm v) := by
        rw [hnorm, hnorm]
        refine mul_le_mul_of_nonneg_left ?_ (l2Norm_nonneg v)
        rw [← hnorm, ← hnorm]
        exact hop
    _ = ‖M‖ * l2Norm v ^ 2 := by ring

end Algebra

section Duality

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **Gaussian duality** (Laplace identity and Sylvester's determinant identity): for every
rectangular `B : ι × κ`, `E_g exp(-‖Bg‖²) = E_h exp(-‖Bᴴh‖²)`, in the form
`E_g exp(-Re g*BᴴBg) = E_h exp(-Re h*BBᴴh)`, `g ~ CN(0,I_κ)`, `h ~ CN(0,I_ι)`. -/
theorem integral_exp_neg_quadForm_conjTranspose_mul_self_eq (B : Matrix ι κ ℂ) :
    ∫ g, Real.exp (-quadForm (Bᴴ * B) g) ∂circularVectorLaw κ =
      ∫ h, Real.exp (-quadForm (B * Bᴴ) h) ∂circularVectorLaw ι := by
  have h1 := integral_exp_neg_quadForm_circular (posSemidef_conjTranspose_mul_self B)
  have h2 := integral_exp_neg_quadForm_circular (posSemidef_conjTranspose_mul_self Bᴴ)
  rw [conjTranspose_conjTranspose] at h2
  rw [h1, h2, Matrix.det_one_add_mul_comm]

/-- **Transfer of a probe** through a factorization `F = BᴴB`: for every `L : ι × κ`,
`E_g exp(-Re (Lg)*F(Lg)) = E_h exp(-Re (Bᴴh)*(LLᴴ)(Bᴴh))`. -/
theorem integral_exp_neg_quadForm_mulVec_eq (B : Matrix ι ι ℂ) (L : Matrix ι κ ℂ) :
    ∫ g, Real.exp (-quadForm (Bᴴ * B) (L *ᵥ g)) ∂circularVectorLaw κ =
      ∫ h, Real.exp (-quadForm (L * Lᴴ) (Bᴴ *ᵥ h)) ∂circularVectorLaw ι := by
  have h := integral_exp_neg_quadForm_conjTranspose_mul_self_eq (B * L)
  have e1 : ∀ g, quadForm (Bᴴ * B) (L *ᵥ g) = quadForm ((B * L)ᴴ * (B * L)) g := by
    intro g
    rw [← CommonPortRatios.quadForm_conj, conjTranspose_mul]
    congr 1
    simp only [Matrix.mul_assoc]
  have e2 : ∀ h, quadForm (L * Lᴴ) (Bᴴ *ᵥ h) = quadForm ((B * L) * (B * L)ᴴ) h := by
    intro h
    rw [← CommonPortRatios.quadForm_conj, conjTranspose_mul, conjTranspose_conjTranspose]
    congr 1
    simp only [Matrix.mul_assoc]
  simp_rw [e1, e2]
  exact h

/-- `Π (1 + x_a) ≥ 1 + Σ x_a` for `x ≥ 0`. -/
theorem CommonPortRatios.one_add_sum_le_prod_one_add {α : Type*} (s : Finset α) (x : α → ℝ)
    (hx : ∀ a, 0 ≤ x a) : 1 + ∑ a ∈ s, x a ≤ ∏ a ∈ s, (1 + x a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hs : 0 ≤ ∑ a ∈ s, x a := Finset.sum_nonneg fun a _ => hx a
    nlinarith [hx a]

/-- `E_h exp(-Re h*Ah) ≤ (1 + Re Tr A)⁻¹` for `A ⪰ 0` (from
`det(I + sA) ≥ 1 + s Tr A`). -/
theorem integral_exp_neg_quadForm_le_inv_one_add_trace {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    ∫ h, Real.exp (-quadForm A h) ∂circularVectorLaw ι ≤ (1 + A.trace.re)⁻¹ := by
  rw [integral_exp_neg_quadForm_circular hA, CommonPortRatios.det_one_add_eq_prod_eigenvalues hA.isHermitian,
    Complex.ofReal_re, hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_sum, Complex.ofReal_re]
  have h0 : 0 ≤ ∑ a, hA.isHermitian.eigenvalues a :=
    Finset.sum_nonneg fun a _ => hA.eigenvalues_nonneg a
  exact inv_anti₀ (by linarith)
    (CommonPortRatios.one_add_sum_le_prod_one_add _ _ fun a => hA.eigenvalues_nonneg a)

end Duality

end BlockBand.Endpoints.Clock
