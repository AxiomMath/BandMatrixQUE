module

public import BlockBand.Critical.GlobalSource.Tightness

/-!
# Global Gaussian source, source replacement: circular Gaussian identities

* phase invariance `circularVectorLaw_map_I_smul`; mean zero `integral_dotc_circular` and zero
  pseudo-covariance `integral_dotc_sq`;
* `E|v^*h|² = ‖v‖²`, `E|v^*h|⁴ = 2‖v‖⁴` (`integral_norm_sq_dotc`, `integral_norm_pow_four_dotc`),
  and for independent vectors `E|Σ_s v_s^*H_s|⁴ = 2(Σ_s‖v_s‖²)²`
  (`integral_norm_pow_four_sum_dotc_pi`): partial sums are conditionally Gaussian;
* `E h^*Ah = Tr A`, `E|h^*Ah|² = |Tr A|² + ‖A‖²_HS`, `E Σ_x|(Bh)_x|² = ‖B‖²_HS`,
  `E(Σ_x|(Bh)_x|²)² ≤ 2‖B‖⁴_HS`, with lower-integral forms (`lintegral_*`);
* block marginal `circularVectorLaw_map_row` and Gaussian stability
  `pi_circularVectorLaw_map_scaledSum` (`M^{-1/2}Σ_i H_i` is again circular), via characteristic
  functions of real Gaussians.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open BlockBand.Counting (complexQuadraticForm circularVector)
open scoped ComplexConjugate NNReal Matrix RealInnerProductSpace
open Complex (exp I)

section Transfer
variable {ι : Type*} [Fintype ι]

/-- Integrals under `circularVectorLaw` are integrals under the product law
`Counting.circularVectorLaw`, through `circularVector`. -/
theorem integral_circularVectorLaw_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (ι → ℂ) → F) (hf : AEStronglyMeasurable f (circularVectorLaw ι)) :
    ∫ h, f h ∂circularVectorLaw ι =
      ∫ z, f (circularVector z) ∂BlockBand.Counting.circularVectorLaw ι := by
  rw [circularVectorLaw_eq_map_circularVector] at hf ⊢
  exact integral_map (measurable_circularVector ι).aemeasurable hf

/-- Lower integrals under `circularVectorLaw` are lower integrals under the product law
`Counting.circularVectorLaw`. -/
theorem lintegral_circularVectorLaw_eq (f : (ι → ℂ) → ENNReal) (hf : Measurable f) :
    ∫⁻ h, f h ∂circularVectorLaw ι =
      ∫⁻ z, f (circularVector z) ∂BlockBand.Counting.circularVectorLaw ι := by
  rw [circularVectorLaw_eq_map_circularVector]
  exact lintegral_map hf (measurable_circularVector ι)

/-- Integrability transfers from the product law `Counting.circularVectorLaw` to
`circularVectorLaw`. -/
theorem integrable_circularVectorLaw_of {F : Type*} [NormedAddCommGroup F]
    (f : (ι → ℂ) → F) (hf : AEStronglyMeasurable f (circularVectorLaw ι))
    (h : Integrable (fun z => f (circularVector z)) (BlockBand.Counting.circularVectorLaw ι)) :
    Integrable f (circularVectorLaw ι) := by
  rw [circularVectorLaw_eq_map_circularVector] at hf ⊢
  exact (integrable_map_measure hf (measurable_circularVector ι).aemeasurable).2 h

/-- **Phase invariance** of the circular law: `h ↦ i h` preserves it. -/
theorem circularVectorLaw_map_I_smul :
    (circularVectorLaw ι).map (fun h => Complex.I • h) = circularVectorLaw ι := by
  rw [circularVectorLaw_eq_map_circularVector, Measure.map_map (by fun_prop)
    (measurable_circularVector ι)]
  have hrot : (fun h : ι → ℂ => Complex.I • h) ∘ circularVector =
      circularVector ∘ fun (z : ι → ℝ × ℝ) i => BlockBand.Counting.circularQuarterTurn (z i) := by
    funext z i
    simp [circularVector, BlockBand.Counting.circularGaussianCoordinate_quarterTurn]
  have hmeas : Measurable fun (z : ι → ℝ × ℝ) i => BlockBand.Counting.circularQuarterTurn (z i) := by
    unfold BlockBand.Counting.circularQuarterTurn; fun_prop
  rw [hrot, ← Measure.map_map (measurable_circularVector ι) hmeas]
  congr 1
  unfold BlockBand.Counting.circularVectorLaw
  have hq : Measurable BlockBand.Counting.circularQuarterTurn := by
    unfold BlockBand.Counting.circularQuarterTurn; fun_prop
  rw [Measure.pi_map_pi (fun _ => hq.aemeasurable)]
  simp_rw [BlockBand.Counting.circularQuarterTurn_law]

end Transfer

section Moments
variable {ι : Type*} [Fintype ι]

/-- Coordinates of the circular vector are integrable. -/
theorem integrable_circularVector_apply (i : ι) :
    Integrable (fun z => circularVector z i) (BlockBand.Counting.circularVectorLaw ι) := by
  have h := BlockBand.Counting.integrable_circular_monomial 0 1 (by norm_num) (by norm_num)
  simp only [pow_zero, pow_one, one_mul] at h
  exact integrable_comp_eval (μ := fun _ : ι => BlockBand.Counting.standardCircularGaussian) h

/-- `v^* h` is integrable under the circular law. -/
theorem integrable_dotc_circular (v : ι → ℂ) :
    Integrable (fun h => star v ⬝ᵥ h) (circularVectorLaw ι) := by
  refine integrable_circularVectorLaw_of _
    ((by unfold dotProduct; fun_prop : Continuous fun h : ι → ℂ => star v ⬝ᵥ h).aestronglyMeasurable) ?_
  unfold dotProduct
  exact integrable_finsetSum _ fun i _ => (integrable_circularVector_apply i).const_mul _

/-- `E v^* h = 0` (phase invariance). -/
theorem integral_dotc_circular (v : ι → ℂ) :
    ∫ h, star v ⬝ᵥ h ∂circularVectorLaw ι = 0 := by
  set m := ∫ h, star v ⬝ᵥ h ∂circularVectorLaw ι
  have hm : m = Complex.I * m := by
    have hf : AEStronglyMeasurable (fun h : ι → ℂ => star v ⬝ᵥ h)
        ((circularVectorLaw ι).map (fun h => Complex.I • h)) := by
      rw [circularVectorLaw_map_I_smul]; exact (integrable_dotc_circular v).aestronglyMeasurable
    have := integral_map (μ := circularVectorLaw ι) (by fun_prop) hf
    rw [circularVectorLaw_map_I_smul] at this
    calc m = _ := this
      _ = Complex.I * m := by simp_rw [dotProduct_smul, smul_eq_mul]; rw [integral_const_mul]
  have h1 : (1 - Complex.I) * m = 0 := by rw [sub_mul, one_mul, ← hm, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exfalso
    have := congrArg Complex.re h
    simp at this
  · exact h

/-- The rank-one matrix `v v^*`. -/
def rankOne (v : ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun i j => v i * conj (v j)

/-- `gᴴ (v v^*) g = |v^* g|²`. -/
theorem complexQuadraticForm_rankOne (v g : ι → ℂ) :
    complexQuadraticForm (rankOne v) g = ((‖star v ⬝ᵥ g‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  unfold complexQuadraticForm rankOne dotProduct
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply, map_mul, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  ring

theorem trace_rankOne (v : ι → ℂ) :
    Matrix.trace (rankOne v) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  unfold Matrix.trace rankOne
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_conj']

theorem hs_rankOne (v : ι → ℂ) :
    ∑ i, ∑ j, ‖rankOne v i j‖ ^ 2 = (∑ i, ‖v i‖ ^ 2) ^ 2 := by
  unfold rankOne
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [mul_pow]

/-- `|v^* g|²` is integrable under the law. -/
theorem integrable_norm_sq_dotc_native [DecidableEq ι] (v : ι → ℂ) :
    Integrable (fun z => ‖star v ⬝ᵥ circularVector z‖ ^ 2)
      (BlockBand.Counting.circularVectorLaw ι) := by
  refine (BlockBand.Counting.integrable_actualComplexQuadratic (rankOne v)).re.congr ?_
  filter_upwards with z
  simp only [complexQuadraticForm_rankOne]
  exact_mod_cast Complex.ofReal_re _

/-- **Second moment**: `E|v^* h|² = ‖v‖²` (law). -/
theorem integral_norm_sq_dotc_native [DecidableEq ι] (v : ι → ℂ) :
    ∫ z, ‖star v ⬝ᵥ circularVector z‖ ^ 2 ∂BlockBand.Counting.circularVectorLaw ι =
      ∑ i, ‖v i‖ ^ 2 := by
  have h := BlockBand.Counting.integral_actualComplexQuadratic_eq_trace (rankOne v)
  simp only [complexQuadraticForm_rankOne, trace_rankOne] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- **Fourth moment**: `E|v^* h|⁴ = 2‖v‖⁴` (law). -/
theorem integral_norm_pow_four_dotc_native [DecidableEq ι] (v : ι → ℂ) :
    ∫ z, ‖star v ⬝ᵥ circularVector z‖ ^ 4 ∂BlockBand.Counting.circularVectorLaw ι =
      2 * (∑ i, ‖v i‖ ^ 2) ^ 2 := by
  have h := integral_norm_sq_complexQuadraticForm (rankOne v)
  simp only [complexQuadraticForm_rankOne, trace_rankOne, hs_rankOne, Complex.norm_real,
    Real.norm_eq_abs, abs_pow, sq_abs, abs_norm] at h
  have h4 : ∀ z, ‖star v ⬝ᵥ circularVector z‖ ^ 4 = (‖star v ⬝ᵥ circularVector z‖ ^ 2) ^ 2 :=
    fun z => by ring
  simp_rw [h4]
  rw [h]; ring

end Moments

section CircularMoments
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem continuous_dotc (v : ι → ℂ) : Continuous fun h : ι → ℂ => star v ⬝ᵥ h := by
  unfold dotProduct; fun_prop

theorem integrable_norm_sq_dotc (v : ι → ℂ) :
    Integrable (fun h => ‖star v ⬝ᵥ h‖ ^ 2) (circularVectorLaw ι) :=
  integrable_circularVectorLaw_of _ (((continuous_dotc v).norm.pow 2).aestronglyMeasurable)
    (integrable_norm_sq_dotc_native v)

/-- **Second moment** under the circular law: `E|v^* h|² = ‖v‖²`. -/
theorem integral_norm_sq_dotc (v : ι → ℂ) :
    ∫ h, ‖star v ⬝ᵥ h‖ ^ 2 ∂circularVectorLaw ι = ∑ i, ‖v i‖ ^ 2 := by
  rw [integral_circularVectorLaw_eq (fun h => ‖star v ⬝ᵥ h‖ ^ 2)
    ((continuous_dotc v).norm.pow 2).aestronglyMeasurable]
  exact integral_norm_sq_dotc_native v

/-- **Fourth moment** under the circular law: `E|v^* h|⁴ = 2‖v‖⁴`. -/
theorem integral_norm_pow_four_dotc (v : ι → ℂ) :
    ∫ h, ‖star v ⬝ᵥ h‖ ^ 4 ∂circularVectorLaw ι = 2 * (∑ i, ‖v i‖ ^ 2) ^ 2 := by
  rw [integral_circularVectorLaw_eq (fun h => ‖star v ⬝ᵥ h‖ ^ 4)
    ((continuous_dotc v).norm.pow 4).aestronglyMeasurable]
  exact integral_norm_pow_four_dotc_native v

theorem integrable_dotc_sq (v : ι → ℂ) :
    Integrable (fun h => (star v ⬝ᵥ h) ^ 2) (circularVectorLaw ι) := by
  refine (integrable_norm_sq_dotc v).mono' ((continuous_dotc v).pow 2).aestronglyMeasurable ?_
  filter_upwards with h
  rw [norm_pow]

/-- **Zero pseudo-covariance**: `E (v^* h)² = 0` (phase invariance). -/
theorem integral_dotc_sq (v : ι → ℂ) :
    ∫ h, (star v ⬝ᵥ h) ^ 2 ∂circularVectorLaw ι = 0 := by
  set m := ∫ h, (star v ⬝ᵥ h) ^ 2 ∂circularVectorLaw ι
  have hm : m = -m := by
    have hf : AEStronglyMeasurable (fun h : ι → ℂ => (star v ⬝ᵥ h) ^ 2)
        ((circularVectorLaw ι).map (fun h => Complex.I • h)) := by
      rw [circularVectorLaw_map_I_smul]; exact (integrable_dotc_sq v).aestronglyMeasurable
    have := integral_map (μ := circularVectorLaw ι) (by fun_prop) hf
    rw [circularVectorLaw_map_I_smul] at this
    calc m = _ := this
      _ = -m := by
        simp_rw [dotProduct_smul, smul_eq_mul, mul_pow, Complex.I_sq, neg_one_mul]
        rw [integral_neg]
  have h2 : (2 : ℂ) * m = 0 := by
    calc (2 : ℂ) * m = m + m := by ring
      _ = 0 := by nth_rewrite 2 [hm]; ring
  rcases mul_eq_zero.1 h2 with h | h
  · norm_num at h
  · exact h

/-- **Fourth moment of a sum over independent vectors**: for i.i.d. circular `H_s`,
`E|Σ_s v_s^* H_s|⁴ = 2 (Σ_s ‖v_s‖²)²`. -/
theorem integral_norm_pow_four_sum_dotc_pi {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : κ → ι → ℂ) :
    ∫ H, ‖∑ s, star (v s) ⬝ᵥ H s‖ ^ 4 ∂Measure.pi (fun _ : κ => circularVectorLaw ι) =
      2 * (∑ s, ∑ i, ‖v s i‖ ^ 2) ^ 2 := by
  have hcont : Continuous fun H : κ → ι → ℂ => ‖∑ s, star (v s) ⬝ᵥ H s‖ ^ 4 := by
    unfold dotProduct; fun_prop
  rw [pi_circularVectorLaw_eq_map, integral_map (by
    exact (Measurable.of_eval fun a => Measurable.of_eval fun i =>
      (measurable_pi_apply (a, i)).comp (measurable_circularVector _)).aemeasurable)
    hcont.aestronglyMeasurable]
  have hpt : ∀ z : κ × ι → ℝ × ℝ,
      ∑ s, star (v s) ⬝ᵥ (fun i => circularVector z (s, i)) =
        star (fun p : κ × ι => v p.1 p.2) ⬝ᵥ circularVector z := by
    intro z
    unfold dotProduct
    rw [Fintype.sum_prod_type]
    rfl
  simp_rw [hpt]
  rw [integral_norm_pow_four_dotc_native, Fintype.sum_prod_type]

omit [DecidableEq ι] in
/-- `h^* A h` is the quadratic form. -/
theorem dotc_mulVec_eq_complexQuadraticForm (A : Matrix ι ι ℂ) (h : ι → ℂ) :
    star h ⬝ᵥ (A *ᵥ h) = complexQuadraticForm A h := by
  unfold dotProduct Matrix.mulVec complexQuadraticForm dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, RCLike.star_def]
  ring

omit [DecidableEq ι] in
theorem continuous_quadratic (A : Matrix ι ι ℂ) :
    Continuous fun h : ι → ℂ => star h ⬝ᵥ (A *ᵥ h) := by
  unfold dotProduct Matrix.mulVec dotProduct; fun_prop

theorem integrable_quadratic (A : Matrix ι ι ℂ) :
    Integrable (fun h => star h ⬝ᵥ (A *ᵥ h)) (circularVectorLaw ι) := by
  refine integrable_circularVectorLaw_of _ (continuous_quadratic A).aestronglyMeasurable ?_
  simp_rw [dotc_mulVec_eq_complexQuadraticForm]
  exact BlockBand.Counting.integrable_actualComplexQuadratic A

/-- `E h^* A h = Tr A`. -/
theorem integral_quadratic (A : Matrix ι ι ℂ) :
    ∫ h, star h ⬝ᵥ (A *ᵥ h) ∂circularVectorLaw ι = Matrix.trace A := by
  rw [integral_circularVectorLaw_eq (fun h => star h ⬝ᵥ (A *ᵥ h))
    (continuous_quadratic A).aestronglyMeasurable]
  simp_rw [dotc_mulVec_eq_complexQuadraticForm]
  exact BlockBand.Counting.integral_actualComplexQuadratic_eq_trace A

/-- `E|h^* A h|² = |Tr A|² + ‖A‖²_HS`. -/
theorem integral_norm_sq_quadratic (A : Matrix ι ι ℂ) :
    ∫ h, ‖star h ⬝ᵥ (A *ᵥ h)‖ ^ 2 ∂circularVectorLaw ι =
      ‖Matrix.trace A‖ ^ 2 + ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [integral_circularVectorLaw_eq (fun h => ‖star h ⬝ᵥ (A *ᵥ h)‖ ^ 2)
    ((continuous_quadratic A).norm.pow 2).aestronglyMeasurable]
  simp_rw [dotc_mulVec_eq_complexQuadraticForm]
  exact integral_norm_sq_complexQuadraticForm A

theorem integrable_norm_sq_quadratic (A : Matrix ι ι ℂ) :
    Integrable (fun h => ‖star h ⬝ᵥ (A *ᵥ h)‖ ^ 2) (circularVectorLaw ι) := by
  refine integrable_circularVectorLaw_of _
    ((continuous_quadratic A).norm.pow 2).aestronglyMeasurable ?_
  simp_rw [dotc_mulVec_eq_complexQuadraticForm]
  exact integrable_norm_sq_complexQuadraticForm A

end CircularMoments

section Matrices
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `h^* (B^*B) h = Σ_x |(Bh)_x|²`. -/
theorem dotc_conjTranspose_mul_mulVec (B : Matrix κ ι ℂ) (h : ι → ℂ) :
    star h ⬝ᵥ ((Bᴴ * B) *ᵥ h) = ((∑ x, ‖(B *ᵥ h) x‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  unfold dotProduct
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.star_apply, RCLike.star_def, Complex.conj_mul']

omit [DecidableEq ι] in
theorem trace_conjTranspose_mul_self (B : Matrix κ ι ℂ) :
    Matrix.trace (Bᴴ * B) = ((∑ x, ∑ y, ‖B x y‖ ^ 2 : ℝ) : ℂ) := by
  unfold Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

omit [DecidableEq ι] in
/-- `‖B^*B‖²_HS ≤ ‖B‖⁴_HS`. -/
theorem hs_conjTranspose_mul_self_le (B : Matrix κ ι ℂ) :
    ∑ i, ∑ j, ‖(Bᴴ * B) i j‖ ^ 2 ≤ (∑ x, ∑ y, ‖B x y‖ ^ 2) ^ 2 := by
  have hentry : ∀ i j, ‖(Bᴴ * B) i j‖ ^ 2 ≤ (∑ x, ‖B x i‖ ^ 2) * (∑ x, ‖B x j‖ ^ 2) := by
    intro i j
    have h1 : ‖(Bᴴ * B) i j‖ ≤ ∑ x, ‖B x i‖ * ‖B x j‖ := by
      rw [Matrix.mul_apply]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [norm_mul, Matrix.conjTranspose_apply, norm_star]
    calc ‖(Bᴴ * B) i j‖ ^ 2 ≤ (∑ x, ‖B x i‖ * ‖B x j‖) ^ 2 := by gcongr
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, ∑ j, ‖(Bᴴ * B) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ x, ‖B x i‖ ^ 2) * (∑ x, ‖B x j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = (∑ i, ∑ x, ‖B x i‖ ^ 2) ^ 2 := by rw [sq, Finset.sum_mul_sum]
    _ = _ := by rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem continuous_sum_norm_sq_mulVec (B : Matrix κ ι ℂ) :
    Continuous fun h : ι → ℂ => ∑ x, ‖(B *ᵥ h) x‖ ^ 2 := by
  unfold Matrix.mulVec dotProduct; fun_prop

/-- `E Σ_x |(Bh)_x|² = ‖B‖²_HS`. -/
theorem integral_sum_norm_sq_mulVec (B : Matrix κ ι ℂ) :
    ∫ h, ∑ x, ‖(B *ᵥ h) x‖ ^ 2 ∂circularVectorLaw ι = ∑ x, ∑ y, ‖B x y‖ ^ 2 := by
  have h := integral_quadratic (Bᴴ * B)
  simp_rw [dotc_conjTranspose_mul_mulVec, trace_conjTranspose_mul_self] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

theorem integrable_sum_norm_sq_mulVec (B : Matrix κ ι ℂ) :
    Integrable (fun h => ∑ x, ‖(B *ᵥ h) x‖ ^ 2) (circularVectorLaw ι) := by
  refine (integrable_quadratic (Bᴴ * B)).re.congr ?_
  filter_upwards with h
  simp only [dotc_conjTranspose_mul_mulVec]
  exact_mod_cast Complex.ofReal_re _

/-- `E (Σ_x |(Bh)_x|²)² ≤ 2 ‖B‖⁴_HS`. -/
theorem integral_sq_sum_norm_sq_mulVec_le (B : Matrix κ ι ℂ) :
    ∫ h, (∑ x, ‖(B *ᵥ h) x‖ ^ 2) ^ 2 ∂circularVectorLaw ι ≤
      2 * (∑ x, ∑ y, ‖B x y‖ ^ 2) ^ 2 := by
  have h := integral_norm_sq_quadratic (Bᴴ * B)
  simp only [dotc_conjTranspose_mul_mulVec, trace_conjTranspose_mul_self, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at h
  rw [h]
  have := hs_conjTranspose_mul_self_le B
  linarith

theorem integrable_sq_sum_norm_sq_mulVec (B : Matrix κ ι ℂ) :
    Integrable (fun h => (∑ x, ‖(B *ᵥ h) x‖ ^ 2) ^ 2) (circularVectorLaw ι) := by
  refine (integrable_norm_sq_quadratic (Bᴴ * B)).congr ?_
  filter_upwards with h
  simp only [dotc_conjTranspose_mul_mulVec, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Matrices

section Laws
variable {ι : Type*} [Fintype ι]

/-- **Block marginal**: the restriction of a circular vector on `α × β` to the row `a` is a circular
vector on `β`. -/
theorem circularVectorLaw_map_row {α β : Type*} [Fintype α] [Fintype β] (a : α) :
    (circularVectorLaw (α × β)).map (fun h y => h (a, y)) = circularVectorLaw β := by
  classical
  have hc : Measurable fun (h : α × β → ℂ) (a : α) (y : β) => h (a, y) :=
    Measurable.of_eval fun a => Measurable.of_eval fun y => measurable_pi_apply (a, y)
  have h1 : (circularVectorLaw (α × β)).map (fun h a y => h (a, y)) =
      Measure.pi (fun _ : α => circularVectorLaw β) := by
    rw [pi_circularVectorLaw_eq_map, circularVectorLaw_eq_map_circularVector,
      Measure.map_map hc (measurable_circularVector _)]
    rfl
  have h2 : (fun (h : α × β → ℂ) (y : β) => h (a, y)) =
      (Function.eval a) ∘ (fun (h : α × β → ℂ) (a : α) (y : β) => h (a, y)) := rfl
  rw [h2, ← Measure.map_map (measurable_pi_apply a) hc, h1, Measure.pi_map_eval]
  simp

/-- Scaled sums of i.i.d. real Gaussian vectors: `M^{-1/2} Σ_i R_i` has the law of `R_1`. -/
theorem pi_gaussianReal_map_scaledSum {P : Type*} [Fintype P] (v : ℝ≥0) {M : ℕ} (hM : 0 < M) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : P => gaussianReal 0 v).map
      (fun R p => (Real.sqrt M)⁻¹ * ∑ i, R i p) = Measure.pi fun _ : P => gaussianReal 0 v := by
  set t₀ : ℝ := (Real.sqrt M)⁻¹
  have hmeas : Measurable fun (R : Fin M → P → ℝ) p => t₀ * ∑ i, R i p := by fun_prop
  have hL : Measurable (WithLp.toLp 2 : (P → ℝ) → PiLp 2 (fun _ : P => ℝ)) :=
    (MeasurableEquiv.toLp 2 (P → ℝ)).measurable
  rw [← charFun_eq_pi_iff]
  intro s
  rw [Measure.map_map hL hmeas, charFun_apply, integral_map (hL.comp hmeas).aemeasurable (by fun_prop)]
  have hpt : ∀ R : Fin M → P → ℝ, exp (⟪(WithLp.toLp 2 ∘ fun (R : Fin M → P → ℝ) p => t₀ * ∑ i, R i p) R, s⟫ * I) =
      ∏ i, exp (⟪WithLp.toLp 2 (R i), t₀ • s⟫ * I) := by
    intro R
    rw [← Complex.exp_sum]
    congr 1
    simp only [Function.comp_apply, PiLp.inner_apply, PiLp.smul_apply]
    simp [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_fintype_prod_eq_prod (f := fun _ (r : P → ℝ) => exp (⟪WithLp.toLp 2 r, t₀ • s⟫ * I))]
  have hfac : ∫ (x : P → ℝ), Complex.exp (↑⟪WithLp.toLp 2 x, t₀ • s⟫ * I) ∂Measure.pi (fun _ : P => gaussianReal 0 v) =
      ∏ p, charFun (gaussianReal 0 v) (t₀ * s.ofLp p) := by
    have := charFun_pi (μ := fun _ : P => gaussianReal 0 v) (t₀ • s)
    rw [charFun_apply, integral_map hL.aemeasurable (by fun_prop)] at this
    rw [this]
    rfl
  have ht : ((t₀ : ℝ) : ℂ) ^ 2 * (M : ℂ) = 1 := by
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have : t₀ ^ 2 * M = 1 := by
      simp only [t₀, inv_pow, Real.sq_sqrt hM'.le]; field_simp
    exact_mod_cast this
  rw [hfac, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  linear_combination (-(v : ℂ) * (s.ofLp p : ℂ) ^ 2 / 2) * ht

/-- **Gaussian stability**: `M^{-1/2} Σ_i H_i` of `M` i.i.d. circular vectors is a circular vector. -/
theorem pi_circularVectorLaw_map_scaledSum {M : ℕ} (hM : 0 < M) :
    (Measure.pi fun _ : Fin M => circularVectorLaw ι).map
      (fun H x => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * ∑ i, H i x) = circularVectorLaw ι := by
  set φ : (ι × Fin 2 → ℝ) → ι → ℂ := fun r a => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I
  have hφ : Measurable φ := by fun_prop
  have hdef : circularVectorLaw ι =
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map φ := rfl
  rw [hdef, ← Measure.pi_map_pi (fun _ => hφ.aemeasurable)]
  have hT : Measurable fun (R : Fin M → ι × Fin 2 → ℝ) p => (Real.sqrt M)⁻¹ * ∑ i, R i p := by
    fun_prop
  have hS : Measurable fun (H : Fin M → ι → ℂ) x => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * ∑ i, H i x := by
    fun_prop
  rw [Measure.map_map hS (by fun_prop)]
  have hcomp : ((fun (H : Fin M → ι → ℂ) x => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * ∑ i, H i x) ∘
      fun (R : Fin M → ι × Fin 2 → ℝ) i => φ (R i)) =
      φ ∘ fun (R : Fin M → ι × Fin 2 → ℝ) p => (Real.sqrt M)⁻¹ * ∑ i, R i p := by
    funext R x
    simp only [Function.comp_apply, φ]
    push_cast
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  rw [hcomp, ← Measure.map_map hφ hT, pi_gaussianReal_map_scaledSum _ hM]

end Laws

section Lintegrals
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrable_norm_pow_four_dotc_native (v : ι → ℂ) :
    Integrable (fun z => ‖star v ⬝ᵥ circularVector z‖ ^ 4)
      (BlockBand.Counting.circularVectorLaw ι) := by
  refine (integrable_norm_sq_complexQuadraticForm (rankOne v)).congr (ae_of_all _ fun z => ?_)
  simp only [complexQuadraticForm_rankOne, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- Lower-integral form of `integral_norm_pow_four_sum_dotc_pi`. -/
theorem lintegral_norm_pow_four_sum_dotc_pi {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : κ → ι → ℂ) :
    ∫⁻ H, ENNReal.ofReal (‖∑ s, star (v s) ⬝ᵥ H s‖ ^ 4)
        ∂Measure.pi (fun _ : κ => circularVectorLaw ι) =
      ENNReal.ofReal (2 * (∑ s, ∑ i, ‖v s i‖ ^ 2) ^ 2) := by
  have hcont : Continuous fun H : κ → ι → ℂ => ‖∑ s, star (v s) ⬝ᵥ H s‖ ^ 4 := by
    unfold dotProduct; fun_prop
  have hmap : Measurable fun (z : κ × ι → ℝ × ℝ) (a : κ) (i : ι) => circularVector z (a, i) :=
    Measurable.of_eval fun a => Measurable.of_eval fun i =>
      (measurable_pi_apply (a, i)).comp (measurable_circularVector _)
  have hpt : ∀ z : κ × ι → ℝ × ℝ,
      ∑ s, star (v s) ⬝ᵥ (fun i => circularVector z (s, i)) =
        star (fun p : κ × ι => v p.1 p.2) ⬝ᵥ circularVector z := by
    intro z
    unfold dotProduct
    rw [Fintype.sum_prod_type]
    rfl
  have hint : Integrable (fun H : κ → ι → ℂ => ‖∑ s, star (v s) ⬝ᵥ H s‖ ^ 4)
      (Measure.pi (fun _ : κ => circularVectorLaw ι)) := by
    rw [pi_circularVectorLaw_eq_map]
    refine (integrable_map_measure hcont.aestronglyMeasurable hmap.aemeasurable).2 ?_
    refine (integrable_norm_pow_four_dotc_native (fun p : κ × ι => v p.1 p.2)).congr
      (ae_of_all _ fun z => ?_)
    simp only [Function.comp_apply, hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity),
    integral_norm_pow_four_sum_dotc_pi]

theorem lintegral_norm_sq_dotc (v : ι → ℂ) :
    ∫⁻ h, ENNReal.ofReal (‖star v ⬝ᵥ h‖ ^ 2) ∂circularVectorLaw ι =
      ENNReal.ofReal (∑ i, ‖v i‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_dotc v)
    (ae_of_all _ fun _ => by positivity), integral_norm_sq_dotc]

theorem lintegral_norm_sq_quadratic (A : Matrix ι ι ℂ) :
    ∫⁻ h, ENNReal.ofReal (‖star h ⬝ᵥ (A *ᵥ h)‖ ^ 2) ∂circularVectorLaw ι =
      ENNReal.ofReal (‖Matrix.trace A‖ ^ 2 + ∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_quadratic A)
    (ae_of_all _ fun _ => by positivity), integral_norm_sq_quadratic]

theorem lintegral_sum_norm_sq_mulVec {κ : Type*} [Fintype κ] (B : Matrix κ ι ℂ) :
    ∫⁻ h, ENNReal.ofReal (∑ x, ‖(B *ᵥ h) x‖ ^ 2) ∂circularVectorLaw ι =
      ENNReal.ofReal (∑ x, ∑ y, ‖B x y‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sum_norm_sq_mulVec B)
    (ae_of_all _ fun _ => by positivity), integral_sum_norm_sq_mulVec]

theorem lintegral_sq_sum_norm_sq_mulVec_le {κ : Type*} [Fintype κ] (B : Matrix κ ι ℂ) :
    ∫⁻ h, ENNReal.ofReal ((∑ x, ‖(B *ᵥ h) x‖ ^ 2) ^ 2) ∂circularVectorLaw ι ≤
      ENNReal.ofReal (2 * (∑ x, ∑ y, ‖B x y‖ ^ 2) ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sq_sum_norm_sq_mulVec B)
    (ae_of_all _ fun _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (integral_sq_sum_norm_sq_mulVec_le B)

theorem lintegral_norm_pow_four_dotc (v : ι → ℂ) :
    ∫⁻ h, ENNReal.ofReal (‖star v ⬝ᵥ h‖ ^ 4) ∂circularVectorLaw ι =
      ENNReal.ofReal (2 * (∑ i, ‖v i‖ ^ 2) ^ 2) := by
  have hint : Integrable (fun h => ‖star v ⬝ᵥ h‖ ^ 4) (circularVectorLaw ι) :=
    integrable_circularVectorLaw_of _ (((continuous_dotc v).norm.pow 4).aestronglyMeasurable)
      (integrable_norm_pow_four_dotc_native v)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity),
    integral_norm_pow_four_dotc]

/-- `(‖C‖²_HS)² ≤ E(Σ_x|(Ch)_x|²)²` (the trace term of the Wick identity). -/
theorem le_lintegral_sq_sum_norm_sq_mulVec {κ : Type*} [Fintype κ] (B : Matrix κ ι ℂ) :
    ENNReal.ofReal ((∑ x, ∑ y, ‖B x y‖ ^ 2) ^ 2) ≤
      ∫⁻ h, ENNReal.ofReal ((∑ x, ‖(B *ᵥ h) x‖ ^ 2) ^ 2) ∂circularVectorLaw ι := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sq_sum_norm_sq_mulVec B)
    (ae_of_all _ fun _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := integral_norm_sq_quadratic (Bᴴ * B)
  simp only [dotc_conjTranspose_mul_mulVec, trace_conjTranspose_mul_self, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at h
  rw [h]
  have : 0 ≤ ∑ i, ∑ j, ‖(Bᴴ * B) i j‖ ^ 2 := by positivity
  linarith

end Lintegrals

end BlockBand.Critical.GlobalSource
