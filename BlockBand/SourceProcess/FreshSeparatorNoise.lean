module

public import BlockBand.SourceProcess.GaussianGramLaw
public import BlockBand.SourceProcess.CurrentAlgebra
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Fresh Gaussian separator noise

A matrix of independent circular Gaussian entries, scaled and sandwiched between projections to
give the fresh separator; it is Gaussian, centred, in every `L^p`, Hermitian for Hermitian
projections, and has explicit second-moment, trace-sandwich and trace-product contractions.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexConjugate BigOperators

/-- The iid circular matrix is a reshaping of the explicit product vector. -/
def freshCircularMatrix {ι : Type*} (ω : (ι × ι) → ℝ × ℝ) : Matrix ι ι ℂ :=
  fun i j => circularGaussianVector ω (i, j)

/-- Finite probability law of all independently sampled entry pairs. -/
def freshCircularMatrixLaw (ι : Type*) [Fintype ι] : Measure ((ι × ι) → ℝ × ℝ) :=
  standardCircularGaussianVectorLaw (ι × ι)

instance freshCircularMatrixLaw_probability {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (freshCircularMatrixLaw ι) := by
  unfold freshCircularMatrixLaw
  infer_instance

/-- The entries are mutually independent. -/
theorem iIndepFun_freshCircularMatrix {ι : Type*} [Fintype ι] :
    iIndepFun (fun u : ι × ι => fun ω : (ι × ι) → ℝ × ℝ =>
      freshCircularMatrix ω u.1 u.2) (freshCircularMatrixLaw ι) :=
  iIndepFun_circularGaussianVector

private def freshMatrixRealLinear {ι : Type*} : ((ι × ι) → ℂ) →ₗ[ℝ] Matrix ι ι ℂ where
  toFun g := fun i j => g (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def freshSeparatorRealLinear {ι : Type*} [Fintype ι]
    (c : ℂ) (P Pprime : Matrix ι ι ℂ) : (Matrix ι ι ℂ) →ₗ[ℝ] Matrix ι ι ℂ where
  toFun G := c • (P * G * Pprime + Pprime * Gᴴ * P)
  map_add' G H := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_add, smul_add]
    abel
  map_smul' r G := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_smul, star_trivial, smul_add]
    exact congrArg₂ (· + ·) (smul_comm c r (P * G * Pprime))
      (smul_comm c r (Pprime * Gᴴ * P))

/-- Fresh separator; the scale has squared value D0 dt/2 when nonnegative. -/
def freshSeparatorNoise {ι : Type*} [Fintype ι]
    (D0 dt : ℝ) (P Pprime : Matrix ι ι ℂ) (ω : (ι × ι) → ℝ × ℝ) : Matrix ι ι ℂ :=
  (Real.sqrt (D0 * dt / 2) : ℂ) •
    (P * freshCircularMatrix ω * Pprime + Pprime * (freshCircularMatrix ω)ᴴ * P)

private def freshMatrixCoordinatesRealLinear {ι : Type*} :
    Matrix ι ι ℂ →ₗ[ℝ] ((ι × ι) → ℂ) where
  toFun G := fun u => G u.1 u.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def freshSeparatorCLM {ι : Type*} [Fintype ι]
    (D0 dt : ℝ) (P Pprime : Matrix ι ι ℂ) : ((ι × ι) → ℂ) →L[ℝ] ((ι × ι) → ℂ) :=
  (freshMatrixCoordinatesRealLinear.comp
    ((freshSeparatorRealLinear (Real.sqrt (D0 * dt / 2)) P Pprime).comp
      freshMatrixRealLinear)).toContinuousLinearMap

/-- The fresh separator has a Gaussian law. -/
theorem hasGaussianLaw_freshSeparatorNoise {ι : Type*} [Fintype ι]
    (D0 dt : ℝ) (P Pprime : Matrix ι ι ℂ) :
    HasGaussianLaw (fun ω (u : ι × ι) => freshSeparatorNoise D0 dt P Pprime ω u.1 u.2)
      (freshCircularMatrixLaw ι) := by
  unfold freshCircularMatrixLaw
  exact (hasGaussianLaw_circularGaussianVector.map_fun
    (freshSeparatorCLM D0 dt P Pprime)).congr
      (Filter.Eventually.of_forall fun _ => by rfl)

/-- Finite Lp moments of the complete separator matrix. -/
theorem memLp_freshSeparatorNoise {ι : Type*} [Fintype ι]
    (D0 dt : ℝ) (P Pprime : Matrix ι ι ℂ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω (u : ι × ι) => freshSeparatorNoise D0 dt P Pprime ω u.1 u.2) p
      (freshCircularMatrixLaw ι) :=
  (hasGaussianLaw_freshSeparatorNoise D0 dt P Pprime).memLp hp

/-- Separator mean is zero as a complete finite matrix. -/
theorem integral_freshSeparatorNoise {ι : Type*} [Fintype ι]
    (D0 dt : ℝ) (P Pprime : Matrix ι ι ℂ) :
    ∫ ω : (ι × ι) → ℝ × ℝ, (fun u : ι × ι => freshSeparatorNoise D0 dt P Pprime ω u.1 u.2)
      ∂freshCircularMatrixLaw ι = 0 := by
  change ∫ ω : (ι × ι) → ℝ × ℝ,
    freshSeparatorCLM D0 dt P Pprime (circularGaussianVector ω)
      ∂standardCircularGaussianVectorLaw (ι × ι) = 0
  have h := (freshSeparatorCLM D0 dt P Pprime).integral_comp_comm
    ((memLp_circularGaussianVector (ι := ι × ι) 1 (by norm_num)).integrable le_rfl)
  rw [integral_circularGaussianVector] at h
  exact h.trans (freshSeparatorCLM D0 dt P Pprime).map_zero

/-- Hermitian projections give a Hermitian separator for every sample. -/
theorem freshSeparatorNoise_isHermitian {ι : Type*} [Fintype ι]
    (D0 dt : ℝ) (P Pprime : Matrix ι ι ℂ) (hP : Pᴴ = P) (hPprime : Pprimeᴴ = Pprime)
    (ω : (ι × ι) → ℝ × ℝ) : (freshSeparatorNoise D0 dt P Pprime ω).IsHermitian := by
  change (freshSeparatorNoise D0 dt P Pprime ω)ᴴ = freshSeparatorNoise D0 dt P Pprime ω
  simp only [freshSeparatorNoise, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP, hPprime]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [add_comm]
  simp only [Matrix.mul_assoc]

private def freshLinearForm {u : Type*} [Fintype u] (c : u → ℂ) (ω : u → ℝ × ℝ) : ℂ :=
  ∑ a, c a * circularGaussianVector ω a

private def freshAntiLinearForm {u : Type*} [Fintype u] (c : u → ℂ) (ω : u → ℝ × ℝ) : ℂ :=
  ∑ a, c a * conj (circularGaussianVector ω a)

private theorem memLp_four_freshLinearForm {u : Type*} [Fintype u] (c : u → ℂ) :
    MemLp (freshLinearForm c) 4 (standardCircularGaussianVectorLaw u) := by
  apply memLp_finsetSum
  intro a _
  exact (memLp_four_circularGaussianVector a).const_mul (c a)

private theorem memLp_four_freshAntiLinearForm {u : Type*} [Fintype u] (c : u → ℂ) :
    MemLp (freshAntiLinearForm c) 4 (standardCircularGaussianVectorLaw u) := by
  apply memLp_finsetSum
  intro a _
  exact MemLp.ae_eq (Filter.Eventually.of_forall fun _ => by rfl)
    ((memLp_four_circularGaussianVector a).star.const_mul (c a))

private theorem freshAntiLinearForm_eq_conj {u : Type*} [Fintype u]
    (c : u → ℂ) (ω : u → ℝ × ℝ) :
    freshAntiLinearForm c ω = conj (freshLinearForm (fun a => conj (c a)) ω) := by
  simp [freshAntiLinearForm, freshLinearForm]

private theorem integral_freshLinearForm_mul_anti {u : Type*} [Fintype u] [DecidableEq u]
    (c d : u → ℂ) :
    ∫ ω : u → ℝ × ℝ, freshLinearForm c ω * freshAntiLinearForm d ω
      ∂standardCircularGaussianVectorLaw u = ∑ a, c a * d a := by
  have hexpand (ω : u → ℝ × ℝ) :
      freshLinearForm c ω * freshAntiLinearForm d ω =
        ∑ a, ∑ b, (c a * d b) *
          (circularGaussianVector ω a * conj (circularGaussianVector ω b)) := by
    simp only [freshLinearForm, freshAntiLinearForm, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _]
  · trans ∑ a, ∑ b, (c a * d b) * (if a = b then 1 else 0)
    · apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum _ (fun b _ =>
        (integrable_circularGaussianVector_covariance a b).const_mul _)]
      simp_rw [integral_const_mul, integral_circularGaussianVector_covariance]
    · simp
  · intro a _
    exact integrable_finsetSum _ (fun b _ =>
      (integrable_circularGaussianVector_covariance a b).const_mul _)

private theorem integral_freshLinearForm_mul_linear {u : Type*} [Fintype u] [DecidableEq u]
    (c d : u → ℂ) :
    ∫ ω : u → ℝ × ℝ, freshLinearForm c ω * freshLinearForm d ω
      ∂standardCircularGaussianVectorLaw u = 0 := by
  have hexpand (ω : u → ℝ × ℝ) :
      freshLinearForm c ω * freshLinearForm d ω =
        ∑ a, ∑ b, (c a * d b) *
          (circularGaussianVector ω a * circularGaussianVector ω b) := by
    simp only [freshLinearForm, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _]
  · trans ∑ a, ∑ b, (c a * d b) * 0
    · apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum _ (fun b _ =>
        (integrable_circularGaussianVector_pseudoCovariance a b).const_mul _)]
      simp_rw [integral_const_mul, integral_circularGaussianVector_pseudoCovariance]
    · simp
  · intro a _
    exact integrable_finsetSum _ (fun b _ =>
      (integrable_circularGaussianVector_pseudoCovariance a b).const_mul _)

private theorem integral_freshAntiLinearForm_mul_anti {u : Type*} [Fintype u] [DecidableEq u]
    (c d : u → ℂ) :
    ∫ ω : u → ℝ × ℝ, freshAntiLinearForm c ω * freshAntiLinearForm d ω
      ∂standardCircularGaussianVectorLaw u = 0 := by
  simp_rw [freshAntiLinearForm_eq_conj, ← map_mul]
  rw [integral_conj, integral_freshLinearForm_mul_linear]
  simp

private theorem integrable_freshForms_mul {u : Type*} [Fintype u]
    (c d : u → ℂ) (b e : Bool) :
    Integrable (fun ω : u → ℝ × ℝ =>
      (if b then freshAntiLinearForm c ω else freshLinearForm c ω) *
      (if e then freshAntiLinearForm d ω else freshLinearForm d ω))
      (standardCircularGaussianVectorLaw u) := by
  have hc : MemLp (fun ω : u → ℝ × ℝ =>
      if b then freshAntiLinearForm c ω else freshLinearForm c ω) 2
      (standardCircularGaussianVectorLaw u) := by
    cases b
    · exact (memLp_four_freshLinearForm c).mono_exponent (by norm_num)
    · exact (memLp_four_freshAntiLinearForm c).mono_exponent (by norm_num)
  have hd : MemLp (fun ω : u → ℝ × ℝ =>
      if e then freshAntiLinearForm d ω else freshLinearForm d ω) 2
      (standardCircularGaussianVectorLaw u) := by
    cases e
    · exact (memLp_four_freshLinearForm d).mono_exponent (by norm_num)
    · exact (memLp_four_freshAntiLinearForm d).mono_exponent (by norm_num)
  exact (hc.integrable_mul hd).congr (Filter.Eventually.of_forall fun _ => by rfl)

private theorem integral_freshMixedForms {u : Type*} [Fintype u] [DecidableEq u]
    (c d e f : u → ℂ) :
    ∫ ω : u → ℝ × ℝ,
      (freshLinearForm c ω + freshAntiLinearForm d ω) *
      (freshLinearForm e ω + freshAntiLinearForm f ω)
      ∂standardCircularGaussianVectorLaw u = ∑ a, (c a * f a + d a * e a) := by
  have h1 := integrable_freshForms_mul c e false false
  have h2 := integrable_freshForms_mul c f false true
  have h3 := integrable_freshForms_mul d e true false
  have h4 := integrable_freshForms_mul d f true true
  simp only [Bool.false_eq_true, ite_false, ite_true] at h1 h2 h3 h4
  simp_rw [add_mul, mul_add]
  rw [integral_add, integral_add, integral_add,
    integral_freshLinearForm_mul_linear, integral_freshLinearForm_mul_anti,
    integral_freshAntiLinearForm_mul_anti]
  have hal : (∫ ω : u → ℝ × ℝ, freshAntiLinearForm d ω * freshLinearForm e ω
      ∂standardCircularGaussianVectorLaw u) = ∑ a, d a * e a := by
    simpa only [mul_comm] using integral_freshLinearForm_mul_anti e d
  rw [hal]
  simp only [zero_add, add_zero, Finset.sum_add_distrib]
  all_goals first | exact h1 | exact h2 | exact h3 | exact h4 | exact h1.add h2 | exact h3.add h4

private theorem mul_freshCircularMatrix_entry {ι : Type*} [Fintype ι]
    (P R : Matrix ι ι ℂ) (ω : (ι × ι) → ℝ × ℝ) (i j : ι) :
    (P * freshCircularMatrix ω * R) i j =
      freshLinearForm (fun u : ι × ι => P i u.1 * R u.2 j) ω := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Finset.mul_sum, freshLinearForm, Fintype.sum_prod_type,
    freshCircularMatrix]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem mul_freshCircularMatrix_adjoint_entry {ι : Type*} [Fintype ι]
    (P R : Matrix ι ι ℂ) (ω : (ι × ι) → ℝ × ℝ) (i j : ι) :
    (P * (freshCircularMatrix ω)ᴴ * R) i j =
      freshAntiLinearForm (fun u : ι × ι => P i u.2 * R u.1 j) ω := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Finset.mul_sum, Matrix.conjTranspose_apply,
    freshAntiLinearForm, Fintype.sum_prod_type, freshCircularMatrix, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem freshSeparatorNoise_entry {ι : Type*} [Fintype ι]
    (D0 dt : ℝ) (P Pprime : Matrix ι ι ℂ) (ω : (ι × ι) → ℝ × ℝ) (i j : ι) :
    freshSeparatorNoise D0 dt P Pprime ω i j =
      (Real.sqrt (D0 * dt / 2) : ℂ) *
        (freshLinearForm (fun u : ι × ι => P i u.1 * Pprime u.2 j) ω +
         freshAntiLinearForm (fun u : ι × ι => Pprime i u.2 * P u.1 j) ω) := by
  simp only [freshSeparatorNoise, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    mul_freshCircularMatrix_entry, mul_freshCircularMatrix_adjoint_entry]

/-- Second entry moment of the separator (both crossed orders). -/
theorem integral_freshSeparatorNoise_entry_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D0 dt : ℝ) (hscale : 0 ≤ D0 * dt / 2) (P Pprime : Matrix ι ι ℂ)
    (hP : P * P = P) (hPprime : Pprime * Pprime = Pprime) (i j k l : ι) :
    ∫ ω : (ι × ι) → ℝ × ℝ,
      freshSeparatorNoise D0 dt P Pprime ω i j * freshSeparatorNoise D0 dt P Pprime ω k l
      ∂freshCircularMatrixLaw ι =
      (D0 * dt / 2 : ℂ) * (P i l * Pprime k j + Pprime i l * P k j) := by
  unfold freshCircularMatrixLaw
  have hnorm : (Real.sqrt (D0 * dt / 2) : ℂ) * Real.sqrt (D0 * dt / 2) =
      (D0 * dt / 2 : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt hscale
  simp_rw [freshSeparatorNoise_entry]
  rw [show (fun ω : (ι × ι) → ℝ × ℝ =>
      (Real.sqrt (D0 * dt / 2) : ℂ) *
        (freshLinearForm (fun u : ι × ι => P i u.1 * Pprime u.2 j) ω +
         freshAntiLinearForm (fun u : ι × ι => Pprime i u.2 * P u.1 j) ω) *
      ((Real.sqrt (D0 * dt / 2) : ℂ) *
        (freshLinearForm (fun u : ι × ι => P k u.1 * Pprime u.2 l) ω +
         freshAntiLinearForm (fun u : ι × ι => Pprime k u.2 * P u.1 l) ω))) =
      fun ω => ((Real.sqrt (D0 * dt / 2) : ℂ) * Real.sqrt (D0 * dt / 2)) *
        ((freshLinearForm (fun u : ι × ι => P i u.1 * Pprime u.2 j) ω +
          freshAntiLinearForm (fun u : ι × ι => Pprime i u.2 * P u.1 j) ω) *
         (freshLinearForm (fun u : ι × ι => P k u.1 * Pprime u.2 l) ω +
          freshAntiLinearForm (fun u : ι × ι => Pprime k u.2 * P u.1 l) ω)) by
    funext ω
    ring]
  rw [integral_const_mul, hnorm, integral_freshMixedForms]
  congr 1
  simp only [Fintype.sum_prod_type, Finset.sum_add_distrib]
  have hfirst : (∑ a, ∑ b, (P i a * Pprime b j) * (Pprime k b * P a l)) =
      (P * P) i l * (Pprime * Pprime) k j := by
    simp only [Matrix.mul_apply, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hsecond : (∑ a, ∑ b, (Pprime i b * P a j) * (P k a * Pprime b l)) =
      (Pprime * Pprime) i l * (P * P) k j := by
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hfirst, hsecond, hP, hPprime]

private theorem memLp_two_freshSeparatorNoise_entry {ι : Type*} [Fintype ι]
    (D0 dt : ℝ) (P Pprime : Matrix ι ι ℂ) (i j : ι) :
    MemLp (fun ω : (ι × ι) → ℝ × ℝ => freshSeparatorNoise D0 dt P Pprime ω i j) 2
      (freshCircularMatrixLaw ι) := by
  have h := ((hasGaussianLaw_freshSeparatorNoise D0 dt P Pprime).map_fun
    ((LinearMap.proj (i, j) : ((ι × ι) → ℂ) →ₗ[ℝ] ℂ).toContinuousLinearMap)).memLp
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  exact MemLp.ae_eq (Filter.Eventually.of_forall fun _ => by rfl) h

/-- Integrability of every bilinear entry contraction of the complete separator. -/
theorem integrable_freshSeparatorNoise_entry_mul {ι : Type*} [Fintype ι]
    (D0 dt : ℝ) (P Pprime : Matrix ι ι ℂ) (i j k l : ι) :
    Integrable (fun ω : (ι × ι) → ℝ × ℝ =>
      freshSeparatorNoise D0 dt P Pprime ω i j * freshSeparatorNoise D0 dt P Pprime ω k l)
      (freshCircularMatrixLaw ι) := by
  exact ((memLp_two_freshSeparatorNoise_entry D0 dt P Pprime i j).integrable_mul
    (memLp_two_freshSeparatorNoise_entry D0 dt P Pprime k l)).congr
      (Filter.Eventually.of_forall fun _ => by rfl)

private theorem trace_mul_pair_entries {ι : Type*} [Fintype ι] (A X : Matrix ι ι ℂ) :
    Matrix.trace (A * X) = ∑ u : ι × ι, A u.1 u.2 * X u.2 u.1 := by
  change (∑ i, (A * X) i i) = _
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]

private theorem trace_four_pair_entries {ι : Type*} [Fintype ι]
    (A X B Y : Matrix ι ι ℂ) :
    Matrix.trace (A * X * B * Y) =
      ∑ u : ι × ι, ∑ v : ι × ι,
        (A u.1 u.2 * B v.1 v.2) * (X u.2 v.1 * Y v.2 u.1) := by
  change (∑ i, (A * X * B * Y) i i) = _
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem trace_product_pair_entries {ι : Type*} [Fintype ι]
    (A B X : Matrix ι ι ℂ) :
    Matrix.trace (A * X) * Matrix.trace (B * X) =
      ∑ u : ι × ι, ∑ v : ι × ι,
        (A u.1 u.2 * B v.1 v.2) * (X u.2 u.1 * X v.2 v.1) := by
  rw [trace_mul_pair_entries, trace_mul_pair_entries]
  simp only [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Trace sandwich contraction under the fresh law, for arbitrary complex `A, B`. -/
theorem integral_freshSeparatorNoise_traceSandwich {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D0 dt : ℝ) (hscale : 0 ≤ D0 * dt / 2) (P Pprime : Matrix ι ι ℂ)
    (hP : P * P = P) (hPprime : Pprime * Pprime = Pprime) (A B : Matrix ι ι ℂ) :
    ∫ ω : (ι × ι) → ℝ × ℝ,
      Matrix.trace (A * freshSeparatorNoise D0 dt P Pprime ω * B *
        freshSeparatorNoise D0 dt P Pprime ω) ∂freshCircularMatrixLaw ι =
      (D0 * dt / 2 : ℂ) *
        (Matrix.trace (A * P) * Matrix.trace (B * Pprime) +
         Matrix.trace (A * Pprime) * Matrix.trace (B * P)) := by
  simp_rw [trace_four_pair_entries]
  rw [integral_finsetSum _]
  · trans ∑ u : ι × ι, ∑ v : ι × ι,
      (A u.1 u.2 * B v.1 v.2) * ((D0 * dt / 2 : ℂ) *
        (P u.2 u.1 * Pprime v.2 v.1 + Pprime u.2 u.1 * P v.2 v.1))
    · apply Finset.sum_congr rfl
      intro u _
      rw [integral_finsetSum _ (fun v _ =>
        (integrable_freshSeparatorNoise_entry_mul D0 dt P Pprime u.2 v.1 v.2 u.1).const_mul _)]
      simp_rw [integral_const_mul,
        integral_freshSeparatorNoise_entry_mul D0 dt hscale P Pprime hP hPprime]
    · simp only [trace_mul_pair_entries]
      simp only [Fintype.sum_mul_sum]
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        ring
      · apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        ring
  · intro u _
    exact integrable_finsetSum _ (fun v _ =>
      (integrable_freshSeparatorNoise_entry_mul D0 dt P Pprime u.2 v.1 v.2 u.1).const_mul _)

/-- Product-of-traces contraction under the fresh law, with both matrix orders. -/
theorem integral_freshSeparatorNoise_traceProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D0 dt : ℝ) (hscale : 0 ≤ D0 * dt / 2) (P Pprime : Matrix ι ι ℂ)
    (hP : P * P = P) (hPprime : Pprime * Pprime = Pprime) (A B : Matrix ι ι ℂ) :
    ∫ ω : (ι × ι) → ℝ × ℝ,
      Matrix.trace (A * freshSeparatorNoise D0 dt P Pprime ω) *
        Matrix.trace (B * freshSeparatorNoise D0 dt P Pprime ω) ∂freshCircularMatrixLaw ι =
      (D0 * dt / 2 : ℂ) *
        (Matrix.trace (A * P * B * Pprime) + Matrix.trace (A * Pprime * B * P)) := by
  simp_rw [trace_product_pair_entries]
  rw [integral_finsetSum _]
  · trans ∑ u : ι × ι, ∑ v : ι × ι,
      (A u.1 u.2 * B v.1 v.2) * ((D0 * dt / 2 : ℂ) *
        (P u.2 v.1 * Pprime v.2 u.1 + Pprime u.2 v.1 * P v.2 u.1))
    · apply Finset.sum_congr rfl
      intro u _
      rw [integral_finsetSum _ (fun v _ =>
        (integrable_freshSeparatorNoise_entry_mul D0 dt P Pprime u.2 u.1 v.2 v.1).const_mul _)]
      simp_rw [integral_const_mul,
        integral_freshSeparatorNoise_entry_mul D0 dt hscale P Pprime hP hPprime]
    · simp only [trace_four_pair_entries, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        ring
      · apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        ring
  · intro u _
    exact integrable_finsetSum _ (fun v _ =>
      (integrable_freshSeparatorNoise_entry_mul D0 dt P Pprime u.2 u.1 v.2 v.1).const_mul _)

/-- The current is the signed difference `P' - P`. -/
theorem freshSeparatorNoise_signedCurrent {ι : Type*} [Fintype ι]
    (D0 dt : ℝ) (P Pprime : Matrix ι ι ℂ) (ω : (ι × ι) → ℝ × ℝ) :
    freshSeparatorNoise D0 dt P Pprime ω =
      (Real.sqrt (D0 * dt / 2) : ℂ) •
        (P * freshCircularMatrix ω * (P + fullCurrent P Pprime) +
          (P + fullCurrent P Pprime) * (freshCircularMatrix ω)ᴴ * P) := by
  have hcurrent : P + fullCurrent P Pprime = Pprime := by
    unfold fullCurrent
    abel
  rw [hcurrent]
  rfl

end BlockBand.SourceProcess
