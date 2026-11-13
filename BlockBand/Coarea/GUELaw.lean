module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Coarea.ChartLaw
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalFreshGUEDensity
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The GUE law `GUE_d(t)` of the coarea formula

## Main results

* `isProbabilityMeasure_gueMeasure`, `measurable_gueSample`, `gueSample_isHermitian`
  (pointwise), `ae_isHermitian_gueMeasure`.
* `gueMeasure_map_unitary_conj`: `(gueMeasure ι t).map (W * · * star W) = gueMeasure ι t`
  for every `W ∈ Matrix.unitaryGroup ι ℂ`. Proof: the real coordinates of `X` have the
  product law `∏ N(0,1)`, which is Mathlib's `stdGaussian` on `EuclideanSpace`
  (`map_pi_eq_stdGaussian`); `X ↦ W X W*` is a real-linear isometry of those coordinates
  (Frobenius norm is unitarily invariant), so `stdGaussian_map` applies; and
  `gueSample t (W X W*) = W (gueSample t X) W*`.
* `gueMeasure_map_reindex`: `(gueMeasure ι t).map (Matrix.reindex e e) = gueMeasure κ t`
  for every equivalence `e : ι ≃ κ` of finite types (moves between
  `PairSite p i` and `Fin (2W)`).
* `gueMeasure_map_coordsOfMatrix`: the diagonal, real strict-upper and imaginary
  strict-upper coordinates of a `gueMeasure (Fin d) t` sample are independent centred
  real Gaussians of variances `t`, `t/2`, `t/2` (`hermCoordGaussian`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.GUELaw

open MeasureTheory ProbabilityTheory Matrix WithLp
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open CoareaNative.BlockBand (StrictUpperIndex HermitianCoordinate hermitianUpperEntry
  hermitianMatrixOfCoordinates coordinatesOfHermitian hermitianCoordinateEquivFin
  HermitianCoordinateSpace hermitianOfFinCoordinates hermitianGUEFinCoordinateVariance
  hermitianGUECoordinateMeasure hermitianGUEDensity hermitianGUEBlock HermitianMatrix)
open scoped ENNReal NNReal ComplexConjugate

variable {ι : Type*}

/-!
## Basic facts
-/

/-- The circular coordinate map `r ↦ (r(u,0) + i r(u,1))/√2` is measurable. -/
theorem measurable_circularBrownianCoordinates :
    Measurable (circularBrownianCoordinates (ι := ι)) := by
  apply Measurable.of_eval
  intro u
  unfold circularBrownianCoordinates
  fun_prop

/-- The GUE sample map `X ↦ √(t/2)(X + Xᴴ)` is continuous. -/
theorem continuous_gueSample (t : ℝ≥0) : Continuous (gueSample (ι := ι) t) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gueSample, Matrix.of_apply]
  fun_prop

/-- The GUE sample map is measurable. -/
theorem measurable_gueSample (t : ℝ≥0) : Measurable (gueSample (ι := ι) t) :=
  Measurable.of_eval_matrix _ fun a b => by
    simp only [gueSample, Matrix.of_apply]
    fun_prop

/-- The circular increment law is a probability measure. -/
instance isProbabilityMeasure_commonCircularIncrementLaw [Fintype ι] (δ : ℝ≥0) :
    IsProbabilityMeasure (commonCircularIncrementLaw ι δ) := by
  unfold commonCircularIncrementLaw
  infer_instance

/-- `GUE_ι(t)` is a probability measure. -/
instance isProbabilityMeasure_gueMeasure [Fintype ι] (t : ℝ≥0) :
    IsProbabilityMeasure (gueMeasure ι t) := by
  unfold gueMeasure
  infer_instance

/-- Every GUE sample is Hermitian, pointwise. -/
theorem gueSample_isHermitian (t : ℝ≥0) (X : ι × ι → ℂ) :
    (gueSample t X).IsHermitian := by
  ext a b
  simp only [gueSample, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_add,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- `GUE_ι(t)` is carried by Hermitian matrices. -/
theorem ae_isHermitian_gueMeasure [Fintype ι] (t : ℝ≥0) :
    ∀ᵐ G ∂gueMeasure ι t, G.IsHermitian := by
  unfold gueMeasure
  rw [ae_map_iff (measurable_gueSample t).aemeasurable
    BlockBand.Model.Construction.measurableSet_isHermitian]
  exact Filter.Eventually.of_forall (gueSample_isHermitian t)

/-!
## Unitary conjugation invariance
-/

/-- Real coordinate index of a flat complex matrix. -/
abbrev RealIndex (ι : Type*) := (ι × ι) × Fin 2

/-- A flat complex array as a matrix. -/
def flatMatrix (X : ι × ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun a b => X (a, b)

/-- Flat conjugation `X ↦ W X W*`. -/
def flatConj [Fintype ι] (W : Matrix ι ι ℂ) (X : ι × ι → ℂ) : ι × ι → ℂ :=
  fun u => (W * flatMatrix X * star W) u.1 u.2

/-- Inverse of `circularBrownianCoordinates`: `√2 Re`, `√2 Im`. -/
def realCoords (Y : ι × ι → ℂ) : RealIndex ι → ℝ :=
  fun q => Real.sqrt 2 * ![(Y q.1).re, (Y q.1).im] q.2

/-- `circularBrownianCoordinates` is a left inverse of `realCoords`. -/
theorem circular_realCoords (Y : ι × ι → ℂ) :
    circularBrownianCoordinates (realCoords Y) = Y := by
  funext u
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
  simp only [circularBrownianCoordinates, realCoords]
  apply Complex.ext <;> simp [Complex.div_ofReal_re, Complex.div_ofReal_im]

/-- `realCoords` is a left inverse of `circularBrownianCoordinates`. -/
theorem realCoords_circular (r : RealIndex ι → ℝ) :
    realCoords (circularBrownianCoordinates r) = r := by
  funext ⟨u, j⟩
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
  fin_cases j <;>
    simp [circularBrownianCoordinates, realCoords, Complex.div_ofReal_re,
      Complex.div_ofReal_im] <;> field_simp

/-- `∑ (realCoords Y)² = 2 ∑ |Y_u|²`. -/
theorem sum_sq_realCoords [Fintype ι] (Y : ι × ι → ℂ) :
    ∑ q, realCoords Y q ^ 2 = 2 * ∑ u, ‖Y u‖ ^ 2 := by
  simp only [realCoords, Fintype.sum_prod_type (f := fun q : (ι × ι) × Fin 2 => _),
    Fin.sum_univ_two, mul_pow, Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2), Complex.sq_norm,
    Complex.normSq_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp
  ring

/-- `∑_{a,b} |A_ab|² = Tr(A Aᴴ)`. -/
theorem sum_norm_sq_eq_trace [Fintype ι] (A : Matrix ι ι ℂ) :
    ((∑ a, ∑ b, ‖A a b‖ ^ 2 : ℝ) : ℂ) = (A * Aᴴ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The Frobenius norm is invariant under unitary conjugation. -/
theorem sum_norm_sq_flatConj [Fintype ι] [DecidableEq ι] {W : Matrix ι ι ℂ}
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) (X : ι × ι → ℂ) :
    ∑ u, ‖flatConj W X u‖ ^ 2 = ∑ u, ‖X u‖ ^ 2 := by
  have hWW : star W * W = 1 := (Matrix.mem_unitaryGroup_iff').1 hW
  set M := flatMatrix X
  have hL : ∑ u, ‖flatConj W X u‖ ^ 2 = ∑ a, ∑ b, ‖(W * M * star W) a b‖ ^ 2 :=
    Fintype.sum_prod_type _
  have hR : ∑ u, ‖X u‖ ^ 2 = ∑ a, ∑ b, ‖M a b‖ ^ 2 := Fintype.sum_prod_type _
  rw [hL, hR]
  apply Complex.ofReal_injective
  rw [sum_norm_sq_eq_trace, sum_norm_sq_eq_trace]
  have : (W * M * star W) * (W * M * star W)ᴴ = W * (M * Mᴴ * star W) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
      star_star, ← Matrix.star_eq_conjTranspose]
    calc W * M * star W * (W * (star M * star W))
        = W * M * (star W * W) * (star M * star W) := by simp only [Matrix.mul_assoc]
      _ = W * (M * star M * star W) := by rw [hWW, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, hWW, Matrix.mul_one]

/-- Additivity of the circular coordinate map. -/
theorem circular_add [Fintype ι] (r s : RealIndex ι → ℝ) :
    circularBrownianCoordinates (r + s) =
      circularBrownianCoordinates r + circularBrownianCoordinates s := by
  funext u; simp only [circularBrownianCoordinates, Pi.add_apply]; push_cast; ring

/-- Real homogeneity of the circular coordinate map. -/
theorem circular_smul [Fintype ι] (c : ℝ) (r : RealIndex ι → ℝ) :
    circularBrownianCoordinates (c • r) = (c : ℂ) • circularBrownianCoordinates r := by
  funext u; simp only [circularBrownianCoordinates, Pi.smul_apply, smul_eq_mul]; push_cast; ring

/-- Additivity of flat conjugation. -/
theorem flatConj_add [Fintype ι] (W : Matrix ι ι ℂ) (X Y : ι × ι → ℂ) :
    flatConj W (X + Y) = flatConj W X + flatConj W Y := by
  have : flatMatrix (X + Y) = flatMatrix X + flatMatrix Y := by ext a b; rfl
  funext u; simp only [flatConj, this, Matrix.mul_add, Matrix.add_mul, Pi.add_apply,
    Matrix.add_apply]

/-- Complex homogeneity of flat conjugation. -/
theorem flatConj_smul [Fintype ι] (W : Matrix ι ι ℂ) (z : ℂ) (X : ι × ι → ℂ) :
    flatConj W (z • X) = z • flatConj W X := by
  have : flatMatrix (z • X) = z • flatMatrix X := by ext a b; rfl
  funext u; simp only [flatConj, this, Matrix.mul_smul, Matrix.smul_mul, Pi.smul_apply,
    Matrix.smul_apply]

/-- Additivity of `realCoords`. -/
theorem realCoords_add (Y Z : ι × ι → ℂ) :
    realCoords (Y + Z) = realCoords Y + realCoords Z := by
  funext ⟨u, j⟩; fin_cases j <;> simp [realCoords] <;> ring

/-- Real homogeneity of `realCoords`. -/
theorem realCoords_smul (c : ℝ) (Y : ι × ι → ℂ) :
    realCoords ((c : ℂ) • Y) = c • realCoords Y := by
  funext ⟨u, j⟩; fin_cases j <;> simp [realCoords] <;> ring

/-- The real-linear map `r ↦ realCoords (W · circ(r) · W*)` on real coordinates. -/
def conjRealLinear [Fintype ι] (W : Matrix ι ι ℂ) :
    (RealIndex ι → ℝ) →ₗ[ℝ] (RealIndex ι → ℝ) where
  toFun r := realCoords (flatConj W (circularBrownianCoordinates r))
  map_add' r s := by rw [circular_add, flatConj_add, realCoords_add]
  map_smul' c r := by
    rw [circular_smul, flatConj_smul, realCoords_smul]; rfl

/-- `∑ r_q² = 2 ∑ |circ(r)_u|²`. -/
theorem norm_sq_eq_sum_circular [Fintype ι] (r : RealIndex ι → ℝ) :
    ∑ q, r q ^ 2 = 2 * ∑ u, ‖circularBrownianCoordinates r u‖ ^ 2 := by
  conv_lhs => rw [← realCoords_circular r]
  exact sum_sq_realCoords _

/-- `conjRealLinear W`, transported to the Euclidean space, is a linear isometry
for unitary `W`. -/
def conjEuclidean [Fintype ι] [DecidableEq ι] {W : Matrix ι ι ℂ}
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    EuclideanSpace ℝ (RealIndex ι) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (RealIndex ι) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (WithLp.linearEquiv 2 ℝ (RealIndex ι → ℝ)).symm.toLinearMap ∘ₗ
        conjRealLinear W ∘ₗ (WithLp.linearEquiv 2 ℝ (RealIndex ι → ℝ)).toLinearMap
      norm_map' := fun x => by
        have key : ‖(WithLp.linearEquiv 2 ℝ (RealIndex ι → ℝ)).symm
            (conjRealLinear W (WithLp.linearEquiv 2 ℝ (RealIndex ι → ℝ) x))‖ ^ 2 = ‖x‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
          change ∑ q, realCoords (flatConj W (circularBrownianCoordinates (ofLp x))) q ^ 2 =
            ∑ q, (ofLp x) q ^ 2
          rw [sum_sq_realCoords, sum_norm_sq_flatConj hW, norm_sq_eq_sum_circular]
        exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 key }
    rfl

/-- Coordinate formula for `conjEuclidean`. -/
theorem conjEuclidean_apply [Fintype ι] [DecidableEq ι] {W : Matrix ι ι ℂ}
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) (x : EuclideanSpace ℝ (RealIndex ι)) :
    ofLp (conjEuclidean hW x) = realCoords (flatConj W (circularBrownianCoordinates (ofLp x))) :=
  rfl

/-- The standard circular matrix law is invariant under `X ↦ W X W*`, `W` unitary. -/
theorem map_flatConj_commonCircularIncrementLaw [Fintype ι] [DecidableEq ι]
    {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    (commonCircularIncrementLaw ι 1).map (flatConj W) = commonCircularIncrementLaw ι 1 := by
  set P : Measure (RealIndex ι → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  have hP : P = (stdGaussian (EuclideanSpace ℝ (RealIndex ι))).map ofLp := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (measurable_ofLp 2 _) (measurable_toLp 2 _)]
    have : (ofLp ∘ toLp 2 : (RealIndex ι → ℝ) → (RealIndex ι → ℝ)) = id := rfl
    rw [this, Measure.map_id]
  have hflat : Measurable (flatConj (ι := ι) W) := by
    apply Measurable.of_eval
    intro u
    simp only [flatConj, flatMatrix, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hfun : flatConj W ∘ circularBrownianCoordinates ∘ ofLp =
      (circularBrownianCoordinates ∘ ofLp) ∘ conjEuclidean hW := by
    funext x
    simp only [Function.comp_apply, conjEuclidean_apply, circular_realCoords]
  unfold commonCircularIncrementLaw
  change (P.map circularBrownianCoordinates).map (flatConj W) = P.map circularBrownianCoordinates
  rw [hP, Measure.map_map measurable_circularBrownianCoordinates (measurable_ofLp 2 _),
    Measure.map_map hflat (measurable_circularBrownianCoordinates.comp (measurable_ofLp 2 _)),
    hfun,
    ← Measure.map_map (measurable_circularBrownianCoordinates.comp (measurable_ofLp 2 _))
      (conjEuclidean hW).continuous.measurable, stdGaussian_map]

/-- Flat conjugation is matrix conjugation. -/
theorem flatMatrix_flatConj [Fintype ι] (W : Matrix ι ι ℂ) (X : ι × ι → ℂ) :
    flatMatrix (flatConj W X) = W * flatMatrix X * star W := by
  ext a b; rfl

/-- `gueSample t X = √(t/2) • (X + Xᴴ)`. -/
theorem gueSample_eq_smul (t : ℝ≥0) (X : ι × ι → ℂ) :
    gueSample t X =
      (Real.sqrt ((t : ℝ) / 2) : ℂ) • (flatMatrix X + (flatMatrix X)ᴴ) := by
  ext a b
  simp [gueSample, flatMatrix, Matrix.conjTranspose_apply]

/-- `gueSample t (W X W*) = W (gueSample t X) W*`. -/
theorem gueSample_flatConj [Fintype ι] (t : ℝ≥0) (W : Matrix ι ι ℂ) (X : ι × ι → ℂ) :
    gueSample t (flatConj W X) = W * gueSample t X * star W := by
  rw [gueSample_eq_smul, gueSample_eq_smul, flatMatrix_flatConj, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose (star W), star_star,
    ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, Matrix.mul_assoc,
    Matrix.mul_assoc]

/-- Unitary conjugation invariance of `GUE_ι(t)`. -/
theorem gueMeasure_map_unitary_conj [Fintype ι] [DecidableEq ι] (t : ℝ≥0)
    {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    (gueMeasure ι t).map (fun G => W * G * star W) = gueMeasure ι t := by
  have hconj : Measurable (fun G : Matrix ι ι ℂ => W * G * star W) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  have hflat : Measurable (flatConj (ι := ι) W) := by
    apply Measurable.of_eval
    intro u
    simp only [flatConj, flatMatrix, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hcomp : (fun G : Matrix ι ι ℂ => W * G * star W) ∘ gueSample t =
      gueSample t ∘ flatConj W := by
    funext X; exact (gueSample_flatConj t W X).symm
  unfold gueMeasure
  rw [Measure.map_map hconj (measurable_gueSample t), hcomp,
    ← Measure.map_map (measurable_gueSample t) hflat,
    map_flatConj_commonCircularIncrementLaw hW]

/-!
## Real coordinate law for `ι = Fin d`
-/

/-- Coordinate variances of `GUE_d(t)`: `t` on the diagonal, `t/2` on each real or
imaginary strict-upper coordinate. -/
def hermCoordVariance {d : ℕ} (t : ℝ≥0) : HermitianCoordinate d → ℝ≥0
  | .inl _ => t
  | .inr _ => t / 2

/-- The explicit product of independent centred real Gaussian coordinate laws. -/
def hermCoordGaussian (d : ℕ) (t : ℝ≥0) : Measure (HermitianCoordinate d → ℝ) :=
  Measure.pi fun k => gaussianReal 0 (hermCoordVariance t k)

/-- The coordinate product is a probability measure. -/
instance (d : ℕ) (t : ℝ≥0) : IsProbabilityMeasure (hermCoordGaussian d t) := by
  unfold hermCoordGaussian; infer_instance

/-- Extraction of diagonal / real-upper / imaginary-upper coordinates on raw matrices; on
Hermitian matrices it is the `coordinatesOfHermitian` (`coordsOfMatrix_coe`).
-/
def coordsOfMatrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : HermitianCoordinate d → ℝ
  | .inl i => (A i i).re
  | .inr (.inl ij) => (A ij.1.1 ij.1.2).re
  | .inr (.inr ij) => (A ij.1.1 ij.1.2).im

/-- On Hermitian matrices `coordsOfMatrix` is the `coordinatesOfHermitian`. -/
theorem coordsOfMatrix_coe {d : ℕ} (A : HermitianMatrix (Fin d)) :
    coordsOfMatrix A.1 = coordinatesOfHermitian A := by
  funext k
  rcases k with i | ij | ij <;> rfl

/-- Reconstruction `hermitianMatrixOfCoordinates` inverts coordinate extraction on
Hermitian matrices.
-/
theorem hermitianMatrixOfCoordinates_coordsOfMatrix {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) : hermitianMatrixOfCoordinates (coordsOfMatrix A) = A := by
  ext i j
  by_cases hEq : i = j
  · subst j
    simpa [hermitianMatrixOfCoordinates, coordsOfMatrix] using hA.coe_re_apply_self i
  · by_cases hLt : i < j
    · simp only [hermitianMatrixOfCoordinates, hEq, hLt, ↓reduceDIte, coordsOfMatrix,
        hermitianUpperEntry]
      apply Complex.ext <;> simp
    · simp only [hermitianMatrixOfCoordinates, hEq, hLt, ↓reduceDIte, coordsOfMatrix,
        hermitianUpperEntry]
      rw [← hA.apply i j]
      congr 1
      apply Complex.ext <;> simp

/-- Coordinate extraction is measurable. -/
theorem measurable_coordsOfMatrix (d : ℕ) :
    Measurable (coordsOfMatrix (d := d)) := by
  refine measurable_pi_iff.2 fun k => ?_
  rcases k with i | ij | ij
  · exact Complex.measurable_re.comp (Matrix.measurable_apply (i := i) (j := i))
  · exact Complex.measurable_re.comp (Matrix.measurable_apply (i := ij.1.1) (j := ij.1.2))
  · exact Complex.measurable_im.comp (Matrix.measurable_apply (i := ij.1.1) (j := ij.1.2))

/-- The Hermitian reconstruction `hermitianMatrixOfCoordinates` is measurable. -/
theorem measurable_hermitianMatrixOfCoordinates (d : ℕ) :
    Measurable (hermitianMatrixOfCoordinates (d := d)) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  by_cases hEq : i = j
  · simp only [hermitianMatrixOfCoordinates, hEq, ↓reduceDIte]; fun_prop
  · by_cases hLt : i < j
    · simp only [hermitianMatrixOfCoordinates, hEq, hLt, ↓reduceDIte, hermitianUpperEntry]
      fun_prop
    · simp only [hermitianMatrixOfCoordinates, hEq, hLt, ↓reduceDIte, hermitianUpperEntry]
      fun_prop

/-- The two circular real coordinates feeding one Hermitian coordinate. -/
def blockIndex {d : ℕ} : HermitianCoordinate d × Fin 2 → RealIndex (Fin d)
  | (.inl a, j) => ((a, a), j)
  | (.inr (.inl ij), j) => (if j = 0 then ij.1 else ij.1.swap, 0)
  | (.inr (.inr ij), j) => (if j = 0 then ij.1 else ij.1.swap, 1)

/-- Distinct Hermitian coordinates use disjoint pairs of circular real inputs. -/
theorem blockIndex_injective (d : ℕ) : Function.Injective (blockIndex (d := d)) := by
  rintro ⟨k, j⟩ ⟨k', j'⟩ h
  rcases k with a | ⟨⟨a, b⟩, hab⟩ | ⟨⟨a, b⟩, hab⟩ <;>
    rcases k' with a' | ⟨⟨a', b'⟩, hab'⟩ | ⟨⟨a', b'⟩, hab'⟩ <;>
    fin_cases j <;> fin_cases j' <;>
    simp [blockIndex, Prod.ext_iff] at h ⊢ <;>
    simp only [Fin.ext_iff, Fin.lt_def] at * <;> omega

/-- `√(t/2)/√2 = √t/2`. -/
def gueScale (t : ℝ≥0) : ℝ := Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2

/-- The Hermitian coordinate as a function of its two circular real inputs. -/
def blockValue {d : ℕ} (t : ℝ≥0) : HermitianCoordinate d → (Fin 2 → ℝ) → ℝ
  | .inl _, u => gueScale t * (u 0 + u 0)
  | .inr (.inl _), u => gueScale t * (u 0 + u 1)
  | .inr (.inr _), u => gueScale t * (u 0 - u 1)

/-- Each `blockValue t k` is measurable. -/
theorem measurable_blockValue {d : ℕ} (t : ℝ≥0) (k : HermitianCoordinate d) :
    Measurable (blockValue t k) := by
  rcases k with a | ij | ij
  · change Measurable fun u : Fin 2 → ℝ => gueScale t * (u 0 + u 0); fun_prop
  · change Measurable fun u : Fin 2 → ℝ => gueScale t * (u 0 + u 1); fun_prop
  · change Measurable fun u : Fin 2 → ℝ => gueScale t * (u 0 - u 1); fun_prop

/-- Each Hermitian coordinate of `gueSample t (circ r)` is `blockValue` of its two inputs. -/
theorem coordsOfMatrix_gueSample (d : ℕ) (t : ℝ≥0) (r : RealIndex (Fin d) → ℝ)
    (k : HermitianCoordinate d) :
    coordsOfMatrix (gueSample t (circularBrownianCoordinates r)) k =
      blockValue t k (fun j => r (blockIndex (k, j))) := by
  rcases k with a | ij | ij <;>
    simp [coordsOfMatrix, gueSample, circularBrownianCoordinates, blockValue, blockIndex,
      gueScale, Complex.div_ofReal_re, Complex.div_ofReal_im, Prod.swap] <;> ring

/-- Under `∏ N(0,1)` the Hermitian coordinates of the GUE sample are mutually independent. -/
theorem iIndepFun_blockValue (d : ℕ) (t : ℝ≥0) :
    iIndepFun (fun k (r : RealIndex (Fin d) → ℝ) => blockValue t k (fun j => r (blockIndex (k, j))))
      (Measure.pi fun _ => gaussianReal 0 1) := by
  have h0 : iIndepFun (fun q (r : RealIndex (Fin d) → ℝ) => r q)
      (Measure.pi fun _ => gaussianReal 0 1) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h1 := h0.precomp (blockIndex_injective d)
  have h2 := BlockBand.Parameters.iIndepFun_curry_of_iIndepFun_prod
    (X := fun k j (r : RealIndex (Fin d) → ℝ) => r (blockIndex (k, j)))
    (fun _ _ => measurable_pi_apply _) h1
  exact h2.comp (fun k => blockValue t k) (measurable_blockValue t)

/-- Marginal law of each Hermitian coordinate: `N(0,t)` diagonal, `N(0,t/2)` off-diagonal. -/
theorem map_blockValue (d : ℕ) (t : ℝ≥0) (k : HermitianCoordinate d) :
    (Measure.pi fun _ : RealIndex (Fin d) => gaussianReal 0 1).map
        (fun r => blockValue t k (fun j => r (blockIndex (k, j)))) =
      gaussianReal 0 (hermCoordVariance t k) := by
  set P : Measure (RealIndex (Fin d) → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  have h0 : iIndepFun (fun q (r : RealIndex (Fin d) → ℝ) => r q) P :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hlaw : ∀ q, HasLaw (fun r : RealIndex (Fin d) → ℝ => r q) (gaussianReal 0 1) P :=
    fun q => ⟨(measurable_pi_apply q).aemeasurable,
      (measurePreserving_eval (fun _ : RealIndex (Fin d) => gaussianReal 0 1) q).map_eq⟩
  have ht2 : (0 : ℝ) ≤ (t : ℝ) / 2 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have hc : gueScale t ^ 2 = (t : ℝ) / 4 := by
    rw [gueScale, div_pow, Real.sq_sqrt ht2, hs2]; ring
  rcases k with a | ij | ij
  · have hf : (fun r : RealIndex (Fin d) → ℝ => blockValue t (.inl a)
        (fun j => r (blockIndex (.inl a, j)))) =
        (fun x => (2 * gueScale t) * x) ∘ (fun r => r ((a, a), 0)) := by
      funext r; simp [blockValue, blockIndex]; ring
    rw [hf, ← Measure.map_map (by fun_prop : Measurable fun x : ℝ => 2 * gueScale t * x)
      (measurable_pi_apply _), (hlaw _).map_eq, gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [hermCoordVariance, mul_pow, hc]; ring
  · have hne : ((ij.1, 0) : RealIndex (Fin d)) ≠ (ij.1.swap, 0) := by
      intro h; have := congrArg (fun q => q.1.1) h; simp at this
      exact absurd ij.2 (by rw [this]; exact lt_irrefl _)
    have hf : (fun r : RealIndex (Fin d) → ℝ => blockValue t (.inr (.inl ij))
        (fun j => r (blockIndex (.inr (.inl ij), j)))) =
        (fun x => gueScale t * x) ∘
          ((fun r : RealIndex (Fin d) → ℝ => r (ij.1, 0)) + fun r => r (ij.1.swap, 0)) := by
      funext r; simp [blockValue, blockIndex]
    rw [hf, ← Measure.map_map (by fun_prop : Measurable fun x : ℝ => gueScale t * x)
      (by fun_prop),
      gaussianReal_add_gaussianReal_of_indepFun (h0.indepFun hne) (hlaw _) (hlaw _),
      gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [hermCoordVariance, hc]; ring
  · have hne : ((ij.1, 1) : RealIndex (Fin d)) ≠ (ij.1.swap, 1) := by
      intro h; have := congrArg (fun q => q.1.1) h; simp at this
      exact absurd ij.2 (by rw [this]; exact lt_irrefl _)
    have hneg : HasLaw (fun r : RealIndex (Fin d) → ℝ => -r (ij.1.swap, 1))
        (gaussianReal 0 1) P := by
      refine ⟨(measurable_pi_apply _).neg.aemeasurable, ?_⟩
      have : (fun r : RealIndex (Fin d) → ℝ => -r (ij.1.swap, 1)) =
          (fun x => -x) ∘ (fun r => r (ij.1.swap, 1)) := rfl
      rw [this, ← Measure.map_map (by fun_prop : Measurable fun x : ℝ => -x)
        (measurable_pi_apply _), (hlaw _).map_eq, gaussianReal_map_neg, neg_zero]
    have hind : IndepFun (fun r : RealIndex (Fin d) → ℝ => r (ij.1, 1))
        (fun r => -r (ij.1.swap, 1)) P :=
      (h0.indepFun hne).comp measurable_id measurable_neg
    have hf : (fun r : RealIndex (Fin d) → ℝ => blockValue t (.inr (.inr ij))
        (fun j => r (blockIndex (.inr (.inr ij), j)))) =
        (fun x => gueScale t * x) ∘
          ((fun r : RealIndex (Fin d) → ℝ => r (ij.1, 1)) + fun r => -r (ij.1.swap, 1)) := by
      funext r; simp [blockValue, blockIndex, sub_eq_add_neg]
    rw [hf, ← Measure.map_map (by fun_prop : Measurable fun x : ℝ => gueScale t * x)
      (by fun_prop),
      gaussianReal_add_gaussianReal_of_indepFun hind (hlaw _) hneg,
      gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [hermCoordVariance, hc]; ring

/-- Coordinate law of `GUE_d(t)`: the diagonal,
real-upper and imaginary-upper coordinates of a `gueMeasure (Fin d) t` sample are
independent centred Gaussians of variances `t`, `t/2`, `t/2`. -/
theorem gueMeasure_map_coordsOfMatrix (d : ℕ) (t : ℝ≥0) :
    (gueMeasure (Fin d) t).map coordsOfMatrix = hermCoordGaussian d t := by
  unfold gueMeasure commonCircularIncrementLaw
  rw [Measure.map_map (measurable_gueSample t) measurable_circularBrownianCoordinates,
    Measure.map_map (measurable_coordsOfMatrix d)
      ((measurable_gueSample t).comp measurable_circularBrownianCoordinates)]
  have hfun : coordsOfMatrix ∘ gueSample t ∘ circularBrownianCoordinates =
      fun (r : RealIndex (Fin d) → ℝ) k => blockValue t k (fun j => r (blockIndex (k, j))) := by
    funext r k; exact coordsOfMatrix_gueSample d t r k
  rw [hfun, (iIndepFun_iff_map_fun_eq_pi_map
    (f := fun k (r : RealIndex (Fin d) → ℝ) => blockValue t k (fun j => r (blockIndex (k, j))))
    (fun k =>
    ((measurable_blockValue t k).comp (Measurable.of_eval
      fun j => measurable_pi_apply (blockIndex (k, j)))).aemeasurable)).1
      (iIndepFun_blockValue d t)]
  unfold hermCoordGaussian
  congr 1
  funext k
  exact map_blockValue d t k

/-- `GUE_d(t)` as the image of the explicit coordinate product under the Hermitian
reconstruction `hermitianMatrixOfCoordinates`.
-/
theorem gueMeasure_eq_map_hermitianMatrixOfCoordinates (d : ℕ) (t : ℝ≥0) :
    gueMeasure (Fin d) t = (hermCoordGaussian d t).map hermitianMatrixOfCoordinates := by
  have h : gueMeasure (Fin d) t =
      ((gueMeasure (Fin d) t).map coordsOfMatrix).map hermitianMatrixOfCoordinates := by
    unfold gueMeasure
    rw [Measure.map_map (measurable_coordsOfMatrix d) (measurable_gueSample t),
      Measure.map_map (measurable_hermitianMatrixOfCoordinates d)
        ((measurable_coordsOfMatrix d).comp (measurable_gueSample t))]
    congr 1
    funext X
    exact (hermitianMatrixOfCoordinates_coordsOfMatrix (gueSample_isHermitian t X)).symm
  rw [h, gueMeasure_map_coordsOfMatrix]

/-- The per-coordinate variance, read through `hermitianCoordinateEquivFin`, is
`hermCoordVariance`.
-/
theorem hermitianGUEFinCoordinateVariance_equivFin (d : ℕ) (t : ℝ≥0)
    (k : HermitianCoordinate d) :
    hermitianGUEFinCoordinateVariance d t t.coe_nonneg (hermitianCoordinateEquivFin d k) =
      hermCoordVariance t k := by
  apply NNReal.eq
  rcases k with i | c
  · rw [CoareaNative.BlockBand.hermitianGUEFinCoordinateVariance_equivFin_inl]; rfl
  · rw [CoareaNative.BlockBand.hermitianGUEFinCoordinateVariance_equivFin_inr]
    simp [hermCoordVariance]

/-- Reindexing the coordinate product `hermitianGUECoordinateMeasure d t _` by
`hermitianCoordinateEquivFin d` gives `hermCoordGaussian d t`.
-/
theorem hermitianGUECoordinateMeasure_map_comp_equivFin (d : ℕ) (t : ℝ≥0) :
    (hermitianGUECoordinateMeasure d t t.coe_nonneg).map
        (fun x => x ∘ hermitianCoordinateEquivFin d) =
      hermCoordGaussian d t := by
  set e := hermitianCoordinateEquivFin d
  have h0 : iIndepFun (fun q (x : HermitianCoordinateSpace d) => x q)
      (hermitianGUECoordinateMeasure d t t.coe_nonneg) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h1 := h0.precomp e.injective
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map
    (f := fun k (x : HermitianCoordinateSpace d) => x (e k))
    (fun k => (measurable_pi_apply (e k)).aemeasurable)).1 h1
  have hfun : (fun x : HermitianCoordinateSpace d => x ∘ e) = fun x k => x (e k) := rfl
  rw [hfun, hmap]
  unfold hermCoordGaussian
  congr 1
  funext k
  have := (measurePreserving_eval (fun q => gaussianReal 0
    (hermitianGUEFinCoordinateVariance d t t.coe_nonneg q)) (e k)).map_eq
  rw [hermitianGUEFinCoordinateVariance_equivFin] at this
  exact this

/-- `hermitianOfFinCoordinates`, as a raw matrix, is measurable. -/
theorem measurable_hermitianOfFinCoordinates_val (d : ℕ) :
    Measurable (fun x : HermitianCoordinateSpace d => (hermitianOfFinCoordinates d x).1) :=
  measurable_subtype_coe.comp (CoareaNative.BlockBand.measurable_hermitianOfFinCoordinates d)

/-- `GUE_d(t)` is the image of the product
`hermitianGUECoordinateMeasure d t t.coe_nonneg` of diagonal `N(0,t)` and strict-upper
real/imaginary `N(0,t/2)` laws under the reconstruction `hermitianOfFinCoordinates`.
-/
theorem gueMeasure_eq_map_hermitianGUECoordinateMeasure (d : ℕ) (t : ℝ≥0) :
    gueMeasure (Fin d) t = (hermitianGUECoordinateMeasure d t t.coe_nonneg).map
      (fun x => (hermitianOfFinCoordinates d x).1) := by
  have hcomp : (fun x : HermitianCoordinateSpace d => (hermitianOfFinCoordinates d x).1) =
      hermitianMatrixOfCoordinates ∘ (fun x => x ∘ hermitianCoordinateEquivFin d) := rfl
  rw [hcomp, ← Measure.map_map (measurable_hermitianMatrixOfCoordinates d)
    (measurable_pi_iff.2 fun k => measurable_pi_apply _),
    hermitianGUECoordinateMeasure_map_comp_equivFin,
    gueMeasure_eq_map_hermitianMatrixOfCoordinates]

/-- `ℝ`-parameter form of `gueMeasure_eq_map_hermitianGUECoordinateMeasure`: for `t: ℝ`,
`0 ≤ t`, `GUE_d(t.toNNReal)` is the image of `hermitianGUECoordinateMeasure d t ht`.
(For
`t: ℝ≥0` and `ht: 0 ≤ (t: ℝ)` the measure `hermitianGUECoordinateMeasure d t ht`
is definitionally the one of the main statement, by proof irrelevance.)
-/
theorem gueMeasure_toNNReal_eq_map_hermitianGUECoordinateMeasure (d : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    gueMeasure (Fin d) t.toNNReal = (hermitianGUECoordinateMeasure d t ht).map
      (fun x => (hermitianOfFinCoordinates d x).1) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℝ≥0, (s : ℝ) = t := ⟨t.toNNReal, Real.coe_toNNReal t ht⟩
  rw [Real.toNNReal_coe]
  exact gueMeasure_eq_map_hermitianGUECoordinateMeasure d s

/-- **Lebesgue density of `GUE_d(t)`**, `0 < t`:
`GUE_d(t)` is the image under `hermitianOfFinCoordinates` of Lebesgue measure on the real
coordinate space `HermitianCoordinateSpace d` weighted by the paper density
`hermitianGUEDensity d t G = Z_d(t)⁻¹ exp(-Tr(G²)/(2t))`, `Z_d(t) = gueNormalizer d t`
(`hermitianGUECoordinateMeasure_eq_withDensity`).
-/
theorem gueMeasure_eq_map_withDensity (d : ℕ) {t : ℝ≥0} (ht : 0 < t) :
    gueMeasure (Fin d) t =
      (volume.withDensity fun x : HermitianCoordinateSpace d =>
        hermitianGUEDensity d t (hermitianGUEBlock d x)).map
          (fun x => (hermitianOfFinCoordinates d x).1) := by
  rw [gueMeasure_eq_map_hermitianGUECoordinateMeasure,
    CoareaNative.BlockBand.hermitianGUECoordinateMeasure_eq_withDensity d
      (t := (t : ℝ)) (NNReal.coe_pos.2 ht)]

/-- `lintegral` form of the GUE density, `0 < t`:
for measurable `f ≥ 0` on matrices,
`∫⁻ f dGUE_d(t) = ∫⁻_{coords} Z_d(t)⁻¹ e^{-Tr(G_x²)/(2t)} f(G_x) dx`, `G_x` the reconstruction of the coordinates `x`.
-/
theorem lintegral_gueMeasure (d : ℕ) {t : ℝ≥0} (ht : 0 < t)
    {f : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ G, f G ∂gueMeasure (Fin d) t =
      ∫⁻ x : HermitianCoordinateSpace d,
        hermitianGUEDensity d t (hermitianGUEBlock d x) *
          f (hermitianOfFinCoordinates d x).1 := by
  rw [gueMeasure_eq_map_withDensity d ht,
    lintegral_map hf (measurable_hermitianOfFinCoordinates_val d),
    lintegral_withDensity_eq_lintegral_mul _
      (CoareaNative.BlockBand.measurable_hermitianGUEDensity_comp_block d t)
      (g := fun x => f (hermitianOfFinCoordinates d x).1)
      (hf.comp (measurable_hermitianOfFinCoordinates_val d))]
  rfl

/-- Bochner-integral form of the GUE density,
`0 < t`, for any `f` that is a.e. strongly measurable for `GUE_d(t)`. -/
theorem integral_gueMeasure (d : ℕ) {t : ℝ≥0} (ht : 0 < t) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Matrix (Fin d) (Fin d) ℂ → E}
    (hf : AEStronglyMeasurable f (gueMeasure (Fin d) t)) :
    ∫ G, f G ∂gueMeasure (Fin d) t =
      ∫ x : HermitianCoordinateSpace d,
        (hermitianGUEDensity d t (hermitianGUEBlock d x)).toReal •
          f (hermitianOfFinCoordinates d x).1 := by
  rw [gueMeasure_eq_map_withDensity d ht] at hf ⊢
  rw [integral_map (measurable_hermitianOfFinCoordinates_val d).aemeasurable hf,
    integral_withDensity_eq_integral_toReal_smul
      (CoareaNative.BlockBand.measurable_hermitianGUEDensity_comp_block d t)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]

/-!
## Reindexing
-/

/-- The flat circular increment law is invariant under reindexing by `e : ι ≃ κ`. -/
theorem commonCircularIncrementLaw_map_comp_equiv {κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) :
    (commonCircularIncrementLaw ι 1).map (fun X => X ∘ (e.prodCongr e).symm) =
      commonCircularIncrementLaw κ 1 := by
  set E : RealIndex ι ≃ RealIndex κ := (e.prodCongr e).prodCongr (Equiv.refl (Fin 2))
  have hE : Measurable (fun r : RealIndex ι → ℝ => r ∘ E.symm) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hX : Measurable (fun X : ι × ι → ℂ => X ∘ (e.prodCongr e).symm) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hfun : (fun X : ι × ι → ℂ => X ∘ (e.prodCongr e).symm) ∘ circularBrownianCoordinates =
      circularBrownianCoordinates ∘ (fun r : RealIndex ι → ℝ => r ∘ E.symm) := by
    funext r u
    rfl
  have hpi : (Measure.pi fun _ : RealIndex ι => gaussianReal 0 (1 : ℝ≥0)).map
      (fun r => r ∘ E.symm) = Measure.pi fun _ : RealIndex κ => gaussianReal 0 (1 : ℝ≥0) :=
    (measurePreserving_arrowCongr' (fun _ => gaussianReal 0 (1 : ℝ≥0))
      (fun _ => gaussianReal 0 (1 : ℝ≥0)) E (MeasurableEquiv.refl ℝ)
      fun _ => MeasurePreserving.id _).map_eq
  unfold commonCircularIncrementLaw
  rw [Measure.map_map hX measurable_circularBrownianCoordinates, hfun,
    ← Measure.map_map measurable_circularBrownianCoordinates hE, hpi]

/-- **Reindexing invariance of `GUE_ι(t)`**: for an
equivalence `e : ι ≃ κ` of finite types, `(gueMeasure ι t).map (Matrix.reindex e e) =
gueMeasure κ t`. -/
theorem gueMeasure_map_reindex {κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (t : ℝ≥0) :
    (gueMeasure ι t).map (Matrix.reindex e e) = gueMeasure κ t := by
  have hR : Measurable (Matrix.reindex e e : Matrix ι ι ℂ → Matrix κ κ ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hX : Measurable (fun X : ι × ι → ℂ => X ∘ (e.prodCongr e).symm) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hcomp : (Matrix.reindex e e : Matrix ι ι ℂ → Matrix κ κ ℂ) ∘ gueSample t =
      gueSample t ∘ (fun X : ι × ι → ℂ => X ∘ (e.prodCongr e).symm) := by
    funext X
    ext a b
    rfl
  unfold gueMeasure
  rw [Measure.map_map hR (measurable_gueSample t), hcomp,
    ← Measure.map_map (measurable_gueSample t) hX, commonCircularIncrementLaw_map_comp_equiv]

end BlockBand.Coarea.GUELaw
