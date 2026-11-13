module

public import BlockBand.Critical.GlobalSource.Bridge
public import BlockBand.Counting.ComplexGaussianWick

/-!
# Global Gaussian source: tightness of `𝒦_W`

The finite-width matrices `𝒦_W = (ζ_a^* G_lead ζ_c)_{a,c}` are tight by the extended source
moments. This file proves the hypothesis `htight` of the reduction
`globalGaussianSource_of_sampling` from `ComplexSourceLawContract.extendedSourceMoments`.

* Circular Gaussian toolkit: `circularVectorLaw_eq_map_circularVector`,
  `pi_circularVectorLaw_eq_map` (the probe law is the product law of `BlockBand.Counting`),
  `integral_norm_sq_complexQuadraticForm` (`E|gᴴAg|² = |Tr A|² + ‖A‖²_HS`).
* `globalProbeMatrix_eq_quadraticForm`, `trace_probePairMatrix`, `hs_probePairMatrix_le`:
  `𝒦_{ac}` is a quadratic form in the joint probe vector; trace and entrywise domination by
  `A_{q̃}`, `q̃ = Σ_b q_b`.
* `lintegral_norm_sq_matrixCoord_le`: `E‖𝒦_W‖² ≤ Σ_a E M₂(q_a) + J² E M₂(q̃)` at every width.
* `isTightMeasureSet_globalProbeMatrixLaw`: tightness of the laws of `𝒦_W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open BlockBand.Counting (complexQuadraticForm circularVector)
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ComplexConjugate NNReal Matrix

/-- The coordinate map `z ↦ (z_i.1 + i z_i.2)_i` of `Counting.circularVector` is Borel. -/
theorem measurable_circularVector (ι : Type*) :
    Measurable (BlockBand.Counting.circularVector (ι := ι)) := by
  refine Measurable.of_eval fun i => ?_
  unfold BlockBand.Counting.circularVector BlockBand.Counting.circularGaussianCoordinate
  fun_prop

/-- **The two circular Gaussian laws agree.** `CoareaPalm.circularVectorLaw ι` (image of i.i.d.
`N(0, 1/2)` coordinates indexed by `ι × Fin 2`) is the image under `Counting.circularVector` of the
product law `Counting.circularVectorLaw ι` (i.i.d. `N(0,1/2) ⊗ N(0,1/2)` pairs indexed by `ι`). This
transfers the Wick identities for `Counting.circularVectorLaw` to the probe law. -/
theorem circularVectorLaw_eq_map_circularVector (ι : Type*) [Fintype ι] :
    circularVectorLaw ι =
      (BlockBand.Counting.circularVectorLaw ι).map BlockBand.Counting.circularVector := by
  unfold circularVectorLaw BlockBand.Counting.circularVectorLaw
  have h1 : (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1/2 : ℝ≥0)).map
      (MeasurableEquiv.curry ι (Fin 2) ℝ) =
      Measure.pi fun _ : ι => Measure.pi fun _ : Fin 2 => gaussianReal 0 (1/2 : ℝ≥0) := by
    have := Measure.infinitePi_map_curry (fun (_ : ι) (_ : Fin 2) => gaussianReal 0 (1/2 : ℝ≥0))
    simpa [Measure.infinitePi_eq_pi] using this
  have h2 : (Measure.pi fun _ : ι => Measure.pi fun _ : Fin 2 => gaussianReal 0 (1/2 : ℝ≥0)).map
      (fun r i => MeasurableEquiv.finTwoArrow (r i)) =
      Measure.pi fun _ : ι => BlockBand.Counting.standardCircularGaussian :=
    (measurePreserving_pi _ _ fun _ => measurePreserving_finTwoArrow _).map_eq
  have hm2 : Measurable (fun (r : ι → Fin 2 → ℝ) i => MeasurableEquiv.finTwoArrow (r i)) :=
    Measurable.of_eval fun i => (MeasurableEquiv.measurable _).comp (measurable_pi_apply i)
  rw [← h2, ← h1, Measure.map_map (measurable_circularVector ι) hm2,
    Measure.map_map ((measurable_circularVector ι).comp hm2) (MeasurableEquiv.measurable _)]
  congr 1
  funext r a
  simp [BlockBand.Counting.circularVector, BlockBand.Counting.circularGaussianCoordinate,
    MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo]
  ring

/-- **Independent circular vectors form one circular vector.** `κ` i.i.d. copies of
`CoareaPalm.circularVectorLaw ι` (the probe law of `globalProbeLaw`, one vector per profile) are
the image of the single product law `Counting.circularVectorLaw (κ × ι)` under currying. -/
theorem pi_circularVectorLaw_eq_map (κ ι : Type*) [Fintype κ] [Fintype ι] :
    Measure.pi (fun _ : κ => circularVectorLaw ι) =
      (BlockBand.Counting.circularVectorLaw (κ × ι)).map
        (fun z a i => circularVector z (a, i)) := by
  simp_rw [circularVectorLaw_eq_map_circularVector]
  rw [← Measure.pi_map_pi (fun _ => (measurable_circularVector ι).aemeasurable)]
  unfold BlockBand.Counting.circularVectorLaw
  have h1 := Measure.infinitePi_map_curry
    (fun (_ : κ) (_ : ι) => BlockBand.Counting.standardCircularGaussian)
  simp only [Measure.infinitePi_eq_pi] at h1
  rw [← h1, Measure.map_map (by
      exact Measurable.of_eval fun a => (measurable_circularVector ι).comp
        (measurable_pi_apply a)) (MeasurableEquiv.measurable _)]
  rfl

/-- `conj(gᴴ A g) = gᴴ Aᴴ g` for every complex matrix `A` and vector `g`. -/
theorem conj_complexQuadraticForm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (g : ι → ℂ) :
    (starRingEnd ℂ) (complexQuadraticForm A g) = complexQuadraticForm Aᴴ g := by
  unfold complexQuadraticForm
  simp only [map_sum, map_mul, Complex.conj_conj, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

/-- **Second moment of a circular quadratic form**: for `g ~ CN(0, I)` (`Counting.circularVectorLaw`)
and every deterministic complex `A`, `E|gᴴAg|² = |Tr A|² + ‖A‖²_HS` (Wick:
`E[(gᴴAg)(gᴴAᴴg)] = Tr A · Tr Aᴴ + Tr(AAᴴ)`). No Hermiticity is assumed. -/
theorem integral_norm_sq_complexQuadraticForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    ∫ z, ‖complexQuadraticForm A (circularVector z)‖ ^ 2
        ∂BlockBand.Counting.circularVectorLaw ι =
      ‖Matrix.trace A‖ ^ 2 + ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have hpt : ∀ z : ι → ℝ × ℝ, (‖complexQuadraticForm A (circularVector z)‖ ^ 2 : ℝ) =
      (complexQuadraticForm A (circularVector z) *
        complexQuadraticForm Aᴴ (circularVector z)).re := by
    intro z
    rw [← conj_complexQuadraticForm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_re]
  simp_rw [hpt]
  have hre : ∫ z, (complexQuadraticForm A (circularVector z) *
        complexQuadraticForm Aᴴ (circularVector z)).re
        ∂BlockBand.Counting.circularVectorLaw ι =
      (∫ z, complexQuadraticForm A (circularVector z) *
        complexQuadraticForm Aᴴ (circularVector z)
        ∂BlockBand.Counting.circularVectorLaw ι).re := by
    simpa using integral_re (BlockBand.Counting.integrable_actualComplexQuadratic_mul A Aᴴ)
  rw [hre, BlockBand.Counting.integral_actualComplexQuadratic_mul_eq_trace]
  rw [Matrix.trace_conjTranspose, Complex.add_re]
  congr 1
  · rw [show star (Matrix.trace A) = (starRingEnd ℂ) (Matrix.trace A) from rfl,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show star (A i j) = (starRingEnd ℂ) (A i j) from rfl, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- Diagonal weight `W⁻¹ √q(j/n)` of the probe `ζ = W⁻¹ Q^{1/2} g` at the path site `x`. -/
def probeWeight (W n : ℕ) (Q : C(BlockBand.Torus, ℝ)) (x : PathSite W n) : ℂ :=
  (((W : ℝ)⁻¹ * Real.sqrt (pathProfileValue n Q x.1) : ℝ) : ℂ)

/-- The coefficient matrix of `𝒦_{ac}` as a quadratic form in the joint vector `(g_{a'})_{a'}` of all
`J` probes: the block `(a, c)` carries `W⁻¹√q_a · G_lead · W⁻¹√q_c`, all other blocks vanish. -/
def probePairMatrix (b E : ℝ) (W n : ℕ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ))
    (ω : GrowthPath W) (a c : Fin J) :
    Matrix (Fin J × PathSite W n) (Fin J × PathSite W n) ℂ :=
  fun p p' => if p.1 = a ∧ p'.1 = c then
    probeWeight W n (Q a) p.2 * leadInverse b E W n ω p.2 p'.2 * probeWeight W n (Q c) p'.2
    else 0

/-- `𝒦_{ac} = ζ_a^* G_lead ζ_c` is the circular quadratic form of `probePairMatrix a c`
in the joint probe vector, when the probes are read off the joint product sample. -/
theorem globalProbeMatrix_eq_quadraticForm (b E : ℝ) (W n : ℕ) {J : ℕ}
    (Q : Fin J → C(BlockBand.Torus, ℝ)) (ω : GrowthPath W)
    (z : Fin J × PathSite W n → ℝ × ℝ) (a c : Fin J) :
    globalProbeMatrix b E W n Q (ω, fun a' x => circularVector z (a', x)) a c =
      complexQuadraticForm (probePairMatrix b E W n Q ω a c) (circularVector z) := by
  classical
  unfold globalProbeMatrix complexQuadraticForm probePairMatrix
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, ite_and, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_const_zero, Finset.sum_ite_irrel, Finset.mem_univ, ite_true]
  simp only [dotProduct, Matrix.mulVec, globalProbeVector, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun y1 _ => ?_
  rw [Pi.star_apply]
  simp only [probeWeight, globalProbeVector, star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

/-- Entries of the extended source matrix `A_q = W⁻² Q^{1/2} G Q^{1/2}`. -/
theorem extendedSourceMatrix_apply (b E : ℝ) (W n : ℕ) (q : Fin n → ℝ) (ω : GrowthPath W)
    (x y : Fin n × Fin W) :
    extendedSourceMatrix b E W n q ω x y =
      (((W : ℝ)⁻¹ * Real.sqrt (q x.1) : ℝ) : ℂ) * (fullInverse b E W n ω).toBlocks₁₁ x y *
        (((W : ℝ)⁻¹ * Real.sqrt (q y.1) : ℝ) : ℂ) := by
  unfold extendedSourceMatrix
  rw [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
  push_cast
  ring

/-- The diagonal block `(a, a)` of `probePairMatrix` is the extended source matrix `A_{q_a}`. -/
theorem probePairMatrix_self_apply (b E : ℝ) (W n : ℕ) {J : ℕ}
    (Q : Fin J → C(BlockBand.Torus, ℝ)) (ω : GrowthPath W) (a : Fin J) (x y : PathSite W n) :
    probePairMatrix b E W n Q ω a a (a, x) (a, y) =
      extendedSourceMatrix b E W (probePathLength n) (pathProfileValue n (Q a)) ω x y := by
  simp [probePairMatrix, extendedSourceMatrix_apply, probeWeight, leadInverse]

/-- `Tr(probePairMatrix a c) = δ_{ac} Tr A_{q_a}`. -/
theorem trace_probePairMatrix (b E : ℝ) (W n : ℕ) {J : ℕ}
    (Q : Fin J → C(BlockBand.Torus, ℝ)) (ω : GrowthPath W) (a c : Fin J) :
    Matrix.trace (probePairMatrix b E W n Q ω a c) =
      if a = c then Matrix.trace (extendedSourceMatrix b E W (probePathLength n)
        (pathProfileValue n (Q a)) ω) else 0 := by
  classical
  by_cases h : a = c
  · subst h
    simp only [eq_self, ite_true]
    unfold Matrix.trace
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · exact Finset.sum_congr rfl fun x _ => probePairMatrix_self_apply b E W n Q ω a x x
    · intro a' _ ha'
      exact Finset.sum_eq_zero fun x _ => by simp [probePairMatrix, ha']
    · simp
  · simp only [h, ite_false, Matrix.trace, Matrix.diag]
    refine Finset.sum_eq_zero fun p _ => ?_
    simp only [probePairMatrix]
    split_ifs with h'
    · exact absurd (h'.1.symm.trans h'.2) h
    · rfl

/-- The pointwise total profile `q̃ = Σ_b q_b` on the path (entrywise domination). -/
def totalProfileValue (n : ℕ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ))
    (i : Fin (probePathLength n)) : ℝ :=
  ∑ b, pathProfileValue n (Q b) i

/-- `W⁻¹√q_a ≤ W⁻¹√q̃` for nonnegative profiles. -/
theorem norm_probeWeight_le (W n : ℕ) {J : ℕ} {Q : Fin J → C(BlockBand.Torus, ℝ)}
    (hQ : ∀ a x, 0 ≤ Q a x) (a : Fin J) (x : PathSite W n) :
    ‖probeWeight W n (Q a) x‖ ≤ (W : ℝ)⁻¹ * Real.sqrt (totalProfileValue n Q x.1) := by
  unfold probeWeight
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  exact Finset.single_le_sum (f := fun b => pathProfileValue n (Q b) x.1)
    (fun b _ => hQ b _) (Finset.mem_univ a)

/-- **Entrywise domination**: `‖probePairMatrix a c‖²_HS ≤ ‖A_{q̃}‖²_HS`, `q̃ = Σ_b q_b`, from
`|√q_a G √q_c| ≤ |√q̃ G √q̃|` entrywise. -/
theorem hs_probePairMatrix_le (b E : ℝ) (W n : ℕ) {J : ℕ} {Q : Fin J → C(BlockBand.Torus, ℝ)}
    (hQ : ∀ a x, 0 ≤ Q a x) (ω : GrowthPath W) (a c : Fin J) :
    ∑ p, ∑ p', ‖probePairMatrix b E W n Q ω a c p p'‖ ^ 2 ≤
      ∑ x, ∑ y, ‖extendedSourceMatrix b E W (probePathLength n) (totalProfileValue n Q) ω x y‖ ^ 2 := by
  classical
  have hzero : ∀ p p', ¬ (p.1 = a ∧ p'.1 = c) → probePairMatrix b E W n Q ω a c p p' = 0 :=
    fun p p' h => by simp only [probePairMatrix, h, ite_false]
  have hcollapse : ∑ p, ∑ p', ‖probePairMatrix b E W n Q ω a c p p'‖ ^ 2 =
      ∑ x, ∑ y, ‖probePairMatrix b E W n Q ω a c (a, x) (c, y)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
      · intro c' _ hc'
        exact Finset.sum_eq_zero fun y _ => by
          rw [hzero _ _ (fun h => hc' h.2)]; simp
      · simp
    · intro a' _ ha'
      exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun p' _ => by
        rw [hzero _ _ (fun h => ha' h.1)]; simp
    · simp
  rw [hcollapse]
  gcongr with x _ y _
  have hA : probePairMatrix b E W n Q ω a c (a, x) (c, y) =
      probeWeight W n (Q a) x * leadInverse b E W n ω x y * probeWeight W n (Q c) y := by
    simp [probePairMatrix]
  rw [hA, extendedSourceMatrix_apply, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have h1 := norm_probeWeight_le W n hQ a x
  have h2 := norm_probeWeight_le W n hQ c y
  unfold leadInverse at *
  gcongr

/-- `|gᴴAg|² = Re((gᴴAg)(gᴴAᴴg))`. -/
theorem norm_sq_complexQuadraticForm_eq_re {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (g : ι → ℂ) :
    ‖complexQuadraticForm A g‖ ^ 2 = (complexQuadraticForm A g * complexQuadraticForm Aᴴ g).re := by
  rw [← conj_complexQuadraticForm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- `|gᴴAg|²` is integrable under the circular product law. -/
theorem integrable_norm_sq_complexQuadraticForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    Integrable (fun z => ‖complexQuadraticForm A (circularVector z)‖ ^ 2)
      (BlockBand.Counting.circularVectorLaw ι) := by
  simp_rw [norm_sq_complexQuadraticForm_eq_re]
  exact (BlockBand.Counting.integrable_actualComplexQuadratic_mul A Aᴴ).re

/-- **Conditional second moment of an entry of `𝒦_W`** given the path `ω`: under the i.i.d.
circular probes of `globalProbeLaw`, `E[|𝒦_{ac}|² | ω] = |Tr P_{ac}|² + ‖P_{ac}‖²_HS` with
`P_{ac} = probePairMatrix a c` (exact; `E gg* = I`, zero pseudo-covariance). -/
theorem lintegral_norm_sq_globalProbeMatrix_apply (b E : ℝ) (W n : ℕ) {J : ℕ}
    (Q : Fin J → C(BlockBand.Torus, ℝ)) (ω : GrowthPath W) (a c : Fin J) :
    ∫⁻ g, ENNReal.ofReal (‖globalProbeMatrix b E W n Q (ω, g) a c‖ ^ 2)
        ∂Measure.pi (fun _ : Fin J => circularVectorLaw (PathSite W n)) =
      ENNReal.ofReal (‖Matrix.trace (probePairMatrix b E W n Q ω a c)‖ ^ 2 +
        ∑ p, ∑ p', ‖probePairMatrix b E W n Q ω a c p p'‖ ^ 2) := by
  classical
  have hmeas : Measurable fun g : Fin J → PathSite W n → ℂ =>
      ENNReal.ofReal (‖globalProbeMatrix b E W n Q (ω, g) a c‖ ^ 2) := by
    have h := (measurable_globalProbeMatrix b E W n Q).comp (measurable_prodMk_left (x := ω))
    have h' : Measurable fun g : Fin J → PathSite W n → ℂ =>
        globalProbeMatrix b E W n Q (ω, g) a c :=
      (measurable_pi_apply c).comp ((measurable_pi_apply a).comp h)
    exact ENNReal.measurable_ofReal.comp (h'.norm.pow_const 2)
  rw [pi_circularVectorLaw_eq_map, lintegral_map hmeas (by
    exact Measurable.of_eval fun a => Measurable.of_eval fun i =>
      (measurable_pi_apply (a, i)).comp (measurable_circularVector _))]
  simp_rw [globalProbeMatrix_eq_quadraticForm]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_complexQuadraticForm _)
    (Filter.Eventually.of_forall fun _ => by positivity), integral_norm_sq_complexQuadraticForm]

/-- `|Tr A_q|² + ‖A_q‖²_HS` for the extended source matrix (the `p = 2` quantity of the extended
source moments). -/
def sourceMoment2 (b E : ℝ) (W n : ℕ) (q : Fin n → ℝ) (ω : GrowthPath W) : ℝ :=
  ‖Matrix.trace (extendedSourceMatrix b E W n q ω)‖ ^ 2 +
    ∑ x, ∑ y, ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2

/-- `sourceMoment2` is nonnegative. -/
theorem sourceMoment2_nonneg (b E : ℝ) (W n : ℕ) (q : Fin n → ℝ) (ω : GrowthPath W) :
    0 ≤ sourceMoment2 b E W n q ω := by
  unfold sourceMoment2; positivity

/-- `A_q` is a Borel function of the grown path. -/
theorem measurable_extendedSourceMatrix (b E : ℝ) (W n : ℕ) (q : Fin n → ℝ) :
    Measurable (extendedSourceMatrix b E W n q) := by
  have h := measurable_matrix_inv.comp
    (measurable_fullPathMatrix b E W n)
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp_rw [extendedSourceMatrix_apply]
  refine (measurable_const.mul ?_).mul measurable_const
  exact (measurable_pi_apply (Sum.inl y)).comp ((measurable_pi_apply (Sum.inl x)).comp h)

/-- `sourceMoment2` is a Borel function of the grown path. -/
theorem measurable_sourceMoment2 (b E : ℝ) (W n : ℕ) (q : Fin n → ℝ) :
    Measurable (sourceMoment2 b E W n q) := by
  have h := measurable_extendedSourceMatrix b E W n q
  unfold sourceMoment2
  refine ((continuous_id.matrix_trace.norm.pow 2).measurable.comp h).add ?_
  refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_
  exact ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp h)).norm.pow_const 2

/-- Pointwise in the path: `Σ_{a,c} (|Tr P_{ac}|² + ‖P_{ac}‖²_HS) ≤ Σ_a M₂(q_a) + J² M₂(q̃)`, where
`M₂ = sourceMoment2`. -/
theorem sum_probePair_le (b E : ℝ) (W n : ℕ) {J : ℕ} {Q : Fin J → C(BlockBand.Torus, ℝ)}
    (hQ : ∀ a x, 0 ≤ Q a x) (ω : GrowthPath W) :
    ∑ a, ∑ c, (‖Matrix.trace (probePairMatrix b E W n Q ω a c)‖ ^ 2 +
        ∑ p, ∑ p', ‖probePairMatrix b E W n Q ω a c p p'‖ ^ 2) ≤
      ∑ a, sourceMoment2 b E W (probePathLength n) (pathProfileValue n (Q a)) ω +
        (J : ℝ) ^ 2 * sourceMoment2 b E W (probePathLength n) (totalProfileValue n Q) ω := by
  classical
  have htr : ∀ a, ∑ c, ‖Matrix.trace (probePairMatrix b E W n Q ω a c)‖ ^ 2 =
      ‖Matrix.trace (extendedSourceMatrix b E W (probePathLength n)
        (pathProfileValue n (Q a)) ω)‖ ^ 2 := by
    intro a
    simp_rw [trace_probePairMatrix]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  have hhs : ∑ a, ∑ c, ∑ p, ∑ p', ‖probePairMatrix b E W n Q ω a c p p'‖ ^ 2 ≤
      ∑ _a : Fin J, ∑ _c : Fin J, ∑ x, ∑ y,
        ‖extendedSourceMatrix b E W (probePathLength n) (totalProfileValue n Q) ω x y‖ ^ 2 :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => hs_probePairMatrix_le b E W n hQ ω a c
  simp only [Finset.sum_add_distrib, htr]
  have hconst : ∑ _a : Fin J, ∑ _c : Fin J, ∑ x, ∑ y,
        ‖extendedSourceMatrix b E W (probePathLength n) (totalProfileValue n Q) ω x y‖ ^ 2 =
      (J : ℝ) ^ 2 * ∑ x, ∑ y,
        ‖extendedSourceMatrix b E W (probePathLength n) (totalProfileValue n Q) ω x y‖ ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hA : ∀ a, ‖Matrix.trace (extendedSourceMatrix b E W (probePathLength n)
        (pathProfileValue n (Q a)) ω)‖ ^ 2 ≤
      sourceMoment2 b E W (probePathLength n) (pathProfileValue n (Q a)) ω := by
    intro a; unfold sourceMoment2; have : (0:ℝ) ≤ ∑ x, ∑ y, ‖extendedSourceMatrix b E W
      (probePathLength n) (pathProfileValue n (Q a)) ω x y‖ ^ 2 := by positivity
    linarith
  have hB : (J : ℝ) ^ 2 * ∑ x, ∑ y,
        ‖extendedSourceMatrix b E W (probePathLength n) (totalProfileValue n Q) ω x y‖ ^ 2 ≤
      (J : ℝ) ^ 2 * sourceMoment2 b E W (probePathLength n) (totalProfileValue n Q) ω := by
    gcongr; unfold sourceMoment2; have := norm_nonneg (Matrix.trace (extendedSourceMatrix b E W
      (probePathLength n) (totalProfileValue n Q) ω)); nlinarith
  calc _ ≤ ∑ a, ‖Matrix.trace (extendedSourceMatrix b E W (probePathLength n)
        (pathProfileValue n (Q a)) ω)‖ ^ 2 + (J : ℝ) ^ 2 * ∑ x, ∑ y,
        ‖extendedSourceMatrix b E W (probePathLength n) (totalProfileValue n Q) ω x y‖ ^ 2 := by
        rw [← hconst]; gcongr
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun a _ => hA a) hB

/-- Coordinates of `matrixCoord`. -/
theorem matrixCoord_apply {J : ℕ} (K : Matrix (Fin J) (Fin J) ℂ) (p : Fin J × Fin J × Fin 2) :
    matrixCoord J K p =
      if p.2.2 = 0 then (K p.1 p.2.1).re else (K p.1 p.2.1).im := rfl

/-- `‖matrixCoord K‖² = Σ_{a,c} |K_{ac}|²` (Euclidean norm of the real coordinates). -/
theorem norm_sq_matrixCoord {J : ℕ} (K : Matrix (Fin J) (Fin J) ℂ) :
    ‖matrixCoord J K‖ ^ 2 = ∑ a, ∑ c, ‖K a c‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [matrixCoord_apply, matrixCoord_apply]
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **Second moment of `𝒦_W`** at fixed width `W` and ring size `n`: under `globalProbeLaw W n J b`,
`E‖𝒦_W‖² ≤ Σ_a E M₂(q_a) + J² E M₂(q̃)`, where `M₂ = |Tr A_q|² + ‖A_q‖²_HS` (`sourceMoment2`) on the
remaining path of `n - 3` blocks and the expectations on the right are under the path law
`growthPathLaw W b`. Exact Gaussian identities plus entrywise domination; no limit and no hypothesis
is used. -/
theorem lintegral_norm_sq_matrixCoord_le (b E : ℝ) (W n : ℕ) {J : ℕ}
    {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x) :
    ∫⁻ x, ENNReal.ofReal (‖matrixCoord J
        (globalProbeMatrix b E W n Q x)‖ ^ 2) ∂globalProbeLaw W n J b ≤
      ∑ a, ∫⁻ ω, ENNReal.ofReal (sourceMoment2 b E W (probePathLength n)
          (pathProfileValue n (Q a)) ω) ∂growthPathLaw W b +
        ENNReal.ofReal ((J : ℝ) ^ 2) * ∫⁻ ω, ENNReal.ofReal (sourceMoment2 b E W
          (probePathLength n) (totalProfileValue n Q) ω) ∂growthPathLaw W b := by
  classical
  have hK := measurable_globalProbeMatrix b E W n Q
  have hent : ∀ a c, Measurable fun x : GlobalProbeSample W n J =>
      ENNReal.ofReal (‖globalProbeMatrix b E W n Q x a c‖ ^ 2) := fun a c =>
    ENNReal.measurable_ofReal.comp
      (((measurable_pi_apply c).comp ((measurable_pi_apply a).comp hK)).norm.pow_const 2)
  have hinner : ∀ ω : GrowthPath W,
      ∫⁻ g, ENNReal.ofReal (‖matrixCoord J
          (globalProbeMatrix b E W n Q (ω, g))‖ ^ 2)
        ∂Measure.pi (fun _ : Fin J => circularVectorLaw (PathSite W n)) =
      ENNReal.ofReal (∑ a, ∑ c, (‖Matrix.trace (probePairMatrix b E W n Q ω a c)‖ ^ 2 +
        ∑ p, ∑ p', ‖probePairMatrix b E W n Q ω a c p p'‖ ^ 2)) := by
    intro ω
    have hent' : ∀ a c, Measurable fun g : Fin J → PathSite W n → ℂ =>
        ENNReal.ofReal (‖globalProbeMatrix b E W n Q (ω, g) a c‖ ^ 2) := fun a c =>
      (hent a c).comp measurable_prodMk_left
    simp_rw [norm_sq_matrixCoord]
    have hnn : ∀ g : Fin J → PathSite W n → ℂ, ∀ a ∈ Finset.univ,
        0 ≤ ∑ c, ‖globalProbeMatrix b E W n Q (ω, g) a c‖ ^ 2 := fun g a _ => by positivity
    simp_rw [ENNReal.ofReal_sum_of_nonneg (hnn _),
      ENNReal.ofReal_sum_of_nonneg (fun c _ => sq_nonneg (‖globalProbeMatrix b E W n Q _ _ c‖))]
    rw [lintegral_finsetSum _ fun a _ => Finset.measurable_sum _ fun c _ => hent' a c]
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => by positivity]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [lintegral_finsetSum _ fun c _ => hent' a c,
      ENNReal.ofReal_sum_of_nonneg fun c _ => by positivity]
    exact Finset.sum_congr rfl fun c _ => lintegral_norm_sq_globalProbeMatrix_apply b E W n Q ω a c
  have hmeasK : Measurable fun x : GlobalProbeSample W n J =>
      ENNReal.ofReal (‖matrixCoord J
        (globalProbeMatrix b E W n Q x)‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((matrixCoord J).continuous.measurable.comp hK).norm.pow_const 2)
  unfold globalProbeLaw
  rw [lintegral_prod _ hmeasK.aemeasurable]
  simp_rw [hinner]
  have hM := fun q => measurable_sourceMoment2 b E W (probePathLength n) q
  calc _ ≤ ∫⁻ ω, (∑ a, ENNReal.ofReal (sourceMoment2 b E W (probePathLength n)
          (pathProfileValue n (Q a)) ω) + ENNReal.ofReal ((J : ℝ) ^ 2) *
          ENNReal.ofReal (sourceMoment2 b E W (probePathLength n) (totalProfileValue n Q) ω))
        ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_sum_of_nonneg
          (fun a _ => sourceMoment2_nonneg _ _ _ _ _ _),
          ← ENNReal.ofReal_add (Finset.sum_nonneg fun a _ => sourceMoment2_nonneg _ _ _ _ _ _)
            (mul_nonneg (by positivity) (sourceMoment2_nonneg _ _ _ _ _ _))]
        exact ENNReal.ofReal_le_ofReal (sum_probePair_le b E W n hQ ω)
    _ = _ := by
        have hM' : ∀ q, Measurable fun ω => ENNReal.ofReal (sourceMoment2 b E W
            (probePathLength n) q ω) := fun q => ENNReal.measurable_ofReal.comp (hM q)
        rw [lintegral_add_left (Finset.measurable_sum _ fun a _ => hM' _),
          lintegral_finsetSum _ fun a _ => hM' _, lintegral_const_mul _ (hM' _)]

/-- `ComplexSourceLawContract.extendedSourceMoments` at `p = 2`, restated for `sourceMoment2`: for
`0 < b < 1/2`, `κI > 0`, `T`, `qmax`, there are `C`, `W₀` with `E M₂(q) ≤ C` for all `W ≥ W₀`,
`E ∈ bulkInterval κI`, path lengths `n ≤ T W` and profiles `0 ≤ q ≤ qmax` (law `growthPathLaw W b`). -/
theorem exists_lintegral_sourceMoment2_le
    (hCS : BlockBand.Internal.Contracts.TransmissionLaws.ComplexSourceLawContract)
    {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {κI : ℝ} (hκI : 0 < κI) (T qmax : ℝ) :
    ∃ C : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ BlockBand.Internal.Contracts.Layers.bulkInterval κI,
      ∀ n : ℕ, (n : ℝ) ≤ T * W → ∀ q : Fin n → ℝ, (∀ k, 0 ≤ q k ∧ q k ≤ qmax) →
        ∫⁻ ω, ENNReal.ofReal (sourceMoment2 b E W n q ω) ∂growthPathLaw W b ≤ ENNReal.ofReal C := by
  obtain ⟨C, W₀, hC⟩ := hCS.extendedSourceMoments b hb hb' κI hκI T 2 qmax (by norm_num)
  refine ⟨C, W₀, fun W hW E hE n hn q hq => ?_⟩
  refine le_of_eq_of_le (lintegral_congr fun ω => ?_) (hC W hW E hE n hn q hq)
  unfold sourceMoment2
  rw [Real.rpow_two, Real.rpow_two, Real.sq_sqrt (by positivity)]

/-- **Uniform second moment of `𝒦_W` along a critical sequence.** Domain:
`0 < b < 1/2`, `-2 < E < 2`, nonnegative continuous profiles, any critical sequence. There is a
finite `B` with `E‖𝒦_{W_j}‖² ≤ B` (real coordinates, law `globalProbeLaw`) for all large `j`.
From `lintegral_norm_sq_matrixCoord_le` and `extendedSourceMoments` (`p = 2`, `T = τ + 1`,
`qmax = Σ_a ‖q_a‖_∞`, `κI = min(2+E, 2-E)`). -/
theorem exists_eventually_lintegral_norm_sq_le
    (hCS : BlockBand.Internal.Contracts.TransmissionLaws.ComplexSourceLawContract)
    {b E τ : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {J : ℕ}
    {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x)
    (s : BlockBand.CriticalSequence τ) :
    ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ᶠ j in atTop,
      ∫⁻ x, ENNReal.ofReal (‖matrixCoord J (globalProbeMatrix b E (s.W j) (s.n j) Q x)‖ ^ 2)
        ∂globalProbeLaw (s.W j) (s.n j) J b ≤ B := by
  classical
  set κI : ℝ := min (2 + E) (2 - E)
  have hκI : 0 < κI := lt_min (by linarith) (by linarith)
  have hEI : E ∈ BlockBand.Internal.Contracts.Layers.bulkInterval κI := by
    unfold BlockBand.Internal.Contracts.Layers.bulkInterval
    constructor
    · have := min_le_left (2 + E) (2 - E); linarith
    · have := min_le_right (2 + E) (2 - E); linarith
  set qmax : ℝ := ∑ a, ‖Q a‖
  have hq1 : ∀ n a (k : Fin (probePathLength n)),
      0 ≤ pathProfileValue n (Q a) k ∧ pathProfileValue n (Q a) k ≤ qmax := by
    intro n a k
    refine ⟨hQ _ _, ?_⟩
    calc pathProfileValue n (Q a) k ≤ ‖Q a‖ :=
          (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ (Q a).norm_coe_le_norm _)
      _ ≤ qmax := Finset.single_le_sum (f := fun a => ‖Q a‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ a)
  have hq2 : ∀ n (k : Fin (probePathLength n)),
      0 ≤ totalProfileValue n Q k ∧ totalProfileValue n Q k ≤ qmax := by
    intro n k
    refine ⟨Finset.sum_nonneg fun a _ => hQ _ _, Finset.sum_le_sum fun a _ => ?_⟩
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ (Q a).norm_coe_le_norm _)
  obtain ⟨C, W₀, hC⟩ := exists_lintegral_sourceMoment2_le hCS hb hb' hκI (τ + 1) qmax
  set B : ENNReal := ∑ _a : Fin J, ENNReal.ofReal C + ENNReal.ofReal ((J : ℝ) ^ 2) *
    ENNReal.ofReal C
  have hBtop : B ≠ ⊤ := by
    simp only [B]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  -- eventually the moment bound holds
  have hev : ∀ᶠ j in atTop, W₀ ≤ s.W j ∧ (probePathLength (s.n j) : ℝ) ≤ (τ + 1) * s.W j := by
    have h1 := s.width_tendsto.eventually_ge_atTop W₀
    have h2 := s.ratio_tendsto.eventually (gt_mem_nhds (show τ < τ + 1 by linarith))
    filter_upwards [h1, h2] with j hj1 hj2
    refine ⟨hj1, ?_⟩
    have hW : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
    have : (s.n j : ℝ) < (τ + 1) * s.W j := by rwa [div_lt_iff₀ hW] at hj2
    have hp : (probePathLength (s.n j) : ℝ) ≤ s.n j := by
      unfold probePathLength; exact_mod_cast Nat.sub_le _ _
    linarith
  refine ⟨B, hBtop, ?_⟩
  filter_upwards [hev] with j hj
  refine (lintegral_norm_sq_matrixCoord_le b E (s.W j) (s.n j) hQ).trans
    (add_le_add (Finset.sum_le_sum fun a _ => ?_) (mul_le_mul_right ?_ _))
  · exact hC _ hj.1 E hEI _ hj.2 _ (hq1 _ a)
  · exact hC _ hj.1 E hEI _ hj.2 _ (hq2 _)

/-- **Tightness of the laws of `𝒦_W`** along every critical sequence, by the same moments. -/
theorem isTightMeasureSet_globalProbeMatrixLaw
    (hCS : BlockBand.Internal.Contracts.TransmissionLaws.ComplexSourceLawContract)
    {b E τ : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {J : ℕ}
    {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x)
    (s : BlockBand.CriticalSequence τ) :
    IsTightMeasureSet {((globalProbeMatrixLaw b E (s.W j) (s.n j) Q :
      ProbabilityMeasure _) : Measure (Matrix (Fin J) (Fin J) ℂ)) | j} := by
  classical
  set e := matrixCoord J
  obtain ⟨B, hBtop, hB⟩ := exists_eventually_lintegral_norm_sq_le hCS hb hb' hE hE' hQ s
  -- the pushed-forward laws on the Euclidean space
  set μ' : ℕ → Measure (EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) := fun j =>
    (((globalProbeMatrixLaw b E (s.W j) (s.n j) Q).map e :
      ProbabilityMeasure _) : Measure _)
  have hμ'int : ∀ j, ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ' j =
      ∫⁻ x, ENNReal.ofReal (‖e (globalProbeMatrix b E (s.W j) (s.n j) Q x)‖ ^ 2)
        ∂globalProbeLaw (s.W j) (s.n j) J b := by
    intro j
    simp only [μ', ProbabilityMeasure.toMeasure_map]
    change ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(((globalProbeLaw (s.W j) (s.n j) J b).map
      (globalProbeMatrix b E (s.W j) (s.n j) Q)).map e) = _
    rw [lintegral_map (f := fun x => ENNReal.ofReal (‖x‖ ^ 2))
      (ENNReal.measurable_ofReal.comp (continuous_norm.measurable.pow_const 2))
      e.continuous.measurable, lintegral_map (f := fun K => ENNReal.ofReal (‖e K‖ ^ 2))
      (ENNReal.measurable_ofReal.comp
        ((continuous_norm.measurable.pow_const 2).comp e.continuous.measurable))
      (measurable_globalProbeMatrix b E (s.W j) (s.n j) Q)]
  have hbound : ∀ᶠ j in atTop, ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ' j ≤ B := by
    filter_upwards [hB] with j hj
    rw [hμ'int]
    exact hj
  have hmarkov : ∀ r : ℝ, 0 < r → ∀ j, ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ' j ≤ B →
      μ' j {x | r < ‖x‖} ≤ B / ENNReal.ofReal (r ^ 2) := by
    intro r hr j hj
    have hr2 : ENNReal.ofReal (r ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    rw [ENNReal.le_div_iff_mul_le (Or.inl hr2) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    refine le_trans ?_ ((mul_meas_ge_le_lintegral (ENNReal.measurable_ofReal.comp
      (continuous_norm.measurable.pow_const 2)) (ENNReal.ofReal (r ^ 2))).trans hj)
    refine mul_le_mul_right (measure_mono fun x hx => ?_) _
    simp only [Set.mem_ofPred_eq, Function.comp_apply] at hx ⊢
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr.le hx.le 2)
  have hlim : Tendsto (fun r : ℝ => limsup (fun j => μ' j {x | r < ‖x‖}) atTop) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun r : ℝ => B / ENNReal.ofReal (r ^ 2)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_div
        (ENNReal.tendsto_ofReal_atTop.comp (tendsto_pow_atTop (two_ne_zero)))
        (a := B) (Or.inr hBtop)
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hbound] with j hj
    exact hmarkov r hr j hj
  have hμ'prob : ∀ j, IsFiniteMeasure (μ' j) := fun j => inferInstance
  have htight := isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt hlim
  refine (htight.map e.symm.continuous).subset ?_
  rintro _ ⟨j, rfl⟩
  refine ⟨μ' j, ⟨j, rfl⟩, ?_⟩
  simp only [μ']
  rw [← ProbabilityMeasure.toMeasure_map, map_matrixCoord_symm_map]

end BlockBand.Critical.GlobalSource
