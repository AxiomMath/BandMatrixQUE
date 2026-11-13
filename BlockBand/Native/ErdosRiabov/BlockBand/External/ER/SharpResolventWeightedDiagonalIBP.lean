module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpResolventWeightedOffDiagonalIBP

/-!
# Supported diagonal IBP for the resolvent-weighted Dyson test

This module treats the one real diagonal Gaussian coordinate separately from
the circular strict-upper coordinates.  It reconstructs the deleted diagonal
background from the complementary upper-entry tuple, proves the exact product
law and Hermitian support, establishes resolvent-test domination and
integrability, and lifts the one-dimensional Gaussian IBP back to the
Gaussian-ring law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSharpCoordinateIBP

open Matrix MeasureTheory ProbabilityTheory
open ERProductCoordinateAnalysis ERGaussianCoordinate
open ERStrictCoordinateDisintegration ERResolventMomentIBP ERProfile
open ERComplementBackgroundReconstruction ERConcrete ERActualWardBound
open scoped BigOperators NNReal Matrix.Norms.L2Operator

local instance (p : Params) : NeZero p.n := p.nNeZero
local instance (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance (p : Params) : Fintype (UpperPair p) := Fintype.ofFinite _
local instance (p : Params) : DecidableEq (UpperPair p) := Classical.decEq _

/-- The selected upper-triangular coordinate attached to a diagonal site. -/
def diagonalUpperPair (p : Params) (a : Site p.n p.W) : UpperPair p :=
  ⟨(a, a), by simp [siteLE]⟩

@[simp] theorem diagonalUpperPair_val (p : Params) (a : Site p.n p.W) :
    (diagonalUpperPair p a).1 = (a, a) := rfl

/-- Reconstruct the Hermitian zero-diagonal background from all unselected
upper entries. -/
def reconstructDiagonalBackground (p : Params) (a : Site p.n p.W)
    (u : (q : (Finset.univ.erase (diagonalUpperPair p a) :
      Finset (UpperPair p))) → ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  reconstructOffdiagBackground p (diagonalUpperPair p a) u

/-- Diagonal-background reconstruction is measurable entrywise. -/
theorem measurable_reconstructDiagonalBackground
    {p : Params} (a : Site p.n p.W) :
    Measurable (reconstructDiagonalBackground p a) :=
  measurable_reconstructOffdiagBackground (diagonalUpperPair p a)

/-- Deleting the selected diagonal coordinate leaves every other entry
unchanged. -/
theorem diagonalRealBackground_apply_of_ne
    {ι : Type*} [DecidableEq ι] (H : Matrix ι ι ℂ)
    {a i j : ι} (hij : (i, j) ≠ (a, a)) :
    diagonalRealBackground H a i j = H i j := by
  have hia : i ≠ a ∨ j ≠ a := by
    by_contra h
    push Not at h
    exact hij (Prod.ext h.1 h.2)
  rcases hia with hi | hj
  · simp [diagonalRealBackground, diagonalRealDirection, Ne.symm hi]
  · simp [diagonalRealBackground, diagonalRealDirection, Ne.symm hj]

/-- The selected diagonal entry of the removed background is zero. -/
@[simp] theorem diagonalRealBackground_apply_self
    {ι : Type*} [DecidableEq ι] (H : Matrix ι ι ℂ) (a : ι) :
    diagonalRealBackground H a a a = H a a - (H a a).re := by
  simp [diagonalRealBackground, diagonalRealDirection]

/-- For a Hermitian matrix the complement reconstruction is exactly the
matrix with its selected real diagonal coordinate removed. -/
theorem reconstruct_complement_eq_diagonalRealBackground
    {p : Params} (H : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hH : H.IsHermitian) (a : Site p.n p.W) :
    reconstructDiagonalBackground p a
      (fun q : (Finset.univ.erase (diagonalUpperPair p a) :
        Finset (UpperPair p)) => H q.1.1.1 q.1.1.2) =
      diagonalRealBackground H a := by
  ext i j
  by_cases hij : siteLE p i j
  · have hup : (upperPairFor p i j).1 = (i, j) :=
      upperPairFor_of_siteLE hij
    by_cases hr : upperPairFor p i j = diagonalUpperPair p a
    · have hp : (i, j) = (a, a) := by
        simpa [hup] using congrArg Subtype.val hr
      have hi : i = a := congrArg Prod.fst hp
      have hj : j = a := congrArg Prod.snd hp
      subst i; subst j
      simp [reconstructDiagonalBackground, reconstructOffdiagBackground, hr,
        diagonalRealBackground_apply_self,
        hermitian_diag_eq_re H hH]
    · have hpair : (i, j) ≠ (a, a) := by
        intro h
        apply hr
        apply Subtype.ext
        exact hup.trans h
      rw [diagonalRealBackground_apply_of_ne H hpair]
      by_cases heq : i = j
      · subst j
        simpa [reconstructDiagonalBackground, reconstructOffdiagBackground,
          hr, hij, complementValue] using hermitian_diag_eq_re H hH i
      · simp [reconstructDiagonalBackground, reconstructOffdiagBackground,
          hr, hij, heq, complementValue]
  · have hji : siteLE p j i := by
      unfold siteLE at hij ⊢
      omega
    have hup : (upperPairFor p i j).1 = (j, i) :=
      upperPairFor_of_not_siteLE hij
    have hr : upperPairFor p i j ≠ diagonalUpperPair p a := by
      intro h
      have hp : (j, i) = (a, a) := by
        simpa [hup] using congrArg Subtype.val h
      have hj : j = a := congrArg Prod.fst hp
      have hi : i = a := congrArg Prod.snd hp
      subst i; subst j
      exact hij (by simp [siteLE])
    have hpair : (i, j) ≠ (a, a) := by
      intro h
      have hi : i = a := congrArg Prod.fst h
      have hj : j = a := congrArg Prod.snd h
      subst i; subst j
      exact hij (by simp [siteLE])
    rw [diagonalRealBackground_apply_of_ne H hpair]
    simpa [reconstructDiagonalBackground, reconstructOffdiagBackground,
      hr, hij, complementValue] using hH.apply i j

/-- Pointwise reconstruction of the deleted diagonal background. -/
theorem Law.reconstruct_complementTuple_eq_diagonalRealBackground
    {p : Params} (M : Law p) (a : Site p.n p.W) (ω : M.Ω) :
    reconstructDiagonalBackground p a
      (complementTuple (upperEntryFamily M) (diagonalUpperPair p a) ω) =
      diagonalRealBackground (M.H ω) a := by
  exact reconstruct_complement_eq_diagonalRealBackground
    (M.H ω) (M.isHermitian ω) a

/-- The deleted diagonal background is measurable. -/
theorem Law.measurable_diagonalRealBackground
    {p : Params} (M : Law p) (a : Site p.n p.W) :
    Measurable (fun ω => diagonalRealBackground (M.H ω) a) := by
  convert (measurable_reconstructDiagonalBackground a).comp
    (measurable_singletonTuple_complementTuple
      (upperEntryFamily M) (diagonalUpperPair p a)
      (measurable_upperEntryFamily M)).2 using 1
  funext ω
  exact (Law.reconstruct_complementTuple_eq_diagonalRealBackground
    M a ω).symm

/-- The selected real diagonal coordinate is independent of its full
matrix-valued background. -/
theorem Law.diagonalReal_indep_background
    {p : Params} (M : Law p) (a : Site p.n p.W) :
    IndepFun (fun ω => (M.H ω a a).re)
      (fun ω => diagonalRealBackground (M.H ω) a) M.P := by
  have h := (Law.diagonalReal_indep_complement M a
    (diagonalUpperPair p a) rfl).comp measurable_id
      (measurable_reconstructDiagonalBackground a)
  simpa only [id_eq, Function.comp_def,
    Law.reconstruct_complementTuple_eq_diagonalRealBackground M a] using h

/-- The real diagonal coordinate and deleted background have the exact
Gaussian product law. -/
theorem Law.diagonalReal_background_productLaw
    {p : Params} (M : Law p) (a : Site p.n p.W) :
    M.P.map (fun ω => ((M.H ω a a).re,
      diagonalRealBackground (M.H ω) a)) =
      (gaussianReal 0 (varianceNNReal p a a)).prod
        (M.P.map (fun ω => diagonalRealBackground (M.H ω) a)) := by
  have h := IndepFun.map_prod_eq_prod_map_map
    (Complex.measurable_re.comp (M.measurable_entry a a)).aemeasurable
    (Law.measurable_diagonalRealBackground M a).aemeasurable
    (Law.diagonalReal_indep_background M a)
  have h' :
      M.P.map (fun ω => ((M.H ω a a).re,
        diagonalRealBackground (M.H ω) a)) =
        (M.P.map (fun ω => (M.H ω a a).re)).prod
          (M.P.map (fun ω => diagonalRealBackground (M.H ω) a)) := by
    simpa only [Function.comp_def] using h
  rw [(M.diagonal_re_law a).map_eq] at h'
  exact h'

/-- The diagonal background marginal. -/
def diagonalBackgroundMeasure {p : Params} (M : Law p)
    (a : Site p.n p.W) :
    Measure (Matrix (Site p.n p.W) (Site p.n p.W) ℂ) :=
  M.P.map (fun ω => diagonalRealBackground (M.H ω) a)

/-- The exact real-coordinate/background product measure. -/
def diagonalCoordinateProductMeasure {p : Params} (M : Law p)
    (a : Site p.n p.W) :
    Measure (ℝ × Matrix (Site p.n p.W) (Site p.n p.W) ℂ) :=
  (gaussianReal 0 (varianceNNReal p a a)).prod
    (diagonalBackgroundMeasure M a)

/-- Arbitrary measurable joint tests transfer from the matrix law to the
real-diagonal/background product. -/
theorem Law.integral_diagonalGaussian_background
    {p : Params} (M : Law p) (a : Site p.n p.W)
    {Φ : ℝ × Matrix (Site p.n p.W) (Site p.n p.W) ℂ → ℂ}
    (hΦ : AEStronglyMeasurable Φ (diagonalCoordinateProductMeasure M a)) :
    (∫ ω, Φ ((M.H ω a a).re,
      diagonalRealBackground (M.H ω) a) ∂M.P) =
      ∫ v, Φ v ∂diagonalCoordinateProductMeasure M a := by
  unfold diagonalCoordinateProductMeasure diagonalBackgroundMeasure at hΦ ⊢
  symm
  rw [← Law.diagonalReal_background_productLaw M a] at hΦ ⊢
  exact integral_map
    (((Complex.measurable_re.comp (M.measurable_entry a a)).prodMk
      (Law.measurable_diagonalRealBackground M a)).aemeasurable) hΦ

/-- The diagonal background marginal is supported on Hermitian matrices. -/
theorem Law.diagonalBackground_ae_isHermitian
    {p : Params} (M : Law p) (a : Site p.n p.W) :
    ∀ᵐ B ∂diagonalBackgroundMeasure M a, B.IsHermitian := by
  unfold diagonalBackgroundMeasure
  have hmap := Law.measurable_diagonalRealBackground M a
  apply (ae_map_iff hmap.aemeasurable ?_).2
  · filter_upwards [] with ω
    exact diagonalRealBackground_isHermitian (M.H ω) (M.isHermitian ω) a
  · have hpred : Measurable
        (fun B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
          ∀ i j, starRingEnd ℂ (B j i) = B i j) := by
      apply Measurable.forall
      intro i
      apply Measurable.forall
      intro j
      exact (Complex.continuous_conj.measurable.comp
        Matrix.measurable_apply).eq Matrix.measurable_apply
    apply hpred.setOf.congr
    ext B
    simp only [Set.mem_ofPred_eq, Matrix.IsHermitian]
    constructor
    · intro h
      ext i j
      exact h i j
    · intro h i j
      exact congrFun (congrFun h i) j

/-- The full diagonal coordinate product is supported on Hermitian
reconstructions. -/
theorem Law.diagonalCoordinateProduct_ae_isHermitian
    {p : Params} (M : Law p) (a : Site p.n p.W) :
    ∀ᵐ v ∂diagonalCoordinateProductMeasure M a, v.2.IsHermitian := by
  let _ : IsFiniteMeasure (diagonalBackgroundMeasure M a) :=
    Measure.isFiniteMeasure_map M.P _
  have hentry : Measurable
      (fun v : ℝ × Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        ∀ i j, starRingEnd ℂ (v.2 j i) = v.2 i j) := by
    apply Measurable.forall
    intro i
    apply Measurable.forall
    intro j
    exact (Complex.continuous_conj.measurable.comp
      (Matrix.measurable_apply.comp measurable_snd)).eq
        (Matrix.measurable_apply.comp measurable_snd)
  have hae : ∀ᵐ v ∂diagonalCoordinateProductMeasure M a,
      ∀ i j, starRingEnd ℂ (v.2 j i) = v.2 i j := by
    apply (Measure.ae_prod_iff_ae_ae hentry.setOf).2
    filter_upwards [] with r
    filter_upwards [Law.diagonalBackground_ae_isHermitian M a] with B hB
    intro i j
    exact congrFun (congrFun hB i) j
  filter_upwards [hae] with v hv
  ext i j
  exact hv i j

/-- The diagonal variance parameter is strictly positive for every admissible
model parameter: its profile contains the positive `c/W` diagonal term. -/
theorem varianceNNReal_diagonal_pos (p : Params) (a : Site p.n p.W) :
    0 < varianceNNReal p a a := by
  change 0 < varianceProfile p a a
  have hc := p.c_pos
  have hb := p.b_pos
  have hW : 0 < (p.W : ℝ) := by exact_mod_cast p.W_pos
  unfold varianceProfile blockWeight
  simp only [ite_true]
  split_ifs <;> apply div_pos <;> positivity

/-- A diagonal reconstructed source-inverse entry is jointly measurable in
the real coordinate and background. -/
theorem measurable_sourceInverse_diagonalProductEntry
    (p : Params) (a i j : Site p.n p.W) (z : ℂ) :
    Measurable (fun v : ℝ ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        sourceInverse (diagonalRealCoordinateMatrix v.2 a v.1) z i j) := by
  let P := fun v : ℝ × Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
    diagonalRealCoordinateMatrix v.2 a v.1 -
      z • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
  have hP : Measurable P := by
    apply Matrix.measurable_iff.mpr
    intro u v
    dsimp [P, diagonalRealCoordinateMatrix, diagonalRealDirection]
    fun_prop
  unfold sourceInverse
  change Measurable (fun v => (Ring.inverse (P v).det • (P v).adjugate) i j)
  rw [show (fun v => (Ring.inverse (P v).det • (P v).adjugate) i j) =
      (fun v => (P v).det⁻¹ * (P v).adjugate i j) by
        funext v
        rw [Matrix.smul_apply]
        simp]
  exact (continuous_id.matrix_det.measurable.comp hP).inv.mul
    ((continuous_id.matrix_adjugate.measurable.comp hP).eval_matrix)

/-- Joint measurability of the diagonal signed error. -/
theorem measurable_diagonalCoordinateSignedError_product
    (p : Params) (a x y : Site p.n p.W) (z : ℂ) :
    Measurable (fun v : ℝ ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        diagonalCoordinateSignedError p v.2 a x y z v.1) := by
  unfold diagonalCoordinateSignedError
  apply Finset.measurable_sum
  intro k _
  exact measurable_const.mul
    ((measurable_sourceInverse_diagonalProductEntry p a k y z).sub
      measurable_const)

/-- Joint measurability of the diagonal resolvent/lower-moment test. -/
theorem measurable_diagonalResolventLowerTest_product
    (p : Params) (a x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) :
    Measurable (fun v : ℝ ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        diagonalResolventLowerTest p v.2 a x y i j z m v.1) := by
  unfold diagonalResolventLowerTest
  exact (measurable_sourceInverse_diagonalProductEntry p a i j z).mul
    (measurable_lowerConjugateMomentTest m
      (measurable_diagonalCoordinateSignedError_product p a x y z))

/-- Joint measurability of the full diagonal derivative test. -/
theorem measurable_diagonalResolventLowerDerivative_product
    (p : Params) (a x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) :
    Measurable (fun v : ℝ ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        diagonalResolventLowerDerivative p v.2 a x y i j z m v.1) := by
  unfold diagonalResolventLowerDerivative diagonalCoordinateSignedErrorDeriv
  have hia := measurable_sourceInverse_diagonalProductEntry p a i a z
  have haj := measurable_sourceInverse_diagonalProductEntry p a a j z
  have hij := measurable_sourceInverse_diagonalProductEntry p a i j z
  have hw := measurable_diagonalCoordinateSignedError_product p a x y z
  have hdw : Measurable (fun v : ℝ ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
      -∑ k, (siteCovariance p x k : ℂ) *
        sourceInverse (diagonalRealCoordinateMatrix v.2 a v.1) z k a *
        sourceInverse (diagonalRealCoordinateMatrix v.2 a v.1) z a y) := by
    apply Measurable.neg
    apply Finset.measurable_sum
    intro k _
    exact (measurable_const.mul
      (measurable_sourceInverse_diagonalProductEntry p a k a z)).mul
        (measurable_sourceInverse_diagonalProductEntry p a a y z)
  exact ((hia.neg.mul haj).mul
      (measurable_lowerConjugateMomentTest m hw)).add
    (hij.mul (measurable_lowerConjugateMomentDerivative m hw hdw))

/-- Uniform diagonal-coordinate inverse-entry domination. -/
theorem norm_sourceInverse_diagonal_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (a i j : ι)
    (z : ℂ) (hz : 0 < z.im) (r : ℝ) :
    ‖sourceInverse (diagonalRealCoordinateMatrix B a r) z i j‖ ≤
      (z.im)⁻¹ := by
  rw [sourceInverse_eq_neg_matrixResolvent _
    (diagonalRealCoordinateMatrix_isHermitian B hB a r) z hz.ne']
  simpa using norm_matrixResolvent_entry_le
    (diagonalRealCoordinateMatrix B a r)
    (diagonalRealCoordinateMatrix_isHermitian B hB a r) hz i j

/-- Uniform diagonal signed-error domination. -/
theorem norm_diagonalCoordinateSignedError_le
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a x y : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (r : ℝ) :
    ‖diagonalCoordinateSignedError p B a x y z r‖ ≤
      (z.im)⁻¹ + ‖erSemicircleStieltjes z‖ := by
  rw [diagonalCoordinateSignedError]
  calc
    _ ≤ ∑ k, ‖(siteCovariance p x k : ℂ) *
        (sourceInverse (diagonalRealCoordinateMatrix B a r) z k y -
          semicircleMatrix p z k y)‖ := norm_sum_le _ _
    _ ≤ ∑ k, siteCovariance p x k *
        ((z.im)⁻¹ + ‖erSemicircleStieltjes z‖) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (siteCovariance_flat p x k).1]
      apply mul_le_mul_of_nonneg_left _ (siteCovariance_flat p x k).1
      refine (norm_sub_le _ _).trans ?_
      gcongr
      · exact norm_sourceInverse_diagonal_le B hB a k y z hz r
      · by_cases h : k = y <;> simp [semicircleMatrix, h]
    _ = _ := by
      rw [← Finset.sum_mul, siteCovariance_stochastic]
      simp

/-- The diagonal signed-error derivative has one, rather than two,
resolvent contractions. -/
theorem norm_diagonalCoordinateSignedErrorDeriv_le
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a x y : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (r : ℝ) :
    ‖diagonalCoordinateSignedErrorDeriv p B a x y z r‖ ≤
      (z.im)⁻¹ ^ 2 := by
  rw [diagonalCoordinateSignedErrorDeriv, norm_neg]
  calc
    _ ≤ ∑ k, ‖(siteCovariance p x k : ℂ) *
      sourceInverse (diagonalRealCoordinateMatrix B a r) z k a *
      sourceInverse (diagonalRealCoordinateMatrix B a r) z a y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k, siteCovariance p x k * (z.im)⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (siteCovariance_flat p x k).1]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (siteCovariance_flat p x k).1
      rw [pow_two]
      exact mul_le_mul
        (norm_sourceInverse_diagonal_le B hB a k a z hz r)
        (norm_sourceInverse_diagonal_le B hB a a y z hz r)
        (norm_nonneg _) (inv_nonneg.mpr hz.le)
    _ = _ := by
      rw [← Finset.sum_mul, siteCovariance_stochastic]
      simp

/-- Explicit uniform bound for the diagonal differentiated test. -/
def diagonalResolventWeightedDerivativeBound (z : ℂ) (m : ℕ) : ℝ :=
  let E := (z.im)⁻¹
  let C := E + ‖erSemicircleStieltjes z‖
  let R := max 1 C
  E ^ 2 * R ^ (2 * m) +
    E * ((2 * m : ℝ) * R ^ (m - 1) * E ^ 2 * R ^ m)

/-- The diagonal test is uniformly dominated almost everywhere on its exact
product law. -/
theorem Law.ae_norm_diagonalResolventLowerTest_le
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    ∀ᵐ v ∂diagonalCoordinateProductMeasure M a,
      ‖diagonalResolventLowerTest p v.2 a x y i j z m v.1‖ ≤
        (z.im)⁻¹ *
          ((z.im)⁻¹ + ‖erSemicircleStieltjes z‖) ^ (2 * m) := by
  filter_upwards [Law.diagonalCoordinateProduct_ae_isHermitian M a] with v hB
  rw [diagonalResolventLowerTest, norm_mul, norm_lowerConjugateMomentTest]
  exact mul_le_mul
    (norm_sourceInverse_diagonal_le v.2 hB a i j z hz v.1)
    (pow_le_pow_left₀ (norm_nonneg _)
      (norm_diagonalCoordinateSignedError_le p v.2 hB a x y z hz v.1) _)
    (by positivity) (inv_nonneg.mpr hz.le)

/-- The full diagonal derivative test is uniformly dominated almost
everywhere. -/
theorem Law.ae_norm_diagonalResolventLowerDerivative_le
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    ∀ᵐ v ∂diagonalCoordinateProductMeasure M a,
      ‖diagonalResolventLowerDerivative p v.2 a x y i j z m v.1‖ ≤
        diagonalResolventWeightedDerivativeBound z m := by
  filter_upwards [Law.diagonalCoordinateProduct_ae_isHermitian M a] with v hB
  let E := (z.im)⁻¹
  let C := E + ‖erSemicircleStieltjes z‖
  let R := max 1 C
  have hE : 0 ≤ E := inv_nonneg.mpr hz.le
  have hG (u w : Site p.n p.W) :
      ‖sourceInverse (diagonalRealCoordinateMatrix v.2 a v.1) z u w‖ ≤ E :=
    norm_sourceInverse_diagonal_le v.2 hB a u w z hz v.1
  have hw : ‖diagonalCoordinateSignedError p v.2 a x y z v.1‖ ≤ C :=
    norm_diagonalCoordinateSignedError_le p v.2 hB a x y z hz v.1
  have hL : ‖lowerConjugateMomentTest m
      (diagonalCoordinateSignedError p v.2 a x y z v.1)‖ ≤ R ^ (2 * m) := by
    rw [norm_lowerConjugateMomentTest]
    exact pow_le_pow_left₀ (norm_nonneg _) (hw.trans (le_max_right _ _)) _
  have hdL : ‖lowerConjugateMomentDerivative m
      (diagonalCoordinateSignedError p v.2 a x y z v.1)
      (diagonalCoordinateSignedErrorDeriv p v.2 a x y z v.1)‖ ≤
      (2 * m : ℝ) * R ^ (m - 1) * E ^ 2 * R ^ m := by
    exact norm_lowerConjugateMomentDerivative_le m _ _ (by positivity) hw
      (norm_diagonalCoordinateSignedErrorDeriv_le
        p v.2 hB a x y z hz v.1)
  rw [diagonalResolventLowerDerivative]
  calc
    _ ≤ ‖(-sourceInverse (diagonalRealCoordinateMatrix v.2 a v.1) z i a *
          sourceInverse (diagonalRealCoordinateMatrix v.2 a v.1) z a j) *
          lowerConjugateMomentTest m
            (diagonalCoordinateSignedError p v.2 a x y z v.1)‖ +
        ‖sourceInverse (diagonalRealCoordinateMatrix v.2 a v.1) z i j *
          lowerConjugateMomentDerivative m
            (diagonalCoordinateSignedError p v.2 a x y z v.1)
            (diagonalCoordinateSignedErrorDeriv p v.2 a x y z v.1)‖ :=
      norm_add_le _ _
    _ ≤ (E * E) * R ^ (2 * m) +
        E * ((2 * m : ℝ) * R ^ (m - 1) * E ^ 2 * R ^ m) := by
      simp only [norm_mul, norm_neg]
      exact add_le_add
        (mul_le_mul (mul_le_mul (hG i a) (hG a j) (norm_nonneg _) hE)
          hL (norm_nonneg _) (mul_nonneg hE hE))
        (mul_le_mul (hG i j) hdL (norm_nonneg _) hE)
    _ = _ := by
      simp only [diagonalResolventWeightedDerivativeBound, E, C, R]
      ring

/-- Product integrability of the undifferentiated diagonal test. -/
theorem Law.integrable_diagonalResolventLowerTest_product
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun v => diagonalResolventLowerTest p v.2
      a x y i j z m v.1) (diagonalCoordinateProductMeasure M a) := by
  let _ : IsFiniteMeasure (diagonalBackgroundMeasure M a) :=
    Measure.isFiniteMeasure_map M.P _
  let _ : IsFiniteMeasure (diagonalCoordinateProductMeasure M a) :=
    Measure.prod.instIsFiniteMeasure _ _
  exact Integrable.of_bound
    (measurable_diagonalResolventLowerTest_product
      p a x y i j z m).aestronglyMeasurable
    ((z.im)⁻¹ * ((z.im)⁻¹ + ‖erSemicircleStieltjes z‖) ^ (2 * m))
    (Law.ae_norm_diagonalResolventLowerTest_le M a x y i j z hz m)

/-- Product integrability of the differentiated diagonal test. -/
theorem Law.integrable_diagonalResolventLowerDerivative_product
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun v => diagonalResolventLowerDerivative p v.2
      a x y i j z m v.1) (diagonalCoordinateProductMeasure M a) := by
  let _ : IsFiniteMeasure (diagonalBackgroundMeasure M a) :=
    Measure.isFiniteMeasure_map M.P _
  let _ : IsFiniteMeasure (diagonalCoordinateProductMeasure M a) :=
    Measure.prod.instIsFiniteMeasure _ _
  exact Integrable.of_bound
    (measurable_diagonalResolventLowerDerivative_product
      p a x y i j z m).aestronglyMeasurable
    (diagonalResolventWeightedDerivativeBound z m)
    (Law.ae_norm_diagonalResolventLowerDerivative_le M a x y i j z hz m)

/-- The selected real diagonal coordinate is integrable on the exact product
law. -/
theorem Law.integrable_diagonalRealCoordinate_product
    {p : Params} (M : Law p) (a : Site p.n p.W) :
    Integrable (fun v : ℝ ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ => (v.1 : ℂ))
      (diagonalCoordinateProductMeasure M a) := by
  let _ : IsFiniteMeasure (diagonalBackgroundMeasure M a) :=
    Measure.isFiniteMeasure_map M.P _
  have hr : Integrable (fun r : ℝ => (r : ℂ))
      (gaussianReal 0 (varianceNNReal p a a)) :=
    ((memLp_id_gaussianReal (μ := 0) (v := varianceNNReal p a a) 1).integrable
      (by norm_num)).ofReal
  simpa [diagonalCoordinateProductMeasure] using
    hr.comp_fst (diagonalBackgroundMeasure M a)

/-- Coordinate-weighted diagonal test integrability needed on the left side
of Gaussian IBP. -/
theorem Law.integrable_realWeightedDiagonalResolventLowerTest_product
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun v => (v.1 : ℂ) *
      diagonalResolventLowerTest p v.2 a x y i j z m v.1)
      (diagonalCoordinateProductMeasure M a) := by
  apply (Law.integrable_diagonalRealCoordinate_product M a).mul_bdd
    (measurable_diagonalResolventLowerTest_product
      p a x y i j z m).aestronglyMeasurable
  exact Law.ae_norm_diagonalResolventLowerTest_le M a x y i j z hz m

/-- Positive diagonal variance allows the supported one-dimensional Gaussian
IBP to be lifted through the diagonal-background marginal. -/
theorem Law.integral_realWeightedDiagonalResolventLowerTest_eq_derivative_product
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    (∫ v, (v.1 : ℂ) *
      diagonalResolventLowerTest p v.2 a x y i j z m v.1
      ∂diagonalCoordinateProductMeasure M a) =
      (((varianceNNReal p a a : NNReal) : ℝ) : ℂ) *
        ∫ v, diagonalResolventLowerDerivative p v.2
          a x y i j z m v.1 ∂diagonalCoordinateProductMeasure M a := by
  let σ : NNReal := varianceNNReal p a a
  have hσ : σ ≠ 0 := ne_of_gt (varianceNNReal_diagonal_pos p a)
  let μB := diagonalBackgroundMeasure M a
  let _ : IsFiniteMeasure μB := Measure.isFiniteMeasure_map M.P _
  let FL : ℝ × Matrix (Site p.n p.W) (Site p.n p.W) ℂ → ℂ :=
    fun v => (v.1 : ℂ) *
      diagonalResolventLowerTest p v.2 a x y i j z m v.1
  let FT : ℝ × Matrix (Site p.n p.W) (Site p.n p.W) ℂ → ℂ :=
    fun v => diagonalResolventLowerTest p v.2 a x y i j z m v.1
  let FR : ℝ × Matrix (Site p.n p.W) (Site p.n p.W) ℂ → ℂ :=
    fun v => diagonalResolventLowerDerivative p v.2 a x y i j z m v.1
  have hL : Integrable FL ((gaussianReal 0 σ).prod μB) := by
    simpa [FL, σ, μB, diagonalCoordinateProductMeasure] using
      Law.integrable_realWeightedDiagonalResolventLowerTest_product
        M a x y i j z hz m
  have hT : Integrable FT ((gaussianReal 0 σ).prod μB) := by
    simpa [FT, σ, μB, diagonalCoordinateProductMeasure] using
      Law.integrable_diagonalResolventLowerTest_product
        M a x y i j z hz m
  have hR : Integrable FR ((gaussianReal 0 σ).prod μB) := by
    simpa [FR, σ, μB, diagonalCoordinateProductMeasure] using
      Law.integrable_diagonalResolventLowerDerivative_product
        M a x y i j z hz m
  change (∫ v, FL v ∂(gaussianReal 0 σ).prod μB) =
    (((σ : NNReal) : ℝ) : ℂ) *
      ∫ v, FR v ∂(gaussianReal 0 σ).prod μB
  rw [integral_prod_symm FL hL, integral_prod_symm FR hR,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Law.diagonalBackground_ae_isHermitian M a,
    hL.prod_left_ae, hT.prod_left_ae, hR.prod_left_ae] with B hB hLB hTB hRB
  exact gaussianIBP_jointTest_real σ hσ
    (fun r (_ : ℝ) (_ : Unit) =>
      diagonalResolventLowerTest p B a x y i j z m r)
    (fun r (_ : ℝ) (_ : Unit) =>
      diagonalResolventLowerDerivative p B a x y i j z m r)
    (fun r _ _ => hasDerivAt_diagonalResolventLowerTest
      p B hB a x y i j z hz.ne' m r)
    0 ()
    (integrable_id_gaussianPDF_mul_of_integrable_gaussianReal σ hσ hLB)
    (integrable_gaussianPDF_mul_of_integrable_gaussianReal σ hσ hRB)
    (integrable_gaussianPDF_mul_of_integrable_gaussianReal σ hσ hTB)

/-- The differentiated diagonal test evaluated on the sample. -/
def actualDiagonalResolventLowerDerivative
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (m : ℕ) (ω : M.Ω) : ℂ :=
  diagonalResolventLowerDerivative p
    (diagonalRealBackground (M.H ω) a) a x y i j z m (M.H ω a a).re

/-- Exact product-law transfer of the differentiated diagonal test. -/
theorem Law.integral_actualDiagonalResolventLowerDerivative_eq_product
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (m : ℕ) :
    (∫ ω, actualDiagonalResolventLowerDerivative
      M a x y i j z m ω ∂M.P) =
      ∫ v, diagonalResolventLowerDerivative p v.2
        a x y i j z m v.1 ∂diagonalCoordinateProductMeasure M a := by
  exact Law.integral_diagonalGaussian_background M a
    (measurable_diagonalResolventLowerDerivative_product
      p a x y i j z m).aestronglyMeasurable

/-- Exact product-law transfer of the coordinate-weighted diagonal test to
`H_aa G_ij` under the matrix law. -/
theorem Law.integral_diagonalEntryWeightedResolventLowerTest_eq_product
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (m : ℕ) :
    (∫ ω, M.H ω a a * green M z ω i j *
      lowerConjugateMomentTest m
        (ERFluctuationMoments.signedResolventError M z x y ω) ∂M.P) =
      ∫ v, (v.1 : ℂ) *
        diagonalResolventLowerTest p v.2 a x y i j z m v.1
        ∂diagonalCoordinateProductMeasure M a := by
  calc
    _ = ∫ ω, (((M.H ω a a).re : ℝ) : ℂ) *
        diagonalResolventLowerTest p
          (diagonalRealBackground (M.H ω) a)
          a x y i j z m (M.H ω a a).re ∂M.P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [diagonalResolventLowerTest_actual M a x y i j z hz m ω]
      rw [hermitian_diag_eq_re (M.H ω) (M.isHermitian ω) a]
      ring
    _ = _ := Law.integral_diagonalGaussian_background M a
      ((measurable_fst.complex_ofReal.mul
        (measurable_diagonalResolventLowerTest_product
          p a x y i j z m))).aestronglyMeasurable

/-- The exact diagonal Gaussian IBP under the matrix law, at the model variance.  Its
variance is positive by admissibility, so no zero-variance case arises. -/
theorem Law.integral_diagonalEntryWeightedResolventLowerTest_eq_actualDerivative
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    (∫ ω, M.H ω a a * green M z ω i j *
      lowerConjugateMomentTest m
        (ERFluctuationMoments.signedResolventError M z x y ω) ∂M.P) =
      (((varianceNNReal p a a : NNReal) : ℝ) : ℂ) *
        ∫ ω, actualDiagonalResolventLowerDerivative
          M a x y i j z m ω ∂M.P := by
  calc
    _ = ∫ v, (v.1 : ℂ) *
        diagonalResolventLowerTest p v.2 a x y i j z m v.1
        ∂diagonalCoordinateProductMeasure M a :=
      Law.integral_diagonalEntryWeightedResolventLowerTest_eq_product
        M a x y i j z hz.ne' m
    _ = (((varianceNNReal p a a : NNReal) : ℝ) : ℂ) *
        ∫ v, diagonalResolventLowerDerivative p v.2
          a x y i j z m v.1 ∂diagonalCoordinateProductMeasure M a :=
      Law.integral_realWeightedDiagonalResolventLowerTest_eq_derivative_product
        M a x y i j z hz m
    _ = _ := by
      rw [← Law.integral_actualDiagonalResolventLowerDerivative_eq_product
        M a x y i j z m]

end ERSharpCoordinateIBP
end GaussianRing
end ERNative.BlockBand
