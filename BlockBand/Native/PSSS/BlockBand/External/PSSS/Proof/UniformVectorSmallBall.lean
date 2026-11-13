module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorMultiplicativeReduction
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Uniform complex-sphere small-image estimate

This module completes the analytic Chernoff-product collapse after the exact polar and
real-Gram spectral reductions.  The normalization is the real standard Gaussian
on the `2N` real coordinates of `ℂ^N`; consequently the spectral weights have total mass
exactly twice the squared complex Frobenius norm.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- Collapsing the negative-half-power Laplace product using only nonnegative weights
and their total mass.  At the Chernoff parameter `1/(8 ε² F²)`, the product is at most
`√2 ε`. -/
theorem laplaceProduct_le_sqrtTwo_mul
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {F ε : ℝ} (hF : 0 < F) (hε : 0 < ε)
    (hsum : ∑ i, w i = 2 * F ^ 2) :
    let t := 1 / (8 * ε ^ 2 * F ^ 2)
    ∏ i, (1 + 2 * t * w i) ^ (-(1 : ℝ) / 2) ≤ Real.sqrt 2 * ε := by
  dsimp only
  let t : ℝ := 1 / (8 * ε ^ 2 * F ^ 2)
  have ht : 0 ≤ t := by positivity
  have htw : ∀ i, 0 ≤ 2 * t * w i := fun i =>
    mul_nonneg (mul_nonneg (by norm_num) ht) (hw i)
  have hfactor : ∀ i, 0 ≤ 1 + 2 * t * w i := fun i =>
    add_nonneg zero_le_one (htw i)
  have hprodEq :
      (∏ i, (1 + 2 * t * w i) ^ (-(1 : ℝ) / 2)) =
        (∏ i, (1 + 2 * t * w i)) ^ (-(1 : ℝ) / 2) := by
    exact Real.finsetProd_rpow Finset.univ (fun i => 1 + 2 * t * w i)
      (fun i _ => hfactor i) _
  have hbase := one_add_sum_le_prod_one_add (fun i => 2 * t * w i)
    htw
  have hsum' : ∑ i, 2 * t * w i = 1 / (2 * ε ^ 2) := by
    rw [← Finset.mul_sum, hsum]
    dsimp [t]
    field_simp
    ring
  have hlower : 1 / (2 * ε ^ 2) ≤ ∏ i, (1 + 2 * t * w i) := by
    rw [hsum'] at hbase
    exact le_trans (le_add_of_nonneg_left zero_le_one) hbase
  have hsmall : 0 < 1 / (2 * ε ^ 2) := by positivity
  have hpow :
      (∏ i, (1 + 2 * t * w i)) ^ (-(1 : ℝ) / 2) ≤
        (1 / (2 * ε ^ 2)) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hsmall hlower (by norm_num)
  rw [hprodEq]
  refine hpow.trans_eq ?_
  rw [Real.rpow_div_two_eq_sqrt (-1) hsmall.le, Real.rpow_neg_one]
  rw [show 1 / (2 * ε ^ 2) = (2 * ε ^ 2)⁻¹ by ring]
  rw [Real.sqrt_inv, inv_inv, Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hε]

/-- The diagonal Gaussian quadratic lower tail after optimizing the Chernoff
parameter.  Zero spectral weights are allowed; only the strictly positive total
mass `2F²` is used. -/
theorem pi_gaussianReal_lowerTail_le_expHalf_sqrtTwo
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {F ε : ℝ} (hF : 0 < F) (hε : 0 < ε)
    (hsum : ∑ i, w i = 2 * F ^ 2) :
    Measure.pi (fun _ : ι => gaussianReal 0 1)
        {x | (∑ i, w i * (x i) ^ 2) ≤ 4 * ε ^ 2 * F ^ 2} ≤
      ENNReal.ofReal (Real.exp (1 / 2) * Real.sqrt 2 * ε) := by
  let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
  let t : ℝ := 1 / (8 * ε ^ 2 * F ^ 2)
  have ht : 0 ≤ t := by positivity
  have hchernoff :=
    pi_gaussianReal_sum_mul_sq_lowerTail_le_laplaceProduct
      w hw (4 * ε ^ 2 * F ^ 2) t ht
  have hprod := laplaceProduct_le_sqrtTwo_mul w hw hF hε hsum
  dsimp only at hprod
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity :
    0 ≤ Real.exp (1 / 2) * Real.sqrt 2 * ε)]
  change μ.real {x | (∑ i, w i * (x i) ^ 2) ≤ 4 * ε ^ 2 * F ^ 2} ≤ _
  calc
    μ.real {x | (∑ i, w i * (x i) ^ 2) ≤ 4 * ε ^ 2 * F ^ 2} ≤
        Real.exp (t * (4 * ε ^ 2 * F ^ 2)) *
          ∏ i, (1 + 2 * t * w i) ^ (-(1 : ℝ) / 2) := hchernoff
    _ = Real.exp (1 / 2) *
          ∏ i, (1 + 2 * t * w i) ^ (-(1 : ℝ) / 2) := by
          congr 2
          dsimp [t]
          field_simp
          ring
    _ ≤ Real.exp (1 / 2) * (Real.sqrt 2 * ε) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg _)
    _ = Real.exp (1 / 2) * Real.sqrt 2 * ε := by ring

/-- Gaussian linear-image small-ball bound in the exact complex Frobenius
normalization.  Rank-deficient matrices are allowed; `Q ≠ 0` is used only to make
the total spectral mass positive. -/
theorem stdGaussian_mulVec_small_frobenius {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) (hQ : Q ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    let F := ‖(WithLp.toLp 2 (Matrix.vec Q) :
      EuclideanSpace ℂ (Fin N × Fin N))‖
    stdGaussian (EuclideanSpace ℂ (Fin N))
        (mulVecNormLeEvent Q (2 * ε * F)) ≤
      ENNReal.ofReal (Real.exp (1 / 2) * Real.sqrt 2 * ε) := by
  dsimp only
  let F := ‖(WithLp.toLp 2 (Matrix.vec Q) :
    EuclideanSpace ℂ (Fin N × Fin N))‖
  have hvec :
      (WithLp.toLp 2 (Matrix.vec Q) :
        EuclideanSpace ℂ (Fin N × Fin N)) ≠ 0 := by
    intro hz
    apply hQ
    ext i j
    have hij := congrArg
      (fun v : EuclideanSpace ℂ (Fin N × Fin N) => WithLp.ofLp v (j, i)) hz
    simpa [Matrix.vec] using hij
  have hF : 0 < F := norm_pos_iff.mpr hvec
  have ha : 0 ≤ 2 * ε * F := by positivity
  rw [stdGaussian_mulVecNormLeEvent_eq_pi_spectral Q ha]
  let T := Matrix.toEuclideanLin (complexGramRealification Q)
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr (complexGramRealification_isSymm Q))
  let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) =
      Fintype.card (Fin N × Fin 2) := by simp
  let w : Fin (Fintype.card (Fin N × Fin 2)) → ℝ :=
    fun k => hT.eigenvalues hdim k
  have hw : ∀ k, 0 ≤ w k := by
    simpa [w, T, hT, hdim] using eigenvalues_complexGramRealification_nonneg Q
  have hsum : ∑ k, w k = 2 * F ^ 2 := by
    have htrace := sum_eigenvalues_complexGramRealification Q
    dsimp only at htrace
    rw [← norm_sq_matrix_vec_eq_sum Q] at htrace
    simpa [w, T, hT, hdim, F] using htrace
  have hbound := pi_gaussianReal_lowerTail_le_expHalf_sqrtTwo
    w hw hF hε hsum
  convert hbound using 1
  · congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    dsimp [w]
    ring_nf

/-- The elementary numerical inequality behind the advertised absolute constant
`5`.  Squaring reduces it to `8e < 24 < 25`. -/
theorem two_mul_expHalf_sqrtTwo_le_five :
    2 * Real.exp (1 / 2) * Real.sqrt 2 ≤ 5 := by
  have he : Real.exp (1 : ℝ) < 3 := Real.exp_one_lt_three
  have hexp : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [Real.exp_half]
    exact Real.sq_sqrt (Real.exp_nonneg 1)
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ 2 * Real.exp (1 / 2) * Real.sqrt 2 := by positivity
  nlinarith

/-- APSSS (Aizenman–Peled–Schenker–Shamis–Sodin) Lemma 3.1, equation (3.6): a
uniform complex unit vector is unlikely
to fall in the Frobenius-scaled small-image set of a nonzero deterministic matrix.
The bound is uniform in the dimension and allows arbitrary rank deficiency. -/
theorem uniformSphere_mulVec_small_frobenius
    {N : ℕ} (hN : 0 < N)
    (Q : Matrix (Fin N) (Fin N) ℂ) (hQ : Q ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    uniformSphere N
      {v |
        ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
          EuclideanSpace ℂ (Fin N))‖
        ≤ ε / Real.sqrt N *
          ‖(WithLp.toLp 2 (Matrix.vec Q) :
            EuclideanSpace ℂ (Fin N × Fin N))‖}
    ≤ ENNReal.ofReal (5 * ε) := by
  let F := ‖(WithLp.toLp 2 (Matrix.vec Q) :
    EuclideanSpace ℂ (Fin N × Fin N))‖
  let a := ε / Real.sqrt N * F
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have ha : 0 ≤ a := by positivity
  have hscale : a * (2 * Real.sqrt N) = 2 * ε * F := by
    dsimp [a]
    field_simp
  have hhalf := half_mul_uniformSphere_mulVec_le_gaussian_smallBall hN Q ha
  rw [hscale] at hhalf
  have hgauss := stdGaussian_mulVec_small_frobenius Q hQ hε
  dsimp only at hgauss
  have hchain :
      ENNReal.ofReal (1 / 2 : ℝ) *
          uniformSphere N (mulVecNormLeEvent Q a) ≤
        ENNReal.ofReal (Real.exp (1 / 2) * Real.sqrt 2 * ε) :=
    hhalf.trans hgauss
  have hofhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  change uniformSphere N (mulVecNormLeEvent Q a) ≤ ENNReal.ofReal (5 * ε)
  calc
    uniformSphere N (mulVecNormLeEvent Q a) =
        2 * (ENNReal.ofReal (1 / 2 : ℝ) *
          uniformSphere N (mulVecNormLeEvent Q a)) := by
            rw [hofhalf]
            rw [← mul_assoc]
            rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * ENNReal.ofReal (Real.exp (1 / 2) * Real.sqrt 2 * ε) := by
      gcongr
    _ = ENNReal.ofReal
        (2 * (Real.exp (1 / 2) * Real.sqrt 2 * ε)) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ ENNReal.ofReal (5 * ε) := by
      apply ENNReal.ofReal_le_ofReal
      have hc := two_mul_expHalf_sqrtTwo_le_five
      nlinarith

end PSSSNative.BlockBand.PSSS
