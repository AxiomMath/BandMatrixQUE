module

public import Mathlib

/-!
# The principal square root `(1 - A)^{1/2}` of a contraction (binomial series)

For `N × N` complex matrices with operator norm `‖A‖_op < 1` we define
`sqrtOneSub A = (1 - A)^{1/2} = ∑_k Ring.choose (1/2) k (-A)^k` (and `0` when `‖A‖_op ≥ 1`).

All analysis is done in the C⋆-algebra
`Op N = EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)` (a normed algebra
with global instances) and transported to matrices through the ⋆-algebra isomorphism
`Matrix.toEuclideanCLM`. The operator norm of a matrix appears only through
`opNorm A = ‖Matrix.toEuclideanCLM A‖`; no norm instance on `Matrix` is used, except that the
smoothness statements are stated with the Frobenius instances activated locally
(`Matrix.frobeniusNormedAddCommGroup`, `Matrix.frobeniusNormedSpace`), as in the transmission
flow statements.

Main results: `sqrtOneSub_mul_self` (`S² = 1 - A`), `sqrtOneSub_commute`,
`sqrtOneSub_conjTranspose`, `sqrtOneSub_isHermitian`, `contDiffOn_sqrtOneSub` (real-analytic,
`ContDiffOn ℝ ⊤`, on the open unit ball), `fderiv_sqrtOneSub_anticomm` (`S' H S + S S' H = -H`),
`fderiv_sqrtOneSub_isHermitian`, the principal-root bound `sqrtOneSub_one_sub_bound`
(`‖(1 - S) v‖² ≤ ‖A‖_op² ‖v‖²`; it holds without positivity, see
`sqrtOneSub_one_sub_bound_of_lt`), `opNorm_mul_conjTranspose_le`, `opNorm_one_of_pos`,
`measurable_sqrtOneSub`.

The scalar input: with `c_k = Ring.choose (1/2) k`, `c_k (-1)^k ≤ 0` for `k ≥ 1`,
`∑ c_k y^k = (1 + y)^{1/2}` for `|y| < 1` (`Real.one_add_rpow_hasFPowerSeriesOnBall_zero`), and
Vandermonde `∑_{i+j=n} c_i c_j = Nat.choose 1 n`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow
open scoped NNReal ENNReal ComplexOrder
open Matrix

/-!
### Scalar binomial coefficients of `(1 + x)^{1/2}`
-/

/-- The binomial coefficients `c_k = Ring.choose (1/2) k` of `(1 + x)^{1/2}`. -/
def halfChoose (k : ℕ) : ℝ := Ring.choose (1/2 : ℝ) k

theorem halfChoose_zero : halfChoose 0 = 1 := by simp [halfChoose]

theorem halfChoose_succ (k : ℕ) :
    ((k : ℝ) + 1) * halfChoose (k + 1) = halfChoose k * (1/2 - k) := by
  have h := Ring.choose_smul_choose (1/2 : ℝ) (Nat.le_succ k)
  rw [Nat.choose_succ_self_right, show k.succ - k = 1 by omega, Ring.choose_one_right,
    nsmul_eq_mul] at h
  simpa [halfChoose] using h

theorem halfChoose_sign (k : ℕ) (hk : 1 ≤ k) : halfChoose k * (-1) ^ k ≤ 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [halfChoose]
    · have ih := ih hk0
      have h := halfChoose_succ k
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk0
      have hpos : (0:ℝ) < (k:ℝ) + 1 := by positivity
      have : ((k:ℝ) + 1) * (halfChoose (k+1) * (-1) ^ (k+1)) =
          (halfChoose k * (-1)^k) * ((k:ℝ) - 1/2) := by
        rw [← mul_assoc, h, pow_succ]; ring
      have h2 : (halfChoose k * (-1)^k) * ((k:ℝ) - 1/2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ih (by linarith)
      nlinarith

theorem hasFPowerSeriesOnBall_sqrt : HasFPowerSeriesOnBall (fun x : ℝ ↦ (1 + x) ^ (1/2 : ℝ))
    (binomialSeries ℝ (1/2 : ℝ)) 0 1 := Real.one_add_rpow_hasFPowerSeriesOnBall_zero

theorem norm_binomialSeries_half (k : ℕ) :
    ‖binomialSeries ℝ (1/2 : ℝ) k‖ = |halfChoose k| := by
  simp [binomialSeries, halfChoose]

theorem summable_abs_halfChoose {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun k ↦ |halfChoose k| * r ^ k) := by
  have h := (binomialSeries ℝ (1/2 : ℝ)).summable_norm_mul_pow (r := r.toNNReal)
    (lt_of_lt_of_le (ENNReal.coe_lt_one_iff.mpr (Real.toNNReal_lt_one.mpr hr))
      hasFPowerSeriesOnBall_sqrt.r_le)
  exact h.congr fun k ↦ by rw [norm_binomialSeries_half, Real.coe_toNNReal _ hr0]

theorem hasSum_halfChoose {y : ℝ} (hy : |y| < 1) :
    HasSum (fun k ↦ halfChoose k * y ^ k) ((1 + y) ^ (1/2 : ℝ)) := by
  have hy' : y ∈ Metric.eball (0:ℝ) 1 := by
    show edist y 0 < 1
    rw [edist_dist, Real.dist_eq, sub_zero]; exact ENNReal.ofReal_lt_one.mpr hy
  have h := hasFPowerSeriesOnBall_sqrt.hasSum hy'
  simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul,
    zero_add] at h
  exact h

theorem hasSum_abs_halfChoose {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun k ↦ |halfChoose k| * x ^ k) (2 - (1 - x) ^ (1/2 : ℝ)) := by
  have h1 := (hasSum_ite_eq 0 (2:ℝ)).sub
    (hasSum_halfChoose (y := -x) (by rw [abs_neg, abs_of_nonneg hx0]; exact hx))
  rw [← sub_eq_add_neg] at h1
  convert h1 using 1
  funext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [halfChoose_zero]; norm_num
  · have hs := halfChoose_sign k hk
    have hk' : k ≠ 0 := by omega
    have habs : |halfChoose k| = -(halfChoose k * (-1) ^ k) := by
      rw [← abs_of_nonpos hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
    simp only [hk', ↓reduceIte]; rw [habs, neg_pow x k]; ring

/-- `∑_{k ≥ 1} |c_k| x^k ≤ x`. -/
theorem hasSum_abs_halfChoose_tail {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun k ↦ if k = 0 then 0 else |halfChoose k| * x ^ k) (1 - (1 - x) ^ (1/2 : ℝ)) ∧
      1 - (1 - x) ^ (1/2 : ℝ) ≤ x := by
  refine ⟨?_, ?_⟩
  · have h1 := (hasSum_abs_halfChoose hx0 hx).sub (hasSum_ite_eq 0 (1:ℝ))
    convert h1 using 1
    · funext k
      split_ifs with hk
      · subst hk; simp [halfChoose_zero]
      · simp
    · ring
  · have : (1 - x) ^ (1:ℝ) ≤ (1 - x) ^ (1/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by norm_num)
    rw [Real.rpow_one] at this
    linarith

variable {N : ℕ}

/-- The operator algebra `B(ℓ²(Fin N))`, a C⋆-algebra with global norm instances. -/
abbrev Op (N : ℕ) := EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)

instance instCompleteSpaceOp : CompleteSpace (Op N) := ContinuousLinearMap.instCompleteSpace

/-- The coefficients `c_k` as complex numbers. -/
def halfChooseC (k : ℕ) : ℂ := (halfChoose k : ℂ)

/-- The binomial series `∑_k c_k (-T)^k = (1 - T)^{1/2}` on `Op N` (used for `‖T‖ < 1`). -/
def opRoot (T : Op N) : Op N := ∑' k, halfChooseC k • (-T) ^ k

theorem norm_pow_le_op (T : Op N) (k : ℕ) : ‖T ^ k‖ ≤ ‖T‖ ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' T hk

theorem norm_rootTerm_le (T : Op N) (k : ℕ) :
    ‖halfChooseC k • (-T) ^ k‖ ≤ |halfChoose k| * ‖T‖ ^ k := by
  rw [norm_smul, halfChooseC, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  simpa using norm_pow_le_op (-T) k

theorem summable_norm_rootTerm {T : Op N} (hT : ‖T‖ < 1) :
    Summable (fun k ↦ ‖halfChooseC k • (-T) ^ k‖) :=
  (summable_abs_halfChoose (norm_nonneg T) hT).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_rootTerm_le T)

theorem summable_rootTerm {T : Op N} (hT : ‖T‖ < 1) :
    Summable (fun k ↦ halfChooseC k • (-T) ^ k) :=
  (summable_norm_rootTerm hT).of_norm

theorem halfChooseC_vandermonde (n : ℕ) :
    ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, halfChooseC kl.1 * halfChooseC kl.2 =
      (Nat.choose 1 n : ℂ) := by
  have h := Ring.add_choose_eq (r := (1/2 : ℝ)) (s := 1/2) n (Commute.refl _)
  rw [show (1/2 : ℝ) + 1/2 = ((1 : ℕ) : ℝ) by norm_num, Ring.choose_natCast] at h
  simp only [halfChooseC, halfChoose, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [← h]; simp

theorem opRoot_mul_self {T : Op N} (hT : ‖T‖ < 1) : opRoot T * opRoot T = 1 - T := by
  unfold opRoot
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_rootTerm hT)
    (summable_norm_rootTerm hT)]
  have hterm : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (halfChooseC kl.1 • (-T) ^ kl.1) * (halfChooseC kl.2 • (-T) ^ kl.2)
      = (Nat.choose 1 n : ℂ) • (-T) ^ n := by
    intro n
    rw [← halfChooseC_vandermonde]
    rw [Finset.sum_smul (M := Op N)]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [smul_mul_smul_comm, ← pow_add, hkl]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, sub_eq_add_neg]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    exact zero_smul ℂ ((-T) ^ n)

theorem opRoot_commute {T : Op N} (hT : ‖T‖ < 1) : T * opRoot T = opRoot T * T := by
  unfold opRoot
  rw [← (summable_rootTerm hT).tsum_mul_left, ← (summable_rootTerm hT).tsum_mul_right]
  refine tsum_congr fun k ↦ ?_
  rw [mul_smul_comm, smul_mul_assoc, ((Commute.refl T).neg_right.pow_right k).eq]

theorem star_opRoot {T : Op N} (hT : ‖T‖ < 1) : star (opRoot T) = opRoot (star T) := by
  unfold opRoot
  have h := (summable_rootTerm hT).hasSum.map (ContinuousLinearMap.adjoint (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (Fin N)) (F := EuclideanSpace ℂ (Fin N)))
    (ContinuousLinearMap.adjoint).continuous
  rw [ContinuousLinearMap.star_eq_adjoint, ← h.tsum_eq]
  refine tsum_congr fun k ↦ ?_
  simp only [Function.comp_apply, ← ContinuousLinearMap.star_eq_adjoint]
  rw [star_smul, star_pow, star_neg, halfChooseC, Complex.star_def, Complex.conj_ofReal]

theorem norm_one_sub_opRoot_le {T : Op N} (hT : ‖T‖ < 1) : ‖1 - opRoot T‖ ≤ ‖T‖ := by
  have hb := (hasSum_ite_eq 0 (1 : Op N)).sub (summable_rootTerm hT).hasSum
  obtain ⟨hg, hle⟩ := hasSum_abs_halfChoose_tail (norm_nonneg T) hT
  refine le_trans (hb.norm_le_of_bounded hg fun k ↦ ?_) hle
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [halfChooseC, halfChoose_zero]
  · have hk' : k ≠ 0 := by omega
    simp only [hk', ↓reduceIte, zero_sub, norm_neg]
    exact norm_rootTerm_le T k

/-- The formal power series `∑_k c_k X^k` on `Op N`. -/
def opRootSeries (N : ℕ) : FormalMultilinearSeries ℂ (Op N) (Op N) :=
  FormalMultilinearSeries.ofScalars (Op N) halfChooseC

theorem one_le_radius_opRootSeries : (1 : ℝ≥0∞) ≤ (opRootSeries N).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
  refine (opRootSeries N).le_radius_of_summable_norm ?_
  refine (summable_abs_halfChoose r.2 hr').of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦ ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [opRootSeries, FormalMultilinearSeries.ofScalars_norm_eq_mul, halfChooseC, Complex.norm_real,
    Real.norm_eq_abs]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  refine (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le).trans ?_
  exact max_le le_rfl ContinuousLinearMap.norm_id_le

theorem opRoot_eq_sum (T : Op N) : opRoot T = (opRootSeries N).sum (-T) :=
  (FormalMultilinearSeries.ofScalars_sum_eq (E := Op N) halfChooseC (-T)).symm

theorem analyticAt_opRoot {T : Op N} (hT : ‖T‖ < 1) : AnalyticAt ℂ opRoot T := by
  have hp := (opRootSeries N).hasFPowerSeriesOnBall
    (lt_of_lt_of_le one_pos one_le_radius_opRootSeries)
  have hmem : -T ∈ Metric.eball (0 : Op N) (opRootSeries N).radius := by
    refine lt_of_lt_of_le ?_ one_le_radius_opRootSeries
    rw [edist_zero_right, enorm_neg, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr hT
  have h1 : AnalyticAt ℂ (opRootSeries N).sum (-T) := hp.analyticAt_of_mem hmem
  have h2 : AnalyticAt ℂ (fun X : Op N ↦ -X) T := analyticAt_id.neg
  have h3 := h1.comp h2
  have hfun : opRoot = (opRootSeries N).sum ∘ (fun X : Op N ↦ -X) := funext opRoot_eq_sum
  rw [hfun]; exact h3

theorem eventually_norm_lt_one {T : Op N} (hT : ‖T‖ < 1) : ∀ᶠ X in nhds T, ‖X‖ < 1 :=
  continuous_norm.continuousAt.eventually_lt continuousAt_const hT

theorem opRoot_anticomm {T : Op N} (hT : ‖T‖ < 1) (H : Op N) :
    opRoot T * fderiv ℂ opRoot T H + fderiv ℂ opRoot T H * opRoot T = -H := by
  have hd := (analyticAt_opRoot hT).differentiableAt.hasFDerivAt
  have h2 := hd.mul' hd
  have heq : (opRoot * opRoot) =ᶠ[nhds T] fun X : Op N ↦ 1 - X :=
    (eventually_norm_lt_one hT).mono fun X hX ↦ opRoot_mul_self hX
  have h3 : HasFDerivAt (fun X : Op N ↦ 1 - X) (-ContinuousLinearMap.id ℂ (Op N)) T :=
    (hasFDerivAt_id T).const_sub 1
  have h4 := congrArg (fun L ↦ L H) (h2.unique (h3.congr_of_eventuallyEq heq))
  simpa using h4

/-!
### Matrices
-/

/-- Operator norm via `toEuclideanCLM`. -/
def opNorm (A : Matrix (Fin N) (Fin N) ℂ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

open Classical in
/-- `(1 − A)^{1/2}` (binomial series) if `opNorm A < 1`, else `0`. -/
def sqrtOneSub (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  if opNorm A < 1 then
    (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (opRoot (Matrix.toEuclideanCLM (𝕜 := ℂ) A))
  else 0

theorem sqrtOneSub_of_not_lt {A : Matrix (Fin N) (Fin N) ℂ} (h : ¬ opNorm A < 1) :
    sqrtOneSub A = 0 := by
  simp [sqrtOneSub, h]

theorem sqrtOneSub_of_lt {A : Matrix (Fin N) (Fin N) ℂ} (h : opNorm A < 1) :
    sqrtOneSub A = (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm
      (opRoot (Matrix.toEuclideanCLM (𝕜 := ℂ) A)) := by
  simp [sqrtOneSub, h]

theorem toEuclideanCLM_sqrtOneSub {A : Matrix (Fin N) (Fin N) ℂ} (h : opNorm A < 1) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (sqrtOneSub A) =
      opRoot (Matrix.toEuclideanCLM (𝕜 := ℂ) A) := by
  rw [sqrtOneSub_of_lt h, StarAlgEquiv.apply_symm_apply]

/-- `toEuclideanCLM` as a `ℂ`-linear map. -/
def toOpLin : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Op N where
  toFun A := Matrix.toEuclideanCLM (𝕜 := ℂ) A
  map_add' := map_add _
  map_smul' := map_smul _

/-- The inverse of `toEuclideanCLM` as a `ℂ`-linear map. -/
def ofOpLin : Op N →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ where
  toFun T := (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm T
  map_add' := map_add _
  map_smul' := map_smul _

theorem continuous_toEuclideanCLM :
    Continuous (fun A : Matrix (Fin N) (Fin N) ℂ ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) A) :=
  (toOpLin (N := N)).continuous_of_finiteDimensional

theorem continuous_toEuclideanCLM_symm :
    Continuous (fun T : Op N ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm T) :=
  (ofOpLin (N := N)).continuous_of_finiteDimensional

theorem isOpen_opNorm_lt_one : IsOpen {A : Matrix (Fin N) (Fin N) ℂ | opNorm A < 1} :=
  isOpen_lt (continuous_norm.comp continuous_toEuclideanCLM) continuous_const

theorem sqrtOneSub_mul_self {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1) :
    sqrtOneSub A * sqrtOneSub A = 1 - A := by
  apply EquivLike.injective (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N))
  rw [map_mul, map_sub, map_one, toEuclideanCLM_sqrtOneSub hA]
  exact opRoot_mul_self hA

theorem sqrtOneSub_commute {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1) :
    A * sqrtOneSub A = sqrtOneSub A * A := by
  apply EquivLike.injective (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N))
  rw [map_mul, map_mul, toEuclideanCLM_sqrtOneSub hA]
  exact opRoot_commute hA

theorem norm_star_op (T : Op N) : ‖star T‖ = ‖T‖ := by
  rw [ContinuousLinearMap.star_eq_adjoint]; exact LinearIsometryEquiv.norm_map _ _

theorem opNorm_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) : opNorm Aᴴ = opNorm A := by
  rw [opNorm, opNorm, ← Matrix.star_eq_conjTranspose, map_star, norm_star_op]

theorem sqrtOneSub_conjTranspose {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1) :
    (sqrtOneSub A)ᴴ = sqrtOneSub Aᴴ := by
  have hA' : opNorm Aᴴ < 1 := by rwa [opNorm_conjTranspose]
  apply EquivLike.injective (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N))
  rw [← Matrix.star_eq_conjTranspose, map_star, toEuclideanCLM_sqrtOneSub hA,
    toEuclideanCLM_sqrtOneSub hA', star_opRoot hA, ← Matrix.star_eq_conjTranspose, map_star]

theorem sqrtOneSub_isHermitian {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1)
    (hAh : A.IsHermitian) : (sqrtOneSub A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [sqrtOneSub_conjTranspose hA, hAh.eq]

/-!
### Vector bounds
-/

theorem sum_norm_mulVec_sq (M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    ∑ k, ‖(M *ᵥ v) k‖ ^ 2 =
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M (WithLp.toLp 2 v)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; rfl

theorem sum_norm_sq (v : Fin N → ℂ) :
    ∑ k, ‖v k‖ ^ 2 = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

/-- The principal-root bound, without positivity:
`‖(1 - √(1 - A)) v‖² ≤ ‖A‖_op² ‖v‖²`. -/
theorem sqrtOneSub_one_sub_bound_of_lt {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1)
    (v : Fin N → ℂ) :
    ∑ k, ‖((1 - sqrtOneSub A) *ᵥ v) k‖ ^ 2 ≤ opNorm A ^ 2 * ∑ k, ‖v k‖ ^ 2 := by
  rw [sum_norm_mulVec_sq, sum_norm_sq, ← mul_pow]
  have hM :
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N) (1 - sqrtOneSub A)‖ ≤ opNorm A := by
    rw [map_sub, map_one, toEuclideanCLM_sqrtOneSub hA]
    exact norm_one_sub_opRoot_le hA
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  exact ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N) (1 - sqrtOneSub A)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hM (norm_nonneg _))

/-- Principal-root bound (the positivity hypothesis is not needed, see
`sqrtOneSub_one_sub_bound_of_lt`). -/
theorem sqrtOneSub_one_sub_bound {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1)
    (_hpsd : A.PosSemidef) (v : Fin N → ℂ) :
    ∑ k, ‖((1 - sqrtOneSub A) *ᵥ v) k‖ ^ 2 ≤ opNorm A ^ 2 * ∑ k, ‖v k‖ ^ 2 :=
  sqrtOneSub_one_sub_bound_of_lt hA v

theorem opNorm_mul_conjTranspose_le (K : Matrix (Fin N) (Fin N) ℂ) {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ v : Fin N → ℂ, ∑ k, ‖(K *ᵥ v) k‖ ^ 2 ≤ q * ∑ k, ‖v k‖ ^ 2) :
    opNorm (K * Kᴴ) ≤ q := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℂ) K with hT
  have hK : ‖T‖ ≤ Real.sqrt q := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg q) fun x ↦ ?_
    have hx := h (WithLp.ofLp x)
    rw [sum_norm_mulVec_sq, sum_norm_sq, WithLp.toLp_ofLp] at hx
    rw [← Real.sqrt_sq (norm_nonneg (T x)), ← Real.sqrt_sq (norm_nonneg x),
      ← Real.sqrt_mul hq]
    exact Real.sqrt_le_sqrt hx
  have h2 : opNorm (K * Kᴴ) = ‖T‖ * ‖T‖ := by
    rw [opNorm, map_mul, ← Matrix.star_eq_conjTranspose, map_star, ← hT]
    exact CStarRing.norm_self_mul_star (E := Op N)
  rw [h2, ← Real.mul_self_sqrt hq]
  exact mul_self_le_mul_self (norm_nonneg _) hK

theorem opNorm_one_of_pos (hN : 0 < N) : opNorm (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [opNorm, map_one]
  exact norm_one

/-!
### Measurability
-/

theorem continuousOn_sqrtOneSub :
    ContinuousOn (sqrtOneSub (N := N)) {A | opNorm A < 1} := by
  intro A hA
  have hA' : opNorm A < 1 := hA
  have hG : ContinuousAt (fun B : Matrix (Fin N) (Fin N) ℂ ↦
      (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm
        (opRoot (Matrix.toEuclideanCLM (𝕜 := ℂ) B))) A :=
    continuous_toEuclideanCLM_symm.continuousAt.comp
      ((analyticAt_opRoot hA').continuousAt.comp continuous_toEuclideanCLM.continuousAt)
  refine (hG.congr ?_).continuousWithinAt
  filter_upwards [isOpen_opNorm_lt_one.mem_nhds hA] with B hB
  exact (sqrtOneSub_of_lt hB).symm

theorem measurable_sqrtOneSub : Measurable (sqrtOneSub (N := N)) := by
  classical
  have h : sqrtOneSub (N := N) = {A | opNorm A < 1}.piecewise sqrtOneSub (fun _ ↦ 0) := by
    funext A
    by_cases hA : opNorm A < 1
    · simp [Set.piecewise, hA]
    · simp [Set.piecewise, hA, sqrtOneSub_of_not_lt hA]
  rw [h]
  exact continuousOn_sqrtOneSub.measurable_piecewise continuousOn_const
    isOpen_opNorm_lt_one.measurableSet

/-!
### Smoothness (Frobenius normed-space structure on matrices, activated locally)
-/

section Smooth

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- `toEuclideanCLM` as a continuous `ℂ`-linear map (Frobenius norm on matrices). -/
def toOpCLM : Matrix (Fin N) (Fin N) ℂ →L[ℂ] Op N :=
  LinearMap.toContinuousLinearMap toOpLin

/-- The inverse of `toEuclideanCLM` as a continuous `ℂ`-linear map. -/
def ofOpCLM : Op N →L[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap ofOpLin

theorem toOpCLM_apply (A : Matrix (Fin N) (Fin N) ℂ) :
    toOpCLM A = Matrix.toEuclideanCLM (𝕜 := ℂ) A := rfl

theorem ofOpCLM_apply (T : Op N) : ofOpCLM T = (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm T := rfl

theorem isOpen_opNorm_lt_one_frobenius :
    IsOpen {A : Matrix (Fin N) (Fin N) ℂ | opNorm A < 1} :=
  isOpen_lt (continuous_norm.comp (toOpCLM (N := N)).continuous) continuous_const

theorem sqrtOneSub_eventuallyEq {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1) :
    (fun B ↦ ofOpCLM (opRoot (toOpCLM B))) =ᶠ[nhds A] sqrtOneSub := by
  filter_upwards [isOpen_opNorm_lt_one_frobenius.mem_nhds hA] with B hB
  exact (sqrtOneSub_of_lt hB).symm

theorem analyticAt_sqrtOneSub {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1) :
    AnalyticAt ℂ sqrtOneSub A := by
  have h : AnalyticAt ℂ (fun B ↦ ofOpCLM (opRoot (toOpCLM B))) A :=
    (ofOpCLM.analyticAt _).comp ((analyticAt_opRoot hA).comp (toOpCLM.analyticAt A))
  exact h.congr (sqrtOneSub_eventuallyEq hA)

theorem contDiffOn_sqrtOneSub : ContDiffOn ℝ ⊤ (sqrtOneSub (N := N)) {A | opNorm A < 1} := by
  have h : AnalyticOnNhd ℂ (sqrtOneSub (N := N)) {A | opNorm A < 1} :=
    fun A hA ↦ analyticAt_sqrtOneSub hA
  exact (h.restrictScalars (𝕜 := ℝ)).contDiffOn isOpen_opNorm_lt_one_frobenius.uniqueDiffOn

/-- The complex derivative of `sqrtOneSub`, transported from `Op N`. -/
def sqrtOneSubDeriv (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ →L[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  ofOpCLM ∘L (fderiv ℂ opRoot (toOpCLM A)) ∘L toOpCLM

theorem hasFDerivAt_sqrtOneSub {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1) :
    HasFDerivAt sqrtOneSub (sqrtOneSubDeriv A) A := by
  have hF : HasFDerivAt opRoot (fderiv ℂ opRoot (toOpCLM A)) (toOpCLM A) :=
    (analyticAt_opRoot hA).differentiableAt.hasFDerivAt
  have h : HasFDerivAt (fun B ↦ ofOpCLM (opRoot (toOpCLM B))) (sqrtOneSubDeriv A) A :=
    ofOpCLM.hasFDerivAt.comp A (hF.comp A toOpCLM.hasFDerivAt)
  exact h.congr_of_eventuallyEq (sqrtOneSub_eventuallyEq hA).symm

theorem hasFDerivAt_real_sqrtOneSub {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1) :
    HasFDerivAt (𝕜 := ℝ) sqrtOneSub ((sqrtOneSubDeriv A).restrictScalars ℝ) A :=
  (hasFDerivAt_sqrtOneSub hA).restrictScalars ℝ

theorem fderiv_sqrtOneSub_apply {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1)
    (H : Matrix (Fin N) (Fin N) ℂ) :
    fderiv ℝ sqrtOneSub A H = (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm
      (fderiv ℂ opRoot (Matrix.toEuclideanCLM (𝕜 := ℂ) A)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) H)) := by
  rw [(hasFDerivAt_real_sqrtOneSub hA).fderiv]
  rfl

theorem fderiv_sqrtOneSub_anticomm {A : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1)
    (H : Matrix (Fin N) (Fin N) ℂ) :
    fderiv ℝ sqrtOneSub A H * sqrtOneSub A + sqrtOneSub A * fderiv ℝ sqrtOneSub A H = -H := by
  rw [fderiv_sqrtOneSub_apply hA, sqrtOneSub_of_lt hA, ← map_mul, ← map_mul, ← map_add,
    add_comm, opRoot_anticomm hA, map_neg, StarAlgEquiv.symm_apply_apply]

/-- Conjugate transpose as a continuous `ℝ`-linear map (Frobenius norm). -/
def conjTransposeCLM : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M ↦ Mᴴ
      map_add' := fun M M' ↦ Matrix.conjTranspose_add M M'
      map_smul' := fun r M ↦ by simp [Matrix.conjTranspose_smul] }

theorem fderiv_sqrtOneSub_isHermitian {A H : Matrix (Fin N) (Fin N) ℂ} (hA : opNorm A < 1)
    (hAh : A.IsHermitian) (hH : H.IsHermitian) : (fderiv ℝ sqrtOneSub A H).IsHermitian := by
  set D := fderiv ℝ (sqrtOneSub (N := N)) A
  have hD : HasFDerivAt (sqrtOneSub (N := N)) D A :=
    (hasFDerivAt_real_sqrtOneSub hA).differentiableAt.hasFDerivAt
  have hD' : HasFDerivAt (sqrtOneSub (N := N)) D (conjTransposeCLM A) := by
    have : conjTransposeCLM A = A := hAh.eq
    rw [this]; exact hD
  have h1 : HasFDerivAt (fun B ↦ sqrtOneSub (conjTransposeCLM B)) (D ∘L conjTransposeCLM) A :=
    hD'.comp A conjTransposeCLM.hasFDerivAt
  have h2 : HasFDerivAt (fun B ↦ conjTransposeCLM (sqrtOneSub B)) (conjTransposeCLM ∘L D) A :=
    conjTransposeCLM.hasFDerivAt.comp A hD
  have heq : (fun B ↦ conjTransposeCLM (sqrtOneSub B)) =ᶠ[nhds A]
      (fun B ↦ sqrtOneSub (conjTransposeCLM B)) := by
    filter_upwards [isOpen_opNorm_lt_one_frobenius.mem_nhds hA] with B hB
    exact sqrtOneSub_conjTranspose hB
  have h3 := congrArg (fun L ↦ L H) (h1.unique (h2.congr_of_eventuallyEq heq.symm))
  have hH' : conjTransposeCLM H = H := hH.eq
  simp only [ContinuousLinearMap.comp_apply, hH'] at h3
  exact h3.symm

end Smooth

end BlockBand.Palm.ReferenceFlow
