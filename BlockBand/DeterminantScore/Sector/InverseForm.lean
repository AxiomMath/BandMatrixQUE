module

public import BlockBand.DeterminantScore.Sector.Clauses
public import BlockBand.Model.Construction.GaussianPolynomialNull
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.Normed

/-!
# The determinant locus is null, and the inverse-form derivatives

* `hermGaussian_det_eq_zero`, `ae_det_ne_zero`: for `t > 0` and **every** square `K`,
  `{x | det(K + G(x)) = 0}` is `hermGaussian m t`-null. The paper says "its zero set has
  Lebesgue measure zero". The proof shows `det(K + G(x))` is a nonzero polynomial,
  using the witness `G(x) = s·1` with `s` not a root of `charpoly(-K)`. It then applies the
  adopted `Parameters.volume_mvPolynomial_zeroSet_fintype` and
  `Parameters.pi_absolutelyContinuous_volume`.
* With `R = M⁻¹` and `E_c = coordDir c = G(e_c)` (the coordinate direction `∂_c M`), the
  inverse forms are:
  * `∂_c(1{N_-=ℓ}P²) = 1{N_-=ℓ} P² · 2Tr(R E_c)`. This holds everywhere: both sides vanish on
    `{P = 0}`.
  * `∂_c(1{N_-=ℓ}P C_ab) = 1{N_-=ℓ} P² (2Tr(R E_c) R_ab − (R E_c R)_ab)`. This holds off
    `{P = 0}`, hence almost everywhere for `t > 0`.
* The two integration-by-parts clauses are restated with these inverse-form derivatives
  (`ibp_one_inverseForm` and `ibp_inverse_inverseForm`). Both hold for every `t ≥ 0`.

The derivative of the inverse is Mathlib's `hasFDerivAt_ringInverse`, applied in the
`L^∞`-operator normed algebra structure on matrices. That structure is used only locally,
inside one proof.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open MeasureTheory ProbabilityTheory MvPolynomial Filter Matrix
open scoped NNReal Topology

variable {m : ℕ}

/-!
## The determinant locus is null
-/

theorem exists_det_ne_zero (K : Matrix (Fin m) (Fin m) ℂ) :
    ∃ x : HermCoord m → ℝ, (K + hermOfCoord x).det ≠ 0 := by
  have hp : (-K).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hfin : {s : ℝ | (-K).charpoly.eval (s : ℂ) = 0}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hp).preimage Complex.ofReal_injective.injOn
  obtain ⟨s, hs⟩ := hfin.infinite_compl.nonempty
  refine ⟨fun c => if c.1 = c.2 then s else 0, ?_⟩
  have hG : hermOfCoord (fun c : HermCoord m => if c.1 = c.2 then s else 0) =
      Matrix.scalar (Fin m) (s : ℂ) := by
    ext a b
    rw [hermOfCoord_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  rw [hG, add_comm, ← sub_neg_eq_add, ← Matrix.eval_charpoly]
  exact hs

theorem detPoly_normSq_ne_zero (K : Matrix (Fin m) (Fin m) ℂ) :
    BlockBand.Parameters.mvPolynomialNormSq (detPoly K) ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_det_ne_zero K
  intro h
  have he := BlockBand.Parameters.eval_mvPolynomialNormSq (detPoly K) x
  rw [h, map_zero] at he
  apply hx
  rw [← realEval_detPoly]
  exact Complex.normSq_eq_zero.mp he.symm

theorem hermGaussian_absolutelyContinuous {t : ℝ≥0} (ht : 0 < t) :
    hermGaussian m t ≪ (volume : Measure (HermCoord m → ℝ)) := by
  refine BlockBand.Parameters.pi_absolutelyContinuous_volume _ fun c => ?_
  refine gaussianReal_absolutelyContinuous 0 ?_
  unfold hermVariance
  split_ifs
  · exact ht.ne'
  · exact div_ne_zero ht.ne' two_ne_zero

/-- For `t > 0` the determinant locus `{det(K + G(x)) = 0}` is `hermGaussian m t`-null. -/
theorem hermGaussian_det_eq_zero {t : ℝ≥0} (ht : 0 < t) (K : Matrix (Fin m) (Fin m) ℂ) :
    hermGaussian m t {x | (K + hermOfCoord x).det = 0} = 0 := by
  have hset : {x : HermCoord m → ℝ | (K + hermOfCoord x).det = 0} =
      {x | MvPolynomial.eval x (BlockBand.Parameters.mvPolynomialNormSq (detPoly K)) = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, BlockBand.Parameters.eval_mvPolynomialNormSq,
      Complex.normSq_eq_zero]
    rw [← realEval_detPoly]
    rfl
  rw [hset]
  exact hermGaussian_absolutelyContinuous ht
    (BlockBand.Parameters.volume_mvPolynomial_zeroSet_fintype _ (detPoly_normSq_ne_zero K))

theorem ae_det_ne_zero {t : ℝ≥0} (ht : 0 < t) (K : Matrix (Fin m) (Fin m) ℂ) :
    ∀ᵐ x ∂hermGaussian m t, (K + hermOfCoord x).det ≠ 0 := by
  rw [ae_iff]
  simpa only [ne_eq, not_not] using hermGaussian_det_eq_zero ht K

/-!
## Derivatives along an affine matrix line
-/

/-- The derivative of the inverse along `A + rE` at an invertible `A`:
`d/dr (A + rE)⁻¹|₀ = -A⁻¹ E A⁻¹`. -/
theorem hasDerivAt_inv_affineLine {n : Type*} [Fintype n] [DecidableEq n]
    (A E : Matrix n n ℂ) (hA : IsUnit A.det) (a b : n) :
    HasDerivAt (fun r : ℝ => (A + (r : ℂ) • E)⁻¹ a b) (-(A⁻¹ * E * A⁻¹) a b) 0 := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have h := (hasFDerivAt_ringInverse (𝕜 := ℂ) hu.unit).restrictScalars ℝ
  have h2 : HasDerivAt (fun r : ℝ => A + (r : ℂ) • E) E 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).smul_const E).const_add A
    convert this using 1 <;> first | rfl | simp
  have h3 := h.comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
  have h4 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℂ) b).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => n → ℂ) a).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h3)
  have hinv : ((hu.unit⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = A⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← Ring.inverse_unit, IsUnit.unit_spec]
  convert h4 using 1
  · funext r
    simp only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse]
    rfl
  · simp [hinv]
    rfl

/-- `det B · adj(B)_ab = det(B)² · (B⁻¹)_ab` for every square matrix (both sides vanish when
`det B = 0`). -/
theorem det_mul_adjugate_apply {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ)
    (a b : n) : B.det * B.adjugate a b = B.det ^ 2 * B⁻¹ a b := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  by_cases hB : B.det = 0
  · simp [hB]
  · rw [Ring.inverse_eq_inv']
    field_simp

/-- The coordinate direction `E_c = ∂_c M = G(e_c)`. -/
def coordDir (c : HermCoord m) : Matrix (Fin m) (Fin m) ℂ := hermOfCoord (Pi.single c 1)

theorem hasDerivAt_realEval_line (Q : MvPolynomial (HermCoord m) ℂ) (x : HermCoord m → ℝ)
    (c : HermCoord m) :
    HasDerivAt (fun r : ℝ => realEval Q (x + r • Pi.single c 1)) (realEval (pderiv c Q) x) 0 := by
  have hl : HasDerivAt (fun r : ℝ => x + r • (Pi.single c 1 : HermCoord m → ℝ))
      (Pi.single c 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single c 1 : HermCoord m → ℝ)).const_add x
  have h := (hasFDerivAt_realEval Q x).comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  rw [realEvalFDeriv_single] at h
  exact h

theorem add_hermOfCoord_line (K : Matrix (Fin m) (Fin m) ℂ) (x : HermCoord m → ℝ)
    (c : HermCoord m) (r : ℝ) :
    K + hermOfCoord (x + r • Pi.single c 1) = (K + hermOfCoord x) + (r : ℂ) • coordDir c := by
  rw [hermOfCoord_add, hermOfCoord_smul, coordDir, add_assoc]

/-- `∂_c(P²) = P² · 2Tr(R E_c)` at **every** point (both sides vanish on `{P = 0}`). -/
theorem realEval_pderiv_detSqPoly (K : Matrix (Fin m) (Fin m) ℂ) (x : HermCoord m → ℝ)
    (c : HermCoord m) :
    realEval (pderiv c (detSqPoly K)) x =
      (K + hermOfCoord x).det ^ 2 * (2 * ((K + hermOfCoord x)⁻¹ * coordDir c).trace) := by
  set A := K + hermOfCoord x
  set E := coordDir (m := m) c
  have h1 := hasDerivAt_realEval_line (detSqPoly K) x c
  have hfun : (fun r : ℝ => realEval (detSqPoly K) (x + r • Pi.single c 1)) =
      fun r : ℝ => (A + (r : ℂ) • E).det ^ 2 := by
    funext r
    rw [realEval_detSqPoly, add_hermOfCoord_line]
  rw [hfun] at h1
  have h2 : HasDerivAt (fun r : ℝ => (A + (r : ℂ) • E).det ^ 2)
      (A.det ^ 2 * (2 * (A⁻¹ * E).trace)) 0 := by
    by_cases hA : A.det = 0
    · have hd := (BlockBand.DeterminantScore.hasDerivAt_det_realAffineLine_general A E).pow 2
      convert hd using 1
      simp [hA]
    · have hd := (BlockBand.DeterminantScore.hasDerivAt_det_realAffineLine A E
        (isUnit_iff_ne_zero.2 hA)).pow 2
      convert hd using 1
      simp only [Complex.ofReal_zero, zero_smul, add_zero, Nat.cast_ofNat]
      ring
  exact h1.unique h2

/-- `∂_c(P C_ab) = P² (2Tr(R E_c) R_ab − (R E_c R)_ab)` off `{P = 0}`. -/
theorem realEval_pderiv_detAdjPoly (K : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m)
    (x : HermCoord m → ℝ) (c : HermCoord m) (hx : (K + hermOfCoord x).det ≠ 0) :
    realEval (pderiv c (detAdjPoly K a b)) x =
      (K + hermOfCoord x).det ^ 2 *
        (2 * ((K + hermOfCoord x)⁻¹ * coordDir c).trace * (K + hermOfCoord x)⁻¹ a b -
          ((K + hermOfCoord x)⁻¹ * coordDir c * (K + hermOfCoord x)⁻¹) a b) := by
  set A := K + hermOfCoord x
  set E := coordDir (m := m) c
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hx
  have h1 := hasDerivAt_realEval_line (detAdjPoly K a b) x c
  have hfun : (fun r : ℝ => realEval (detAdjPoly K a b) (x + r • Pi.single c 1)) =
      fun r : ℝ => (A + (r : ℂ) • E).det ^ 2 * (A + (r : ℂ) • E)⁻¹ a b := by
    funext r
    rw [realEval_detAdjPoly, add_hermOfCoord_line, det_mul_adjugate_apply]
  rw [hfun] at h1
  have hd := ((BlockBand.DeterminantScore.hasDerivAt_det_realAffineLine A E hu).pow 2).mul
    (hasDerivAt_inv_affineLine A E hu a b)
  have h2 : HasDerivAt (fun r : ℝ => (A + (r : ℂ) • E).det ^ 2 * (A + (r : ℂ) • E)⁻¹ a b)
      (A.det ^ 2 * (2 * (A⁻¹ * E).trace * A⁻¹ a b - (A⁻¹ * E * A⁻¹) a b)) 0 := by
    convert hd using 1
    simp only [Complex.ofReal_zero, zero_smul, add_zero, Nat.cast_ofNat, Pi.pow_apply]
    ring
  exact h1.unique h2

/-!
## Inverse-form weak derivatives and integration by parts
-/

/-- The inverse form of `∂_c(1{N_-=ℓ}P²)`: `1{N_-=ℓ} P² · 2Tr(R E_c)`. -/
def sectorDetSqDerivInv (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (c : HermCoord m)
    (x : HermCoord m → ℝ) : ℂ :=
  if InSector K ℓ x then
    (K + hermOfCoord x).det ^ 2 * (2 * ((K + hermOfCoord x)⁻¹ * coordDir c).trace)
  else 0

/-- The inverse form of `∂_c(1{N_-=ℓ}P C_ab)`:
`1{N_-=ℓ} P² (2Tr(R E_c) R_ab − (R E_c R)_ab)`. -/
def sectorDetAdjDerivInv (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (a b : Fin m)
    (c : HermCoord m) (x : HermCoord m → ℝ) : ℂ :=
  if InSector K ℓ x then
    (K + hermOfCoord x).det ^ 2 *
      (2 * ((K + hermOfCoord x)⁻¹ * coordDir c).trace * (K + hermOfCoord x)⁻¹ a b -
        ((K + hermOfCoord x)⁻¹ * coordDir c * (K + hermOfCoord x)⁻¹) a b)
  else 0

/-- Everywhere: `∂_c(1{N_-=ℓ}P²) = 1{N_-=ℓ} P² 2Tr(R E_c)`. -/
theorem sectorDetSqDeriv_eq_inv (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (c : HermCoord m) :
    sectorDetSqDeriv K ℓ c = sectorDetSqDerivInv K ℓ c := by
  rw [sectorDetSqDeriv_eq_cutDeriv]
  funext x
  simp only [cutDeriv, sectorDetSqDerivInv, realEval_pderiv_detSqPoly]

/-- Off `{P = 0}`: `∂_c(1{N_-=ℓ}P C_ab) = 1{N_-=ℓ} P² (2Tr(R E_c) R_ab − (R E_c R)_ab)`. -/
theorem sectorDetAdjDeriv_eq_inv_of_det_ne_zero (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ)
    (a b : Fin m) (c : HermCoord m) {x : HermCoord m → ℝ} (hx : (K + hermOfCoord x).det ≠ 0) :
    sectorDetAdjDeriv K ℓ a b c x = sectorDetAdjDerivInv K ℓ a b c x := by
  rw [sectorDetAdjDeriv_eq_cutDeriv]
  simp only [cutDeriv, sectorDetAdjDerivInv, realEval_pderiv_detAdjPoly K a b x c hx]

/-- For `t > 0`, almost everywhere:
`∂_c(1{N_-=ℓ}P C_ab) = 1{N_-=ℓ} P² (2Tr(R E_c) R_ab − (R E_c R)_ab)`. -/
theorem sectorDetAdjDeriv_ae_eq_inv {t : ℝ≥0} (ht : 0 < t) (K : Matrix (Fin m) (Fin m) ℂ)
    (ℓ : ℕ) (a b : Fin m) (c : HermCoord m) :
    sectorDetAdjDeriv K ℓ a b c =ᵐ[hermGaussian m t] sectorDetAdjDerivInv K ℓ a b c := by
  filter_upwards [ae_det_ne_zero ht K] with x hx
  exact sectorDetAdjDeriv_eq_inv_of_det_ne_zero K ℓ a b c hx

/-- `E[x_c 1{N_-=ℓ}P²] = v_c E[1{N_-=ℓ} P² 2Tr(R E_c)]`, every `t ≥ 0`. -/
theorem ibp_one_inverseForm {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) (ℓ : ℕ)
    (t : ℝ≥0) (c : HermCoord m) :
    (∫ x, x c • sectorDetSq K ℓ x ∂hermGaussian m t) =
      (hermVariance m t c : ℝ) • ∫ x, sectorDetSqDerivInv K ℓ c x ∂hermGaussian m t := by
  rw [ibp_one hK ℓ t c, sectorDetSqDeriv_eq_inv]

/-- `E[x_c 1{N_-=ℓ}P² R_ab] = v_c E[1{N_-=ℓ} P² (2Tr(R E_c) R_ab − (R E_c R)_ab)]`, every
`t ≥ 0` (for `t = 0` both sides vanish since every coordinate variance is zero). -/
theorem ibp_inverse_inverseForm {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) (ℓ : ℕ)
    (t : ℝ≥0) (a b : Fin m) (c : HermCoord m) :
    (∫ x, x c • sectorDetSqInv K ℓ a b x ∂hermGaussian m t) =
      (hermVariance m t c : ℝ) • ∫ x, sectorDetAdjDerivInv K ℓ a b c x ∂hermGaussian m t := by
  rw [ibp_inverse hK ℓ t a b c]
  rcases eq_zero_or_pos t with h0 | ht
  · have hv : (hermVariance m t c : ℝ) = 0 := by
      subst h0
      unfold hermVariance
      split_ifs <;> simp
    rw [hv, zero_smul, zero_smul]
  · rw [integral_congr_ae (sectorDetAdjDeriv_ae_eq_inv ht K ℓ a b c)]

end BlockBand.DeterminantScore.Sector
