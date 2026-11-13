module

public import BlockBand.DeterminantScore.Sector.InverseForm
public import BlockBand.DeterminantScore.Sector.GUELaw
public import BlockBand.DeterminantScore.PhysicalColumnGaussian

/-!
# The exact sector loop identity

On each complete sector, `⟨Tr G_d R⟩_θ = 2t⟨Tr R²⟩_θ − t⟨(Tr R)²⟩_θ`.

* `sum_coordDir_contract`: the `GUE_m(t)` covariance in the real coordinates,
  `Σ_c v_c (E_c)_ij (E_c)_kl = t δ_il δ_jk` (`E_c = coordDir c`, `v_c = hermVariance m t c`);
  its consequences `Σ_c v_c Tr(A E_c)Tr(B E_c) = t Tr(BA)`, `Σ_c v_c E_c B E_c = t (Tr B) 1`;
* `sum_loop_contraction`: the two contractions (`∂R = −R(∂G)R` contributes `−t(Tr R)²`;
  differentiating `det(M)²` contributes `2t Tr R²`), pointwise;
* `integral_sector_loop`: the identity in coordinates, from the sector integration-by-parts
  corollary `Sector.ibp_inverse_inverseForm` (inverse insertion), summed against
  `Tr(G R) = Σ_c x_c Σ_{ab} (E_c)_ab R_ba`;
* `gue_sector_loop`: the same under `GUE_m(t)` (`map_hermOfCoord_hermGaussian`) with the real
  sector weight `secW n ℓ (K + G) = |det M|² 1{N_-(M) + n = ℓ}`, together with the
  integrability of the five sector integrands (`1`, `Re Tr R`, `(Re Tr R)²`, `Re Tr R²`,
  `Re Tr(GR)`); for Hermitian `K` and `t > 0`. All quantities are unnormalized (the
  normalization by `𝔷_ℓ` is done in `realLoopError_mul_sectorZ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.RealLoop

open MeasureTheory Matrix
open BlockBand.DeterminantScore.Sector
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.DeterminantScore.PhysicalColumn
open scoped NNReal

variable {m : ℕ}

theorem coordDir_apply (c : HermCoord m) (i j : Fin m) :
    coordDir c i j = if i = j then (if c = (i, i) then 1 else 0)
      else if i < j then (if c = (i, j) then 1 else 0) + (if c = (j, i) then Complex.I else 0)
      else (if c = (j, i) then 1 else 0) - (if c = (i, j) then Complex.I else 0) := by
  simp only [coordDir, hermOfCoord_apply, Pi.single_apply, eq_comm (a := c)]
  split_ifs <;> simp

theorem sum_coordDir_contract (t : ℝ≥0) (i j k l : Fin m) :
    ∑ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) * (coordDir c i j * coordDir c k l) =
      if i = l ∧ j = k then ((t : ℝ) : ℂ) else 0 := by
  simp only [coordDir_apply]
  by_cases h1 : i = j <;> by_cases h2 : i < j <;> by_cases h3 : k = l <;> by_cases h4 : k < l <;>
  simp only [h1, h2, h3, h4, ite_true, ite_false,
      mul_add, add_mul, mul_sub, sub_mul,
      ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, Prod.mk.injEq, hermVariance] <;>
  split_ifs <;>
  first
    | (exfalso; simp only [Fin.ext_iff, Fin.lt_def, not_and, not_lt] at *; omega)
    | (push_cast; ring_nf; done)
    | (push_cast; ring_nf; simp only [Complex.I_sq]; ring)

/-- `Σ_c v_c (E_c)_ij Σ ... `: swapping the coordinate sum inside a double sum. -/
theorem sum_coordDir_contract_two (t : ℝ≥0) (F : Fin m → Fin m → ℂ) (i l : Fin m) :
    ∑ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) * ∑ j, ∑ k, F j k * (coordDir c i j * coordDir c k l) =
      if i = l then ((t : ℝ) : ℂ) * ∑ j, F j j else 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ j : Fin m, ∑ c : HermCoord m, ∑ k, ((hermVariance m t c : ℝ) : ℂ) *
      (F j k * (coordDir c i j * coordDir c k l)) =
      ∑ k, F j k * (if i = l ∧ j = k then ((t : ℝ) : ℂ) else 0) := by
    intro j
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sum_coordDir_contract t i j k l, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [Finset.sum_congr rfl fun j _ => h j]
  split_ifs with hil
  · simp [hil, mul_ite, mul_comm]
  · simp [hil]

theorem sum_trace_smul_coordDir (t : ℝ≥0) (A : Matrix (Fin m) (Fin m) ℂ) :
    ∑ c : HermCoord m, (((hermVariance m t c : ℝ) : ℂ) * (A * coordDir c).trace) • coordDir c =
      ((t : ℝ) : ℂ) • A := by
  ext k l
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply]
  have h1 : ∀ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) *
      (∑ i, ∑ j, A i j * coordDir c j i) * coordDir c k l =
      ∑ i, ∑ j, ((hermVariance m t c : ℝ) : ℂ) * (A i j * (coordDir c j i * coordDir c k l)) := by
    intro c
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_comm]
  have h2 : ∀ i : Fin m, ∑ c : HermCoord m, ∑ j, ((hermVariance m t c : ℝ) : ℂ) *
      (A i j * (coordDir c j i * coordDir c k l)) =
      ∑ j, A i j * (if j = l ∧ i = k then ((t : ℝ) : ℂ) else 0) := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_coordDir_contract t j i k l, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [Finset.sum_congr rfl fun i _ => h2 i]
  simp [mul_ite, ite_and, mul_comm]

/-- `Σ_c v_c E_c B E_c = t (Tr B) 1`. -/
theorem sum_coordDir_mul_mul (t : ℝ≥0) (B : Matrix (Fin m) (Fin m) ℂ) :
    ∑ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) • (coordDir c * B * coordDir c) =
      (((t : ℝ) : ℂ) * B.trace) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  ext i l
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  have h1 : ∀ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) *
      ∑ k, (∑ j, coordDir c i j * B j k) * coordDir c k l =
      ((hermVariance m t c : ℝ) : ℂ) * ∑ j, ∑ k, B j k * (coordDir c i j * coordDir c k l) := by
    intro c
    congr 1
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  refine (sum_coordDir_contract_two t (fun j k => B j k) i l).trans ?_
  simp [Matrix.one_apply, Matrix.trace, mul_ite]

/-- `Σ_c v_c Tr(A E_c) Tr(B E_c) = t Tr(B A)`. -/
theorem sum_trace_mul_trace (t : ℝ≥0) (A B : Matrix (Fin m) (Fin m) ℂ) :
    ∑ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) * ((A * coordDir c).trace *
      (B * coordDir c).trace) = ((t : ℝ) : ℂ) * (B * A).trace := by
  have h := congrArg (fun X => (B * X).trace) (sum_trace_smul_coordDir t A)
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul] at h
  rw [← h]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- `Σ_c v_c Tr(A E_c B E_c) = t Tr A Tr B`. -/
theorem sum_trace_mul_coordDir_mul (t : ℝ≥0) (A B : Matrix (Fin m) (Fin m) ℂ) :
    ∑ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) * (A * (coordDir c * B * coordDir c)).trace =
      ((t : ℝ) : ℂ) * (A.trace * B.trace) := by
  have h := congrArg (fun X => (A * X).trace) (sum_coordDir_mul_mul t B)
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_one] at h
  rw [h]; ring

theorem sum_mul_apply_eq_trace (A X : Matrix (Fin m) (Fin m) ℂ) :
    ∑ a, ∑ b, A a b * X b a = (A * X).trace := by
  simp [Matrix.trace, Matrix.mul_apply]

/-- The pointwise contraction of the sector loop identity: for every matrix `R`,
`Σ_c v_c Σ_{a,b} (E_c)_ab (2Tr(R E_c) R_ba − (R E_c R)_ba) = 2t Tr R² − t (Tr R)²`. -/
theorem sum_loop_contraction (t : ℝ≥0) (R : Matrix (Fin m) (Fin m) ℂ) :
    ∑ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) * ∑ a, ∑ b, coordDir c a b *
      (2 * (R * coordDir c).trace * R b a - (R * coordDir c * R) b a) =
      2 * ((t : ℝ) : ℂ) * (R * R).trace - ((t : ℝ) : ℂ) * R.trace ^ 2 := by
  have h1 : ∀ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) * ∑ a, ∑ b, coordDir c a b *
      (2 * (R * coordDir c).trace * R b a - (R * coordDir c * R) b a) =
      2 * (((hermVariance m t c : ℝ) : ℂ) * ((R * coordDir c).trace * (R * coordDir c).trace)) -
        ((hermVariance m t c : ℝ) : ℂ) * (R * (coordDir c * R * coordDir c)).trace := by
    intro c
    have e : ∑ a, ∑ b, coordDir c a b *
        (2 * (R * coordDir c).trace * R b a - (R * coordDir c * R) b a) =
        2 * (R * coordDir c).trace * ∑ a, ∑ b, coordDir c a b * R b a -
          ∑ a, ∑ b, coordDir c a b * (R * coordDir c * R) b a := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e, sum_mul_apply_eq_trace, sum_mul_apply_eq_trace, Matrix.trace_mul_comm (coordDir c) R,
      show coordDir c * (R * coordDir c * R) = (coordDir c * R * coordDir c) * R by
        simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm _ R]
    ring
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_trace_mul_coordDir_mul, sum_trace_mul_trace]
  ring

/-!
## The loop identity in the Gaussian coordinates
-/

theorem hermOfCoord_eq_sum (x : HermCoord m → ℝ) :
    hermOfCoord x = ∑ c : HermCoord m, (x c : ℂ) • coordDir c := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, coordDir_apply, hermOfCoord_apply]
  split_ifs <;> simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
    Finset.sum_ite_eq', mul_comm]

theorem trace_hermOfCoord_mul (x : HermCoord m → ℝ) (R : Matrix (Fin m) (Fin m) ℂ) :
    (hermOfCoord x * R).trace = ∑ c : HermCoord m, (x c : ℂ) * ∑ a, ∑ b, coordDir c a b * R b a := by
  rw [hermOfCoord_eq_sum, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, sum_mul_apply_eq_trace]

theorem inv_eq_inv_det_smul (A : Matrix (Fin m) (Fin m) ℂ) : A⁻¹ = (A.det)⁻¹ • A.adjugate := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

theorem realEval_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (HermCoord m) ℂ)
    (x : HermCoord m → ℝ) : realEval (∑ i ∈ s, f i) x = ∑ i ∈ s, realEval (f i) x := by
  simp [realEval, map_sum]

/-- `Σ_{a,b} adj_ab adj_ba` and `(Σ_a adj_aa)²` as polynomials. -/
def adjSqTracePoly (K : Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (HermCoord m) ℂ :=
  ∑ a, ∑ b, adjPoly K a b * adjPoly K b a

def adjTraceSqPoly (K : Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (HermCoord m) ℂ :=
  (∑ a, adjPoly K a a) ^ 2

theorem cut_adjSqTracePoly_ae {t : ℝ≥0} (ht : 0 < t) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) :
    cut K ℓ (adjSqTracePoly K) =ᵐ[hermGaussian m t] fun x => sectorDetSq K ℓ x *
      ((K + hermOfCoord x)⁻¹ * (K + hermOfCoord x)⁻¹).trace := by
  filter_upwards [ae_det_ne_zero ht K] with x hx
  simp only [cut, sectorDetSq, adjSqTracePoly]
  split_ifs
  · simp only [realEval_sum, realEval_mul, realEval_adjPoly, sum_mul_apply_eq_trace]
    rw [inv_eq_inv_det_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
      smul_eq_mul]
    field_simp
  · simp

theorem cut_adjTraceSqPoly_ae {t : ℝ≥0} (ht : 0 < t) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) :
    cut K ℓ (adjTraceSqPoly K) =ᵐ[hermGaussian m t] fun x => sectorDetSq K ℓ x *
      ((K + hermOfCoord x)⁻¹).trace ^ 2 := by
  filter_upwards [ae_det_ne_zero ht K] with x hx
  simp only [cut, sectorDetSq, adjTraceSqPoly]
  split_ifs
  · simp only [realEval_pow, realEval_sum, realEval_adjPoly]
    rw [inv_eq_inv_det_smul, Matrix.trace_smul, smul_eq_mul]
    simp only [Matrix.trace, Matrix.diag]
    field_simp
  · simp

section Loop

theorem integral_triple_sum {μ : Measure (HermCoord m → ℝ)} (g : HermCoord m → Fin m → Fin m → ℂ)
    (f : HermCoord m → Fin m → Fin m → (HermCoord m → ℝ) → ℂ)
    (hf : ∀ c a b, Integrable (f c a b) μ) :
    (∫ x, ∑ c, ∑ a, ∑ b, g c a b * f c a b x ∂μ) = ∑ c, ∑ a, ∑ b, g c a b * ∫ x, f c a b x ∂μ := by
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun b _ => (hf c a b).const_mul _]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hf c a b).const_mul _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (hf c a b).const_mul _]
  exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _

variable {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) (ℓ : ℕ) {t : ℝ≥0} (ht : 0 < t)
include hK ht

theorem integrable_sectorDetSq_mul_trace_sq :
    Integrable (fun x => sectorDetSq K ℓ x *
      ((K + hermOfCoord x)⁻¹ * (K + hermOfCoord x)⁻¹).trace) (hermGaussian m t) :=
  (integrable_cut hK ℓ (adjSqTracePoly K) (hermVariance m t)).congr
    (cut_adjSqTracePoly_ae ht K ℓ)

theorem integrable_sectorDetSq_mul_trace_pow :
    Integrable (fun x => sectorDetSq K ℓ x * ((K + hermOfCoord x)⁻¹).trace ^ 2)
      (hermGaussian m t) :=
  (integrable_cut hK ℓ (adjTraceSqPoly K) (hermVariance m t)).congr
    (cut_adjTraceSqPoly_ae ht K ℓ)

omit hK ht in
theorem sectorDetSq_mul_trace_hermOfCoord (x : HermCoord m → ℝ) :
    sectorDetSq K ℓ x * (hermOfCoord x * (K + hermOfCoord x)⁻¹).trace =
      ∑ c : HermCoord m, ∑ a, ∑ b, coordDir c a b * (x c • sectorDetSqInv K ℓ b a x) := by
  rw [trace_hermOfCoord_mul]
  simp only [sectorDetSq, sectorDetSqInv]
  split_ifs
  · simp only [Finset.mul_sum, Complex.real_smul]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by ring
  · simp

omit ht in
theorem integrable_coord_smul_sectorDetSqInv (c : HermCoord m) (a b : Fin m) :
    Integrable (fun x => x c • sectorDetSqInv K ℓ b a x) (hermGaussian m t) := by
  rw [sectorDetSqInv_eq]
  exact (integrable_detAdj hK ℓ t b a c).2.2

omit ht in
theorem integrable_sectorDetSq_mul_trace_hermOfCoord :
    Integrable (fun x => sectorDetSq K ℓ x * (hermOfCoord x * (K + hermOfCoord x)⁻¹).trace)
      (hermGaussian m t) := by
  simp only [sectorDetSq_mul_trace_hermOfCoord ℓ]
  exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun b _ =>
      (integrable_coord_smul_sectorDetSqInv hK ℓ c a b).const_mul _

omit ht in
theorem integrable_sectorDetSq_mul_trace :
    Integrable (fun x => sectorDetSq K ℓ x * ((K + hermOfCoord x)⁻¹).trace) (hermGaussian m t) := by
  have h : (fun x => sectorDetSq K ℓ x * ((K + hermOfCoord x)⁻¹).trace) =
      fun x => ∑ a, sectorDetSqInv K ℓ a a x := by
    funext x
    simp only [sectorDetSq, sectorDetSqInv, Matrix.trace, Matrix.diag]
    split_ifs
    · rw [Finset.mul_sum]
    · simp
  rw [h]
  exact integrable_finsetSum _ fun a _ => by
    rw [sectorDetSqInv_eq]; exact (integrable_detAdj hK ℓ t a a (a, a)).1

/-- **The sector loop identity** in the real coordinates of `G_m(t)`, unnormalized:
`E[1{N_-=ℓ}P² Tr(G R)] = 2t E[1{N_-=ℓ}P² Tr R²] - t E[1{N_-=ℓ}P² (Tr R)²]`. -/
theorem integral_sector_loop :
    (∫ x, sectorDetSq K ℓ x * (hermOfCoord x * (K + hermOfCoord x)⁻¹).trace ∂hermGaussian m t) =
      2 * ((t : ℝ) : ℂ) * (∫ x, sectorDetSq K ℓ x *
          ((K + hermOfCoord x)⁻¹ * (K + hermOfCoord x)⁻¹).trace ∂hermGaussian m t) -
        ((t : ℝ) : ℂ) * ∫ x, sectorDetSq K ℓ x * ((K + hermOfCoord x)⁻¹).trace ^ 2
          ∂hermGaussian m t := by
  set μ := hermGaussian m t
  have hc := integrable_coord_smul_sectorDetSqInv hK ℓ (t := t)
  have hd : ∀ (c : HermCoord m) (a b : Fin m), Integrable (sectorDetAdjDerivInv K ℓ b a c) μ :=
    fun c a b => (integrable_detAdj hK ℓ t b a c).2.1.congr (sectorDetAdjDeriv_ae_eq_inv ht K ℓ b a c)
  have p1 : (fun x => sectorDetSq K ℓ x * (hermOfCoord x * (K + hermOfCoord x)⁻¹).trace) =
      fun x => ∑ c : HermCoord m, ∑ a, ∑ b, coordDir c a b * (x c • sectorDetSqInv K ℓ b a x) :=
    funext (sectorDetSq_mul_trace_hermOfCoord ℓ)
  have p2 : ∀ x, ∑ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) *
      ∑ a, ∑ b, coordDir c a b * sectorDetAdjDerivInv K ℓ b a c x =
      2 * ((t : ℝ) : ℂ) * (sectorDetSq K ℓ x *
          ((K + hermOfCoord x)⁻¹ * (K + hermOfCoord x)⁻¹).trace) -
        ((t : ℝ) : ℂ) * (sectorDetSq K ℓ x * ((K + hermOfCoord x)⁻¹).trace ^ 2) := by
    intro x
    simp only [sectorDetAdjDerivInv, sectorDetSq]
    split_ifs
    · set P := (K + hermOfCoord x).det
      set R := (K + hermOfCoord x)⁻¹
      have e : ∀ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) *
          ∑ a, ∑ b, coordDir c a b * (P ^ 2 * (2 * (R * coordDir c).trace * R b a -
            (R * coordDir c * R) b a)) =
          P ^ 2 * (((hermVariance m t c : ℝ) : ℂ) * ∑ a, ∑ b, coordDir c a b *
            (2 * (R * coordDir c).trace * R b a - (R * coordDir c * R) b a)) := by
        intro c
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [Finset.sum_congr rfl fun c _ => e c, ← Finset.mul_sum, sum_loop_contraction]
      ring
    · simp
  have q1 := integral_triple_sum (μ := μ) (fun c a b => coordDir c a b)
    (fun c a b x => x c • sectorDetSqInv K ℓ b a x) hc
  have q2 := integral_triple_sum (μ := μ)
    (fun c a b => ((hermVariance m t c : ℝ) : ℂ) * coordDir c a b)
    (fun c a b x => sectorDetAdjDerivInv K ℓ b a c x) hd
  have q3 : ∀ x, ∑ c : HermCoord m, ∑ a, ∑ b, ((hermVariance m t c : ℝ) : ℂ) * coordDir c a b *
      sectorDetAdjDerivInv K ℓ b a c x = ∑ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) *
      ∑ a, ∑ b, coordDir c a b * sectorDetAdjDerivInv K ℓ b a c x := by
    intro x
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [q3] at q2
  calc _ = ∑ c : HermCoord m, ∑ a, ∑ b, coordDir c a b *
        ∫ x, x c • sectorDetSqInv K ℓ b a x ∂μ := by rw [p1]; exact q1
    _ = ∫ x, ∑ c : HermCoord m, ((hermVariance m t c : ℝ) : ℂ) *
        ∑ a, ∑ b, coordDir c a b * sectorDetAdjDerivInv K ℓ b a c x ∂μ := by
        rw [q2]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        rw [ibp_inverse_inverseForm hK ℓ t b a c, Complex.real_smul]
        ring
    _ = _ := by
        simp only [p2]
        rw [integral_sub ((integrable_sectorDetSq_mul_trace_sq hK ℓ ht).const_mul _)
          ((integrable_sectorDetSq_mul_trace_pow hK ℓ ht).const_mul _),
          integral_const_mul, integral_const_mul]

end Loop

/-!
## Transfer to the matrix law `GUE_m(t)` with the real sector weight
-/

theorem measurable_inv_add (K : Matrix (Fin m) (Fin m) ℂ) :
    Measurable fun G : Matrix (Fin m) (Fin m) ℂ => (K + G)⁻¹ := by
  have h : Measurable fun M : Matrix (Fin m) (Fin m) ℂ => M⁻¹ :=
    measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b =>
      BlockBand.DeterminantScore.ExactScore.measurable_inv_apply a b
  exact h.comp (measurable_const_add K)

theorem re_trace_mul_of_isHermitian {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (A * B).trace.im = 0 := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.1 h

theorem trace_im_of_isHermitian {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) :
    A.trace.im = 0 := by
  have h : star A.trace = A.trace := by rw [← Matrix.trace_conjTranspose, hA.eq]
  exact Complex.conj_eq_iff_im.1 h

theorem secW_mul_re {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) {n ℓ : ℕ} (hn : n ≤ ℓ)
    (x : HermCoord m → ℝ) {F : ℂ} (hF : F.im = 0) :
    secW n ℓ (K + hermOfCoord x) * F.re = (sectorDetSq K (ℓ - n) x * F).re := by
  have him := BlockBand.Angular.DetFactor.det_im_eq_zero (hK.add (isHermitian_hermOfCoord x))
  simp only [secW, sectorDetSq]
  by_cases hs : InSector K (ℓ - n) x
  · have hx' : negativeCount (K + hermOfCoord x) + n = ℓ := by
      unfold InSector at hs; omega
    simp only [hx', hs, ↓reduceIte, mul_one]
    simp [Complex.mul_re, pow_two, Complex.normSq_apply, him, hF]
  · have hx' : ¬ negativeCount (K + hermOfCoord x) + n = ℓ := by
      unfold InSector at hs; omega
    simp [hx', hs]

/-- Transfer of a sector observable from `GUE_m(t)` to the coordinates. -/
theorem gue_transfer {n ℓ : ℕ} (K : Matrix (Fin m) (Fin m) ℂ) (t : ℝ≥0)
    {f : Matrix (Fin m) (Fin m) ℂ → ℝ} (hf : Measurable f) {F : (HermCoord m → ℝ) → ℂ}
    (hF : Integrable F (hermGaussian m t))
    (hpt : ∀ x, secW n ℓ (K + hermOfCoord x) * f (hermOfCoord x) = (F x).re) :
    Integrable (fun G => secW n ℓ (K + G) * f G) (gueMeasure (Fin m) t) ∧
      (∫ G, secW n ℓ (K + G) * f G ∂gueMeasure (Fin m) t) = (∫ x, F x ∂hermGaussian m t).re := by
  have hm : Measurable fun G : Matrix (Fin m) (Fin m) ℂ => secW n ℓ (K + G) * f G :=
    ((measurable_secW n ℓ).comp (measurable_const_add K)).mul hf
  have hcomp : (fun G : Matrix (Fin m) (Fin m) ℂ => secW n ℓ (K + G) * f G) ∘ hermOfCoord =
      fun x => (F x).re := funext hpt
  rw [← map_hermOfCoord_hermGaussian]
  refine ⟨?_, ?_⟩
  · rw [integrable_map_measure hm.aestronglyMeasurable
      continuous_hermOfCoord.measurable.aemeasurable, hcomp]
    exact hF.re
  · rw [integral_map continuous_hermOfCoord.measurable.aemeasurable hm.aestronglyMeasurable]
    change ∫ x, ((fun G : Matrix (Fin m) (Fin m) ℂ => secW n ℓ (K + G) * f G) ∘ hermOfCoord) x
      ∂hermGaussian m t = _
    rw [hcomp]
    exact integral_re hF

theorem secW_eq_zero_of_lt {n ℓ : ℕ} (h : ¬ n ≤ ℓ) (M : Matrix (Fin m) (Fin m) ℂ) :
    secW n ℓ M = 0 := by
  have : ¬ negativeCount M + n = ℓ := by omega
  simp [secW, this]

/-- **The sector loop identity** for `M = K + G`, `G ~ GUE_m(t)`, with the real sector weight
`w = |det M|² 1{N_-(M) + n = ℓ}` (unnormalized): the five sector integrands are integrable and
`E[w Re Tr(GR)] = 2t E[w Re Tr R²] - t E[w (Re Tr R)²]`. -/
theorem gue_sector_loop {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) (n ℓ : ℕ)
    {t : ℝ≥0} (ht : 0 < t) :
    Integrable (fun G => secW n ℓ (K + G)) (gueMeasure (Fin m) t) ∧
    Integrable (fun G => secW n ℓ (K + G) * ((K + G)⁻¹).trace.re) (gueMeasure (Fin m) t) ∧
    Integrable (fun G => secW n ℓ (K + G) * ((K + G)⁻¹).trace.re ^ 2) (gueMeasure (Fin m) t) ∧
    Integrable (fun G => secW n ℓ (K + G) * ((K + G)⁻¹ * (K + G)⁻¹).trace.re)
      (gueMeasure (Fin m) t) ∧
    Integrable (fun G => secW n ℓ (K + G) * (G * (K + G)⁻¹).trace.re) (gueMeasure (Fin m) t) ∧
    (∫ G, secW n ℓ (K + G) * (G * (K + G)⁻¹).trace.re ∂gueMeasure (Fin m) t) =
      2 * (t : ℝ) * (∫ G, secW n ℓ (K + G) * ((K + G)⁻¹ * (K + G)⁻¹).trace.re
          ∂gueMeasure (Fin m) t) -
        (t : ℝ) * ∫ G, secW n ℓ (K + G) * ((K + G)⁻¹).trace.re ^ 2 ∂gueMeasure (Fin m) t := by
  by_cases hn : n ≤ ℓ
  swap
  · simp only [secW_eq_zero_of_lt hn, zero_mul, integral_zero, mul_zero, sub_zero]
    exact ⟨integrable_zero _ _ _, integrable_zero _ _ _, integrable_zero _ _ _,
      integrable_zero _ _ _, integrable_zero _ _ _, trivial⟩
  set ℓ' := ℓ - n
  have hinv := measurable_inv_add K
  have hHx : ∀ x : HermCoord m → ℝ, (K + hermOfCoord x).IsHermitian :=
    fun x => hK.add (isHermitian_hermOfCoord x)
  have hRx : ∀ x : HermCoord m → ℝ, ((K + hermOfCoord x)⁻¹).IsHermitian := fun x => (hHx x).inv
  have hS : Integrable (sectorDetSq K ℓ') (hermGaussian m t) := by
    rw [sectorDetSq_eq_cut, hermGaussian_eq]; exact integrable_cut hK ℓ' _ _
  have t1 := gue_transfer (n := n) (ℓ := ℓ) K t (f := fun _ => (1 : ℝ)) measurable_const hS
    (fun x => by
      have := secW_mul_re hK hn x (F := 1) (by simp)
      simpa using this)
  have t2 := gue_transfer (n := n) (ℓ := ℓ) K t (f := fun G => ((K + G)⁻¹).trace.re)
    ((Complex.continuous_re.comp (continuous_id.matrix_trace)).measurable.comp hinv)
    (integrable_sectorDetSq_mul_trace hK ℓ')
    (fun x => secW_mul_re hK hn x (trace_im_of_isHermitian (hRx x)))
  have t3 := gue_transfer (n := n) (ℓ := ℓ) K t (f := fun G => ((K + G)⁻¹).trace.re ^ 2)
    (((Complex.continuous_re.comp (continuous_id.matrix_trace)).pow 2).measurable.comp hinv)
    (integrable_sectorDetSq_mul_trace_pow hK ℓ' ht)
    (fun x => by
      have him := trace_im_of_isHermitian (hRx x)
      have := secW_mul_re hK hn x (F := ((K + hermOfCoord x)⁻¹).trace ^ 2)
        (by simp [pow_two, Complex.mul_im, him])
      rw [← this]
      simp [pow_two, Complex.mul_re, him])
  have t4 := gue_transfer (n := n) (ℓ := ℓ) K t
    (f := fun G => ((K + G)⁻¹ * (K + G)⁻¹).trace.re)
    ((Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_id).matrix_trace)).measurable.comp
      hinv)
    (integrable_sectorDetSq_mul_trace_sq hK ℓ' ht)
    (fun x => secW_mul_re hK hn x (re_trace_mul_of_isHermitian (hRx x) (hRx x)))
  have hm5 : Measurable fun G : Matrix (Fin m) (Fin m) ℂ => (G * (K + G)⁻¹).trace.re := by
    have e : (fun G : Matrix (Fin m) (Fin m) ℂ => (G * (K + G)⁻¹).trace.re) =
        fun G => ∑ a, ∑ b, (G a b * (K + G)⁻¹ b a).re := by
      funext G
      simp [Matrix.trace, Matrix.mul_apply, Complex.re_sum]
    rw [e]
    refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
    have h1 : Measurable fun G : Matrix (Fin m) (Fin m) ℂ => G a b :=
      (measurable_pi_apply b).comp (measurable_pi_apply a)
    have h2 : Measurable fun G : Matrix (Fin m) (Fin m) ℂ => (K + G)⁻¹ b a :=
      (BlockBand.DeterminantScore.ExactScore.measurable_inv_apply b a).comp
        (measurable_const_add K)
    exact Complex.measurable_re.comp (h1.mul h2)
  have t5 := gue_transfer (n := n) (ℓ := ℓ) K t (f := fun G => (G * (K + G)⁻¹).trace.re) hm5
    (integrable_sectorDetSq_mul_trace_hermOfCoord hK ℓ')
    (fun x => secW_mul_re hK hn x
      (re_trace_mul_of_isHermitian (isHermitian_hermOfCoord x) (hRx x)))
  simp only [mul_one] at t1
  refine ⟨t1.1, t2.1, t3.1, t4.1, t5.1, ?_⟩
  rw [t5.2, t4.2, t3.2, integral_sector_loop hK ℓ' ht]
  simp [Complex.sub_re, Complex.mul_re]

end BlockBand.DeterminantScore.RealLoop