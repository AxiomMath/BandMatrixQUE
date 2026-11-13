module

public import BlockBand.Endpoints.Response.ResponseVarianceGaussianMoments
public import BlockBand.Endpoints.Response.ResponseVarianceGaussianInvariance

/-!
# The Gaussian variance lower bound

Law: `h ~ circularVectorLaw ι` (standard complex Gaussian, `E hh* = I`; real and imaginary parts
independent `N(0, 1/2)`). Statement: for every finite `ι`, Hermitian `B`, and `A` with
`A - B ⪰ 0`, `A + B ⪰ 0` (`IsSandwichedOn B A`), with `X = h*Bh`, `Y = h*Ah` (`quadForm`) and
the default `0/0 = 0` on the null event `Y = 0`:
`(Re Tr B)² + ‖B‖²_HS ≤ 432 (Re Tr A)² E|X/Y|²`.

Proof. Diagonalize `B = U diag(λ) U*` and use the unitary invariance of the law
(`rvG_circularVectorLaw_map_unitary`): `X` has the law of `Σ_k λ_k |h_k|²`
`= Tr B + Σ_{k,j} λ_k (r_{k,j}² - 1/2)`, an independent centered real chaos. Hence
`E X² = M := (Tr B)² + Σ λ_k² = (Tr B)² + ‖B‖²_HS` and `E X⁴ ≤ 216 M²`
(`rvG_pi_chaos_moments`, `rvG_shift_moments`); the same bound for `A ⪰ 0` gives
`E Y⁴ ≤ 864 (Tr A)⁴`. Then `E X²Y² ≤ 432 M (Tr A)²` (AM–GM with an optimized weight) and the
Cauchy–Schwarz step `X² = (X/Y)(XY) ≤ (s (X/Y)² + X²Y²/s)/2` pointwise (`X = 0` where `Y = 0` by
the sandwich) gives `M ≤ 432 (Tr A)² E(X/Y)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

/-!
### Diagonal quadratic forms
-/

/-- `Σ_k λ_k |h_k|²`. -/
def rvG_diag {ι : Type} [Fintype ι] (l : ι → ℝ) (h : ι → ℂ) : ℝ :=
  ∑ k, l k * Complex.normSq (h k)

theorem rvG_diag_cplx {ι : Type} [Fintype ι] (l : ι → ℝ) (r : ι × Fin 2 → ℝ) :
    rvG_diag l (rvG_cplx r) =
      ∑ k, l k + ∑ p : ι × Fin 2, l p.1 * (r p ^ 2 - ((1 / 2 : ℝ≥0) : ℝ)) := by
  simp only [rvG_diag, rvG_cplx, Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.normSq_apply]
  ring

theorem rvG_measurable_diag {ι : Type} [Fintype ι] (l : ι → ℝ) :
    Measurable (rvG_diag l) := by
  unfold rvG_diag
  fun_prop

/-- Moments of the diagonal form under the circular law: `E D² = (Σλ)² + Σλ²`,
`E D⁴ ≤ 216 ((Σλ)² + Σλ²)²`. -/
theorem rvG_diag_moments {ι : Type} [Fintype ι] [DecidableEq ι] (l : ι → ℝ) :
    Integrable (fun h => rvG_diag l h ^ 4) (circularVectorLaw ι) ∧
      Integrable (fun h => rvG_diag l h ^ 2) (circularVectorLaw ι) ∧
      ∫ h, rvG_diag l h ^ 2 ∂circularVectorLaw ι = (∑ k, l k) ^ 2 + ∑ k, l k ^ 2 ∧
      ∫ h, rvG_diag l h ^ 4 ∂circularVectorLaw ι ≤
        216 * ((∑ k, l k) ^ 2 + ∑ k, l k ^ 2) ^ 2 := by
  have hlaw : circularVectorLaw ι =
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map rvG_cplx := rfl
  set P := Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)
  have hc : AEMeasurable (rvG_cplx (ι := ι)) P := rvG_continuous_cplx.measurable.aemeasurable
  obtain ⟨c4, c1, c2, c4le⟩ := rvG_pi_chaos_moments (κ := ι × Fin 2) (1 / 2 : ℝ≥0)
    (fun p => l p.1)
  have hZm : AEStronglyMeasurable (fun r : ι × Fin 2 → ℝ =>
      ∑ p : ι × Fin 2, l p.1 * (r p ^ 2 - ((1 / 2 : ℝ≥0) : ℝ))) P :=
    (Finset.measurable_sum _ fun p _ => by fun_prop).aestronglyMeasurable
  obtain ⟨s4, s2, s2eq, s4le⟩ := rvG_shift_moments hZm c4 c1 (∑ k, l k)
  have hm2 : ∑ p : ι × Fin 2, l p.1 ^ 2 = 2 * ∑ k, l k ^ 2 := by
    rw [Fintype.sum_prod_type]; simp [Finset.mul_sum]
  rw [hm2] at c2 c4le
  have hD (n : ℕ) : (fun r => rvG_diag l (rvG_cplx r) ^ n) = fun r : ι × Fin 2 → ℝ =>
      (∑ k, l k + ∑ p : ι × Fin 2, l p.1 * (r p ^ 2 - ((1 / 2 : ℝ≥0) : ℝ))) ^ n := by
    funext r; rw [rvG_diag_cplx]
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun h => rvG_diag l h ^ n) (circularVectorLaw ι) :=
    ((rvG_measurable_diag l).pow_const n).aestronglyMeasurable
  have hInt (n : ℕ) : Integrable (fun h => rvG_diag l h ^ n) (circularVectorLaw ι) ↔
      Integrable (fun r => rvG_diag l (rvG_cplx r) ^ n) P := by
    rw [hlaw, integrable_map_measure (by rw [← hlaw]; exact hmeas n) hc]
    rfl
  have hI (n : ℕ) : ∫ h, rvG_diag l h ^ n ∂circularVectorLaw ι =
      ∫ r, rvG_diag l (rvG_cplx r) ^ n ∂P := by
    rw [hlaw, integral_map hc (by rw [← hlaw]; exact hmeas n)]
  have hv : (((1 / 2 : ℝ≥0) : ℝ)) = 1 / 2 := by simp
  refine ⟨(hInt 4).2 (by rw [hD]; exact s4), (hInt 2).2 (by rw [hD]; exact s2), ?_, ?_⟩
  · rw [hI, hD, s2eq, c2, hv]; ring
  · rw [hI, hD]
    refine s4le.trans ?_
    have hk : 2 * ((1 / 2 : ℝ≥0) : ℝ) ^ 2 * (2 * ∑ k, l k ^ 2) = ∑ k, l k ^ 2 := by
      rw [hv]; ring
    rw [hk] at c4le
    have hq : 0 ≤ ∑ k, l k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    nlinarith [pow_nonneg (sq_nonneg (∑ k, l k)) 2, sq_nonneg (∑ k, l k), mul_nonneg
      (sq_nonneg (∑ k, l k)) hq]

/-!
### Hermitian quadratic forms
-/

theorem rvG_continuous_quadForm {ι : Type} [Fintype ι] (Γ : Matrix ι ι ℂ) :
    Continuous (quadForm Γ) := by
  unfold quadForm
  exact Complex.continuous_re.comp
    (continuous_star.dotProduct (continuous_const.matrix_mulVec continuous_id))

theorem rvG_spectral {ι : Type} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) :
    B = (hB.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (RCLike.ofReal ∘ hB.eigenvalues) *
      (star hB.eigenvectorUnitary : Matrix ι ι ℂ) := by
  conv_lhs => rw [hB.spectral_theorem]
  rfl

theorem rvG_quadForm_conj {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hUU : star U * U = 1) (l : ι → ℝ) (g : ι → ℂ) :
    quadForm (U * diagonal (RCLike.ofReal ∘ l) * star U) (U *ᵥ g) = rvG_diag l g := by
  unfold quadForm
  rw [mulVec_mulVec, mul_assoc _ (star U), hUU, mul_one, ← mulVec_mulVec, star_mulVec,
    dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose, hUU, vecMul_one]
  simp only [rvG_diag, dotProduct, mulVec_diagonal, Complex.re_sum, Function.comp_apply,
    Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.normSq_apply]
  ring

/-- `h ↦ U h` with `U` the eigenvector unitary turns `h*Bh` into `Σ λ_k |h_k|²`. -/
theorem rvG_quadForm_eigen {ι : Type} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (g : ι → ℂ) :
    quadForm B ((hB.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ g) = rvG_diag hB.eigenvalues g := by
  have h := rvG_quadForm_conj (hB.eigenvectorUnitary : Matrix ι ι ℂ)
    (Unitary.coe_star_mul_self _) hB.eigenvalues g
  rwa [← rvG_spectral hB] at h

theorem rvG_trace_re_eq {ι : Type} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) : B.trace.re = ∑ k, hB.eigenvalues k := by
  rw [hB.trace_eq_sum_eigenvalues, Complex.re_sum]
  simp

theorem rvG_hsSq_eq {ι : Type} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) : hsSq B = ∑ k, hB.eigenvalues k ^ 2 := by
  have hUU : (star hB.eigenvectorUnitary : Matrix ι ι ℂ) * (hB.eigenvectorUnitary : Matrix ι ι ℂ)
      = 1 := Unitary.coe_star_mul_self _
  rw [← trace_conjTranspose_mul_self_re_eq_hsSq]
  conv_lhs => rw [hB.eq, rvG_spectral hB]
  set U : Matrix ι ι ℂ := (hB.eigenvectorUnitary : Matrix ι ι ℂ)
  set V : Matrix ι ι ℂ := (star hB.eigenvectorUnitary : Matrix ι ι ℂ)
  set D : Matrix ι ι ℂ := diagonal (RCLike.ofReal ∘ hB.eigenvalues)
  have e : U * D * V * (U * D * V) = U * (D * D) * V := by
    calc U * D * V * (U * D * V) = U * D * (V * U) * D * V := by simp only [mul_assoc]
      _ = U * (D * D) * V := by rw [hUU, mul_one]; simp only [mul_assoc]
  rw [e, trace_mul_cycle, hUU, one_mul, diagonal_mul_diagonal, trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [pow_two]

/-- Moments of a Hermitian quadratic form: with `λ` the eigenvalues,
`E (h*Bh)² = (Σλ)² + Σλ²`, `E (h*Bh)⁴ ≤ 216 ((Σλ)² + Σλ²)²`. -/
theorem rvG_quadForm_moments {ι : Type} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) :
    Integrable (fun h => quadForm B h ^ 4) (circularVectorLaw ι) ∧
      Integrable (fun h => quadForm B h ^ 2) (circularVectorLaw ι) ∧
      ∫ h, quadForm B h ^ 2 ∂circularVectorLaw ι =
        (∑ k, hB.eigenvalues k) ^ 2 + ∑ k, hB.eigenvalues k ^ 2 ∧
      ∫ h, quadForm B h ^ 4 ∂circularVectorLaw ι ≤
        216 * ((∑ k, hB.eigenvalues k) ^ 2 + ∑ k, hB.eigenvalues k ^ 2) ^ 2 := by
  obtain ⟨d4, d2, d2eq, d4le⟩ := rvG_diag_moments hB.eigenvalues
  set U : Matrix ι ι ℂ := (hB.eigenvectorUnitary : Matrix ι ι ℂ)
  have hmap := rvG_circularVectorLaw_map_unitary U hB.eigenvectorUnitary.2
  have hU_m : Measurable (fun h : ι → ℂ => U *ᵥ h) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun h => quadForm B h ^ n)
      ((circularVectorLaw ι).map (fun h => U *ᵥ h)) :=
    ((rvG_continuous_quadForm B).pow n).aestronglyMeasurable
  have hI (n : ℕ) : ∫ h, quadForm B h ^ n ∂circularVectorLaw ι =
      ∫ h, rvG_diag hB.eigenvalues h ^ n ∂circularVectorLaw ι := by
    conv_lhs => rw [← hmap]
    rw [integral_map hU_m.aemeasurable (hmeas n)]
    simp_rw [U, rvG_quadForm_eigen]
  have hInt (n : ℕ) : Integrable (fun h => quadForm B h ^ n) (circularVectorLaw ι) ↔
      Integrable (fun h => rvG_diag hB.eigenvalues h ^ n) (circularVectorLaw ι) := by
    conv_lhs => rw [← hmap]
    rw [integrable_map_measure (hmeas n) hU_m.aemeasurable]
    simp only [Function.comp_def, U, rvG_quadForm_eigen]
  exact ⟨(hInt 4).2 d4, (hInt 2).2 d2, by rw [hI]; exact d2eq, by rw [hI]; exact d4le⟩

/-!
### The sandwich and the pointwise inequalities
-/

theorem rvG_quadForm_sub {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) (h : ι → ℂ) :
    quadForm (A - B) h = quadForm A h - quadForm B h := by
  simp [quadForm, sub_mulVec, dotProduct_sub]

theorem rvG_quadForm_add {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) (h : ι → ℂ) :
    quadForm (A + B) h = quadForm A h + quadForm B h := by
  simp [quadForm, add_mulVec, dotProduct_add]

theorem rvG_quadForm_nonneg {ι : Type} [Fintype ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (h : ι → ℂ) : 0 ≤ quadForm A h :=
  hA.re_dotProduct_nonneg h

/-- The sandwich `-A ⪯ B ⪯ A` gives `|h*Bh| ≤ h*Ah`. -/
theorem rvG_abs_le_of_sandwich {ι : Type} [Fintype ι] {A B : Matrix ι ι ℂ}
    (hS : IsSandwichedOn B A) (h : ι → ℂ) : |quadForm B h| ≤ quadForm A h := by
  have h1 := rvG_quadForm_nonneg hS.2.1 h
  have h2 := rvG_quadForm_nonneg hS.2.2 h
  rw [rvG_quadForm_sub] at h1
  rw [rvG_quadForm_add] at h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem rvG_posSemidef_of_sandwich {ι : Type} [Fintype ι] {A B : Matrix ι ι ℂ}
    (hS : IsSandwichedOn B A) : A.PosSemidef := by
  have e : A = (1 / 2 : ℝ) • ((A - B) + (A + B)) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]
    rw [Complex.real_smul]
    push_cast
    ring
  rw [e]
  exact (hS.2.1.add hS.2.2).smul (by norm_num)

/-- AM–GM: `2αβ x²y² ≤ α²x⁴ + β²y⁴`. -/
theorem rvG_amgm_four (x y α β : ℝ) :
    2 * (α * β) * (x ^ 2 * y ^ 2) ≤ α ^ 2 * x ^ 4 + β ^ 2 * y ^ 4 := by
  nlinarith [sq_nonneg (α * x ^ 2 - β * y ^ 2)]

/-- The pointwise Cauchy–Schwarz step: `2α x² ≤ α² (x/y)² + x²y²` when `x = 0` on `y = 0`. -/
theorem rvG_amgm_ratio (x y α : ℝ) (hxy : y = 0 → x = 0) :
    2 * α * x ^ 2 ≤ α ^ 2 * (x / y) ^ 2 + x ^ 2 * y ^ 2 := by
  by_cases hy : y = 0
  · simp [hxy hy, hy]
  · have e : x ^ 2 = (x / y) * (x * y) := by field_simp
    rw [e]
    nlinarith [sq_nonneg (α * (x / y) - x * y)]

/-!
### The theorem
-/

/-- The Gaussian variance lower bound with constant `c = 432`. Law: `h ~ circularVectorLaw ι`
(standard complex Gaussian, `E hh* = I`). For every finite `ι`, Hermitian `B` and `A` with
`-A ⪯ B ⪯ A` (`IsSandwichedOn B A`; the default `0/0 = 0` on the null event `h*Ah = 0`):
`(Re Tr B)² + ‖B‖²_HS ≤ 432 (Re Tr A)² E_h |h*Bh / h*Ah|²`. -/
theorem rvG_gaussianVarianceLower_const :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ),
      IsSandwichedOn B A →
        B.trace.re ^ 2 + hsSq B ≤
          432 * A.trace.re ^ 2 * ∫ h, (quadForm B h / quadForm A h) ^ 2 ∂circularVectorLaw ι := by
  intro ι _ _ A B hS
  have hB : B.IsHermitian := hS.1
  have hA : A.PosSemidef := rvG_posSemidef_of_sandwich hS
  set μ := circularVectorLaw ι
  set a := A.trace.re with ha_def
  set M := B.trace.re ^ 2 + hsSq B with hM_def
  set R := ∫ h, (quadForm B h / quadForm A h) ^ 2 ∂μ with hR_def
  have hXY := rvG_abs_le_of_sandwich hS
  obtain ⟨iX4, iX2, eX2, eX4⟩ := rvG_quadForm_moments hB
  obtain ⟨iY4, -, -, eY4⟩ := rvG_quadForm_moments hA.isHermitian
  rw [← rvG_trace_re_eq hB, ← rvG_hsSq_eq hB, ← hM_def] at eX2 eX4
  have hμ_nonneg : ∀ k, 0 ≤ hA.isHermitian.eigenvalues k := hA.eigenvalues_nonneg
  have hsq : ∑ k, hA.isHermitian.eigenvalues k ^ 2 ≤ (∑ k, hA.isHermitian.eigenvalues k) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => hμ_nonneg k
  rw [← rvG_trace_re_eq hA.isHermitian, ← ha_def] at hsq eY4
  have ha0 : 0 ≤ a := by
    rw [ha_def, rvG_trace_re_eq hA.isHermitian]
    exact Finset.sum_nonneg fun k _ => hμ_nonneg k
  have hEY4 : ∫ h, quadForm A h ^ 4 ∂μ ≤ 864 * a ^ 4 := by
    refine eY4.trans ?_
    have : (a ^ 2 + ∑ k, hA.isHermitian.eigenvalues k ^ 2) ^ 2 ≤ (2 * a ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  have hM0 : 0 ≤ M := by rw [hM_def]; exact add_nonneg (sq_nonneg _) (hsSq_nonneg _)
  have hR0 : 0 ≤ R := integral_nonneg fun h => sq_nonneg _
  -- integrability
  have hXm : Measurable (quadForm B) := (rvG_continuous_quadForm B).measurable
  have hYm : Measurable (quadForm A) := (rvG_continuous_quadForm A).measurable
  have iR : Integrable (fun h => (quadForm B h / quadForm A h) ^ 2) μ := by
    refine (integrable_const (1 : ℝ)).mono' ((hXm.div hYm).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with h
    rw [Real.norm_eq_abs, abs_pow]
    have hx := hXY h
    rcases eq_or_lt_of_le ((abs_nonneg _).trans hx) with hy | hy
    · rw [← hy, div_zero, abs_zero]; norm_num
    · have h1 : |quadForm B h / quadForm A h| ≤ 1 := by
        rw [abs_div, abs_of_pos hy, div_le_one hy]; exact hx
      exact pow_le_one₀ (abs_nonneg _) h1
  have iP : Integrable (fun h => quadForm B h ^ 2 * quadForm A h ^ 2) μ := by
    refine iY4.mono' ((hXm.pow_const 2).mul (hYm.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards with h
    have hx := hXY h
    have hx2 : quadForm B h ^ 2 ≤ quadForm A h ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (quadForm A h)]
  set P := ∫ h, quadForm B h ^ 2 * quadForm A h ^ 2 ∂μ with hP_def
  -- `E X²Y² ≤ (α² E X⁴ + β² E Y⁴)/(2αβ)`
  have step1 : ∀ α β : ℝ, 2 * (α * β) * P ≤
      α ^ 2 * ∫ h, quadForm B h ^ 4 ∂μ + β ^ 2 * ∫ h, quadForm A h ^ 4 ∂μ := by
    intro α β
    rw [hP_def, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (iX4.const_mul _) (iY4.const_mul _)]
    exact integral_mono (iP.const_mul _) ((iX4.const_mul _).add (iY4.const_mul _))
      fun h => rvG_amgm_four _ _ α β
  -- `2α M ≤ α² R + P`
  have step2 : ∀ α : ℝ, 2 * α * M ≤ α ^ 2 * R + P := by
    intro α
    rw [← eX2, hR_def, hP_def, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (iR.const_mul _) iP]
    refine integral_mono (iX2.const_mul _) ((iR.const_mul _).add iP) fun h => ?_
    refine rvG_amgm_ratio _ _ α fun hy => ?_
    have := hXY h
    rw [hy] at this
    exact abs_nonpos_iff.1 this
  -- conclusion
  rcases eq_or_lt_of_le hM0 with hM | hM
  · rw [← hM]; positivity
  rcases eq_or_lt_of_le ha0 with ha | ha
  · -- `Tr A = 0` forces `A = 0`, hence `X = 0` and `M = 0`.
    exfalso
    have htr : A.trace = 0 := by
      rw [hA.isHermitian.trace_eq_sum_eigenvalues]
      have : ∑ k, hA.isHermitian.eigenvalues k = 0 := by
        rw [← rvG_trace_re_eq hA.isHermitian, ← ha_def, ← ha]
      simpa using congrArg (fun r : ℝ => (r : ℂ)) this
    have hA0 : A = 0 := hA.trace_eq_zero_iff.1 htr
    have hX0 : ∀ h, quadForm B h = 0 := fun h => by
      have := hXY h
      rw [hA0] at this
      simpa [quadForm] using this
    have : M = 0 := by
      rw [← eX2]; simp [hX0]
    linarith
  have hP : P ≤ 432 * a ^ 2 * M := by
    have h1 := step1 (2 * a ^ 2) M
    have h2 : (4 * a ^ 2 * M) * P ≤ (4 * a ^ 2 * M) * (432 * a ^ 2 * M) := by
      nlinarith [mul_le_mul_of_nonneg_left eX4 (sq_nonneg (2 * a ^ 2)),
        mul_le_mul_of_nonneg_left hEY4 (sq_nonneg M)]
    exact le_of_mul_le_mul_left h2 (by positivity)
  have h3 := step2 (432 * a ^ 2)
  have h4 : (432 * a ^ 2) * M ≤ (432 * a ^ 2) * (432 * a ^ 2 * R) := by nlinarith
  have h5 := le_of_mul_le_mul_left h4 (by positivity)
  linarith

/-- `RvGaussianVarianceLower` holds, with the absolute constant `c = 432`. Law:
`h ~ circularVectorLaw ι`, the standard complex Gaussian (`E hh* = I`). Statement: for every
finite `ι`, Hermitian `B` and `A` with `-A ⪯ B ⪯ A`,
`(Re Tr B)² + ‖B‖²_HS ≤ c (Re Tr A)² E_h |h*Bh / h*Ah|²` (default `0/0 = 0`). -/
theorem rvGaussianVarianceLower_holds : RvGaussianVarianceLower :=
  ⟨432, by norm_num, rvG_gaussianVarianceLower_const⟩

end BlockBand.Endpoints
