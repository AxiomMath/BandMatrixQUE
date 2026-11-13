module

public import BlockBand.Endpoints.Poisson.FiniteLogDefs

/-!
# Full-absorber identity for the positive finite logarithm

Domain: a finite index type `ι`, a complex Hermitian `H : Matrix ι ι ℂ`, real
`E`, `Λ ≠ 0`, `δ`, and the full absorber `P = 1`. Eigenvalues are
`BlockBand.Foundations.Spectral.increasingEigenvalue`, with multiplicity.
Norms of determinants are the complex absolute value. Everything is exact and
deterministic; there is no measure on matrices and no asymptotic limit.

- `inv_pi_mul_log_det_ratio_one_eq_sum_logKernel`: for every real `x` with
  `x ≠ Λ (λ_α - E)` for all `α`,
  `(πδ)⁻¹ log (‖det(H - E - x/Λ + iδ/Λ)‖ / ‖det(H - E - x/Λ)‖) =
   Σ_α k_δ(Λ(λ_α - E) - x)`;
- `positiveLogStatistic_one_eq_sum_integral_logKernel`: for `f` continuous with
  compact support, `𝓡_δ^I(H; f) = Σ_α ∫ f(x) k_δ(Λ(λ_α - E) - x) dx` (Lebesgue
  measure on `ℝ`; the excluded `x` form a finite set and `k_δ` is locally
  integrable).

The proof is the eigenvalue-product argument: `det(H - E - x/Λ + i a)` is the product of the
factors `λ_i - E - x/Λ + i a`, and each factor of the ratio contributes
`½ log (1 + a²/(λ_i - E - x/Λ)²)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Polynomial
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a complex Hermitian matrix `A` and any `z : ℂ`, `det(A + z I) = ∏_i (λ_i + z)`, where
`λ_i` are Mathlib's eigenvalues `hA.eigenvalues` (with multiplicity). -/
theorem det_add_smul_one_eq_prod_eigenvalues {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (z : ℂ) :
    (A + z • (1 : Matrix ι ι ℂ)).det = ∏ i, ((hA.eigenvalues i : ℂ) + z) := by
  apply mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))
  calc
    (-1 : ℂ) ^ Fintype.card ι * (A + z • (1 : Matrix ι ι ℂ)).det =
        (-(A + z • (1 : Matrix ι ι ℂ))).det :=
      (Matrix.det_neg _).symm
    _ = (Matrix.scalar ι (-z) - A).det := by
      congr 1
      ext i j
      by_cases hij : i = j
      · simp [Matrix.scalar_apply, hij]
        ring
      · simp [Matrix.scalar_apply, hij]
    _ = A.charpoly.eval (-z) := (Matrix.eval_charpoly A (-z)).symm
    _ = (∏ i, (X - C (hA.eigenvalues i : ℂ))).eval (-z) :=
      congrArg (fun p : ℂ[X] => p.eval (-z)) hA.charpoly_eq
    _ = (-1 : ℂ) ^ Fintype.card ι *
        ∏ i, ((hA.eigenvalues i : ℂ) + z) := by
      simp only [eval_prod, eval_sub, eval_X, eval_C]
      calc
        ∏ i, (-z - (hA.eigenvalues i : ℂ)) =
            ∏ i, ((-1 : ℂ) * ((hA.eigenvalues i : ℂ) + z)) := by
          apply Finset.prod_congr rfl
          intro i _hi
          ring
        _ = (∏ _i : ι, (-1 : ℂ)) *
            ∏ i, ((hA.eigenvalues i : ℂ) + z) := Finset.prod_mul_distrib
        _ = (-1 : ℂ) ^ Fintype.card ι *
            ∏ i, ((hA.eigenvalues i : ℂ) + z) := by simp

/-- For every Hermitian `H` and real `E, Λ, x, a`, the full-absorber matrix has
`‖det(H - (E + x/Λ) + i a)‖ = ∏_i √((λ_i - E - x/Λ)² + a²)`, with Mathlib's
eigenvalues `hH.eigenvalues` (multiplicity). -/
theorem norm_det_absorbedShift_one {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (E Λ x a : ℝ) :
    ‖(absorbedShift H E Λ x a 1).det‖ =
      ∏ i, √((hH.eigenvalues i - (E + x / Λ)) ^ 2 + a ^ 2) := by
  have hmat : absorbedShift H E Λ x a 1 =
      H + ((((-(E + x / Λ)) : ℝ) : ℂ) + (a : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) := by
    unfold absorbedShift
    rw [add_smul, Complex.ofReal_neg, neg_smul]
    abel
  rw [hmat, det_add_smul_one_eq_prod_eigenvalues hH, norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Complex.norm_add_mul_I]
  congr 1
  push_cast
  ring

/-- One eigenvalue factor of the full-absorber ratio:
`log (√(μ² + a²) / √(μ² + 0²)) = ½ log (1 + a²/μ²)` for real `μ ≠ 0`, `a`. -/
theorem log_sqrt_ratio_eq_half_log {μ a : ℝ} (hμ : μ ≠ 0) :
    Real.log (√(μ ^ 2 + a ^ 2) / √(μ ^ 2 + (0 : ℝ) ^ 2)) =
      (1 / 2 : ℝ) * Real.log (1 + a ^ 2 / μ ^ 2) := by
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hnum : 0 < μ ^ 2 + a ^ 2 := by positivity
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
    Real.log_div (Real.sqrt_pos.mpr hnum).ne' (Real.sqrt_pos.mpr hμ2).ne',
    Real.log_sqrt hnum.le, Real.log_sqrt hμ2.le,
    show 1 + a ^ 2 / μ ^ 2 = (μ ^ 2 + a ^ 2) / μ ^ 2 by field_simp,
    Real.log_div hnum.ne' hμ2.ne']
  ring

/-- **Step 1, eigenvalue form.** For Hermitian `H`, real `E, x, a`, `Λ`, if
`λ_i ≠ E + x/Λ` for every Mathlib eigenvalue `λ_i = hH.eigenvalues i`, then
`log (‖det(H - E - x/Λ + i a)‖ / ‖det(H - E - x/Λ)‖) =
 Σ_i ½ log (1 + a² / (λ_i - E - x/Λ)²)`. -/
theorem log_norm_det_absorbedShift_one_ratio {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (E Λ x a : ℝ) (hx : ∀ i, hH.eigenvalues i - (E + x / Λ) ≠ 0) :
    Real.log (‖(absorbedShift H E Λ x a 1).det‖ / ‖(absorbedShift H E Λ x 0 1).det‖) =
      ∑ i, (1 / 2 : ℝ) * Real.log (1 + a ^ 2 / (hH.eigenvalues i - (E + x / Λ)) ^ 2) := by
  rw [norm_det_absorbedShift_one hH, norm_det_absorbedShift_one hH,
    ← Finset.prod_div_distrib, Real.log_prod]
  · exact Finset.sum_congr rfl fun i _ => log_sqrt_ratio_eq_half_log (hx i)
  · intro i _
    have h1 : 0 < (hH.eigenvalues i - (E + x / Λ)) ^ 2 + a ^ 2 := by
      have := hx i
      positivity
    have h2 : 0 < (hH.eigenvalues i - (E + x / Λ)) ^ 2 + (0 : ℝ) ^ 2 := by
      have := hx i
      positivity
    exact (div_pos (Real.sqrt_pos.mpr h1) (Real.sqrt_pos.mpr h2)).ne'

/-- For Hermitian `H`, real `E`, `Λ ≠ 0` and real `x` with `x ≠ Λ(λ_α - E)` for all
increasing eigenvalues `λ_α`, every Mathlib eigenvalue satisfies
`hH.eigenvalues i - (E + x/Λ) ≠ 0`. -/
theorem eigenvalues_sub_ne_zero_of_ne_unfolded {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (E : ℝ) {Λ x : ℝ} (hΛ : Λ ≠ 0)
    (hx : ∀ α, x ≠ Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E)) :
    ∀ i, hH.eigenvalues i - (E + x / Λ) ≠ 0 := by
  open BlockBand.Foundations.Spectral in
  intro i hi
  apply hx (increasingIndex.symm i)
  have h1 : hH.eigenvalues i = E + x / Λ := by linarith
  rw [← eigenvalue_increasingIndex, Equiv.apply_symm_apply, h1, add_sub_cancel_left]
  field_simp

/-- For Hermitian `H`, real `E`, `Λ ≠ 0` and real `x` with `x ≠ Λ(λ_α - E)` for all
increasing eigenvalues, `det(H - E - x/Λ) ≠ 0`. -/
theorem det_absorbedShift_zero_ne_zero {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (E : ℝ) {Λ x : ℝ} (hΛ : Λ ≠ 0)
    (hx : ∀ α, x ≠ Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E)) :
    (absorbedShift H E Λ x 0 1).det ≠ 0 := by
  have h := eigenvalues_sub_ne_zero_of_ne_unfolded hH E hΛ hx
  rw [← norm_ne_zero_iff, norm_det_absorbedShift_one hH]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  rw [Real.sqrt_ne_zero']
  have := h i
  positivity

/-- **Step 1 of the finite-log recovery lemma.** For every
Hermitian `H`, real `E, δ`, `Λ ≠ 0`, and every real `x` with
`x ≠ Λ (λ_α - E)` for all increasing eigenvalues `λ_α` (multiplicity):
`(πδ)⁻¹ log (‖det(H - E - x/Λ + iδ/Λ)‖ / ‖det(H - E - x/Λ)‖) =
 Σ_α k_δ(Λ(λ_α - E) - x)`. -/
theorem inv_pi_mul_log_det_ratio_one_eq_sum_logKernel {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (E δ : ℝ) {Λ x : ℝ} (hΛ : Λ ≠ 0)
    (hx : ∀ α, x ≠ Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E)) :
    (Real.pi * δ)⁻¹ * Real.log
        (‖(absorbedShift H E Λ x (δ / Λ) 1).det‖ / ‖(absorbedShift H E Λ x 0 1).det‖) =
      ∑ α, logKernel δ
        (Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E) - x) := by
  open BlockBand.Foundations.Spectral in
  rw [log_norm_det_absorbedShift_one_ratio hH E Λ x _
    (eigenvalues_sub_ne_zero_of_ne_unfolded hH E hΛ hx), Finset.mul_sum]
  open BlockBand.Foundations.Spectral in
  rw [← (increasingIndex (ι := ι)).sum_comp]
  refine Finset.sum_congr rfl fun α _ => ?_
  open BlockBand.Foundations.Spectral in
  rw [eigenvalue_increasingIndex]
  unfold logKernel
  have hratio : (δ / Λ) ^ 2 /
      (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - (E + x / Λ)) ^ 2 =
      δ ^ 2 / (Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E) - x) ^ 2 := by
    have hmul : Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E) - x =
        Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - (E + x / Λ)) := by
      field_simp
      ring
    rw [hmul, mul_pow, div_pow, div_div]
  rw [hratio]
  ring

/-- For every real `δ` and `u`, the kernel `x ↦ k_δ(u - x)` is locally integrable
for Lebesgue measure on `ℝ` (its only singularity is logarithmic, at `x = u`). -/
theorem locallyIntegrable_logKernel_sub (δ u : ℝ) :
    LocallyIntegrable (fun x : ℝ => logKernel δ (u - x)) volume := by
  have hmero : ∀ a b : ℝ,
      MeromorphicOn (fun x : ℝ => 1 + δ ^ 2 / (u - x) ^ 2) (Set.uIcc a b) := by
    intro a b x _
    fun_prop
  have hint : ∀ a b : ℝ,
      IntervalIntegrable (fun x : ℝ => logKernel δ (u - x)) volume a b := by
    intro a b
    exact ((hmero a b).intervalIntegrable_log).const_mul _
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hsub : K ⊆ Set.Icc (-(|R| + 1)) (|R| + 1) := by
    intro y hy
    have := hR hy
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    have hRR := le_abs_self R
    exact abs_le.mp (by linarith)
  have hle : -(|R| + 1) ≤ |R| + 1 := by linarith [abs_nonneg R]
  have hIcc : IntegrableOn (fun x : ℝ => logKernel δ (u - x))
      (Set.Icc (-(|R| + 1)) (|R| + 1)) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp (hint _ _)
  exact hIcc.mono_set hsub

/-- For `f` continuous with compact support and all real `δ, u`, the function
`x ↦ f x · k_δ(u - x)` is Lebesgue integrable on `ℝ`. -/
theorem integrable_mul_logKernel_sub {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (δ u : ℝ) :
    Integrable (fun x : ℝ => f x * logKernel δ (u - x)) volume :=
  (locallyIntegrable_logKernel_sub δ u).integrable_smul_left_of_hasCompactSupport hf hfs

/-- For every Hermitian `H` and real `E, Λ`, Lebesgue-almost every real `x` avoids
the finitely many unfolded eigenvalues: `x ≠ Λ (λ_α - E)` for all `α`. -/
theorem ae_ne_unfoldedEigenvalue {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (E Λ : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ∀ α, x ≠ Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E) := by
  have hfin := Set.finite_range fun α =>
    Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)] with x hx α h
  exact hx ⟨α, h.symm⟩

/-- **Step 1, integrated: `𝓡_δ^I(H; f) = Σ_α (k_δ * f)(u_α)`.**
For every Hermitian `H`, real `E, δ`, `Λ ≠ 0`, and `f : ℝ → ℝ` continuous with
compact support,
`positiveLogStatistic H E Λ δ 1 f = Σ_α ∫ f(x) k_δ(Λ(λ_α - E) - x) dx`
(Lebesgue integrals; increasing eigenvalues with multiplicity). -/
theorem positiveLogStatistic_one_eq_sum_integral_logKernel {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (E δ : ℝ) {Λ : ℝ} (hΛ : Λ ≠ 0) {f : ℝ → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    positiveLogStatistic H E Λ δ 1 f =
      ∑ α, ∫ x, f x * logKernel δ
        (Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E) - x) := by
  unfold positiveLogStatistic
  rw [← integral_const_mul, ← integral_finsetSum _ fun α _ =>
    integrable_mul_logKernel_sub hf hfs δ _]
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_unfoldedEigenvalue hH E Λ] with x hx
  have hk := inv_pi_mul_log_det_ratio_one_eq_sum_logKernel hH E δ hΛ hx
  rw [Finset.sum_congr rfl (fun α _ => (mul_comm (f x) _)), ← Finset.sum_mul, ← hk]
  ring

/-- For every Hermitian `H`, real `E`, `Λ ≠ 0`, `δ ≠ 0`, and `f` continuous with
compact support, the full-absorber integrand
`x ↦ f(x) log (‖det(H - E - x/Λ + iδ/Λ)‖ / ‖det(H - E - x/Λ)‖)` of
`positiveLogStatistic H E Λ δ 1 f` is Lebesgue integrable on `ℝ`. -/
theorem integrable_positiveLogIntegrand_one {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (E : ℝ) {Λ δ : ℝ} (hΛ : Λ ≠ 0) (hδ : δ ≠ 0) {f : ℝ → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    Integrable (fun x => f x * Real.log
      (‖(absorbedShift H E Λ x (δ / Λ) 1).det‖ / ‖(absorbedShift H E Λ x 0 1).det‖))
      volume := by
  have hint : Integrable (fun x => (Real.pi * δ) * ∑ α, f x * logKernel δ
      (Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E) - x)) volume :=
    (integrable_finsetSum _ fun α _ => integrable_mul_logKernel_sub hf hfs δ _).const_mul _
  refine hint.congr ?_
  filter_upwards [ae_ne_unfoldedEigenvalue hH E Λ] with x hx
  have hk := inv_pi_mul_log_det_ratio_one_eq_sum_logKernel hH E δ hΛ hx
  have hπδ : Real.pi * δ ≠ 0 := mul_ne_zero Real.pi_ne_zero hδ
  rw [← Finset.mul_sum, ← hk]
  field_simp

end BlockBand.Endpoints
