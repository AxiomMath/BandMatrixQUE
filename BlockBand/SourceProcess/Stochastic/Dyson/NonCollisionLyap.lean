module

public import BlockBand.SourceProcess.Stochastic.Dyson.ItoIdentities
public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionAlgebra

/-!
# The log-Vandermonde Lyapunov function and its Itô drift

In the coordinates `y ↦ vecHerm N y`, with `λ_i = lam N i`:
* `lyap N y = ∑_{i ≠ j} log|λ_i - λ_j|` (`Real.log` is `log|·|`), `C^n` on `simpleSet N`;
* `itoDrift_lyap`: the contract's `itoDrift` of `(t, y) ↦ lyap N y` with zero drift and the GUE
  covariance `gueCovVec N = I/N` equals `lyapDrift N y = (1/N) ∑_{i ≠ j} (λ_i - λ_j)⁻² ≥ 0`.
The proof uses the Hadamard formulas `lapl_lam` (`∑_a ∂_a² λ_i = 2 ∑_{j≠i} (λ_i-λ_j)⁻¹`), the
gradient orthonormality `∑_a ∂_aλ_i ∂_aλ_j = δ_ij` (from `gradPair_dysonState`), and the
cancellation `lyap_drift_identity`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix Filter Topology Finset
open scoped NNReal ContDiff
open BlockBand.Internal.Contracts.Transmission

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eventually_differentiableAt {f : E → ℝ} {y : E} (hf : ContDiffAt ℝ 2 f y) :
    ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ f z :=
  (hf.eventually (by simp)).mono fun _ hz => hz.differentiableAt (by norm_num)

theorem differentiableAt_fderiv {f : E → ℝ} {y : E} (hf : ContDiffAt ℝ 2 f y) :
    DifferentiableAt ℝ (fderiv ℝ f) y :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

theorem fderiv2_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {y : E}
    (hf : ∀ k ∈ s, ContDiffAt ℝ 2 (f k) y) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun z => ∑ k ∈ s, f k z)) y v w =
      ∑ k ∈ s, fderiv ℝ (fderiv ℝ (f k)) y v w := by
  have hev : ∀ᶠ z in 𝓝 y, ∀ k ∈ s, DifferentiableAt ℝ (f k) z :=
    (eventually_all_finset s).2 fun k hk => eventually_differentiableAt (hf k hk)
  have h1 : fderiv ℝ (fun z => ∑ k ∈ s, f k z) =ᶠ[𝓝 y] fun z => ∑ k ∈ s, fderiv ℝ (f k) z := by
    filter_upwards [hev] with z hz
    exact fderiv_fun_sum hz
  rw [h1.fderiv_eq, fderiv_fun_sum fun k hk => differentiableAt_fderiv (hf k hk)]
  simp

theorem fderiv2_sub {f g : E → ℝ} {y : E} (hf : ContDiffAt ℝ 2 f y) (hg : ContDiffAt ℝ 2 g y)
    (v w : E) :
    fderiv ℝ (fderiv ℝ (fun z => f z - g z)) y v w =
      fderiv ℝ (fderiv ℝ f) y v w - fderiv ℝ (fderiv ℝ g) y v w := by
  have h1 : fderiv ℝ (fun z => f z - g z) =ᶠ[𝓝 y] fun z => fderiv ℝ f z - fderiv ℝ g z := by
    filter_upwards [eventually_differentiableAt hf, eventually_differentiableAt hg] with z hz1 hz2
    exact fderiv_fun_sub hz1 hz2
  rw [h1.fderiv_eq, fderiv_fun_sub (differentiableAt_fderiv hf) (differentiableAt_fderiv hg)]
  rfl

/-- Second derivative of `log ∘ d` where `d ≠ 0`. -/
theorem fderiv2_log_comp {d : E → ℝ} {y : E} (hd : ContDiffAt ℝ 2 d y) (hy : d y ≠ 0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun z => Real.log (d z))) y v w =
      (d y)⁻¹ * fderiv ℝ (fderiv ℝ d) y v w -
        (d y ^ 2)⁻¹ * (fderiv ℝ d y v * fderiv ℝ d y w) := by
  have h1 : fderiv ℝ (fun z => Real.log (d z)) =ᶠ[𝓝 y] fun z => (d z)⁻¹ • fderiv ℝ d z := by
    filter_upwards [eventually_differentiableAt hd, hd.continuousAt.eventually_ne hy] with z hz1 hz2
    exact (hz1.hasFDerivAt.log hz2).fderiv
  have hinv : HasFDerivAt (fun z => (d z)⁻¹) ((-(d y ^ 2)⁻¹) • fderiv ℝ d y) y :=
    (hasDerivAt_inv hy).comp_hasFDerivAt y (hd.differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt (fun z => (d z)⁻¹ • fderiv ℝ d z) _ y :=
    hinv.smul (differentiableAt_fderiv hd).hasFDerivAt
  rw [h1.fderiv_eq, h2.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, neg_mul]
  ring

end Calculus

variable {N : ℕ}

/-- The log-Vandermonde function `∑_{i ≠ j} log|λ_i - λ_j|` in coordinates. -/
def lyap (N : ℕ) (y : Fin (N * N) → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ univ.erase i, Real.log (lam N i y - lam N j y)

/-- Its Itô drift `(1/N) ∑_{i ≠ j} (λ_i - λ_j)⁻²`. -/
def lyapDrift (N : ℕ) (y : Fin (N * N) → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, ∑ j ∈ univ.erase i, ((lam N i y - lam N j y)⁻¹) ^ 2

theorem lam_sub_ne_zero {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) {i j : Fin N}
    (hj : j ∈ univ.erase i) : lam N i y - lam N j y ≠ 0 :=
  sub_ne_zero.mpr (HasSimpleSpectrum.ne hy (Ne.symm (ne_of_mem_erase hj)))

theorem contDiffAt_lam {n : WithTop ℕ∞} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (i : Fin N) : ContDiffAt ℝ n (lam N i) y :=
  contDiffAt_eigenvalue hy i

theorem contDiffAt_lam_sub {n : WithTop ℕ∞} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (i j : Fin N) : ContDiffAt ℝ n (fun z => lam N i z - lam N j z) y :=
  (contDiffAt_eigenvalue hy i).sub (contDiffAt_eigenvalue hy j)

theorem contDiffAt_lyap {n : WithTop ℕ∞} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) :
    ContDiffAt ℝ n (lyap N) y := by
  unfold lyap
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j hj =>
    (contDiffAt_lam_sub hy i j).log (lam_sub_ne_zero hy hj)

theorem measurable_lam (i : Fin N) : Measurable (lam N i) :=
  (measurable_dysonEigenvalue i).comp continuous_vecHerm.measurable

theorem measurable_lyap : Measurable (lyap N) := by
  unfold lyap
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact Real.measurable_log.comp ((measurable_lam i).sub (measurable_lam j))

theorem lyapDrift_nonneg (y : Fin (N * N) → ℝ) : 0 ≤ lyapDrift N y := by
  unfold lyapDrift
  exact mul_nonneg (by positivity) (sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _)

/-- Gradient orthonormality of the eigenvalues: `∑_a ∂_aλ_i ∂_aλ_j = δ_ij`. -/
theorem gradPair_lam {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i j : Fin N) :
    ∑ a, fderiv ℝ (lam N i) y (Pi.single a 1) * fderiv ℝ (lam N j) y (Pi.single a 1) =
      if i = j then 1 else 0 := by
  have h := gradPair_dysonState hy 0 (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
  rw [stateFn_inl, stateFn_inl, dysonStateCov_inl_inl] at h
  have hN := ne_zero_of_fin i
  split_ifs at h ⊢ with hij
  · field_simp at h; linarith
  · rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 (one_div_ne_zero hN)
    · exact h0

/-- The coordinate Laplacian of `log(λ_i - λ_j)`, `i ≠ j`. -/
theorem lapl_log_gap {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) {i j : Fin N}
    (hj : j ∈ univ.erase i) :
    ∑ a, fderiv ℝ (fderiv ℝ (fun z => Real.log (lam N i z - lam N j z))) y
        (Pi.single a 1) (Pi.single a 1) =
      pinv (fun k => lam N k y) i j * (2 * rowSum (fun k => lam N k y) i -
        2 * rowSum (fun k => lam N k y) j) - pinv (fun k => lam N k y) i j ^ 2 * 2 := by
  have hij : i ≠ j := Ne.symm (ne_of_mem_erase hj)
  have hd := contDiffAt_lam_sub (n := 2) hy i j
  have hdi : DifferentiableAt ℝ (lam N i) y := (contDiffAt_eigenvalue (n := 1) hy i).differentiableAt
    (by norm_num)
  have hdj : DifferentiableAt ℝ (lam N j) y := (contDiffAt_eigenvalue (n := 1) hy j).differentiableAt
    (by norm_num)
  simp_rw [fderiv2_log_comp hd (lam_sub_ne_zero hy hj), fderiv2_sub (contDiffAt_lam hy i)
    (contDiffAt_lam hy j), fderiv_fun_sub hdi hdj, _root_.sub_apply]
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib, lapl_lam hy i, lapl_lam hy j]
  have hsq : ∑ a, (fderiv ℝ (lam N i) y (Pi.single a 1) - fderiv ℝ (lam N j) y (Pi.single a 1)) *
      (fderiv ℝ (lam N i) y (Pi.single a 1) - fderiv ℝ (lam N j) y (Pi.single a 1)) = 2 := by
    simp only [sub_mul, mul_sub, sum_sub_distrib]
    rw [gradPair_lam hy i i, gradPair_lam hy i j, gradPair_lam hy j i, gradPair_lam hy j j]
    simp [hij, Ne.symm hij]; norm_num
  rw [hsq]
  simp only [pinv, rowSum, inv_pow]

/-- **Itô drift of the log-Vandermonde function.** -/
theorem itoDrift_lyap {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (t : ℝ≥0) :
    itoDrift (fun p : ℝ × (Fin (N * N) → ℝ) => lyap N p.2) y t 0 (gueCovVec N) =
      lyapDrift N y := by
  rw [gueCovVec_eq, itoDrift_comp_snd (contDiffAt_lyap hy)]
  have h1 : ∀ a : Fin (N * N), fderiv ℝ (fderiv ℝ (lyap N)) y (Pi.single a 1) (Pi.single a 1) =
      ∑ i, ∑ j ∈ univ.erase i, fderiv ℝ (fderiv ℝ (fun z => Real.log (lam N i z - lam N j z))) y
        (Pi.single a 1) (Pi.single a 1) := by
    intro a
    unfold lyap
    rw [fderiv2_sum _ (fun i _ => ContDiffAt.sum fun j hj =>
      (contDiffAt_lam_sub hy i j).log (lam_sub_ne_zero hy hj))]
    refine sum_congr rfl fun i _ => ?_
    exact fderiv2_sum _ (fun j hj => (contDiffAt_lam_sub hy i j).log (lam_sub_ne_zero hy hj)) _ _
  simp_rw [h1]
  rw [sum_comm]
  simp_rw [sum_comm (s := univ) (t := univ.erase _)]
  have h2 : ∑ i, ∑ j ∈ univ.erase i, ∑ a : Fin (N * N), fderiv ℝ (fderiv ℝ
      (fun z => Real.log (lam N i z - lam N j z))) y (Pi.single a 1) (Pi.single a 1) =
      ∑ i, ∑ j ∈ univ.erase i, (pinv (fun k => lam N k y) i j *
        (2 * rowSum (fun k => lam N k y) i - 2 * rowSum (fun k => lam N k y) j) -
        pinv (fun k => lam N k y) i j ^ 2 * 2) :=
    sum_congr rfl fun i _ => sum_congr rfl fun j hj => lapl_log_gap hy hj
  rw [h2]
  have hinj : Function.Injective fun k => lam N k y := (show HasSimpleSpectrum N (vecHerm N y)
    from hy).injective
  rw [lyap_drift_identity hinj, lyapDrift]
  simp only [pinv]
  ring

end BlockBand.SourceProcess.Stochastic.Dyson
