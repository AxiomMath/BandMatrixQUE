module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Determinant-Laplace test function and its `a`-derivatives

For a positive semidefinite Hermitian `Q : Matrix (Fin n) (Fin n) ℂ` and real
`a` we set

* `detLaplace Q a = F_a(Q) = det(I + aQ)⁻¹`, realised as the real number
  `(det (1 + a • Q)).re⁻¹` (the determinant is real: `im_det_one_add_smul`,
  and `ofReal_detLaplace` identifies it with the complex inverse);
* `resolventWeight Q a = A_a = aQ(I + aQ)⁻¹`.

We prove, for every `n`, every positive semidefinite `Q` and every real `a ≥ 0`:

* `1 ≤ Re det(I + aQ)`, `Im det(I + aQ) = 0`, `0 < F_a(Q) ≤ 1`;
* `A_a` is positive semidefinite, `aQ - A_a` is positive semidefinite,
  `0 ≤ Re Tr A_a ≤ a γ` with `γ = Re Tr Q`, and `Im Tr A_a = 0`;
* `a ∂_a F_a = -F_a Re Tr A_a` and
  `a² ∂_a² F_a = F_a [(Re Tr A_a)² + Re Tr A_a²]`,
  with `∂_a` the ordinary derivative of the real function `a ↦ F_a(Q)`.

Method: unitary diagonalisation `Q = U diag(λ) Uᴴ` (Mathlib spectral theorem),
so `F_a = ∏ᵢ (1 + aλᵢ)⁻¹`, `Tr A_a = ∑ᵢ aλᵢ/(1+aλᵢ)`,
`Tr A_a² = ∑ᵢ (aλᵢ/(1+aλᵢ))²`; the derivatives are computed through
`F = exp(-∑ᵢ log(1 + aλᵢ))` near `a`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-- `F_a(Q) = det(I + aQ)⁻¹` (display before the deterministic-clock lemma), as a real
number: the real part of the complex determinant, inverted. For Hermitian `Q`
the determinant is real (`im_det_one_add_smul`), so nothing is lost. -/
def detLaplace (Q : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) : ℝ :=
  ((1 + (a : ℂ) • Q).det).re⁻¹

/-- `A_a = aQ(I + aQ)⁻¹` (display before the deterministic-clock lemma). -/
def resolventWeight (Q : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  ((a : ℂ) • Q) * (1 + (a : ℂ) • Q)⁻¹

section Conj

variable (U : Matrix (Fin n) (Fin n) ℂ)

private lemma conj_mul_conj (hU : star U * U = 1) (M N : Matrix (Fin n) (Fin n) ℂ) :
    (U * M * star U) * (U * N * star U) = U * (M * N) * star U := by
  calc (U * M * star U) * (U * N * star U) = U * M * (star U * U) * N * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private lemma det_conj_unitary (hU : star U * U = 1) (M : Matrix (Fin n) (Fin n) ℂ) :
    (U * M * star U).det = M.det := by
  rw [det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, hU, det_one, one_mul]

private lemma trace_conj_unitary (hU : star U * U = 1) (M : Matrix (Fin n) (Fin n) ℂ) :
    (U * M * star U).trace = M.trace := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

variable {Q : Matrix (Fin n) (Fin n) ℂ} {U} (μ : Fin n → ℝ)

private lemma oneAdd_eq (hU2 : U * star U = 1)
    (hspec : Q = U * diagonal (fun i => (μ i : ℂ)) * star U) (a : ℝ) :
    1 + (a : ℂ) • Q = U * diagonal (fun i => ((1 + a * μ i : ℝ) : ℂ)) * star U := by
  subst hspec
  have hd : diagonal (fun i => ((1 + a * μ i : ℝ) : ℂ))
      = 1 + (a : ℂ) • diagonal (fun i => (μ i : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU2, Matrix.mul_smul, Matrix.smul_mul]

private lemma inv_oneAdd_eq (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (hspec : Q = U * diagonal (fun i => (μ i : ℂ)) * star U) (a : ℝ)
    (h : ∀ i, 1 + a * μ i ≠ 0) :
    (1 + (a : ℂ) • Q)⁻¹ = U * diagonal (fun i => (((1 + a * μ i)⁻¹ : ℝ) : ℂ)) * star U := by
  rw [oneAdd_eq μ hU2 hspec]
  apply Matrix.inv_eq_left_inv
  rw [conj_mul_conj U hU1, diagonal_mul_diagonal]
  have : (fun i => (((1 + a * μ i)⁻¹ : ℝ) : ℂ) * ((1 + a * μ i : ℝ) : ℂ)) = fun _ => (1 : ℂ) :=
    funext fun i => by rw [← Complex.ofReal_mul, inv_mul_cancel₀ (h i), Complex.ofReal_one]
  rw [this, diagonal_one, Matrix.mul_one, hU2]

private lemma resolventWeight_eq (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (hspec : Q = U * diagonal (fun i => (μ i : ℂ)) * star U) (a : ℝ)
    (h : ∀ i, 1 + a * μ i ≠ 0) :
    resolventWeight Q a
      = U * diagonal (fun i => ((a * μ i / (1 + a * μ i) : ℝ) : ℂ)) * star U := by
  unfold resolventWeight
  rw [inv_oneAdd_eq μ hU1 hU2 hspec a h]
  have hs : (a : ℂ) • Q = U * diagonal (fun i => ((a * μ i : ℝ) : ℂ)) * star U := by
    rw [hspec, ← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [hs, conj_mul_conj U hU1, diagonal_mul_diagonal]
  refine congrArg (fun d => U * diagonal d * star U) (funext fun i => ?_)
  rw [← Complex.ofReal_mul, div_eq_mul_inv]

private lemma det_oneAdd_eq (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (hspec : Q = U * diagonal (fun i => (μ i : ℂ)) * star U) (a : ℝ) :
    (1 + (a : ℂ) • Q).det = ((∏ i, (1 + a * μ i) : ℝ) : ℂ) := by
  rw [oneAdd_eq μ hU2 hspec, det_conj_unitary U hU1, det_diagonal, Complex.ofReal_prod]

private lemma trace_resolventWeight_eq (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (hspec : Q = U * diagonal (fun i => (μ i : ℂ)) * star U) (a : ℝ)
    (h : ∀ i, 1 + a * μ i ≠ 0) :
    (resolventWeight Q a).trace = ((∑ i, a * μ i / (1 + a * μ i) : ℝ) : ℂ) := by
  rw [resolventWeight_eq μ hU1 hU2 hspec a h, trace_conj_unitary U hU1, trace_diagonal,
    Complex.ofReal_sum]

private lemma trace_resolventWeight_sq_eq (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (hspec : Q = U * diagonal (fun i => (μ i : ℂ)) * star U) (a : ℝ)
    (h : ∀ i, 1 + a * μ i ≠ 0) :
    ((resolventWeight Q a) ^ 2).trace = ((∑ i, (a * μ i / (1 + a * μ i)) ^ 2 : ℝ) : ℂ) := by
  rw [pow_two, resolventWeight_eq μ hU1 hU2 hspec a h, conj_mul_conj U hU1,
    diagonal_mul_diagonal, trace_conj_unitary U hU1, trace_diagonal, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_pow, pow_two]

private lemma smul_sub_resolventWeight_eq (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (hspec : Q = U * diagonal (fun i => (μ i : ℂ)) * star U) (a : ℝ)
    (h : ∀ i, 1 + a * μ i ≠ 0) :
    (a : ℂ) • Q - resolventWeight Q a
      = U * diagonal (fun i => ((a * μ i - a * μ i / (1 + a * μ i) : ℝ) : ℂ)) * star U := by
  rw [resolventWeight_eq μ hU1 hU2 hspec a h, hspec, ← Matrix.smul_mul, ← Matrix.mul_smul,
    ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

end Conj

section Spectral

variable {Q : Matrix (Fin n) (Fin n) ℂ}

private lemma spectral_data (hQ : Q.IsHermitian) :
    Q = (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
        * diagonal (fun i => (hQ.eigenvalues i : ℂ))
        * star (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  conv_lhs => rw [hQ.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

private lemma u1 (hQ : Q.IsHermitian) :
    star (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      * (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  Unitary.coe_star_mul_self _

private lemma u2 (hQ : Q.IsHermitian) :
    (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      * star (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  Unitary.coe_mul_star_self _

/-- For Hermitian `Q` and every real `a`,
`det(I + aQ) = ∏ᵢ (1 + aλᵢ)` with `λ = hQ.eigenvalues`. -/
theorem det_one_add_smul_eq_prod (hQ : Q.IsHermitian) (a : ℝ) :
    (1 + (a : ℂ) • Q).det = ((∏ i, (1 + a * hQ.eigenvalues i) : ℝ) : ℂ) :=
  det_oneAdd_eq _ (u1 hQ) (u2 hQ) (spectral_data hQ) a

/-- For Hermitian `Q` and every real `a`, `F_a(Q) = ∏ᵢ (1 + aλᵢ)⁻¹`. -/
theorem detLaplace_eq_prod (hQ : Q.IsHermitian) (a : ℝ) :
    detLaplace Q a = ∏ i, (1 + a * hQ.eigenvalues i)⁻¹ := by
  rw [detLaplace, det_one_add_smul_eq_prod hQ, Complex.ofReal_re, Finset.prod_inv_distrib]

end Spectral

section Calculus

variable (μ : Fin n → ℝ)

private def prodInv (b : ℝ) : ℝ := ∏ i, (1 + b * μ i)⁻¹

private def gSum (b : ℝ) : ℝ := ∑ i, μ i * (1 + b * μ i)⁻¹

private def hSum (b : ℝ) : ℝ := ∑ i, μ i ^ 2 * ((1 + b * μ i)⁻¹) ^ 2

private lemma eventually_pos {b : ℝ} (hb : ∀ i, 0 < 1 + b * μ i) :
    ∀ᶠ c in nhds b, ∀ i, 0 < 1 + c * μ i := by
  rw [Filter.eventually_all]
  intro i
  have hc : ContinuousAt (fun c : ℝ => 1 + c * μ i) b := by fun_prop
  exact hc.eventually (lt_mem_nhds (hb i))

private lemma hasDerivAt_affine (i : Fin n) (b : ℝ) :
    HasDerivAt (fun c : ℝ => 1 + c * μ i) (μ i) b := by
  simpa using ((hasDerivAt_id b).mul_const (μ i)).const_add 1

private lemma hasDerivAt_prodInv {b : ℝ} (hb : ∀ i, 0 < 1 + b * μ i) :
    HasDerivAt (prodInv μ) (-(prodInv μ b) * gSum μ b) b := by
  have hlog : HasDerivAt (fun c => -∑ i, Real.log (1 + c * μ i))
      (-∑ i, μ i / (1 + b * μ i)) b :=
    (HasDerivAt.fun_sum fun i _ => (hasDerivAt_affine μ i b).log (hb i).ne').neg
  have hexp := hlog.exp
  have heq : (fun c => Real.exp (-∑ i, Real.log (1 + c * μ i))) =ᶠ[nhds b] prodInv μ := by
    filter_upwards [eventually_pos μ hb] with c hc
    rw [Real.exp_neg, Real.exp_sum, prodInv, Finset.prod_inv_distrib]
    congr 1
    exact Finset.prod_congr rfl fun i _ => Real.exp_log (hc i)
  have hval : Real.exp (-∑ i, Real.log (1 + b * μ i)) = prodInv μ b := heq.eq_of_nhds
  rw [hval] at hexp
  have := hexp.congr_of_eventuallyEq heq.symm
  convert this using 1
  simp only [gSum, div_eq_mul_inv]
  ring

private lemma hasDerivAt_gSum {b : ℝ} (hb : ∀ i, 0 < 1 + b * μ i) :
    HasDerivAt (gSum μ) (-(hSum μ b)) b := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((hasDerivAt_affine μ i b).inv (hb i).ne').const_mul (μ i)
  unfold gSum hSum
  convert h using 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

private lemma deriv_prodInv_eventually {a : ℝ} (ha : ∀ i, 0 < 1 + a * μ i) :
    deriv (prodInv μ) =ᶠ[nhds a] fun c => -(prodInv μ c) * gSum μ c := by
  filter_upwards [eventually_pos μ ha] with c hc
  exact (hasDerivAt_prodInv μ hc).deriv

private lemma hasDerivAt_deriv_prodInv {a : ℝ} (ha : ∀ i, 0 < 1 + a * μ i) :
    HasDerivAt (deriv (prodInv μ))
      (prodInv μ a * (gSum μ a ^ 2 + hSum μ a)) a := by
  have h := ((hasDerivAt_prodInv μ ha).neg).mul (hasDerivAt_gSum μ ha)
  have h2 := h.congr_of_eventuallyEq (deriv_prodInv_eventually μ ha)
  convert h2 using 1
  simp only [Pi.neg_apply]
  ring

end Calculus

section Main

variable {Q : Matrix (Fin n) (Fin n) ℂ}

/-- For Hermitian `Q` and every real `a`, the real number `F_a(Q)`, cast to `ℂ`,
is the inverse of the complex determinant `det(I + aQ)`. -/
theorem ofReal_detLaplace (hQ : Q.IsHermitian) (a : ℝ) :
    ((detLaplace Q a : ℝ) : ℂ) = ((1 + (a : ℂ) • Q).det)⁻¹ := by
  rw [detLaplace, det_one_add_smul_eq_prod hQ, Complex.ofReal_re, Complex.ofReal_inv]

private lemma factor_pos (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) (i : Fin n) :
    0 < 1 + a * hQ.isHermitian.eigenvalues i := by
  have := hQ.eigenvalues_nonneg i
  positivity

/-- For Hermitian `Q` and every real `a`, `det(I + aQ)` is real. -/
theorem im_det_one_add_smul (hQ : Q.IsHermitian) (a : ℝ) :
    (1 + (a : ℂ) • Q).det.im = 0 := by
  rw [det_one_add_smul_eq_prod hQ, Complex.ofReal_im]

/-- For PSD `Q` and every `a ≥ 0`, `1 ≤ Re det(I + aQ)`. -/
theorem one_le_re_det_one_add_smul (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    1 ≤ (1 + (a : ℂ) • Q).det.re := by
  rw [det_one_add_smul_eq_prod hQ.isHermitian, Complex.ofReal_re]
  refine Finset.one_le_prod₀ fun i _ => ?_
  have := hQ.eigenvalues_nonneg i
  have : 0 ≤ a * hQ.isHermitian.eigenvalues i := by positivity
  linarith

/-- `0 < F_a(Q)` for PSD `Q` and every `a ≥ 0` (display before
the deterministic-clock lemma). -/
theorem detLaplace_pos (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) : 0 < detLaplace Q a := by
  rw [detLaplace_eq_prod hQ.isHermitian]
  exact Finset.prod_pos fun i _ => inv_pos.mpr (factor_pos hQ ha i)

/-- `F_a(Q) ≤ 1` for PSD `Q` and every `a ≥ 0` (display before
the deterministic-clock lemma). -/
theorem detLaplace_le_one (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) : detLaplace Q a ≤ 1 := by
  rw [detLaplace, inv_le_one₀ (by linarith [one_le_re_det_one_add_smul hQ ha])]
  exact one_le_re_det_one_add_smul hQ ha

/-- For PSD `Q` and `a ≥ 0`, `Tr A_a = ∑ᵢ aλᵢ/(1 + aλᵢ)` (a real number). -/
theorem trace_resolventWeight_eq_sum (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    (resolventWeight Q a).trace
      = ((∑ i, a * hQ.isHermitian.eigenvalues i / (1 + a * hQ.isHermitian.eigenvalues i) : ℝ)
          : ℂ) :=
  trace_resolventWeight_eq _ (u1 hQ.isHermitian) (u2 hQ.isHermitian)
    (spectral_data hQ.isHermitian) a fun i => (factor_pos hQ ha i).ne'

/-- For PSD `Q` and `a ≥ 0`, `Tr A_a² = ∑ᵢ (aλᵢ/(1 + aλᵢ))²` (a real number). -/
theorem trace_resolventWeight_sq_eq_sum (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    ((resolventWeight Q a) ^ 2).trace
      = ((∑ i, (a * hQ.isHermitian.eigenvalues i
          / (1 + a * hQ.isHermitian.eigenvalues i)) ^ 2 : ℝ) : ℂ) :=
  trace_resolventWeight_sq_eq _ (u1 hQ.isHermitian) (u2 hQ.isHermitian)
    (spectral_data hQ.isHermitian) a fun i => (factor_pos hQ ha i).ne'

/-- For PSD `Q` and `a ≥ 0`, `Tr A_a` is real. -/
theorem im_trace_resolventWeight (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    (resolventWeight Q a).trace.im = 0 := by
  rw [trace_resolventWeight_eq_sum hQ ha, Complex.ofReal_im]

/-- For PSD `Q` and `a ≥ 0`, `A_a` is positive semidefinite. -/
theorem resolventWeight_posSemidef (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    (resolventWeight Q a).PosSemidef := by
  rw [resolventWeight_eq _ (u1 hQ.isHermitian) (u2 hQ.isHermitian)
    (spectral_data hQ.isHermitian) a fun i => (factor_pos hQ ha i).ne',
    Matrix.star_eq_conjTranspose]
  refine PosSemidef.mul_mul_conjTranspose_same (posSemidef_diagonal_iff.mpr fun i => ?_) _
  have := hQ.eigenvalues_nonneg i
  have := factor_pos hQ ha i
  exact Complex.zero_le_real.mpr (by positivity)

/-- For PSD `Q` and `a ≥ 0`, `A_a ⪯ aQ` in the Loewner order. -/
theorem posSemidef_smul_sub_resolventWeight (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    ((a : ℂ) • Q - resolventWeight Q a).PosSemidef := by
  rw [smul_sub_resolventWeight_eq _ (u1 hQ.isHermitian) (u2 hQ.isHermitian)
    (spectral_data hQ.isHermitian) a fun i => (factor_pos hQ ha i).ne',
    Matrix.star_eq_conjTranspose]
  refine PosSemidef.mul_mul_conjTranspose_same (posSemidef_diagonal_iff.mpr fun i => ?_) _
  have h0 := hQ.eigenvalues_nonneg i
  have h1 := factor_pos hQ ha i
  refine Complex.zero_le_real.mpr ?_
  have : a * hQ.isHermitian.eigenvalues i / (1 + a * hQ.isHermitian.eigenvalues i)
      ≤ a * hQ.isHermitian.eigenvalues i :=
    div_le_self (by positivity) (by nlinarith)
  linarith

/-- For PSD `Q` and `a ≥ 0`, `0 ≤ Re Tr A_a`. -/
theorem re_trace_resolventWeight_nonneg (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ (resolventWeight Q a).trace.re := by
  rw [trace_resolventWeight_eq_sum hQ ha, Complex.ofReal_re]
  refine Finset.sum_nonneg fun i _ => ?_
  have := hQ.eigenvalues_nonneg i
  have := factor_pos hQ ha i
  positivity

/-- `Tr A_a ≤ aγ`, `γ = Re Tr Q`, for PSD `Q` and every `a ≥ 0` (display
before the deterministic-clock lemma). -/
theorem re_trace_resolventWeight_le (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    (resolventWeight Q a).trace.re ≤ a * Q.trace.re := by
  have hγ : Q.trace.re = ∑ i, hQ.isHermitian.eigenvalues i := by
    rw [hQ.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [trace_resolventWeight_eq_sum hQ ha, Complex.ofReal_re, hγ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have := hQ.eigenvalues_nonneg i
  exact div_le_self (by positivity) (by nlinarith)

private theorem detLaplace_eq_prodInv (hQ : Q.IsHermitian) :
    detLaplace Q = prodInv hQ.eigenvalues :=
  funext fun a => detLaplace_eq_prod hQ a

/-- For PSD `Q` and every `a ≥ 0`, the real function `b ↦ F_b(Q)` has
derivative `-F_a(Q) ∑ᵢ λᵢ(1 + aλᵢ)⁻¹` at `a`. -/
theorem hasDerivAt_detLaplace (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    HasDerivAt (detLaplace Q)
      (-(detLaplace Q a) * ∑ i, hQ.isHermitian.eigenvalues i
          * (1 + a * hQ.isHermitian.eigenvalues i)⁻¹) a := by
  rw [detLaplace_eq_prodInv hQ.isHermitian]
  exact hasDerivAt_prodInv _ (factor_pos hQ ha)

/-- First-derivative identity `a ∂_a F_a = -F_a Tr A_a`, for PSD `Q` and every
`a ≥ 0`; `∂_a` is the ordinary derivative of `b ↦ F_b(Q)` at `a`. -/
theorem mul_deriv_detLaplace (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    a * deriv (detLaplace Q) a = -(detLaplace Q a) * (resolventWeight Q a).trace.re := by
  rw [(hasDerivAt_detLaplace hQ ha).deriv, trace_resolventWeight_eq_sum hQ ha, Complex.ofReal_re,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv]
  ring

/-- For PSD `Q` and every `a ≥ 0`, `deriv (b ↦ F_b(Q))` has derivative
`F_a [(∑ᵢ λᵢ(1+aλᵢ)⁻¹)² + ∑ᵢ λᵢ²(1+aλᵢ)⁻²]` at `a`. -/
theorem hasDerivAt_deriv_detLaplace (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    HasDerivAt (deriv (detLaplace Q))
      (detLaplace Q a * ((∑ i, hQ.isHermitian.eigenvalues i
          * (1 + a * hQ.isHermitian.eigenvalues i)⁻¹) ^ 2
        + ∑ i, hQ.isHermitian.eigenvalues i ^ 2
          * ((1 + a * hQ.isHermitian.eigenvalues i)⁻¹) ^ 2)) a := by
  rw [detLaplace_eq_prodInv hQ.isHermitian]
  exact hasDerivAt_deriv_prodInv _ (factor_pos hQ ha)

/-- The second derivative of the determinant-Laplace function: for every PSD `Q` and every real `a ≥ 0`,
`a² ∂_a² F_a = F_a [(Tr A_a)² + Tr A_a²]`, where `∂_a²` is the second
ordinary derivative `deriv (deriv (b ↦ F_b(Q)))` at `a`, and traces are real
parts (the traces are real by `trace_resolventWeight_eq_sum` and
`trace_resolventWeight_sq_eq_sum`). -/
theorem sq_mul_deriv_deriv_detLaplace (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    a ^ 2 * deriv (deriv (detLaplace Q)) a
      = detLaplace Q a * ((resolventWeight Q a).trace.re ^ 2
          + ((resolventWeight Q a) ^ 2).trace.re) := by
  rw [(hasDerivAt_deriv_detLaplace hQ ha).deriv, trace_resolventWeight_eq_sum hQ ha,
    trace_resolventWeight_sq_eq_sum hQ ha, Complex.ofReal_re, Complex.ofReal_re]
  have h1 : a * ∑ i, hQ.isHermitian.eigenvalues i * (1 + a * hQ.isHermitian.eigenvalues i)⁻¹
      = ∑ i, a * hQ.isHermitian.eigenvalues i / (1 + a * hQ.isHermitian.eigenvalues i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]; ring
  have h2 : a ^ 2 * ∑ i, hQ.isHermitian.eigenvalues i ^ 2
        * ((1 + a * hQ.isHermitian.eigenvalues i)⁻¹) ^ 2
      = ∑ i, (a * hQ.isHermitian.eigenvalues i / (1 + a * hQ.isHermitian.eigenvalues i)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]; ring
  rw [← h1, ← h2]
  ring

end Main

end BlockBand.Endpoints.Clock
