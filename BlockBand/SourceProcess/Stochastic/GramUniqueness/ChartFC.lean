module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartSqrt
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.Normed
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Functional calculus of the Hermitian part, Lipschitz in the Frobenius norm

For `A : Matrix n n ℂ`, `hermPart A = (A + Aᴴ)/2` and `fcM f A = U diag(f(λ)) Uᴴ` (spectral
decomposition of `hermPart A`, Mathlib's `eigenvectorUnitary`). Frobenius norm (local instance).

* `fcM_conjTranspose`, `fcM_mul`, `fcM_id`: `fcM f A` is Hermitian, multiplicative in `f`, and
  `fcM id A = hermPart A`.
* **`norm_fcM_sub_le`** (Kittaneh's Hilbert–Schmidt bound): for `L`-Lipschitz `f`,
  `‖fcM f A - fcM f B‖ ≤ L ‖hermPart A - hermPart B‖ ≤ L ‖A - B‖` (`norm_hermPart_sub_le`).
  Proof: `Uᴴ (fcM f A - fcM f B) W` has entries `(f λ_i - f μ_j) (UᴴW)_ij`, and the Frobenius norm
  is unitarily invariant (`sqF_conj_unitary`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open Matrix
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian part `(A + Aᴴ)/2`. -/
def hermPart (A : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (A + Aᴴ)

omit [Fintype n] [DecidableEq n] in
theorem isHermitian_hermPart (A : Matrix n n ℂ) : (hermPart A).IsHermitian := by
  unfold hermPart IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

omit [Fintype n] [DecidableEq n] in
theorem hermPart_of_herm {A : Matrix n n ℂ} (h : Aᴴ = A) : hermPart A = A := by
  unfold hermPart
  rw [h, ← two_smul ℂ A, smul_smul]
  norm_num

/-- The eigenvector unitary of `hermPart A`. -/
def eU (A : Matrix n n ℂ) : Matrix n n ℂ :=
  ((isHermitian_hermPart A).eigenvectorUnitary : Matrix n n ℂ)

/-- The eigenvalues of `hermPart A`. -/
def eL (A : Matrix n n ℂ) : n → ℝ := (isHermitian_hermPart A).eigenvalues

theorem eU_star_mul (A : Matrix n n ℂ) : star (eU A) * eU A = 1 := Unitary.coe_star_mul_self _

theorem eU_mul_star (A : Matrix n n ℂ) : eU A * star (eU A) = 1 := Unitary.coe_mul_star_self _

/-- `f(hermPart A)` by the spectral decomposition. -/
def fcM (f : ℝ → ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  eU A * diagonal (fun i => ((f (eL A i) : ℝ) : ℂ)) * star (eU A)

theorem fcM_id (A : Matrix n n ℂ) : fcM id A = hermPart A := by
  conv_rhs => rw [(isHermitian_hermPart A).spectral_theorem]
  simp [fcM, eU, eL, Unitary.conjStarAlgAut_apply, Function.comp_def]

theorem fcM_conjTranspose (f : ℝ → ℝ) (A : Matrix n n ℂ) : (fcM f A)ᴴ = fcM f A := by
  rw [← star_eq_conjTranspose]
  simp only [fcM, star_mul, star_star, Matrix.mul_assoc]
  congr 1
  rw [star_eq_conjTranspose (diagonal _), diagonal_conjTranspose]
  congr 2
  funext i
  simp

theorem fcM_mul (f g : ℝ → ℝ) (A : Matrix n n ℂ) :
    fcM f A * fcM g A = fcM (fun x => f x * g x) A := by
  simp only [fcM]
  calc eU A * diagonal (fun i => ((f (eL A i) : ℝ) : ℂ)) * star (eU A) *
        (eU A * diagonal (fun i => ((g (eL A i) : ℝ) : ℂ)) * star (eU A))
      = eU A * diagonal (fun i => ((f (eL A i) : ℝ) : ℂ)) * (star (eU A) * eU A) *
          diagonal (fun i => ((g (eL A i) : ℝ) : ℂ)) * star (eU A) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [eU_star_mul, Matrix.mul_one, Matrix.mul_assoc (eU A), diagonal_mul_diagonal]
        congr 3
        funext i
        push_cast
        rfl

/-- If `f(λ)² = λ` on the spectrum, `fcM f A` is a square root of `hermPart A`. -/
theorem fcM_mul_self {f : ℝ → ℝ} {A : Matrix n n ℂ} (hf : ∀ i, f (eL A i) * f (eL A i) = eL A i) :
    fcM f A * fcM f A = hermPart A := by
  rw [fcM_mul, ← fcM_id]
  simp only [fcM]
  congr 3
  funext i
  rw [hf i]
  rfl

/-- Squared Frobenius norm as a sum. -/
def sqF (Z : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖Z i j‖ ^ 2

omit [DecidableEq n] in
theorem norm_sq_eq_sqF (Z : Matrix n n ℂ) : ‖Z‖ ^ 2 = sqF Z := by
  rw [frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => by positivity)]
  simp only [sqF, Real.rpow_two]

omit [DecidableEq n] in
theorem sqF_eq_trace (Z : Matrix n n ℂ) : sqF Z = (trace (Zᴴ * Z)).re := by
  simp only [sqF, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem sqF_conj_unitary {U W : Matrix n n ℂ} (hU : U * star U = 1) (hW : W * star W = 1)
    (Z : Matrix n n ℂ) : sqF (star U * Z * W) = sqF Z := by
  rw [sqF_eq_trace, sqF_eq_trace]
  congr 1
  have e : (star U * Z * W)ᴴ * (star U * Z * W) = star W * (star Z * Z) * W := by
    simp only [← star_eq_conjTranspose, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U (star U), hU, Matrix.one_mul]
  rw [e, trace_mul_cycle, hW, Matrix.one_mul, star_eq_conjTranspose]

theorem conj_fcM_sub (f : ℝ → ℝ) (A B : Matrix n n ℂ) :
    star (eU A) * (fcM f A - fcM f B) * eU B =
      of fun i j => (((f (eL A i) : ℝ) : ℂ) - ((f (eL B j) : ℝ) : ℂ)) *
        (star (eU A) * eU B) i j := by
  have h1 : star (eU A) * fcM f A * eU B =
      diagonal (fun i => ((f (eL A i) : ℝ) : ℂ)) * (star (eU A) * eU B) := by
    simp only [fcM, ← Matrix.mul_assoc, eU_star_mul, Matrix.one_mul]
  have h2 : star (eU A) * fcM f B * eU B =
      (star (eU A) * eU B) * diagonal (fun i => ((f (eL B i) : ℝ) : ℂ)) := by
    simp only [fcM, Matrix.mul_assoc, eU_star_mul, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2]
  ext i j
  simp [diagonal_mul, mul_diagonal, sub_mul, mul_comm]

/-- **Kittaneh's bound.** -/
theorem norm_fcM_sub_le {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (A B : Matrix n n ℂ) :
    ‖fcM f A - fcM f B‖ ≤ L * ‖hermPart A - hermPart B‖ := by
  set Z := star (eU A) * eU B
  have hX := sqF_conj_unitary (eU_mul_star A) (eU_mul_star B) (fcM f A - fcM f B)
  have hY := sqF_conj_unitary (eU_mul_star A) (eU_mul_star B) (fcM id A - fcM id B)
  rw [conj_fcM_sub] at hX hY
  rw [fcM_id, fcM_id] at hY
  have key : ‖fcM f A - fcM f B‖ ^ 2 ≤ ((L : ℝ) * ‖hermPart A - hermPart B‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq_sqF, norm_sq_eq_sqF, ← hX, ← hY]
    simp only [sqF, of_apply, norm_mul, mul_pow, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, ← mul_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    have := hf.dist_le_mul (eL A i) (eL B j)
    rwa [Real.dist_eq, Real.dist_eq] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key

omit [DecidableEq n] in
theorem norm_hermPart_sub_le (A B : Matrix n n ℂ) : ‖hermPart A - hermPart B‖ ≤ ‖A - B‖ := by
  have e : hermPart A - hermPart B = (1 / 2 : ℂ) • ((A - B) + (A - B)ᴴ) := by
    simp only [hermPart, conjTranspose_sub, smul_add, smul_sub]; abel
  rw [e, norm_smul]
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans ?_
  rw [frobenius_norm_conjTranspose]
  norm_num
  linarith [norm_nonneg (A - B)]

/-- **`A ↦ fcM f A` is Lipschitz** in the Frobenius norm. -/
theorem lipschitzWith_fcM {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (fcM (n := n) f) :=
  LipschitzWith.of_dist_le_mul fun A B => by
    rw [dist_eq_norm, dist_eq_norm]
    exact (norm_fcM_sub_le hf A B).trans
      (mul_le_mul_of_nonneg_left (norm_hermPart_sub_le A B) L.2)

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
