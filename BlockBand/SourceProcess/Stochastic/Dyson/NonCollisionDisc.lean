module

public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionPoly
public import BlockBand.SourceProcess.Stochastic.Dyson.GUEMoments
public import BlockBand.SourceProcess.Stochastic.Dyson.Lagrange
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# The trace discriminant: non-simple spectrum is a polynomial zero set

`traceDisc N H = det [tr(H^{k+l})]_{k,l<N}`. For `H = U diag(μ) U*` with `U` unitary this is
`det(V(μ))²` (Vandermonde), so:
* `traceDisc_eq_zero_of_not_simple`: a Hermitian matrix without simple spectrum has `traceDisc = 0`;
* `traceDisc_diagonal_ne_zero`: `diag(0, 1, …, N-1)` has `traceDisc ≠ 0`.
For a fixed matrix `F₀`, `r ↦ traceDisc (F₀ + hermitianOfCoords N r)` is the evaluation of the
polynomial `discPoly N F₀` in the real coordinates `r` (`evalR_discPoly`), which is nonzero
when `F₀` is Hermitian (`discPoly_ne_zero`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory Matrix MvPolynomial
open scoped Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- The Hankel–trace discriminant `det [tr(H^{k+l})]_{k,l<N}`. -/
def traceDisc (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  det (Matrix.of fun k l : Fin N => trace (H ^ ((k : ℕ) + l)))

theorem conj_pow_of_unitary {U D : Matrix (Fin N) (Fin N) ℂ} (hU : star U * U = 1)
    (hU' : U * star U = 1) (m : ℕ) :
    (U * D * star U) ^ m = U * D ^ m * star U := by
  induction m with
  | zero =>
    simp only [pow_zero, Matrix.mul_one, hU']
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    calc U * D ^ m * star U * (U * D * star U) = U * D ^ m * (star U * U) * D * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (D ^ m * D) * star U := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- `traceDisc (U diag(μ) U*) = det(V(μ))²` for unitary `U`. -/
theorem traceDisc_conj {U : Matrix (Fin N) (Fin N) ℂ} (hU : star U * U = 1)
    (hU' : U * star U = 1) (μ : Fin N → ℂ) :
    traceDisc N (U * diagonal μ * star U) = det (vandermonde μ) ^ 2 := by
  have htr : ∀ m : ℕ, trace ((U * diagonal μ * star U) ^ m) = ∑ i, μ i ^ m := by
    intro m
    rw [conj_pow_of_unitary hU hU', trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
      diagonal_pow, trace_diagonal]
    rfl
  have hM : (Matrix.of fun k l : Fin N => trace ((U * diagonal μ * star U) ^ ((k : ℕ) + l))) =
      (vandermonde μ)ᵀ * vandermonde μ := by
    ext k l
    rw [of_apply, htr]
    simp only [mul_apply, transpose_apply, vandermonde_apply, pow_add]
  unfold traceDisc
  rw [hM, det_mul, det_transpose, sq]

theorem traceDisc_eq_zero_of_not_simple {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (h : ¬ HasSimpleSpectrum N H) : traceDisc N H = 0 := by
  rw [spectral_eq hH, traceDisc_conj (specU_star_mul H) (specU_mul_star H)]
  have hanti : Antitone (dysonEigenvalue N H) := fun i j hij => by
    unfold dysonEigenvalue
    exact div_le_div_of_nonneg_right ((Matrix.isHermitian_add_transpose_self H).eigenvalues₀_antitone
      (Fin.le_def.mpr (Fin.le_def.mp hij))) (by norm_num)
  have hni : ¬ Function.Injective (dysonEigenvalue N H) := fun hi =>
    h (hanti.strictAnti_of_injective hi)
  have : ¬ Function.Injective (fun k => (dysonEigenvalue N H (specPerm N k) : ℂ)) := by
    intro hi
    apply hni
    intro i j hij
    have := @hi ((specPerm N).symm i) ((specPerm N).symm j) (by simp [hij])
    simpa using this
  have h0 : det (vandermonde fun k => (dysonEigenvalue N H (specPerm N k) : ℂ)) = 0 := by
    by_contra hne; exact this (det_vandermonde_ne_zero_iff.mp hne)
  rw [h0]; ring

theorem traceDisc_diagonal_ne_zero :
    traceDisc N (diagonal fun i : Fin N => ((i : ℕ) : ℂ)) ≠ 0 := by
  have h := traceDisc_conj (U := (1 : Matrix (Fin N) (Fin N) ℂ)) (by simp) (by simp)
    (fun i : Fin N => ((i : ℕ) : ℂ))
  simp only [Matrix.one_mul, star_one, Matrix.mul_one] at h
  rw [h]
  refine pow_ne_zero 2 (det_vandermonde_ne_zero_iff.mpr fun i j hij => ?_)
  exact Fin.ext (by exact_mod_cast hij)

/-!
### The discriminant as a polynomial in the GUE coordinates
-/

/-- Index set of the real GUE coordinates. -/
abbrev GIdx (N : ℕ) := (Fin N × Fin N) × Fin 2

/-- `F₀ + hermitianOfCoords N r` with `r` replaced by polynomial variables. -/
def matPoly (N : ℕ) (F₀ : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (GIdx N) ℂ) :=
  Matrix.of fun a b => C (F₀ a b) + C (gueScale N) * ((X ((a, b), 0) + X ((a, b), 1) * C Complex.I)
    + (X ((b, a), 0) - X ((b, a), 1) * C Complex.I))

/-- The discriminant polynomial of `F₀ + hermitianOfCoords N r` in the variables `r`. -/
def discPoly (N : ℕ) (F₀ : Matrix (Fin N) (Fin N) ℂ) : MvPolynomial (GIdx N) ℂ :=
  det (Matrix.of fun k l : Fin N => trace (matPoly N F₀ ^ ((k : ℕ) + l)))

theorem map_matPoly (F₀ : Matrix (Fin N) (Fin N) ℂ) (r : GIdx N → ℝ) :
    (matPoly N F₀).map (eval fun i => (r i : ℂ)) = F₀ + hermitianOfCoords N r := by
  ext a b
  simp [matPoly, hermitianOfCoords_apply]

theorem evalR_discPoly (F₀ : Matrix (Fin N) (Fin N) ℂ) (r : GIdx N → ℝ) :
    evalR r (discPoly N F₀) = traceDisc N (F₀ + hermitianOfCoords N r) := by
  set f : MvPolynomial (GIdx N) ℂ →+* ℂ := eval fun i => (r i : ℂ)
  change f (discPoly N F₀) = _
  rw [discPoly, RingHom.map_det, traceDisc, ← map_matPoly F₀ r]
  congr 1
  ext k l
  simp only [RingHom.mapMatrix_apply, map_apply, of_apply]
  rw [AddMonoidHom.map_trace f, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]

/-- Every Hermitian matrix is `hermitianOfCoords` of some coordinates (`N > 0` not needed). -/
theorem exists_hermitianOfCoords_eq {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) :
    ∃ r, hermitianOfCoords N r = K := by
  refine ⟨fun x => Real.sqrt N * if x.2 = 0 then (K x.1.1 x.1.2).re else (K x.1.1 x.1.2).im, ?_⟩
  ext a b
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Fin.pos a).ne'
  have hN : (Real.sqrt N : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  have hba : K b a = conj (K a b) := by
    rw [← hK.apply a b]; simp
  rw [hermitianOfCoords_apply, hba]
  simp only [gueScale, Fin.isValue, ite_true, one_ne_zero, ite_false, Complex.ofReal_mul,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_neg]
  field_simp
  apply Complex.ext <;> simp <;> ring_nf <;> rw [Real.sq_sqrt (Nat.cast_nonneg _)] <;>
    field_simp

theorem discPoly_ne_zero {F₀ : Matrix (Fin N) (Fin N) ℂ} (hF₀ : F₀.IsHermitian) :
    discPoly N F₀ ≠ 0 := by
  have hK : (diagonal (fun i : Fin N => ((i : ℕ) : ℂ)) - F₀).IsHermitian :=
    (isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)).sub hF₀
  obtain ⟨r, hr⟩ := exists_hermitianOfCoords_eq hK
  intro h0
  have := evalR_discPoly F₀ r
  rw [h0, hr, add_sub_cancel] at this
  exact traceDisc_diagonal_ne_zero (by rw [← this]; simp)

end BlockBand.SourceProcess.Stochastic.Dyson
