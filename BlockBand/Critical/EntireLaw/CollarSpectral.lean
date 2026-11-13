module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# The entire law: deterministic spectral inputs for the collar estimate

* `absResolvent E δ H = cfc w_δ H`, `w_δ(x) = |x - E|⁻¹ 1{|x - E| > δ}` (`collarWeight`): the
  truncated `|R|`.
* `norm_sq_dotProduct_inv_le`: if no eigenvalue of the Hermitian `H` lies within `δ ≥ 0` of `E`,
  `|u^* (H - E)⁻¹ v|² ≤ Re(u^*|R|u) Re(v^*|R|v)` (eigen-decomposition and Cauchy–Schwarz; this
  avoids a second-moment bound on `E|ζ_o^*Rζ_c|²` and needs only `Tr |R|`).
* `re_dotProduct_cfc_mulVec_self_nonneg`, `re_absResolvent_diag_nonneg`,
  `sum_re_absResolvent_diag` (`Σ_x Re|R|_xx = Σ_i w_δ(λ_i)`), `absResolvent_submatrix`
  (`cfc` commutes with permutation reindexing, `StarAlgHom.map_cfc`).
* `collarWeight_le_dyadic`, `sum_collarWeight_le`: at `δ = 2^{-(K+1)}`,
  `Σ_i w_δ(λ_i) ≤ #ι + Σ_{k ≤ K} 2^k #{i : |λ_i - E| ≤ 2^{-k}}` (dyadic splitting).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open Matrix
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quadratic form of the triple product `U D U^*`. -/
theorem dotProduct_conj_diagonal_mulVec (U : Matrix ι ι ℂ) (d : ι → ℂ) (u v : ι → ℂ) :
    star u ⬝ᵥ ((U * diagonal d * star U) *ᵥ v) =
      ∑ i, d i * (star ((star U *ᵥ u) i) * (star U *ᵥ v) i) := by
  have h : star u ᵥ* U = star (star U *ᵥ u) := by
    ext i
    simp only [vecMul, mulVec, dotProduct, Pi.star_apply, star_sum, star_mul', star_apply,
      star_star]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, h]
  simp only [dotProduct, Pi.star_apply, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem continuousOn_spectrum (A : Matrix ι ι ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) :=
  (Matrix.finite_real_spectrum (A := A)).continuousOn f

/-- `cfc f H = U diag(f λ) U^*` written with the eigenvector unitary. -/
theorem cfc_eq_unitary {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ) :
    cfc f H = (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun i => ((f (hH.eigenvalues i) : ℝ) : ℂ)) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) := by
  rw [hH.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

theorem eigenvectorUnitary_star_mul {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    star (hH.eigenvectorUnitary : Matrix ι ι ℂ) * (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  Unitary.coe_star_mul_self _

theorem eigenvectorUnitary_mul_star {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix ι ι ℂ) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  Unitary.coe_mul_star_self _

/-- `H - E = U diag(λ - E) U^*`. -/
theorem sub_smul_eq_unitary {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (E : ℝ) :
    H - (E : ℂ) • 1 = (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun i => ((hH.eigenvalues i - E : ℝ) : ℂ)) *
        star (hH.eigenvectorUnitary : Matrix ι ι ℂ) := by
  set U := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  have hS : H = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hE : (E : ℂ) • (1 : Matrix ι ι ℂ) = U * diagonal (fun _ => (E : ℂ)) * star U := by
    rw [← smul_one_eq_diagonal, mul_smul_comm, mul_one, smul_mul_assoc,
      eigenvectorUnitary_mul_star hH]
  conv_lhs => rw [hS, hE]
  rw [← sub_mul, ← mul_sub, diagonal_sub]
  congr 3
  funext i
  push_cast
  ring

/-- `(H - E)⁻¹ = U diag((λ - E)⁻¹) U^*` when no eigenvalue equals `E`. -/
theorem inv_sub_smul_eq_unitary {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {E : ℝ}
    (hE : ∀ i, hH.eigenvalues i ≠ E) :
    (H - (E : ℂ) • 1)⁻¹ = (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun i => (((hH.eigenvalues i - E)⁻¹ : ℝ) : ℂ)) *
        star (hH.eigenvectorUnitary : Matrix ι ι ℂ) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [sub_smul_eq_unitary hH E]
  set U := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  calc U * diagonal (fun i => ((hH.eigenvalues i - E : ℝ) : ℂ)) * star U *
        (U * diagonal (fun i => (((hH.eigenvalues i - E)⁻¹ : ℝ) : ℂ)) * star U)
      = U * (diagonal (fun i => ((hH.eigenvalues i - E : ℝ) : ℂ)) * (star U * U) *
        diagonal (fun i => (((hH.eigenvalues i - E)⁻¹ : ℝ) : ℂ))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * star U := by
        rw [eigenvectorUnitary_star_mul hH, Matrix.mul_one, diagonal_mul_diagonal]
        congr 1
        convert Matrix.mul_one U using 2
        rw [← diagonal_one]
        congr 1
        funext i
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ (sub_ne_zero.mpr (hE i)), Complex.ofReal_one]
    _ = 1 := eigenvectorUnitary_mul_star hH

/-- Quadratic form of `cfc f H` in eigen-coordinates. -/
theorem dotProduct_cfc_mulVec {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ)
    (u v : ι → ℂ) :
    star u ⬝ᵥ (cfc f H *ᵥ v) = ∑ i, ((f (hH.eigenvalues i) : ℝ) : ℂ) *
      (star ((star (hH.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ u) i) *
        (star (hH.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ v) i) := by
  rw [cfc_eq_unitary hH, dotProduct_conj_diagonal_mulVec]

theorem re_dotProduct_cfc_mulVec_self {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ)
    (u : ι → ℂ) :
    (star u ⬝ᵥ (cfc f H *ᵥ u)).re = ∑ i, f (hH.eigenvalues i) *
      ‖(star (hH.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ u) i‖ ^ 2 := by
  rw [dotProduct_cfc_mulVec hH, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The quadratic form of `cfc f H` is nonnegative for `f ≥ 0` (every square matrix: `cfc` is `0`
off the Hermitian matrices). -/
theorem re_dotProduct_cfc_mulVec_self_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    (H : Matrix ι ι ℂ) (u : ι → ℂ) : 0 ≤ (star u ⬝ᵥ (cfc f H *ᵥ u)).re := by
  by_cases hH : H.IsHermitian
  · rw [re_dotProduct_cfc_mulVec_self hH]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hf _) (sq_nonneg _)
  · have hH' : ¬ IsSelfAdjoint H := hH
    rw [cfc_apply_of_not_predicate H hH']
    simp

/-- The weight `w_δ(x) = |x - E|⁻¹ 1{|x - E| > δ}`. -/
def collarWeight (E δ x : ℝ) : ℝ := if δ < |x - E| then |x - E|⁻¹ else 0

theorem collarWeight_nonneg (E δ x : ℝ) : 0 ≤ collarWeight E δ x := by
  unfold collarWeight; split_ifs <;> positivity

/-- `|R|` truncated at distance `δ` from `E`: `cfc w_δ H`. -/
def absResolvent (E δ : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc (collarWeight E δ) H

/-- **Cauchy–Schwarz for the resolvent**: if no eigenvalue of the Hermitian `H` is within `δ ≥ 0`
of `E`, then `|u^* R v|² ≤ (u^* |R| u)(v^* |R| v)`, `R = (H - E)⁻¹`, `|R| = absResolvent E δ H`. -/
theorem norm_sq_dotProduct_inv_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {E δ : ℝ}
    (hδ : 0 ≤ δ) (hgap : ∀ i, δ < |hH.eigenvalues i - E|) (u v : ι → ℂ) :
    ‖star u ⬝ᵥ ((H - (E : ℂ) • 1)⁻¹ *ᵥ v)‖ ^ 2 ≤
      (star u ⬝ᵥ (absResolvent E δ H *ᵥ u)).re * (star v ⬝ᵥ (absResolvent E δ H *ᵥ v)).re := by
  have hne : ∀ i, hH.eigenvalues i ≠ E := fun i h => by
    have := hgap i; rw [h, sub_self, abs_zero] at this; linarith
  set U := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  set a := star U *ᵥ u
  set c := star U *ᵥ v
  have hw : ∀ i, collarWeight E δ (hH.eigenvalues i) = |hH.eigenvalues i - E|⁻¹ := fun i => by
    unfold collarWeight; rw [ite_eq_left_iff.mpr fun h => absurd (hgap i) h]
  rw [inv_sub_smul_eq_unitary hH hne, dotProduct_conj_diagonal_mulVec, absResolvent,
    re_dotProduct_cfc_mulVec_self hH, re_dotProduct_cfc_mulVec_self hH]
  simp only [hw]
  set x : ι → ℝ := fun i => Real.sqrt |hH.eigenvalues i - E|⁻¹ * ‖a i‖
  set y : ι → ℝ := fun i => Real.sqrt |hH.eigenvalues i - E|⁻¹ * ‖c i‖
  have h1 : ‖∑ i, (((hH.eigenvalues i - E)⁻¹ : ℝ) : ℂ) * (star (a i) * c i)‖ ≤ ∑ i, x i * y i := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp only [x, y, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
    have hs : Real.sqrt |hH.eigenvalues i - E|⁻¹ * Real.sqrt |hH.eigenvalues i - E|⁻¹ =
        |hH.eigenvalues i - E|⁻¹ := Real.mul_self_sqrt (by positivity)
    rw [abs_inv]
    linear_combination (-(‖a i‖ * ‖c i‖)) * hs
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hx : ∀ i, x i ^ 2 = |hH.eigenvalues i - E|⁻¹ * ‖a i‖ ^ 2 := fun i => by
    simp only [x, mul_pow, Real.sq_sqrt (inv_nonneg.mpr (abs_nonneg _))]
  have hy : ∀ i, y i ^ 2 = |hH.eigenvalues i - E|⁻¹ * ‖c i‖ ^ 2 := fun i => by
    simp only [y, mul_pow, Real.sq_sqrt (inv_nonneg.mpr (abs_nonneg _))]
  simp only [hx, hy] at h2
  have h0 : 0 ≤ ∑ i, x i * y i :=
    (norm_nonneg _).trans h1
  calc ‖∑ i, (((hH.eigenvalues i - E)⁻¹ : ℝ) : ℂ) * (star (a i) * c i)‖ ^ 2
      ≤ (∑ i, x i * y i) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem dotProduct_single_mulVec_single (A : Matrix ι ι ℂ) (x : ι) :
    star (Pi.single x 1 : ι → ℂ) ⬝ᵥ (A *ᵥ Pi.single x 1) = A x x := by
  simp [dotProduct, Pi.single_apply]

/-- Diagonal entries of `|R|` have nonnegative real part. -/
theorem re_absResolvent_diag_nonneg (E δ : ℝ) (H : Matrix ι ι ℂ) (x : ι) :
    0 ≤ (absResolvent E δ H x x).re := by
  rw [← dotProduct_single_mulVec_single (absResolvent E δ H) x]
  exact re_dotProduct_cfc_mulVec_self_nonneg (collarWeight_nonneg E δ) H _

/-- `Tr cfc f H = Σ_i f(λ_i)`. -/
theorem trace_cfc_eq {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ) :
    (cfc f H).trace = ∑ i, ((f (hH.eigenvalues i) : ℝ) : ℂ) := by
  rw [cfc_eq_unitary hH, Matrix.trace_mul_cycle, eigenvectorUnitary_star_mul hH, Matrix.one_mul,
    trace_diagonal]

theorem sum_re_absResolvent_diag {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (E δ : ℝ) :
    ∑ x, (absResolvent E δ H x x).re = ∑ i, collarWeight E δ (hH.eigenvalues i) := by
  have h := congrArg Complex.re (trace_cfc_eq hH (collarWeight E δ))
  rw [Matrix.trace, Complex.re_sum, Complex.re_sum] at h
  simpa [absResolvent] using h

/-- Reindexing by a permutation as a star-algebra homomorphism. -/
def reindexStarAlgHom (e : ι ≃ ι) : Matrix ι ι ℂ →⋆ₐ[ℝ] Matrix ι ι ℂ :=
  { (reindexAlgEquiv ℝ ℂ e.symm).toAlgHom with
    map_star' := fun A => by
      change reindex e.symm e.symm (star A) = star (reindex e.symm e.symm A)
      simp only [star_eq_conjTranspose, conjTranspose_reindex] }

theorem reindexStarAlgHom_apply (e : ι ≃ ι) (A : Matrix ι ι ℂ) :
    reindexStarAlgHom e A = A.submatrix e e := rfl

theorem continuous_reindexStarAlgHom (e : ι ≃ ι) : Continuous (reindexStarAlgHom e) := by
  change Continuous fun A : Matrix ι ι ℂ => A.submatrix e e
  fun_prop

/-- `cfc` commutes with reindexing by a permutation. -/
theorem cfc_submatrix {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ) (e : ι ≃ ι) :
    cfc f (H.submatrix e e) = (cfc f H).submatrix e e := by
  have h := StarAlgHom.map_cfc (reindexStarAlgHom e) f H (continuousOn_spectrum H f)
    (continuous_reindexStarAlgHom e) hH (hH.submatrix e)
  rw [reindexStarAlgHom_apply, reindexStarAlgHom_apply] at h
  exact h.symm

theorem absResolvent_submatrix {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (E δ : ℝ) (e : ι ≃ ι) :
    absResolvent E δ (H.submatrix e e) = (absResolvent E δ H).submatrix e e :=
  cfc_submatrix hH _ e

/-- **Dyadic bound** of the truncated weight at `δ = 2^{-(K+1)}`:
`w(x) ≤ 1 + Σ_{k ≤ K} 2^k 1{|x - E| ≤ 2^{-k}}`. -/
theorem collarWeight_le_dyadic (E x : ℝ) (K : ℕ) :
    collarWeight E ((1 / 2 : ℝ) ^ (K + 1)) x ≤
      1 + ∑ k ∈ Finset.range (K + 1),
        (2 : ℝ) ^ k * (if |x - E| ≤ (1 / 2 : ℝ) ^ k then 1 else 0) := by
  have hS : ∀ K : ℕ, 0 ≤ ∑ k ∈ Finset.range (K + 1),
      (2 : ℝ) ^ k * (if |x - E| ≤ (1 / 2 : ℝ) ^ k then 1 else 0) := fun K =>
    Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (by split_ifs <;> norm_num)
  unfold collarWeight
  split_ifs with hx
  swap
  · linarith [hS K]
  set t := |x - E|
  have ht : 0 < t := lt_of_le_of_lt (by positivity) hx
  clear_value t
  induction K with
  | zero =>
    simp only [zero_add, pow_one] at hx
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul]
    split_ifs with h1
    · rw [inv_le_iff_one_le_mul₀ ht]; linarith
    · rw [not_le] at h1
      rw [add_zero]
      exact (inv_lt_one_of_one_lt₀ h1).le
  | succ K ih =>
    by_cases h : (1 / 2 : ℝ) ^ (K + 1) < t
    · refine (ih h).trans ?_
      rw [Finset.sum_range_succ _ (K + 1)]
      have : 0 ≤ (2 : ℝ) ^ (K + 1) * (if t ≤ (1 / 2 : ℝ) ^ (K + 1) then 1 else 0) :=
        mul_nonneg (by positivity) (by split_ifs <;> norm_num)
      linarith
    · rw [not_lt] at h
      have hall : ∀ k ∈ Finset.range (K + 1 + 1),
          (2 : ℝ) ^ k * (if t ≤ (1 / 2 : ℝ) ^ k then 1 else 0) = 2 ^ k := by
        intro k hk
        have hk' : k ≤ K + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [ite_eq_left_iff.mpr fun hc => absurd (h.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk')) hc, mul_one]
      rw [Finset.sum_congr rfl hall]
      have hgeom : ∑ k ∈ Finset.range (K + 1 + 1), (2 : ℝ) ^ k = 2 ^ (K + 1 + 1) - 1 := by
        have := geom_sum_mul (2 : ℝ) (K + 1 + 1)
        linarith
      rw [hgeom]
      have h2 : t⁻¹ < 2 ^ (K + 1 + 1) := by
        rw [inv_lt_comm₀ ht (by positivity), ← inv_pow]
        simpa [one_div] using hx
      linarith

omit [DecidableEq ι] in
/-- Summed dyadic bound: `Σ_i w(λ_i) ≤ #ι + Σ_{k ≤ K} 2^k #{i : |λ_i - E| ≤ 2^{-k}}`. -/
theorem sum_collarWeight_le (lam : ι → ℝ) (E : ℝ) (K : ℕ) :
    ∑ i, collarWeight E ((1 / 2 : ℝ) ^ (K + 1)) (lam i) ≤
      (Fintype.card ι : ℝ) + ∑ k ∈ Finset.range (K + 1),
        (2 : ℝ) ^ k * ((Finset.univ.filter fun i => |lam i - E| ≤ (1 / 2 : ℝ) ^ k).card : ℝ) := by
  refine (Finset.sum_le_sum fun i _ => collarWeight_le_dyadic E (lam i) K).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, Finset.sum_boole]

end BlockBand.Critical.EntireLaw
