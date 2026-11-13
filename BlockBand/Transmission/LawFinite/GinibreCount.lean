module

public import BlockBand.Transmission.LawFinite.GinibreGram

/-!
# Deterministic count bound: `#{λ_i < a}·log(1/a) ≤ Tr BᴴB - Σ_j log‖gs_j‖²`

Used with `W⁻¹ E Σ log⁻(s_i²) ≤ C_b` and Markov. For `λ_i > 0`:
`1{λ_i < a} log(1/a) ≤ λ_i - log λ_i`, and `Σ log λ_i = log det(BᴴB) = Σ_j log ‖gs_j‖²`
(`det_gram_eq`).
* `count_mul_log_le`: the real inequality when every `gs_j ≠ 0`;
* **`ofReal_count_mul_log_le`**: the `ℝ≥0∞` form with `nlog` and arbitrary normalisations
  `m_j > 0`, valid for every column family (if some `gs_j = 0` the right side is `∞`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder

variable {W : ℕ}

section Eigen

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

theorem sum_increasingEigenvalue {M : Type*} [AddCommMonoid M] (hA : A.IsHermitian)
    (f : ℝ → M) :
    ∑ i, f (BlockBand.Foundations.Spectral.increasingEigenvalue hA i) =
      ∑ j, f (hA.eigenvalues j) := by
  simp only [BlockBand.Foundations.Spectral.increasingEigenvalue, IsHermitian.eigenvalues]
  rw [Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => f (hA.eigenvalues₀ k))]
  exact Equiv.sum_comp Fin.revPerm (fun k => f (hA.eigenvalues₀ k))

theorem prod_increasingEigenvalue {M : Type*} [CommMonoid M] (hA : A.IsHermitian)
    (f : ℝ → M) :
    ∏ i, f (BlockBand.Foundations.Spectral.increasingEigenvalue hA i) =
      ∏ j, f (hA.eigenvalues j) := by
  simp only [BlockBand.Foundations.Spectral.increasingEigenvalue, IsHermitian.eigenvalues]
  rw [Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => f (hA.eigenvalues₀ k))]
  exact Equiv.prod_comp Fin.revPerm (fun k => f (hA.eigenvalues₀ k))

end Eigen

theorem increasingEigenvalue_gram_nonneg (B : Matrix (Fin W) (Fin W) ℂ)
    (i : Fin (Fintype.card (Fin W))) :
    0 ≤ BlockBand.Foundations.Spectral.increasingEigenvalue
      (isHermitian_conjTranspose_mul_self B) i := by
  have h := (posSemidef_conjTranspose_mul_self B).eigenvalues_nonneg
    ((Fintype.equivOfCardEq (Fintype.card_fin _)) i.rev)
  simpa [BlockBand.Foundations.Spectral.increasingEigenvalue, IsHermitian.eigenvalues] using h

/-- `Σ_j |c_j|² = Σ_j chiSum W (c j)`. -/
theorem trace_gram_re (c : Fin W → Fin W → ℂ) :
    ((colsMat c)ᴴ * colsMat c).trace.re = ∑ j, chiSum W (c j) := by
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag, Matrix.mul_apply, Complex.re_sum, chiSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [x.isLt, ↓reduceIte]
  simp only [colsMat, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  rw [Complex.conj_mul']
  norm_cast

/-- **Real count bound** when every Gram–Schmidt vector is nonzero. -/
theorem count_mul_log_le (c : Fin W → Fin W → ℂ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hgs : ∀ j, gsC c j ≠ 0) :
    (smallSingularCount a (colsMat c) : ℝ) * Real.log a⁻¹ ≤
      ∑ j, chiSum W (c j) - ∑ j, Real.log (‖gsC c j‖ ^ 2) := by
  set hA := isHermitian_conjTranspose_mul_self (colsMat c)
  set lam := fun i => BlockBand.Foundations.Spectral.increasingEigenvalue hA i
  have hnn : ∀ i, 0 ≤ lam i := increasingEigenvalue_gram_nonneg (colsMat c)
  have hprodC : ∏ i, ((lam i : ℝ) : ℂ) = ((∏ j, ‖gsC c j‖ ^ 2 : ℝ) : ℂ) := by
    have hd : ((colsMat c)ᴴ * colsMat c).det = ∏ j, ((hA.eigenvalues j : ℝ) : ℂ) := by
      exact_mod_cast hA.det_eq_prod_eigenvalues
    rw [prod_increasingEigenvalue hA (fun x => ((x : ℝ) : ℂ)), ← hd,
      det_gram_eq, Complex.ofReal_prod]
  have hprod : ∏ i, lam i = ∏ j, ‖gsC c j‖ ^ 2 := by
    exact_mod_cast hprodC
  have hgpos : ∀ j, 0 < ‖gsC c j‖ ^ 2 := fun j => by
    have := norm_pos_iff.2 (hgs j); positivity
  have hpos : ∀ i, 0 < lam i := by
    intro i
    refine lt_of_le_of_ne (hnn i) (fun h => ?_)
    have h0 : ∏ i, lam i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h.symm
    rw [hprod] at h0
    exact (Finset.prod_ne_zero_iff.2 fun j _ => (hgpos j).ne') h0
  have hlog : ∑ i, Real.log (lam i) = ∑ j, Real.log (‖gsC c j‖ ^ 2) := by
    rw [← Real.log_prod (fun i _ => (hpos i).ne'), hprod,
      Real.log_prod (fun j _ => (hgpos j).ne')]
  have htr : ∑ i, lam i = ∑ j, chiSum W (c j) := by
    rw [← trace_gram_re, hA.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact (sum_increasingEigenvalue hA id).trans
      (Finset.sum_congr rfl fun i _ => (Complex.ofReal_re _).symm)
  have hcount : (smallSingularCount a (colsMat c) : ℝ) =
      ∑ i, if lam i < a then (1 : ℝ) else 0 := by
    rw [smallSingularCount, Finset.sum_boole]
  rw [hcount, Finset.sum_mul, ← htr, ← hlog, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hl := Real.log_le_sub_one_of_pos (hpos i)
  split_ifs with hi
  · have : Real.log a⁻¹ ≤ -Real.log (lam i) := by
      rw [Real.log_inv]
      exact neg_le_neg (Real.log_le_log (hpos i) hi.le)
    linarith [hnn i]
  · linarith

theorem ofReal_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

/-- **`ℝ≥0∞` count bound**, for every column family and normalisations `m_j > 0`. -/
theorem ofReal_count_mul_log_le (c : Fin W → Fin W → ℂ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (m : Fin W → ℝ) (hm : ∀ j, 0 < m j) :
    ENNReal.ofReal ((smallSingularCount a (colsMat c) : ℝ) * Real.log a⁻¹) ≤
      ENNReal.ofReal (∑ j, chiSum W (c j)) +
        ∑ j, (nlog (‖gsC c j‖ ^ 2 / m j) + ENNReal.ofReal (Real.log (m j)⁻¹)) := by
  by_cases hgs : ∀ j, gsC c j ≠ 0
  · have hgpos : ∀ j, 0 < ‖gsC c j‖ ^ 2 / m j := fun j => by
      have := norm_pos_iff.2 (hgs j); have := hm j; positivity
    have hreal := count_mul_log_le c ha0 ha1 hgs
    have hsplit : ∀ j, -Real.log (‖gsC c j‖ ^ 2) =
        -Real.log (‖gsC c j‖ ^ 2 / m j) + Real.log (m j)⁻¹ := fun j => by
      have := norm_pos_iff.2 (hgs j)
      rw [Real.log_div (by positivity) (hm j).ne', Real.log_inv]; ring
    have hreal' : (smallSingularCount a (colsMat c) : ℝ) * Real.log a⁻¹ ≤
        ∑ j, chiSum W (c j) +
          ∑ j, (-Real.log (‖gsC c j‖ ^ 2 / m j) + Real.log (m j)⁻¹) := by
      rw [← Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_neg_distrib]; linarith
    refine (ENNReal.ofReal_le_ofReal hreal').trans (ENNReal.ofReal_add_le.trans
      (add_le_add le_rfl ((ofReal_sum_le' _ _).trans (Finset.sum_le_sum fun j _ => ?_))))
    refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
    simp only [nlog, hgpos j, ↓reduceIte, le_refl]
  · push Not at hgs
    obtain ⟨j, hj⟩ := hgs
    have htop : nlog (‖gsC c j‖ ^ 2 / m j) = ⊤ := by
      rw [nlog, hj]; simp
    have : (∑ j, (nlog (‖gsC c j‖ ^ 2 / m j) + ENNReal.ofReal (Real.log (m j)⁻¹))) = ⊤ := by
      rw [ENNReal.sum_eq_top]
      exact ⟨j, Finset.mem_univ j, by rw [htop, top_add]⟩
    rw [this, add_top]
    exact le_top

end BlockBand.Transmission.LawFinite
