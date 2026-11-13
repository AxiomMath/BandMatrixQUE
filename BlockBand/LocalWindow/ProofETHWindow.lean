module

public import Mathlib

/-!
# From eigenstate thermalization (ETH) on a window to every eigenvector

Deterministic transfer of eigenvector overlap bounds from the eigenvectors of a comparison matrix
`Â` in a spectral window to every approximate eigenvector of `A`, without a spectral gap, for
part (ii) of the physical local-window lemma.

## Main results

* `orthonormal_expand`, `sqNorm_eq_sum_coeff` (completeness and Parseval of an orthonormal
  family indexed by the coordinates).
* `outside_window_le`: if `Â` is Hermitian with orthonormal eigenvectors `e_k` (eigenvalues
  `μ_k`), `A u = λ u`, `‖(A - Â)u‖ ≤ r` and `|μ_k - λ| ≥ h > 0` off a set `S`, then
  `Σ_{k ∉ S} |⟨e_k, u⟩|² ≤ (r/h)²` (no gap assumption).
* `window_transfer`: if moreover the ETH pair bounds
  `|e_k* J e_l - δ_{kl} c_k| ≤ ε` hold for `k, l ∈ S`, `|c_k - c₀| ≤ ε'` on `S`, and `J` is a
  contraction (`|x* J y| ≤ ‖x‖‖y‖`), then for every unit `u` with `A u = λ u`:
  `|u* J u - c₀| ≤ |S| ε + ε' + 2τ + (1 + |c₀|) τ²`, `τ = r/h`.
  (`|S| ε` is the term `rank P · W^{-1/2+β}`; the window radius `h` and the grid error `r`
  give `τ = r_W W^{1-β}`.)
* `bilinear_le_of_opNorm_le`: an `L²`-operator-norm contraction satisfies the bilinear bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofETH

open Matrix Finset
open scoped Matrix.Norms.L2Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `Σ_k |x_k|²`. -/
def sqNorm (x : ι → ℂ) : ℝ := ∑ k, ‖x k‖ ^ 2

theorem sqNorm_nonneg (x : ι → ℂ) : 0 ≤ sqNorm x := by
  unfold sqNorm; positivity

theorem star_dotProduct_self (x : ι → ℂ) : star x ⬝ᵥ x = ((sqNorm x : ℝ) : ℂ) := by
  simp only [sqNorm, dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/-- Orthonormal family indexed by the coordinates. -/
def IsOrthonormalFamily (e : ι → ι → ℂ) : Prop :=
  ∀ k l, star (e k) ⬝ᵥ e l = if k = l then 1 else 0

/-- Expansion of a sesquilinear form along two finite combinations. -/
theorem star_sum_dotProduct_mulVec_sum (J : Matrix ι ι ℂ) (e : ι → ι → ℂ) (a b : ι → ℂ)
    (S T : Finset ι) :
    star (∑ k ∈ S, a k • e k) ⬝ᵥ (J *ᵥ ∑ l ∈ T, b l • e l) =
      ∑ k ∈ S, ∑ l ∈ T, star (a k) * b l * (star (e k) ⬝ᵥ (J *ᵥ e l)) := by
  rw [star_sum, mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **Completeness**: `u = Σ_k ⟨e_k, u⟩ e_k` for an orthonormal family indexed by `ι`. -/
theorem orthonormal_expand {e : ι → ι → ℂ} (he : IsOrthonormalFamily e) (u : ι → ℂ) :
    u = ∑ k, (star (e k) ⬝ᵥ u) • e k := by
  set U : Matrix ι ι ℂ := Matrix.of fun x k => e k x
  have hUU : Uᴴ * U = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← he k l]
    simp [U, dotProduct, Matrix.conjTranspose_apply]
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hUU
  have h1 : u = U *ᵥ (Uᴴ *ᵥ u) := by rw [mulVec_mulVec, hUU', one_mulVec]
  conv_lhs => rw [h1]
  ext x
  simp only [mulVec, dotProduct, U, Matrix.of_apply, Matrix.conjTranspose_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `‖Σ_{k∈S} a_k e_k‖² = Σ_{k∈S} |a_k|²`. -/
theorem sqNorm_sum_smul {e : ι → ι → ℂ} (he : IsOrthonormalFamily e) (a : ι → ℂ)
    (S : Finset ι) : sqNorm (∑ k ∈ S, a k • e k) = ∑ k ∈ S, ‖a k‖ ^ 2 := by
  have he' : ∀ k l, star (e k) ⬝ᵥ e l = if k = l then 1 else 0 := he
  have h := star_sum_dotProduct_mulVec_sum 1 e a a S S
  simp only [one_mulVec, he'] at h
  rw [star_dotProduct_self] at h
  have h2 : ∀ k ∈ S, (∑ l ∈ S, star (a k) * a l * (if k = l then (1 : ℂ) else 0)) =
      ((‖a k‖ ^ 2 : ℝ) : ℂ) := by
    intro k hk
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (fun h => absurd hk h)]
    simp only [ite_true, mul_one, Complex.ofReal_pow]
    rw [Complex.star_def, Complex.conj_mul']
  rw [Finset.sum_congr rfl h2, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- **Parseval**: `‖u‖² = Σ_k |⟨e_k, u⟩|²`. -/
theorem sqNorm_eq_sum_coeff {e : ι → ι → ℂ} (he : IsOrthonormalFamily e) (u : ι → ℂ) :
    sqNorm u = ∑ k, ‖star (e k) ⬝ᵥ u‖ ^ 2 := by
  conv_lhs => rw [orthonormal_expand he u]
  exact sqNorm_sum_smul he _ _

/-- `⟨e_k, Â u⟩ = μ_k ⟨e_k, u⟩` for Hermitian `Â` and an eigenvector `e_k`. -/
theorem coeff_mulVec {Ahat : Matrix ι ι ℂ} (hA : Ahat.IsHermitian) {v : ι → ℂ} {μ : ℝ}
    (hv : Ahat *ᵥ v = (μ : ℂ) • v) (u : ι → ℂ) :
    star v ⬝ᵥ (Ahat *ᵥ u) = (μ : ℂ) * (star v ⬝ᵥ u) := by
  rw [dotProduct_mulVec]
  have : star v ᵥ* Ahat = star (Ahat *ᵥ v) := by
    rw [star_mulVec, hA.eq]
  rw [this, hv, star_smul, smul_dotProduct, smul_eq_mul]
  congr 1
  simp

/-- **Outside-window component** (the spectral theorem without a gap): for
Hermitian `Â` with orthonormal eigenvectors `e_k` (eigenvalues `μ_k`), `A u = λ u`,
`‖(A - Â)u‖² ≤ r²` and `h ≤ |μ_k - λ|` for `k ∉ S` (`h > 0`), the coefficients of `u`
outside `S` satisfy `Σ_{k ∉ S} |⟨e_k, u⟩|² ≤ (r/h)²`. -/
theorem outside_window_le {A Ahat : Matrix ι ι ℂ} (hAhat : Ahat.IsHermitian) {e : ι → ι → ℂ}
    (he : IsOrthonormalFamily e) {μ : ι → ℝ} (heig : ∀ k, Ahat *ᵥ e k = (μ k : ℂ) • e k)
    {u : ι → ℂ} {lam : ℝ} (hAu : A *ᵥ u = (lam : ℂ) • u) {r h : ℝ} (hh : 0 < h)
    (hpert : sqNorm ((A - Ahat) *ᵥ u) ≤ r ^ 2) {S : Finset ι}
    (hS : ∀ k ∉ S, h ≤ |μ k - lam|) :
    ∑ k ∈ Sᶜ, ‖star (e k) ⬝ᵥ u‖ ^ 2 ≤ (r / h) ^ 2 := by
  set w := (A - Ahat) *ᵥ u
  have hcoef : ∀ k, star (e k) ⬝ᵥ w = ((lam - μ k : ℝ) : ℂ) * (star (e k) ⬝ᵥ u) := by
    intro k
    simp only [w, sub_mulVec, dotProduct_sub, hAu, dotProduct_smul, smul_eq_mul,
      coeff_mulVec hAhat (heig k) u]
    push_cast; ring
  have hpars := sqNorm_eq_sum_coeff he w
  simp only [hcoef, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] at hpars
  have hsub : ∑ k ∈ Sᶜ, (lam - μ k) ^ 2 * ‖star (e k) ⬝ᵥ u‖ ^ 2 ≤ r ^ 2 := by
    refine le_trans ?_ (hpars ▸ hpert)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => by positivity)
  rw [div_pow, le_div_iff₀ (by positivity), Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum fun k hk => ?_) hsub
  have hk' := hS k (Finset.mem_compl.mp hk)
  have : h ^ 2 ≤ (lam - μ k) ^ 2 := by
    rw [← sq_abs (lam - μ k), abs_sub_comm]
    exact pow_le_pow_left₀ hh.le hk' 2
  nlinarith [norm_nonneg (star (e k) ⬝ᵥ u), sq_nonneg ‖star (e k) ⬝ᵥ u‖]

/-- An `L²`-operator-norm contraction satisfies `|x* J y| ≤ ‖x‖ ‖y‖`. -/
theorem bilinear_le_of_opNorm_le {J : Matrix ι ι ℂ} (hJ : ‖J‖ ≤ 1) (x y : ι → ℂ) :
    ‖star x ⬝ᵥ (J *ᵥ y)‖ ≤ Real.sqrt (sqNorm x) * Real.sqrt (sqNorm y) := by
  have hnorm : ∀ v : ι → ℂ, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ = Real.sqrt (sqNorm v) := by
    intro v; rw [EuclideanSpace.norm_eq]; rfl
  have hinner : star x ⬝ᵥ (J *ᵥ y) =
      inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
        ((EuclideanSpace.equiv ι ℂ).symm (J *ᵥ (WithLp.toLp 2 y : EuclideanSpace ℂ ι))) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  rw [hinner]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [hnorm x, ← hnorm y]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (Matrix.l2_opNorm_mulVec J _).trans ?_
  calc ‖J‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖
      ≤ 1 * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ :=
        mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
    _ = _ := one_mul _

/-- **Window transfer**. Let `Â` be Hermitian with orthonormal
eigenvectors `e_k` and eigenvalues `μ_k`, `S` a set of labels with `h ≤ |μ_k - λ|` off `S`
(`h > 0`; `S` is the spectral window of radius `h` at `λ`). Assume the ETH pair bounds
`|e_k* J e_l - δ_{kl} c_k| ≤ ε` for `k, l ∈ S`, the centre bound `|c_k - c₀| ≤ ε'` on `S`,
and that `J` is a contraction. If `A u = λ u`, `‖u‖ = 1` and `‖(A - Â)u‖ ≤ r`, then with
`τ = r/h`: `|u* J u - c₀| ≤ |S| ε + ε' + 2τ + (1 + |c₀|) τ²`. No eigenvalue gap of `A` or
`Â` is assumed. -/
theorem window_transfer {A Ahat J : Matrix ι ι ℂ} (hAhat : Ahat.IsHermitian) {e : ι → ι → ℂ}
    (he : IsOrthonormalFamily e) {μ : ι → ℝ} (heig : ∀ k, Ahat *ᵥ e k = (μ k : ℂ) • e k)
    (hJ : ∀ x y : ι → ℂ, ‖star x ⬝ᵥ (J *ᵥ y)‖ ≤ Real.sqrt (sqNorm x) * Real.sqrt (sqNorm y))
    {u : ι → ℂ} (hu : sqNorm u = 1) {lam : ℝ} (hAu : A *ᵥ u = (lam : ℂ) • u) {r h : ℝ}
    (hr : 0 ≤ r) (hh : 0 < h) (hpert : sqNorm ((A - Ahat) *ᵥ u) ≤ r ^ 2) {S : Finset ι}
    (hS : ∀ k ∉ S, h ≤ |μ k - lam|) {c : ι → ℂ} {c₀ : ℂ} {ε ε' : ℝ} (hε : 0 ≤ ε)
    (hε' : 0 ≤ ε')
    (hpair : ∀ k ∈ S, ∀ l ∈ S,
      ‖star (e k) ⬝ᵥ (J *ᵥ e l) - (if k = l then c k else 0)‖ ≤ ε)
    (hcen : ∀ k ∈ S, ‖c k - c₀‖ ≤ ε') :
    ‖star u ⬝ᵥ (J *ᵥ u) - c₀‖ ≤
      S.card * ε + ε' + 2 * (r / h) + (1 + ‖c₀‖) * (r / h) ^ 2 := by
  set τ := r / h with hτ
  have hτ0 : 0 ≤ τ := div_nonneg hr hh.le
  set a : ι → ℂ := fun k => star (e k) ⬝ᵥ u
  set v := ∑ k ∈ S, a k • e k
  set w := ∑ k ∈ Sᶜ, a k • e k
  have huvw : u = v + w := by
    conv_lhs => rw [orthonormal_expand he u]
    exact (Finset.sum_add_sum_compl S _).symm
  have hw : sqNorm w ≤ τ ^ 2 := by
    rw [sqNorm_sum_smul he]
    exact outside_window_le hAhat he heig hAu hh hpert hS
  have hvw : sqNorm v + sqNorm w = 1 := by
    rw [sqNorm_sum_smul he, sqNorm_sum_smul he, Finset.sum_add_sum_compl, ← hu,
      sqNorm_eq_sum_coeff he u]
  have hv1 : sqNorm v ≤ 1 := by linarith [sqNorm_nonneg w]
  have hsv : Real.sqrt (sqNorm v) ≤ 1 := Real.sqrt_le_one.mpr hv1
  have hsw : Real.sqrt (sqNorm w) ≤ τ := by
    rw [Real.sqrt_le_left hτ0]; exact hw
  have hsw0 := Real.sqrt_nonneg (sqNorm w)
  -- the four terms
  have hexp : star u ⬝ᵥ (J *ᵥ u) = star v ⬝ᵥ (J *ᵥ v) + star v ⬝ᵥ (J *ᵥ w) +
      star w ⬝ᵥ (J *ᵥ v) + star w ⬝ᵥ (J *ᵥ w) := by
    rw [huvw, star_add, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
    ring
  have hvw1 : ‖star v ⬝ᵥ (J *ᵥ w)‖ ≤ τ :=
    (hJ v w).trans (by nlinarith [Real.sqrt_nonneg (sqNorm v)])
  have hvw2 : ‖star w ⬝ᵥ (J *ᵥ v)‖ ≤ τ :=
    (hJ w v).trans (by nlinarith [Real.sqrt_nonneg (sqNorm v)])
  have hww : ‖star w ⬝ᵥ (J *ᵥ w)‖ ≤ τ ^ 2 :=
    (hJ w w).trans (by nlinarith)
  -- the window term
  set X : ι → ι → ℂ := fun k l => star (e k) ⬝ᵥ (J *ᵥ e l) - (if k = l then c k else 0)
  have hvv : star v ⬝ᵥ (J *ᵥ v) = (∑ k ∈ S, ∑ l ∈ S, star (a k) * a l * X k l) +
      ∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * c k := by
    rw [star_sum_dotProduct_mulVec_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hX : ∀ l, star (e k) ⬝ᵥ (J *ᵥ e l) = X k l + (if k = l then c k else 0) := by
      intro l; simp only [X]; ring
    simp only [hX, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (fun h => absurd hk h)]
    simp only [ite_true, Complex.ofReal_pow]
    rw [Complex.star_def, Complex.conj_mul']
  have hsumX : ‖∑ k ∈ S, ∑ l ∈ S, star (a k) * a l * X k l‖ ≤ S.card * ε := by
    calc ‖∑ k ∈ S, ∑ l ∈ S, star (a k) * a l * X k l‖
        ≤ ∑ k ∈ S, ∑ l ∈ S, ‖a k‖ * ‖a l‖ * ε := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
          rw [norm_mul, norm_mul, norm_star]
          exact mul_le_mul_of_nonneg_left (hpair k hk l hl) (by positivity)
      _ = (∑ k ∈ S, ‖a k‖) ^ 2 * ε := by
          rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
      _ ≤ (S.card * ∑ k ∈ S, ‖a k‖ ^ 2) * ε :=
          mul_le_mul_of_nonneg_right (sq_sum_le_card_mul_sum_sq) hε
      _ ≤ S.card * ε := by
          have : ∑ k ∈ S, ‖a k‖ ^ 2 ≤ 1 := by rw [← sqNorm_sum_smul he]; exact hv1
          have hc : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left this hc]
  have hcentre : ‖(∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * c k) - c₀‖ ≤ ε' + ‖c₀‖ * τ ^ 2 := by
    have hsplit : (∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * c k) - c₀ =
        (∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * (c k - c₀)) - ((sqNorm w : ℝ) : ℂ) * c₀ := by
      have h1 : ((sqNorm w : ℝ) : ℂ) = 1 - ∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.ofReal_sum, ← sqNorm_sum_smul he]
        have : sqNorm w = 1 - sqNorm v := by linarith
        rw [this]; push_cast; ring
      rw [h1]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * (c k - c₀)‖
          ≤ ∑ k ∈ S, ‖a k‖ ^ 2 * ε' := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left (hcen k hk) (by positivity)
        _ ≤ ε' := by
            rw [← Finset.sum_mul, ← sqNorm_sum_smul he]
            nlinarith
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sqNorm_nonneg w),
        mul_comm]
      exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  rw [hexp, hvv]
  have key : (∑ k ∈ S, ∑ l ∈ S, star (a k) * a l * X k l) +
        (∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * c k) + star v ⬝ᵥ (J *ᵥ w) +
        star w ⬝ᵥ (J *ᵥ v) + star w ⬝ᵥ (J *ᵥ w) - c₀ =
      (∑ k ∈ S, ∑ l ∈ S, star (a k) * a l * X k l) +
        ((∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * c k) - c₀) + star v ⬝ᵥ (J *ᵥ w) +
        star w ⬝ᵥ (J *ᵥ v) + star w ⬝ᵥ (J *ᵥ w) := by ring
  rw [key]
  have n1 := norm_add_le (∑ k ∈ S, ∑ l ∈ S, star (a k) * a l * X k l +
    ((∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * c k) - c₀) + star v ⬝ᵥ (J *ᵥ w) +
    star w ⬝ᵥ (J *ᵥ v)) (star w ⬝ᵥ (J *ᵥ w))
  have n2 := norm_add_le (∑ k ∈ S, ∑ l ∈ S, star (a k) * a l * X k l +
    ((∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * c k) - c₀) + star v ⬝ᵥ (J *ᵥ w))
    (star w ⬝ᵥ (J *ᵥ v))
  have n3 := norm_add_le (∑ k ∈ S, ∑ l ∈ S, star (a k) * a l * X k l +
    ((∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * c k) - c₀)) (star v ⬝ᵥ (J *ᵥ w))
  have n4 := norm_add_le (∑ k ∈ S, ∑ l ∈ S, star (a k) * a l * X k l)
    ((∑ k ∈ S, ((‖a k‖ ^ 2 : ℝ) : ℂ) * c k) - c₀)
  linarith

end BlockBand.LocalWindow.ProofETH
