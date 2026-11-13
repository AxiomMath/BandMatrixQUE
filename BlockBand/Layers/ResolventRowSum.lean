module

public import BlockBand.Internal.Contracts.Layers

/-!
# Resolvent row sums for the two-port layer contraction

From the proof of the layer-contraction lemma:

> Set `Q_ij = W⁻¹ Tr R_ij R_ji`. Normality of `R` and the imaginary resolvent identity give
> `max_i Σ_j |Q_ij| ≤ (1-b)⁻¹ + O(d(X))`.

This file proves the deterministic core of that sentence for an arbitrary Hermitian `X` and
an arbitrary spectral parameter `z` with `Im z > 0`, `R = (z - X)⁻¹`:

* `resolvent_det_ne_zero`, `resolvent_mul_sub`, `sub_mul_resolvent`: `z - X` is invertible;
* `resolvent_sub_conjTranspose`: `R - R* = -2i Im z · R R*` (imaginary resolvent identity);
* `resolvent_normal`: `R R* = R* R`;
* `resolvent_row_sq_sum`, `resolvent_col_sq_sum`: `Σ_q |R_pq|² = Σ_q |R_qp|² = -Im R_pp / Im z`;
* `rowBlockMass_eq`, `colBlockMass_eq`: the block versions with the normalized block trace;
* `norm_blockPairTrace_le`: `|Q_ij| ≤ ½ (W⁻¹ Σ |R_(i,x)(j,y)|² + W⁻¹ Σ |R_(j,y)(i,x)|²)`;
* `sum_norm_blockPairTrace_le`: `Σ_j |Q_ij| ≤ -Im(W⁻¹ Tr R_ii) / Im z`;
* `sum_norm_blockPairTrace_le_center`: for every `a : ℂ`,
  `Σ_j |Q_ij| ≤ -Im a / Im z + |W⁻¹ Tr R_ii - a| / Im z`.

With `a = matchedA E`, `z = boundaryZ b E` (so `-Im a / Im z = (1-b)⁻¹` in the bulk) the last
statement gives the `rowSum` field of `StrictContractionContract`:
`strictContraction_rowSum` proves that field exactly as stated, with the explicit constant
`C = 2 / ((1 - b) √(κ (4 - κ))) ≥ 1 / Im z_∂` on `bulkInterval κ` (helpers `rowSum_normSq_matchedA`,
`rowSum_im_matchedA`, `rowSum_im_boundaryZ`). Of that field's hypotheses, `0 < b` and `0 < W` are not used
and `b < 1/2` is used only through `b < 1`.

Norms: `‖·‖` on `ℂ` is the complex modulus; all bounds are entrywise sums of moduli.
Uniformity: every statement is deterministic and holds for every `W : ℕ` (including `W = 0`,
where `blockTrace` and `blockPairTrace` vanish), every Hermitian `X` and every `z` with
`0 < Im z`; no constant is hidden.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Layers

open Matrix ComplexConjugate
open scoped ComplexOrder
open BlockBand.Internal.Contracts.Layers

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Invertibility of `z - X`.** For Hermitian `X : Matrix n n ℂ` and `Im z > 0`,
`det (z • 1 - X) ≠ 0`. Proof: if `(z - X) v = 0` then `Im ⟨v, (z - X) v⟩ = Im z ‖v‖² = 0`.
Deterministic, every finite index type. -/
theorem resolvent_det_ne_zero (X : Matrix n n ℂ) (hX : X.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) : (z • (1 : Matrix n n ℂ) - X).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : star v ⬝ᵥ ((z • (1 : Matrix n n ℂ) - X) *ᵥ v) = 0 := by rw [hAv]; simp
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul] at h1
  have h2 := congrArg Complex.im h1
  have hXi : (star v ⬝ᵥ X *ᵥ v).im = 0 := hX.im_star_dotProduct_mulVec_self v
  have hs : 0 ≤ star v ⬝ᵥ v := dotProduct_star_self_nonneg v
  rw [Complex.le_def] at hs
  simp only [Complex.zero_re, Complex.zero_im] at hs
  simp only [Complex.sub_im, smul_eq_mul, Complex.mul_im, hXi, Complex.zero_im, sub_zero,
    ← hs.2, mul_zero, zero_add] at h2
  have hre : (star v ⬝ᵥ v).re = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hz.ne'
    · exact h
  have : star v ⬝ᵥ v = 0 := Complex.ext hre hs.2.symm
  exact hv (dotProduct_star_self_eq_zero.mp this)

/-- `R (z - X) = 1` for `R = (z - X)⁻¹`, `X` Hermitian, `Im z > 0`. -/
theorem resolvent_mul_sub (X : Matrix n n ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    (z • (1 : Matrix n n ℂ) - X)⁻¹ * (z • (1 : Matrix n n ℂ) - X) = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (resolvent_det_ne_zero X hX z hz))

/-- `(z - X) R = 1` for `R = (z - X)⁻¹`, `X` Hermitian, `Im z > 0`. -/
theorem sub_mul_resolvent (X : Matrix n n ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    (z • (1 : Matrix n n ℂ) - X) * (z • (1 : Matrix n n ℂ) - X)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (resolvent_det_ne_zero X hX z hz))

omit [Fintype n] in
private theorem conjTranspose_sub_eq (X : Matrix n n ℂ) (hX : X.IsHermitian) (z : ℂ) :
    (z • (1 : Matrix n n ℂ) - X)ᴴ - (z • (1 : Matrix n n ℂ) - X) =
      (star z - z) • (1 : Matrix n n ℂ) := by
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq, sub_smul]
  abel

private theorem star_sub_self (z : ℂ) : star z - z = -(2 * z.im) * Complex.I := by
  apply Complex.ext <;> simp; ring

/-- **Imaginary resolvent identity, both orders.** With `A = z - X`, `R = A⁻¹`:
`R - R* = (z̄ - z) R R* = (z̄ - z) R* R`. -/
private theorem resolvent_sub_conjTranspose_both (X : Matrix n n ℂ) (hX : X.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) :
    (z • (1 : Matrix n n ℂ) - X)⁻¹ - (z • (1 : Matrix n n ℂ) - X)⁻¹ᴴ =
        (star z - z) • ((z • (1 : Matrix n n ℂ) - X)⁻¹ * (z • (1 : Matrix n n ℂ) - X)⁻¹ᴴ) ∧
      (z • (1 : Matrix n n ℂ) - X)⁻¹ - (z • (1 : Matrix n n ℂ) - X)⁻¹ᴴ =
        (star z - z) • ((z • (1 : Matrix n n ℂ) - X)⁻¹ᴴ * (z • (1 : Matrix n n ℂ) - X)⁻¹) := by
  set A := z • (1 : Matrix n n ℂ) - X with hA
  set R := A⁻¹ with hR
  have hRA : R * A = 1 := resolvent_mul_sub X hX z hz
  have hAR : A * R = 1 := sub_mul_resolvent X hX z hz
  have hAhRh : Aᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRA, conjTranspose_one]
  have hRhAh : Rᴴ * Aᴴ = 1 := by rw [← conjTranspose_mul, hAR, conjTranspose_one]
  have hdiff : Aᴴ - A = (star z - z) • (1 : Matrix n n ℂ) := conjTranspose_sub_eq X hX z
  constructor
  · have : R * (Aᴴ - A) * Rᴴ = R - Rᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hAhRh, Matrix.mul_one, hRA,
        Matrix.one_mul]
    rw [← this, hdiff, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  · have : Rᴴ * (Aᴴ - A) * R = R - Rᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hRhAh, Matrix.one_mul, Matrix.mul_assoc, hAR,
        Matrix.mul_one]
    rw [← this, hdiff, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- **Imaginary resolvent identity** ("the imaginary resolvent identity").
For Hermitian `X : Matrix n n ℂ`, `Im z > 0`, `R = (z • 1 - X)⁻¹`:
`R - Rᴴ = (-(2 Im z) i) • (R * Rᴴ)`, i.e. `Im R = -(Im z) R R*`.
Deterministic, every finite index type. -/
theorem resolvent_sub_conjTranspose (X : Matrix n n ℂ) (hX : X.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) :
    (z • (1 : Matrix n n ℂ) - X)⁻¹ - (z • (1 : Matrix n n ℂ) - X)⁻¹ᴴ =
      (-(2 * z.im) * Complex.I) •
        ((z • (1 : Matrix n n ℂ) - X)⁻¹ * (z • (1 : Matrix n n ℂ) - X)⁻¹ᴴ) := by
  rw [← star_sub_self]
  exact (resolvent_sub_conjTranspose_both X hX z hz).1

/-- **Normality of the resolvent** ("normality of `R`"). For Hermitian
`X : Matrix n n ℂ`, `Im z > 0`, `R = (z • 1 - X)⁻¹`: `R * Rᴴ = Rᴴ * R`.
Deterministic, every finite index type. -/
theorem resolvent_normal (X : Matrix n n ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    (z • (1 : Matrix n n ℂ) - X)⁻¹ * (z • (1 : Matrix n n ℂ) - X)⁻¹ᴴ =
      (z • (1 : Matrix n n ℂ) - X)⁻¹ᴴ * (z • (1 : Matrix n n ℂ) - X)⁻¹ := by
  obtain ⟨h1, h2⟩ := resolvent_sub_conjTranspose_both X hX z hz
  have hc : star z - z ≠ 0 := by
    rw [star_sub_self]
    have : (2 * z.im : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * z.im : ℝ) ≠ 0)
    simpa [Complex.I_ne_zero] using this
  exact smul_right_injective _ hc (h1.symm.trans h2)

private theorem re_mul_star (u : ℂ) : (u * star u).re = ‖u‖ ^ 2 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem re_star_mul (u : ℂ) : (star u * u).re = ‖u‖ ^ 2 := by
  rw [mul_comm, re_mul_star]

/-- Diagonal form of the imaginary resolvent identity: `2 Im R_pp = -2 Im z (R R*)_pp`
and the same with `R* R`; real parts of the diagonal of `R R*` are row sums of squares. -/
private theorem im_diag_eq (X : Matrix n n ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (p : n) :
    ∑ q, ‖(z • (1 : Matrix n n ℂ) - X)⁻¹ p q‖ ^ 2 =
        -((z • (1 : Matrix n n ℂ) - X)⁻¹ p p).im / z.im ∧
      ∑ q, ‖(z • (1 : Matrix n n ℂ) - X)⁻¹ q p‖ ^ 2 =
        -((z • (1 : Matrix n n ℂ) - X)⁻¹ p p).im / z.im := by
  obtain ⟨h1, h2⟩ := resolvent_sub_conjTranspose_both X hX z hz
  rw [star_sub_self] at h1 h2
  set R := (z • (1 : Matrix n n ℂ) - X)⁻¹
  have key : ∀ M : Matrix n n ℂ, R - Rᴴ = (-(2 * z.im) * Complex.I) • M →
      (M p p).re = -(R p p).im / z.im := by
    intro M hM
    have h := congrArg Complex.im (congrFun (congrFun hM p) p)
    rw [Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, Complex.sub_im,
      Complex.star_def, Complex.conj_im] at h
    have hc : ((-(2 * z.im : ℂ)) * Complex.I * M p p).im = -(2 * z.im) * (M p p).re := by
      simp [Complex.mul_im, Complex.mul_re]
    rw [hc] at h
    field_simp
    linarith
  constructor
  · have := key _ h1
    rw [mul_apply, Complex.re_sum] at this
    simpa only [conjTranspose_apply, re_mul_star] using this
  · have := key _ h2
    rw [mul_apply, Complex.re_sum] at this
    simpa only [conjTranspose_apply, re_star_mul] using this

/-- **Row sums of squares of the resolvent.** For Hermitian `X : Matrix n n ℂ`,
`Im z > 0`, `R = (z • 1 - X)⁻¹` and every `p`: `Σ_q |R_pq|² = -Im R_pp / Im z`
(diagonal of the imaginary resolvent identity). Deterministic. -/
theorem resolvent_row_sq_sum (X : Matrix n n ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (p : n) :
    ∑ q, ‖(z • (1 : Matrix n n ℂ) - X)⁻¹ p q‖ ^ 2 =
      -((z • (1 : Matrix n n ℂ) - X)⁻¹ p p).im / z.im :=
  (im_diag_eq X hX z hz p).1

/-- **Column sums of squares of the resolvent.** For Hermitian `X : Matrix n n ℂ`,
`Im z > 0`, `R = (z • 1 - X)⁻¹` and every `p`: `Σ_q |R_qp|² = -Im R_pp / Im z`
(diagonal of the identity `R - R* = (z̄ - z) R* R`, i.e. normality). Deterministic. -/
theorem resolvent_col_sq_sum (X : Matrix n n ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (p : n) :
    ∑ q, ‖(z • (1 : Matrix n n ℂ) - X)⁻¹ q p‖ ^ 2 =
      -((z • (1 : Matrix n n ℂ) - X)⁻¹ p p).im / z.im :=
  (im_diag_eq X hX z hz p).2

end General

section TwoPort

variable {W : ℕ}

private theorem im_blockTrace (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    (blockTrace M i).im = (W : ℝ)⁻¹ * ∑ x : Fin W, (M (i, x) (i, x)).im := by
  unfold blockTrace
  have : ((W : ℂ))⁻¹ = (((W : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.im_ofReal_mul, Complex.im_sum]

private theorem block_mass_aux (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (z : ℂ)
    (i : Fin 2) (f : Fin W → ℝ)
    (hf : ∀ x, f x = -((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ (i, x)
      (i, x)).im / z.im) :
    (W : ℝ)⁻¹ * ∑ x, f x =
      -(blockTrace ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) i).im /
        z.im := by
  rw [im_blockTrace, Finset.sum_congr rfl (fun x _ => hf x)]
  simp only [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div]
  ring

/-- **Row block mass** (the layer-contraction lemma). Setting: `W : ℕ`
arbitrary, `X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ` Hermitian, `Im z > 0`,
`R = (z • 1 - X)⁻¹`. For each block `i`,
`W⁻¹ Σ_j Σ_{x,y} |R_(i,x)(j,y)|² = -Im (blockTrace R i) / Im z`, `|·|` the complex modulus.
Deterministic, uniform in `W` and `X`. -/
theorem rowBlockMass_eq (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hX : X.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i : Fin 2) :
    (W : ℝ)⁻¹ * ∑ j : Fin 2, ∑ x : Fin W, ∑ y : Fin W,
        ‖(z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ (i, x) (j, y)‖ ^ 2 =
      -(blockTrace ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) i).im /
        z.im := by
  rw [Finset.sum_comm]
  apply block_mass_aux X z i
  intro x
  rw [← resolvent_row_sq_sum X hX z hz (i, x), Fintype.sum_prod_type]

/-- **Column block mass** (the layer-contraction lemma, via normality of `R`).
Setting as in `rowBlockMass_eq`. For each block `i`,
`W⁻¹ Σ_j Σ_{x,y} |R_(j,y)(i,x)|² = -Im (blockTrace R i) / Im z`. Deterministic, uniform in
`W` and `X`. -/
theorem colBlockMass_eq (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hX : X.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i : Fin 2) :
    (W : ℝ)⁻¹ * ∑ j : Fin 2, ∑ x : Fin W, ∑ y : Fin W,
        ‖(z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ (j, y) (i, x)‖ ^ 2 =
      -(blockTrace ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) i).im /
        z.im := by
  rw [Finset.sum_comm]
  apply block_mass_aux X z i
  intro x
  rw [← resolvent_col_sq_sum X hX z hz (i, x), Fintype.sum_prod_type]

/-- **Entrywise AM–GM bound for `Q_ij`** (the layer-contraction lemma). For
every matrix `R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ` (no hypothesis), every `W` and
blocks `i j`, with `Q_ij = blockPairTrace R i j = W⁻¹ Σ_{x,y} R_(i,x)(j,y) R_(j,y)(i,x)`:
`|Q_ij| ≤ ½ (W⁻¹ Σ_{x,y} |R_(i,x)(j,y)|² + W⁻¹ Σ_{x,y} |R_(j,y)(i,x)|²)`. -/
theorem norm_blockPairTrace_le (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    ‖blockPairTrace R i j‖ ≤
      (1 / 2) * ((W : ℝ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W, ‖R (i, x) (j, y)‖ ^ 2 +
        (W : ℝ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W, ‖R (j, y) (i, x)‖ ^ 2) := by
  unfold blockPairTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hW : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hS : ‖∑ x : Fin W, ∑ y : Fin W, R (i, x) (j, y) * R (j, y) (i, x)‖ ≤
      ∑ x : Fin W, ∑ y : Fin W, (1 / 2) * (‖R (i, x) (j, y)‖ ^ 2 + ‖R (j, y) (i, x)‖ ^ 2) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul]
    nlinarith [two_mul_le_add_sq ‖R (i, x) (j, y)‖ ‖R (j, y) (i, x)‖]
  calc (W : ℝ)⁻¹ * ‖∑ x : Fin W, ∑ y : Fin W, R (i, x) (j, y) * R (j, y) (i, x)‖
      ≤ (W : ℝ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W,
          (1 / 2) * (‖R (i, x) (j, y)‖ ^ 2 + ‖R (j, y) (i, x)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hS hW
    _ = _ := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
        ring

/-- **Row sum of `|Q_ij|`** (the layer-contraction lemma: "normality of `R` and
the imaginary resolvent identity give `max_i Σ_j |Q_ij| ≤ …`"). Setting: `W : ℕ` arbitrary,
`X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ` Hermitian, `Im z > 0`, `R = (z • 1 - X)⁻¹`,
`Q_ij = blockPairTrace R i j`. For each block `i`:
`Σ_j |Q_ij| ≤ -Im (W⁻¹ Tr R_ii) / Im z`, `|·|` the complex modulus.
Deterministic; uniform in `W`, `X` and `z` (no constant). -/
theorem sum_norm_blockPairTrace_le (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (i : Fin 2) :
    ∑ j : Fin 2, ‖blockPairTrace ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹)
        i j‖ ≤
      -(blockTrace ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) i).im /
        z.im := by
  set R := (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ with hR
  have hrow := rowBlockMass_eq X hX z hz i
  have hcol := colBlockMass_eq X hX z hz i
  rw [← hR] at hrow hcol
  calc ∑ j : Fin 2, ‖blockPairTrace R i j‖
      ≤ ∑ j : Fin 2, (1 / 2) * ((W : ℝ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W, ‖R (i, x) (j, y)‖ ^ 2 +
          (W : ℝ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W, ‖R (j, y) (i, x)‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => norm_blockPairTrace_le R i j
    _ = (1 / 2) * ((W : ℝ)⁻¹ * ∑ j : Fin 2, ∑ x : Fin W, ∑ y : Fin W, ‖R (i, x) (j, y)‖ ^ 2 +
          (W : ℝ)⁻¹ * ∑ j : Fin 2, ∑ x : Fin W, ∑ y : Fin W, ‖R (j, y) (i, x)‖ ^ 2) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = -(blockTrace R i).im / z.im := by rw [hrow, hcol]; ring

/-- **Row sum of `|Q_ij|` around a center** (the layer-contraction lemma).
Setting as in `sum_norm_blockPairTrace_le`; `a : ℂ` arbitrary. For each block `i`:
`Σ_j |Q_ij| ≤ -Im a / Im z + |W⁻¹ Tr R_ii - a| / Im z`. With `a = matchedA E`,
`z = boundaryZ b E` this is `Σ_j |Q_ij| ≤ (1-b)⁻¹ + d(X) / Im z_∂`.
Deterministic; uniform in `W`, `X`, `z` and `a`. -/
theorem sum_norm_blockPairTrace_le_center (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (a : ℂ) (i : Fin 2) :
    ∑ j : Fin 2, ‖blockPairTrace ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹)
        i j‖ ≤
      -a.im / z.im +
        ‖blockTrace ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) i - a‖ /
          z.im := by
  refine (sum_norm_blockPairTrace_le X hX z hz i).trans ?_
  set t := blockTrace ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) i
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ hz.le
  have h1 : -(t - a).im ≤ ‖t - a‖ := (neg_le_abs _).trans (Complex.abs_im_le_norm _)
  rw [Complex.sub_im] at h1
  linarith

end TwoPort

section Contract

/-- `|a|² = 1` for the matched value `a = matchedA E` whenever `E² ≤ 4`. -/
theorem rowSum_normSq_matchedA {E : ℝ} (hE : E ^ 2 ≤ 4) : Complex.normSq (matchedA E) = 1 := by
  have hs : Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := Real.sq_sqrt (by linarith)
  simp only [matchedA, Complex.normSq_mk]
  nlinarith [hs]

/-- `Im a = -√(4 - E²)/2` for `a = matchedA E`. -/
theorem rowSum_im_matchedA (E : ℝ) : (matchedA E).im = -Real.sqrt (4 - E ^ 2) / 2 := rfl

/-- `Im z_∂ = (1 - b) √(4 - E²)/2` for `z_∂ = boundaryZ b E = a⁻¹ + b a`, `E² ≤ 4`. -/
theorem rowSum_im_boundaryZ {b E : ℝ} (hE : E ^ 2 ≤ 4) :
    (boundaryZ b E).im = (1 - b) * (Real.sqrt (4 - E ^ 2) / 2) := by
  have h := rowSum_normSq_matchedA hE
  simp only [boundaryZ, Complex.add_im, Complex.inv_im, h, div_one, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, rowSum_im_matchedA]
  ring

/-- **The `rowSum` field of `StrictContractionContract`** (the layer-contraction
lemma: `max_i Σ_j |Q_ij| ≤ (1-b)⁻¹ + O(d(X))`), with the exact statement of
`BlockBand.Internal.Contracts.Layers.StrictContractionContract.rowSum`. Setting: `0 < b < 1/2`,
`κ > 0`, `E ∈ bulkInterval κ = [-2+κ, 2-κ]`, `z = z_∂(E) = boundaryZ b E`, any `W > 0`, any
Hermitian `X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ`, `R = (z • 1 - X)⁻¹`,
`Q_ij = blockPairTrace R i j`, `d(X) = matchedDistance b E X`; `|·|` the complex modulus.
Explicit constant `C = 2 / ((1 - b) √(κ (4 - κ)))`, depending only on `b, κ`;
deterministic, uniform in `W`, `X`, `E` and `i`. -/
theorem strictContraction_rowSum : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ C : ℝ,
    ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ, ∀ i : Fin 2,
      ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ ≤
        (1 - b)⁻¹ + C * matchedDistance b E X := by
  intro b hb0 hb1 κ hκ
  refine ⟨2 / ((1 - b) * Real.sqrt (κ * (4 - κ))), ?_⟩
  intro W _ X hX E hE i
  obtain ⟨hE1, hE2⟩ := hE
  have hκ2 : κ ≤ 2 := by linarith
  have hE4 : E ^ 2 ≤ (2 - κ) ^ 2 := by nlinarith
  have hE4' : E ^ 2 ≤ 4 := by nlinarith
  have hpos : 0 < κ * (4 - κ) := by nlinarith
  have hsq0 : 0 < Real.sqrt (κ * (4 - κ)) := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt (κ * (4 - κ)) ≤ Real.sqrt (4 - E ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : 0 < Real.sqrt (4 - E ^ 2) := hsq0.trans_le hsq
  have h1b : 0 < 1 - b := by linarith
  have hz : 0 < (boundaryZ b E).im := by rw [rowSum_im_boundaryZ hE4']; positivity
  refine (sum_norm_blockPairTrace_le_center X hX _ hz (matchedA E) i).trans ?_
  rw [rowSum_im_boundaryZ hE4', rowSum_im_matchedA]
  have hfirst : -(-Real.sqrt (4 - E ^ 2) / 2) / ((1 - b) * (Real.sqrt (4 - E ^ 2) / 2)) =
      (1 - b)⁻¹ := by
    field_simp
  rw [hfirst]
  gcongr
  have hd : ‖blockTrace ((boundaryZ b E • 1 - X)⁻¹) i - matchedA E‖ ≤ matchedDistance b E X := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  rw [div_eq_mul_inv, mul_comm]
  refine mul_le_mul ?_ hd (norm_nonneg _) (by positivity)
  rw [show ((1 - b) * (Real.sqrt (4 - E ^ 2) / 2))⁻¹ = 2 / ((1 - b) * Real.sqrt (4 - E ^ 2)) by
    field_simp]
  gcongr

end Contract

end BlockBand.Layers
