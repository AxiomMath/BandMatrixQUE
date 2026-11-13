module

public import BlockBand.Internal.Contracts.Critical
public import BlockBand.Layers.ComparisonStability
public import BlockBand.Layers.TraceFluctuation

/-!
# Common-port mean: deterministic comparison of `M` with `R = K⁻¹`

Deterministic; no measure. Domain: `W ≥ 1` (any `W` where stated), Hermitian `X`, `|e| ≤ 2`,
`b < 1`, block shifts `s : Fin 2 → ℂ` with `Im s_j ≤ -y < 0`. `H = cmpTopH e X = -e - X`,
`M = cmpInv H s = (H - diag(s_j))⁻¹`, `R = cmpInv H s₀`, `s₀ = (1-b)a`, `a = matchedA e`; by
`cmp_resolvent_eq`, `R = (z_b - X)⁻¹ = K⁻¹`. The ladder coefficients are
`𝖠'_ij = cmpPair M Mᴴ i j = W⁻¹ Tr M_ij M_ij*`. Norms: `ℓ²` operator norms; complex modulus.

* `row_sq_le_opNorm`: `Σ_q |A_pq|² ≤ ‖A‖²`.
* `norm_cmpInv_sub_le`: `‖M - M'‖ ≤ ‖M‖ ‖M'‖ max_j |s_j - s'_j|` (second resolvent identity).
* `matchedLeadK_mul_cmpInv`, `norm_matchedLeadK_mul_cmpInv_sub_one_le`:
  `K M = 1 + diag(s - s₀) M`, `‖K M - 1‖ ≤ max_j|s_j - s₀_j| ‖M‖`.
* `cmpPair_conj_self`: `𝖠_ij(R) = cmpRowMass R i j` (a nonnegative real);
  `norm_ladderCoef_sub_le`: `|𝖠'_ij - 𝖠_ij| ≤ (‖M‖ + ‖R‖) ‖M - R‖`.
* `rowMass_R_sum`, `rowMass_R_sum_sub_le`: `Σ_j 𝖠_ij(R) = -Im tr_i R / ζ`, `ζ = -(1-b) Im a > 0`,
  and `|Σ_j 𝖠_ij(R) - (1-b)⁻¹| ≤ δ/ζ`, `δ = matchedDistance b e X` (the row-sum ↔ `δ`
  link, via the imaginary resolvent identity `cmp_rowMass_im`, the block-shift form
  of `rowBlockMass_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open Matrix BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Layers
open scoped Matrix.Norms.L2Operator ComplexConjugate

variable {W : ℕ}

/-- Row mass bounded by the operator norm: `Σ_q |A_pq|² ≤ ‖A‖²`. -/
theorem row_sq_le_opNorm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (p : n) :
    ∑ q, ‖A p q‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have h := tfl_col_sq_le Aᴴ p
  rw [l2_opNorm_conjTranspose] at h
  refine le_of_eq_of_le ?_ h
  exact Finset.sum_congr rfl fun q _ => by rw [conjTranspose_apply, norm_star]

/-- `‖diag(cmpExt δ)‖ ≤ max_j |δ_j|`. -/
theorem norm_diagonal_cmpExt_le (δ : Fin 2 → ℂ) :
    ‖(diagonal (cmpExt δ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ max ‖δ 0‖ ‖δ 1‖ := by
  rw [l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (le_max_left _ _)) |>.mpr fun q => ?_
  simp only [cmpExt]
  rcases q with ⟨j, x⟩
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- **Second resolvent identity in norm.** For Hermitian `H` and `Im s_j, Im s'_j < 0`:
`‖M - M'‖ ≤ ‖M‖ ‖M'‖ max_j |s_j - s'_j|`, `M = cmpInv H s`, `M' = cmpInv H s'`. -/
theorem norm_cmpInv_sub_le (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hH : H.IsHermitian)
    (s s' : Fin 2 → ℂ) (hs : ∀ j, (s j).im < 0) (hs' : ∀ j, (s' j).im < 0) :
    ‖cmpInv H s - cmpInv H s'‖ ≤
      ‖cmpInv H s‖ * ‖cmpInv H s'‖ * max ‖s 0 - s' 0‖ ‖s 1 - s' 1‖ := by
  unfold cmpInv
  rw [cmp_inv_sub_inv H hH (cmpExt s) (cmpExt s') (fun p => hs p.1) (fun p => hs' p.1),
    cmpExt_sub]
  have hd := norm_diagonal_cmpExt_le (W := W) (s - s')
  simp only [Pi.sub_apply] at hd
  calc ‖(H - diagonal (cmpExt s))⁻¹ * diagonal (cmpExt (s - s')) * (H - diagonal (cmpExt s'))⁻¹‖
      ≤ ‖(H - diagonal (cmpExt s))⁻¹‖ * ‖(diagonal (cmpExt (s - s')) :
          Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ * ‖(H - diagonal (cmpExt s'))⁻¹‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖(H - diagonal (cmpExt s))⁻¹‖ * max ‖s 0 - s' 0‖ ‖s 1 - s' 1‖ *
          ‖(H - diagonal (cmpExt s'))⁻¹‖ := by gcongr
    _ = _ := by ring

/-- `K = z_b - X = H - diag(s₀)`, `s₀ = (1-b)a`, for `|e| ≤ 2`. -/
theorem matchedLeadK_eq_cmp {b e : ℝ} (he : |e| ≤ 2) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    matchedLeadK b e X =
      cmpTopH e X - diagonal (cmpExt (fun _ => (1 - (b : ℂ)) * matchedA e)) := by
  unfold matchedLeadK cmpTopH
  rw [boundaryZ_eq he]
  ext p q
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, diagonal_apply, cmpExt,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- **`KM = 1 + diag(s - s₀) M`** (deterministic). For Hermitian `X`,
`|e| ≤ 2` and `Im s_j < 0`. -/
theorem matchedLeadK_mul_cmpInv {b e : ℝ} (he : |e| ≤ 2)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (s : Fin 2 → ℂ)
    (hs : ∀ j, (s j).im < 0) :
    matchedLeadK b e X * cmpInv (cmpTopH e X) s =
      1 + diagonal (cmpExt (s - fun _ => (1 - (b : ℂ)) * matchedA e)) *
        cmpInv (cmpTopH e X) s := by
  have hK : matchedLeadK b e X = (cmpTopH e X - diagonal (cmpExt s)) +
      diagonal (cmpExt (s - fun _ => (1 - (b : ℂ)) * matchedA e)) := by
    rw [matchedLeadK_eq_cmp he]
    ext p q
    simp only [Matrix.add_apply, Matrix.sub_apply, diagonal_apply, cmpExt, Pi.sub_apply]
    split_ifs <;> ring
  rw [hK, Matrix.add_mul]
  unfold cmpInv
  rw [cmp_mul_inv (cmpTopH e X) (cmpTopH_isHermitian e hX) (cmpExt s) (fun p => hs p.1)]

/-- `‖KM - 1‖ ≤ max_j |s_j - s₀_j| ‖M‖`. -/
theorem norm_matchedLeadK_mul_cmpInv_sub_one_le {b e : ℝ} (he : |e| ≤ 2)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (s : Fin 2 → ℂ)
    (hs : ∀ j, (s j).im < 0) :
    ‖matchedLeadK b e X * cmpInv (cmpTopH e X) s - 1‖ ≤
      max ‖s 0 - (1 - (b : ℂ)) * matchedA e‖ ‖s 1 - (1 - (b : ℂ)) * matchedA e‖ *
        ‖cmpInv (cmpTopH e X) s‖ := by
  rw [matchedLeadK_mul_cmpInv he hX s hs, add_sub_cancel_left]
  refine (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have := norm_diagonal_cmpExt_le (W := W) (s - fun _ => (1 - (b : ℂ)) * matchedA e)
  simpa only [Pi.sub_apply] using this

/-- `𝖠_ij(R) = cmpPair R Rᴴ i j = W⁻¹ Σ_{x,y} |R_(i,x)(j,y)|²` (a real number). -/
theorem cmpPair_conj_self (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    cmpPair R Rᴴ i j = ((cmpRowMass R i j : ℝ) : ℂ) := by
  unfold cmpPair cmpRowMass
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_pow]

/-- Bilinear splitting `P(M, Mᴴ) - P(R, Rᴴ) = P(M - R, Mᴴ) + P(R, (M - R)ᴴ)`. -/
theorem cmpPair_conj_sub (M R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    cmpPair M Mᴴ i j - cmpPair R Rᴴ i j =
      cmpPair (M - R) Mᴴ i j + cmpPair R (M - R)ᴴ i j := by
  unfold cmpPair
  rw [← mul_sub, ← mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.sub_apply, conjTranspose_apply, star_sub]
  ring

/-- **Ladder coefficients are Lipschitz in the inverse**:
`|𝖠'_ij(M) - 𝖠_ij(R)| ≤ (‖M‖ + ‖R‖) ‖M - R‖`. -/
theorem norm_ladderCoef_sub_le (M R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    ‖cmpPair M Mᴴ i j - cmpPair R Rᴴ i j‖ ≤ (‖M‖ + ‖R‖) * ‖M - R‖ := by
  rw [cmpPair_conj_sub]
  have hcol : ∀ (A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (q : Fin 2 × Fin W),
      ∑ p, ‖Aᴴ p q‖ ^ 2 ≤ ‖A‖ ^ 2 := fun A q => by
    have h := row_sq_le_opNorm A q
    refine le_of_eq_of_le ?_ h
    exact Finset.sum_congr rfl fun p _ => by rw [conjTranspose_apply, norm_star]
  have h1 := cmp_pair_le (M - R) Mᴴ (norm_nonneg _) (norm_nonneg M)
    (row_sq_le_opNorm (M - R)) (hcol M) i j
  have h2 := cmp_pair_le R (M - R)ᴴ (norm_nonneg R) (norm_nonneg (M - R))
    (row_sq_le_opNorm R) (hcol (M - R)) i j
  refine (norm_add_le _ _).trans ?_
  nlinarith [h1, h2]

/-- **Row sums of the matched ladder coefficients** (imaginary resolvent
identity). For Hermitian `X`, `|e| < 2`, `b < 1`:
`Σ_j 𝖠_ij(R) = -Im tr_i R / ζ`, `ζ = -(1-b) Im a > 0`, `R = (z_b - X)⁻¹`. -/
theorem rowMass_R_sum {b e : ℝ} (hb : b < 1) (he : |e| < 2)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (i : Fin 2) :
    ∑ j, cmpRowMass ((boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) i j =
      -(blockTrace ((boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹)
        i).im / (-(1 - b) * (matchedA e).im) := by
  have ha : (matchedA e).im < 0 := matchedA_im_neg he
  have hζ : 0 < -(1 - b) * (matchedA e).im := by nlinarith
  have hs0 : ∀ j : Fin 2, ((fun _ => (1 - (b : ℂ)) * matchedA e) j).im < 0 := fun j => by
    simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, zero_mul, add_zero]
    nlinarith
  have h := cmp_rowMass_im (cmpTopH e X) (cmpTopH_isHermitian e hX) _ hs0 i
  rw [← cmp_resolvent_eq he.le X] at h
  have him : -(((fun _ : Fin 2 => (1 - (b : ℂ)) * matchedA e) 0).im) =
      -(1 - b) * (matchedA e).im := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, zero_mul, add_zero]
    ring
  rw [eq_div_iff hζ.ne', ← him, Finset.sum_mul]
  exact h

/-- **Row-sum defect is `O(δ)`**: for Hermitian `X`, `|e| < 2`, `b < 1`,
`|Σ_j 𝖠_ij(R) - (1-b)⁻¹| ≤ δ / ζ`, `δ = matchedDistance b e X`, `ζ = -(1-b) Im a > 0`. -/
theorem rowMass_R_sum_sub_le {b e : ℝ} (hb : b < 1) (he : |e| < 2)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (i : Fin 2) :
    |∑ j, cmpRowMass ((boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) i j -
        (1 - b)⁻¹| ≤ matchedDistance b e X / (-(1 - b) * (matchedA e).im) := by
  have ha : (matchedA e).im < 0 := matchedA_im_neg he
  have hb1 : 0 < 1 - b := by linarith
  have hζ : 0 < -(1 - b) * (matchedA e).im := by nlinarith
  rw [rowMass_R_sum hb he hX i]
  set T := blockTrace ((boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) i
  have hid : -T.im / (-(1 - b) * (matchedA e).im) - (1 - b)⁻¹ =
      -(T - matchedA e).im / (-(1 - b) * (matchedA e).im) := by
    have hane : (matchedA e).im ≠ 0 := ha.ne
    rw [Complex.sub_im]
    field_simp
  rw [hid, abs_div, abs_of_pos hζ, abs_neg]
  refine div_le_div_of_nonneg_right ?_ hζ.le
  exact (Complex.abs_im_le_norm _).trans (cmp_le_matchedDistance b e X i)

end BlockBand.Critical.CommonPort
