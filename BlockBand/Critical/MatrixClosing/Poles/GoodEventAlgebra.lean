module

public import BlockBand.Critical.MatrixClosing.Poles.Average
public import BlockBand.Critical.Collar.Density.TwoSidedBound

/-!
# The good event of the conditional collar: deterministic algebra

Deterministic; no measure. Common-port layer sample `ω₁ = (A, B)`, every `W`, real `b`, `e`,
deterministic `X` and frame `J` (Hermitian / orthonormal where stated).

* `collarF_eq_collarFW`: the `F` of `Poles.Average` is `Collar.Density.collarFW`.
* `frameFin_zero_eq`: `J^*KD⁻¹B = -J^*K T` (`T = -D⁻¹B`, port index on `Fin W`).
* `inv_conjTranspose_mul_self_eq`, `freshGamma_eq`: `Γ_F = c (F - z̄)⁻¹((F - z̄)⁻¹)^*`,
  `z = c m_{F,c}(0)` (normality of `F - z`).
* `collarVt_gamma_eq`: `Ṽ^*Γ_FṼ = λ ΨΨ^*`, `Ψ = (J^*KD⁻¹B)(F - z̄)⁻¹`,
  `λ = πwc/W` (`w = residueWeight`).
* `inv_sub_eq_mul`: `(F - z)⁻¹ = (F - w)⁻¹(1 + (z - w)(F - z)⁻¹)`.
* `norm_star_dotProduct_mulVec_le`, `l2Norm_mulVec_le`: `|x^*My| ≤ ‖M‖‖x‖‖y‖`.
* **`collarCov_entry_le`**: on `D` invertible, `A`, `X` Hermitian, `|e| < 2`,
  `Im m_{F,c}(0) ≥ v > 0` and `|m_{F,c}(0) - ā| ≤ k`, every entry satisfies
  `|(Ṽ^*Γ_FṼ - I)_{ij}| ≤ λ((2k/v + (k/v)²)‖L‖² + |u_i^*(LL^* - M)u_j| + ‖M - γI‖)`
  for every matrix `M`, provided `λγ = 1` (`u_i = J e_i`, `L = commonPortL`).
* `collarLambda_mul_gamma`: `λγ = 1` in the bulk (`ρ(e)cγ = η/π`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate Matrix.Norms.L2Operator

variable {W r : ℕ}

/-!
## Norm helpers
-/

theorem l2Norm_nonneg' {ι : Type} [Fintype ι] (x : ι → ℂ) : 0 ≤ l2Norm x := Real.sqrt_nonneg _

theorem l2Norm_mulVec_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℂ) (x : n → ℂ) : l2Norm (M *ᵥ x) ≤ ‖M‖ * l2Norm x := by
  have h := Collar.Density.sumsq_mulVec_le_opNorm M x
  unfold l2Norm
  rw [← Real.sqrt_sq (norm_nonneg M), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt h

/-- `|x^*My| ≤ ‖M‖ ‖x‖ ‖y‖` (Cauchy–Schwarz, `l2` operator norm). -/
theorem norm_star_dotProduct_mulVec_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (M : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :
    ‖star x ⬝ᵥ (M *ᵥ y)‖ ≤ ‖M‖ * l2Norm x * l2Norm y := by
  have h1 : ‖star x ⬝ᵥ (M *ᵥ y)‖ ≤ ∑ a, ‖x a‖ * ‖(M *ᵥ y) a‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖x a‖)
    (fun a => ‖(M *ᵥ y) a‖)
  have hM := Collar.Density.sumsq_mulVec_le_opNorm M y
  have hs0 : 0 ≤ ∑ a, ‖x a‖ * ‖(M *ᵥ y) a‖ := by positivity
  have hR : 0 ≤ ‖M‖ * l2Norm x * l2Norm y := by unfold l2Norm; positivity
  have hsq : (∑ a, ‖x a‖ * ‖(M *ᵥ y) a‖) ^ 2 ≤ (‖M‖ * l2Norm x * l2Norm y) ^ 2 := by
    rw [mul_pow, mul_pow, l2Norm, l2Norm, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    calc _ ≤ _ := hcs
      _ ≤ (∑ a, ‖x a‖ ^ 2) * (‖M‖ ^ 2 * ∑ a, ‖y a‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by ring
  exact h1.trans ((pow_le_pow_iff_left₀ hs0 hR (by norm_num)).1 hsq)

/-- The `(i, j)` entry of `J^*MJ` is `u_i^*Mu_j`, `u_i = J e_i`. -/
theorem conjTranspose_mul_mul_apply {m : Type} [Fintype m] (J : Matrix m (Fin r) ℂ)
    (M : Matrix m m ℂ) (i j : Fin r) :
    (Jᴴ * M * J) i j = star (fun x => J x i) ⬝ᵥ (M *ᵥ fun x => J x j) := by
  rw [Matrix.mul_assoc]
  rfl

theorem one_apply_eq_dotProduct {m : Type} [Fintype m] {J : Matrix m (Fin r) ℂ}
    (hJ : Jᴴ * J = 1) (i j : Fin r) :
    (1 : Matrix (Fin r) (Fin r) ℂ) i j = star (fun x => J x i) ⬝ᵥ fun x => J x j := by
  rw [← hJ]
  rfl

theorem l2Norm_frame_col {m : Type} [Fintype m] {J : Matrix m (Fin r) ℂ} (hJ : Jᴴ * J = 1)
    (i : Fin r) : l2Norm (fun x => J x i) = 1 := by
  have h := one_apply_eq_dotProduct hJ i i
  rw [Matrix.one_apply_eq] at h
  have hs : ∑ x, ‖J x i‖ ^ 2 = 1 := by
    have h2 : ((∑ x, ‖J x i‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [h]
      unfold dotProduct
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    exact_mod_cast h2
  rw [l2Norm, hs, Real.sqrt_one]

/-- `u^*(AMA^*)v = (A^*u)^*M(A^*v)`. -/
theorem star_dotProduct_sandwich {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℂ)
    (M : Matrix n n ℂ) (u v : m → ℂ) :
    star u ⬝ᵥ ((A * M * Aᴴ) *ᵥ v) = star (Aᴴ *ᵥ u) ⬝ᵥ (M *ᵥ (Aᴴ *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

/-!
## The deformation, the frame and `Γ`
-/

/-- The `F` of `Poles.Average` is the `F` of `Collar.Density` on `Fin W`. -/
theorem collarF_eq_collarFW (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω₁ : LayerSample W .common) : collarF e X ω₁ = Collar.Density.collarFW e X ω₁ := by
  unfold collarF portSchurFin portSchur Collar.Density.collarFW Collar.Density.collarF
  rw [Matrix.reindex_apply]
  simp only [zero_sub]
  rfl

/-- `J^*KD⁻¹B = -J^*K T` on `Fin W`. -/
theorem frameFin_zero_eq (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω₁ : LayerSample W .common) :
    frameFin b e X J (ω₁, 0) =
      -(Jᴴ * (matchedLeadK b e X * Collar.Density.collarTW e X ω₁)) := by
  unfold frameFin collarFrame Collar.Density.collarTW Collar.Density.collarT
  have h : (-((Collar.Density.collarTopBlock e X ω₁)⁻¹ * bondMatrix .common ω₁.2)).submatrix id
      (Collar.Density.portEquiv W).symm =
        -(((Collar.Density.collarTopBlock e X ω₁)⁻¹ * bondMatrix .common ω₁.2).submatrix id
          (Collar.Density.portEquiv W).symm) := by
    ext i j; simp
  rw [h, Matrix.mul_neg, Matrix.mul_neg, neg_neg]
  simp only [Matrix.mul_assoc]
  rfl

/-- Normality of `F - z`: `((F - z)^*(F - z))⁻¹ = (F - z̄)⁻¹((F - z̄)⁻¹)^*`. -/
theorem inv_conjTranspose_mul_self_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Matrix ι ι ℂ} (hF : F.IsHermitian) (z : ℂ) :
    ((F - z • (1 : Matrix ι ι ℂ))ᴴ * (F - z • 1))⁻¹ =
      (F - star z • 1)⁻¹ * ((F - star z • 1)⁻¹)ᴴ := by
  have hXh : ∀ y : ℂ, (F - y • (1 : Matrix ι ι ℂ))ᴴ = F - star y • 1 := fun y => by
    rw [conjTranspose_sub, hF.eq, conjTranspose_smul, conjTranspose_one]
  have hcomm : (F - star z • (1 : Matrix ι ι ℂ)) * (F - z • 1) =
      (F - z • 1) * (F - star z • 1) := by
    have hc : Commute (F - star z • (1 : Matrix ι ι ℂ)) (F - z • 1) := by
      refine Commute.sub_left (Commute.sub_right (Commute.refl F) ?_) (Commute.sub_right ?_ ?_)
      · exact (Commute.one_right F).smul_right z
      · exact (Commute.one_left F).smul_left (star z)
      · exact ((Commute.one_left _).smul_left (star z)).smul_right z
    exact hc.eq
  rw [hXh, hcomm, Matrix.mul_inv_rev, conjTranspose_nonsing_inv, hXh, star_star]

/-- `Γ_F = c (F - z̄)⁻¹((F - z̄)⁻¹)^*` with `z = E + c m_{F,c}(E)`. -/
theorem freshGamma_eq {ι : ℕ} {F : Matrix (Fin ι) (Fin ι) ℂ} (hF : F.IsHermitian) (c E : ℝ) :
    freshGamma F c E = (c : ℂ) •
      ((F - star ((E : ℂ) + (c : ℂ) * freshDyson F c E) • 1)⁻¹ *
        ((F - star ((E : ℂ) + (c : ℂ) * freshDyson F c E) • 1)⁻¹)ᴴ) := by
  unfold freshGamma
  simp only
  rw [inv_conjTranspose_mul_self_eq hF]

/-- `Ṽ^*Γ_FṼ = λ ΨΨ^*`, `Ψ = (J^*KD⁻¹B)(F - z̄)⁻¹`, `λ = πwc/W`. -/
theorem collarVt_gamma_eq (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω₁ : LayerSample W .common)
    (hF : (collarF e X ω₁).IsHermitian) :
    (collarVt b e X J ω₁)ᴴ * freshGamma (collarF e X ω₁) (1 - 2 * b) 0 * collarVt b e X J ω₁ =
      ((Real.pi * residueWeight W b e / W * (1 - 2 * b) : ℝ) : ℂ) •
        ((frameFin b e X J (ω₁, 0) * (collarF e X ω₁ - star (((0 : ℝ) : ℂ) +
            ((1 - 2 * b : ℝ) : ℂ) * freshDyson (collarF e X ω₁) (1 - 2 * b) ((0 : ℝ) : ℂ)) • 1)⁻¹) *
          (frameFin b e X J (ω₁, 0) * (collarF e X ω₁ - star (((0 : ℝ) : ℂ) +
            ((1 - 2 * b : ℝ) : ℂ) * freshDyson (collarF e X ω₁) (1 - 2 * b) ((0 : ℝ) : ℂ)) •
              1)⁻¹)ᴴ) := by
  set s := Real.sqrt (Real.pi * residueWeight W b e / W)
  have hs : s ^ 2 = Real.pi * residueWeight W b e / W := by
    refine Real.sq_sqrt ?_
    have := residueWeight_nonneg W b e
    positivity
  set Y := (collarF e X ω₁ - star (((0 : ℝ) : ℂ) +
    ((1 - 2 * b : ℝ) : ℂ) * freshDyson (collarF e X ω₁) (1 - 2 * b) ((0 : ℝ) : ℂ)) • 1)⁻¹
  set M := frameFin b e X J (ω₁, 0)
  rw [freshGamma_eq hF]
  change ((s : ℂ) • Mᴴ)ᴴ * (((1 - 2 * b : ℝ) : ℂ) • (Y * Yᴴ)) * ((s : ℂ) • Mᴴ) = _
  rw [conjTranspose_smul, conjTranspose_conjTranspose, Complex.star_def, Complex.conj_ofReal,
    conjTranspose_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  congr 1
  rw [← hs]
  push_cast
  ring

/-!
## Resolvent comparison
-/

/-- `(F - z)⁻¹ = (F - w)⁻¹(1 + (z - w)(F - z)⁻¹)`. -/
theorem inv_sub_eq_mul {ι : Type} [Fintype ι] [DecidableEq ι] {F : Matrix ι ι ℂ} {w z : ℂ}
    (hw : IsUnit (F - w • (1 : Matrix ι ι ℂ)).det) (hz : IsUnit (F - z • (1 : Matrix ι ι ℂ)).det) :
    (F - z • (1 : Matrix ι ι ℂ))⁻¹ = (F - w • 1)⁻¹ * (1 + (z - w) • (F - z • 1)⁻¹) := by
  have h1 : 1 + (z - w) • (F - z • (1 : Matrix ι ι ℂ))⁻¹ = (F - w • 1) * (F - z • 1)⁻¹ := by
    have h : F - w • (1 : Matrix ι ι ℂ) = (F - z • 1) + (z - w) • 1 := by
      rw [sub_smul]; abel
    rw [h, Matrix.add_mul, mul_nonsing_inv _ hz, Matrix.smul_mul, Matrix.one_mul, add_comm]
  rw [h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hw, Matrix.one_mul]

/-- `‖(1 + E)(1 + E)^* - 1‖ ≤ 2‖E‖ + ‖E‖²`. -/
theorem norm_one_add_mul_conj_sub_one_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℂ) : ‖(1 + E) * (1 + E)ᴴ - 1‖ ≤ 2 * ‖E‖ + ‖E‖ ^ 2 := by
  have h : (1 + E) * (1 + E)ᴴ - 1 = E + Eᴴ + E * Eᴴ := by
    rw [conjTranspose_add, conjTranspose_one]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [h]
  calc ‖E + Eᴴ + E * Eᴴ‖ ≤ ‖E‖ + ‖Eᴴ‖ + ‖E‖ * ‖Eᴴ‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (Matrix.l2_opNorm_mul _ _))
    _ = 2 * ‖E‖ + ‖E‖ ^ 2 := by rw [Matrix.l2_opNorm_conjTranspose]; ring

/-!
## The bulk scalars
-/

theorem semicircleDensity_eq_im (e : ℝ) :
    Parameters.semicircleDensity e = (star (matchedA e)).im / Real.pi := by
  unfold Parameters.semicircleDensity matchedA
  rw [Complex.star_def, Complex.conj_im]
  simp only [neg_div, neg_neg]
  field_simp

/-- The collar normalization `λ = πwc/W` (`w = residueWeight`). -/
def collarLambda (W : ℕ) (b e : ℝ) : ℝ := Real.pi * residueWeight W b e / W * (1 - 2 * b)

theorem collarLambda_nonneg (W : ℕ) {b e : ℝ} (hb : b < 1 / 2) : 0 ≤ collarLambda W b e := by
  unfold collarLambda
  have := residueWeight_nonneg W b e
  have : 0 < 1 - 2 * b := by linarith
  have := Real.pi_pos
  positivity

/-- **`λγ = 1` in the bulk** (`ρ(e)cγ = η/π`). -/
theorem collarLambda_mul_gamma (hW : 0 < W) {b e : ℝ} (hb : b < 1 / 2) (he : |e| < 2) :
    collarLambda W b e * commonPortGamma b = 1 := by
  have hai := BlockBand.Layers.matchedA_im_neg he
  have hη := BlockBand.Layers.boundaryZ_im (b := b) he.le
  have hb1 : 0 < 1 - b := by linarith
  have hc : 0 < 1 - 2 * b := by linarith
  have hηpos : 0 < (boundaryZ b e).im := by rw [hη]; nlinarith
  have hρ : Parameters.semicircleDensity e = -(matchedA e).im / Real.pi := by
    rw [semicircleDensity_eq_im, Complex.star_def, Complex.conj_im]
  have hpi := Real.pi_pos
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hres : residueWeight W b e = W * Parameters.semicircleDensity e / (boundaryZ b e).im := by
    unfold residueWeight poleScale
    refine max_eq_left ?_
    rw [hρ]
    have : 0 < -(matchedA e).im := by linarith
    positivity
  unfold collarLambda commonPortGamma
  rw [hres, hρ, hη]
  have h1 : (matchedA e).im ≠ 0 := hai.ne
  have h2 : (1 - 2 * b) ≠ 0 := hc.ne'
  have h3 : (1 - b) ≠ 0 := hb1.ne'
  field_simp
  exact div_self (by intro h; apply h2; linarith)

/-!
## The entrywise covariance bound
-/

/-- **Entrywise bound for the collar projection covariance** (deterministic). On `D` invertible,
`A`, `X` Hermitian, `|e| < 2`, `Im m_{F,c}(0) ≥ v > 0` and `|m_{F,c}(0) - ā| ≤ k`: for every
matrix `M` and every `γ` with `λγ = 1`,
`|(Ṽ^*Γ_FṼ - I)_{ij}| ≤ λ((2k/v + (k/v)²)‖L‖² + |u_i^*(LL^* - M)u_j| + ‖M - γI‖)`. -/
theorem collarCov_entry_le {b e : ℝ} (hb : b < 1 / 2) (he : |e| < 2)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {J : Matrix (Fin 2 × Fin W) (Fin r) ℂ} (hJ : Jᴴ * J = 1) {ω₁ : LayerSample W .common}
    (hA : ∀ k, (ω₁.1 k).IsHermitian) (hD : IsUnit (Collar.Density.collarTopBlock e X ω₁).det)
    {v k : ℝ} (hv : 0 < v)
    (hm : v ≤ (freshDyson (collarF e X ω₁) (1 - 2 * b) ((0 : ℝ) : ℂ)).im)
    (hk : ‖freshDyson (collarF e X ω₁) (1 - 2 * b) ((0 : ℝ) : ℂ) - star (matchedA e)‖ ≤ k)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (γ : ℝ) (hlam : collarLambda W b e * γ = 1)
    (i j : Fin r) :
    ‖((collarVt b e X J ω₁)ᴴ * freshGamma (collarF e X ω₁) (1 - 2 * b) 0 * collarVt b e X J ω₁ -
        (1 : Matrix (Fin r) (Fin r) ℂ)) i j‖ ≤
      collarLambda W b e * ((2 * (k / v) + (k / v) ^ 2) * ‖commonPortL b e X ω₁‖ ^ 2 +
        ‖star (fun x => J x i) ⬝ᵥ ((commonPortLL b e X ω₁ - M) *ᵥ fun x => J x j)‖ +
        ‖M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖) := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hF : (collarF e X ω₁).IsHermitian := by
    rw [collarF_eq_collarFW]; exact Collar.Density.collarFW_isHermitian e hX hA
  rw [collarVt_gamma_eq b e X J ω₁ hF]
  set lam := collarLambda W b e with hlamc
  have hlam0 : 0 ≤ lam := collarLambda_nonneg W hb
  change ‖((lam : ℂ) • _ - (1 : Matrix (Fin r) (Fin r) ℂ)) i j‖ ≤ _
  -- notation
  set c : ℝ := 1 - 2 * b with hcdef
  set m := freshDyson (collarF e X ω₁) c ((0 : ℝ) : ℂ) with hmdef
  set z : ℂ := ((0 : ℝ) : ℂ) + (c : ℂ) * m with hzdef
  rw [collarF_eq_collarFW] at hF ⊢
  set Fw := Collar.Density.collarFW e X ω₁ with hFw
  set w := Collar.Density.collarShiftW b e with hwdef
  have hw_eq : w = (c : ℂ) * matchedA e := Collar.Density.collarShiftW_eq he.le
  have hwim : w.im < 0 := by
    rw [hw_eq]
    have := BlockBand.Layers.matchedA_im_neg he
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg hc this
  have hzim : z.im = c * m.im := by simp [hzdef]
  have hmpos : 0 < m.im := hv.trans_le hm
  have hYu : IsUnit (Fw - star z • (1 : Matrix (Fin W) (Fin W) ℂ)).det :=
    Collar.Density.isUnit_det_sub_star_smul_one hF (z := z) (by rw [hzim]; positivity)
  have hHu : IsUnit (Fw - w • (1 : Matrix (Fin W) (Fin W) ℂ)).det :=
    Collar.Density.isUnit_det_collarFW_sub hX hA hwim
  have hS := Collar.Density.isUnit_det_collarF_sub (b := b) hX hA hwim
  set Y := (Fw - star z • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ with hY
  set E := (star z - w) • Y with hE
  set Lw := (commonPortL b e X ω₁).submatrix id (Collar.Density.portEquiv W).symm with hLw
  -- `Ψ = -(J^*L_w)(1 + E)`
  have hΨ : frameFin b e X J (ω₁, 0) * Y = -(Jᴴ * Lw) * (1 + E) := by
    rw [hY, inv_sub_eq_mul hHu hYu, ← hY, ← hE, frameFin_zero_eq, ← Matrix.mul_assoc]
    congr 1
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (_⁻¹),
      Collar.Density.commonPortL_submatrix_eq b e X ω₁ hD hS]
  have hΨΨ : (frameFin b e X J (ω₁, 0) * Y) * (frameFin b e X J (ω₁, 0) * Y)ᴴ =
      Jᴴ * (Lw * ((1 + E) * (1 + E)ᴴ) * Lwᴴ) * J := by
    rw [hΨ, conjTranspose_mul, conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  have hLL : Lw * Lwᴴ = commonPortLL b e X ω₁ := by
    rw [hLw, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id]
    rfl
  -- entries
  set u : Fin 2 × Fin W → ℂ := fun x => J x i with hu
  set u' : Fin 2 × Fin W → ℂ := fun x => J x j with hu'
  set G := (1 + E) * (1 + E)ᴴ with hG
  have hentry : ((lam : ℂ) • ((frameFin b e X J (ω₁, 0) * Y) *
      (frameFin b e X J (ω₁, 0) * Y)ᴴ) - (1 : Matrix (Fin r) (Fin r) ℂ)) i j =
        (lam : ℂ) * (star (Lwᴴ *ᵥ u) ⬝ᵥ ((G - 1) *ᵥ (Lwᴴ *ᵥ u'))) +
        (lam : ℂ) * (star u ⬝ᵥ ((commonPortLL b e X ω₁ - M) *ᵥ u')) +
        (lam : ℂ) * (star u ⬝ᵥ ((M - ((γ : ℝ) : ℂ) • 1) *ᵥ u')) := by
    rw [hΨΨ, Matrix.sub_apply, Matrix.smul_apply, conjTranspose_mul_mul_apply,
      one_apply_eq_dotProduct hJ, ← star_dotProduct_sandwich, smul_eq_mul]
    have h1 : (1 : ℂ) = (lam : ℂ) * (γ : ℂ) := by exact_mod_cast hlam.symm
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hLL, sub_mulVec, dotProduct_sub,
      smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [← hu, ← hu']
    linear_combination (-(star u ⬝ᵥ u')) * h1
  rw [hentry]
  -- the three bounds
  have hEn : ‖E‖ ≤ k / v := by
    have hsz : ‖star z - w‖ ≤ c * k := by
      have : star z - w = (c : ℂ) * star (m - star (matchedA e)) := by
        rw [hzdef, hw_eq, star_add, star_mul', star_sub, star_star]
        simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_zero, map_zero, zero_add]
        ring
      rw [this, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left hk hc.le
    have hYn : ‖Y‖ ≤ (c * v)⁻¹ := by
      rw [hY, smul_one_eq_diagonal]
      refine BlockBand.Layers.lct_norm_shifted_inv_le Fw hF _ (by positivity) fun _ => ?_
      rw [Complex.star_def, Complex.conj_im, neg_neg, hzim]
      exact mul_le_mul_of_nonneg_left hm hc.le
    calc ‖E‖ ≤ ‖star z - w‖ * ‖Y‖ := norm_smul_le _ _
      _ ≤ (c * k) * (c * v)⁻¹ :=
          mul_le_mul hsz hYn (norm_nonneg _) (by
            have : 0 ≤ ‖star z - w‖ := norm_nonneg _
            linarith [hsz, this])
      _ = k / v := by field_simp
  have hk0 : 0 ≤ k := (norm_nonneg _).trans hk
  have hG1 : ‖G - 1‖ ≤ 2 * (k / v) + (k / v) ^ 2 := by
    refine (norm_one_add_mul_conj_sub_one_le E).trans ?_
    have := norm_nonneg E
    have hkv : 0 ≤ k / v := div_nonneg hk0 hv.le
    nlinarith
  have hLu : ∀ q : Fin 2 × Fin W → ℂ, l2Norm (Lwᴴ *ᵥ q) ≤ ‖commonPortL b e X ω₁‖ * l2Norm q := by
    intro q
    have h := l2Norm_mulVec_le (commonPortL b e X ω₁)ᴴ q
    rw [Matrix.l2_opNorm_conjTranspose] at h
    refine le_of_eq_of_le ?_ h
    unfold l2Norm
    rw [hLw, Collar.Density.sum_norm_sq_conjTranspose_submatrix]
  have hun : l2Norm u = 1 := l2Norm_frame_col hJ i
  have hun' : l2Norm u' = 1 := l2Norm_frame_col hJ j
  have hT1 : ‖star (Lwᴴ *ᵥ u) ⬝ᵥ ((G - 1) *ᵥ (Lwᴴ *ᵥ u'))‖ ≤
      (2 * (k / v) + (k / v) ^ 2) * ‖commonPortL b e X ω₁‖ ^ 2 := by
    refine (norm_star_dotProduct_mulVec_le _ _ _).trans ?_
    have h1 := hLu u
    have h2 := hLu u'
    rw [hun, mul_one] at h1
    rw [hun', mul_one] at h2
    have := l2Norm_nonneg' (Lwᴴ *ᵥ u)
    have := l2Norm_nonneg' (Lwᴴ *ᵥ u')
    have := norm_nonneg (G - 1)
    calc ‖G - 1‖ * l2Norm (Lwᴴ *ᵥ u) * l2Norm (Lwᴴ *ᵥ u') ≤
        (2 * (k / v) + (k / v) ^ 2) * ‖commonPortL b e X ω₁‖ * ‖commonPortL b e X ω₁‖ := by
          gcongr
      _ = _ := by ring
  have hT3 : ‖star u ⬝ᵥ ((M - ((γ : ℝ) : ℂ) • 1) *ᵥ u')‖ ≤
      ‖M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ := by
    refine (norm_star_dotProduct_mulVec_le _ _ _).trans ?_
    rw [hun, hun', mul_one, mul_one]
  have hlamn : ‖(lam : ℂ)‖ = lam := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam0]
  calc _ ≤ ‖(lam : ℂ) * (star (Lwᴴ *ᵥ u) ⬝ᵥ ((G - 1) *ᵥ (Lwᴴ *ᵥ u')))‖ +
        ‖(lam : ℂ) * (star u ⬝ᵥ ((commonPortLL b e X ω₁ - M) *ᵥ u'))‖ +
        ‖(lam : ℂ) * (star u ⬝ᵥ ((M - ((γ : ℝ) : ℂ) • 1) *ᵥ u'))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
        rw [norm_mul, norm_mul, norm_mul, hlamn]
        have := norm_nonneg (star u ⬝ᵥ ((commonPortLL b e X ω₁ - M) *ᵥ u'))
        nlinarith [mul_le_mul_of_nonneg_left hT1 hlam0, mul_le_mul_of_nonneg_left hT3 hlam0]

end BlockBand.Critical.MatrixClosing.Poles
