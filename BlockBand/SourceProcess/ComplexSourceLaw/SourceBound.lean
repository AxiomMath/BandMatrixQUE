module

public import BlockBand.SourceProcess.ComplexSourceLaw.Algebra

/-!
# Pointwise control of the source data by the entries of `𝒦`

From `𝒦 - 𝒦ᴴ = (z̄ - z) M_pr` and `|z̄ - z| = 2η`, and the bound
`|(Yᴴ diag(d) Y)ᵢⱼ| ≤ ((YᴴY)ᵢᵢ + (YᴴY)ⱼⱼ)/2` for `|d| ≤ 1`, every entry of the source data
`y = (𝒦, M_pr, B_pr, J_pr)` satisfies `|yᵣᵢⱼ| ≤ (1 + η⁻¹)(|𝒦ᵢⱼ| + |𝒦ⱼᵢ| + |𝒦ᵢᵢ| + |𝒦ⱼⱼ|)`
(`norm_sourceData_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexConjugate

variable {W : ℕ}

/-- `𝒦 - 𝒦ᴴ = (z̄ - z) M_pr`. -/
theorem kc_sub_conjTranspose (b E : ℝ) {np : ℕ} (n : ℕ) (τ m : Fin np → ℝ)
    (x : ProbedPath W np) (hA : ∀ k, (x.1.1 k).IsHermitian) :
    complexSourceK b E W n τ m x - (complexSourceK b E W n τ m x)ᴴ =
      (conj (boundaryZ b E) - boundaryZ b E) •
        ((probeFrame b E W n τ m x)ᴴ * probeFrame b E W n τ m x) := by
  have h := interior_sub_conjTranspose b E n x.1 hA
  have e1 : complexSourceK b E W n τ m x - (complexSourceK b E W n τ m x)ᴴ =
      (probeColumns W n τ m x.2)ᴴ * ((fullInverse b E W n x.1).toBlocks₁₁ -
        ((fullInverse b E W n x.1).toBlocks₁₁)ᴴ) * probeColumns W n τ m x.2 := by
    simp only [complexSourceK, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc]
  rw [e1, h]
  simp only [probeFrame, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]

/-- `|(z̄ - z)| = 2η`. -/
theorem norm_conj_boundaryZ_sub (b E : ℝ) (hη : 0 < etaZ b E) :
    ‖conj (boundaryZ b E) - boundaryZ b E‖ = 2 * etaZ b E := by
  rw [conj_boundaryZ_sub, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  norm_num

/-- `|(M_pr)ᵢⱼ| ≤ (|𝒦ᵢⱼ| + |𝒦ⱼᵢ|)/(2η)`. -/
theorem norm_gram_entry_le (b E : ℝ) (hη : 0 < etaZ b E) {np : ℕ} (n : ℕ) (τ m : Fin np → ℝ)
    (x : ProbedPath W np) (hA : ∀ k, (x.1.1 k).IsHermitian) (i j : Fin np) :
    ‖((probeFrame b E W n τ m x)ᴴ * probeFrame b E W n τ m x) i j‖ ≤
      (‖complexSourceK b E W n τ m x i j‖ + ‖complexSourceK b E W n τ m x j i‖) /
        (2 * etaZ b E) := by
  have h := congrFun (congrFun (kc_sub_conjTranspose b E n τ m x hA) i) j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.conjTranspose_apply] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_conj_boundaryZ_sub b E hη] at hn
  rw [le_div_iff₀ (by positivity), mul_comm, ← hn]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_star]

/-- `(YᴴY)ᵢᵢ = Σₓ |Yₓᵢ|²`. -/
theorem norm_gram_diag {ι c : Type*} [Fintype ι] (Y : Matrix ι c ℂ) (i : c) :
    ‖(Yᴴ * Y) i i‖ = ∑ x, ‖Y x i‖ ^ 2 := by
  have : (Yᴴ * Y) i i = ((∑ x, ‖Y x i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum,
      Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  rw [this, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]

/-- `|(Yᴴ diag(d) Y)ᵢⱼ| ≤ ((YᴴY)ᵢᵢ + (YᴴY)ⱼⱼ)/2` for `|d| ≤ 1`. -/
theorem norm_sandwich_diag_le {ι c : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι c ℂ)
    (d : ι → ℂ) (hd : ∀ x, ‖d x‖ ≤ 1) (i j : c) :
    ‖(Yᴴ * Matrix.diagonal d * Y) i j‖ ≤ (‖(Yᴴ * Y) i i‖ + ‖(Yᴴ * Y) j j‖) / 2 := by
  rw [norm_gram_diag, norm_gram_diag, ← Finset.sum_add_distrib, Finset.sum_div, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have h1 : ‖Y x i‖ * ‖d x‖ ≤ ‖Y x i‖ := mul_le_of_le_one_right (norm_nonneg _) (hd x)
  nlinarith [sq_nonneg (‖Y x i‖ - ‖Y x j‖), norm_nonneg (Y x j), norm_nonneg (Y x i)]

theorem nearProjection_eq_diagonal :
    nearProjection W = Matrix.diagonal fun x : Fin 2 × Fin W => if x.1 = 0 then 1 else 0 := rfl

theorem norm_nearIndicator_le (x : Fin 2 × Fin W) : ‖(if x.1 = 0 then (1 : ℂ) else 0)‖ ≤ 1 := by
  split_ifs <;> simp

/-- **Pointwise control of the source data by `𝒦`**: for Hermitian path blocks and `η > 0`,
`|yᵣᵢⱼ| ≤ (1 + η⁻¹)(|𝒦ᵢⱼ| + |𝒦ⱼᵢ| + |𝒦ᵢᵢ| + |𝒦ⱼⱼ|)` for `y = (𝒦, M_pr, B_pr, J_pr)`. -/
theorem norm_sourceData_le (b E : ℝ) (hη : 0 < etaZ b E) {np : ℕ} (n : ℕ) (τ m : Fin np → ℝ)
    (x : ProbedPath W np) (hA : ∀ k, (x.1.1 k).IsHermitian) (r : Fin 4) (i j : Fin np) :
    ‖complexSourceData b E W n τ m x r i j‖ ≤ (1 + (etaZ b E)⁻¹) *
      (‖complexSourceK b E W n τ m x i j‖ + ‖complexSourceK b E W n τ m x j i‖ +
        ‖complexSourceK b E W n τ m x i i‖ + ‖complexSourceK b E W n τ m x j j‖) := by
  set K := complexSourceK b E W n τ m x
  set V := probeFrame b E W n τ m x
  set e := (etaZ b E)⁻¹
  have he : 0 < e := inv_pos.2 hη
  have hdiv : ∀ a : ℝ, a / (2 * etaZ b E) = e * a / 2 := fun a => by
    simp only [e]; field_simp
  have hM : ∀ a c, ‖(Vᴴ * V) a c‖ ≤ e * (‖K a c‖ + ‖K c a‖) / 2 := fun a c => by
    rw [← hdiv]; exact norm_gram_entry_le b E hη n τ m x hA a c
  have hMd : ∀ a, ‖(Vᴴ * V) a a‖ ≤ e * ‖K a a‖ := fun a => by
    have := hM a a; linarith
  have hS : (scatteringMatrix b E W n x.1 * V)ᴴ * (scatteringMatrix b E W n x.1 * V) = Vᴴ * V := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ V,
      conjTranspose_mul_scattering b E n x.1 hA, Matrix.one_mul]
  have hB : ‖(Vᴴ * nearProjection W * V) i j‖ ≤ (‖(Vᴴ * V) i i‖ + ‖(Vᴴ * V) j j‖) / 2 := by
    rw [nearProjection_eq_diagonal]
    exact norm_sandwich_diag_le V _ norm_nearIndicator_le i j
  have hJ1 : ‖((scatteringMatrix b E W n x.1 * V)ᴴ * nearProjection W *
      (scatteringMatrix b E W n x.1 * V)) i j‖ ≤ (‖(Vᴴ * V) i i‖ + ‖(Vᴴ * V) j j‖) / 2 := by
    rw [nearProjection_eq_diagonal, ← hS]
    exact norm_sandwich_diag_le _ _ norm_nearIndicator_le i j
  have hJ : Vᴴ * pathCurrent b E W n x.1 * V =
      (scatteringMatrix b E W n x.1 * V)ᴴ * nearProjection W *
        (scatteringMatrix b E W n x.1 * V) - Vᴴ * nearProjection W * V := by
    rw [pathCurrent, conjTranspose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have n1 := norm_nonneg (K i j)
  have n2 := norm_nonneg (K j i)
  have n3 := norm_nonneg (K i i)
  have n4 := norm_nonneg (K j j)
  have hSum : ∀ X : ℝ, X ≤ e * (‖K i j‖ + ‖K j i‖ + ‖K i i‖ + ‖K j j‖) →
      X ≤ (1 + e) * (‖K i j‖ + ‖K j i‖ + ‖K i i‖ + ‖K j j‖) := fun X hX => by nlinarith
  have hMi := hMd i
  have hMj := hMd j
  fin_cases r
  · show ‖K i j‖ ≤ _
    nlinarith
  · refine hSum _ ((hM i j).trans ?_)
    show e * (‖K i j‖ + ‖K j i‖) / 2 ≤ _
    nlinarith
  · refine hSum _ (hB.trans ?_)
    nlinarith
  · refine hSum _ ?_
    show ‖(Vᴴ * pathCurrent b E W n x.1 * V) i j‖ ≤ _
    rw [hJ, Matrix.sub_apply]
    refine (norm_sub_le _ _).trans ?_
    nlinarith

end BlockBand.SourceProcess.ComplexSourceLaw
