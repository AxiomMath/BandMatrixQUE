module

public import BlockBand.Critical.Collar.Density.CondSchurAnalysis

/-!
# Conditional Schur identity: Kernels

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

The top quadratic form `csTop` of the spectral projector of the pencil, the smoothed kernels
`csK` (real scalar, height `ε`) and `csF` (Cauchy-averaged scalar), their bounds, continuity and
the exact relation `csF = E_s csK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter Topology
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open BlockBand.Critical.WeightedDensity (cauchyKernel cauchyKernel_eq_im_inv cauchyKernel_nonneg
  continuous_cauchyKernel measurable_cauchyKernel)
open scoped ComplexConjugate ComplexOrder

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {D : Matrix m m ℂ} {B : Matrix m n ℂ} {G : Matrix n n ℂ}

/-- The top quadratic form of the spectral projector of the pencil at a real scalar `θ`. -/
def csTop (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ) (a₁ a₂ : ℝ) (u : m → ℂ)
    (θ : ℝ) : ℝ :=
  quadForm ((cfc ((Set.Icc a₁ a₂).indicator (1 : ℝ → ℝ)) (csPencil D B G θ)).toBlocks₁₁) u

theorem continuous_csPencil (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ) :
    Continuous fun w : ℂ => csPencil D B G w := by
  have h : (fun w : ℂ => csPencil D B G w) = fun w => csPencil D B G 0 + w • csPort := by
    funext w; rw [← csPencil_add, zero_add]
  rw [h]; fun_prop

theorem continuous_quadForm_toBlocks11 (u : m → ℂ) :
    Continuous fun N : Matrix (m ⊕ n) (m ⊕ n) ℂ => quadForm N.toBlocks₁₁ u := by
  unfold quadForm
  have h : ∀ N : Matrix (m ⊕ n) (m ⊕ n) ℂ, N.toBlocks₁₁ = N.submatrix Sum.inl Sum.inl :=
    fun N => rfl
  simp_rw [h]
  exact Complex.continuous_re.comp (continuous_const.dotProduct
    ((continuous_id.matrix_submatrix _ _).matrix_mulVec continuous_const))

theorem csTop_eq_sum (hD : D.IsHermitian) (hG : G.IsHermitian) (a₁ a₂ : ℝ) (u : m → ℂ)
    (θ : ℝ) :
    csTop D B G a₁ a₂ u θ = ∑ r, (Set.Icc a₁ a₂).indicator (1 : ℝ → ℝ)
      (increasingEigenvalue (csPencil_isHermitian (B := B) hD hG θ) r) *
      ‖star (increasingEigenvector (csPencil_isHermitian (B := B) hD hG θ) r) ⬝ᵥ
        Sum.elim u (0 : n → ℂ)‖ ^ 2 :=
  quadForm_cfc_toBlocks11 _ _ u

theorem sum_eigen_weight {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (ψ : ι → ℂ) :
    ∑ r, ‖star (increasingEigenvector hH r) ⬝ᵥ ψ‖ ^ 2 = ∑ a, ‖ψ a‖ ^ 2 :=
  (sum_norm_sq_eq_sum_eigen hH ψ).symm

theorem sum_norm_sq_sumElim (u : m → ℂ) :
    ∑ a, ‖Sum.elim u (0 : n → ℂ) a‖ ^ 2 = ∑ a, ‖u a‖ ^ 2 := by
  simp [Fintype.sum_sum_type]

theorem csTop_nonneg_le (hD : D.IsHermitian) (hG : G.IsHermitian) (a₁ a₂ : ℝ) (u : m → ℂ)
    (θ : ℝ) : 0 ≤ csTop D B G a₁ a₂ u θ ∧ csTop D B G a₁ a₂ u θ ≤ ∑ a, ‖u a‖ ^ 2 := by
  rw [csTop_eq_sum hD hG, ← sum_norm_sq_sumElim (n := n),
    ← sum_eigen_weight (csPencil_isHermitian (B := B) hD hG θ)]
  have hind : ∀ y : ℝ, 0 ≤ (Set.Icc a₁ a₂).indicator (1 : ℝ → ℝ) y ∧
      (Set.Icc a₁ a₂).indicator (1 : ℝ → ℝ) y ≤ 1 := fun y => by
    by_cases hy : y ∈ Set.Icc a₁ a₂
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  constructor
  · exact Finset.sum_nonneg fun r _ => mul_nonneg (hind _).1 (sq_nonneg _)
  · exact Finset.sum_le_sum fun r _ => mul_le_of_le_one_left (sq_nonneg _) (hind _).2

theorem measurable_csTop (hD : D.IsHermitian) (hG : G.IsHermitian) (a₁ a₂ : ℝ) (u : m → ℂ) :
    Measurable (csTop D B G a₁ a₂ u) := by
  have heq : csTop D B G a₁ a₂ u = fun θ : ℝ => quadForm ((rawCfc ((Set.Icc a₁ a₂).indicator
      (1 : ℝ → ℝ)) (csPencil D B G θ)).toBlocks₁₁) u := by
    funext θ
    rw [csTop, rawCfc_eq_cfc (csPencil_isHermitian hD hG θ)]
  rw [heq]
  have hM : Measurable fun θ : ℝ => csPencil D B G θ :=
    ((continuous_csPencil D B G).comp Complex.continuous_ofReal).measurable
  have hR : Measurable fun θ : ℝ => rawCfc ((Set.Icc a₁ a₂).indicator (1 : ℝ → ℝ))
      (csPencil D B G θ) :=
    measurable_matrix_of_entries fun x y =>
      measurable_rawCfc_apply hM (measurable_const.indicator measurableSet_Icc) x y
  exact (continuous_quadForm_toBlocks11 (n := n) u).measurable.comp hR

/-!
## The smoothed kernels
-/

/-- `K_ε(s, x) = π⁻¹ Im ũ*(csPencil(t + ηs) - x - iε)⁻¹ũ`. -/
def csK (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ) (u : m → ℂ) (t η ε : ℝ)
    (s x : ℝ) : ℝ :=
  Real.pi⁻¹ * (star (Sum.elim u (0 : n → ℂ)) ⬝ᵥ ((csPencil D B G ((t + η * s : ℝ) : ℂ) -
    ((x : ℂ) + (ε : ℂ) * Complex.I) • 1)⁻¹ *ᵥ Sum.elim u 0)).im

/-- `F_ε(x) = π⁻¹ Im ũ*(csPencil(t - iη) - x - iε)⁻¹ũ`. -/
def csF (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ) (u : m → ℂ) (t η ε : ℝ)
    (x : ℝ) : ℝ :=
  Real.pi⁻¹ * (star (Sum.elim u (0 : n → ℂ)) ⬝ᵥ ((csPencil D B G ((t : ℂ) - (η : ℂ) * Complex.I) -
    ((x : ℂ) + (ε : ℂ) * Complex.I) • 1)⁻¹ *ᵥ Sum.elim u 0)).im

theorem csK_eq_sum (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ) (t η : ℝ) {ε : ℝ}
    (hε : 0 < ε) (s x : ℝ) :
    csK D B G u t η ε s x = ∑ r, cauchyKernel ε (x - increasingEigenvalue
      (csPencil_isHermitian (B := B) hD hG (t + η * s)) r) *
      ‖star (increasingEigenvector (csPencil_isHermitian (B := B) hD hG (t + η * s)) r) ⬝ᵥ
        Sum.elim u (0 : n → ℂ)‖ ^ 2 :=
  im_resolventForm_eq_sum _ x hε _

theorem continuous_csK (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ) (t η : ℝ)
    {ε : ℝ} (hε : 0 < ε) : Continuous fun p : ℝ × ℝ => csK D B G u t η ε p.1 p.2 := by
  have hM : Continuous fun p : ℝ × ℝ => csPencil D B G ((t + η * p.1 : ℝ) : ℂ) -
      ((p.2 : ℂ) + (ε : ℂ) * Complex.I) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) := by
    refine ((continuous_csPencil D B G).comp ?_).sub ?_ <;> fun_prop
  have hU : ∀ p : ℝ × ℝ, IsUnit (csPencil D B G ((t + η * p.1 : ℝ) : ℂ) -
      ((p.2 : ℂ) + (ε : ℂ) * Complex.I) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ)).det := fun p =>
    isUnit_det_sub_smul_one' (csPencil_isHermitian hD hG _) (by simp [hε])
  have hinv := continuous_inv_of_isUnit_det hM hU
  unfold csK
  exact continuous_const.mul (Complex.continuous_im.comp (continuous_const.dotProduct
    (hinv.matrix_mulVec continuous_const)))

theorem csK_nonneg_le (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ) (t η : ℝ)
    {ε : ℝ} (hε : 0 < ε) (s x : ℝ) :
    0 ≤ csK D B G u t η ε s x ∧ csK D B G u t η ε s x ≤ (Real.pi * ε)⁻¹ * ∑ a, ‖u a‖ ^ 2 := by
  rw [csK_eq_sum hD hG u t η hε, ← sum_norm_sq_sumElim (n := n),
    ← sum_eigen_weight (csPencil_isHermitian (B := B) hD hG (t + η * s)), Finset.mul_sum]
  constructor
  · exact Finset.sum_nonneg fun r _ => mul_nonneg (cauchyKernel_nonneg hε.le _) (sq_nonneg _)
  · exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (cauchyKernel_le hε _)
      (sq_nonneg _)

/-- `∫_I K_ε(s, ·) = Σ_r w_r ∫_I P_ε(x - μ_r)`. -/
theorem setIntegral_csK_eq (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ) (t η : ℝ)
    {ε : ℝ} (hε : 0 < ε) (s a₁ a₂ : ℝ) :
    ∫ x in Set.Icc a₁ a₂, csK D B G u t η ε s x = ∑ r,
      (∫ x in Set.Icc a₁ a₂, cauchyKernel ε (x - increasingEigenvalue
        (csPencil_isHermitian (B := B) hD hG (t + η * s)) r)) *
      ‖star (increasingEigenvector (csPencil_isHermitian (B := B) hD hG (t + η * s)) r) ⬝ᵥ
        Sum.elim u (0 : n → ℂ)‖ ^ 2 := by
  simp_rw [csK_eq_sum hD hG u t η hε]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_mul_const]
  · intro r _
    exact (((continuous_cauchyKernel hε).comp (continuous_id.sub continuous_const)).mul
      continuous_const).integrableOn_Icc

theorem csF_eq_integral (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ) (t : ℝ) {η : ℝ}
    (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    csF D B G u t η ε x = ∫ s, csK D B G u t η ε s x ∂stdCauchy := by
  have h := isCauchyMean_topForm (B := B) hD hG t hη (z := (x : ℂ) + (ε : ℂ) * Complex.I)
    (by simp [hε]) (Sum.elim u 0)
  unfold csF csK
  rw [integral_const_mul]
  congr 1
  rw [← h.2]
  exact (integral_im h.1).symm

end BlockBand.Critical.Collar.Density
