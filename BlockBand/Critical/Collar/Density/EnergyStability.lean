module

public import BlockBand.Critical.Collar.Density.Window

/-!
# Stability of the matched scalars and of `d(X)` in the energy

* `norm_matchedA_sub_le`: `‖a(E) - a(E')‖ ≤ (1/2 + 1/√(4-(2-κ)²))|E - E'|` on `bulkInterval κ`.
* `norm_boundaryZ_sub_le`: `‖z_b(E) - z_b(E')‖ ≤ (1 + (1-b)L_κ)|E - E'|`.
* `norm_inv_mul_inv_apply_le`: `|[(z'-X)⁻¹(z-X)⁻¹]_{aa}| ≤ (Im z' Im z)⁻¹` for Hermitian `X`.
* `matchedDistance_le_energy`: `d_{E'}(X) ≤ d_E(X) + ‖z_b(E)-z_b(E')‖/(Im z_b(E') Im z_b(E)) +
  ‖a(E') - a(E)‖` for Hermitian `X` (no norm bound on `X`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Foundations.Spectral
open scoped ComplexConjugate

/-!
## Lipschitz bounds for the matched scalars
-/

theorem le_two_of_mem_bulkInterval {κ E : ℝ} (hE : E ∈ bulkInterval κ) : κ ≤ 2 := by
  have h1 := hE.1; have h2 := hE.2; linarith

theorem norm_matchedA_sub_le {κ E E' : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    (hE' : E' ∈ bulkInterval κ) :
    ‖matchedA E - matchedA E'‖ ≤ (1 / 2 + 1 / Real.sqrt (4 - (2 - κ) ^ 2)) * |E - E'| := by
  have hκ2 := le_two_of_mem_bulkInterval hE
  have hm : 0 < 4 - (2 - κ) ^ 2 := BlockBand.Layers.four_sub_sq_pos hκ (by linarith)
  have hsm : 0 < Real.sqrt (4 - (2 - κ) ^ 2) := Real.sqrt_pos.2 hm
  have hE2 := BlockBand.Layers.sq_le_of_mem_bulkInterval hE
  have hE2' := BlockBand.Layers.sq_le_of_mem_bulkInterval hE'
  have hu : 4 - (2 - κ) ^ 2 ≤ 4 - E ^ 2 := by linarith
  have hu' : 4 - (2 - κ) ^ 2 ≤ 4 - E' ^ 2 := by linarith
  have hs1 : Real.sqrt (4 - (2 - κ) ^ 2) ≤ Real.sqrt (4 - E ^ 2) := Real.sqrt_le_sqrt hu
  have hs2 : Real.sqrt (4 - (2 - κ) ^ 2) ≤ Real.sqrt (4 - E' ^ 2) := Real.sqrt_le_sqrt hu'
  have hprod : (Real.sqrt (4 - E ^ 2) - Real.sqrt (4 - E' ^ 2)) *
      (Real.sqrt (4 - E ^ 2) + Real.sqrt (4 - E' ^ 2)) = E' ^ 2 - E ^ 2 := by
    have h1 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 - E ^ 2)
    have h2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 - E' ^ 2)
    nlinarith
  have hsum : 2 * Real.sqrt (4 - (2 - κ) ^ 2) ≤
      Real.sqrt (4 - E ^ 2) + Real.sqrt (4 - E' ^ 2) := by linarith
  have hEE : |E' ^ 2 - E ^ 2| ≤ 4 * |E - E'| := by
    have hb : |E' + E| ≤ 4 := by
      have := BlockBand.Layers.abs_le_of_mem_bulkInterval hE
      have := BlockBand.Layers.abs_le_of_mem_bulkInterval hE'
      calc |E' + E| ≤ |E'| + |E| := abs_add_le _ _
        _ ≤ 4 := by linarith
    rw [show E' ^ 2 - E ^ 2 = (E' + E) * (E' - E) by ring, abs_mul, abs_sub_comm E' E]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hsq : |Real.sqrt (4 - E ^ 2) - Real.sqrt (4 - E' ^ 2)| ≤
      2 / Real.sqrt (4 - (2 - κ) ^ 2) * |E - E'| := by
    have hpos : 0 < Real.sqrt (4 - E ^ 2) + Real.sqrt (4 - E' ^ 2) := by linarith
    have heq : Real.sqrt (4 - E ^ 2) - Real.sqrt (4 - E' ^ 2) =
        (E' ^ 2 - E ^ 2) / (Real.sqrt (4 - E ^ 2) + Real.sqrt (4 - E' ^ 2)) := by
      field_simp; linarith [hprod]
    rw [heq, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |E' ^ 2 - E ^ 2| ≤ 4 * |E - E'| := hEE
      _ = 2 / Real.sqrt (4 - (2 - κ) ^ 2) * |E - E'| * (2 * Real.sqrt (4 - (2 - κ) ^ 2)) := by
          field_simp; ring
      _ ≤ 2 / Real.sqrt (4 - (2 - κ) ^ 2) * |E - E'| *
          (Real.sqrt (4 - E ^ 2) + Real.sqrt (4 - E' ^ 2)) := by gcongr
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [matchedA, Complex.sub_re, Complex.sub_im]
  have hre : |-E / 2 - -E' / 2| = |E - E'| / 2 := by
    rw [show -E / 2 - -E' / 2 = -(E - E') / 2 by ring, abs_div, abs_neg]; norm_num
  have him : |-Real.sqrt (4 - E ^ 2) / 2 - -Real.sqrt (4 - E' ^ 2) / 2| =
      |Real.sqrt (4 - E ^ 2) - Real.sqrt (4 - E' ^ 2)| / 2 := by
    rw [show -Real.sqrt (4 - E ^ 2) / 2 - -Real.sqrt (4 - E' ^ 2) / 2 =
      -(Real.sqrt (4 - E ^ 2) - Real.sqrt (4 - E' ^ 2)) / 2 by ring, abs_div, abs_neg]; norm_num
  rw [hre, him]
  have : |Real.sqrt (4 - E ^ 2) - Real.sqrt (4 - E' ^ 2)| / 2 ≤
      1 / Real.sqrt (4 - (2 - κ) ^ 2) * |E - E'| := by
    have := hsq; rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc |Real.sqrt (4 - E ^ 2) - Real.sqrt (4 - E' ^ 2)| ≤
        2 / Real.sqrt (4 - (2 - κ) ^ 2) * |E - E'| := hsq
      _ = 1 / Real.sqrt (4 - (2 - κ) ^ 2) * |E - E'| * 2 := by ring
  linarith

theorem norm_boundaryZ_sub_le {b κ E E' : ℝ} (hb1 : b ≤ 1) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) (hE' : E' ∈ bulkInterval κ) :
    ‖boundaryZ b E - boundaryZ b E'‖ ≤
      (1 + (1 - b) * (1 / 2 + 1 / Real.sqrt (4 - (2 - κ) ^ 2))) * |E - E'| := by
  rw [BlockBand.Layers.boundaryZ_eq (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ hE).le,
    BlockBand.Layers.boundaryZ_eq (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ hE').le]
  have h := norm_matchedA_sub_le hκ hE hE'
  have heq : -(E : ℂ) - (1 - (b : ℂ)) * matchedA E - (-(E' : ℂ) - (1 - (b : ℂ)) * matchedA E') =
      -((E - E' : ℝ) : ℂ) - ((1 - b : ℝ) : ℂ) * (matchedA E - matchedA E') := by push_cast; ring
  rw [heq]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - b)]
  have h1b : 0 ≤ 1 - b := by linarith
  nlinarith [abs_nonneg (E - E'), mul_le_mul_of_nonneg_left h h1b]

/-!
## Diagonal entries of resolvent products
-/

theorem specSum_mul_specSum {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (g h : ℝ → ℂ) :
    specSum hM g * specSum hM h = specSum hM (fun l => g l * h l) := by
  refine BlockBand.Model.Construction.matrix_eq_of_mulVec_increasingEigenvector_eq ⟨M, hM⟩ _ _
    fun r => ?_
  change (specSum hM g * specSum hM h) *ᵥ increasingEigenvector hM r =
    specSum hM (fun l => g l * h l) *ᵥ increasingEigenvector hM r
  rw [← mulVec_mulVec, specSum_mulVec_eigenvector, mulVec_smul, specSum_mulVec_eigenvector,
    specSum_mulVec_eigenvector, smul_smul, mul_comm]

theorem specSum_neg {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (g : ℝ → ℂ) : specSum hM (fun l => -g l) = -specSum hM g := by
  simp only [specSum, neg_smul, Finset.sum_neg_distrib]

theorem sum_norm_sq_increasingEigenvector_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (a : ι) :
    ∑ r, ‖increasingEigenvector hM r a‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (specSum_one hM) a) a
  rw [specSum_apply, one_apply_eq] at h
  have h2 := congrArg Complex.re h
  simp only [one_mul, Complex.re_sum, Complex.one_re] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem norm_specSum_apply_self_le {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) {g : ℝ → ℂ} {B : ℝ} (hg : ∀ l, ‖g l‖ ≤ B) (a : ι) :
    ‖specSum hM g a a‖ ≤ B := by
  rw [specSum_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ r, ‖g (increasingEigenvalue hM r) * (increasingEigenvector hM r a *
        star (increasingEigenvector hM r a))‖
      = ∑ r, ‖g (increasingEigenvalue hM r)‖ * ‖increasingEigenvector hM r a‖ ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [norm_mul, norm_mul, norm_star, sq]
    _ ≤ ∑ r, B * ‖increasingEigenvector hM r a‖ ^ 2 :=
        Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hg _) (sq_nonneg _)
    _ = B := by rw [← Finset.mul_sum, sum_norm_sq_increasingEigenvector_apply hM a, mul_one]

theorem inv_smul_one_sub_eq_specSum {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (z • (1 : Matrix ι ι ℂ) - X)⁻¹ = specSum hX (fun l => -((l : ℂ) - z)⁻¹) := by
  have hu : IsUnit (X - z • (1 : Matrix ι ι ℂ)).det := by
    have h := inv_sub_eq_specSum hX hz
    have hinv : (X - z • (1 : Matrix ι ι ℂ)) * (X - z • 1)⁻¹ = 1 := by
      rw [h]
      refine BlockBand.Model.Construction.matrix_eq_of_mulVec_increasingEigenvector_eq ⟨X, hX⟩ _ _
        fun r => ?_
      change ((X - z • 1) * specSum hX _) *ᵥ increasingEigenvector hX r = 1 *ᵥ _
      have hne : ((increasingEigenvalue hX r : ℝ) : ℂ) - z ≠ 0 := fun h0 => hz (by
        have := congrArg Complex.im h0; simpa using this.symm)
      rw [← mulVec_mulVec, specSum_mulVec_eigenvector, mulVec_smul, sub_mulVec,
        mulVec_increasingEigenvector, smul_mulVec, one_mulVec, ← sub_smul, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
    exact Matrix.isUnit_det_of_right_inverse hinv
  rw [show z • (1 : Matrix ι ι ℂ) - X = -(X - z • 1) by rw [neg_sub], inv_neg_of_isUnit_det hu,
    inv_sub_eq_specSum hX hz, specSum_neg]

/-- `|[(z'-X)⁻¹(z-X)⁻¹]_{aa}| ≤ (Im z' Im z)⁻¹` for Hermitian `X`, `Im z, Im z' > 0`. -/
theorem norm_inv_mul_inv_apply_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) (a : ι) :
    ‖((z' • (1 : Matrix ι ι ℂ) - X)⁻¹ * (z • 1 - X)⁻¹) a a‖ ≤ (z'.im * z.im)⁻¹ := by
  rw [inv_smul_one_sub_eq_specSum hX hz'.ne', inv_smul_one_sub_eq_specSum hX hz.ne',
    specSum_mul_specSum]
  refine norm_specSum_apply_self_le hX (fun l => ?_) a
  have h1 : ∀ w : ℂ, 0 < w.im → ‖-(((l : ℝ) : ℂ) - w)⁻¹‖ ≤ w.im⁻¹ := by
    intro w hw
    rw [norm_neg, norm_inv]
    refine inv_anti₀ hw ?_
    have := Complex.abs_im_le_norm (((l : ℝ) : ℂ) - w)
    have him : (((l : ℝ) : ℂ) - w).im = -w.im := by simp
    rw [him, abs_neg, abs_of_pos hw] at this
    exact this
  rw [norm_mul, mul_inv]
  exact mul_le_mul (h1 z' hz') (h1 z hz) (norm_nonneg _) (inv_nonneg.2 hz'.le)

/-!
## Stability of `d(X)` in the energy
-/

theorem isUnit_det_smul_one_sub {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im) : IsUnit (z • (1 : Matrix ι ι ℂ) - X).det := by
  have h := BlockBand.Critical.Collar.Density.isUnit_det_sub_smul_one' hX hz
  have hu : IsUnit (X - z • (1 : Matrix ι ι ℂ)) := (Matrix.isUnit_iff_isUnit_det _).2 h
  rw [show z • (1 : Matrix ι ι ℂ) - X = -(X - z • 1) by rw [neg_sub]]
  exact (Matrix.isUnit_iff_isUnit_det _).1 hu.neg

theorem norm_blockTrace_le {k W : ℕ} (hW : 0 < W) {M : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ}
    {B : ℝ} (hM : ∀ a, ‖M a a‖ ≤ B) (j : Fin k) : ‖blockTrace M j‖ ≤ B := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  unfold blockTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖∑ a : Fin W, M (j, a) (j, a)‖ ≤ (W : ℝ)⁻¹ * ∑ _a : Fin W, B := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hM _)
    _ = B := by simp; field_simp

/-- **Energy stability of `d(X)`** (Hermitian `X`, no norm bound):
`d_{E'}(X) ≤ d_E(X) + ‖z_b(E)-z_b(E')‖ (Im z_b(E') Im z_b(E))⁻¹ + ‖a(E') - a(E)‖`. -/
theorem matchedDistance_le_energy {b E E' : ℝ} {W : ℕ} (hW : 0 < W)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (hη : 0 < (boundaryZ b E).im) (hη' : 0 < (boundaryZ b E').im) :
    matchedDistance b E' X ≤ matchedDistance b E X +
      ‖boundaryZ b E - boundaryZ b E'‖ * ((boundaryZ b E').im * (boundaryZ b E).im)⁻¹ +
        ‖matchedA E' - matchedA E‖ := by
  set z := boundaryZ b E
  set z' := boundaryZ b E'
  set R := (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹
  set R' := (z' • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹
  have hu := isUnit_det_smul_one_sub hX hη
  have hu' := isUnit_det_smul_one_sub hX hη'
  have hdiff : R' - R = (z - z') • (R' * R) := by
    have h1 : (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X) * R = 1 :=
      mul_nonsing_inv _ hu
    have h2 : R' * (z' • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X) = 1 :=
      nonsing_inv_mul _ hu'
    calc R' - R = R' * ((z • 1 - X) * R) - (R' * (z' • 1 - X)) * R := by
          rw [h1, h2, mul_one, one_mul]
      _ = R' * ((z • 1 - X) - (z' • 1 - X)) * R := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (z - z') • (R' * R) := by
          rw [show (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X) - (z' • 1 - X) =
            (z - z') • 1 by rw [sub_smul]; abel, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hbt : ∀ j : Fin 2, ‖blockTrace R' j - blockTrace R j‖ ≤
      ‖z - z'‖ * (z'.im * z.im)⁻¹ := by
    intro j
    have hlin : blockTrace R' j - blockTrace R j = (z - z') * blockTrace (R' * R) j := by
      have : blockTrace (R' - R) j = blockTrace R' j - blockTrace R j := by
        simp only [blockTrace, Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]
      rw [← this, hdiff]
      simp only [blockTrace, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring
    rw [hlin, norm_mul]
    gcongr
    exact norm_blockTrace_le hW (fun a => norm_inv_mul_inv_apply_le hX hη hη' a) j
  have hd : ∀ j : Fin 2, ‖blockTrace R j - matchedA E‖ ≤ matchedDistance b E X := by
    intro j
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have key : ∀ j : Fin 2, ‖blockTrace R' j - matchedA E'‖ ≤ matchedDistance b E X +
      ‖z - z'‖ * (z'.im * z.im)⁻¹ + ‖matchedA E' - matchedA E‖ := by
    intro j
    calc ‖blockTrace R' j - matchedA E'‖
        = ‖(blockTrace R j - matchedA E) + (blockTrace R' j - blockTrace R j) -
            (matchedA E' - matchedA E)‖ := by congr 1; ring
      _ ≤ ‖blockTrace R j - matchedA E‖ + ‖blockTrace R' j - blockTrace R j‖ +
            ‖matchedA E' - matchedA E‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ _ := by gcongr <;> [exact hd j; exact hbt j]
  exact max_le (key 0) (key 1)

end BlockBand.Critical.Collar.Density
