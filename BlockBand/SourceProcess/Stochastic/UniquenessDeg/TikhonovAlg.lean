module
public import BlockBand.SourceProcess.Stochastic.Representation.PseudoInverse
public import BlockBand.SourceProcess.Stochastic.Levy.Penrose
public import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Regularized drivers for a degenerate covariance: matrix algebra

For a square matrix `s` (`d × d`) and `ε > 0`, with `G = sᵀ s + ε`:
* `tikX s ε : Fin d → Fin d ⊕ Fin (d + d) → ℝ` is the matrix `[P_ε s | √(2ε) P_ε | ε G⁻¹]`;
  **`tikX_orth`**: its rows are orthonormal (`(P s)(P s)ᵀ + 2ε P Pᵀ + ε² G⁻² = 1`), which makes
  `∫ P_ε dM + ∫ [√(2ε) P_ε | ε G⁻¹] dB'` a Brownian motion.
* `pinvX s = [s⁺ s | 0 | 1 - s⁺ s]`; `pinvX_orth`, and `s · pinvX s = [s | 0 | 0]`
  (`mul_pinvX_inl`, `mul_pinvX_inr`): the limit has orthonormal rows and reproduces `s`.
* **`tendsto_tikX`**: `tikX s ε_n → pinvX s` entrywise along `ε_n = regSeq n → 0`.
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open Matrix Filter Topology
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Levy

variable {d : ℕ}

/-- The regularized driver matrix `[P_ε s | √(2ε) P_ε | ε G⁻¹]`. -/
def tikX (s : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (k : Fin d) : Fin d ⊕ Fin (d + d) → ℝ :=
  Sum.elim (fun m => (tikhonov s ε * s) k m)
    (fun l => Fin.addCases (fun l₁ => Real.sqrt (2 * ε) * tikhonov s ε k l₁)
      (fun l₂ => ε * (gramReg s ε)⁻¹ k l₂) l)

/-- The limit `[s⁺ s | 0 | 1 - s⁺ s]`. -/
def pinvX (s : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) : Fin d ⊕ Fin (d + d) → ℝ :=
  Sum.elim (fun m => (pinv s * s) k m)
    (fun l => Fin.addCases (fun _ => 0) (fun l₂ => (1 - pinv s * s) k l₂) l)

theorem gramReg_transpose (s : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) :
    (gramReg s ε)ᵀ = gramReg s ε := by
  simp [gramReg, transpose_add, transpose_mul, transpose_smul]

theorem tikhonov_matrix_orth (s : Matrix (Fin d) (Fin d) ℝ) {ε : ℝ} (hε : 0 < ε) :
    tikhonov s ε * s * (tikhonov s ε * s)ᵀ + (2 * ε) • (tikhonov s ε * (tikhonov s ε)ᵀ) +
      (ε ^ 2) • ((gramReg s ε)⁻¹ * ((gramReg s ε)⁻¹)ᵀ) = 1 := by
  set G := gramReg s ε
  set Gi := G⁻¹
  set S := sᵀ * s
  have hGi : Gi * G = 1 := nonsing_inv_mul G (isUnit_det_gramReg s hε)
  have hGi' : G * Gi = 1 := mul_nonsing_inv G (isUnit_det_gramReg s hε)
  have hGiT : Giᵀ = Gi := by rw [transpose_nonsing_inv, gramReg_transpose]
  have hST : Sᵀ = S := by simp [S, transpose_mul]
  have hGG : G * G = S * S + (2 * ε) • S + (ε ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    simp only [G, gramReg, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul, S]
    rw [two_mul, add_smul, sq]
    abel
  have hP : tikhonov s ε = Gi * sᵀ := rfl
  have e1 : tikhonov s ε * s * (tikhonov s ε * s)ᵀ = Gi * S * S * Gi := by
    rw [hP, Matrix.mul_assoc Gi, transpose_mul, hST, hGiT]
    simp only [Matrix.mul_assoc, S]
  have e2 : tikhonov s ε * (tikhonov s ε)ᵀ = Gi * S * Gi := by
    rw [hP, transpose_mul, transpose_transpose, hGiT]
    simp only [Matrix.mul_assoc, S]
  rw [e1, e2, hGiT]
  have e3 : Gi * S * S * Gi + (2 * ε) • (Gi * S * Gi) + (ε ^ 2) • (Gi * Gi) =
      Gi * (G * G) * Gi := by
    rw [hGG]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  rw [e3]
  calc Gi * (G * G) * Gi = (Gi * G) * (G * Gi) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hGi, hGi', Matrix.one_mul]

theorem mul_transpose_apply {n p : ℕ} (A B : Matrix (Fin n) (Fin p) ℝ) (k l : Fin n) :
    (A * Bᵀ) k l = ∑ j, A k j * B l j := by
  rw [Matrix.mul_apply]; rfl

/-- **Orthonormal rows of the regularized driver.** -/
theorem tikX_orth (s : Matrix (Fin d) (Fin d) ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Fin d) :
    ∑ c, tikX s ε k c * tikX s ε l c = if k = l then 1 else 0 := by
  have h := congrFun (congrFun (tikhonov_matrix_orth s hε) k) l
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    mul_transpose_apply, mul_transpose_apply, mul_transpose_apply, smul_eq_mul, smul_eq_mul,
    Matrix.one_apply] at h
  rw [← h, Fintype.sum_sum_type, Fin.sum_univ_add]
  simp only [tikX, Sum.elim_inl, Sum.elim_inr, Fin.addCases_left, Fin.addCases_right]
  have h2 : Real.sqrt (2 * ε) * Real.sqrt (2 * ε) = 2 * ε := Real.mul_self_sqrt (by positivity)
  rw [add_assoc, Finset.mul_sum, Finset.mul_sum]
  congr 2
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show Real.sqrt (2 * ε) * tikhonov s ε k j * (Real.sqrt (2 * ε) * tikhonov s ε l j) =
      (Real.sqrt (2 * ε) * Real.sqrt (2 * ε)) * (tikhonov s ε k j * tikhonov s ε l j) by ring, h2]
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem pinvX_orth (s : Matrix (Fin d) (Fin d) ℝ) (k l : Fin d) :
    ∑ c, pinvX s k c * pinvX s l c = if k = l then 1 else 0 := by
  have hP := isMoorePenrose_pinv s
  have h := hP.bracket_identity
  have e1 : pinv s * (s * sᵀ) * (pinv s)ᵀ = pinv s * s * (pinv s * s)ᵀ := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [e1] at h
  have h' := congrFun (congrFun h k) l
  rw [Matrix.add_apply, mul_transpose_apply, mul_transpose_apply, Matrix.one_apply] at h'
  rw [← h', Fintype.sum_sum_type, Fin.sum_univ_add]
  simp only [pinvX, Sum.elim_inl, Sum.elim_inr, Fin.addCases_left, Fin.addCases_right,
    mul_zero, Finset.sum_const_zero, zero_add]

theorem mul_pinvX_inl (s : Matrix (Fin d) (Fin d) ℝ) (i m : Fin d) :
    ∑ k, s i k * pinvX s k (Sum.inl m) = s i m := by
  have h := congrFun (congrFun (isMoorePenrose_pinv s).left i) m
  simp only [pinvX, Sum.elim_inl]
  rw [← h, Matrix.mul_assoc, Matrix.mul_apply]

theorem mul_pinvX_inr (s : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (l : Fin (d + d)) :
    ∑ k, s i k * pinvX s k (Sum.inr l) = 0 := by
  have h := congrFun (congrFun (isMoorePenrose_pinv s).sigma_mul_compl i)
  revert l
  refine Fin.addCases (fun l₁ => ?_) (fun l₂ => ?_)
  · simp [pinvX]
  · have := h l₂
    rw [Matrix.mul_apply, Matrix.zero_apply] at this
    simp only [pinvX, Sum.elim_inr, Fin.addCases_right]
    exact this

/-- **Convergence of the regularized drivers** along `ε_n = regSeq n`. -/
theorem tendsto_tikX (s : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) (c : Fin d ⊕ Fin (d + d)) :
    Tendsto (fun n => tikX s (regSeq n) k c) atTop (𝓝 (pinvX s k c)) := by
  have hT := tendsto_tikhonov s
  have hcont : Continuous fun A : Matrix (Fin d) (Fin d) ℝ => A * s :=
    continuous_id.matrix_mul continuous_const
  rcases c with m | l
  · exact ((continuous_apply m).comp (continuous_apply k) |>.tendsto _).comp
      ((hcont.tendsto _).comp hT)
  · revert l
    refine Fin.addCases (fun l₁ => ?_) (fun l₂ => ?_)
    · simp only [tikX, pinvX, Sum.elim_inr, Fin.addCases_left]
      have h0 : Tendsto (fun n => Real.sqrt (2 * regSeq n)) atTop (𝓝 0) := by
        have h := (Real.continuous_sqrt.tendsto (2 * 0)).comp (tendsto_regSeq.const_mul 2)
        simpa [Function.comp_def] using h
      have h1 : Tendsto (fun n => tikhonov s (regSeq n) k l₁) atTop (𝓝 (pinv s k l₁)) :=
        ((continuous_id.matrix_elem k l₁).tendsto _).comp hT
      simpa using h0.mul h1
    · simp only [tikX, pinvX, Sum.elim_inr, Fin.addCases_right]
      have e : ∀ n, regSeq n * (gramReg s (regSeq n))⁻¹ k l₂ =
          (1 - tikhonov s (regSeq n) * s) k l₂ := fun n => by
        have h := inv_gramReg_mul s (regSeq_pos n)
        have h2 : tikhonov s (regSeq n) * s = (gramReg s (regSeq n))⁻¹ * (sᵀ * s) := by
          rw [tikhonov, Matrix.mul_assoc]
        rw [h2, h]
        simp
      simp_rw [e]
      have hc2 : Continuous fun A : Matrix (Fin d) (Fin d) ℝ => (1 - A * s) k l₂ :=
        (continuous_apply l₂).comp ((continuous_apply k).comp (continuous_const.sub hcont))
      exact (hc2.tendsto _).comp hT

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
