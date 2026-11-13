module

public import BlockBand.Transmission.PathScalar.Dissipative

/-!
# The dissipative row bound for a non-normal passive resolvent

For `R = K⁻¹` with `Im K = Y + η`, `Y ⪰ 0`, `η > 0` (e.g. `K = z - 𝕏`, `-Im 𝕏 = Y`):
* `negIm_inv_eq`: `-Im R = R(Im K)R* = R*(Im K)R`;
* `row_col_le`: `η Σ_q |R_pq|² ≤ -Im R_pp` and `η Σ_q |R_qp|² ≤ -Im R_pp`;
* `sum_norm_pairTrace_le`: on blocks `Fin k × Fin W`,
  `Σ_j |W⁻¹ Tr R_ij R_ji| ≤ -Im(W⁻¹ Tr R_ii)/η` (the local bound of the strict contraction).

With one block (`k = 1`) the row bound is the Herglotz derivative bound
`|∂_z W⁻¹Tr(z-X)⁻¹| = |W⁻¹Tr R²| ≤ -Im(W⁻¹Tr R)/Im z` used by the passive mean step.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open Matrix BlockBand.Transmission
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem negIm_inv_eq (K : Matrix ι ι ℂ) (hK1 : K * K⁻¹ = 1) (hK2 : K⁻¹ * K = 1) :
    -matrixImaginaryPart (K⁻¹) = K⁻¹ * matrixImaginaryPart K * (K⁻¹)ᴴ ∧
      -matrixImaginaryPart (K⁻¹) = (K⁻¹)ᴴ * matrixImaginaryPart K * K⁻¹ := by
  have h1 : Kᴴ * (K⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, hK2, conjTranspose_one]
  have h2 : (K⁻¹)ᴴ * Kᴴ = 1 := by rw [← conjTranspose_mul, hK1, conjTranspose_one]
  constructor
  · simp only [matrixImaginaryPart, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul]
    rw [hK2, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one, ← smul_neg, neg_sub]
  · simp only [matrixImaginaryPart, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul]
    rw [Matrix.mul_assoc (K⁻¹ᴴ) K, hK1, Matrix.mul_one, h2, Matrix.one_mul, ← smul_neg, neg_sub]

omit [Fintype ι] [DecidableEq ι] in
theorem diag_negIm (M : Matrix ι ι ℂ) (p : ι) :
    (-matrixImaginaryPart M) p p = ((-(M p p).im : ℝ) : ℂ) := by
  simp only [matrixImaginaryPart, Matrix.neg_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, smul_eq_mul]
  apply Complex.ext
  · simp; ring
  · simp

/-- Row and column bounds: `η Σ_q |R_pq|² ≤ -Im R_pp`, `η Σ_q |R_qp|² ≤ -Im R_pp`. -/
theorem row_col_le (K Y : Matrix ι ι ℂ) {η : ℝ} (hη : 0 < η) (hY : Y.PosSemidef)
    (him : matrixImaginaryPart K = Y + η • (1 : Matrix ι ι ℂ)) (p : ι) :
    η * ∑ q, ‖K⁻¹ p q‖ ^ 2 ≤ -(K⁻¹ p p).im ∧ η * ∑ q, ‖K⁻¹ q p‖ ^ 2 ≤ -(K⁻¹ p p).im := by
  obtain ⟨-, hK1, hK2⟩ := BlockBand.Transmission.passive_inverse_constructed K Y hη hY him
  obtain ⟨hA, hB⟩ := negIm_inv_eq K hK1 hK2
  set R := K⁻¹
  have hPA := (hY.mul_mul_conjTranspose_same R).diag_nonneg (i := p)
  have hPB := (hY.conjTranspose_mul_mul_same R).diag_nonneg (i := p)
  have eA := congrArg (fun M => (M p p).re) hA
  have eB := congrArg (fun M => (M p p).re) hB
  simp only [diag_negIm, Complex.ofReal_re] at eA eB
  rw [him, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.add_apply, Complex.add_re, Matrix.smul_apply] at eA eB
  have hRR : ((R * Rᴴ) p p) = ((∑ q, ‖R p q‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.ofReal_pow, ← Complex.mul_conj']; rfl
  have hRR' : ((Rᴴ * R) p p) = ((∑ q, ‖R q p‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]; rfl
  rw [Complex.nonneg_iff] at hPA hPB
  constructor
  · rw [hRR, Complex.smul_re, Complex.ofReal_re, smul_eq_mul] at eA; linarith [hPA.1]
  · rw [hRR', Complex.smul_re, Complex.ofReal_re, smul_eq_mul] at eB; linarith [hPB.1]

theorem cs_sqrt {κ : Type*} (s : Finset κ) (f g : κ → ℝ) :
    ∑ i ∈ s, f i * g i ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le (Finset.sum_mul_sq_le_sq_mul_sq s f g)

open BlockBand.Internal.Contracts.Layers in
/-- **The dissipative row bound**: for `R = K⁻¹`, `Im K = Y + η`, `Y ⪰ 0`,
`Σ_j |W⁻¹ Tr R_ij R_ji| ≤ -Im(W⁻¹ Tr R_ii)/η`. -/
theorem sum_norm_pairTrace_le {k W : ℕ} (K Y : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) {η : ℝ}
    (hη : 0 < η) (hY : Y.PosSemidef)
    (him : matrixImaginaryPart K = Y + η • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ))
    (i : Fin k) :
    ∑ j, ‖(W : ℂ)⁻¹ * ∑ x, ∑ y, K⁻¹ (i, x) (j, y) * K⁻¹ (j, y) (i, x)‖ ≤
      -(blockTrace K⁻¹ i).im / η := by
  set R := K⁻¹
  set r : Fin k → ℝ := fun j => ∑ x, ∑ y, ‖R (i, x) (j, y)‖ ^ 2
  set c : Fin k → ℝ := fun j => ∑ x, ∑ y, ‖R (j, y) (i, x)‖ ^ 2
  set m : ℝ := ∑ x, -(R (i, x) (i, x)).im
  have hr0 : ∀ j, 0 ≤ r j := fun j => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc0 : ∀ j, 0 ≤ c j := fun j => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrow : η * ∑ j, r j ≤ m := by
    have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => (row_col_le K Y hη hY him (i, x)).1
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum] at this
    simp only [r, m]; rw [Finset.sum_comm]; linarith
  have hcol : η * ∑ j, c j ≤ m := by
    have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => (row_col_le K Y hη hY him (i, x)).2
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum] at this
    simp only [c, m]; rw [Finset.sum_comm]; linarith
  have hpair : ∀ j, ‖∑ x, ∑ y, R (i, x) (j, y) * R (j, y) (i, x)‖ ≤
      Real.sqrt (r j) * Real.sqrt (c j) := by
    intro j
    calc ‖∑ x, ∑ y, R (i, x) (j, y) * R (j, y) (i, x)‖
        ≤ ∑ x, ∑ y, ‖R (i, x) (j, y)‖ * ‖R (j, y) (i, x)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ =>
            (norm_sum_le _ _).trans (le_of_eq (by simp)))
      _ = ∑ q : Fin W × Fin W, ‖R (i, q.1) (j, q.2)‖ * ‖R (j, q.2) (i, q.1)‖ := by
          rw [Fintype.sum_prod_type]
      _ ≤ Real.sqrt (∑ q : Fin W × Fin W, ‖R (i, q.1) (j, q.2)‖ ^ 2) *
            Real.sqrt (∑ q : Fin W × Fin W, ‖R (j, q.2) (i, q.1)‖ ^ 2) :=
          cs_sqrt _ _ _
      _ = Real.sqrt (r j) * Real.sqrt (c j) := by
          simp only [r, c, Fintype.sum_prod_type]
  have hsum : ∑ j, Real.sqrt (r j) * Real.sqrt (c j) ≤ m / η := by
    refine (cs_sqrt _ _ _).trans ?_
    simp only [Real.sq_sqrt (hr0 _), Real.sq_sqrt (hc0 _)]
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => hr0 j)]
    have hm : 0 ≤ m / η := by
      have := mul_nonneg hη.le (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hr0 j)
      exact div_nonneg (by linarith) hη.le
    rw [Real.sqrt_le_left hm]
    have h1 : ∑ j, r j ≤ m / η := by rw [le_div_iff₀ hη]; linarith
    have h2 : ∑ j, c j ≤ m / η := by rw [le_div_iff₀ hη]; linarith
    calc (∑ j, r j) * ∑ j, c j ≤ (m / η) * (m / η) :=
          mul_le_mul h1 h2 (Finset.sum_nonneg fun j _ => hc0 j) hm
      _ = (m / η) ^ 2 := by ring
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp [blockTrace]
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hbt : -(blockTrace R i).im = (W : ℝ)⁻¹ * m := by
    simp only [blockTrace, m, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.natCast_re,
      Complex.natCast_im, Complex.im_sum, Complex.re_sum, Finset.sum_neg_distrib]
    simp
  rw [hbt]
  calc ∑ j, ‖(W : ℂ)⁻¹ * ∑ x, ∑ y, R (i, x) (j, y) * R (j, y) (i, x)‖
      = (W : ℝ)⁻¹ * ∑ j, ‖∑ x, ∑ y, R (i, x) (j, y) * R (j, y) (i, x)‖ := by
        rw [Finset.mul_sum]; congr 1; funext j
        rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (W : ℝ)⁻¹ * (m / η) := by
        gcongr; exact (Finset.sum_le_sum fun j _ => hpair j).trans hsum
    _ = (W : ℝ)⁻¹ * m / η := by ring

open BlockBand.Internal.Contracts.Layers in

/-- **The two-port dissipative row bound**: for a passive two-port `𝕏` (`-Im 𝕏 ⪰ 0`) and
`Im z > 0`, `R = (z - 𝕏)⁻¹`, `Σ_j |Q_ij| ≤ -Im(W⁻¹Tr R_ii)/Im z`. -/
theorem sum_norm_blockPairTrace_le {W : ℕ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {z : ℂ} (hz : 0 < z.im) (hY : (-matrixImaginaryPart XX).PosSemidef) (i : Fin 2) :
    ∑ j, ‖blockPairTrace ((z • 1 - XX)⁻¹) i j‖ ≤ -(blockTrace (z • 1 - XX)⁻¹ i).im / z.im := by
  have him : matrixImaginaryPart (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - XX) =
      -matrixImaginaryPart XX + z.im • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) := by
    have h := matrixImaginaryPart_portPencil_general XX z
    rw [portPencil] at h
    rw [h]; abel
  exact sum_norm_pairTrace_le _ _ hz hY him i

end BlockBand.Transmission.PathScalar
