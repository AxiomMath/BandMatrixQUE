module

public import BlockBand.Adapters.CEH.MDEUniqueness

/-!
# Operator-norm and trace estimates for the eigenstate thermalization input

Elementary bounds on entries, normalized traces, Frobenius norms and resolvents of
`N × N` complex matrices, used with the external eigenstate thermalization theorem.

* `norm_entry_le`, `norm_normalizedTrace_le`: `|A_ij| ≤ ‖A‖`, `|⟨A⟩| ≤ ‖A‖`.
* `frobSq_mul_le`: `‖AB‖_F² ≤ ‖A‖² ‖B‖_F²`.
* `normalizedTrace_imaginaryPart`, `norm_imaginaryPart_le`, `normSq_normalizedTrace_le`.
* `ward_trace`: `Im tr M = Im w · ‖M‖_F²` when `(F - w)M = 1`.
* `resolvent_near`: Neumann bound, `(F - w)⁻¹` is a right inverse with `‖(F - w)⁻¹‖ ≤ 2K`
  once `(F - w_b) M_b = 1`, `‖M_b‖ ≤ K`, `|w - w_b| K ≤ 1/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.CEH

open Matrix
open BlockBand.External
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {N : ℕ}

/-- `Σ_i |(Ax)_i|² ≤ ‖A‖² Σ_i |x_i|²` (operator norm). -/
theorem sumsq_mulVec_le (A : CEH.SourceMatrix N) (x : Fin N → ℂ) :
    ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
  have h0 : 0 ≤ ∑ i, ‖x i‖ ^ 2 := by positivity
  have h1 : 0 ≤ ∑ i, ‖(A *ᵥ x) i‖ ^ 2 := by positivity
  simp at h
  have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt h1, mul_pow, Real.sq_sqrt h0] at this
  exact this

/-- Entries are bounded by the operator norm. -/
theorem norm_entry_le (A : CEH.SourceMatrix N) (i j : Fin N) : ‖A i j‖ ≤ ‖A‖ := by
  have h := sumsq_mulVec_le A (Pi.single j 1)
  have hcol : A *ᵥ Pi.single j 1 = fun k => A k j := by
    funext k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hone : ∑ k, ‖(Pi.single j (1 : ℂ) : Fin N → ℂ) k‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [hcol, hone, mul_one] at h
  have hle : ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 :=
    (Finset.single_le_sum (f := fun k => ‖A k j‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)).trans h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle

/-- `‖1‖ ≤ 1` for the operator norm (equality for `N > 0`). -/
theorem norm_one_le : ‖(1 : CEH.SourceMatrix N)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : (1 : CEH.SourceMatrix 0) = 0 := Subsingleton.elim _ _
    simp [this]
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    simp

/-- `|⟨A⟩| ≤ ‖A‖`. -/
theorem norm_normalizedTrace_le (A : CEH.SourceMatrix N) :
    ‖CEH.normalizedTrace A‖ ≤ ‖A‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [CEH.normalizedTrace]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have htr : ‖A.trace‖ ≤ N * ‖A‖ := by
    simp only [Matrix.trace, Matrix.diag]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖A i i‖ ≤ ∑ _i : Fin N, ‖A‖ := Finset.sum_le_sum fun i _ => norm_entry_le A i i
      _ = N * ‖A‖ := by simp
  rw [CEH.normalizedTrace, norm_mul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_le_iff₀ hNpos]
  exact htr

/-- `‖AB‖_F² ≤ ‖A‖² ‖B‖_F²`. -/
theorem frobSq_mul_le (A B : CEH.SourceMatrix N) : frobSq (A * B) ≤ ‖A‖ ^ 2 * frobSq B := by
  have hcol : ∀ i j, (A * B) i j = (A *ᵥ fun k => B k j) i := by
    intro i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold frobSq
  simp_rw [hcol]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖B i j‖ ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => sumsq_mulVec_le A _

/-- `⟨Im A⟩ = Im⟨A⟩`. -/
theorem normalizedTrace_imaginaryPart (A : CEH.SourceMatrix N) :
    CEH.normalizedTrace (CEH.imaginaryPart A) = ((CEH.normalizedTrace A).im : ℂ) := by
  unfold CEH.normalizedTrace CEH.imaginaryPart
  rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, smul_eq_mul,
    RCLike.star_def, inv_two_I_mul_sub_conj]
  have : ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.im_ofReal_mul]
  push_cast
  ring

/-- `‖Im A‖ ≤ ‖A‖`. -/
theorem norm_imaginaryPart_le (A : CEH.SourceMatrix N) : ‖CEH.imaginaryPart A‖ ≤ ‖A‖ := by
  unfold CEH.imaginaryPart
  refine (norm_smul_le _ _).trans ?_
  have h2 : ‖(2 * Complex.I)⁻¹‖ = 1 / 2 := by simp
  rw [h2]
  have := norm_sub_le A Aᴴ
  rw [Matrix.l2_opNorm_conjTranspose] at this
  linarith

/-- `frobSq 1 = N`. -/
theorem frobSq_one : frobSq (1 : CEH.SourceMatrix N) = N := by
  unfold frobSq
  have : ∀ i : Fin N, ∑ j, ‖(1 : CEH.SourceMatrix N) i j‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb])
      (by simp)]
    simp
  simp [this]

/-- Cauchy–Schwarz: `|⟨A⟩|² ≤ N⁻¹ ‖A‖_F² = ⟨AA*⟩`. -/
theorem normSq_normalizedTrace_le (A : CEH.SourceMatrix N) :
    ‖CEH.normalizedTrace A‖ ^ 2 ≤ (N : ℝ)⁻¹ * frobSq A := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [CEH.normalizedTrace]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcs := norm_trace_mul_sq_le A 1
  rw [Matrix.mul_one, frobSq_one] at hcs
  rw [CEH.normalizedTrace, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  calc (N : ℝ)⁻¹ ^ 2 * ‖A.trace‖ ^ 2 ≤ (N : ℝ)⁻¹ ^ 2 * (frobSq A * N) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = (N : ℝ)⁻¹ * frobSq A := by field_simp

/-- Traced Ward identity: `(F - w)M = 1`, `F` Hermitian ⇒ `Im tr M = Im w · ‖M‖_F²`. -/
theorem ward_trace (F : CEH.SourceHermitian N) {w : ℂ} {M : CEH.SourceMatrix N}
    (h : (F.1 - w • (1 : CEH.SourceMatrix N)) * M = 1) :
    (M.trace).im = w.im * frobSq M := by
  have hward := congrArg Matrix.trace (ward_identity F h)
  rw [Matrix.trace_sub, Matrix.trace_conjTranspose, Matrix.trace_smul,
    trace_mul_conjTranspose_self, smul_eq_mul] at hward
  have := congrArg Complex.im hward
  simp at this
  linarith

/-- `⟨MM*⟩ = N⁻¹ ‖M‖_F²` as a complex number. -/
theorem normalizedTrace_mul_conjTranspose (M : CEH.SourceMatrix N) :
    CEH.normalizedTrace (M * Mᴴ) = (((N : ℝ)⁻¹ * frobSq M : ℝ) : ℂ) := by
  rw [CEH.normalizedTrace, trace_mul_conjTranspose_self]
  push_cast
  rfl

/-- Neumann bound. If `(F - w_b) M_b = 1`, `‖M_b‖ ≤ K` and `|w - w_b| K ≤ 1/2`, then the
matrix inverse `(F - w)⁻¹` is a right inverse of `F - w` and `‖(F - w)⁻¹‖ ≤ 2K`. -/
theorem resolvent_near (F : CEH.SourceHermitian N) {wb w : ℂ} {Mb : CEH.SourceMatrix N}
    {K : ℝ} (hb : (F.1 - wb • (1 : CEH.SourceMatrix N)) * Mb = 1) (hK : ‖Mb‖ ≤ K)
    (hw : ‖w - wb‖ * K ≤ 1 / 2) :
    (F.1 - w • (1 : CEH.SourceMatrix N)) * (F.1 - w • (1 : CEH.SourceMatrix N))⁻¹ = 1 ∧
      ‖(F.1 - w • (1 : CEH.SourceMatrix N))⁻¹‖ ≤ 2 * K := by
  set y : CEH.SourceMatrix N := (w - wb) • Mb with hy
  have hy2 : ‖y‖ ≤ 1 / 2 :=
    (norm_smul_le _ _).trans ((mul_le_mul_of_nonneg_left hK (norm_nonneg _)).trans hw)
  have hy1 : ‖y‖ < 1 := by linarith
  set U := Units.oneSub y hy1 with hU
  have hUv : (U : CEH.SourceMatrix N) = 1 - y := rfl
  set V : CEH.SourceMatrix N := ((U⁻¹ : (CEH.SourceMatrix N)ˣ) : CEH.SourceMatrix N) with hV
  have hUV : (1 - y) * V = 1 := by
    rw [← hUv, hV]
    exact U.mul_inv
  have hfac : F.1 - w • (1 : CEH.SourceMatrix N) =
      (F.1 - wb • (1 : CEH.SourceMatrix N)) * (1 - y) := by
    rw [hy, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hb]
    module
  have hR : (F.1 - w • (1 : CEH.SourceMatrix N)) * (V * Mb) = 1 := by
    rw [hfac, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - y), hUV, Matrix.one_mul, hb]
  have hinv := Matrix.inv_eq_right_inv hR
  refine ⟨by rw [hinv]; exact hR, ?_⟩
  rw [hinv]
  have hVeq : V = 1 + y * V := by
    have : V - y * V = 1 := by rw [← hUV, Matrix.sub_mul, Matrix.one_mul]
    rw [← this]; abel
  have hVn : ‖V‖ ≤ 2 := by
    have h1 : ‖V‖ ≤ 1 + 1 / 2 * ‖V‖ := by
      calc ‖V‖ = ‖1 + y * V‖ := by rw [← hVeq]
        _ ≤ ‖(1 : CEH.SourceMatrix N)‖ + ‖y‖ * ‖V‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
        _ ≤ 1 + 1 / 2 * ‖V‖ :=
          add_le_add norm_one_le (mul_le_mul_of_nonneg_right hy2 (norm_nonneg _))
    linarith
  calc ‖V * Mb‖ ≤ ‖V‖ * ‖Mb‖ := norm_mul_le _ _
    _ ≤ 2 * K := mul_le_mul hVn hK (norm_nonneg _) (by norm_num)

/-- Distance to the base point: under the hypotheses of `resolvent_near`,
`(F - w)⁻¹ - M_b = (w - w_b)(F - w)⁻¹ M_b` and `‖(F - w)⁻¹ - M_b‖ ≤ 2K² |w - w_b|`. -/
theorem resolvent_near_sub (F : CEH.SourceHermitian N) {wb w : ℂ} {Mb : CEH.SourceMatrix N}
    {K : ℝ} (hb : (F.1 - wb • (1 : CEH.SourceMatrix N)) * Mb = 1) (hK : ‖Mb‖ ≤ K)
    (hw : ‖w - wb‖ * K ≤ 1 / 2) :
    ‖(F.1 - w • (1 : CEH.SourceMatrix N))⁻¹ - Mb‖ ≤ 2 * K ^ 2 * ‖w - wb‖ := by
  obtain ⟨hR, hRn⟩ := resolvent_near F hb hK hw
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  rw [resolvent_identity F hR hb]
  calc ‖(w - wb) • ((F.1 - w • (1 : CEH.SourceMatrix N))⁻¹ * Mb)‖
      ≤ ‖w - wb‖ * (‖(F.1 - w • (1 : CEH.SourceMatrix N))⁻¹‖ * ‖Mb‖) :=
        (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖w - wb‖ * (2 * K * K) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hRn hK (norm_nonneg _) (by linarith))
          (norm_nonneg _)
    _ = 2 * K ^ 2 * ‖w - wb‖ := by ring

end BlockBand.Adapters.CEH
