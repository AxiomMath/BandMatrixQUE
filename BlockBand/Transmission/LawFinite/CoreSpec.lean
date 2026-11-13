module

public import BlockBand.Transmission.LawFinite.DriftForcing
public import BlockBand.Transmission.LawFinite.All

/-!
# Spectral cuts of a Hermitian matrix (bare functional calculus)

No probability, no hypothesis. For the deterministic step `0 → 1` of `FiniteCoreEntrance` we use
Mathlib's `IsHermitian.cfc f = U diag(f(λ)) U*` with possibly discontinuous `f` (the spectral cut
`1_{λ < c}` and the truncated inverse `λ⁻¹1_{λ ≥ c}`):

* `cfc_mul_cfc`, `cfc_id'`, `cfc_const`, `cfc_sub`, `cfc_conjTranspose`: algebra;
* `norm_cfc_le`: `‖cfc f‖ ≤ C` when `|f(λ_i)| ≤ C`;
* `re_trace_cutLow_mul_le`: `Re Tr(1_{<c}(H)·M) ≤ #{i : λ_i < c}·‖M‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

section Spec

variable {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian)

/-- The diagonal of `f(λ)`. -/
abbrev cfcDiag (f : ℝ → ℝ) : Matrix n n ℂ := diagonal fun i => ((f (hH.eigenvalues i) : ℝ) : ℂ)

theorem cfc_def (f : ℝ → ℝ) :
    hH.cfc f = (hH.eigenvectorUnitary : Matrix n n ℂ) * cfcDiag hH f *
      star (hH.eigenvectorUnitary : Matrix n n ℂ) := by
  simp only [IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

theorem eigU_mem : (hH.eigenvectorUnitary : Matrix n n ℂ) ∈ unitary (Matrix n n ℂ) :=
  hH.eigenvectorUnitary.2

theorem cfc_mul_cfc (f g : ℝ → ℝ) : hH.cfc f * hH.cfc g = hH.cfc (fun x => f x * g x) := by
  rw [cfc_def, cfc_def, cfc_def]
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (eigU_mem hH)
  calc U * cfcDiag hH f * star U * (U * cfcDiag hH g * star U)
      = U * cfcDiag hH f * (star U * U) * cfcDiag hH g * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
        congr 3; funext i; push_cast; ring

theorem cfc_id' : hH.cfc (fun x => x) = H := by
  conv_rhs => rw [hH.spectral_theorem]
  rfl

theorem cfc_const (c : ℝ) : hH.cfc (fun _ => c) = (c : ℂ) • 1 := by
  rw [cfc_def]
  have : cfcDiag hH (fun _ : ℝ => c) = (c : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j; simp [cfcDiag, diagonal, Matrix.one_apply]
  rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Unitary.mul_star_self_of_mem (eigU_mem hH)]

theorem cfc_sub (f g : ℝ → ℝ) : hH.cfc (fun x => f x - g x) = hH.cfc f - hH.cfc g := by
  rw [cfc_def, cfc_def, cfc_def]
  have : cfcDiag hH (fun x => f x - g x) = cfcDiag hH f - cfcDiag hH g := by
    ext i j; simp only [cfcDiag, diagonal, Matrix.of_apply, Matrix.sub_apply]
    split_ifs <;> push_cast <;> ring
  rw [this, Matrix.mul_sub, Matrix.sub_mul]

theorem cfc_conjTranspose (f : ℝ → ℝ) : (hH.cfc f)ᴴ = hH.cfc f := by
  have : (cfcDiag hH f)ᴴ = cfcDiag hH f := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp
  rw [cfc_def, conjTranspose_mul, conjTranspose_mul, this, star_eq_conjTranspose,
    conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem norm_cfc_le (f : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i, |f (hH.eigenvalues i)| ≤ C) :
    ‖hH.cfc f‖ ≤ C := by
  rw [cfc_def, Matrix.mul_assoc, CStarRing.norm_mem_unitary_mul _ (eigU_mem hH),
    CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (eigU_mem hH)), l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg hC).2 fun i => ?_
  simpa [Complex.norm_real] using hf i

/-- `Re Tr(cfc 1_{<c} · M) ≤ #{i : λ_i < c}·‖M‖`. -/
theorem re_trace_cutLow_mul_le (c : ℝ) (M : Matrix n n ℂ) :
    (hH.cfc (fun x => if x < c then 1 else 0) * M).trace.re ≤
      ((Finset.univ.filter fun i => hH.eigenvalues i < c).card : ℝ) * ‖M‖ := by
  rw [cfc_def]
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  set D := cfcDiag hH (fun x : ℝ => if x < c then (1 : ℝ) else 0)
  have htr : (U * D * star U * M).trace = (D * (star U * M * U)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]
  have hN : ‖star U * M * U‖ = ‖M‖ := by
    rw [CStarRing.norm_mul_mem_unitary _ (eigU_mem hH),
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem (eigU_mem hH))]
  rw [htr]
  have hdiag : (D * (star U * M * U)).trace = ∑ i, (if hH.eigenvalues i < c then (1 : ℂ) else 0) *
      (star U * M * U) i i := by
    simp only [D, cfcDiag, Matrix.trace, Matrix.diag, diagonal_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [hdiag, Complex.re_sum]
  calc ∑ i, ((if hH.eigenvalues i < c then (1 : ℂ) else 0) * (star U * M * U) i i).re
      ≤ ∑ i, (if hH.eigenvalues i < c then ‖M‖ else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · rw [one_mul, ← hN]
          exact (Complex.re_le_norm _).trans (PassiveCovariance.norm_entry_le' _ _ _)
        · simp
    _ = _ := by rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]

end Spec

end BlockBand.Transmission.LawFinite
