module

public import BlockBand.Adapters.CEH.GUEWigner

/-!
# Identification of the matrix Dyson equation branch

The matrix Dyson equation (MDE) `(F - z - s⟨M⟩) M = 1` is identified with the branch.

* Existence of a branch with `λ = √s`: the cited `CEH.SourceContract` field
  `mde_exists` at the family `gueWignerFamily`.
* Every branch solves the MDE: `(√s)² = s`.
* Pointwise uniqueness of solutions of the MDE at every nonreal `z` (no input): with
  `w = z + s⟨M⟩` the Ward identity `M - M* = (w - w̄) M M*` gives
  `Im⟨M⟩ = Im w · ⟨MM*⟩`, and `Im z · Im⟨M⟩ ≥ 0` forces `s⟨MM*⟩ < 1`. For two solutions the
  resolvent identity gives `⟨M₁⟩ - ⟨M₂⟩ = s(⟨M₁⟩ - ⟨M₂⟩)⟨M₁M₂⟩`, while Cauchy–Schwarz gives
  `|s⟨M₁M₂⟩|² ≤ s⟨M₁M₁*⟩ · s⟨M₂M₂*⟩ < 1`; hence `⟨M₁⟩ = ⟨M₂⟩` and `M₁ = M₂`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.CEH

open Matrix
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexOrder ComplexConjugate

variable {N : ℕ}

/-- Unnormalized squared Frobenius norm `Σ_{ij} |M_ij|²`. -/
def frobSq (M : CEH.SourceMatrix N) : ℝ := ∑ i, ∑ j, ‖M i j‖ ^ 2

/-- The squared Frobenius norm is nonnegative. -/
theorem frobSq_nonneg (M : CEH.SourceMatrix N) : 0 ≤ frobSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- `tr(M M*) = Σ_{ij} |M_ij|²`. -/
theorem trace_mul_conjTranspose_self (M : CEH.SourceMatrix N) :
    (M * Mᴴ).trace = ((frobSq M : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, frobSq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- Cauchy–Schwarz for `tr(M₁M₂)`. -/
theorem norm_trace_mul_sq_le (M₁ M₂ : CEH.SourceMatrix N) :
    ‖(M₁ * M₂).trace‖ ^ 2 ≤ frobSq M₁ * frobSq M₂ := by
  have h1 : ‖(M₁ * M₂).trace‖ ≤ ∑ i, ∑ j, ‖M₁ i j‖ * ‖M₂ j i‖ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  have h2 : (∑ i, ∑ j, ‖M₁ i j‖ * ‖M₂ j i‖) ^ 2 ≤ frobSq M₁ * frobSq M₂ := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N × Fin N))
      (fun p => ‖M₁ p.1 p.2‖) (fun p => ‖M₂ p.2 p.1‖)
    rw [Fintype.sum_prod_type' (fun i j => ‖M₁ i j‖ * ‖M₂ j i‖),
      Fintype.sum_prod_type' (fun i j => ‖M₁ i j‖ ^ 2),
      Fintype.sum_prod_type' (fun i j => ‖M₂ j i‖ ^ 2)] at hcs
    have e : ∑ i, ∑ j, ‖M₂ j i‖ ^ 2 = frobSq M₂ := Finset.sum_comm
    rw [e] at hcs
    exact hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- Left inverse ⇒ right inverse, for square matrices. -/
theorem mul_eq_one_symm {A B : CEH.SourceMatrix N} (h : A * B = 1) : B * A = 1 :=
  (mul_eq_one_comm_of_card_eq (Fin N) (Fin N) ℂ rfl).mp h

/-- Ward identity: `M - M* = (w - w̄) M M*` when `(F - w) M = 1`, `F` Hermitian. -/
theorem ward_identity (F : CEH.SourceHermitian N) {w : ℂ} {M : CEH.SourceMatrix N}
    (h : (F.1 - w • (1 : CEH.SourceMatrix N)) * M = 1) :
    M - Mᴴ = (w - conj w) • (M * Mᴴ) := by
  have h1 : M * (F.1 - w • (1 : CEH.SourceMatrix N)) = 1 := mul_eq_one_symm h
  have h2 : (F.1 - conj w • (1 : CEH.SourceMatrix N)) * Mᴴ = 1 := by
    have := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, F.2.eq] at this
    exact this
  calc M - Mᴴ = M * ((F.1 - conj w • (1 : CEH.SourceMatrix N)) * Mᴴ) -
        (M * (F.1 - w • (1 : CEH.SourceMatrix N))) * Mᴴ := by rw [h1, h2, Matrix.mul_one,
          Matrix.one_mul]
    _ = (w - conj w) • (M * Mᴴ) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      module

/-- Resolvent identity: `M₁ - M₂ = (w₁ - w₂) M₁ M₂`. -/
theorem resolvent_identity (F : CEH.SourceHermitian N) {w₁ w₂ : ℂ}
    {M₁ M₂ : CEH.SourceMatrix N}
    (h₁ : (F.1 - w₁ • (1 : CEH.SourceMatrix N)) * M₁ = 1)
    (h₂ : (F.1 - w₂ • (1 : CEH.SourceMatrix N)) * M₂ = 1) :
    M₁ - M₂ = (w₁ - w₂) • (M₁ * M₂) := by
  have h1 : M₁ * (F.1 - w₁ • (1 : CEH.SourceMatrix N)) = 1 := mul_eq_one_symm h₁
  calc M₁ - M₂ = M₁ * ((F.1 - w₂ • (1 : CEH.SourceMatrix N)) * M₂) -
        (M₁ * (F.1 - w₁ • (1 : CEH.SourceMatrix N))) * M₂ := by rw [h1, h₂, Matrix.mul_one,
          Matrix.one_mul]
    _ = (w₁ - w₂) • (M₁ * M₂) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      module

/-- `(t - t̄)/(2i) = Im t`. -/
theorem inv_two_I_mul_sub_conj (t : ℂ) : (2 * Complex.I)⁻¹ * (t - conj t) = (t.im : ℂ) := by
  rw [Complex.sub_conj]
  push_cast
  field_simp

/-- Contraction bound: a solution of the MDE with `s ≥ 0` has `s ⟨M M*⟩ < 1`. -/
theorem mde_contraction {s : ℝ} (hs : 0 ≤ s) (F : CEH.SourceHermitian N) {z : ℂ}
    (hz : z.im ≠ 0) {M : CEH.SourceMatrix N} (h : IsManuscriptMDE s F z M) :
    s * ((N : ℝ)⁻¹ * frobSq M) < 1 := by
  obtain ⟨hinv, hpos⟩ := h
  set w := z + (s : ℂ) * CEH.normalizedTrace M with hw
  -- Ward identity, traced: `Im tr M = Im w · ‖M‖_F²`.
  have hward := congrArg Matrix.trace (ward_identity F hinv)
  rw [Matrix.trace_sub, Matrix.trace_conjTranspose, Matrix.trace_smul,
    trace_mul_conjTranspose_self, smul_eq_mul] at hward
  have hT : (M.trace).im = w.im * frobSq M := by
    have := congrArg Complex.im hward
    simp at this
    linarith
  -- Positivity: `Im z · Im tr M ≥ 0`.
  have htr := hpos.posSemidef.trace_nonneg
  rw [Matrix.trace_smul, CEH.imaginaryPart, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_conjTranspose, RCLike.star_def, smul_eq_mul, smul_eq_mul,
    inv_two_I_mul_sub_conj, ← Complex.ofReal_mul, Complex.zero_le_real] at htr
  -- Scalars.
  have hNinv : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hwim : w.im = z.im + s * ((N : ℝ)⁻¹ * (M.trace).im) := by
    simp [hw, CEH.normalizedTrace]
  have hrel : z.im = w.im * (1 - s * ((N : ℝ)⁻¹ * frobSq M)) := by
    linear_combination (-1 : ℝ) * hwim - s * (N : ℝ)⁻¹ * hT
  have hyv : z.im ^ 2 ≤ z.im * w.im := by
    rw [hwim]
    nlinarith [mul_nonneg (mul_nonneg hs hNinv) htr]
  have hy2 : 0 < z.im ^ 2 := by positivity
  by_contra hge
  have hge' := not_lt.mp hge
  have hprod : z.im * w.im = w.im ^ 2 * (1 - s * ((N : ℝ)⁻¹ * frobSq M)) := by
    rw [hrel]
    ring
  nlinarith [sq_nonneg w.im]

/-- Pointwise uniqueness for the MDE: for Hermitian `F` on `ℂ^N`
(any `N`), `s ≥ 0` and nonreal `z` (either half-plane), two matrices solving
`(F - z - s⟨M⟩) M = 1` with `Im z · Im M ≻ 0` coincide. No input is used. -/
theorem isManuscriptMDE_unique {s : ℝ} (hs : 0 ≤ s) (F : CEH.SourceHermitian N) {z : ℂ}
    (hz : z.im ≠ 0) {M₁ M₂ : CEH.SourceMatrix N}
    (h₁ : IsManuscriptMDE s F z M₁) (h₂ : IsManuscriptMDE s F z M₂) : M₁ = M₂ := by
  have hc₁ := mde_contraction hs F hz h₁
  have hc₂ := mde_contraction hs F hz h₂
  obtain ⟨hinv₁, -⟩ := h₁
  obtain ⟨hinv₂, -⟩ := h₂
  have hres := resolvent_identity F hinv₁ hinv₂
  have htr : CEH.normalizedTrace M₁ - CEH.normalizedTrace M₂ =
      (s : ℂ) * (CEH.normalizedTrace M₁ - CEH.normalizedTrace M₂) *
        CEH.normalizedTrace (M₁ * M₂) := by
    have := congrArg CEH.normalizedTrace hres
    unfold CEH.normalizedTrace at this ⊢
    rw [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at this
    linear_combination this
  have hm : CEH.normalizedTrace M₁ = CEH.normalizedTrace M₂ := by
    by_contra hne
    have hk : (s : ℂ) * CEH.normalizedTrace (M₁ * M₂) = 1 := by
      have hne' : CEH.normalizedTrace M₁ - CEH.normalizedTrace M₂ ≠ 0 := sub_ne_zero.mpr hne
      have h0 : (CEH.normalizedTrace M₁ - CEH.normalizedTrace M₂) *
          (1 - (s : ℂ) * CEH.normalizedTrace (M₁ * M₂)) = 0 := by
        linear_combination htr
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hne'
      · linear_combination -h
    have hn : s * (N : ℝ)⁻¹ * ‖(M₁ * M₂).trace‖ = 1 := by
      have := congrArg norm hk
      simpa [CEH.normalizedTrace, norm_mul, abs_of_nonneg hs, mul_assoc] using this
    have hcs := norm_trace_mul_sq_le M₁ M₂
    have hNinv : 0 ≤ (N : ℝ)⁻¹ := by positivity
    have h1 : 1 ≤ (s * (N : ℝ)⁻¹) ^ 2 * (frobSq M₁ * frobSq M₂) :=
      calc (1 : ℝ) = (s * (N : ℝ)⁻¹ * ‖(M₁ * M₂).trace‖) ^ 2 := by rw [hn]; norm_num
        _ = (s * (N : ℝ)⁻¹) ^ 2 * ‖(M₁ * M₂).trace‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    have ha₁ : 0 ≤ s * ((N : ℝ)⁻¹ * frobSq M₁) :=
      mul_nonneg hs (mul_nonneg hNinv (frobSq_nonneg _))
    have ha₂ : 0 ≤ s * ((N : ℝ)⁻¹ * frobSq M₂) :=
      mul_nonneg hs (mul_nonneg hNinv (frobSq_nonneg _))
    have he : (s * (N : ℝ)⁻¹) ^ 2 * (frobSq M₁ * frobSq M₂) =
        (s * ((N : ℝ)⁻¹ * frobSq M₁)) * (s * ((N : ℝ)⁻¹ * frobSq M₂)) := by ring
    nlinarith [mul_le_mul hc₁.le hc₂.le ha₂ zero_le_one, mul_lt_mul_of_pos_right hc₁ one_pos]
  rw [hm] at hinv₁
  have hl := mul_eq_one_symm hinv₁
  calc M₁ = M₁ * ((F.1 - (z + (s : ℂ) * CEH.normalizedTrace M₂) •
        (1 : CEH.SourceMatrix N)) * M₂) := by rw [hinv₂, Matrix.mul_one]
    _ = (M₁ * (F.1 - (z + (s : ℂ) * CEH.normalizedTrace M₂) •
        (1 : CEH.SourceMatrix N))) * M₂ := (Matrix.mul_assoc _ _ _).symm
    _ = M₂ := by rw [hl, Matrix.one_mul]

/-- `MDEBranchIdentification` from `CEH.SourceContract` for every Wigner family: for `N > 0`,
`s > 0` and Hermitian `F`, (i) a branch `CEH.MDEBranch (√s) F` exists (the field `mde_exists`
at `gueWignerFamily`), (ii) every such branch solves the MDE at every nonreal `z` (since
`(√s)² = s`), and (iii) the MDE has at most one solution at each nonreal `z`
(`isManuscriptMDE_unique`). -/
theorem mdeBranchIdentification_holds
    (hceh : ∀ W : CEH.WignerFamily, CEH.SourceContract W) : MDEBranchIdentification := by
  intro N hN s hs F
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  refine ⟨(hceh gueWignerFamily).mde_exists N hN _ hsq F, fun M z hz => ?_,
    fun z hz M₁ M₂ h₁ h₂ => isManuscriptMDE_unique hs.le F hz h₁ h₂⟩
  have hsol := M.solution z hz
  have hsq2 : ((Real.sqrt s : ℝ) : ℂ) ^ 2 = (s : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]
  refine ⟨?_, hsol.halfPlane_positive⟩
  have := hsol.inverse_equation
  rw [hsq2] at this
  exact this

end BlockBand.Adapters.CEH
