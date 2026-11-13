module

public import BlockBand.SourceProcess.ClosingLeak.RankOne

/-!
# Gram differences controlled by column norms

Columns are `Fᵀ k` (`= fun x => F x k`); `l2` is the Euclidean norm `ClosingLeak.l2`.

* `norm_conjTranspose_mul_apply_le`: `|(GᴴH)ᵢₖ| ≤ ‖Gᵢ‖ ‖Hₖ‖` (Cauchy–Schwarz).
* `norm_gram_sub_apply_le`: `|((F+Δ)ᴴ(F+Δ) - FᴴF)ᵢₖ| ≤ ‖Fᵢ‖‖Δₖ‖ + ‖Δᵢ‖‖Fₖ‖ + ‖Δᵢ‖‖Δₖ‖`.
* `l2_mulVec_le_of_proj`, `l2_mulVec_of_unitary`: orthogonal projections contract, unitaries
  preserve `l2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open Matrix BlockBand.SourceProcess.ClosingLeak
open scoped ComplexOrder

variable {ρ c : Type*} [Fintype ρ]

theorem conjTranspose_mul_apply_eq (G H : Matrix ρ c ℂ) (i k : c) :
    (Gᴴ * H) i k = star (Gᵀ i) ⬝ᵥ Hᵀ k := by
  simp [Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply]

/-- `|u*v| ≤ ‖u‖ ‖v‖`. -/
theorem norm_star_dotProduct_le (u v : ρ → ℂ) : ‖star u ⬝ᵥ v‖ ≤ l2 u * l2 v := by
  rw [l2_eq_norm, l2_eq_norm, dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp]
  exact norm_inner_le_norm _ _

/-- **Cauchy–Schwarz for Gram entries**: `|(GᴴH)ᵢₖ| ≤ ‖Gᵢ‖ ‖Hₖ‖`. -/
theorem norm_conjTranspose_mul_apply_le (G H : Matrix ρ c ℂ) (i k : c) :
    ‖(Gᴴ * H) i k‖ ≤ l2 (Gᵀ i) * l2 (Hᵀ k) := by
  rw [conjTranspose_mul_apply_eq]
  exact norm_star_dotProduct_le _ _

/-- **Gram difference**: `|((F+Δ)ᴴ(F+Δ) - FᴴF)ᵢₖ| ≤ ‖Fᵢ‖‖Δₖ‖ + ‖Δᵢ‖‖Fₖ‖ + ‖Δᵢ‖‖Δₖ‖`. -/
theorem norm_gram_sub_apply_le [Fintype c] (F D : Matrix ρ c ℂ) (i k : c) :
    ‖((F + D)ᴴ * (F + D) - Fᴴ * F) i k‖ ≤
      l2 (Fᵀ i) * l2 (Dᵀ k) + l2 (Dᵀ i) * l2 (Fᵀ k) + l2 (Dᵀ i) * l2 (Dᵀ k) := by
  have e : (F + D)ᴴ * (F + D) - Fᴴ * F = Fᴴ * D + Dᴴ * F + Dᴴ * D := by
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  rw [e, Matrix.add_apply, Matrix.add_apply]
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_) <;>
    exact norm_conjTranspose_mul_apply_le _ _ _ _

/-- `star (Mv) ⬝ᵥ (Mv) = star v ⬝ᵥ (MᴴM v)`. -/
theorem star_mulVec_dotProduct {κ : Type*} [Fintype κ] (M : Matrix κ ρ ℂ) (v : ρ → ℂ) :
    star (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = star v ⬝ᵥ ((Mᴴ * M) *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

/-- An orthogonal projection does not increase `l2`. -/
theorem l2_mulVec_le_of_proj [DecidableEq ρ] {B : Matrix ρ ρ ℂ} (hB2 : B * B = B)
    (hBH : Bᴴ = B) (v : ρ → ℂ) : l2 (B *ᵥ v) ≤ l2 v := by
  apply l2_le_of_sq_le
  have h1 : (1 - B)ᴴ * (1 - B) = 1 - B := by
    rw [conjTranspose_sub, conjTranspose_one, hBH, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_sub, Matrix.mul_one, hB2, sub_self, sub_zero]
  have h0 := (Complex.nonneg_iff.1
    (dotProduct_star_self_nonneg (((1 : Matrix ρ ρ ℂ) - B) *ᵥ v))).1
  rw [star_mulVec_dotProduct, h1, sub_mulVec, one_mulVec, dotProduct_sub, Complex.sub_re] at h0
  rw [star_mulVec_dotProduct, hBH, hB2]
  linarith

/-- A unitary preserves `l2`. -/
theorem l2_mulVec_of_unitary [DecidableEq ρ] {S : Matrix ρ ρ ℂ} (hS : Sᴴ * S = 1) (v : ρ → ℂ) :
    l2 (S *ᵥ v) = l2 v := by
  have h : l2 (S *ᵥ v) ^ 2 = l2 v ^ 2 := by
    rw [l2_sq, l2_sq, star_mulVec_dotProduct, hS, one_mulVec]
  exact (pow_left_inj₀ (l2_nonneg _) (l2_nonneg _) two_ne_zero).1 h

end BlockBand.SourceProcess.PhysApprox
