module

public import BlockBand.SourceProcess.ClosedPath.PairGram

/-!
# The pair frame diagonalizes `P' - P` blockwise

Under the hypotheses of `pairFrame` (orthogonal projections `P, Q`, masked far eigenvector
columns `F`), with `x_k = √(t_k(1-t_k))`:

* `far_mul_mask`: `FᴴF = D_m ⇒ F D_m = F` (non-retained columns vanish);
* `mask_xInv_x`: `D_m D_x⁻¹ D_x = D_m`;
* **`sub_mul_far`**: `(Q - P) f_k = x_k n_k + t_k f_k`, i.e. `(Q - P)F = N D_x + F D_t`.

Not formalized here: the companion `(Q - P) n_k = -t_k n_k + x_k f_k` and the `2 × 2` eigen
equation of `modeVector` (which together say that the columns of `Φ V₀` are `t_k^{1/4}` times
unit eigenvectors of `P' - P` with eigenvalues `±√t_k`). `modeBlock` and `pairBlockMat` record
the block `[[-t, x], [x, t]]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedPath

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}
variable {P Q : Matrix ι ι ℂ} {F : Matrix ι (Fin K) ℂ} {t : ℕ → ℝ} {h : ℝ}

/-- `D_x = diag(√(t_k(1-t_k)))`. -/
def xDiag (K : ℕ) (t : ℕ → ℝ) : Matrix (Fin K) (Fin K) ℂ :=
  diagonal fun k => ((Real.sqrt (t k.val * (1 - t k.val)) : ℝ) : ℂ)

/-- The `2 × 2` block `[[-t, x], [x, t]]` of mode `t`. -/
def modeBlock (t : ℝ) (τ σ : Fin 2) : ℂ :=
  if τ = σ then (if τ = 0 then -(t : ℂ) else (t : ℂ)) else ((Real.sqrt (t * (1 - t)) : ℝ) : ℂ)

/-- `B = ⊕_k [[-t_k, x_k], [x_k, t_k]]` on the mode space. -/
def pairBlockMat (K : ℕ) (t : ℕ → ℝ) : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  Matrix.of fun c d => if c.1 = d.1 then modeBlock (t d.1.val) c.2 d.2 else 0

omit [DecidableEq ι] in
theorem far_mul_mask (hFF : Fᴴ * F = maskDiag K t h) : F * maskDiag K t h = F := by
  have hmm : maskDiag K t h * maskDiag K t h = maskDiag K t h := by
    simp only [maskDiag, diagonal_mul_diagonal]
    congr 1; funext k; simp only [retainMask]; split_ifs <;> simp
  have hmH : (maskDiag K t h)ᴴ = maskDiag K t h := by
    simp only [maskDiag, diagonal_conjTranspose]
    congr 1; funext k; simp only [retainMask, Pi.star_apply]; split_ifs <;> simp
  have h0 : (F - F * maskDiag K t h)ᴴ * (F - F * maskDiag K t h) = 0 := by
    calc (F - F * maskDiag K t h)ᴴ * (F - F * maskDiag K t h)
        = Fᴴ * F - Fᴴ * F * maskDiag K t h - maskDiag K t h * (Fᴴ * F) +
            maskDiag K t h * (Fᴴ * F) * maskDiag K t h := by
          rw [conjTranspose_sub, conjTranspose_mul, hmH]
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]; abel
      _ = 0 := by rw [hFF, hmm, hmm]; abel
  have := (Matrix.conjTranspose_mul_self_eq_zero).1 h0
  rw [sub_eq_zero] at this; exact this.symm

/-- Diagonal arithmetic on retained modes. -/
theorem mask_diag_eq (ht : ∀ k : Fin K, h ^ 2 < t k.val → 0 < t k.val ∧ t k.val < 1)
    (f g : ℝ → ℂ) (hfg : ∀ u : ℝ, 0 < u → u < 1 → f u = g u) :
    maskDiag K t h * diagonal (fun k => f (t k.val)) =
      maskDiag K t h * diagonal (fun k => g (t k.val)) := by
  simp only [maskDiag, diagonal_mul_diagonal, retainMask]
  congr 1; funext k
  split_ifs with hk
  · rw [hfg _ (ht k hk).1 (ht k hk).2]
  · simp

/-- `D_x⁻¹ D_x = 1` on retained modes. -/
theorem mask_xInv_x (ht : ∀ k : Fin K, h ^ 2 < t k.val → 0 < t k.val ∧ t k.val < 1) :
    maskDiag K t h * (xInvDiag K t * xDiag K t) = maskDiag K t h := by
  have e := mask_diag_eq ht (fun u => (((Real.sqrt (u * (1 - u)))⁻¹ : ℝ) : ℂ) *
    ((Real.sqrt (u * (1 - u)) : ℝ) : ℂ)) (fun _ => 1) (fun u h0 h1 => by
      have : Real.sqrt (u * (1 - u)) ≠ 0 := (Real.sqrt_pos.2 (mul_pos h0 (by linarith))).ne'
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ this, Complex.ofReal_one])
  simp only [diagonal_one] at e
  rw [xInvDiag, xDiag, diagonal_mul_diagonal, e, Matrix.mul_one]

/-- **`(Q - P) f_k = x_k n_k + t_k f_k`.** -/
theorem sub_mul_far (hPF : P * F = 0) (hFF : Fᴴ * F = maskDiag K t h)
    (hQF : (1 - P) * Q * F = F * tDiag K t)
    (ht : ∀ k : Fin K, h ^ 2 < t k.val → 0 < t k.val ∧ t k.val < 1) :
    (Q - P) * F = nearPartners P Q F t * xDiag K t + F * tDiag K t := by
  have hFm := far_mul_mask hFF
  have hNx : nearPartners P Q F t * xDiag K t = P * Q * F := by
    calc nearPartners P Q F t * xDiag K t = P * Q * F * (xInvDiag K t * xDiag K t) := by
          simp only [nearPartners, Matrix.mul_assoc]
      _ = P * Q * (F * maskDiag K t h) * (xInvDiag K t * xDiag K t) := by rw [hFm]
      _ = P * Q * F * (maskDiag K t h * (xInvDiag K t * xDiag K t)) := by
          simp only [Matrix.mul_assoc]
      _ = P * Q * F := by rw [mask_xInv_x ht, Matrix.mul_assoc (P * Q), hFm]
  have hsplit : Q * F = P * Q * F + (1 - P) * Q * F := by
    simp only [Matrix.sub_mul, Matrix.one_mul]; abel
  rw [Matrix.sub_mul, hPF, sub_zero, hsplit, hQF, hNx]

end BlockBand.SourceProcess.ClosedPath
