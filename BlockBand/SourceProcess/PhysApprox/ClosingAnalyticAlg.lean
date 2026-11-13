module

public import BlockBand.SourceProcess.ClosingAux.Contraction
public import BlockBand.SourceProcess.Closing.HardyAvg
public import Mathlib.Tactic.NoncommRing

/-!
# The closed Gram identity `C Cᴴ = 1 + Z + Zᴴ` on the unit circle

With `N = Π𝕊A`, `T = Π𝕊(1-A)`, `Q = (1 - zN)⁻¹`, the closing map `C(z) = (1-A) + QzT` and the
closed resolvent factor `Z(z) = zQΠ𝕊`, for an orthogonal projection `A`, `ΠΠᴴ = A`, `𝕊𝕊ᴴ = 1`,
`|z| = 1` and `1 - zN` invertible:

* `closingMap_mul_conj`: `C(z)C(z)ᴴ = 1 + Z(z) + Z(z)ᴴ`.

Proof: `(1-A)Q = 1-A`, `(1-A)X = 0`, `X(1-A) = X` for `X = QzT`, so `CCᴴ = (1-A) + X + Xᴴ + XXᴴ`;
`Z = X + (Q - 1)`; and `XXᴴ = Q(A - NNᴴ)Qᴴ = A + (Q-1) + (Q-1)ᴴ`, since conjugating the right side
by `L = 1 - zN` gives `LALᴴ + (Lᴴ - LLᴴ) + (L - LLᴴ) = A - NNᴴ` (`NA = N`, `ANᴴ = Nᴴ`,
`|z| = 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The closed resolvent factor `Z(z) = z(1 - zN)⁻¹Π𝕊`. -/
def closingZ (S A Pi : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  z • ((1 - z • closingN S A Pi)⁻¹ * (Pi * S))

/-- The scalar-polynomial identity behind `XXᴴ = A + (Q - 1) + (Q - 1)ᴴ`. -/
theorem conj_expand_aux (A N : Matrix ι ι ℂ) (z w : ℂ) (hzw : z * w = 1) (hNA : N * A = N)
    (hAN : A * Nᴴ = Nᴴ) :
    (1 - z • N) * A * (1 - w • Nᴴ) + ((1 - w • Nᴴ) - (1 - z • N) * (1 - w • Nᴴ)) +
      ((1 - z • N) - (1 - z • N) * (1 - w • Nᴴ)) = A - N * Nᴴ := by
  have hwz : w * z = 1 := by rw [mul_comm]; exact hzw
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub, smul_smul, hNA, hAN, hwz, one_smul]
  abel

/-- A ring identity (`L`, `A`, `Q`, `Qh`, `Lh` as free variables). -/
theorem sandwich_expand_aux (L A Q Qh Lh : Matrix ι ι ℂ) :
    L * (A + (Q - 1) + (Qh - 1)) * Lh =
      L * A * Lh + (L * Q * Lh - L * Lh) + (L * Qh * Lh - L * Lh) := by
  noncomm_ring

/-- The abstract form of `closingMap_mul_conj`, with `N`, `T`, `Q` as free variables. -/
theorem closed_gram_abstract {S A Pi N T Q : Matrix ι ι ℂ} {z : ℂ} (hA2 : A * A = A)
    (hAH : Aᴴ = A) (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1) (hz : z * star z = 1)
    (hN : N = Pi * S * A) (hT : T = Pi * S * (1 - A)) (hQL : Q * (1 - z • N) = 1)
    (hLQ : (1 - z • N) * Q = 1) :
    ((1 - A) + Q * (z • T)) * ((1 - A) + Q * (z • T))ᴴ =
      1 + z • (Q * (Pi * S)) + (z • (Q * (Pi * S)))ᴴ := by
  have hAPi : A * Pi = Pi := proj_mul_partialIso hA2 hAH hPi
  have hNA : N * A = N := by
    rw [hN]
    simp only [Matrix.mul_assoc, hA2]
  have hAN : A * N = N := by
    rw [hN]
    simp only [← Matrix.mul_assoc, hAPi]
  have hANh : A * Nᴴ = Nᴴ := by
    have h := congrArg conjTranspose hNA
    rwa [conjTranspose_mul, hAH] at h
  have hTT : T * Tᴴ = A - N * Nᴴ := by
    rw [hT, hN]
    exact closingT_mul_conj hA2 hAH hPi hS
  have h11 : (1 - A) * (1 - A) = 1 - A := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hA2]
    abel
  have h1AH : (1 - A)ᴴ = 1 - A := by rw [conjTranspose_sub, conjTranspose_one, hAH]
  have h1AN : (1 - A) * N = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hAN, sub_self]
  have h1APi : (1 - A) * Pi = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hAPi, sub_self]
  have hQ1 : Q = 1 + z • (N * Q) := by
    have h := hLQ
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul] at h
    rw [← h]
    abel
  have h1AQ : (1 - A) * Q = 1 - A := by
    rw [hQ1, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, h1AN,
      Matrix.zero_mul, smul_zero, add_zero]
  have h1AX : (1 - A) * (Q * (z • T)) = 0 := by
    rw [← Matrix.mul_assoc, h1AQ, Matrix.mul_smul, hT, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      h1APi, Matrix.zero_mul, Matrix.zero_mul, smul_zero]
  have hT1 : T * (1 - A) = T := by
    rw [hT]
    simp only [Matrix.mul_assoc, h11]
  have hX1A : Q * (z • T) * (1 - A) = Q * (z • T) := by
    rw [Matrix.mul_assoc, Matrix.smul_mul, hT1]
  have h1AXh : (1 - A) * (Q * (z • T))ᴴ = (Q * (z • T))ᴴ := by
    have h := congrArg conjTranspose hX1A
    rwa [conjTranspose_mul, h1AH] at h
  have hzT : (z • T) * (z • T)ᴴ = T * Tᴴ := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, one_smul]
  have hXX : Q * (z • T) * (Q * (z • T))ᴴ = Q * (A - N * Nᴴ) * Qᴴ := by
    rw [conjTranspose_mul, ← hTT, ← hzT]
    simp only [Matrix.mul_assoc]
  have hLh : (1 - z • N)ᴴ = 1 - star z • Nᴴ := by
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul]
  have hconj : ∀ M : Matrix ι ι ℂ, M = Q * ((1 - z • N) * M * (1 - z • N)ᴴ) * Qᴴ := by
    intro M
    have hLQh : (1 - z • N)ᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQL, conjTranspose_one]
    have e : Q * ((1 - z • N) * M * (1 - z • N)ᴴ) * Qᴴ =
        (Q * (1 - z • N)) * M * ((1 - z • N)ᴴ * Qᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [e, hQL, hLQh, Matrix.one_mul, Matrix.mul_one]
  have hkey : (1 - z • N) * (A + (Q - 1) + (Qᴴ - 1)) * (1 - z • N)ᴴ = A - N * Nᴴ := by
    have h1 : (1 - z • N) * Q * (1 - z • N)ᴴ = (1 - z • N)ᴴ := by
      rw [hLQ, Matrix.one_mul]
    have h2 : (1 - z • N) * Qᴴ * (1 - z • N)ᴴ = 1 - z • N := by
      rw [Matrix.mul_assoc, ← conjTranspose_mul, hLQ, conjTranspose_one, Matrix.mul_one]
    rw [sandwich_expand_aux, h1, h2, hLh]
    exact conj_expand_aux A N z (star z) hz hNA hANh
  have hXX' : Q * (z • T) * (Q * (z • T))ᴴ = A + (Q - 1) + (Q - 1)ᴴ := by
    rw [hXX, conjTranspose_sub Q 1, conjTranspose_one, ← hkey, ← hconj]
  have hzQN : z • (Q * N) = Q - 1 := by
    have h := hQL
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul] at h
    rw [← h]
    abel
  have hPS : Pi * S = T + N := by
    rw [hT, hN, Matrix.mul_sub, Matrix.mul_one]
    abel
  have hZ : z • (Q * (Pi * S)) = Q * (z • T) + (Q - 1) := by
    rw [hPS, Matrix.mul_add, smul_add, hzQN, Matrix.mul_smul]
  rw [hZ, conjTranspose_add, conjTranspose_add, h1AH, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, h11, h1AXh, hX1A, hXX']
  abel

/-- **`C(z)C(z)ᴴ = 1 + Z(z) + Z(z)ᴴ`** on `|z| = 1`, `1 - zN` invertible. -/
theorem closingMap_mul_conj {S A Pi : Matrix ι ι ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1) {z : ℂ} (hz : z * star z = 1)
    (hU : IsUnit (1 - z • closingN S A Pi).det) :
    closingMap S A Pi z * (closingMap S A Pi z)ᴴ =
      1 + closingZ S A Pi z + (closingZ S A Pi z)ᴴ :=
  closed_gram_abstract hA2 hAH hPi hS hz rfl rfl (nonsing_inv_mul _ hU) (mul_nonsing_inv _ hU)

end BlockBand.SourceProcess.PhysApprox
