module

public import BlockBand.SourceProcess.ClosedPath.Pair

/-!
# The current frame at time `s` has exactly the Gram state `initialGram`

Hypotheses (as for `pairFrame`): `P, Q` orthogonal projections, masked far eigenvector columns
`F` (`PF = 0`, `FᴴF = D_m`, `(1-P)QF = F D_t`), and `0 < t_k < 1` on retained modes.

* `nearPartners_conj_mul_self`: `n_kᴴ n_l = δ_kl` on retained modes (`NᴴN = D_m`), from
  `FᴴQPQF = FᴴQF - FᴴQ(1-P)QF = D_m D_t - D_t D_m D_t`.
* `pairFrame_gram`: `ΦᴴΦ = D_m ⊗ 1`; `pairFrame_nearGram`: `ΦᴴPΦ = (D_m ⊗ 1)·⊕P_i`.
* **`gramPair_curFrame`**: `gramPair P (Φ V₀) = initialGram K π t h`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedPath

open Matrix
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}
variable {P Q : Matrix ι ι ℂ} {F : Matrix ι (Fin K) ℂ} {t : ℕ → ℝ} {h : ℝ}

/-- The mask on the mode space, `(D_m ⊗ 1)_{(k,σ)} = 1_{h² < t_k}`. -/
def maskDiag2 (K : ℕ) (t : ℕ → ℝ) (h : ℝ) : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  diagonal fun c => retainMask K t h c.1

/-- **Near partners are orthonormal**: `NᴴN = D_m`. -/
theorem nearPartners_conj_mul_self (hPH : Pᴴ = P) (hPP : P * P = P) (hQH : Qᴴ = Q)
    (hQQ : Q * Q = Q) (hPF : P * F = 0) (hFF : Fᴴ * F = maskDiag K t h)
    (hQF : (1 - P) * Q * F = F * tDiag K t)
    (ht : ∀ k : Fin K, h ^ 2 < t k.val → 0 < t k.val ∧ t k.val < 1) :
    (nearPartners P Q F t)ᴴ * nearPartners P Q F t = maskDiag K t h := by
  have e1 : Fᴴ * Q * P * Q * F = Fᴴ * Q * F - Fᴴ * Q * (1 - P) * Q * F := by
    have : Fᴴ * Q * (1 - P) * Q * F = Fᴴ * Q * Q * F - Fᴴ * Q * P * Q * F := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [this, Matrix.mul_assoc Fᴴ Q Q, hQQ]; abel
  have e2 : (nearPartners P Q F t)ᴴ * nearPartners P Q F t =
      xInvDiag K t * (Fᴴ * Q * P * Q * F) * xInvDiag K t := by
    rw [nearPartners, conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, hPH, hQH,
      conjTranspose_xInvDiag]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, hPP]
  rw [e2, e1, far_conj_Q_far hPH hPF hFF hQF, far_conj_QcQ_far hPH hPP hQH hFF hQF]
  simp only [xInvDiag, maskDiag, tDiag, diagonal_mul_diagonal, diagonal_sub]
  congr 1; funext k
  unfold retainMask
  split_ifs with hk
  · obtain ⟨h0, h1⟩ := ht k hk
    have hp : 0 < t k.val * (1 - t k.val) := mul_pos h0 (by linarith)
    have hs : Real.sqrt (t k.val * (1 - t k.val)) ^ 2 = t k.val * (1 - t k.val) :=
      Real.sq_sqrt hp.le
    have hne : Real.sqrt (t k.val * (1 - t k.val)) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
    have hne' : ((Real.sqrt (t k.val * (1 - t k.val)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    have hs' : ((Real.sqrt (t k.val * (1 - t k.val)) : ℝ) : ℂ) ^ 2 =
        ((t k.val : ℝ) : ℂ) * (1 - ((t k.val : ℝ) : ℂ)) := by exact_mod_cast hs
    push_cast
    field_simp
    linear_combination -hs'
  · simp

omit [DecidableEq ι] in
theorem nearPartners_P (hPP : P * P = P) : P * nearPartners P Q F t = nearPartners P Q F t := by
  simp only [nearPartners, ← Matrix.mul_assoc, hPP]

/-- **`ΦᴴΦ = D_m ⊗ 1`.** -/
theorem pairFrame_gram (hPH : Pᴴ = P) (hPP : P * P = P) (hQH : Qᴴ = Q)
    (hQQ : Q * Q = Q) (hPF : P * F = 0) (hFF : Fᴴ * F = maskDiag K t h)
    (hQF : (1 - P) * Q * F = F * tDiag K t)
    (ht : ∀ k : Fin K, h ^ 2 < t k.val → 0 < t k.val ∧ t k.val < 1) :
    (pairFrame P Q F t)ᴴ * pairFrame P Q F t = maskDiag2 K t h := by
  have hNN := nearPartners_conj_mul_self hPH hPP hQH hQQ hPF hFF hQF ht
  have hNF := nearPartners_conj_mul_far (t := t) hPH hQH hPF
  have hFN : Fᴴ * nearPartners P Q F t = 0 := by
    have := congrArg conjTranspose hNF
    simpa [conjTranspose_mul] using this
  ext ⟨k, σ⟩ ⟨l, σ'⟩
  have e := pairFrame_conj_mul P Q 1 F t (k, σ) (l, σ')
  rw [Matrix.mul_one, Matrix.mul_one] at e
  rw [e]
  fin_cases σ <;> fin_cases σ' <;>
    simp [pairBlock, hNN, hNF, hFN, hFF, maskDiag, maskDiag2, diagonal_apply]

/-- **`ΦᴴPΦ = (D_m ⊗ 1)·⊕P_i`.** -/
theorem pairFrame_nearGram (hPH : Pᴴ = P) (hPP : P * P = P) (hQH : Qᴴ = Q)
    (hQQ : Q * Q = Q) (hPF : P * F = 0) (hFF : Fᴴ * F = maskDiag K t h)
    (hQF : (1 - P) * Q * F = F * tDiag K t)
    (ht : ∀ k : Fin K, h ^ 2 < t k.val → 0 < t k.val ∧ t k.val < 1) :
    (pairFrame P Q F t)ᴴ * P * pairFrame P Q F t = maskDiag2 K t h * modeProjection K := by
  have hNN := nearPartners_conj_mul_self hPH hPP hQH hQQ hPF hFF hQF ht
  have hPN := nearPartners_P (Q := Q) (F := F) (t := t) hPP
  have hFP : Fᴴ * P = 0 := by rw [← hPH, ← conjTranspose_mul, hPF, conjTranspose_zero]
  have h00 : (nearPartners P Q F t)ᴴ * P * nearPartners P Q F t = maskDiag K t h := by
    rw [Matrix.mul_assoc, hPN, hNN]
  have h01 : (nearPartners P Q F t)ᴴ * P * F = 0 := by rw [Matrix.mul_assoc, hPF, Matrix.mul_zero]
  have h10 : Fᴴ * P * nearPartners P Q F t = 0 := by rw [hFP, Matrix.zero_mul]
  have h11 : Fᴴ * P * F = 0 := by rw [hFP, Matrix.zero_mul]
  ext ⟨k, σ⟩ ⟨l, σ'⟩
  rw [pairFrame_conj_mul]
  fin_cases σ <;> fin_cases σ' <;>
    simp [pairBlock, h00, h01, h10, h11, maskDiag, maskDiag2, modeProjection, diagonal_apply]

omit [DecidableEq ι] in
theorem maskDiag2_mul_initialFrame (π : Type*) :
    maskDiag2 K t h * initialFrame K π t h = initialFrame K π t h := by
  ext ⟨k, σ⟩ c
  rw [maskDiag2, diagonal_mul]
  rcases c with ⟨l, σ'⟩ | i
  · by_cases hk : h ^ 2 < t k.val
    · simp [retainMask, hk]
    · simp only [retainMask, hk, ↓reduceIte, zero_mul, initialFrame]
      split_ifs with hl
      · exact absurd (hl.1 ▸ hl.2) hk
      · rfl
  · simp [initialFrame]

/-- **The current frame at time `s` has Gram state `initialGram`** (exactly). -/
theorem gramPair_curFrame (π : Type*) (hPH : Pᴴ = P) (hPP : P * P = P) (hQH : Qᴴ = Q)
    (hQQ : Q * Q = Q) (hPF : P * F = 0) (hFF : Fᴴ * F = maskDiag K t h)
    (hQF : (1 - P) * Q * F = F * tDiag K t)
    (ht : ∀ k : Fin K, h ^ 2 < t k.val → 0 < t k.val ∧ t k.val < 1) :
    gramPair P (curFrame P Q F π t h) = initialGram K π t h := by
  have hD : (maskDiag2 K t h)ᴴ = maskDiag2 K t h := by
    simp [maskDiag2, diagonal_conjTranspose, Pi.star_def, retainMask, apply_ite]
  have hV := maskDiag2_mul_initialFrame (K := K) (t := t) (h := h) π
  have hV' : (initialFrame K π t h)ᴴ * maskDiag2 K t h = (initialFrame K π t h)ᴴ := by
    conv_rhs => rw [← hV]
    rw [conjTranspose_mul, hD]
  have hcomm : maskDiag2 K t h * modeProjection K = modeProjection K * maskDiag2 K t h := by
    simp only [maskDiag2, modeProjection, diagonal_mul_diagonal, mul_comm]
  simp only [gramPair, initialGram, sourceGram, nearGram, curFrame, conjTranspose_mul]
  refine Prod.ext ?_ ?_
  · calc (initialFrame K π t h)ᴴ * (pairFrame P Q F t)ᴴ * (pairFrame P Q F t * initialFrame K π t h)
        = (initialFrame K π t h)ᴴ * ((pairFrame P Q F t)ᴴ * pairFrame P Q F t) *
            initialFrame K π t h := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [pairFrame_gram hPH hPP hQH hQQ hPF hFF hQF ht, hV']
  · calc (initialFrame K π t h)ᴴ * (pairFrame P Q F t)ᴴ * P *
          (pairFrame P Q F t * initialFrame K π t h)
        = (initialFrame K π t h)ᴴ * ((pairFrame P Q F t)ᴴ * P * pairFrame P Q F t) *
            initialFrame K π t h := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [pairFrame_nearGram hPH hPP hQH hQQ hPF hFF hQF ht, ← Matrix.mul_assoc, hV']

end BlockBand.SourceProcess.ClosedPath
