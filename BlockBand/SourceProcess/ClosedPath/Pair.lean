module

public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# The canonical two-projection pair frame from far eigenvectors

Pure algebra on a finite space `ι` with two orthogonal projections: `P` (near inputs) and
`Q = P' = 𝕊ᴴP𝕊` (inputs leaving at the near end). The far input eigenvectors of the retained
modes are the columns of `F : Matrix ι (Fin K) ℂ`, already **masked** (column `k` is `0` unless
mode `k` is retained):

* `PF = 0` (far vectors), `FᴴF = D_m` (orthonormal retained columns, `D_m` the 0/1 mask),
* `(1 - P)QF = F D_t` (eigenvectors of the far compression `T_far` of `Q`, eigenvalues `t_k`).

The **phase is fixed through the far eigenvector**: the near partner of
`f_k` is `n_k = P Q f_k / √(t_k(1-t_k))` (`nearPartners`), whose overlap `⟨n_k, Q f_k⟩` is then
real positive. The pair frame `Φ` (`pairFrame`) has columns `(k,0) ↦ n_k`, `(k,1) ↦ f_k`.

This module defines these frames and proves the algebraic identities behind them
(`curFrame_apply`, `nearPartners_conj_mul_far`, `far_conj_Q_far`, `far_conj_QcQ_far`). The sibling
module `PairGram` proves `ΦᴴΦ = D_m ⊗ 1` and `ΦᴴPΦ = (D_m ⊗ 1)·modeProjection` (`pairFrame_gram`,
`pairFrame_nearGram`), hence for the current frame `V = Φ V₀` with `V₀ = initialFrame`
(columns `t_k^{1/4}(e_±(t_k)_0 n_k + e_±(t_k)_1 f_k)`):

`gramPair P (Φ V₀) = initialGram K π t h` (**`gramPair_curFrame`**) — exactly, not in law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedPath

open Matrix
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}

/-- The retained mask `1_{h² < t_k}` (the condition of `initialFrame`). -/
def retainMask (K : ℕ) (t : ℕ → ℝ) (h : ℝ) (k : Fin K) : ℂ := if h ^ 2 < t k.val then 1 else 0

/-- `D_m = diag(1_{h² < t_k})`. -/
def maskDiag (K : ℕ) (t : ℕ → ℝ) (h : ℝ) : Matrix (Fin K) (Fin K) ℂ := diagonal (retainMask K t h)

/-- `D_t = diag(t_k)`. -/
def tDiag (K : ℕ) (t : ℕ → ℝ) : Matrix (Fin K) (Fin K) ℂ := diagonal fun k => ((t k.val : ℝ) : ℂ)

/-- `D_x⁻¹ = diag(1/√(t_k(1-t_k)))`. -/
def xInvDiag (K : ℕ) (t : ℕ → ℝ) : Matrix (Fin K) (Fin K) ℂ :=
  diagonal fun k => (((Real.sqrt (t k.val * (1 - t k.val)))⁻¹ : ℝ) : ℂ)

/-- The near partners `n_k = P Q f_k / √(t_k(1-t_k))`. -/
def nearPartners (P Q : Matrix ι ι ℂ) (F : Matrix ι (Fin K) ℂ) (t : ℕ → ℝ) : Matrix ι (Fin K) ℂ :=
  P * Q * F * xInvDiag K t

/-- Near partner block (`σ = 0`) or far block (`σ = 1`). -/
def pairBlock (P Q : Matrix ι ι ℂ) (F : Matrix ι (Fin K) ℂ) (t : ℕ → ℝ) (σ : Fin 2) :
    Matrix ι (Fin K) ℂ :=
  if σ = 0 then nearPartners P Q F t else F

/-- **The canonical pair frame** `Φ`: column `(k,0)` is `n_k`, column `(k,1)` is `f_k`. -/
def pairFrame (P Q : Matrix ι ι ℂ) (F : Matrix ι (Fin K) ℂ) (t : ℕ → ℝ) :
    Matrix ι (Fin K × Fin 2) ℂ :=
  Matrix.of fun x c => pairBlock P Q F t c.2 x c.1

/-- **The current frame at time `s`**: `Φ V₀`, `V₀ = initialFrame` (probe columns zero). -/
def curFrame (P Q : Matrix ι ι ℂ) (F : Matrix ι (Fin K) ℂ) (π : Type*) (t : ℕ → ℝ) (h : ℝ) :
    Matrix ι (SrcCol K π) ℂ :=
  pairFrame P Q F t * initialFrame K π t h

omit [DecidableEq ι] in
theorem pairFrame_conj_mul (P Q M : Matrix ι ι ℂ) (F : Matrix ι (Fin K) ℂ) (t : ℕ → ℝ)
    (c d : Fin K × Fin 2) :
    ((pairFrame P Q F t)ᴴ * M * pairFrame P Q F t) c d =
      ((pairBlock P Q F t c.2)ᴴ * M * pairBlock P Q F t d.2) c.1 d.1 := by
  simp only [mul_apply, conjTranspose_apply, pairFrame, of_apply]

omit [DecidableEq ι] in
/-- The two-mode column formula: `(Φ V₀)_{(k,σ)} = t_k^{1/4}(e_σ(t_k)_0 n_k + e_σ(t_k)_1 f_k)`
for retained `k`, and `0` otherwise. -/
theorem curFrame_apply (P Q : Matrix ι ι ℂ) (F : Matrix ι (Fin K) ℂ) (π : Type*) (t : ℕ → ℝ)
    (h : ℝ) (x : ι) (k : Fin K) (σ : Fin 2) :
    curFrame P Q F π t h x (Sum.inl (k, σ)) = if h ^ 2 < t k.val then
      ((t k.val ^ (1 / 4 : ℝ) : ℝ) : ℂ) * (modeVector (t k.val) σ 0 * nearPartners P Q F t x k +
        modeVector (t k.val) σ 1 * F x k) else 0 := by
  simp only [curFrame, mul_apply, initialFrame, pairFrame, of_apply, Fintype.sum_prod_type]
  by_cases hk : h ^ 2 < t k.val
  · simp only [hk, ↓reduceIte]
    rw [Finset.sum_eq_single k]
    · simp [Fin.sum_univ_two, pairBlock]; ring
    · intro j _ hj; simp [hj]
    · simp
  · simp [hk]

variable {P Q : Matrix ι ι ℂ} {F : Matrix ι (Fin K) ℂ} {t : ℕ → ℝ} {h : ℝ}

theorem conjTranspose_tDiag : (tDiag K t)ᴴ = tDiag K t := by
  simp [tDiag, diagonal_conjTranspose, Pi.star_def]

theorem conjTranspose_xInvDiag : (xInvDiag K t)ᴴ = xInvDiag K t := by
  simp [xInvDiag, diagonal_conjTranspose, Pi.star_def]

omit [DecidableEq ι] in
/-- `n_kᴴ f_l = 0`. -/
theorem nearPartners_conj_mul_far (hPH : Pᴴ = P) (hQH : Qᴴ = Q) (hPF : P * F = 0) :
    (nearPartners P Q F t)ᴴ * F = 0 := by
  rw [nearPartners, conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, hPH, hQH,
    conjTranspose_xInvDiag]
  simp only [Matrix.mul_assoc, hPF, Matrix.mul_zero]

/-- `FᴴQF = D_m D_t`. -/
theorem far_conj_Q_far (hPH : Pᴴ = P) (hPF : P * F = 0) (hFF : Fᴴ * F = maskDiag K t h)
    (hQF : (1 - P) * Q * F = F * tDiag K t) : Fᴴ * Q * F = maskDiag K t h * tDiag K t := by
  have hFP : Fᴴ * P = 0 := by rw [← hPH, ← conjTranspose_mul, hPF, conjTranspose_zero]
  have e : Fᴴ * ((1 - P) * Q * F) = (Fᴴ - Fᴴ * P) * Q * F := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
  rw [hFP, sub_zero] at e
  rw [← e, hQF, ← Matrix.mul_assoc, hFF]

/-- `FᴴQ(1-P)QF = D_t D_m D_t`. -/
theorem far_conj_QcQ_far (hPH : Pᴴ = P) (hPP : P * P = P) (hQH : Qᴴ = Q)
    (hFF : Fᴴ * F = maskDiag K t h) (hQF : (1 - P) * Q * F = F * tDiag K t) :
    Fᴴ * Q * (1 - P) * Q * F = tDiag K t * maskDiag K t h * tDiag K t := by
  have hc : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]; simp
  have e : Fᴴ * Q * (1 - P) * Q * F = ((1 - P) * Q * F)ᴴ * ((1 - P) * Q * F) := by
    rw [conjTranspose_mul, conjTranspose_mul, hQH, conjTranspose_sub, conjTranspose_one, hPH]
    calc Fᴴ * Q * (1 - P) * Q * F = Fᴴ * Q * ((1 - P) * (1 - P)) * Q * F := by rw [hc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, hQF, conjTranspose_mul, conjTranspose_tDiag, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ,
    hFF, Matrix.mul_assoc]

end BlockBand.SourceProcess.ClosedPath
