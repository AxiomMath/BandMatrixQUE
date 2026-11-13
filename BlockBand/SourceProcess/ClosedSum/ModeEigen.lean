module

public import BlockBand.SourceProcess.ClosedPath.PairEigen

/-!
# The current columns are eigenvectors of `P' - P`

This completes `sub_mul_far` (which gives only `(Q - P)F = N D_x + F D_t`). Same generic
hypotheses (`P, Q` orthogonal projections, `PF = 0`, `FᴴF = D_m`, `(1-P)QF = F D_t`, retained
`0 < t_k < 1`), `x_k = √(t_k(1-t_k))`:

* **`sub_mul_near`**: the companion `(Q - P) n_k = -t_k n_k + x_k f_k`, i.e.
  `(Q - P)N = F D_x - N D_t`;
* **`modeBlock_mulVec_modeVector`** (`0 ≤ t ≤ 1`): the `2 × 2` eigen-equation
  `[[-t, x], [x, t]] e_σ(t) = λ_σ e_σ(t)`, `λ_0 = √t`, `λ_1 = -√t`;
* **`sub_mul_curFrame`**: hence every current column of `Φ V₀` is an eigenvector of `P' - P`:
  `(Q - P) V_{(k,σ)} = λ_σ(t_k) V_{(k,σ)}` (and `0` columns stay `0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open Matrix BlockBand.SourceProcess.ClosedPath
open BlockBand.Internal.Contracts.TransmissionLaws

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}
variable {P Q : Matrix ι ι ℂ} {F : Matrix ι (Fin K) ℂ} {t : ℕ → ℝ} {h : ℝ}

/-- **The companion identity** `(Q - P) n_k = -t_k n_k + x_k f_k`. -/
theorem sub_mul_near (hPP : P * P = P) (hQQ : Q * Q = Q) (hFF : Fᴴ * F = maskDiag K t h)
    (hQF : (1 - P) * Q * F = F * tDiag K t)
    (ht : ∀ k : Fin K, h ^ 2 < t k.val → 0 < t k.val ∧ t k.val < 1) :
    (Q - P) * nearPartners P Q F t = F * xDiag K t - nearPartners P Q F t * tDiag K t := by
  set Dt := tDiag K t
  set Di := xInvDiag K t
  have hQF' : Q * F = P * Q * F + F * Dt := by
    rw [← hQF]; simp only [Matrix.sub_mul, Matrix.one_mul]; abel
  have hQPQ : Q * (P * Q * F) = Q * F - Q * F * Dt := by
    have e : Q * (P * Q * F) = Q * Q * F - Q * ((1 - P) * Q * F) := by
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_assoc]; abel
    rw [e, hQQ, hQF, ← Matrix.mul_assoc]
  have hDc : Dt * Di = Di * Dt := by
    simp only [Dt, Di, tDiag, xInvDiag, diagonal_mul_diagonal, mul_comm]
  have hFm := far_mul_mask hFF
  have hdiag : F * ((Dt - Dt * Dt) * Di) = F * xDiag K t := by
    have e := mask_diag_eq ht (fun u => ((u : ℂ) - (u : ℂ) * (u : ℂ)) *
      (((Real.sqrt (u * (1 - u)))⁻¹ : ℝ) : ℂ)) (fun u => ((Real.sqrt (u * (1 - u)) : ℝ) : ℂ))
      (fun u h0 h1 => by
        have hp : 0 < u * (1 - u) := mul_pos h0 (by linarith)
        have hs : Real.sqrt (u * (1 - u)) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
        have hsq := Real.mul_self_sqrt hp.le
        rw [show ((u : ℂ) - (u : ℂ) * (u : ℂ)) = ((u * (1 - u) : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_mul]
        congr 1
        field_simp
        linarith)
    have e1 : (Dt - Dt * Dt) * Di = diagonal (fun k : Fin K => ((t k.val : ℂ) -
        (t k.val : ℂ) * (t k.val : ℂ)) * (((Real.sqrt (t k.val * (1 - t k.val)))⁻¹ : ℝ) : ℂ)) := by
      simp only [Dt, Di, tDiag, xInvDiag, diagonal_mul_diagonal, diagonal_sub]
    rw [e1, ← hFm, Matrix.mul_assoc, e, ← Matrix.mul_assoc, hFm]
    rfl
  calc (Q - P) * nearPartners P Q F t
      = Q * (P * Q * F) * Di - P * P * Q * F * Di := by
        simp only [nearPartners, Matrix.sub_mul, Matrix.mul_assoc]; rfl
    _ = F * ((Dt - Dt * Dt) * Di) - P * Q * F * Di * Dt := by
        rw [hQPQ, hQF', hPP]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_assoc, hDc]
        abel
    _ = _ := by rw [hdiag]; rfl

/-- The eigenvalue `λ_σ(t)`: `+√t` for `σ = 0`, `-√t` for `σ = 1`. -/
def modeEig (t : ℝ) (σ : Fin 2) : ℂ := if σ = 0 then (Real.sqrt t : ℂ) else -(Real.sqrt t : ℂ)

/-- **The `2 × 2` eigen-equation**: `[[-t, x], [x, t]] e_σ(t) = λ_σ e_σ(t)` for `0 ≤ t ≤ 1`. -/
theorem modeBlock_mulVec_modeVector {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) (σ τ : Fin 2) :
    ∑ ρ, modeBlock u τ ρ * modeVector u σ ρ = modeEig u σ * modeVector u σ τ := by
  have hr : Real.sqrt u ≤ 1 := Real.sqrt_le_one.mpr h1
  have hr0 := Real.sqrt_nonneg u
  set a := Real.sqrt (1 - Real.sqrt u)
  set c := Real.sqrt (1 + Real.sqrt u)
  have ha : a * a = 1 - Real.sqrt u := Real.mul_self_sqrt (by linarith)
  have hc : c * c = 1 + Real.sqrt u := Real.mul_self_sqrt (by linarith)
  have hx : Real.sqrt (u * (1 - u)) = Real.sqrt u * (a * c) := by
    rw [← Real.sqrt_mul (by linarith) (1 + Real.sqrt u),
      ← Real.sqrt_mul h0, show (1 - Real.sqrt u) * (1 + Real.sqrt u) = 1 - u by
        nlinarith [Real.mul_self_sqrt h0]]
  have hu : u = Real.sqrt u * Real.sqrt u := (Real.mul_self_sqrt h0).symm
  have haC : (a : ℂ) * (a : ℂ) = 1 - (Real.sqrt u : ℂ) := by exact_mod_cast ha
  have hcC : (c : ℂ) * (c : ℂ) = 1 + (Real.sqrt u : ℂ) := by exact_mod_cast hc
  have huC : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by exact_mod_cast hu.symm
  set r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
  simp only [Fin.sum_univ_two, modeBlock, modeVector, modeEig, hx]
  fin_cases σ <;> fin_cases τ
  · simp
    linear_combination ((a : ℂ) * r * (Real.sqrt u : ℂ)) * hcC + ((a : ℂ) * r) * huC
  · simp
    linear_combination ((c : ℂ) * r * (Real.sqrt u : ℂ)) * haC - ((c : ℂ) * r) * huC
  · simp
    linear_combination (-((c : ℂ) * r * (Real.sqrt u : ℂ))) * haC + ((c : ℂ) * r) * huC
  · simp
    linear_combination ((a : ℂ) * r * (Real.sqrt u : ℂ)) * hcC + ((a : ℂ) * r) * huC

omit [DecidableEq ι] in
theorem mul_curFrame_apply (π : Type*) (M : Matrix ι ι ℂ) (x : ι) (k : Fin K) (σ : Fin 2) :
    (M * curFrame P Q F π t h) x (Sum.inl (k, σ)) = if h ^ 2 < t k.val then
      ((t k.val ^ (1 / 4 : ℝ) : ℝ) : ℂ) * (modeVector (t k.val) σ 0 * (M * nearPartners P Q F t) x k +
        modeVector (t k.val) σ 1 * (M * F) x k) else 0 := by
  simp only [mul_apply, curFrame_apply]
  split_ifs with hk
  · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  · simp

/-- **Every current column of `Φ V₀` is an eigenvector of `P' - P`** with eigenvalue
`λ_σ(t_k) = ±√t_k`. -/
theorem sub_mul_curFrame (π : Type*) (hPP : P * P = P) (hQQ : Q * Q = Q) (hPF : P * F = 0)
    (hFF : Fᴴ * F = maskDiag K t h) (hQF : (1 - P) * Q * F = F * tDiag K t)
    (ht : ∀ k : Fin K, h ^ 2 < t k.val → 0 < t k.val ∧ t k.val < 1) (x : ι) (k : Fin K)
    (σ : Fin 2) :
    ((Q - P) * curFrame P Q F π t h) x (Sum.inl (k, σ)) =
      modeEig (t k.val) σ * curFrame P Q F π t h x (Sum.inl (k, σ)) := by
  rw [mul_curFrame_apply, sub_mul_near hPP hQQ hFF hQF ht, sub_mul_far hPF hFF hQF ht,
    curFrame_apply]
  split_ifs with hk
  · have r0 := modeBlock_mulVec_modeVector (ht k hk).1.le (ht k hk).2.le σ 0
    have r1 := modeBlock_mulVec_modeVector (ht k hk).1.le (ht k hk).2.le σ 1
    simp only [Fin.sum_univ_two, modeBlock] at r0 r1
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one] at r0 r1
    generalize modeVector (t k.val) σ 0 = e0 at r0 r1 ⊢
    generalize modeVector (t k.val) σ 1 = e1 at r0 r1 ⊢
    simp only [Matrix.sub_apply, Matrix.add_apply, mul_diagonal, xDiag, tDiag]
    linear_combination (((t k.val ^ (1 / 4 : ℝ) : ℝ) : ℂ) * nearPartners P Q F t x k) * r0 +
      (((t k.val ^ (1 / 4 : ℝ) : ℝ) : ℂ) * F x k) * r1
  · simp

end BlockBand.SourceProcess.ClosedSum
