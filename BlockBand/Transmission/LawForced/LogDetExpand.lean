module

public import BlockBand.Transmission.LawForced.LogDetSand

/-!
# The global second-order `log det` expansion about a diagonal

**`logDet_sand_expand`**: for Hermitian `S`, `1 + wt_k > 0`, `m ≤ (1+wt_k)⁻¹ ≤ ρ`, `c₀ ≥ 0`,
`0 < c₀m ≤ 1` and `I + wS − c₀I ⪰ 0`:
```
|log Re det(I+wS) − Σ_k log(1+wt_k) − w Re Tr(RB) + (w²/2) Re Tr(RBRB)|
    ≤ 9/(c₀m) · √(w²ρ²‖B‖²_HS) · w²ρ²‖B‖²_HS.
```
Also `eig_ge_of_posSemidef` (`I + wH − aI ⪰ 0 ⇒ a − 1 ≤ wλ_k(H)`), hence
`re_det_one_add_smul_pos` (`Re det(I + wS) > 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix
open scoped ComplexOrder ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n] {w : ℝ} {t : n → ℝ}

/-- `I + wH − aI ⪰ 0 ⇒ a − 1 ≤ wλ_k(H)`. -/
theorem eig_ge_of_posSemidef {H : Matrix n n ℂ} (hH : H.IsHermitian) {a : ℝ}
    (hP : (1 + (w : ℂ) • H - (a : ℂ) • 1).PosSemidef) (k : n) :
    a - 1 ≤ w * hH.eigenvalues k := by
  set v := ⇑(hH.eigenvectorBasis k)
  have hp := hP.re_dotProduct_nonneg v
  have hn : star v ⬝ᵥ v = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      hH.eigenvectorBasis.orthonormal.1 k]
    simp
  have he : hH.eigenvalues k = RCLike.re (star v ⬝ᵥ (H *ᵥ v)) := hH.eigenvalues_eq k
  rw [sub_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_add, dotProduct_smul, dotProduct_smul, hn, map_sub, map_add] at hp
  simp only [smul_eq_mul, RCLike.one_re, mul_one] at hp
  rw [show RCLike.re ((w : ℂ) * (star v ⬝ᵥ (H *ᵥ v))) = w * (star v ⬝ᵥ (H *ᵥ v)).re from
    Complex.re_ofReal_mul _ _, show RCLike.re (a : ℂ) = a from Complex.ofReal_re a] at hp
  have : RCLike.re (star v ⬝ᵥ (H *ᵥ v)) = (star v ⬝ᵥ (H *ᵥ v)).re := rfl
  rw [he, this]
  linarith

theorem re_det_one_add_smul_pos {S : Matrix n n ℂ} (hS : S.IsHermitian) {c₀ : ℝ} (hc : 0 < c₀)
    (hP : (1 + (w : ℂ) • S - (c₀ : ℂ) • 1).PosSemidef) : 0 < (1 + (w : ℂ) • S).det.re := by
  rw [det_one_add_smul_eq_prod hS w, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_pos fun k _ => by linarith [eig_ge_of_posSemidef hS hP k]

omit [Fintype n] in
theorem rhalf_isHermitian : (rhalf w t).IsHermitian := by
  rw [rhalf]; exact isHermitian_diagonal_of_self_adjoint _ (by ext k; simp)

theorem nSand_isHermitian {S : Matrix n n ℂ} (hS : S.IsHermitian) :
    (nSand w t S).IsHermitian := by
  have hD : (dmat t).IsHermitian := by
    rw [dmat]; exact isHermitian_diagonal_of_self_adjoint _ (by ext k; simp)
  have hB : (S - dmat t).IsHermitian := hS.sub hD
  have hh := (rhalf_isHermitian (w := w) (t := t))
  unfold nSand
  rw [IsHermitian, conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, hh.eq, hB.eq,
    Complex.star_def, Complex.conj_ofReal, Matrix.mul_assoc]

theorem posSemidef_one_add_nSand {S : Matrix n n ℂ} {c₀ m : ℝ} (hd : ∀ k, 0 < 1 + w * t k)
    (hm : ∀ k, m ≤ (1 + w * t k)⁻¹) (hc₀ : 0 ≤ c₀)
    (hP : (1 + (w : ℂ) • S - (c₀ : ℂ) • 1).PosSemidef) :
    (1 + ((1 : ℝ) : ℂ) • nSand w t S - ((c₀ * m : ℝ) : ℂ) • 1).PosSemidef := by
  set h := rhalf w t
  have hhH : hᴴ = h := rhalf_isHermitian.eq
  have e : 1 + ((1 : ℝ) : ℂ) • nSand w t S - ((c₀ * m : ℝ) : ℂ) • 1 =
      hᴴ * (1 + (w : ℂ) • S - (c₀ : ℂ) • 1) * h +
        (c₀ : ℂ) • (rres w t - ((m : ℝ) : ℂ) • 1) := by
    rw [Complex.ofReal_one, one_smul, one_add_nSand hd, hhH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, rhalf_mul_rhalf hd, smul_sub, smul_smul,
      Complex.ofReal_mul]
    abel
  rw [e]
  refine (hP.conjTranspose_mul_mul_same h).add (PosSemidef.smul ?_ (Complex.zero_le_real.2 hc₀))
  have : rres w t - ((m : ℝ) : ℂ) • 1 = diagonal fun k => (((1 + w * t k)⁻¹ - m : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [rres]
    · simp [rres, diagonal_apply_ne _ hij, one_apply_ne hij]
  rw [this, posSemidef_diagonal_iff]
  exact fun k => Complex.zero_le_real.2 (by linarith [hm k])

/-- **The global second-order expansion of `log det(I + wS)` about `D = diag t`.** -/
theorem logDet_sand_expand {S : Matrix n n ℂ} (hS : S.IsHermitian) {c₀ m ρ : ℝ}
    (hd : ∀ k, 0 < 1 + w * t k) (hm : ∀ k, m ≤ (1 + w * t k)⁻¹)
    (hρ : ∀ k, (1 + w * t k)⁻¹ ≤ ρ) (hc₀ : 0 ≤ c₀) (hc : 0 < c₀ * m) (hc1 : c₀ * m ≤ 1)
    (hP : (1 + (w : ℂ) • S - (c₀ : ℂ) • 1).PosSemidef) :
    |Real.log (1 + (w : ℂ) • S).det.re - ∑ k, Real.log (1 + w * t k) -
        w * (rres w t * (S - dmat t)).trace.re +
        w ^ 2 / 2 * (rres w t * (S - dmat t) * rres w t * (S - dmat t)).trace.re| ≤
      9 / (c₀ * m) * (Real.sqrt (w ^ 2 * ρ ^ 2 * Generator.frobSq (S - dmat t)) *
        (w ^ 2 * ρ ^ 2 * Generator.frobSq (S - dmat t))) := by
  have hN := nSand_isHermitian (w := w) (t := t) hS
  have hc0 : 0 < c₀ := lt_of_le_of_ne hc₀ fun h => by
    rw [← h, zero_mul] at hc; exact lt_irrefl _ hc
  have hlow : ∀ k, c₀ * m - 1 ≤ hN.eigenvalues k := fun k => by
    have := eig_ge_of_posSemidef hN (posSemidef_one_add_nSand hd hm hc₀ hP) k
    linarith
  have key := abs_logDet_sub_le hN hc hc1 hlow
  have htr : (nSand w t S).trace.re = w * (rres w t * (S - dmat t)).trace.re := by
    rw [trace_nSand hd, Complex.re_ofReal_mul]
  have htr2 : (nSand w t S ^ 2).trace.re =
      w ^ 2 * (rres w t * (S - dmat t) * rres w t * (S - dmat t)).trace.re := by
    rw [trace_nSand_sq hd, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hX : (nSand w t S ^ 2).trace.re ≤ w ^ 2 * ρ ^ 2 * Generator.frobSq (S - dmat t) := by
    rw [re_trace_sq_eq_frobSq hN]; exact frobSq_nSand_le hd hρ S
  have hX0 : 0 ≤ (nSand w t S ^ 2).trace.re := by
    rw [re_trace_sq_eq_frobSq hN]; exact Generator.frobSq_nonneg _
  rw [log_det_one_add_nSand hd S (re_det_one_add_smul_pos hS hc0 hP), htr] at key
  have hmono : 9 / (c₀ * m) * (Real.sqrt (nSand w t S ^ 2).trace.re *
      (nSand w t S ^ 2).trace.re) ≤ 9 / (c₀ * m) * (Real.sqrt (w ^ 2 * ρ ^ 2 *
        Generator.frobSq (S - dmat t)) * (w ^ 2 * ρ ^ 2 * Generator.frobSq (S - dmat t))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt hX) hX hX0 (Real.sqrt_nonneg _))
      (by positivity)
  refine le_trans (le_of_eq ?_) (key.trans hmono)
  rw [htr2]
  congr 1
  ring

end BlockBand.Transmission.LawForced
