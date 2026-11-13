module

public import BlockBand.LocalWindow.ProofPartTwoTransfer

/-!
# The compressed window centre as `|ρ| → ∞`

The compressed window estimate is centred at the compressed centre
`(d-1)⁻¹ Tr(J' Γ'(λ))` (`J' = U*JU`, `Γ' = s'|B₀ - λ - s'm'|⁻²`, `m'` the Dyson root of the
compressed deformation `B₀ = U*MU` at variance `s'`), while part (ii) is centred at
`j_B(E, λ) = d⁻¹ Tr(J Γ(λ))` of the full deformation `K = M + ρ ww*`. This file proves that the two
agree up to `O(1/|ρ|)`, deterministically and with constants depending only on `‖M‖`, `s`, `v₀`.

Coordinate-free setting: `U : ℂ^κ → ℂ^ι` with `U*U = 1`, the complementary projection
`Π = 1 - UU*` (`= ww*` for the pole direction `w`), `K = M + ρΠ`, `d = |ι| = |κ| + 1`.

## Main results

* `compress_resolvent_sub_le` (Schur complement at `ρ = ∞`): for Hermitian `M`, `Im ω > 0`,
  `‖ω‖ < |ρ|`: `‖(K - ω)⁻¹ - U(B₀ - ω)⁻¹U*‖ ≤ (1 + ‖M‖/Im ω)³/(|ρ| - ‖ω‖)`.
* **`approxRoot_stability`**: an approximate Dyson root `m₂` (`m₂ = ⟨(F - z - sm₂)⁻¹⟩ + e`) is
  within `2|e|/(s v₀²)` of the exact root `m₁` (`Im m_j ≥ v₀`, `|e| ≤ v₀/2`, `|e| ≤ s v₀³`).
* **`compress_root_close`**: with `s' = s|κ|/|ι|` and `m` the root of `K` at real `x`, `d m/(d-1)`
  is within `4δ/(s'v₀²)` of the root `m'` of `B₀` at variance `s'`
  (`δ = (1 + ‖M‖/(s'v₀))³/(|ρ| - |x| - 1/v₀)`).
* **`compress_centre_close`**: `|d⁻¹Tr(J s RR*) - (d-1)⁻¹Tr(U*JU s' R'R'*)| ≤
  (2s/(s'v₀))(1 + 4/(v₀²(s'v₀)²)) δ` (`R, R'` the resolvents at the respective roots).
* **`pairCentre_compress_close`**: the same for `pairCentre J K s x` of a pair deformation and the
  compressed centre `compressCentre` on `Fin (2W - 1)` (`s' = compressVar p s = s(1 - 1/(2W))`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.LocalWindow.ProofETH
open scoped ComplexConjugate Matrix.Norms.L2Operator

section Generic

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- An isometry `U*U = 1` is a contraction. -/
theorem compress_opNorm_isometry_le {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) : ‖U‖ ≤ 1 := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have : U = 0 := by ext a b; exact (IsEmpty.false b).elim
    rw [this, norm_zero]; exact zero_le_one
  · have h := Matrix.l2_opNorm_conjTranspose_mul_self U
    rw [hU, norm_one] at h
    nlinarith [norm_nonneg U]

theorem compress_opNorm_isometry_adj_le {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) : ‖Uᴴ‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_conjTranspose]; exact compress_opNorm_isometry_le hU

/-- A Hermitian idempotent is a contraction. -/
theorem compress_opNorm_proj_le {P : Matrix ι ι ℂ} (hH : Pᴴ = P) (hI : P * P = P) : ‖P‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hH, hI] at h
  rcases (norm_nonneg P).eq_or_lt with h0 | h0
  · rw [← h0]; exact zero_le_one
  · nlinarith

/-- `|Tr X| ≤ N ‖X‖` (`L²` operator norm). -/
theorem compress_norm_trace_le (X : Matrix ι ι ℂ) : ‖X.trace‖ ≤ Fintype.card ι * ‖X‖ := by
  have hdiag : ∀ a, ‖X a a‖ ≤ ‖X‖ := by
    intro a
    have h := sqNorm_mulVec_le_opNorm X (Pi.single a 1)
    have h2 : sqNorm (Pi.single a (1 : ℂ) : ι → ℂ) = 1 := by
      unfold sqNorm
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
      simp
    have h3 : ‖X a a‖ ^ 2 ≤ sqNorm (X *ᵥ Pi.single a 1) := by
      have e : (X *ᵥ Pi.single a (1 : ℂ)) a = X a a := by rw [mulVec_single_one]; rfl
      unfold sqNorm
      rw [← e]
      exact Finset.single_le_sum (f := fun b => ‖(X *ᵥ Pi.single a (1 : ℂ)) b‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ a)
    rw [h2, mul_one] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (h3.trans h)
  calc ‖X.trace‖ ≤ ∑ a, ‖X a a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ι, ‖X‖ := Finset.sum_le_sum fun a _ => hdiag a
    _ = Fintype.card ι * ‖X‖ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- The compressed matrix `B₀ = U*MU` of a Hermitian `M` is Hermitian. -/
theorem isHermitian_compress {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (U : Matrix ι κ ℂ) :
    (Uᴴ * M * U).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hM.eq, Matrix.mul_assoc]

/-- `K = M + ρ(1 - UU*)` is Hermitian. -/
theorem isHermitian_compressFull {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (U : Matrix ι κ ℂ)
    (ρ : ℝ) : (M + (ρ : ℂ) • (1 - U * Uᴴ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_mul, conjTranspose_conjTranspose, hM.eq, Complex.star_def, Complex.conj_ofReal]

/-- **The resolvent at `ρ = ∞` is the compressed resolvent** (Schur complement):
for Hermitian `M`, an isometry `U` (`U*U = 1`), `Π = 1 - UU*`, `Im ω > 0` and `‖ω‖ < |ρ|`,
`‖(M + ρΠ - ω)⁻¹ - U (U*MU - ω)⁻¹ U*‖ ≤ (1 + ‖M‖/Im ω)³/(|ρ| - ‖ω‖)`. -/
theorem compress_resolvent_sub_le [Nonempty ι] {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) {ρ : ℝ} {ω : ℂ} (hω : 0 < ω.im) (hρ : ‖ω‖ < |ρ|) :
    ‖(M + (ρ : ℂ) • (1 - U * Uᴴ) - ω • (1 : Matrix ι ι ℂ))⁻¹ -
        U * (Uᴴ * M * U - ω • (1 : Matrix κ κ ℂ))⁻¹ * Uᴴ‖ ≤
      (1 + ‖M‖ / ω.im) ^ 3 / (|ρ| - ‖ω‖) := by
  have hKH := isHermitian_compressFull hM U ρ
  have hB₀H := isHermitian_compress hM U
  have hω0 : ω.im ≠ 0 := hω.ne'
  have hpos : 0 < |ρ| - ‖ω‖ := by linarith
  set Pr : Matrix ι ι ℂ := 1 - U * Uᴴ with hPr
  set A := M + (ρ : ℂ) • Pr - ω • (1 : Matrix ι ι ℂ) with hA
  set B₀ := Uᴴ * M * U with hB₀
  set Bw := B₀ - ω • (1 : Matrix κ κ ℂ) with hBw
  set R := A⁻¹ with hR
  set R' := Bw⁻¹ with hR'
  set T := U * R' * Uᴴ with hT
  set c := ω.im with hc
  have hAdet : A.det ≠ 0 := det_resolvent_ne_zero hKH hω0
  have hBdet : Bw.det ≠ 0 := det_resolvent_ne_zero hB₀H hω0
  have hRA : R * A = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hAdet)
  have hAR : A * R = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hAdet)
  have hBR : Bw * R' = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hBdet)
  have hRB : R' * Bw = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hBdet)
  have hRn : ‖R‖ ≤ c⁻¹ := by
    have := opNorm_resolvent_le hKH hω0; rwa [abs_of_pos hω] at this
  have hR'n : ‖R'‖ ≤ c⁻¹ := by
    have := opNorm_resolvent_le hB₀H hω0; rwa [abs_of_pos hω] at this
  have hUn := compress_opNorm_isometry_le hU
  have hUhn := compress_opNorm_isometry_adj_le hU
  have hc0 : 0 < c := hω
  have hM0 := norm_nonneg M
  -- the projection `Π`
  have hPU : Pr * U = 0 := by
    rw [hPr, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  have hUP : Uᴴ * Pr = 0 := by
    rw [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul, sub_self]
  have hPP : Pr * Pr = Pr := by
    have e : U * Uᴴ * (U * Uᴴ) = U * Uᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
    rw [hPr, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, e, sub_self, sub_zero]
  have hPH : Prᴴ = Pr := by
    rw [hPr, conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
  have hPn : ‖Pr‖ ≤ 1 := compress_opNorm_proj_le hPH hPP
  have hUU : U * Uᴴ = 1 - Pr := by rw [hPr]; abel
  -- `A U = U (B₀ - ω) + Π M U`
  have hAU : A * U = U * Bw + Pr * M * U := by
    have e1 : A * U = M * U - ω • U := by
      rw [hA, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, hPU, smul_zero, add_zero,
        Matrix.smul_mul, Matrix.one_mul]
    have e2 : U * Bw = U * Uᴴ * M * U - ω • U := by
      rw [hBw, hB₀, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    rw [e1, e2, hUU]
    simp only [Matrix.sub_mul, Matrix.one_mul]
    abel
  -- `A T = 1 - Π + Π M T`
  have hAT : A * T = 1 - Pr + Pr * M * T := by
    calc A * T = (A * U) * R' * Uᴴ := by rw [hT]; simp only [Matrix.mul_assoc]
      _ = U * (Bw * R') * Uᴴ + Pr * M * T := by
          rw [hAU, Matrix.add_mul, Matrix.add_mul, hT]; simp only [Matrix.mul_assoc]
      _ = 1 - Pr + Pr * M * T := by rw [hBR, Matrix.mul_one, hUU]
  -- `R - T = R Π (1 - M T)`
  have hRT : R - T = R * Pr * (1 - M * T) := by
    have h1 : T = R * (A * T) := by rw [← Matrix.mul_assoc, hRA, Matrix.one_mul]
    rw [hAT] at h1
    conv_lhs => rw [h1]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
    abel
  -- the size of `Q = R Π`
  set Q := R * Pr with hQ
  have hQn : ‖Q‖ ≤ c⁻¹ :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg R, norm_nonneg Pr, inv_pos.mpr hc0])
  have hAQ : A * Q = Pr := by rw [hQ, ← Matrix.mul_assoc, hAR, Matrix.one_mul]
  have hPA : Pr * A = Pr * M + ((ρ : ℂ) - ω) • Pr := by
    rw [hA, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, hPP, Matrix.mul_smul, Matrix.mul_one,
      sub_smul]
    abel
  have hPQ : ((ρ : ℂ) - ω) • (Pr * Q) = Pr - Pr * M * Q := by
    have h : Pr * (A * Q) = Pr * Pr := by rw [hAQ]
    rw [← Matrix.mul_assoc, hPA, hPP, Matrix.add_mul, Matrix.smul_mul] at h
    exact eq_sub_of_add_eq' h
  have hρω : |ρ| - ‖ω‖ ≤ ‖(ρ : ℂ) - ω‖ := by
    have := norm_sub_norm_le (ρ : ℂ) ω
    rwa [Complex.norm_real, Real.norm_eq_abs] at this
  have hPMQ : ‖Pr * M * Q‖ ≤ ‖M‖ / c := by
    calc ‖Pr * M * Q‖ ≤ ‖Pr‖ * ‖M‖ * ‖Q‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖M‖ * c⁻¹ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hPn hM0) hQn (norm_nonneg _) ?_
          positivity
      _ = ‖M‖ / c := by ring
  have hPQn : ‖Pr * Q‖ ≤ (1 + ‖M‖ / c) / (|ρ| - ‖ω‖) := by
    have h := congrArg norm hPQ
    rw [norm_smul] at h
    have hr : ‖Pr - Pr * M * Q‖ ≤ 1 + ‖M‖ / c := (norm_sub_le _ _).trans (add_le_add hPn hPMQ)
    rw [le_div_iff₀ hpos]
    calc ‖Pr * Q‖ * (|ρ| - ‖ω‖) ≤ ‖Pr * Q‖ * ‖(ρ : ℂ) - ω‖ :=
          mul_le_mul_of_nonneg_left hρω (norm_nonneg _)
      _ = ‖(ρ : ℂ) - ω‖ * ‖Pr * Q‖ := mul_comm _ _
      _ = ‖Pr - Pr * M * Q‖ := h
      _ ≤ _ := hr
  -- `U* Q = -R' U* M Π Q`
  have hUA : Uᴴ * A = Bw * Uᴴ + Uᴴ * M * Pr := by
    have e1 : Uᴴ * A = Uᴴ * M - ω • Uᴴ := by
      rw [hA, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, hUP, smul_zero, add_zero,
        Matrix.mul_smul, Matrix.mul_one]
    have e2 : Bw * Uᴴ = Uᴴ * M * (U * Uᴴ) - ω • Uᴴ := by
      rw [hBw, hB₀, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, e2, hUU]
    simp only [Matrix.mul_sub, Matrix.mul_one]
    abel
  have hUQ : Uᴴ * Q = -(R' * (Uᴴ * M * (Pr * Q))) := by
    have h0 : Uᴴ * (A * Q) = 0 := by rw [hAQ, hUP]
    rw [← Matrix.mul_assoc, hUA, Matrix.add_mul] at h0
    have h2 : Bw * (Uᴴ * Q) = -(Uᴴ * M * (Pr * Q)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc (Uᴴ * M)]
      exact eq_neg_of_add_eq_zero_left h0
    have h1 : Uᴴ * Q = R' * (Bw * (Uᴴ * Q)) := by
      rw [← Matrix.mul_assoc R' Bw, hRB, Matrix.one_mul]
    rw [h1, h2, Matrix.mul_neg]
  have hQsplit : Q = U * (Uᴴ * Q) + Pr * Q := by
    rw [← Matrix.mul_assoc, ← Matrix.add_mul, hUU, sub_add_cancel, Matrix.one_mul]
  have hUQn : ‖Uᴴ * Q‖ ≤ ‖M‖ / c * ‖Pr * Q‖ := by
    rw [hUQ, norm_neg]
    calc ‖R' * (Uᴴ * M * (Pr * Q))‖ ≤ ‖R'‖ * (‖Uᴴ‖ * ‖M‖ * ‖Pr * Q‖) :=
          (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left
            ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
              (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ c⁻¹ * (1 * ‖M‖ * ‖Pr * Q‖) := by
          refine mul_le_mul hR'n ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUhn hM0) (norm_nonneg _)
      _ = ‖M‖ / c * ‖Pr * Q‖ := by ring
  have hQn2 : ‖Q‖ ≤ (1 + ‖M‖ / c) * ‖Pr * Q‖ := by
    calc ‖Q‖ = ‖U * (Uᴴ * Q) + Pr * Q‖ := by rw [← hQsplit]
      _ ≤ ‖U‖ * ‖Uᴴ * Q‖ + ‖Pr * Q‖ := (norm_add_le _ _).trans
          (add_le_add (Matrix.l2_opNorm_mul _ _) le_rfl)
      _ ≤ 1 * (‖M‖ / c * ‖Pr * Q‖) + ‖Pr * Q‖ :=
          add_le_add (mul_le_mul hUn hUQn (norm_nonneg _) zero_le_one) le_rfl
      _ = (1 + ‖M‖ / c) * ‖Pr * Q‖ := by ring
  -- the final bound
  have hTn : ‖T‖ ≤ c⁻¹ := by
    calc ‖T‖ ≤ ‖U‖ * ‖R'‖ * ‖Uᴴ‖ := by
          rw [hT]
          exact (Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ 1 * c⁻¹ * 1 := by
          refine mul_le_mul (mul_le_mul hUn hR'n (norm_nonneg _) zero_le_one) hUhn
            (norm_nonneg _) (by positivity)
      _ = c⁻¹ := by ring
  have h1MT : ‖1 - M * T‖ ≤ 1 + ‖M‖ / c := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    refine add_le_add le_rfl ((norm_mul_le _ _).trans ?_)
    calc ‖M‖ * ‖T‖ ≤ ‖M‖ * c⁻¹ := mul_le_mul_of_nonneg_left hTn hM0
      _ = ‖M‖ / c := by ring
  have hL : 0 ≤ 1 + ‖M‖ / c := by positivity
  rw [hRT]
  calc ‖Q * (1 - M * T)‖ ≤ ‖Q‖ * ‖1 - M * T‖ := norm_mul_le _ _
    _ ≤ ((1 + ‖M‖ / c) * ((1 + ‖M‖ / c) / (|ρ| - ‖ω‖))) * (1 + ‖M‖ / c) :=
        mul_le_mul (hQn2.trans (mul_le_mul_of_nonneg_left hPQn hL)) h1MT (norm_nonneg _)
          (by positivity)
    _ = (1 + ‖M‖ / c) ^ 3 / (|ρ| - ‖ω‖) := by ring

/-- **Stability of the Dyson equation at an approximate root**: for Hermitian `F`, `s > 0`,
`Im z ≥ 0`, an exact root `m₁` and any `m₂` with `Im m_j ≥ v₀ > 0` whose defect
`e = m₂ - N⁻¹ Tr (F - z - s m₂)⁻¹` has `|e| ≤ v₀/2` and `|e| ≤ s v₀³`:
`|m₁ - m₂| ≤ 2|e|/(s v₀²)`. -/
theorem approxRoot_stability [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z m₁ m₂ : ℂ} (hz : 0 ≤ z.im) (h₁ : IsDysonRoot F s z m₁) {v₀ : ℝ}
    (hv₀ : 0 < v₀) (hv₁ : v₀ ≤ m₁.im) (hv₂ : v₀ ≤ m₂.im)
    (he₁ : ‖m₂ - (Fintype.card ι : ℂ)⁻¹ *
      ((F - (z + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace‖ ≤ v₀ / 2)
    (he₂ : ‖m₂ - (Fintype.card ι : ℂ)⁻¹ *
      ((F - (z + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace‖ ≤ s * v₀ ^ 3) :
    ‖m₁ - m₂‖ ≤ 2 / (s * v₀ ^ 2) * ‖m₂ - (Fintype.card ι : ℂ)⁻¹ *
      ((F - (z + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace‖ := by
  set M₁ := (F - (z + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ with hM₁
  set M₂ := (F - (z + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹ with hM₂
  set e := m₂ - (Fintype.card ι : ℂ)⁻¹ * M₂.trace with he
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hNc : ((N : ℝ) : ℂ) = (Fintype.card ι : ℂ) := Complex.ofReal_natCast _
  have hNne : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm₂ : 0 < m₂.im := hv₀.trans_le hv₂
  have hw₁ : 0 < (z + (s : ℂ) * m₁).im := dysonRoot_w_im_pos hs hz h₁.1
  have hw₂ : 0 < (z + (s : ℂ) * m₂).im := dysonRoot_w_im_pos hs hz hm₂
  have e1 : M₁.trace = N * m₁ := by
    rw [h₁.2, ← mul_assoc, hNc, mul_inv_cancel₀ hNne, one_mul]
  have e2 : M₂.trace = N * (m₂ - e) := by
    rw [he, sub_sub_cancel, ← mul_assoc, hNc, mul_inv_cancel₀ hNne, one_mul]
  have hdiff : M₁ - M₂ = ((s : ℂ) * (m₁ - m₂)) • (M₁ * M₂) := by
    have h := resolvent_sub hF hw₁.ne' hw₂.ne'
    rwa [show (z + (s : ℂ) * m₁) - (z + (s : ℂ) * m₂) = (s : ℂ) * (m₁ - m₂) by ring] at h
  set T := (M₁ * M₂).trace with hT
  have hkey : (m₁ - m₂) * ((N : ℂ) - (s : ℂ) * T) = -((N : ℂ) * e) := by
    have h := congrArg Matrix.trace hdiff
    rw [trace_sub, trace_smul, e1, e2, smul_eq_mul] at h
    linear_combination h
  -- `frob (M₁ - M₂*) = f₁ + f₂ - 2 Re T`
  set Y := M₁ - M₂ᴴ with hYdef
  have hY : frob Y = frob M₁ + frob M₂ - 2 * T.re := by
    have h := trace_mul_conjTranspose Y
    have e : Y * Yᴴ = M₁ * M₁ᴴ - M₁ * M₂ - (M₁ * M₂)ᴴ + M₂ᴴ * M₂ := by
      simp only [Y, conjTranspose_sub, conjTranspose_conjTranspose, conjTranspose_mul,
        Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [e, trace_add, trace_sub, trace_sub, trace_conjTranspose, trace_mul_comm M₂ᴴ M₂,
      trace_mul_conjTranspose, trace_mul_conjTranspose] at h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.star_def,
      Complex.conj_re] at this
    linarith
  have htrY : Y.trace.im = N * (m₁.im + m₂.im - e.im) := by
    simp only [Y, trace_sub, trace_conjTranspose, e1, e2, Complex.sub_im, Complex.star_def,
      Complex.conj_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, map_mul, Complex.conj_ofReal, map_sub]
    ring
  have heim : |e.im| ≤ ‖e‖ := Complex.abs_im_le_norm e
  have heim1 : -e.im ≥ -(v₀ / 2) := by have := (abs_le.mp (heim.trans he₁)).2; linarith
  have hsum : 3 / 2 * v₀ ≤ m₁.im + m₂.im - e.im := by linarith
  have hYlow : N * (3 / 2 * v₀) ^ 2 ≤ frob Y := by
    have h1 := norm_trace_sq_le Y
    have h2 : |Y.trace.im| ≤ ‖Y.trace‖ := Complex.abs_im_le_norm _
    have h3 : (Y.trace.im) ^ 2 ≤ ‖Y.trace‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [htrY] at h3
    have h4 : (3 / 2 * v₀) ^ 2 ≤ (m₁.im + m₂.im - e.im) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsum 2
    have : N ^ 2 * (3 / 2 * v₀) ^ 2 ≤ N * frob Y := by nlinarith
    nlinarith
  have hf₁ := s_frob_le hF hs hz h₁
  have hf₂ : s * frob M₂ ≤ N + N * s * v₀ ^ 2 := by
    have him := trace_im_resolvent hF hw₂.ne'
    rw [← hM₂, e2] at him
    have hreim : ((N : ℂ) * (m₂ - e)).im = N * (m₂.im - e.im) := by
      simp [Complex.mul_im]
    rw [hreim] at him
    have hwim : s * m₂.im ≤ (z + (s : ℂ) * m₂).im := dysonRoot_w_im hz
    have hf0 := frob_nonneg M₂
    have hb : s * m₂.im * frob M₂ ≤ N * (m₂.im - e.im) := by
      rw [him]; exact mul_le_mul_of_nonneg_right hwim hf0
    have he3 : -e.im ≤ s * v₀ ^ 3 := by have := (abs_le.mp (heim.trans he₂)).1; linarith
    have hv3 : s * v₀ ^ 3 ≤ s * v₀ ^ 2 * m₂.im := by
      have : v₀ ^ 3 = v₀ ^ 2 * v₀ := by ring
      rw [this, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hv₂ (by positivity)
    have hc : (s * frob M₂) * m₂.im ≤ (N + N * s * v₀ ^ 2) * m₂.im := by nlinarith
    exact le_of_mul_le_mul_right hc hm₂
  have hre : 1 / 2 * (s * N * v₀ ^ 2) ≤ ((N : ℂ) - (s : ℂ) * T).re := by
    have : ((N : ℂ) - (s : ℂ) * T).re = N - s * T.re := by simp [Complex.mul_re]
    rw [this]
    have hsY := mul_le_mul_of_nonneg_left hYlow hs.le
    have hTre : T.re = (frob M₁ + frob M₂ - frob Y) / 2 := by linarith
    rw [hTre]
    have hid : N - s * ((frob M₁ + frob M₂ - frob Y) / 2) - 1 / 2 * (s * N * v₀ ^ 2) =
        (N - s * frob M₁) / 2 + (N + N * s * v₀ ^ 2 - s * frob M₂) / 2 +
          (s * frob Y - s * (N * (3 / 2 * v₀) ^ 2)) / 2 + 1 / 8 * (s * N * v₀ ^ 2) := by ring
    have hp : 0 ≤ 1 / 8 * (s * N * v₀ ^ 2) := by positivity
    have hf₁' : s * frob M₁ ≤ N := hf₁
    linarith
  have hlow : 1 / 2 * (s * N * v₀ ^ 2) ≤ ‖(N : ℂ) - (s : ℂ) * T‖ :=
    hre.trans (Complex.re_le_norm _)
  have hnorm := congrArg norm hkey
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN] at hnorm
  have hpos : 0 < 1 / 2 * (s * N * v₀ ^ 2) := by positivity
  have h5 : ‖m₁ - m₂‖ * (1 / 2 * (s * N * v₀ ^ 2)) ≤ N * ‖e‖ := by
    rw [← hnorm]; exact mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : ‖m₁ - m₂‖ * (s * v₀ ^ 2) * N ≤ 2 * ‖e‖ * N := by nlinarith
  exact le_of_mul_le_mul_right this hN

/-- The root of a Hermitian deformation at real `x` is bounded: `s ‖m‖ ≤ 1/v₀` if `Im m ≥ v₀`. -/
theorem dysonRoot_norm_le [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z m : ℂ} (hz : 0 ≤ z.im) (h : IsDysonRoot F s z m) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hv : v₀ ≤ m.im) : s * ‖m‖ ≤ 1 / v₀ := by
  have hw := dysonRoot_w_im_pos hs hz h.1
  have hwim : s * m.im ≤ (z + (s : ℂ) * m).im := dysonRoot_w_im hz
  have hR := opNorm_resolvent_le hF hw.ne'
  rw [abs_of_pos hw] at hR
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have htr := compress_norm_trace_le ((F - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹)
  have hm : ‖m‖ ≤ ((z + (s : ℂ) * m).im)⁻¹ := by
    have e := h.2
    have : ‖m‖ = (Fintype.card ι : ℝ)⁻¹ *
        ‖((F - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹).trace‖ := by
      conv_lhs => rw [e]
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    rw [this, inv_mul_le_iff₀ hN]
    exact htr.trans (mul_le_mul_of_nonneg_left hR hN.le)
  have hsm : 0 < s * m.im := mul_pos hs (hv₀.trans_le hv)
  calc s * ‖m‖ ≤ s * ((z + (s : ℂ) * m).im)⁻¹ := mul_le_mul_of_nonneg_left hm hs.le
    _ ≤ s * (s * m.im)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hsm hwim) hs.le
    _ = 1 / m.im := by field_simp
    _ ≤ 1 / v₀ := one_div_le_one_div_of_le hv₀ hv

/-- The resolvent error of `compress_resolvent_sub_le` at the root: for a root `m` of
`K = M + ρ(1 - UU*)` at real `x` with `Im m ≥ v₀`, `0 < c₀ ≤ s v₀` and
`(1 + ‖M‖/c₀)³ ≤ δ(|ρ| - |x| - 1/v₀)`, `|x| + 1/v₀ < |ρ|`, the error at `ω = x + s m` is `≤ δ`. -/
theorem compress_resolvent_at_root_le [Nonempty ι] {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) {ρ s x v₀ c₀ δ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀)
    {m : ℂ} (hm : IsDysonRoot (M + (ρ : ℂ) • (1 - U * Uᴴ)) s (x : ℂ) m) (hmv : v₀ ≤ m.im)
    (hc₀ : 0 < c₀) (hc₀s : c₀ ≤ s * v₀) (hρ : |x| + 1 / v₀ < |ρ|)
    (hδ : (1 + ‖M‖ / c₀) ^ 3 ≤ δ * (|ρ| - (|x| + 1 / v₀))) :
    ‖(M + (ρ : ℂ) • (1 - U * Uᴴ) - ((x : ℂ) + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹ -
      U * (Uᴴ * M * U - ((x : ℂ) + (s : ℂ) * m) • (1 : Matrix κ κ ℂ))⁻¹ * Uᴴ‖ ≤ δ := by
  have hKH := isHermitian_compressFull hM U ρ
  set ω : ℂ := (x : ℂ) + (s : ℂ) * m with hω
  have hωim : ω.im = s * m.im := by simp [hω, Complex.mul_im]
  have hωpos : 0 < ω.im := by rw [hωim]; exact mul_pos hs (hv₀.trans_le hmv)
  have hc : c₀ ≤ ω.im := by rw [hωim]; exact hc₀s.trans (mul_le_mul_of_nonneg_left hmv hs.le)
  have hsm := dysonRoot_norm_le hKH hs (by simp) hm hv₀ hmv
  have hωn : ‖ω‖ ≤ |x| + 1 / v₀ := by
    refine (norm_add_le _ _).trans (add_le_add (by simp) ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]; exact hsm
  have hres := compress_resolvent_sub_le hM hU hωpos (hωn.trans_lt hρ)
  have hpos : 0 < |ρ| - (|x| + 1 / v₀) := by linarith
  refine hres.trans ?_
  have h1 : 1 + ‖M‖ / ω.im ≤ 1 + ‖M‖ / c₀ := by
    have := div_le_div_of_nonneg_left (norm_nonneg M) hc₀ hc
    linarith
  have h2 : (1 + ‖M‖ / ω.im) ^ 3 ≤ (1 + ‖M‖ / c₀) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h1 3
  have hδ0 : 0 ≤ δ := by
    by_contra hneg
    have : δ * (|ρ| - (|x| + 1 / v₀)) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
    have : 0 ≤ (1 + ‖M‖ / c₀) ^ 3 := by positivity
    linarith
  rw [div_le_iff₀ (by linarith)]
  calc (1 + ‖M‖ / ω.im) ^ 3 ≤ δ * (|ρ| - (|x| + 1 / v₀)) := h2.trans hδ
    _ ≤ δ * (|ρ| - ‖ω‖) := mul_le_mul_of_nonneg_left (by linarith) hδ0

/-- **The full root is the rescaled compressed root up to `O(1/|ρ|)`**
(`s m ≈ s' m'`). Let `|κ| + 1 = |ι|`, `s' = s|κ|/|ι|`, `M` Hermitian, `U*U = 1`,
`K = M + ρ(1 - UU*)`, `m` a root of `K` at real `x` (variance `s`) and `m'` a root of `U*MU` at `x`
(variance `s'`), `Im m, Im m' ≥ v₀ > 0`. If `(1 + ‖M‖/(s'v₀))³ ≤ δ (|ρ| - |x| - 1/v₀)`,
`4δ ≤ v₀` and `2δ ≤ s'v₀³`, then `‖(|ι|/|κ|) m - m'‖ ≤ 4δ/(s'v₀²)`. -/
theorem compress_root_close [Nonempty ι] [Nonempty κ]
    (hcard : Fintype.card κ + 1 = Fintype.card ι) {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) {ρ s x v₀ δ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀)
    {m m' : ℂ}
    (hm : IsDysonRoot (M + (ρ : ℂ) • (1 - U * Uᴴ)) s (x : ℂ) m) (hmv : v₀ ≤ m.im)
    (hm' : IsDysonRoot (Uᴴ * M * U) (s * Fintype.card κ / Fintype.card ι) (x : ℂ) m')
    (hm'v : v₀ ≤ m'.im) (hρ : |x| + 1 / v₀ < |ρ|)
    (hδ : (1 + ‖M‖ / (s * Fintype.card κ / Fintype.card ι * v₀)) ^ 3 ≤
      δ * (|ρ| - (|x| + 1 / v₀)))
    (hδ₁ : 4 * δ ≤ v₀) (hδ₂ : 2 * δ ≤ s * Fintype.card κ / Fintype.card ι * v₀ ^ 3) :
    ‖((Fintype.card ι : ℂ) / Fintype.card κ) * m - m'‖ ≤
      4 * δ / (s * Fintype.card κ / Fintype.card ι * v₀ ^ 2) := by
  set dι : ℝ := (Fintype.card ι : ℝ) with hdι
  set dκ : ℝ := (Fintype.card κ : ℝ) with hdκ
  have hdκ0 : 0 < dκ := Nat.cast_pos.mpr Fintype.card_pos
  have hdι0 : 0 < dι := Nat.cast_pos.mpr Fintype.card_pos
  have hcard' : dκ + 1 = dι := by rw [hdι, hdκ]; exact_mod_cast hcard
  have hdle : dκ ≤ dι := by linarith
  have hd2 : dι ≤ 2 * dκ := by
    have : (1 : ℝ) ≤ dκ := by rw [hdκ]; exact_mod_cast Fintype.card_pos
    linarith
  set s' := s * dκ / dι with hs'
  have hs'0 : 0 < s' := by positivity
  have hs's : s' ≤ s := by
    rw [hs', div_le_iff₀ hdι0]; exact mul_le_mul_of_nonneg_left hdle hs.le
  have hKH := isHermitian_compressFull hM U ρ
  have hB₀H := isHermitian_compress hM U
  set ω : ℂ := (x : ℂ) + (s : ℂ) * m with hω
  have hmpos : 0 < m.im := hv₀.trans_le hmv
  have hωim : ω.im = s * m.im := by simp [hω, Complex.mul_im]
  have hωpos : 0 < ω.im := by rw [hωim]; positivity
  have hc₀ : s' * v₀ ≤ ω.im := by
    rw [hωim]; exact mul_le_mul hs's hmv hv₀.le hs.le
  have hc₀' : s' * v₀ ≤ s * v₀ := mul_le_mul_of_nonneg_right hs's hv₀.le
  have hRT := compress_resolvent_at_root_le hM hU hs hv₀ hm hmv (by positivity) hc₀' hρ hδ
  -- the approximate compressed root
  set μ : ℂ := ((dι : ℂ) / dκ) * m with hμ
  have hdκne : (dκ : ℂ) ≠ 0 := by exact_mod_cast hdκ0.ne'
  have hdιne : (dι : ℂ) ≠ 0 := by exact_mod_cast hdι0.ne'
  have hsμ : (s' : ℂ) * μ = (s : ℂ) * m := by
    rw [hμ, hs']; push_cast; field_simp
  have hμim : μ.im = dι / dκ * m.im := by
    rw [hμ, show ((dι : ℂ) / dκ) = ((dι / dκ : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul]
  have hμv : v₀ ≤ μ.im := by
    rw [hμim]
    have : 1 ≤ dι / dκ := by rw [le_div_iff₀ hdκ0]; linarith
    nlinarith
  set R := (M + (ρ : ℂ) • (1 - U * Uᴴ) - ω • (1 : Matrix ι ι ℂ))⁻¹ with hR
  set R' := (Uᴴ * M * U - ω • (1 : Matrix κ κ ℂ))⁻¹ with hR'
  have htrT : (U * R' * Uᴴ).trace = R'.trace := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hdιc : ((dι : ℝ) : ℂ) = (Fintype.card ι : ℂ) := Complex.ofReal_natCast _
  have hdκc : ((dκ : ℝ) : ℂ) = (Fintype.card κ : ℂ) := Complex.ofReal_natCast _
  have hmtr : (dι : ℂ) * m = R.trace := by
    have e := hm.2
    rw [hdιc, e, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),
      one_mul]
  have he : μ - (Fintype.card κ : ℂ)⁻¹ *
      ((Uᴴ * M * U - ((x : ℂ) + (s' : ℂ) * μ) • (1 : Matrix κ κ ℂ))⁻¹).trace =
      (Fintype.card κ : ℂ)⁻¹ * (R - U * R' * Uᴴ).trace := by
    rw [hsμ, ← hω, ← hR', trace_sub, htrT, ← hmtr, hμ, ← hdκc]
    field_simp
  have hen : ‖μ - (Fintype.card κ : ℂ)⁻¹ *
      ((Uᴴ * M * U - ((x : ℂ) + (s' : ℂ) * μ) • (1 : Matrix κ κ ℂ))⁻¹).trace‖ ≤ 2 * δ := by
    rw [he, norm_mul, norm_inv, Complex.norm_natCast, ← hdκ]
    have ht := compress_norm_trace_le (R - U * R' * Uᴴ)
    rw [← hdι] at ht
    rw [inv_mul_le_iff₀ hdκ0]
    calc ‖(R - U * R' * Uᴴ).trace‖ ≤ dι * ‖R - U * R' * Uᴴ‖ := ht
      _ ≤ (2 * dκ) * δ := mul_le_mul hd2 hRT (norm_nonneg _) (by positivity)
      _ = dκ * (2 * δ) := by ring
  have hst := approxRoot_stability hB₀H hs'0 (z := (x : ℂ)) (by simp) hm' hv₀ hm'v hμv
    (hen.trans (by linarith)) (hen.trans hδ₂)
  rw [norm_sub_rev]
  calc ‖m' - μ‖ ≤ 2 / (s' * v₀ ^ 2) * (2 * δ) :=
        hst.trans (mul_le_mul_of_nonneg_left hen (by positivity))
    _ = 4 * δ / (s' * v₀ ^ 2) := by ring

/-- **The full window centre is the compressed window centre up to `O(1/|ρ|)`**
(`j_B(E, λ)` for `K = M + ρ ww*` versus the centre of the compressed window estimate). Hypotheses of `compress_root_close` and `‖J‖ ≤ 1`. With
`R = (K - x - s m)⁻¹`, `R' = (U*MU - x - s'm')⁻¹`, `s' = s|κ|/|ι|`:
`‖|ι|⁻¹ Tr(J · sRR*) - |κ|⁻¹ Tr(U*JU · s'R'R'*)‖ ≤ (2s/(s'v₀))(1 + 4/(v₀²(s'v₀)²)) δ`. -/
theorem compress_centre_close [Nonempty ι] [Nonempty κ]
    (hcard : Fintype.card κ + 1 = Fintype.card ι) {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) {ρ s x v₀ δ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀)
    {m m' : ℂ}
    (hm : IsDysonRoot (M + (ρ : ℂ) • (1 - U * Uᴴ)) s (x : ℂ) m) (hmv : v₀ ≤ m.im)
    (hm' : IsDysonRoot (Uᴴ * M * U) (s * Fintype.card κ / Fintype.card ι) (x : ℂ) m')
    (hm'v : v₀ ≤ m'.im) (hρ : |x| + 1 / v₀ < |ρ|)
    (hδ : (1 + ‖M‖ / (s * Fintype.card κ / Fintype.card ι * v₀)) ^ 3 ≤
      δ * (|ρ| - (|x| + 1 / v₀)))
    (hδ₁ : 4 * δ ≤ v₀) (hδ₂ : 2 * δ ≤ s * Fintype.card κ / Fintype.card ι * v₀ ^ 3)
    {J : Matrix ι ι ℂ} (hJ : ‖J‖ ≤ 1) :
    ‖(Fintype.card ι : ℂ)⁻¹ * (J * ((s : ℂ) •
          ((M + (ρ : ℂ) • (1 - U * Uᴴ) - ((x : ℂ) + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹ *
            ((M + (ρ : ℂ) • (1 - U * Uᴴ) -
              ((x : ℂ) + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹)ᴴ))).trace -
        (Fintype.card κ : ℂ)⁻¹ * (Uᴴ * J * U *
          (((s * Fintype.card κ / Fintype.card ι : ℝ) : ℂ) •
            ((Uᴴ * M * U - ((x : ℂ) + ((s * Fintype.card κ / Fintype.card ι : ℝ) : ℂ) * m') •
                (1 : Matrix κ κ ℂ))⁻¹ *
              ((Uᴴ * M * U - ((x : ℂ) + ((s * Fintype.card κ / Fintype.card ι : ℝ) : ℂ) * m') •
                (1 : Matrix κ κ ℂ))⁻¹)ᴴ))).trace‖ ≤
      2 * s / (s * Fintype.card κ / Fintype.card ι * v₀) *
        (1 + 4 / (v₀ ^ 2 * (s * Fintype.card κ / Fintype.card ι * v₀) ^ 2)) * δ := by
  set dι : ℝ := (Fintype.card ι : ℝ) with hdι
  set dκ : ℝ := (Fintype.card κ : ℝ) with hdκ
  have hdκ0 : 0 < dκ := Nat.cast_pos.mpr Fintype.card_pos
  have hdι0 : 0 < dι := Nat.cast_pos.mpr Fintype.card_pos
  have hcard' : dκ + 1 = dι := by rw [hdι, hdκ]; exact_mod_cast hcard
  have hdle : dκ ≤ dι := by linarith
  set s' := s * dκ / dι with hs'
  have hs'0 : 0 < s' := by positivity
  have hs's : s' ≤ s := by
    rw [hs', div_le_iff₀ hdι0]; exact mul_le_mul_of_nonneg_left hdle hs.le
  set c₀ := s' * v₀ with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  have hKH := isHermitian_compressFull hM U ρ
  have hB₀H := isHermitian_compress hM U
  have hclose := compress_root_close hcard hM hU hs hv₀ hm hmv hm' hm'v hρ hδ hδ₁ hδ₂
  have hδ0 : 0 ≤ δ := by
    have : 0 < 1 / v₀ := by positivity
    have h0 : 0 ≤ (1 + ‖M‖ / c₀) ^ 3 := by positivity
    by_contra hneg
    have : δ * (|ρ| - (|x| + 1 / v₀)) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hneg) (by linarith)
    linarith
  have hRT := compress_resolvent_at_root_le hM hU hs hv₀ hm hmv hc₀
    (mul_le_mul_of_nonneg_right hs's hv₀.le) hρ hδ
  set ω : ℂ := (x : ℂ) + (s : ℂ) * m with hω
  set ω' : ℂ := (x : ℂ) + (s' : ℂ) * m' with hω'
  have hmpos : 0 < m.im := hv₀.trans_le hmv
  have hωim : ω.im = s * m.im := by simp [hω, Complex.mul_im]
  have hω'im : ω'.im = s' * m'.im := by simp [hω', Complex.mul_im]
  have hcω : c₀ ≤ ω.im := by rw [hωim]; exact mul_le_mul hs's hmv hv₀.le hs.le
  have hcω' : c₀ ≤ ω'.im := by rw [hω'im]; exact mul_le_mul_of_nonneg_left hm'v hs'0.le
  have hωpos : 0 < ω.im := hc₀.trans_le hcω
  have hω'pos : 0 < ω'.im := hc₀.trans_le hcω'
  set R := (M + (ρ : ℂ) • (1 - U * Uᴴ) - ω • (1 : Matrix ι ι ℂ))⁻¹ with hR
  set R₁ := (Uᴴ * M * U - ω • (1 : Matrix κ κ ℂ))⁻¹ with hR₁
  set R₂ := (Uᴴ * M * U - ω' • (1 : Matrix κ κ ℂ))⁻¹ with hR₂
  have hRn : ‖R‖ ≤ c₀⁻¹ := by
    have := opNorm_resolvent_le hKH hωpos.ne'
    rw [abs_of_pos hωpos] at this
    exact this.trans (inv_anti₀ hc₀ hcω)
  have hR₁n : ‖R₁‖ ≤ c₀⁻¹ := by
    have := opNorm_resolvent_le hB₀H hωpos.ne'
    rw [abs_of_pos hωpos] at this
    exact this.trans (inv_anti₀ hc₀ hcω)
  have hR₂n : ‖R₂‖ ≤ c₀⁻¹ := by
    have := opNorm_resolvent_le hB₀H hω'pos.ne'
    rw [abs_of_pos hω'pos] at this
    exact this.trans (inv_anti₀ hc₀ hcω')
  have hUn := compress_opNorm_isometry_le hU
  have hUhn := compress_opNorm_isometry_adj_le hU
  -- `ω - ω' = s'(μ - m')`
  have hdκne : (dκ : ℂ) ≠ 0 := by exact_mod_cast hdκ0.ne'
  have hdιne : (dι : ℂ) ≠ 0 := by exact_mod_cast hdι0.ne'
  have hωω : ω - ω' = (s' : ℂ) * (((dι : ℂ) / dκ) * m - m') := by
    rw [hω, hω', hs']; push_cast; field_simp; ring
  have hωωn : ‖ω - ω'‖ ≤ 4 * δ / v₀ ^ 2 := by
    rw [hωω, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs'0]
    calc s' * ‖(dι : ℂ) / dκ * m - m'‖ ≤ s' * (4 * δ / (s' * v₀ ^ 2)) :=
          mul_le_mul_of_nonneg_left hclose hs'0.le
      _ = 4 * δ / v₀ ^ 2 := by field_simp
  have hR12 : ‖R₁ - R₂‖ ≤ 4 * δ / v₀ ^ 2 * (c₀⁻¹ * c₀⁻¹) := by
    rw [resolvent_sub hB₀H hωpos.ne' hω'pos.ne', norm_smul]
    exact mul_le_mul hωωn ((norm_mul_le _ _).trans (mul_le_mul hR₁n hR₂n (norm_nonneg _)
      (by positivity))) (norm_nonneg _) (by positivity)
  -- `R - T₂`, `T₂ = U R₂ U*`
  set T₂ := U * R₂ * Uᴴ with hT₂
  have hUXU : ∀ X : Matrix κ κ ℂ, ‖U * X * Uᴴ‖ ≤ ‖X‖ := by
    intro X
    calc ‖U * X * Uᴴ‖ ≤ ‖U‖ * ‖X‖ * ‖Uᴴ‖ :=
          (Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ 1 * ‖X‖ * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hUn (norm_nonneg _)) hUhn (norm_nonneg _)
            (by positivity)
      _ = ‖X‖ := by ring
  have hRT₂ : ‖R - T₂‖ ≤ δ * (1 + 4 / (v₀ ^ 2 * c₀ ^ 2)) := by
    have e : R - T₂ = (R - U * R₁ * Uᴴ) + U * (R₁ - R₂) * Uᴴ := by
      rw [hT₂, Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h2 := (hUXU (R₁ - R₂)).trans hR12
    have : 4 * δ / v₀ ^ 2 * (c₀⁻¹ * c₀⁻¹) = δ * (4 / (v₀ ^ 2 * c₀ ^ 2)) := by
      field_simp
    linarith
  have hT₂n : ‖T₂‖ ≤ c₀⁻¹ := (hUXU R₂).trans hR₂n
  -- `RR* - T₂T₂*`
  have hsq : ‖R * Rᴴ - T₂ * T₂ᴴ‖ ≤ 2 * c₀⁻¹ * (δ * (1 + 4 / (v₀ ^ 2 * c₀ ^ 2))) := by
    have e : R * Rᴴ - T₂ * T₂ᴴ = (R - T₂) * Rᴴ + T₂ * (R - T₂)ᴴ := by
      rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(R - T₂) * Rᴴ‖ ≤ ‖R - T₂‖ * c₀⁻¹ := by
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [Matrix.l2_opNorm_conjTranspose]; exact hRn
    have h2 : ‖T₂ * (R - T₂)ᴴ‖ ≤ c₀⁻¹ * ‖R - T₂‖ := by
      refine (norm_mul_le _ _).trans (mul_le_mul hT₂n ?_ (norm_nonneg _) (by positivity))
      rw [Matrix.l2_opNorm_conjTranspose]
    have hc0i : 0 ≤ c₀⁻¹ := by positivity
    calc ‖(R - T₂) * Rᴴ‖ + ‖T₂ * (R - T₂)ᴴ‖ ≤ ‖R - T₂‖ * c₀⁻¹ + c₀⁻¹ * ‖R - T₂‖ :=
          add_le_add h1 h2
      _ = 2 * c₀⁻¹ * ‖R - T₂‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hRT₂ (by positivity)
  -- the compressed centre is a full trace
  have hT₂T : T₂ * T₂ᴴ = U * (R₂ * R₂ᴴ) * Uᴴ := by
    rw [hT₂, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  have hcomp : (dκ : ℂ)⁻¹ * (Uᴴ * J * U * ((s' : ℂ) • (R₂ * R₂ᴴ))).trace =
      (dι : ℂ)⁻¹ * (s : ℂ) * (J * (T₂ * T₂ᴴ)).trace := by
    rw [Matrix.mul_smul, trace_smul, hT₂T, smul_eq_mul]
    have htr : (Uᴴ * J * U * (R₂ * R₂ᴴ)).trace = (J * (U * (R₂ * R₂ᴴ) * Uᴴ)).trace := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [htr, hs']; push_cast; field_simp
  have hfull : (dι : ℂ)⁻¹ * (J * ((s : ℂ) • (R * Rᴴ))).trace =
      (dι : ℂ)⁻¹ * (s : ℂ) * (J * (R * Rᴴ)).trace := by
    rw [Matrix.mul_smul, trace_smul, smul_eq_mul]; ring
  have hdιc : ((dι : ℝ) : ℂ) = (Fintype.card ι : ℂ) := Complex.ofReal_natCast _
  have hdκc : ((dκ : ℝ) : ℂ) = (Fintype.card κ : ℂ) := Complex.ofReal_natCast _
  rw [← hdιc, ← hdκc, hfull, hcomp, ← mul_sub, ← trace_sub, ← Matrix.mul_sub, norm_mul,
    norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hdι0, abs_of_pos hs]
  have htr := compress_norm_trace_le (J * (R * Rᴴ - T₂ * T₂ᴴ))
  rw [← hdι] at htr
  have hJX : ‖J * (R * Rᴴ - T₂ * T₂ᴴ)‖ ≤ ‖R * Rᴴ - T₂ * T₂ᴴ‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right hJ (norm_nonneg _)).trans
      (one_mul _).le)
  calc dι⁻¹ * s * ‖(J * (R * Rᴴ - T₂ * T₂ᴴ)).trace‖
      ≤ dι⁻¹ * s * (dι * ‖R * Rᴴ - T₂ * T₂ᴴ‖) :=
        mul_le_mul_of_nonneg_left (htr.trans (mul_le_mul_of_nonneg_left hJX hdι0.le))
          (by positivity)
    _ = s * ‖R * Rᴴ - T₂ * T₂ᴴ‖ := by field_simp
    _ ≤ s * (2 * c₀⁻¹ * (δ * (1 + 4 / (v₀ ^ 2 * c₀ ^ 2)))) := mul_le_mul_of_nonneg_left hsq hs.le
    _ = 2 * s / c₀ * (1 + 4 / (v₀ ^ 2 * c₀ ^ 2)) * δ := by field_simp

end Generic

/-!
## The pair form
-/

section Pair

variable {p : Parameters} {i : ZMod p.n}

/-- The compressed real-axis window centre on `Fin (2W - 1)`:
`(2W - 1)⁻¹ Tr(J' Γ'(x))`, `Γ' = s'|B - x - s'm'|⁻²`, `m' = freshDyson B s' x` (the centre of the
compressed window estimate; `s' = s(1 - 1/(2W))` in the application). -/
def compressCentre (p : Parameters) (J' B : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ)
    (s' x : ℝ) : ℂ :=
  ((2 * p.W - 1 : ℕ) : ℂ)⁻¹ * (J' * ((s' : ℂ) •
    ((B - ((x : ℂ) + (s' : ℂ) * freshDyson B s' x) • (1 : Matrix (Fin (2 * p.W - 1))
        (Fin (2 * p.W - 1)) ℂ))⁻¹ *
      ((B - ((x : ℂ) + (s' : ℂ) * freshDyson B s' x) • (1 : Matrix (Fin (2 * p.W - 1))
        (Fin (2 * p.W - 1)) ℂ))⁻¹)ᴴ))).trace

theorem card_pairSite_cc : Fintype.card (PairSite p i) = 2 * p.W := by
  rw [Fintype.card_congr (BlockBand.LocalWindow.LawBridge.pairEquiv p i), Fintype.card_fin]

/-- **The window centre `j_B(E, λ)` of a pole deformation is the compressed centre up to
`O(1/|ρ|)`**. For a Hermitian pair matrix `M`, an
isometry `U : ℂ^{2W-1} → ℂ^{pair}` (`U*U = 1`, so `1 - UU* = ww*` for the unit `w ⊥ ran U`),
`K = M + ρ(1 - UU*)`, `s > 0`, `s' = s(1 - 1/(2W))`, real `x` with Dyson roots `m` of `K`
(variance `s`) and `m'` of `U*MU` (variance `s'`), `Im m, Im m' ≥ v₀ > 0`, a pair contraction `J`
and `δ = (1 + ‖M‖/(s'v₀))³/(|ρ| - |x| - 1/v₀)` with `|ρ| > |x| + 1/v₀`, `4δ ≤ v₀`,
`2δ ≤ s'v₀³`: `‖pairCentre J K s x - compressCentre (U*JU) (U*MU) s' x‖ ≤
(2s/(s'v₀))(1 + 4/(v₀²(s'v₀)²)) δ`. -/
theorem pairCentre_compress_close {M : PairMatrix p i} (hM : M.IsHermitian)
    {U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ} (hU : Uᴴ * U = 1) {ρ s x v₀ : ℝ}
    (hs : 0 < s) (hv₀ : 0 < v₀) {m m' : ℂ}
    (hm : IsDysonRoot (M + (ρ : ℂ) • (1 - U * Uᴴ)) s (x : ℂ) m) (hmv : v₀ ≤ m.im)
    (hm' : IsDysonRoot (Uᴴ * M * U) (s * (1 - 1 / (2 * (p.W : ℝ)))) (x : ℂ) m')
    (hm'v : v₀ ≤ m'.im) (hρ : |x| + 1 / v₀ < |ρ|)
    (hδ₁ : 4 * ((1 + ‖M‖ / (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀)) ^ 3 /
      (|ρ| - (|x| + 1 / v₀))) ≤ v₀)
    (hδ₂ : 2 * ((1 + ‖M‖ / (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀)) ^ 3 /
      (|ρ| - (|x| + 1 / v₀))) ≤ s * (1 - 1 / (2 * (p.W : ℝ))) * v₀ ^ 3)
    {J : PairMatrix p i} (hJ : ‖J‖ ≤ 1) :
    ‖pairCentre J (M + (ρ : ℂ) • (1 - U * Uᴴ)) s x -
        compressCentre p (Uᴴ * J * U) (Uᴴ * M * U) (s * (1 - 1 / (2 * (p.W : ℝ)))) x‖ ≤
      2 * s / (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀) *
        (1 + 4 / (v₀ ^ 2 * (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀) ^ 2)) *
        ((1 + ‖M‖ / (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀)) ^ 3 / (|ρ| - (|x| + 1 / v₀))) := by
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW1 : 1 ≤ 2 * p.W := by have := p.W_pos; omega
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  have : NeZero (2 * p.W - 1) := ⟨by have := p.W_pos; omega⟩
  have : Nonempty (Fin (2 * p.W - 1)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  have hcard : Fintype.card (Fin (2 * p.W - 1)) + 1 = Fintype.card (PairSite p i) := by
    rw [Fintype.card_fin, card_pairSite_cc]; omega
  have hsv : s * (Fintype.card (Fin (2 * p.W - 1)) : ℝ) / (Fintype.card (PairSite p i) : ℝ) =
      s * (1 - 1 / (2 * (p.W : ℝ))) := by
    rw [Fintype.card_fin, card_pairSite_cc, Nat.cast_sub hW1]
    push_cast
    field_simp
  have hs'0 : 0 < s * (1 - 1 / (2 * (p.W : ℝ))) := by
    have h2 : 1 / (2 * (p.W : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    exact mul_pos hs (by linarith)
  set s' := s * (1 - 1 / (2 * (p.W : ℝ))) with hs'
  set δ := (1 + ‖M‖ / (s' * v₀)) ^ 3 / (|ρ| - (|x| + 1 / v₀)) with hδdef
  have hpos : 0 < |ρ| - (|x| + 1 / v₀) := by linarith
  have hδ : (1 + ‖M‖ / (s' * v₀)) ^ 3 ≤ δ * (|ρ| - (|x| + 1 / v₀)) := by
    rw [hδdef, div_mul_cancel₀ _ hpos.ne']
  have hm'' : IsDysonRoot (Uᴴ * M * U)
      (s * (Fintype.card (Fin (2 * p.W - 1)) : ℝ) / (Fintype.card (PairSite p i) : ℝ))
      (x : ℂ) m' := by rw [hsv]; exact hm'
  have h := compress_centre_close hcard hM hU hs hv₀ hm hmv hm'' hm'v hρ
    (by rw [hsv]; exact hδ) hδ₁ (by rw [hsv]; exact hδ₂) hJ
  rw [hsv] at h
  -- identify the two centres
  have hKH := isHermitian_compressFull hM U ρ
  have hB₀H := isHermitian_compress hM U
  have hpd : BlockBand.LocalWindow.pairDyson p i (M + (ρ : ℂ) • (1 - U * Uᴴ)) s x = m :=
    pairDyson_eq_of_isDysonRoot p i hKH hs (by simp) hm
  have hfd : freshDyson (Uᴴ * M * U) s' x = m' :=
    freshDyson_eq_of_isDysonRoot hB₀H hs'0 (by simp) hm'
  have e1 : pairCentre J (M + (ρ : ℂ) • (1 - U * Uᴴ)) s x =
      (Fintype.card (PairSite p i) : ℂ)⁻¹ * (J * ((s : ℂ) •
        ((M + (ρ : ℂ) • (1 - U * Uᴴ) - ((x : ℂ) + (s : ℂ) * m) • (1 : PairMatrix p i))⁻¹ *
          ((M + (ρ : ℂ) • (1 - U * Uᴴ) -
            ((x : ℂ) + (s : ℂ) * m) • (1 : PairMatrix p i))⁻¹)ᴴ))).trace := by
    unfold pairCentre
    rw [windowGamma_eq, hpd, card_pairSite_cc]
    push_cast
    rfl
  have e2 : compressCentre p (Uᴴ * J * U) (Uᴴ * M * U) s' x =
      (Fintype.card (Fin (2 * p.W - 1)) : ℂ)⁻¹ * (Uᴴ * J * U * ((s' : ℂ) •
        ((Uᴴ * M * U - ((x : ℂ) + (s' : ℂ) * m') • (1 : Matrix (Fin (2 * p.W - 1))
            (Fin (2 * p.W - 1)) ℂ))⁻¹ *
          ((Uᴴ * M * U - ((x : ℂ) + (s' : ℂ) * m') • (1 : Matrix (Fin (2 * p.W - 1))
            (Fin (2 * p.W - 1)) ℂ))⁻¹)ᴴ))).trace := by
    unfold compressCentre
    rw [hfd, Fintype.card_fin]
  rw [e1, e2]
  exact h

end Pair

end BlockBand.LocalWindow.ProofPartTwo
