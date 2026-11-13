module

public import BlockBand.DeterminantScore.Statements

/-!
# Weighted energies of the spread tests

Dropping the Gaussian term in the weighted spectral variance and using `Σ_j λ_j⁻⁴ ≤ U²` gives
`Var √U ≤ ½E U`, `Var U^{-1/2} ≤ ½E U⁻¹`, `Var log U ≤ 2`.

On the eigenvalue side `U = invSqSum λ = Σ_j λ_j⁻²`. For `φ` differentiable at `U(λ)` with
derivative `d` and all `λ_j ≠ 0`, `t > 0`:
`weightedEnergy t (φ ∘ U) λ ≤ 2d²U(λ)²` (`weightedEnergy_comp_le`), since
`∂_j(φ∘U) = -2dλ_j⁻³`, `4d²λ_j⁻⁶/(t⁻¹ + 2λ_j⁻²) ≤ 2d²λ_j⁻⁴` and `Σ_jλ_j⁻⁴ ≤ U²`.
The four tests `√U`, `√(U⁻¹)`, `log U`, `log U⁻¹` give the energies `U/2`, `U⁻¹/2`, `2`, `2`
(`weightedEnergy_sqrt_le`, …). Smoothness on the chamber: `contDiffOn_comp_invSqSum`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.NegativeSpread

open BlockBand.DeterminantScore
open scoped ContDiff

variable {m : ℕ}

/-- `U(λ) = Σ_j λ_j⁻²`. -/
def invSqSum (lam : Fin m → ℝ) : ℝ := ∑ j, (lam j)⁻¹ ^ 2

theorem invSqSum_nonneg (lam : Fin m → ℝ) : 0 ≤ invSqSum lam :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem invSqSum_pos {lam : Fin m → ℝ} (hlam : ∀ j, lam j ≠ 0) (j : Fin m) :
    0 < invSqSum lam :=
  lt_of_lt_of_le (by have := hlam j; positivity)
    (Finset.single_le_sum (f := fun k => (lam k)⁻¹ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j))

theorem sq_le_invSqSum (lam : Fin m → ℝ) (j : Fin m) : (lam j)⁻¹ ^ 2 ≤ invSqSum lam :=
  Finset.single_le_sum (f := fun k => (lam k)⁻¹ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)

theorem measurable_invSqSum : Measurable (invSqSum (m := m)) :=
  Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).inv).pow_const 2

/-- Points of the chamber have no zero coordinate. -/
theorem ne_zero_of_mem_chamber {ℓ : ℕ} {lam : Fin m → ℝ} (h : lam ∈ chamber m ℓ) (j : Fin m) :
    lam j ≠ 0 := by
  obtain ⟨-, h⟩ := h
  rcases lt_or_ge j.val ℓ with hj | hj
  · exact ((h j).1 hj).ne
  · exact ((h j).2 hj).ne'

theorem hasFDerivAt_invSqSum {lam : Fin m → ℝ} (hlam : ∀ j, lam j ≠ 0) :
    HasFDerivAt invSqSum (∑ k, (-2 * (lam k)⁻¹ ^ 3) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k) lam := by
  unfold invSqSum
  refine HasFDerivAt.fun_sum fun k _ => ?_
  have h1 : HasDerivAt (fun y : ℝ => y⁻¹ ^ 2) (-2 * (lam k)⁻¹ ^ 3) (lam k) := by
    have h := (hasDerivAt_inv (hlam k)).fun_pow 2
    convert h using 1
    have := hlam k
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp
  exact h1.comp_hasFDerivAt lam (hasFDerivAt_apply (𝕜 := ℝ) k lam)

theorem fderiv_invSqSum_single {lam : Fin m → ℝ} (hlam : ∀ j, lam j ≠ 0) (j : Fin m) :
    fderiv ℝ invSqSum lam (Pi.single j 1) = -2 * (lam j)⁻¹ ^ 3 := by
  rw [(hasFDerivAt_invSqSum hlam).fderiv]
  simp [Pi.single_apply]

/-- `weightedEnergy t (φ ∘ U) λ ≤ 2 d² U(λ)²`. -/
theorem weightedEnergy_comp_le {t : ℝ} (ht : 0 < t) {lam : Fin m → ℝ} (hlam : ∀ j, lam j ≠ 0)
    {φ : ℝ → ℝ} {d : ℝ} (hφ : HasDerivAt φ d (invSqSum lam)) :
    weightedEnergy t (fun y => φ (invSqSum y)) lam ≤ 2 * d ^ 2 * invSqSum lam ^ 2 := by
  have hF : HasFDerivAt (fun y => φ (invSqSum y)) (d • fderiv ℝ invSqSum lam) lam := by
    have := hφ.comp_hasFDerivAt lam (hasFDerivAt_invSqSum hlam)
    rw [(hasFDerivAt_invSqSum hlam).fderiv]
    exact this
  unfold weightedEnergy
  rw [hF.fderiv]
  have hterm : ∀ j : Fin m, ((d • fderiv ℝ invSqSum lam) (Pi.single j 1)) ^ 2 /
      (t⁻¹ + 2 / lam j ^ 2) ≤ 2 * d ^ 2 * ((lam j)⁻¹ ^ 2) ^ 2 := by
    intro j
    have hv : (d • fderiv ℝ invSqSum lam) (Pi.single j 1) = d * (-2 * (lam j)⁻¹ ^ 3) := by
      rw [← fderiv_invSqSum_single hlam j]; rfl
    rw [hv]
    have hj := hlam j
    have hti : 0 ≤ t⁻¹ := inv_nonneg.2 ht.le
    have hden : 0 < t⁻¹ + 2 / lam j ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have hy : 2 / lam j ^ 2 = 2 * ((lam j)⁻¹) ^ 2 := by field_simp
    rw [hy]
    have h0 : 0 ≤ 2 * d ^ 2 * ((lam j)⁻¹ ^ 2) ^ 2 * t⁻¹ := by positivity
    nlinarith [h0]
  calc ∑ j, ((d • fderiv ℝ invSqSum lam) (Pi.single j 1)) ^ 2 / (t⁻¹ + 2 / lam j ^ 2)
      ≤ ∑ j, 2 * d ^ 2 * ((lam j)⁻¹ ^ 2) ^ 2 := Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * d ^ 2 * ∑ j, ((lam j)⁻¹ ^ 2) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * d ^ 2 * invSqSum lam ^ 2 := by
      gcongr
      rw [sq (invSqSum lam), invSqSum, Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [sq ((lam j)⁻¹ ^ 2)]
      exact mul_le_mul_of_nonneg_left (sq_le_invSqSum lam j) (sq_nonneg _)

section Tests

variable {t : ℝ} (ht : 0 < t) {lam : Fin m → ℝ} (hlam : ∀ j, lam j ≠ 0) (j₀ : Fin m)
include ht hlam j₀

theorem weightedEnergy_sqrt_le :
    weightedEnergy t (fun y => Real.sqrt (invSqSum y)) lam ≤ invSqSum lam / 2 := by
  have hU := invSqSum_pos hlam j₀
  refine (weightedEnergy_comp_le ht hlam (Real.hasDerivAt_sqrt hU.ne')).trans_eq ?_
  have hs := Real.sq_sqrt hU.le
  rw [div_pow, mul_pow, hs]
  field_simp

theorem weightedEnergy_sqrt_inv_le :
    weightedEnergy t (fun y => Real.sqrt (invSqSum y)⁻¹) lam ≤ (invSqSum lam)⁻¹ / 2 := by
  have hU := invSqSum_pos hlam j₀
  have hd : HasDerivAt (fun y : ℝ => Real.sqrt y⁻¹)
      (1 / (2 * Real.sqrt (invSqSum lam)⁻¹) * (-(invSqSum lam ^ 2)⁻¹)) (invSqSum lam) :=
    (Real.hasDerivAt_sqrt (inv_pos.2 hU).ne').comp _ (hasDerivAt_inv hU.ne')
  refine (weightedEnergy_comp_le ht hlam hd).trans_eq ?_
  have hs := Real.sq_sqrt (inv_pos.2 hU).le
  rw [div_mul_eq_mul_div, one_mul, div_pow, mul_pow, hs]
  field_simp

theorem weightedEnergy_log_le :
    weightedEnergy t (fun y => Real.log (invSqSum y)) lam ≤ 2 := by
  have hU := invSqSum_pos hlam j₀
  refine (weightedEnergy_comp_le ht hlam (Real.hasDerivAt_log hU.ne')).trans_eq ?_
  field_simp

theorem weightedEnergy_log_inv_le :
    weightedEnergy t (fun y => Real.log (invSqSum y)⁻¹) lam ≤ 2 := by
  have hU := invSqSum_pos hlam j₀
  have hd : HasDerivAt (fun y : ℝ => Real.log y⁻¹)
      ((invSqSum lam)⁻¹⁻¹ * (-(invSqSum lam ^ 2)⁻¹)) (invSqSum lam) :=
    (Real.hasDerivAt_log (inv_pos.2 hU).ne').comp _ (hasDerivAt_inv hU.ne')
  refine (weightedEnergy_comp_le ht hlam hd).trans_eq ?_
  field_simp

end Tests

theorem contDiffAt_invSqSum {lam : Fin m → ℝ} (hlam : ∀ j, lam j ≠ 0) :
    ContDiffAt ℝ ∞ invSqSum lam := by
  unfold invSqSum
  refine ContDiffAt.sum fun k _ => ?_
  exact ((contDiffAt_inv ℝ (hlam k)).comp lam (contDiff_apply ℝ ℝ k).contDiffAt).pow 2

/-- A test `φ ∘ U` is smooth on the chamber when `φ` is smooth on `(0, ∞)`. -/
theorem contDiffOn_comp_invSqSum {ℓ : ℕ} (hm : 0 < m) {φ : ℝ → ℝ}
    (hφ : ∀ y : ℝ, 0 < y → ContDiffAt ℝ ∞ φ y) :
    ContDiffOn ℝ ∞ (fun y => φ (invSqSum y)) (chamber m ℓ) := fun lam hlam => by
  have hne := ne_zero_of_mem_chamber hlam
  exact ((hφ _ (invSqSum_pos hne ⟨0, hm⟩)).comp lam (contDiffAt_invSqSum hne)).contDiffWithinAt

end BlockBand.DeterminantScore.NegativeSpread
