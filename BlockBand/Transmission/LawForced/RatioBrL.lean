module

public import BlockBand.Transmission.LawForced.RatioBrQ

/-!
# The `κ ≡ 0` one-layer brackets: the deterministic terms and the total

Notation of `RatioBrQ`, plus `y = a·g`, `c = (1 + y)⁻¹` (`meanC_eq`), `‖Ū − c‖ ≤ U_a`,
`G = gW hT Λ` and `L_w = ‖Tr(GŪ) − c·Tr G‖` (what part (b) of `ubarMean_bulk` bounds).
* `meanC_scalar`: `0 ≤ 1 − c ≤ y`, `|1 − c − y| ≤ y²`;
* `linB_bracket_le`: `|linB B̄ − y·ΣtΛ| ≤ L_w + y²Λ̂g`, and `|linB B̄| ≤ L_w + yΛ̂g`;
* `quadB_bracket_le`: `|quadB B̄| ≤ quadK·(U_a + y)²g`;
* **`ratioBr_le`**: `ratioBr ≤ ratioBrBd` (all five brackets).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {p W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}

/-- The bound on the five brackets. -/
def ratioBrBd (z : DualCoord p) (g y Lw Ua ε S τ hs : ℝ) : ℝ :=
  Lw + y ^ 2 * (lamHat z * g) + quadK z * ((Ua + y) ^ 2 * g) + (Lw + y * (lamHat z * g)) ^ 2 / 2 +
    quadK z * (ε * g ^ 2 + S * ((1 + lamHat z) * τ) ^ 2) +
    (S * lamHat z ^ 2 * hs ^ 2 + ε * lamHat z ^ 2 * g ^ 2) / 2

theorem meanC_scalar {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ 1 - (1 + y)⁻¹ ∧ 1 - (1 + y)⁻¹ ≤ y ∧ |1 - (1 + y)⁻¹ - y| ≤ y ^ 2 := by
  have hp : 0 < 1 + y := by linarith
  have e : 1 - (1 + y)⁻¹ = y * (1 + y)⁻¹ := by
    have := mul_inv_cancel₀ hp.ne'
    linear_combination -this
  have hi : (1 + y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hi0 : 0 < (1 + y)⁻¹ := inv_pos.2 hp
  have e2 : 1 - (1 + y)⁻¹ - y = -(y ^ 2 * (1 + y)⁻¹) := by
    have := mul_inv_cancel₀ hp.ne'
    linear_combination (y - 1) * this
  refine ⟨by rw [e]; positivity, by rw [e]; nlinarith, ?_⟩
  rw [e2, abs_neg, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg y]

theorem linB_bracket_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (ht1 : ∀ i, ts_lam hT i ≤ 1) (Ub : Matrix (Fin W) (Fin W) ℂ) {a : ℝ} (ha : 0 ≤ a) :
    |linB z (ts_lam hT) (sand hT Ub - dmat (ts_lam hT)) -
        a * ((∑ k, ts_lam hT k) * ∑ k, ts_lam hT k * dualLam z (ts_lam hT k))| ≤
      ‖((gW hT fun k => dualLam z (ts_lam hT k)) * Ub).trace -
          (((1 + a * T.trace.re)⁻¹ : ℝ) : ℂ) * (gW hT fun k => dualLam z (ts_lam hT k)).trace‖ +
        (a * T.trace.re) ^ 2 * (lamHat z * T.trace.re) ∧
    |linB z (ts_lam hT) (sand hT Ub - dmat (ts_lam hT))| ≤
      ‖((gW hT fun k => dualLam z (ts_lam hT k)) * Ub).trace -
          (((1 + a * T.trace.re)⁻¹ : ℝ) : ℂ) * (gW hT fun k => dualLam z (ts_lam hT k)).trace‖ +
        a * T.trace.re * (lamHat z * T.trace.re) := by
  set t := ts_lam hT
  have ht0 := ts_lam_nonneg hT
  have hg : ∑ k, t k = T.trace.re := ts_sum_lam hT
  have hg0 : 0 ≤ T.trace.re := by rw [← hg]; exact Finset.sum_nonneg fun k _ => ht0 k
  set y := a * T.trace.re
  have hy : 0 ≤ y := mul_nonneg ha hg0
  obtain ⟨c0, c1, c2⟩ := meanC_scalar hy
  obtain ⟨s0, s1⟩ := sum_t_dualLam_le hz ht0 ht1
  rw [hg] at s1
  have h := abs_linB_mean_sub_le z hT Ub (1 + y)⁻¹
  set L := linB z t (sand hT Ub - dmat t)
  set sl := ∑ k, t k * dualLam z (t k)
  rw [hg]
  have e : L - a * (T.trace.re * sl) = (L - (1 - (1 + y)⁻¹) * sl) + (1 - (1 + y)⁻¹ - y) * sl := by
    simp only [y]; ring
  refine ⟨?_, ?_⟩
  · rw [e]
    refine (abs_add_le _ _).trans (add_le_add h ?_)
    rw [abs_mul, abs_of_nonneg s0]
    exact mul_le_mul c2 s1 s0 (sq_nonneg _)
  · have e' : L = (L - (1 - (1 + y)⁻¹) * sl) + (1 - (1 + y)⁻¹) * sl := by ring
    rw [e']
    refine (abs_add_le _ _).trans (add_le_add h ?_)
    rw [abs_of_nonneg (mul_nonneg c0 s0)]
    exact mul_le_mul c1 s1 s0 hy

theorem quadB_bracket_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (ht1 : ∀ i, ts_lam hT i ≤ 1) (Ub : Matrix (Fin W) (Fin W) ℂ) {c Ua : ℝ} (hc0 : 0 ≤ 1 - c)
    (hUa : ‖Ub - (c : ℂ) • 1‖ ≤ Ua) :
    |quadB z (ts_lam hT) (sand hT Ub - dmat (ts_lam hT))| ≤
      quadK z * ((Ua + (1 - c)) ^ 2 * T.trace.re) := by
  have ht0 := ts_lam_nonneg hT
  have h := abs_quadR_le hz (S := sand hT Ub) ht0 ht1
  rw [quadR_eq_quadB] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (quadK_nonneg z))
  have hD : dmat (ts_lam hT) = sand hT 1 := by rw [sand_one]; rfl
  rw [hD, ← sand_sub]
  refine (frobSq_sand_le hT ht1 _).trans ?_
  have hg0 : 0 ≤ T.trace.re := by
    rw [← ts_sum_lam hT]; exact Finset.sum_nonneg fun k _ => ht0 k
  have hn : ‖Ub - 1‖ ≤ Ua + (1 - c) := by
    have e : Ub - 1 = (Ub - (c : ℂ) • 1) + ((c - 1 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
      push_cast; rw [sub_smul, one_smul]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add hUa ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hc0]
    exact mul_le_of_le_one_right hc0 PassiveLayer.norm_one_le'
  have := pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact mul_le_mul_of_nonneg_right this hg0

/-- **All five brackets.** -/
theorem ratioBr_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (ht1 : ∀ i, ts_lam hT i ≤ 1) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (f : Matrix (Fin W) (Fin W) ℂ) {a : ℝ} (ha : 0 ≤ a) (σ σ' : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      ((a : ℂ) * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) {Ua : ℝ}
    (hUa : ‖matrixExpect μ U - (((1 + a * T.trace.re)⁻¹ : ℝ) : ℂ) • 1‖ ≤ Ua) :
    ratioBr μ hT U z a ≤ ratioBrBd z T.trace.re (a * T.trace.re)
      ‖((gW hT fun k => dualLam z (ts_lam hT k)) * matrixExpect μ U).trace -
          (((1 + a * T.trace.re)⁻¹ : ℝ) : ℂ) * (gW hT fun k => dualLam z (ts_lam hT k)).trace‖
      Ua ε (‖σ‖ + ‖σ'‖) (‖(T * f).trace‖ + Real.sqrt T.trace.re * hsSandwich T f)
      (hsSandwich T f) := by
  have ht0 := ts_lam_nonneg hT
  have hg0 : 0 ≤ T.trace.re := by
    rw [← ts_sum_lam hT]; exact Finset.sum_nonneg fun k _ => ht0 k
  have hy : 0 ≤ a * T.trace.re := mul_nonneg ha hg0
  obtain ⟨c0, c1, -⟩ := meanC_scalar hy
  have hUa0 : 0 ≤ Ua := (norm_nonneg _).trans hUa
  obtain ⟨l1, l2⟩ := linB_bracket_le hz hT ht1 (matrixExpect μ U) ha
  have q1 := quadB_bracket_le hz hT ht1 (matrixExpect μ U) c0 hUa
  have q2 := quadMean_sub_le hz hT ht1 U f a σ σ' hcov
  have q3 := covV_sub_le hz hT ht1 U f a σ σ' hcov
  have hsq : (Ua + (1 - (1 + a * T.trace.re)⁻¹)) ^ 2 * T.trace.re ≤
      (Ua + a * T.trace.re) ^ 2 * T.trace.re :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) 2) hg0
  have l3 := pow_le_pow_left₀ (abs_nonneg _) l2 2
  rw [sq_abs] at l3
  unfold ratioBr ratioBrBd
  have := mul_le_mul_of_nonneg_left hsq (quadK_nonneg z)
  linarith

end BlockBand.Transmission.LawForced
