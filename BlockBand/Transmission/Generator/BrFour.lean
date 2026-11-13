module

public import BlockBand.Transmission.Generator.BrMean

/-!
# One-layer fourth moment of the increment (input of `PowerModulusAlong`)

* `eLpNorm_brLin_le`: `‖λ_k(Z)‖_p ≤ B·Tr T` from bilinear bounds `‖u*Zv‖_p ≤ B|u||v|` (Minkowski
  over the eigenbasis, `k ≥ 1`);
* `pow_four_add3_le`: `(a+b+c)⁴ ≤ 27(a⁴+b⁴+c⁴)`;
* **`br_four`**: `E Δ_{k+1}⁴ ≤ 27((k+1)⁴L₄ + ((k+1)νg)⁴ + 128c_k⁴(H₈ + (ν²g)⁴))` for
  `E|λ_{k+1}(Z)|⁴ ≤ L₄`, `E h⁴ ≤ H₈`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Internal.Contracts.Layers
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Minkowski for `λ_k`.** -/
theorem eLpNorm_brLin_le (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) {k : ℕ} (hk : 1 ≤ k)
    (Z : Ω → Matrix (Fin W) (Fin W) ℂ) {p : ℝ≥0∞} (hp : 1 ≤ p) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (Z ω) v) p μ ≤
      ENNReal.ofReal (B * vecNorm u * vecNorm v)) :
    eLpNorm (fun ω => brLin hT k (Z ω)) p μ ≤ ENNReal.ofReal (B * T.trace.re) := by
  have e : (fun ω => brLin hT k (Z ω)) =
      ∑ i, ((ts_lam hT i ^ k : ℝ) : ℂ) • fun ω => ts_ent hT (Z ω) i i := by
    funext ω; simp [brLin, Finset.sum_apply]
  rw [e]
  refine (eLpNorm_sum_le hp).trans ?_
  have hterm : ∀ i, eLpNorm (((ts_lam hT i ^ k : ℝ) : ℂ) • fun ω => ts_ent hT (Z ω) i i) p μ ≤
      ENNReal.ofReal (ts_lam hT i * B) := fun i => by
    rw [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (ts_lam_nonneg hT i) k)]
    have h := hB (ts_vec hT i) (ts_vec hT i)
    rw [ts_vecNorm, mul_one, mul_one] at h
    calc ENNReal.ofReal (ts_lam hT i ^ k) * eLpNorm (fun ω => ts_ent hT (Z ω) i i) p μ ≤
        ENNReal.ofReal (ts_lam hT i) * ENNReal.ofReal B := by
          gcongr
          · exact pow_le_of_le_one (ts_lam_nonneg hT i) (ht1 i) (by omega)
          · exact h
      _ = ENNReal.ofReal (ts_lam hT i * B) := (ENNReal.ofReal_mul (ts_lam_nonneg hT i)).symm
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (ts_lam_nonneg hT i) hB0,
    ← Finset.sum_mul, ts_sum_lam hT, mul_comm]

theorem pow_four_add3_le (a b c : ℝ) : (a + b + c) ^ 4 ≤ 27 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  have h2 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have h4 : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ 3 * (a ^ 4 + b ^ 4 + c ^ 4) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - c ^ 2)]
  have h0 : 0 ≤ (a + b + c) ^ 2 := sq_nonneg _
  calc (a + b + c) ^ 4 = ((a + b + c) ^ 2) ^ 2 := by ring
    _ ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h2 2
    _ = 9 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by ring
    _ ≤ 9 * (3 * (a ^ 4 + b ^ 4 + c ^ 4)) := by linarith
    _ = _ := by ring

theorem br_four_point {Δ x bb R h n c B L : ℝ} (hΔ : Δ = x + bb + R) (hx : |x| ≤ L)
    (hb : |bb| ≤ B) (hR : |R| ≤ c * (2 * h + 2 * n)) :
    Δ ^ 4 ≤ 27 * (L ^ 4 + B ^ 4 + 128 * c ^ 4 * (h ^ 4 + n ^ 4)) := by
  have p4 : ∀ {y Y : ℝ}, |y| ≤ Y → y ^ 4 ≤ Y ^ 4 := fun {y Y} hy => by
    have := pow_le_pow_left₀ (abs_nonneg y) hy 4
    rwa [show |y| ^ 4 = y ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
      at this
  have hR4 := p4 hR
  have hhn : (h + n) ^ 4 ≤ 8 * (h ^ 4 + n ^ 4) := by
    have a : (h + n) ^ 2 ≤ 2 * (h ^ 2 + n ^ 2) := by nlinarith [sq_nonneg (h - n)]
    have b : (h ^ 2 + n ^ 2) ^ 2 ≤ 2 * (h ^ 4 + n ^ 4) := by nlinarith [sq_nonneg (h ^ 2 - n ^ 2)]
    calc (h + n) ^ 4 = ((h + n) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (h ^ 2 + n ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) a 2
      _ = 4 * (h ^ 2 + n ^ 2) ^ 2 := by ring
      _ ≤ 4 * (2 * (h ^ 4 + n ^ 4)) := by linarith
      _ = _ := by ring
  have e : (c * (2 * h + 2 * n)) ^ 4 = 16 * c ^ 4 * (h + n) ^ 4 := by ring
  rw [e] at hR4
  have hc4 : 0 ≤ 16 * c ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_left hhn hc4
  rw [hΔ]
  refine (pow_four_add3_le x bb R).trans ?_
  have := p4 hx
  have := p4 hb
  nlinarith

/-- The first-order remainder about `D`, pointwise. -/
theorem br_rem_le (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    {U Ub : Matrix (Fin W) (Fin W) ℂ} (hS : ‖sand hT U‖ ≤ 1) {ν : ℝ} (hν : ‖Ub - 1‖ ≤ ν)
    (m : ℕ) :
    |brInc hT (m + 1) U - ((m + 1 : ℕ) : ℝ) * (brLin hT (m + 1) (U - Ub)).re -
      ((m + 1 : ℕ) : ℝ) * (brLin hT (m + 1) (Ub - 1)).re| ≤
      ((m + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (m + 1)) *
        (2 * frobSq (sand hT (U - Ub)) + 2 * (ν ^ 2 * T.trace.re)) := by
  have hg : 0 ≤ T.trace.re := by
    rw [← ts_sum_lam hT]; exact Finset.sum_nonneg fun i _ => ts_lam_nonneg hT i
  have hfb : frobSq (sand hT (Ub - 1)) ≤ ν ^ 2 * T.trace.re :=
    (frobSq_sand_le hT ht1 _).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hν 2) hg)
  have h := br_expand hT ht1 U hS m
  have e : U - 1 = (U - Ub) + (Ub - 1) := by abel
  rw [e, brLin_add, Complex.add_re, sand_add] at h
  have hf := frobSq_add_le (sand hT (U - Ub)) (sand hT (Ub - 1))
  have hc : 0 ≤ ((m + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (m + 1)) := by positivity
  refine le_trans (le_of_eq ?_) (h.trans (mul_le_mul_of_nonneg_left (hf.trans (by linarith)) hc))
  congr 1; unfold brInc; ring

/-- **The one-layer fourth moment of `Δ_{k+1}`, abstract law.** -/
theorem br_four [IsProbabilityMeasure μ] (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUm : Measurable U) (hS : ∀ᵐ ω ∂μ, ‖sand hT (U ω)‖ ≤ 1)
    {ν : ℝ} (hν : ‖matrixExpect μ U - 1‖ ≤ ν) (k : ℕ) {H8 L4 : ℝ}
    (hh : Integrable (fun ω => frobSq (sand hT (U ω - matrixExpect μ U)) ^ 4) μ)
    (hH8 : ∫ ω, frobSq (sand hT (U ω - matrixExpect μ U)) ^ 4 ∂μ ≤ H8)
    (hl : Integrable (fun ω => ‖brLin hT (k + 1) (U ω - matrixExpect μ U)‖ ^ 4) μ)
    (hL4 : ∫ ω, ‖brLin hT (k + 1) (U ω - matrixExpect μ U)‖ ^ 4 ∂μ ≤ L4) :
    Integrable (fun ω => brInc hT (k + 1) (U ω) ^ 4) μ ∧
    ∫ ω, brInc hT (k + 1) (U ω) ^ 4 ∂μ ≤
      27 * (((k + 1 : ℕ) : ℝ) ^ 4 * L4 + (((k + 1 : ℕ) : ℝ) * (ν * T.trace.re)) ^ 4 +
        128 * (((k + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (k + 1))) ^ 4 *
          (H8 + (ν ^ 2 * T.trace.re) ^ 4)) := by
  set Ub := matrixExpect μ U
  set K : ℝ := ((k + 1 : ℕ) : ℝ)
  set c : ℝ := K * (3 * 2) ^ (2 * (k + 1))
  set n : ℝ := ν ^ 2 * T.trace.re
  have hg : 0 ≤ T.trace.re := by
    rw [← ts_sum_lam hT]; exact Finset.sum_nonneg fun i _ => ts_lam_nonneg hT i
  have hm : Measurable fun ω => brInc hT (k + 1) (U ω) ^ 4 :=
    ((continuous_brInc hT (k + 1)).measurable.comp hUm).pow_const 4
  have iD : Integrable (fun ω => brInc hT (k + 1) (U ω) ^ 4) μ := by
    refine Integrable.of_bound hm.aestronglyMeasurable ((2 * W) ^ 4) ?_
    filter_upwards [hS] with ω hω
    rw [Real.norm_of_nonneg (by positivity)]
    have h := abs_brInc_le hT ht1 (k + 1) hω
    calc brInc hT (k + 1) (U ω) ^ 4 = |brInc hT (k + 1) (U ω)| ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h 4
  have hpt : ∀ᵐ ω ∂μ, brInc hT (k + 1) (U ω) ^ 4 ≤
      27 * (K ^ 4 * ‖brLin hT (k + 1) (U ω - Ub)‖ ^ 4 + (K * (ν * T.trace.re)) ^ 4 +
        128 * c ^ 4 * (frobSq (sand hT (U ω - Ub)) ^ 4 + n ^ 4)) := by
    filter_upwards [hS] with ω hω
    have hR := br_rem_le hT ht1 hω hν k
    have hb : |K * (brLin hT (k + 1) (Ub - 1)).re| ≤ K * (ν * T.trace.re) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (Nat.cast_nonneg _)
      exact (norm_brLin_le hT ht1 (by omega) _).trans (mul_le_mul_of_nonneg_right hν hg)
    have hx : |K * (brLin hT (k + 1) (U ω - Ub)).re| ≤ K * ‖brLin hT (k + 1) (U ω - Ub)‖ := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Nat.cast_nonneg _)
    have h := br_four_point (Δ := brInc hT (k + 1) (U ω))
      (x := K * (brLin hT (k + 1) (U ω - Ub)).re) (bb := K * (brLin hT (k + 1) (Ub - 1)).re)
      (R := brInc hT (k + 1) (U ω) - K * (brLin hT (k + 1) (U ω - Ub)).re -
        K * (brLin hT (k + 1) (Ub - 1)).re) (by ring) hx hb hR
    refine h.trans (le_of_eq ?_)
    ring
  have i1 : Integrable (fun ω => K ^ 4 * ‖brLin hT (k + 1) (U ω - Ub)‖ ^ 4) μ := hl.const_mul _
  have i2 : Integrable (fun ω => K ^ 4 * ‖brLin hT (k + 1) (U ω - Ub)‖ ^ 4 +
      (K * (ν * T.trace.re)) ^ 4) μ := i1.add (integrable_const _)
  have i3 : Integrable (fun ω => 128 * c ^ 4 * (frobSq (sand hT (U ω - Ub)) ^ 4 + n ^ 4)) μ :=
    (hh.add (integrable_const _)).const_mul _
  have i4 : Integrable (fun ω => K ^ 4 * ‖brLin hT (k + 1) (U ω - Ub)‖ ^ 4 +
      (K * (ν * T.trace.re)) ^ 4 + 128 * c ^ 4 * (frobSq (sand hT (U ω - Ub)) ^ 4 + n ^ 4)) μ :=
    i2.add i3
  have eI : ∫ ω, 27 * (K ^ 4 * ‖brLin hT (k + 1) (U ω - Ub)‖ ^ 4 + (K * (ν * T.trace.re)) ^ 4 +
      128 * c ^ 4 * (frobSq (sand hT (U ω - Ub)) ^ 4 + n ^ 4)) ∂μ =
      27 * (K ^ 4 * ∫ ω, ‖brLin hT (k + 1) (U ω - Ub)‖ ^ 4 ∂μ + (K * (ν * T.trace.re)) ^ 4 +
        128 * c ^ 4 * (∫ ω, frobSq (sand hT (U ω - Ub)) ^ 4 ∂μ + n ^ 4)) := by
    rw [integral_const_mul, integral_add i2 i3, integral_add i1 (integrable_const _),
      integral_const_mul, integral_const, integral_const_mul,
      integral_add hh (integrable_const _), integral_const]
    simp
  refine ⟨iD, (integral_mono_ae iD (i4.const_mul 27) hpt).trans ?_⟩
  rw [eI]
  have c4 : 0 ≤ 128 * c ^ 4 := by positivity
  have a1 := mul_le_mul_of_nonneg_left hL4 (by positivity : (0 : ℝ) ≤ K ^ 4)
  have a2 := mul_le_mul_of_nonneg_left (add_le_add_right hH8 (n ^ 4)) c4
  linarith

end BlockBand.Transmission.Generator
