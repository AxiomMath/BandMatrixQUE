module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Products of `m + D` with centered `D`: the scalar part of the word expansion

For constants `m_p` (`|m_p| ≤ μ`) and centered random scalars `D_p` with `‖D_p‖_Q ≤ β`, `p` in a
set of size `≤ d`, `Q = (d+2)r`, put `V = Π_p (m_p + D_p)`, `B = dβ`, `K = 2^d(1+μ)^d`:
* `|EV - Π m| ≤ K B²(1 + B^d)`: the terms with one centered factor have mean zero, the others
  are quadratic in `D` (in the paper, "with just one centered factor, the conditional mean
  is zero");
* `‖V - Π m‖_r ≤ K B(1 + B^d)` (in the paper, "each scalar bilinear form is
  `O_{L^p}(W^{-1/2})`").
The pointwise inputs are `expand_bounds` (`|Π(m+D) - Πm| ≤ S R`, the same minus the linear
terms `≤ S²R`, `S = Σ|D_p|`, `R = Π(1+|m_p|+|D_p|)`), proved by induction.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Finset
open scoped ENNReal

section Pointwise

variable {P : Type*} [DecidableEq P] (m D : P → ℂ)

omit [DecidableEq P] in
theorem norm_prod_add_le (s : Finset P) :
    ‖∏ i ∈ s, (m i + D i)‖ ≤ ∏ i ∈ s, (1 + ‖m i‖ + ‖D i‖) :=
  (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
    (norm_add_le _ _).trans (by linarith [norm_nonneg (m i), norm_nonneg (D i)]))

/-- **Pointwise expansion bounds.** -/
theorem expand_bounds (s : Finset P) :
    ‖∏ i ∈ s, (m i + D i) - ∏ i ∈ s, m i‖ ≤
        (∑ i ∈ s, ‖D i‖) * ∏ i ∈ s, (1 + ‖m i‖ + ‖D i‖) ∧
      ‖∏ i ∈ s, (m i + D i) - ∏ i ∈ s, m i - ∑ i ∈ s, D i * ∏ j ∈ s.erase i, m j‖ ≤
        (∑ i ∈ s, ‖D i‖) ^ 2 * ∏ i ∈ s, (1 + ‖m i‖ + ‖D i‖) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih
    set A := ∏ i ∈ s, (m i + D i)
    set B := ∏ i ∈ s, m i
    set L := ∑ i ∈ s, D i * ∏ j ∈ s.erase i, m j
    set R := ∏ i ∈ s, (1 + ‖m i‖ + ‖D i‖)
    set Sd := ∑ i ∈ s, ‖D i‖
    have hR : 0 ≤ R := prod_nonneg fun _ _ => by positivity
    have hS : 0 ≤ Sd := sum_nonneg fun _ _ => norm_nonneg _
    have hA : ‖A‖ ≤ R := norm_prod_add_le m D s
    have hL : ∑ i ∈ insert a s, D i * ∏ j ∈ (insert a s).erase i, m j = D a * B + m a * L := by
      rw [sum_insert ha, erase_insert ha, mul_sum]
      congr 1
      refine sum_congr rfl fun i hi => ?_
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      rw [erase_insert_of_ne hne, prod_insert (fun h => ha (mem_of_mem_erase h))]
      ring
    have hma := norm_nonneg (m a)
    have hda := norm_nonneg (D a)
    rw [hL, prod_insert ha, prod_insert ha, sum_insert ha, prod_insert ha]
    constructor
    · have e : (m a + D a) * A - m a * B = m a * (A - B) + D a * A := by ring
      rw [e]
      calc ‖m a * (A - B) + D a * A‖ ≤ ‖m a‖ * (Sd * R) + ‖D a‖ * R := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left h1 hma) (mul_le_mul_of_nonneg_left hA hda)
        _ ≤ (‖D a‖ + Sd) * ((1 + ‖m a‖ + ‖D a‖) * R) := by
            nlinarith [mul_nonneg (mul_nonneg hda hma) hR, mul_nonneg (mul_nonneg hda hda) hR,
              mul_nonneg hS hR, mul_nonneg (mul_nonneg hS hda) hR]
    · have e : (m a + D a) * A - m a * B - (D a * B + m a * L) =
          m a * (A - B - L) + D a * (A - B) := by ring
      rw [e]
      calc ‖m a * (A - B - L) + D a * (A - B)‖ ≤ ‖m a‖ * (Sd ^ 2 * R) + ‖D a‖ * (Sd * R) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left h2 hma) (mul_le_mul_of_nonneg_left h1 hda)
        _ ≤ (‖D a‖ + Sd) ^ 2 * ((1 + ‖m a‖ + ‖D a‖) * R) := by
            have hδ := mul_nonneg hda hR
            nlinarith [mul_nonneg (mul_nonneg hda hda) hR, mul_nonneg (mul_nonneg hda hS) hR,
              mul_nonneg (mul_nonneg hS hS) hR, mul_nonneg (mul_nonneg hδ hda) hma,
              mul_nonneg (mul_nonneg hδ hS) hma, mul_nonneg (mul_nonneg hδ hda) hda,
              mul_nonneg (mul_nonneg hδ hda) hS, mul_nonneg (mul_nonneg hδ hS) hS]

theorem add_pow_le_two_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (d : ℕ) :
    (a + b) ^ d ≤ 2 ^ d * (a ^ d + b ^ d) := by
  have h1 : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  have h2 : max a b ^ d ≤ a ^ d + b ^ d := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ha d]
    · rw [max_eq_left h]; linarith [pow_nonneg hb d]
  calc (a + b) ^ d ≤ (2 * max a b) ^ d := pow_le_pow_left₀ (by positivity) h1 d
    _ = 2 ^ d * max a b ^ d := mul_pow _ _ _
    _ ≤ 2 ^ d * (a ^ d + b ^ d) := mul_le_mul_of_nonneg_left h2 (by positivity)

omit [DecidableEq P] in
/-- `S^k Π_p(1+|m_p|+|D_p|) ≤ 2^d(1+μ)^d (S^k + S^{k+d})`, `S = Σ_p|D_p|`. -/
theorem weight_le [Fintype P] {d : ℕ} (hcard : Fintype.card P ≤ d) {μ : ℝ} (hμ : 0 ≤ μ)
    (hm : ∀ p, ‖m p‖ ≤ μ) (k : ℕ) :
    (∑ i, ‖D i‖) ^ k * ∏ i, (1 + ‖m i‖ + ‖D i‖) ≤
      2 ^ d * (1 + μ) ^ d * ((∑ i, ‖D i‖) ^ k + (∑ i, ‖D i‖) ^ (k + d)) := by
  set S := ∑ i, ‖D i‖
  have hS : 0 ≤ S := sum_nonneg fun _ _ => norm_nonneg _
  have hp : ∏ i, (1 + ‖m i‖ + ‖D i‖) ≤ (1 + μ + S) ^ d := by
    calc ∏ i, (1 + ‖m i‖ + ‖D i‖) ≤ ∏ _i : P, (1 + μ + S) := by
          refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => ?_
          have := single_le_sum (f := fun i => ‖D i‖) (fun _ _ => norm_nonneg _) (mem_univ i)
          linarith [hm i]
      _ = (1 + μ + S) ^ Fintype.card P := by rw [prod_const, card_univ]
      _ ≤ (1 + μ + S) ^ d := pow_le_pow_right₀ (by linarith) hcard
  have h2 := add_pow_le_two_pow (by linarith : (0 : ℝ) ≤ 1 + μ) hS d
  have h1 : 1 ≤ (1 + μ) ^ d := one_le_pow₀ (by linarith)
  have hSk := pow_nonneg hS k
  have hSd := pow_nonneg hS d
  calc S ^ k * ∏ i, (1 + ‖m i‖ + ‖D i‖) ≤ S ^ k * (2 ^ d * ((1 + μ) ^ d + S ^ d)) :=
        mul_le_mul_of_nonneg_left (hp.trans h2) hSk
    _ = 2 ^ d * ((1 + μ) ^ d * S ^ k + S ^ (k + d)) := by rw [pow_add]; ring
    _ ≤ 2 ^ d * ((1 + μ) ^ d * S ^ k + (1 + μ) ^ d * S ^ (k + d)) := by
        gcongr; exact le_mul_of_one_le_left (pow_nonneg hS _) h1
    _ = _ := by ring

end Pointwise

section Lp

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- Moments of `S = Σ_p|D_p|`: `‖S^k‖_{r'} ≤ (dβ)^k` when `kr' ≤ Q` and `‖D_p‖_Q ≤ β`. -/
theorem eLpNorm_sumNorm_pow_le {P : Type*} [Fintype P] {d : ℕ} (hcard : Fintype.card P ≤ d)
    (D : P → Ω → ℂ) (hD : ∀ p, AEStronglyMeasurable (D p) ν) {Q β : ℝ} (hQ : 1 ≤ Q)
    (hβ : 0 ≤ β) (hDβ : ∀ p, eLpNorm (D p) (ENNReal.ofReal Q) ν ≤ ENNReal.ofReal β)
    (k : ℕ) (hk : 1 ≤ k) {r' : ℝ} (hr' : 0 < r') (hkr : k * r' ≤ Q) :
    eLpNorm (fun ω => (∑ i, ‖D i ω‖) ^ k) (ENNReal.ofReal r') ν ≤
      ENNReal.ofReal ((d * β) ^ k) := by
  set S : Ω → ℝ := fun ω => ∑ i, ‖D i ω‖
  have hSm : AEStronglyMeasurable S ν :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hD i).norm
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => sum_nonneg fun _ _ => norm_nonneg _
  have e : (fun ω => S ω ^ k) = fun ω => ‖S ω‖ ^ (k : ℝ) := by
    funext ω; rw [Real.norm_of_nonneg (hS0 ω), Real.rpow_natCast]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  change eLpNorm (fun ω => S ω ^ k) _ ν ≤ _
  rw [e, eLpNorm_norm_rpow S hSm hk0]
  have hS1 : eLpNorm S (ENNReal.ofReal Q) ν ≤ ENNReal.ofReal (d * β) := by
    have hsum : S = ∑ i, fun ω => ‖D i ω‖ := by funext ω; simp [S]
    rw [hsum]
    refine (eLpNorm_sum_le (by simpa using hQ)).trans ?_
    calc ∑ i, eLpNorm (fun ω => ‖D i ω‖) (ENNReal.ofReal Q) ν ≤
          ∑ _i : P, ENNReal.ofReal β := sum_le_sum fun i _ => by rw [eLpNorm_norm _ (hD i)]; exact hDβ i
      _ = (Fintype.card P : ℝ≥0∞) * ENNReal.ofReal β := by simp
      _ ≤ (d : ℝ≥0∞) * ENNReal.ofReal β := by gcongr
      _ = ENNReal.ofReal (d * β) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
  have hexp : ENNReal.ofReal r' * ENNReal.ofReal k ≤ ENNReal.ofReal Q := by
    rw [← ENNReal.ofReal_mul hr'.le]; exact ENNReal.ofReal_le_ofReal (by linarith)
  calc eLpNorm S (ENNReal.ofReal r' * ENNReal.ofReal k) ν ^ (k : ℝ) ≤
        eLpNorm S (ENNReal.ofReal Q) ν ^ (k : ℝ) :=
        ENNReal.rpow_le_rpow (eLpNorm_le_eLpNorm_of_exponent_le hexp) hk0.le
    _ ≤ ENNReal.ofReal (d * β) ^ (k : ℝ) := ENNReal.rpow_le_rpow hS1 hk0.le
    _ = ENNReal.ofReal ((d * β) ^ k) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hk0.le, Real.rpow_natCast]

end Lp

end BlockBand.SourceProcess.ContractingWords
