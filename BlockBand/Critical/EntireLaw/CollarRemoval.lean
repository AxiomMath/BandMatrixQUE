module

public import BlockBand.Critical.EntireLaw.CollarBound
public import BlockBand.Critical.EntireLaw.ClosingTightness
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The entire law: collar source removal from the counting theorem

`collarSourceRemoval_of_source` proves `CollarSourceRemoval` from the counting theorem
(`External.PSSS.SourceContract`), and `entireLaw_of_closing_source` derives `EntireLawContract`
from `GlobalGaussianSourceStatement`, `MatrixClosing.MatrixClosingStatement`, the same source and
`ClosedSourceLimitStep`.

The argument takes a single limit: `δ_W = 2^{-3(⌊log₂W⌋+1)} ≤ W⁻³`, so that
`P(𝓔^c) ≤ 2(C/√c)(n/W)/W → 0` directly, and `η_W = W^{-1/2}`; the cross term is bounded by
Cauchy–Schwarz with `Tr|R|` only (no `Tr R²`). The resulting bound is
`O(1/W) + O((1 + log W)/√W)` along every critical sequence (`n/W → τ`). The proof does not use
`|E| < 2` or `b < 1/2` beyond the constant `c = 1 - 2b > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-!
## 1. Asymptotics
-/

theorem tendsto_log_div_sqrt : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
  refine h.congr fun x => ?_
  rw [Real.sqrt_eq_rpow]

theorem tendsto_natLog_div_sqrt {W : ℕ → ℕ} (hW : Tendsto W atTop atTop) :
    Tendsto (fun j => (Nat.log 2 (W j) : ℝ) / Real.sqrt (W j)) atTop (𝓝 0) := by
  have hWr : Tendsto (fun j => (W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hW
  have h1 : Tendsto (fun j => Real.log (W j) / Real.sqrt (W j) / Real.log 2) atTop (𝓝 0) := by
    simpa using (tendsto_log_div_sqrt.comp hWr).div_const (Real.log 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun j => ?_) (fun j => ?_)
  · positivity
  · have hl := Real.natLog_le_logb (W j) 2
    rw [Real.logb] at hl
    push_cast at hl
    rw [div_div, mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right hl (Real.sqrt_nonneg _)

theorem tendsto_inv_sqrt {W : ℕ → ℕ} (hW : Tendsto W atTop atTop) :
    Tendsto (fun j => (Real.sqrt (W j))⁻¹) atTop (𝓝 0) := by
  have hWr : Tendsto (fun j => (W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hW
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hWr)

theorem tendsto_inv_nat {W : ℕ → ℕ} (hW : Tendsto W atTop atTop) :
    Tendsto (fun j => ((W j : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hW)

theorem term_identity_collar {W n w L q : ℝ} (hw : 0 < w) (hW : W = w ^ 2) (hn : 0 < n) :
    (W ^ 2)⁻¹ * q * (3 * (n * W * L) / n) / w⁻¹ = 3 * q * (L / w) := by
  subst hW
  field_simp

theorem term_identity_full {W n w L q t : ℝ} (hw : 0 < w) (hW : W = w ^ 2) (ht : 0 < t) :
    (W ^ 2)⁻¹ * q * (n * W * L) / (t / w⁻¹) = q / t * (n / W) * (L / w) := by
  subst hW
  field_simp

/-!
## 2. `CollarSourceRemoval` from the counting theorem
-/

/-- **`CollarSourceRemoval` from the counting theorem**, with no further hypothesis.
Choices along the sequence: `δ_W = 2^{-3(⌊log₂ W⌋+1)} ≤ W⁻³` (so `P(𝓔^c) ≤ 2(C/√c)(n/W)/W → 0`)
and `η_W = W^{-1/2}`; the four `|R|`-forms are `O(log W / √W)`. -/
theorem collarSourceRemoval_of_source (source : BlockBand.External.PSSS.SourceContract.{0}) :
    CollarSourceRemoval := by
  intro b E hb hb' hE τ J Q hQ s R a c ε hε
  set P : ℕ → Parameters := fun j => s.parameters b hb hb' j
  set ℓ : ℕ → ℕ := fun j => Nat.log 2 (s.W j)
  set K : ℕ → ℕ := fun j => 3 * ℓ j + 2
  set w : ℕ → ℝ := fun j => Real.sqrt (s.W j)
  have hWpos : ∀ j, (0 : ℝ) < s.W j := fun j => by exact_mod_cast s.W_pos j
  have hnpos : ∀ j, (0 : ℝ) < s.n j := fun j => by
    have := s.n_ge_four j; exact_mod_cast (by omega : 0 < s.n j)
  have hw : ∀ j, 0 < w j := fun j => Real.sqrt_pos.mpr (hWpos j)
  have hWw : ∀ j, (s.W j : ℝ) = w j ^ 2 := fun j => (Real.sq_sqrt (hWpos j).le).symm
  set C' : ℝ := source.C / Real.sqrt (1 - 2 * b)
  set L : ℕ → ℝ := fun j => 1 + 2 * C' * ((K j : ℝ) + 1)
  have hL : ∀ j, traceConst (P j) source (K j) = L j := fun j => rfl
  have hN : ∀ j, ((P j).N : ℝ) = s.n j * s.W j := fun j => by
    simp [P, Parameters.N, CriticalSequence.parameters]
  set t : ℝ := ε ^ 2 / 4
  have ht : 0 < t := by positivity
  -- the asymptotic inputs
  have hr : Tendsto (fun j => (s.n j : ℝ) / s.W j) atTop (𝓝 τ.1) := s.ratio_tendsto
  have hu : Tendsto (fun j => L j / w j) atTop (𝓝 0) := by
    have h1 := tendsto_inv_sqrt s.width_tendsto
    have h2 := tendsto_natLog_div_sqrt s.width_tendsto
    have h := (h1.const_mul (1 + 6 * C')).add (h2.const_mul (6 * C'))
    rw [mul_zero, mul_zero, add_zero] at h
    refine h.congr fun j => ?_
    simp only [L, K, w, ℓ]
    push_cast
    field_simp
    ring
  have hinvW := tendsto_inv_nat s.width_tendsto
  -- the five terms
  set T0 : ℕ → ℝ := fun j =>
    source.C / Real.sqrt (P j).c * (P j).N * (2 * (1 / 2 : ℝ) ^ (K j + 1))
  set T1 : ℝ → ℕ → ℝ := fun q j => (((P j).W : ℝ) ^ 2)⁻¹ * q *
    (3 * ((P j).N * traceConst (P j) source (K j)) / (P j).n) / (w j)⁻¹
  set T2 : ℝ → ℕ → ℝ := fun q j => (((P j).W : ℝ) ^ 2)⁻¹ * q *
    ((P j).N * traceConst (P j) source (K j)) / (ε ^ 2 / 4 / (w j)⁻¹)
  have hC' : 0 ≤ C' := div_nonneg source.C_pos.le (Real.sqrt_nonneg _)
  have h0 : Tendsto T0 atTop (𝓝 0) := by
    have hup : Tendsto (fun j => 2 * C' * ((s.n j : ℝ) / s.W j) * ((s.W j : ℝ))⁻¹) atTop
        (𝓝 0) := by
      simpa using (hr.const_mul (2 * C')).mul hinvW
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun j => ?_)
      (fun j => ?_)
    · simp only [T0]
      have : 0 ≤ source.C / Real.sqrt (P j).c := div_nonneg source.C_pos.le (Real.sqrt_nonneg _)
      positivity
    · simp only [T0]
      have hpow : (1 / 2 : ℝ) ^ (K j + 1) ≤ ((s.W j : ℝ) ^ 3)⁻¹ := by
        have hlt : s.W j < 2 ^ (ℓ j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
        have hlt' : (s.W j : ℝ) < 2 ^ (ℓ j + 1) := by exact_mod_cast hlt
        have hK : K j + 1 = (ℓ j + 1) * 3 := by simp only [K]; ring
        rw [hK, pow_mul]
        have hb1 : (1 / 2 : ℝ) ^ (ℓ j + 1) ≤ (s.W j : ℝ)⁻¹ := by
          rw [one_div, inv_pow]; exact inv_anti₀ (hWpos j) hlt'.le
        calc ((1 / 2 : ℝ) ^ (ℓ j + 1)) ^ 3 ≤ ((s.W j : ℝ)⁻¹) ^ 3 :=
              pow_le_pow_left₀ (by positivity) hb1 3
          _ = ((s.W j : ℝ) ^ 3)⁻¹ := inv_pow _ _
      have hc : Real.sqrt (P j).c = Real.sqrt (1 - 2 * b) := rfl
      rw [hc, hN]
      calc C' * (s.n j * s.W j) * (2 * (1 / 2 : ℝ) ^ (K j + 1))
          ≤ C' * (s.n j * s.W j) * (2 * ((s.W j : ℝ) ^ 3)⁻¹) := by
            gcongr
        _ = 2 * C' * ((s.n j : ℝ) / s.W j) * ((s.W j : ℝ))⁻¹ := by
            have := (hWpos j).ne'
            field_simp
  have h1 : ∀ q : ℝ, Tendsto (T1 q) atTop (𝓝 0) := fun q => by
    have h := hu.const_mul (3 * q)
    rw [mul_zero] at h
    refine h.congr fun j => ?_
    simp only [T1, hL, hN]
    exact (term_identity_collar (hw j) (hWw j) (hnpos j)).symm
  have h2 : ∀ q : ℝ, Tendsto (T2 q) atTop (𝓝 0) := fun q => by
    have h := (hr.const_mul (q / t)).mul hu
    rw [mul_zero] at h
    refine h.congr fun j => ?_
    simp only [T2, hL, hN]
    exact (term_identity_full (hw j) (hWw j) ht).symm
  -- squeeze
  have hsum : Tendsto (fun j => ENNReal.ofReal (T0 j) + ENNReal.ofReal (T1 ‖Q a‖ j) +
      ENNReal.ofReal (T2 ‖Q c‖ j) + ENNReal.ofReal (T1 ‖Q c‖ j) + ENNReal.ofReal (T2 ‖Q a‖ j))
      atTop (𝓝 0) := by
    have e := ((((ENNReal.tendsto_ofReal h0).add (ENNReal.tendsto_ofReal (h1 ‖Q a‖))).add
      (ENNReal.tendsto_ofReal (h2 ‖Q c‖))).add (ENNReal.tendsto_ofReal (h1 ‖Q c‖))).add
      (ENNReal.tendsto_ofReal (h2 ‖Q a‖))
    simpa using e
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun j => zero_le)
    (fun j => ?_)
  exact measure_collarDiff_le (R j).model source E Q hQ a c hε (inv_pos.mpr (hw j)) (K j)

/-- **The entire law from `GlobalGaussianSourceStatement`, `MatrixClosingStatement`, the
counting theorem and `ClosedSourceLimitStep`** (`entireLaw_of_closing` with `CollarSourceRemoval`
discharged by `collarSourceRemoval_of_source`). -/
theorem entireLaw_of_closing_source (hGS : BlockBand.Critical.GlobalSource.GlobalGaussianSourceStatement)
    (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (hO4 : ClosedSourceLimitStep) :
    BlockBand.Internal.Contracts.CriticalEntire.EntireLawContract :=
  entireLaw_of_closing hGS hMC (collarSourceRemoval_of_source source) hO4

end BlockBand.Critical.EntireLaw
