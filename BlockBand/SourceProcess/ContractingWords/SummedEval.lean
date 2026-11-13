module

public import BlockBand.SourceProcess.ContractingWords.SummedMoments

/-!
# The summed step on the path: the generator and carré du champ, evaluated

The generator `wordGenerator` and the carré du champ `wordCarre` of a trace polynomial, evaluated
at a point, are the first- and second-order sums of the increment formulas (`eval_wordGenerator`,
`eval_wordCarre`).

* `momT_le`, the monotonicity and linearity of `stepErr`, and the remainder arithmetic.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory MvPolynomial
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

variable {nT nI : ℕ}

/-- `c·𝒜_tΦ(x) = Σ_w ∂_wΦ(x)a_w + Σ_{(w,v)} ½∂_v∂_wΦ(x)b_{wv}`, with `a_w = c(drift_w + inj_w(t))(x)`
and `b_{wv} = c·cov_{w,v}(x)`, for any scalar `c` (typically `c = W⁻¹`). -/
theorem eval_wordGenerator (b E : ℝ) (q : Fin nI → ℝ → ℝ) (t : ℝ) (Φ : TracePoly nT nI)
    (x : TraceWord nT nI → ℂ) (c : ℂ) :
    c * eval x (wordGenerator b E q t Φ) =
      (∑ w ∈ Φ.vars, eval x (pderiv w Φ) *
          (c * eval x (wordDrift (transportD0 b E) w + C (wordInjection b q t w)))) +
        ∑ p ∈ Φ.vars ×ˢ Φ.vars, (1 / 2 * eval x (pderiv p.2 (pderiv p.1 Φ))) *
          (c * eval x (wordCov (transportD0 b E) p.1 p.2)) := by
  simp only [wordGenerator, map_add, map_sum, map_mul, eval_C, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by ring
  · rw [Finset.sum_product]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => by ring

/-- `c·Γ(Φ)(x) = Σ_{(w,v)} ∂_wΦ∂_vΦ(x) b_{wv}` with `b_{wv} = c·cov_{w,v}(x)`, for any scalar `c`
(typically `c = W⁻¹`). -/
theorem eval_wordCarre (b E : ℝ) (Φ : TracePoly nT nI) (x : TraceWord nT nI → ℂ) (c : ℂ) :
    c * eval x (wordCarre b E Φ) =
      ∑ p ∈ Φ.vars ×ˢ Φ.vars, (eval x (pderiv p.1 Φ) * eval x (pderiv p.2 Φ)) *
        (c * eval x (wordCov (transportD0 b E) p.1 p.2)) := by
  simp only [wordCarre, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_product]
  exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => by ring

theorem momT_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {M : Ω → ℝ} {n : ℕ}
    {B : ℝ} (hB : 0 ≤ B) (h : ∫⁻ ω, ENNReal.ofReal (M ω) ^ (2 * n) ∂μ ≤ ENNReal.ofReal B) :
    momT μ M n ≤ ENNReal.ofReal (B ^ (1 / 2 : ℝ)) := by
  unfold momT
  rw [← ENNReal.ofReal_rpow_of_nonneg hB (by norm_num)]
  exact ENNReal.rpow_le_rpow h (by norm_num)

theorem stepErr_mono {C C' ρ ρ' ε : ℝ} {W : ℕ} {k : Fin nT → ℕ} {j : ℕ} (hC : C ≤ C')
    (hC0 : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ρ') :
    stepErr C ρ ε W k j ≤ stepErr C' ρ' ε W k j := by
  unfold stepErr
  have h1 : ρ ^ (j - restartIndex ε W k j) ≤ ρ' ^ (j - restartIndex ε W k j) :=
    pow_le_pow_left₀ hρ0 hρ _
  have h2 : 0 ≤ ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W := by positivity
  have h3 : C / W ≤ C' / W := div_le_div_of_nonneg_right hC (Nat.cast_nonneg W)
  calc C / W * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W) ≤
      C' / W * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W) :=
        mul_le_mul_of_nonneg_right h3 h2
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) ((div_nonneg hC0 (Nat.cast_nonneg W)).trans h3)

/-- `(C₃/√W)³ ≤ C₃³/W·(ρ^n + W^{-1/2})`. -/
theorem cube_le_stepErr {C₃ ρ ε : ℝ} {W : ℕ} (hW : 1 ≤ W) (hC₃ : 0 ≤ C₃) (hρ : 0 ≤ ρ)
    {k : Fin nT → ℕ} {j : ℕ} :
    (C₃ / Real.sqrt W) ^ 3 ≤ stepErr (C₃ ^ 3) ρ ε W k j := by
  unfold stepErr
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hs := Real.sqrt_pos.mpr hW0
  have hsq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0.le
  have e : (C₃ / Real.sqrt W) ^ 3 = C₃ ^ 3 / W * (1 / Real.sqrt W) := by
    field_simp
    rw [hsq]
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have : 0 ≤ ρ ^ (j - restartIndex ε W k j) := pow_nonneg hρ _
  linarith

theorem stepErr_smul (a C ρ ε : ℝ) (W : ℕ) (k : Fin nT → ℕ) (j : ℕ) :
    a * stepErr C ρ ε W k j = stepErr (a * C) ρ ε W k j := by
  unfold stepErr; ring

theorem stepErr_add (C C' ρ ε : ℝ) (W : ℕ) (k : Fin nT → ℕ) (j : ℕ) :
    stepErr C ρ ε W k j + stepErr C' ρ ε W k j = stepErr (C + C') ρ ε W k j := by
  unfold stepErr; ring

theorem stepErr_nonneg {C ρ ε : ℝ} {W : ℕ} {k : Fin nT → ℕ} {j : ℕ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) :
    0 ≤ stepErr C ρ ε W k j := by
  unfold stepErr
  have := pow_nonneg hρ (j - restartIndex ε W k j)
  positivity

theorem sum_ofReal_mul_le {ι : Type*} (s : Finset ι) (a t : ι → ℝ) (m : ι → ℝ≥0∞)
    (ha : ∀ i, 0 ≤ a i) (ht : ∀ i, 0 ≤ t i) (hm : ∀ i ∈ s, m i ≤ ENNReal.ofReal (t i)) :
    ∑ i ∈ s, ENNReal.ofReal (a i) * m i ≤ ENNReal.ofReal (∑ i ∈ s, a i * t i) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (ha i) (ht i)]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [ENNReal.ofReal_mul (ha i)]
  exact mul_le_mul_right (hm i hi) _

/-- The remainder term in real form. -/
theorem rem_term_le {c s C₃ : ℝ} {n : ℕ} {m : ℝ≥0∞} (hc : 0 ≤ c) (hs : 0 ≤ s) (hC₃ : 0 ≤ C₃)
    {W : ℕ} (hm : m ≤ ENNReal.ofReal s) :
    ENNReal.ofReal c * ((n : ℝ≥0∞) * (m * ENNReal.ofReal (C₃ / Real.sqrt W) ^ (3 : ℝ))) ≤
      ENNReal.ofReal (c * (n * s) * (C₃ / Real.sqrt W) ^ 3) := by
  have h3 : ENNReal.ofReal (C₃ / Real.sqrt W) ^ (3 : ℝ) =
      ENNReal.ofReal ((C₃ / Real.sqrt W) ^ 3) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    norm_cast
  rw [h3]
  calc ENNReal.ofReal c * ((n : ℝ≥0∞) * (m * ENNReal.ofReal ((C₃ / Real.sqrt W) ^ 3))) ≤
      ENNReal.ofReal c * (ENNReal.ofReal n * (ENNReal.ofReal s *
        ENNReal.ofReal ((C₃ / Real.sqrt W) ^ 3))) := by
        rw [ENNReal.ofReal_natCast]; gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc,
          ENNReal.ofReal_mul (by positivity)]
        ring

end BlockBand.SourceProcess.ContractingWords
