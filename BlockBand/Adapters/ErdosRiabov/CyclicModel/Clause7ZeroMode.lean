module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Clause1CyclicControl
public import Mathlib.Analysis.PSeries
public import Mathlib

/-!
# Zero-mode-subtracted theta bound for the cyclic ER profile

Source-faithful proof of Erdős–Riabov, Definition 2.4(vii), for the cyclic
nearest-neighbour profile.  The comparison constant depends on the fixed bond
weight `b`; in particular this module does not reuse the unrelated universal
scalar-control constant `6e`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause7

open scoped BigOperators
open ERProfile ERProfileAnalytic ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERCharacterAngle ERNearestNeighbor ERCyclicDecay ERJumpNormalization ERCyclicSummation ERHerglotz ERPhysicalBridge ERScalarProfileControl

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The inverse-square weight of the unoriented nonzero cyclic frequencies has
a dimension-free sum.  The constant four is deliberately elementary: it comes
from the two orientations and `sum_Ioo_inv_sq_le 0 n`. -/
theorem sum_inv_principalFrequency_sq_le_four (p : Params) :
    (∑ r : ZMod p.n, if r = 0 then 0 else
      ((principalFrequency p r : ℝ) ^ 2)⁻¹) ≤ 4 := by
  let e : ZMod p.n ≃ Fin p.n :=
    { toFun := fun r => ⟨r.val, r.val_lt⟩
      invFun := fun i => (i.val : ZMod p.n)
      left_inv := fun r => ZMod.natCast_zmod_val r
      right_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt) }
  rw [Fintype.sum_equiv e
    (fun r : ZMod p.n => if r = 0 then 0 else
      ((principalFrequency p r : ℝ) ^ 2)⁻¹)
    (fun i : Fin p.n => if i.1 = 0 then 0 else
      ((min i.1 (p.n - i.1) : ℝ) ^ 2)⁻¹) (by
      intro r
      have he : ((e r : Fin p.n) : ℕ) = r.val := rfl
      rw [he]
      by_cases hr : r = 0
      · simp [hr]
      · have hrval : r.val ≠ 0 := by
          intro hv
          apply hr
          apply ZMod.val_injective p.n
          simp [hv]
        simp only [hr, hrval, ↓reduceIte, principalFrequency]
        rw [Nat.cast_min, Nat.cast_sub (ZMod.val_le r)])]
  calc
    (∑ i : Fin p.n, if i.1 = 0 then 0 else
        ((min i.1 (p.n - i.1) : ℝ) ^ 2)⁻¹) ≤
      ∑ i : Fin p.n, if i.1 = 0 then 0 else
        ((i.1 : ℝ) ^ 2)⁻¹ + (((p.n - i.1 : ℕ) : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i.1 = 0
        · simp [hi]
        · simp only [hi, ↓reduceIte]
          have hil : (i.1 : ℝ) ≤ (p.n : ℝ) := by
            exact_mod_cast i.isLt.le
          rw [Nat.cast_sub i.isLt.le]
          by_cases hle : (i.1 : ℝ) ≤ (p.n : ℝ) - i.1
          · rw [min_eq_left hle]
            exact le_add_of_nonneg_right (inv_nonneg.mpr (sq_nonneg _))
          · rw [min_eq_right (le_of_not_ge hle)]
            exact le_add_of_nonneg_left (inv_nonneg.mpr (sq_nonneg _))
    _ ≤ 4 := by
      rw [show (∑ i : Fin p.n, if i.1 = 0 then 0 else
          ((i.1 : ℝ) ^ 2)⁻¹ + (((p.n - i.1 : ℕ) : ℝ) ^ 2)⁻¹) =
        (∑ i : Fin p.n, ((if i.1 = 0 then 0 else ((i.1 : ℝ) ^ 2)⁻¹) +
          (if i.1 = 0 then 0 else (((p.n - i.1 : ℕ) : ℝ) ^ 2)⁻¹))) by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i.1 = 0 <;> simp [hi], Finset.sum_add_distrib]
      have h₁ : (∑ i : Fin p.n, if i.1 = 0 then 0 else
          ((i.1 : ℝ) ^ 2)⁻¹) ≤ 2 := by
        have h := sum_Ioo_inv_sq_le (α := ℝ) 0 p.n
        rw [Fin.sum_univ_eq_sum_range (fun i => if i = 0 then 0 else (((i : ℝ) ^ 2)⁻¹)) p.n]
        have heq : (∑ i ∈ Finset.range p.n,
            if i = 0 then 0 else (((i : ℝ) ^ 2)⁻¹)) =
            ∑ i ∈ Finset.Ioo 0 p.n, (((i : ℝ) ^ 2)⁻¹) := by
          calc
            (∑ i ∈ Finset.range p.n,
                if i = 0 then 0 else (((i : ℝ) ^ 2)⁻¹)) =
              ∑ i ∈ Finset.range p.n,
                if i ≠ 0 then (((i : ℝ) ^ 2)⁻¹) else 0 := by
                  apply Finset.sum_congr rfl
                  intro i _
                  by_cases hi : i = 0 <;> simp [hi]
            _ = ∑ i ∈ (Finset.range p.n).filter (fun i => i ≠ 0),
                (((i : ℝ) ^ 2)⁻¹) := by rw [Finset.sum_filter]
            _ = ∑ i ∈ Finset.Ioo 0 p.n, (((i : ℝ) ^ 2)⁻¹) := by
              apply Finset.sum_congr
              · ext i
                simp [Nat.pos_iff_ne_zero, and_comm]
              · intro i hi
                rfl
        rw [heq]
        simpa using h
      have h₂ : (∑ i : Fin p.n, if i.1 = 0 then 0 else
          (((p.n - i.1 : ℕ) : ℝ) ^ 2)⁻¹) ≤ 2 := by
        have h := sum_Ioo_inv_sq_le (α := ℝ) 0 p.n
        rw [Fin.sum_univ_eq_sum_range (fun i => if i = 0 then 0 else
          ((((p.n - i : ℕ) : ℝ) ^ 2)⁻¹)) p.n]
        have hfilter : (∑ i ∈ Finset.range p.n,
            if i = 0 then 0 else ((((p.n - i : ℕ) : ℝ) ^ 2)⁻¹)) =
            ∑ i ∈ Finset.Ioo 0 p.n,
              ((((p.n - i : ℕ) : ℝ) ^ 2)⁻¹) := by
          calc
            (∑ i ∈ Finset.range p.n,
                if i = 0 then 0 else ((((p.n - i : ℕ) : ℝ) ^ 2)⁻¹)) =
              ∑ i ∈ Finset.range p.n,
                if i ≠ 0 then ((((p.n - i : ℕ) : ℝ) ^ 2)⁻¹) else 0 := by
                  apply Finset.sum_congr rfl
                  intro i _
                  by_cases hi : i = 0 <;> simp [hi]
            _ = ∑ i ∈ (Finset.range p.n).filter (fun i => i ≠ 0),
                ((((p.n - i : ℕ) : ℝ) ^ 2)⁻¹) := by rw [Finset.sum_filter]
            _ = ∑ i ∈ Finset.Ioo 0 p.n,
                ((((p.n - i : ℕ) : ℝ) ^ 2)⁻¹) := by
              apply Finset.sum_congr
              · ext i
                simp [Nat.pos_iff_ne_zero, and_comm]
              · intro i hi
                rfl
        rw [hfilter]
        have hreindex :
            (∑ i ∈ Finset.Ioo 0 p.n,
              ((((p.n - i : ℕ) : ℝ) ^ 2)⁻¹)) =
            ∑ i ∈ Finset.Ioo 0 p.n, (((i : ℝ) ^ 2)⁻¹) := by
          apply Finset.sum_bij (fun i _ => p.n - i)
          · intro i hi
            simp only [Finset.mem_Ioo] at hi ⊢
            omega
          · intro i₁ hi₁ i₂ hi₂ heq
            simp only [Finset.mem_Ioo] at hi₁ hi₂
            omega
          · intro j hj
            refine ⟨p.n - j, ?_, ?_⟩
            · simp only [Finset.mem_Ioo] at hj ⊢
              omega
            · simp only [Finset.mem_Ioo] at hj
              omega
          · intro i hi
            rfl
        rw [hreindex]
        simpa using h
      linarith

/-- Fixed-bond coefficient used in Definition 2.4(vii).  It diverges at the
admissible endpoints, as the source proof requires. -/
def clause7ComparisonConstant (b : ℝ) : ℝ :=
  1 / (2 * b) + 2 / (2 - 4 * b)

/-- Every nonconstant Fourier coefficient of the corrected Green kernel is
controlled by its quadratic positive-edge gap, plus the fixed negative-edge
margin. -/
theorem norm_inverseStabilityMultiplier_sub_one_le
    (p : Params) {α : ℂ} (hα : ‖α‖ < 1) (r : ZMod p.n) (hr : r ≠ 0) :
    ‖inverseStabilityMultiplier p α r - 1‖ ≤
      ((p.n : ℝ) ^ 2 / (16 * p.b)) *
          ((principalFrequency p r : ℝ) ^ 2)⁻¹ +
        1 / (2 - 4 * p.b) := by
  let lam : ℝ := cyclicSymbol p.b (principalAngle p r)
  have hlameq : covarianceEigenvalue p r = (lam : ℂ) :=
    covarianceEigenvalue_eq_cyclicSymbol_principalAngle p r
  have hden0 : stabilityMultiplier p α r ≠ 0 :=
    stabilityMultiplier_ne_zero p hα r
  have hden0' : 1 - α * (lam : ℂ) ≠ 0 := by
    simpa [stabilityMultiplier, hlameq] using hden0
  have hcoeff : inverseStabilityMultiplier p α r - 1 =
      α * (lam : ℂ) / (1 - α * (lam : ℂ)) := by
    rw [inverseStabilityMultiplier, stabilityMultiplier, hlameq]
    field_simp [hden0']
    ring
  rw [hcoeff, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hlamabs : |lam| ≤ 1 :=
    abs_cyclicSymbol_le_one p (principalAngle p r)
  have hnum : ‖α‖ * |lam| ≤ 1 := by
    nlinarith [norm_nonneg α, abs_nonneg lam]
  by_cases hlam : 0 ≤ lam
  · have hgap := principalAngle_quadratic_gap p r
    have hrpf : principalFrequency p r ≠ 0 := by
      intro hzero
      apply hr
      apply ZMod.val_injective p.n
      unfold principalFrequency at hzero
      have hval_lt := r.val_lt
      have hv : r.val = 0 := by omega
      simp [hv]
    have hθ : principalAngle p r =
        2 * Real.pi * principalFrequency p r / p.n := rfl
    have hgap' :
        16 * p.b * (principalFrequency p r : ℝ) ^ 2 /
            (p.n : ℝ) ^ 2 ≤ 1 - lam := by
      dsimp only [lam]
      rw [hθ]
      calc
        16 * p.b * (principalFrequency p r : ℝ) ^ 2 /
            (p.n : ℝ) ^ 2 =
          (4 * p.b / Real.pi ^ 2) *
            (2 * Real.pi * principalFrequency p r / p.n) ^ 2 := by
              field_simp
              ring
        _ ≤ 1 - cyclicSymbol p.b
            (2 * Real.pi * principalFrequency p r / p.n) := hgap
    have hden : 1 - lam ≤ ‖1 - α * (lam : ℂ)‖ := by
      calc
        1 - lam ≤ 1 - ‖α‖ * lam := by
          have ha : ‖α‖ ≤ 1 := hα.le
          nlinarith
        _ ≤ ‖1 - α * (lam : ℂ)‖ := by
          simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hlam] using
            (norm_sub_norm_le (1 : ℂ) (α * (lam : ℂ)))
    have hnpos : 0 < (p.n : ℝ) := by exact_mod_cast p.n_pos
    have hbpos : 0 < 16 * p.b := mul_pos (by norm_num) p.b_pos
    have hkpos : 0 < (principalFrequency p r : ℝ) ^ 2 := by positivity
    have hmain :
        ‖α‖ * |lam| / ‖1 - α * (lam : ℂ)‖ ≤
          ((p.n : ℝ) ^ 2 / (16 * p.b)) *
            ((principalFrequency p r : ℝ) ^ 2)⁻¹ := by
      have hdenpos : 0 < ‖1 - α * (lam : ℂ)‖ := norm_pos_iff.mpr (by
        simpa [stabilityMultiplier, hlameq] using hden0)
      have hgapPos : 0 < 1 - lam := lt_of_lt_of_le
        (div_pos (mul_pos hbpos hkpos) (sq_pos_of_pos hnpos)) hgap'
      calc
        ‖α‖ * |lam| / ‖1 - α * (lam : ℂ)‖ ≤
            1 / ‖1 - α * (lam : ℂ)‖ := by gcongr
        _ ≤ 1 / (1 - lam) := one_div_le_one_div_of_le hgapPos hden
        _ ≤ ((p.n : ℝ) ^ 2 / (16 * p.b)) *
            ((principalFrequency p r : ℝ) ^ 2)⁻¹ := by
          have hApos : 0 <
              16 * p.b * (principalFrequency p r : ℝ) ^ 2 /
                (p.n : ℝ) ^ 2 := by positivity
          calc
            1 / (1 - lam) ≤ 1 /
                (16 * p.b * (principalFrequency p r : ℝ) ^ 2 /
                  (p.n : ℝ) ^ 2) :=
              one_div_le_one_div_of_le hApos hgap'
            _ = _ := by field_simp
    have hm : 0 ≤ 1 / (2 - 4 * p.b) := by
      exact one_div_nonneg.mpr (by linarith [p.b_lt_half])
    exact hmain.trans (le_add_of_nonneg_right hm)
  · have hlamneg : lam < 0 := lt_of_not_ge hlam
    have hlow : 1 - 4 * p.b ≤ lam :=
      one_sub_four_b_le_cyclicSymbol p.b_pos.le
    have hmargin : 0 < 2 - 4 * p.b := by linarith [p.b_lt_half]
    have habslam : |lam| = -lam := abs_of_neg hlamneg
    have hden : 2 - 4 * p.b ≤ ‖1 - α * (lam : ℂ)‖ := by
      calc
        2 - 4 * p.b ≤ 1 - |lam| := by rw [habslam]; linarith
        _ ≤ 1 - ‖α‖ * |lam| := by
          have ha : ‖α‖ ≤ 1 := hα.le
          nlinarith [abs_nonneg lam]
        _ ≤ ‖1 - α * (lam : ℂ)‖ := by
          simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
            (norm_sub_norm_le (1 : ℂ) (α * (lam : ℂ)))
    have hneg :
        ‖α‖ * |lam| / ‖1 - α * (lam : ℂ)‖ ≤ 1 / (2 - 4 * p.b) := by
      calc
        ‖α‖ * |lam| / ‖1 - α * (lam : ℂ)‖ ≤
            1 / ‖1 - α * (lam : ℂ)‖ := by gcongr
        _ ≤ 1 / (2 - 4 * p.b) :=
          one_div_le_one_div_of_le hmargin hden
    have hfirst : 0 ≤ ((p.n : ℝ) ^ 2 / (16 * p.b)) *
        ((principalFrequency p r : ℝ) ^ 2)⁻¹ :=
      mul_nonneg (div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) p.b_pos.le))
        (inv_nonneg.mpr (sq_nonneg _))
    exact hneg.trans (le_add_of_nonneg_left hfirst)

/-- Fourier expansion of the corrected scalar Green kernel.  Subtracting the
block identity replaces every inverse multiplier by `inverse - 1`. -/
theorem fourierGreenKernel_sub_delta_eq_sum (p : Params) (α : ℂ)
    (x y : ZMod p.n) :
    fourierGreenKernel p α x y - (if x = y then 1 else 0) =
      (p.n : ℂ)⁻¹ * ∑ r,
        ZMod.stdAddChar (r * (x - y)) *
          (inverseStabilityMultiplier p α r - 1) := by
  have hzero := fourierGreenKernel_zero p x y
  have hdelta :
      (if x = y then (1 : ℂ) else 0) =
        (p.n : ℂ)⁻¹ * ∑ r : ZMod p.n,
          ZMod.stdAddChar (r * (x - y)) := by
    simpa [fourierGreenKernel, inverseStabilityMultiplier,
      stabilityMultiplier, cyclicDelta, eq_comm] using hzero.symm
  rw [fourierGreenKernel, hdelta, ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Difference of two corrected block kernels.  The zero Fourier mode cancels
before estimation, which is the key point of Definition 2.4(vii). -/
theorem norm_fourierGreenKernel_sub_delta_sub_le
    (p : Params) {α : ℂ} (hα : ‖α‖ < 1)
    (x y z : ZMod p.n) :
    ‖(fourierGreenKernel p α x y - (if x = y then 1 else 0)) -
      (fourierGreenKernel p α x z - (if x = z then 1 else 0))‖ ≤
      clause7ComparisonConstant p.b * (p.n : ℝ) := by
  rw [fourierGreenKernel_sub_delta_eq_sum,
    fourierGreenKernel_sub_delta_eq_sum, ← mul_sub,
    ← Finset.sum_sub_distrib]
  have hnpos : 0 < (p.n : ℝ) := by exact_mod_cast p.n_pos
  have hnormcast : ‖((p.n : ℂ)⁻¹)‖ = (p.n : ℝ)⁻¹ := by
    rw [norm_inv]
    simp
  calc
    ‖(p.n : ℂ)⁻¹ *
        ∑ r : ZMod p.n,
          (ZMod.stdAddChar (r * (x - y)) *
              (inverseStabilityMultiplier p α r - 1) -
            ZMod.stdAddChar (r * (x - z)) *
              (inverseStabilityMultiplier p α r - 1))‖ ≤
      (p.n : ℝ)⁻¹ * ∑ r : ZMod p.n,
        ‖ZMod.stdAddChar (r * (x - y)) *
              (inverseStabilityMultiplier p α r - 1) -
          ZMod.stdAddChar (r * (x - z)) *
              (inverseStabilityMultiplier p α r - 1)‖ := by
        rw [norm_mul, hnormcast]
        gcongr
        exact norm_sum_le _ _
    _ ≤ (p.n : ℝ)⁻¹ * ∑ r : ZMod p.n,
        if r = 0 then 0 else
          2 * (((p.n : ℝ) ^ 2 / (16 * p.b)) *
              ((principalFrequency p r : ℝ) ^ 2)⁻¹ +
            1 / (2 - 4 * p.b)) := by
      gcongr with r
      by_cases hr : r = 0
      · subst r
        simp
      · simp only [hr, ↓reduceIte]
        calc
          ‖ZMod.stdAddChar (r * (x - y)) *
                (inverseStabilityMultiplier p α r - 1) -
            ZMod.stdAddChar (r * (x - z)) *
                (inverseStabilityMultiplier p α r - 1)‖ ≤
              ‖ZMod.stdAddChar (r * (x - y)) *
                (inverseStabilityMultiplier p α r - 1)‖ +
              ‖ZMod.stdAddChar (r * (x - z)) *
                (inverseStabilityMultiplier p α r - 1)‖ := norm_sub_le _ _
          _ = 2 * ‖inverseStabilityMultiplier p α r - 1‖ := by
            rw [norm_mul, norm_mul, norm_stdAddChar, norm_stdAddChar]
            ring
          _ ≤ 2 * (((p.n : ℝ) ^ 2 / (16 * p.b)) *
                ((principalFrequency p r : ℝ) ^ 2)⁻¹ +
              1 / (2 - 4 * p.b)) := by
            gcongr
            exact norm_inverseStabilityMultiplier_sub_one_le p hα r hr
    _ ≤ (p.n : ℝ)⁻¹ *
        (2 * (((p.n : ℝ) ^ 2 / (16 * p.b)) * 4 +
          (p.n : ℝ) * (1 / (2 - 4 * p.b)))) := by
      gcongr
      rw [show (∑ r : ZMod p.n, if r = 0 then 0 else
          2 * (((p.n : ℝ) ^ 2 / (16 * p.b)) *
              ((principalFrequency p r : ℝ) ^ 2)⁻¹ +
            1 / (2 - 4 * p.b))) =
        2 * ∑ r : ZMod p.n, if r = 0 then 0 else
          (((p.n : ℝ) ^ 2 / (16 * p.b)) *
              ((principalFrequency p r : ℝ) ^ 2)⁻¹ +
            1 / (2 - 4 * p.b)) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          by_cases hr : r = 0
          · subst r
            simp
          · simp [hr]]
      gcongr
      calc
        (∑ r : ZMod p.n, if r = 0 then 0 else
            (((p.n : ℝ) ^ 2 / (16 * p.b)) *
                ((principalFrequency p r : ℝ) ^ 2)⁻¹ +
              1 / (2 - 4 * p.b))) ≤
          ((p.n : ℝ) ^ 2 / (16 * p.b)) *
              (∑ r : ZMod p.n, if r = 0 then 0 else
                ((principalFrequency p r : ℝ) ^ 2)⁻¹) +
            (p.n : ℝ) * (1 / (2 - 4 * p.b)) := by
              rw [Finset.mul_sum]
              calc
                _ ≤ ∑ r : ZMod p.n,
                    (((p.n : ℝ) ^ 2 / (16 * p.b)) *
                      (if r = 0 then 0 else
                        ((principalFrequency p r : ℝ) ^ 2)⁻¹) +
                      1 / (2 - 4 * p.b)) := by
                    apply Finset.sum_le_sum
                    intro r _
                    by_cases hr : r = 0
                    · subst r
                      have hm : 0 ≤ 1 / (2 - 4 * p.b) := by
                        exact one_div_nonneg.mpr (by linarith [p.b_lt_half])
                      simpa using hm
                    · simp [hr]
                _ = _ := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                  simp
        _ ≤ ((p.n : ℝ) ^ 2 / (16 * p.b)) * 4 +
            (p.n : ℝ) * (1 / (2 - 4 * p.b)) := by
          have hcoef : 0 ≤ (p.n : ℝ) ^ 2 / (16 * p.b) :=
            div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) p.b_pos.le)
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (sum_inv_principalFrequency_sq_le_four p) hcoef) (le_refl _)
    _ ≤ clause7ComparisonConstant p.b * (p.n : ℝ) := by
      have hn : 1 ≤ (p.n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr p.n_ne_zero)
      have hm : 0 < 2 - 4 * p.b := by linarith [p.b_lt_half]
      calc
        (p.n : ℝ)⁻¹ *
            (2 * (((p.n : ℝ) ^ 2 / (16 * p.b)) * 4 +
              (p.n : ℝ) * (1 / (2 - 4 * p.b)))) =
            (p.n : ℝ) / (2 * p.b) + 2 / (2 - 4 * p.b) := by
              field_simp
              ring
        _ ≤ (p.n : ℝ) / (2 * p.b) +
            2 * (p.n : ℝ) / (2 - 4 * p.b) := by
          have hfrac : 2 / (2 - 4 * p.b) ≤
              2 * (p.n : ℝ) / (2 - 4 * p.b) := by
            exact div_le_div_of_nonneg_right (by nlinarith) hm.le
          exact add_le_add (le_refl _) hfrac
        _ = clause7ComparisonConstant p.b * (p.n : ℝ) := by
          unfold clause7ComparisonConstant
          ring

/-- Exact physical-site form of the corrected theta kernel: after the
within-block identity cancels, only the block correction divided by `W`
remains. -/
theorem erTheta_eq_fourierCorrection_div_width
    (p : Params) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (x y : Site p.n p.W) :
    erTheta p z₁ z₂ x y =
      (fourierGreenKernel p
          (erSemicircleStieltjes z₁ *
            starRingEnd ℂ (erSemicircleStieltjes z₂)) x.1 y.1 -
        (if x.1 = y.1 then 1 else 0)) / (p.W : ℂ) := by
  rw [erTheta_apply_eq_siteGreenKernel_sub_identity p hz₁ hz₂]
  unfold siteGreenKernel
  ring

/-- The fixed-bond oscillation bound on physical theta entries.  It is uniform
in spectral height because the zero mode cancels between the two entries. -/
theorem norm_erTheta_sub_erTheta_le_fixedBond
    (p : Params) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (x y z : Site p.n p.W) :
    ‖erTheta p z₁ z₂ x y - erTheta p z₁ z₂ x z‖ ≤
      clause7ComparisonConstant p.b * p.ratio := by
  let α : ℂ := erSemicircleStieltjes z₁ *
    starRingEnd ℂ (erSemicircleStieltjes z₂)
  have hα : ‖α‖ < 1 := norm_thetaMultiplier_lt_one
    (norm_erSemicircleStieltjes_lt_one hz₁)
    (norm_erSemicircleStieltjes_lt_one hz₂)
  rw [erTheta_eq_fourierCorrection_div_width p hz₁ hz₂,
    erTheta_eq_fourierCorrection_div_width p hz₁ hz₂,
    ← sub_div, norm_div]
  have hblock := norm_fourierGreenKernel_sub_delta_sub_le
    p hα x.1 y.1 z.1
  dsimp only [α] at hblock
  have hW : ‖(p.W : ℂ)‖ = (p.W : ℝ) := by simp
  rw [hW]
  unfold Params.ratio Conventions.criticalRatio
  calc
    _ ≤ clause7ComparisonConstant p.b * (p.n : ℝ) / (p.W : ℝ) :=
      div_le_div_of_nonneg_right hblock p.real_W_pos.le
    _ = clause7ComparisonConstant p.b * ((p.n : ℝ) / (p.W : ℝ)) := by ring

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause7