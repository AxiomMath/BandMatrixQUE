module

public import BlockBand.LocalWindow.ProofTruncationBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Scale arithmetic for part (i) of the physical local window

Elementary inequalities between the scales `W`, `η` and `W^{γ/2}` used in the assembly of part (i)
of the physical local-window lemma.

With `u = W^{γ/2}` and `η = W^{-1+γ}` (`0 < γ < 1/2`, `W ≥ 1`):
* **`partOne_scale_facts`**: `1 ≤ u ≤ W`, `Wη = u²`, `η u² ≤ 1`, `(2W)^{γ/2} ≤ 2u`,
  `W^{-1/2} u ≤ 1`, `η > 0`, `W^{-2} W ≤ η`.
* `small_W_absorb`: if `W^{γ/2} < K` then `1 ≤ K^{2D/γ} W^{-D}` (small `W` absorbed by `C`).
* `l2_opNorm_le_of_toE`: an action bound gives the `L²` operator-norm bound.
* `truncF_scale`: `(c + C_G) + c²/W^{-A} ≤ (|T| + C_G + T²)(2W)^{A+4}` for `c ≤ |T| W²`.
* `norm_ofReal_add_I_le`: `|e + i t| ≤ |e| + |t|`.
* `grid_card_bound`: `4/h + 1 ≤ W^{2A + 7}` for `h = W^{-2}/((nW)² W^{2A} + 1)`, `n ≤ TW`,
  `W ≥ 4T² + 5`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartOne

open Matrix
open scoped Matrix.Norms.L2Operator

/-- **The scale facts of part (i)**: for `W ≥ 1`, `0 < γ < 1/2`,
`u = W^{γ/2}` and `η = W^{-1+γ}`. -/
theorem partOne_scale_facts {W γ : ℝ} (hW : 1 ≤ W) (hγ : 0 < γ) (hγ1 : γ < 1 / 2) :
    1 ≤ W ^ (γ / 2) ∧ W ^ (γ / 2) ≤ W ∧ W * W ^ (-1 + γ) = (W ^ (γ / 2)) ^ 2 ∧
      W ^ (-1 + γ) * (W ^ (γ / 2)) ^ 2 ≤ 1 ∧ (2 * W) ^ (γ / 2) ≤ 2 * W ^ (γ / 2) ∧
      W ^ (-1 + 1 / 2 : ℝ) * W ^ (γ / 2) ≤ 1 ∧ 0 < W ^ (-1 + γ) ∧
      W ^ (-2 : ℝ) * W ≤ W ^ (-1 + γ) := by
  have hW0 : 0 < W := by linarith
  have hsq : (W ^ (γ / 2)) ^ 2 = W ^ γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
  refine ⟨Real.one_le_rpow hW (by linarith), ?_, ?_, ?_, ?_, ?_, Real.rpow_pos_of_pos hW0 _, ?_⟩
  · calc W ^ (γ / 2) ≤ W ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW (by linarith)
      _ = W := Real.rpow_one W
  · rw [hsq]
    calc W * W ^ (-1 + γ) = W ^ (1 : ℝ) * W ^ (-1 + γ) := by rw [Real.rpow_one]
      _ = W ^ γ := by rw [← Real.rpow_add hW0]; ring_nf
  · rw [hsq, ← Real.rpow_add hW0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW (by linarith)
  · rw [Real.mul_rpow (by norm_num) hW0.le]
    have : (2 : ℝ) ^ (γ / 2) ≤ 2 := by
      calc (2 : ℝ) ^ (γ / 2) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hW0.le _)
  · rw [← Real.rpow_add hW0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW (by linarith)
  · calc W ^ (-2 : ℝ) * W = W ^ (-2 : ℝ) * W ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = W ^ (-1 : ℝ) := by rw [← Real.rpow_add hW0]; norm_num
      _ ≤ W ^ (-1 + γ) := Real.rpow_le_rpow_of_exponent_le hW (by linarith)

/-- **Small `W` is absorbed by the constant**: if `W > 0`, `γ > 0`, `D ≥ 0` and
`W^{γ/2} < K`, then `1 ≤ K^{2D/γ} W^{-D}`. -/
theorem small_W_absorb {W γ D K : ℝ} (hW : 0 < W) (hγ : 0 < γ) (hD : 0 ≤ D)
    (h : W ^ (γ / 2) < K) : 1 ≤ K ^ (2 * D / γ) * W ^ (-D) := by
  have hWD : W ^ D ≤ K ^ (2 * D / γ) := by
    have h1 : W ^ D = (W ^ (γ / 2)) ^ (2 * D / γ) := by
      rw [← Real.rpow_mul hW.le]; congr 1; field_simp
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hW.le _) h.le (by positivity)
  have hpos : 0 < W ^ D := Real.rpow_pos_of_pos hW D
  rw [Real.rpow_neg hW.le, ← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
  exact hWD

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

/-- An action bound `‖A x‖ ≤ B ‖x‖` gives `‖A‖ ≤ B` (`L²` operator norm). -/
theorem l2_opNorm_le_of_toE {β : Type} [Fintype β] [DecidableEq β] {A : Matrix β β ℂ} {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ x, ‖T A x‖ ≤ B * ‖x‖) : ‖A‖ ≤ B := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hB h

/-- **Grid cardinality**: with `ε₀ = W^{-A}`, `n ≤ TW`, `W ≥ 4T² + 5`, `A ≥ 0` and
`h = W^{-2}/((nW)²/ε₀² + 1)`: `4/h + 1 ≤ W^{2A + 7}`. -/
theorem grid_card_bound {W n Tn A : ℝ} (hW : 1 ≤ W) (hn0 : 0 ≤ n) (hn : n ≤ Tn * W)
    (hA : 0 ≤ A) (hWT : 4 * Tn ^ 2 + 5 ≤ W) :
    4 / (W ^ (-2 : ℝ) / ((n * W) ^ 2 / (W ^ (-A)) ^ 2 + 1)) + 1 ≤ W ^ (2 * A + 7) := by
  have hW0 : 0 < W := by linarith
  have hε : (W ^ (-A)) ^ 2 = (W ^ (2 * A))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_neg hW0.le]
    congr 1; push_cast; ring
  have hW2 : W ^ (-2 : ℝ) = (W ^ 2)⁻¹ := by
    rw [Real.rpow_neg hW0.le]; norm_cast
  set X := W ^ (2 * A) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hW (by linarith)
  have hnW : (n * W) ^ 2 ≤ Tn ^ 2 * W ^ 4 := by
    have h1 : n * W ≤ Tn * W * W := mul_le_mul_of_nonneg_right hn hW0.le
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  rw [hε, hW2, div_inv_eq_mul]
  have e1 : 4 / ((W ^ 2)⁻¹ / ((n * W) ^ 2 * X + 1)) = 4 * W ^ 2 * ((n * W) ^ 2 * X + 1) := by
    field_simp
  rw [e1]
  have hfin : W ^ (2 * A + 7) = X * W ^ 7 := by
    rw [hX, Real.rpow_add hW0]; norm_cast
  rw [hfin]
  have hW7 : W ^ 7 = W * W ^ 6 := by ring
  have hT0 : 0 ≤ Tn ^ 2 := sq_nonneg _
  have hW6 : 1 ≤ W ^ 6 := one_le_pow₀ hW
  have k1 : 4 * W ^ 2 * ((n * W) ^ 2 * X + 1) + 1 ≤ (4 * Tn ^ 2 + 5) * (X * W ^ 6) := by
    have hW2' : 1 ≤ W ^ 2 := one_le_pow₀ hW
    have a1 : 4 * W ^ 2 * ((n * W) ^ 2 * X) ≤ 4 * Tn ^ 2 * (X * W ^ 6) := by
      have := mul_le_mul_of_nonneg_left hnW (by positivity : (0 : ℝ) ≤ 4 * W ^ 2 * X)
      nlinarith
    have a2 : 4 * W ^ 2 + 1 ≤ 5 * (X * W ^ 6) := by
      have : W ^ 2 ≤ W ^ 6 := pow_le_pow_right₀ hW (by norm_num)
      nlinarith
    nlinarith
  have k2 : (4 * Tn ^ 2 + 5) * (X * W ^ 6) ≤ W * (X * W ^ 6) :=
    mul_le_mul_of_nonneg_right hWT (by positivity)
  nlinarith

/-- **Norm scale of the truncated deformation** (`‖F̂(E)‖ ≤ C W^{A₀}`): for
`W ≥ 1`, `0 ≤ c ≤ |T| W²`, `C_G ≥ 0`, `A ≥ 0`:
`(c + C_G) + c²/W^{-A} ≤ (|T| + C_G + T²)(2W)^{A+4}`. -/
theorem truncF_scale {W c CG Tn A : ℝ} (hW : 1 ≤ W) (hc0 : 0 ≤ c) (hc : c ≤ |Tn| * W ^ 2)
    (hCG : 0 ≤ CG) (hA : 0 ≤ A) :
    (c + CG) + c ^ 2 / W ^ (-A) ≤ (|Tn| + CG + Tn ^ 2) * (2 * W) ^ (A + 4) := by
  have hW0 : 0 < W := by linarith
  set Y := W ^ A with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow hW hA
  have hdiv : c ^ 2 / W ^ (-A) = c ^ 2 * Y := by
    rw [Real.rpow_neg hW0.le, div_inv_eq_mul]
  have hc2 : c ^ 2 ≤ Tn ^ 2 * W ^ 4 := by
    have := pow_le_pow_left₀ hc0 hc 2
    rw [mul_pow, sq_abs] at this
    nlinarith
  have hWA : W ^ (A + 4) = Y * W ^ 4 := by
    rw [Real.rpow_add hW0]; norm_cast
  have h2W : W ^ (A + 4) ≤ (2 * W) ^ (A + 4) :=
    Real.rpow_le_rpow hW0.le (by linarith) (by linarith)
  have hW24 : W ^ 2 ≤ W ^ 4 := pow_le_pow_right₀ hW (by norm_num)
  have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ hW
  have hT : 0 ≤ |Tn| := abs_nonneg _
  have hK : 0 ≤ |Tn| + CG + Tn ^ 2 := by positivity
  rw [hdiv]
  calc (c + CG) + c ^ 2 * Y ≤ |Tn| * W ^ 2 + CG + Tn ^ 2 * W ^ 4 * Y := by
        have := mul_le_mul_of_nonneg_right hc2 (by linarith : (0 : ℝ) ≤ Y)
        linarith
    _ ≤ (|Tn| + CG + Tn ^ 2) * (Y * W ^ 4) := by
        have a1 : |Tn| * W ^ 2 ≤ |Tn| * (Y * W ^ 4) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hT
        have a2 : CG ≤ CG * (Y * W ^ 4) := le_mul_of_one_le_right hCG (by nlinarith)
        nlinarith
    _ = (|Tn| + CG + Tn ^ 2) * W ^ (A + 4) := by rw [hWA]
    _ ≤ _ := mul_le_mul_of_nonneg_left h2W hK

/-- `|e + i t| ≤ |e| + |t|`. -/
theorem norm_ofReal_add_I_le (e t : ℝ) : ‖(e : ℂ) + Complex.I * (t : ℂ)‖ ≤ |e| + |t| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

end BlockBand.LocalWindow.ProofPartOne
