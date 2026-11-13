module

public import BlockBand.Critical.Collar.Density.TraceEvent

/-!
# Frobenius cutoff of the fresh bonds

*Law.* `layerLaw W b .common` (bonds distributed as `Gin(b/W)`), every `W ≥ 1`, `b > 0`. The
expected squared Frobenius norm of the bond matrix is computed, and Markov's inequality bounds the
probability that it exceeds a threshold. No hypothesis is used.

* `lintegral_frobenius_bond`: `E Σ_{x,y}|B_xy|² = 2W·W·(b/W)`.
* `layerLaw_frobenius_bad_le`: `P(Σ|B_xy|² > β) ≤ 2W²(b/W)/β`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal

variable {W : ℕ}

theorem sum_norm_sq_conjTranspose_mulVec_single {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℂ) (x : m) :
    ∑ y, ‖(Mᴴ *ᵥ Pi.single x 1) y‖ ^ 2 = ∑ y, ‖M x y‖ ^ 2 := by
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mulVec_single_one]
  simp [conjTranspose_apply]

theorem measurable_bondMatrix_apply (x : Fin 2 × Fin W) (y : Fin 1 × Fin W) :
    Measurable fun B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ => bondMatrix .common B x y := by
  simp only [bondMatrix, LayerShape.incident, ite_true]
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
    ((measurable_pi_apply _).comp (measurable_pi_apply _)))

/-- `E Σ_{x,y}|B_xy|² = 2W · W t` under `bondLaw 2 1 W t`. -/
theorem lintegral_frobenius_bond (t : ℝ≥0) :
    ∫⁻ B, ENNReal.ofReal (∑ x, ∑ y, ‖bondMatrix .common B x y‖ ^ 2)
        ∂BlockBand.Layers.bondLaw 2 1 W t = ENNReal.ofReal ((2 * W : ℝ) * (W * t)) := by
  have hm : ∀ x, Measurable fun B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ =>
      ENNReal.ofReal (∑ y, ‖bondMatrix .common B x y‖ ^ 2) := fun x =>
    ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun y _ =>
      ((measurable_bondMatrix_apply x y).norm).pow_const 2)
  have hsplit : ∀ B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ,
      ENNReal.ofReal (∑ x, ∑ y, ‖bondMatrix .common B x y‖ ^ 2) =
        ∑ x, ENNReal.ofReal (∑ y, ‖bondMatrix .common B x y‖ ^ 2) := fun B =>
    ENNReal.ofReal_sum_of_nonneg fun x _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [hsplit]
  rw [lintegral_finsetSum _ fun x _ => hm x]
  have hx : ∀ x : Fin 2 × Fin W, ∫⁻ B, ENNReal.ofReal (∑ y, ‖bondMatrix .common B x y‖ ^ 2)
      ∂BlockBand.Layers.bondLaw 2 1 W t = ENNReal.ofReal (W * t) := by
    intro x
    have h := lintegral_norm_sq_bond_mulVec (W := W) t (Pi.single x 1)
    simp_rw [sum_norm_sq_conjTranspose_mulVec_single] at h
    rw [h]
    congr 1
    have : ∑ a, ‖(Pi.single x (1 : ℂ) : Fin 2 × Fin W → ℂ) a‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single x (fun a _ ha => by simp [ha]) (by simp)]
      simp
    rw [this, mul_one]
  simp_rw [hx]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- **Frobenius cutoff of the bonds** (Markov): for `β > 0`,
`P_layer(Σ|B_xy|² > β) ≤ 2W · W(b/W) / β`. -/
theorem layerLaw_frobenius_bad_le (W : ℕ) (b : ℝ) {β : ℝ} (hβ : 0 < β) :
    layerLaw W b .common {ω | β < ∑ x, ∑ y, ‖bondMatrix .common ω.2 x y‖ ^ 2} ≤
      ENNReal.ofReal ((2 * W : ℝ) * (W * Real.toNNReal (b / W)) / β) := by
  have hev := BlockBand.Layers.layerLaw_bond_event W b .common
    {B | β < ∑ x, ∑ y, ‖bondMatrix .common B x y‖ ^ 2}
  simp only [Set.mem_ofPred_eq] at hev
  rw [hev]
  have hmeas : Measurable fun B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ =>
      ENNReal.ofReal (∑ x, ∑ y, ‖bondMatrix .common B x y‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _
      fun y _ => ((measurable_bondMatrix_apply x y).norm).pow_const 2)
  have hsub : {B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ |
      β < ∑ x, ∑ y, ‖bondMatrix .common B x y‖ ^ 2} ⊆
        {B | ENNReal.ofReal β ≤ ENNReal.ofReal (∑ x, ∑ y, ‖bondMatrix .common B x y‖ ^ 2)} :=
    fun B hB => ENNReal.ofReal_le_ofReal (le_of_lt hB)
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div hmeas.aemeasurable (ENNReal.ofReal_pos.2 hβ).ne'
    ENNReal.ofReal_ne_top).trans ?_
  rw [lintegral_frobenius_bond, ← ENNReal.ofReal_div_of_pos hβ]

end BlockBand.Critical.Collar.Density
