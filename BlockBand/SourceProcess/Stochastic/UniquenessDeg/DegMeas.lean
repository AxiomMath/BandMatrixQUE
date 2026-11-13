module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegPoint
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Measurability of the regularized drivers

* `continuous_gramReg_inv`, `continuous_tikX`, `continuous_hval`: for `ε > 0` the
  regularized driver matrices depend continuously on `s`.
* `measurable_pinvX_comp`, `measurable_tikXerr_comp`: for `s : X → ℝ^{d×d}` with measurable
  entries, `x ↦ pinvX (s x)` and `x ↦ frob(tikX (s x) ε - pinvX (s x))` are measurable (the
  pseudoinverse is only Borel, `measurable_pinv_comp`).
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open Matrix Filter Topology
open BlockBand.SourceProcess.Stochastic.Representation

variable {d : ℕ}

theorem continuous_gramReg_inv {ε : ℝ} (hε : 0 < ε) :
    Continuous fun s : Matrix (Fin d) (Fin d) ℝ => (gramReg s ε)⁻¹ := by
  have hG : Continuous fun A : Matrix (Fin d) (Fin d) ℝ => gramReg A ε :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).add continuous_const
  have he : (fun A : Matrix (Fin d) (Fin d) ℝ => (gramReg A ε)⁻¹) =
      fun A => ((gramReg A ε).det)⁻¹ • (gramReg A ε).adjugate := by
    funext A; rw [inv_def, Ring.inverse_eq_inv]
  rw [he]
  exact (hG.matrix_det.inv₀ fun A => (isUnit_det_gramReg A hε).ne_zero).smul
    hG.matrix_adjugate

theorem continuous_tikhonov' {ε : ℝ} (hε : 0 < ε) :
    Continuous fun s : Matrix (Fin d) (Fin d) ℝ => tikhonov s ε :=
  (continuous_gramReg_inv hε).matrix_mul continuous_id.matrix_transpose

theorem continuous_tikX {ε : ℝ} (hε : 0 < ε) (k : Fin d) (c : Fin d ⊕ Fin (d + d)) :
    Continuous fun s : Matrix (Fin d) (Fin d) ℝ => tikX s ε k c := by
  rcases c with m | l
  · exact ((continuous_tikhonov' hε).matrix_mul continuous_id).matrix_elem k m
  · revert l
    refine Fin.addCases (fun l₁ => ?_) (fun l₂ => ?_)
    · simp only [tikX, Sum.elim_inr, Fin.addCases_left]
      exact continuous_const.mul ((continuous_tikhonov' hε).matrix_elem k l₁)
    · simp only [tikX, Sum.elim_inr, Fin.addCases_right]
      exact continuous_const.mul ((continuous_gramReg_inv hε).matrix_elem k l₂)

theorem continuous_hval {ε : ℝ} (hε : 0 < ε) (k : Fin d) (c : Fin d ⊕ Fin (d + d)) :
    Continuous fun s : Matrix (Fin d) (Fin d) ℝ => hval s ε k c := by
  rcases c with i | l
  · exact (continuous_tikhonov' hε).matrix_elem k i
  · exact continuous_tikX hε k (Sum.inr l)

variable {X : Type*} [MeasurableSpace X]

theorem measurable_pinvX_comp {s : X → Matrix (Fin d) (Fin d) ℝ}
    (hs : ∀ i j, Measurable fun x => s x i j) (k : Fin d) (c : Fin d ⊕ Fin (d + d)) :
    Measurable fun x => pinvX (s x) k c := by
  have hp := measurable_pinv_comp hs
  have hPs : ∀ m, Measurable fun x => (pinv (s x) * s x) k m := fun m => by
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun j _ => (hp k j).mul (hs j m)
  rcases c with m | l
  · exact hPs m
  · revert l
    refine Fin.addCases (fun l₁ => ?_) (fun l₂ => ?_)
    · simp only [pinvX, Sum.elim_inr, Fin.addCases_left]; exact measurable_const
    · simp only [pinvX, Sum.elim_inr, Fin.addCases_right, Matrix.sub_apply]
      exact measurable_const.sub (hPs l₂)

theorem measurable_tikXerr_comp {s : X → Matrix (Fin d) (Fin d) ℝ}
    (hs : ∀ i j, Measurable fun x => s x i j) {ε : ℝ} (hε : 0 < ε) :
    Measurable fun x => frob (fun k c => tikX (s x) ε k c + -pinvX (s x) k c) := by
  have hsm : Measurable s := measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hs i j
  exact Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun c _ =>
    (((continuous_tikX hε k c).measurable.comp hsm).add
      (measurable_pinvX_comp hs k c).neg).pow_const 2

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
