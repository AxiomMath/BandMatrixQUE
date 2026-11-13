module

public import BlockBand.Transmission.PassiveCovariance.GaussianIBP
public import BlockBand.Internal.Contracts.Layers

/-!
# Gaussian integration by parts for `ginibreMeasure`

Circular Gaussian integration by parts for the Ginibre law: `E[B_xy F(B)] = t E[(F_a + iF_b)/2]`,
with `F_a`, `F_b` the real derivatives of `F` along `E_xy` and `i·E_xy` (`stein_ginibre`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped NNReal

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The coordinate map of `ginibreMeasure`. -/
def ginibreCoord (r : ι × κ × Fin 2 → ℝ) : Matrix ι κ ℂ :=
  Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem measurable_ginibreCoord : Measurable (ginibreCoord (ι := ι) (κ := κ)) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [ginibreCoord, Matrix.of_apply]
  fun_prop

omit [DecidableEq ι] [DecidableEq κ] in
theorem ginibreMeasure_eq_map (t : ℝ≥0) :
    ginibreMeasure ι κ t =
      (Measure.pi fun _ : ι × κ × Fin 2 => gaussianReal 0 (t / 2)).map ginibreCoord := rfl

omit [Fintype ι] [Fintype κ] in
theorem ginibreCoord_update (r : ι × κ × Fin 2 → ℝ) (x : ι) (y : κ) (k : Fin 2) (c : ℂ)
    (hc : c = if k = 0 then 1 else Complex.I) (s : ℝ) :
    ginibreCoord (Function.update r (x, y, k) s) =
      ginibreCoord r + (((s - r (x, y, k) : ℝ) : ℂ) * c) • Matrix.single x y 1 := by
  ext a d
  simp only [ginibreCoord, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul]
  by_cases h : x = a ∧ y = d
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true, mul_one]
    obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    · have h1 : (x, y, (1 : Fin 2)) ≠ (x, y, 0) := by simp
      simp only [ite_true] at hc
      rw [hc, Function.update_self, Function.update_of_ne h1]; push_cast; ring
    · have h0 : (x, y, (0 : Fin 2)) ≠ (x, y, 1) := by simp
      simp only [one_ne_zero, ite_false] at hc
      rw [hc, Function.update_self, Function.update_of_ne h0]; push_cast; ring
  · have h0 : (a, d, (0 : Fin 2)) ≠ (x, y, k) := fun e => h ⟨(congrArg Prod.fst e).symm,
      (congrArg (fun p => p.2.1) e).symm⟩
    have h1 : (a, d, (1 : Fin 2)) ≠ (x, y, k) := fun e => h ⟨(congrArg Prod.fst e).symm,
      (congrArg (fun p => p.2.1) e).symm⟩
    rw [Function.update_of_ne h0, Function.update_of_ne h1, ite_eq_right_iff.mpr (fun e => absurd e h), mul_zero, add_zero]

/-- **Circular Gaussian IBP for `ginibreMeasure`**: `E[B_xy F(B)] = t E[(F_a + iF_b)/2]`,
with `F_a`, `F_b` the real derivatives of `F` along `E_xy` and `i·E_xy`. -/
theorem stein_ginibre (t : ℝ≥0) (x : ι) (y : κ) (F Fa Fb : Matrix ι κ ℂ → ℂ)
    (ha : ∀ B, HasDerivAt (fun s : ℝ => F (B + (s : ℂ) • Matrix.single x y 1)) (Fa B) 0)
    (hb : ∀ B, HasDerivAt (fun s : ℝ => F (B + ((s : ℂ) * Complex.I) • Matrix.single x y 1))
      (Fb B) 0)
    (hF : Integrable F (ginibreMeasure ι κ t)) (hFa : Integrable Fa (ginibreMeasure ι κ t))
    (hFb : Integrable Fb (ginibreMeasure ι κ t))
    (hxF : Integrable (fun B => B x y * F B) (ginibreMeasure ι κ t)) :
    ∫ B, B x y * F B ∂ginibreMeasure ι κ t =
      (t : ℂ) * ∫ B, (Fa B + Complex.I * Fb B) / 2 ∂ginibreMeasure ι κ t := by
  have hm := measurable_ginibreCoord (ι := ι) (κ := κ)
  have hint : Integrable (fun B => (Fa B + Complex.I * Fb B) / 2) (ginibreMeasure ι κ t) :=
    (hFa.add (hFb.const_mul Complex.I)).div_const 2
  rw [ginibreMeasure_eq_map] at hF hFa hFb hxF hint ⊢
  set μ := Measure.pi fun _ : ι × κ × Fin 2 => gaussianReal 0 (t / 2)
  have hF' : Integrable (fun r => F (ginibreCoord r)) μ := hF.comp_measurable hm
  have hFa' : Integrable (fun r => Fa (ginibreCoord r)) μ := hFa.comp_measurable hm
  have hFb' : Integrable (fun r => Fb (ginibreCoord r)) μ := hFb.comp_measurable hm
  have hxF' : Integrable (fun r => (ginibreCoord r) x y * F (ginibreCoord r)) μ :=
    hxF.comp_measurable hm
  -- the two real coordinate products are integrable
  have hre : Integrable (fun r => (r (x, y, 0) : ℂ) * F (ginibreCoord r)) μ := by
    refine hxF'.mono ?_ (ae_of_all _ fun r => ?_)
    · exact ((measurable_pi_apply _).complex_ofReal.aestronglyMeasurable).mul hF'.1
    · simp only [ginibreCoord, Matrix.of_apply, norm_mul, Complex.norm_real]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := Complex.abs_re_le_norm ((r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I)
      simpa using this
  have him : Integrable (fun r => (r (x, y, 1) : ℂ) * F (ginibreCoord r)) μ := by
    refine hxF'.mono ?_ (ae_of_all _ fun r => ?_)
    · exact ((measurable_pi_apply _).complex_ofReal.aestronglyMeasurable).mul hF'.1
    · simp only [ginibreCoord, Matrix.of_apply, norm_mul, Complex.norm_real]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := Complex.abs_im_le_norm ((r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I)
      simpa using this
  have deriv_k : ∀ (k : Fin 2) (G : Matrix ι κ ℂ → ℂ),
      (∀ B, HasDerivAt (fun s : ℝ => F (B + ((s : ℂ) * (if k = 0 then 1 else Complex.I)) •
        Matrix.single x y 1)) (G B) 0) →
      ∀ r, HasDerivAt (fun s => F (ginibreCoord (Function.update r (x, y, k) s)))
        (G (ginibreCoord r)) (r (x, y, k)) := by
    intro k G hG r
    have hout : HasDerivAt (fun s : ℝ => F (ginibreCoord r +
        ((s : ℂ) * (if k = 0 then 1 else Complex.I)) • Matrix.single x y 1))
        (G (ginibreCoord r)) (r (x, y, k) - r (x, y, k)) := by
      rw [sub_self]; exact hG _
    have h := HasDerivAt.comp_sub_const (r (x, y, k)) (r (x, y, k)) hout
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show F (ginibreCoord (Function.update r (x, y, k) s)) = _
    rw [ginibreCoord_update r x y k _ rfl s]
  have s0 := stein_pi (fun _ : ι × κ × Fin 2 => t / 2) (x, y, 0) (fun r => F (ginibreCoord r))
    (fun r => Fa (ginibreCoord r)) (deriv_k 0 Fa (fun B => by simpa using ha B)) hF' hFa' hre
  have s1 := stein_pi (fun _ : ι × κ × Fin 2 => t / 2) (x, y, 1) (fun r => F (ginibreCoord r))
    (fun r => Fb (ginibreCoord r)) (deriv_k 1 Fb (fun B => by simpa using hb B)) hF' hFb' him
  rw [integral_map hm.aemeasurable hxF.aestronglyMeasurable,
    integral_map hm.aemeasurable hint.aestronglyMeasurable]
  have hsplit : (fun r => (ginibreCoord r) x y * F (ginibreCoord r)) =
      fun r => (r (x, y, 0) : ℂ) * F (ginibreCoord r) +
        Complex.I * ((r (x, y, 1) : ℂ) * F (ginibreCoord r)) := by
    funext r; simp only [ginibreCoord, Matrix.of_apply]; ring
  rw [hsplit, integral_add hre (him.const_mul _), integral_const_mul]
  rw [s0, s1, integral_div, integral_add hFa' (hFb'.const_mul _), integral_const_mul]
  push_cast
  ring

end BlockBand.Transmission.PassiveCovariance
