module

public import BlockBand.QUE.Haar.SecondMoment
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Integration

/-!
# Independent Haar rotations inside finite complex blocks

Each block `v_b ∈ ℂ^A` is rotated by an independent Haar unitary. The rotated coordinate masses
conserve the block mass, have first moment `‖v_b‖²/W`, same-block second moments with the complex
`W(W+1)` denominator, and factorizing distinct-block second moments.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.Haar

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

variable {B A : Type*} [Fintype B] [Fintype A] [DecidableEq A]

/-- Independent finite family of normalized complex Haar rotations. -/
def blockProbability : Measure (B → Matrix.unitaryGroup A ℂ) :=
  Measure.pi (fun _ => unitaryProbability)

instance probabilityBlock : IsProbabilityMeasure (blockProbability (B := B) (A := A)) := by
  unfold blockProbability
  infer_instance

/-- Squared coordinate masses after independent block rotations. -/
def rotatedMass (v : B → A → ℂ) (U : B → Matrix.unitaryGroup A ℂ)
    (x : B × A) : ℝ := ‖((U x.1 : Matrix A A ℂ) *ᵥ v x.1) x.2‖ ^ 2

/-- The mass of a fixed unrotated block, with complex absolute values. -/
def blockMass (v : B → A → ℂ) (b : B) : ℝ := ∑ a : A, ‖v b a‖ ^ 2

omit [Fintype B] in
/-- Block mass is conserved for each independent unitary rotation. -/
theorem sum_rotatedMass (v : B → A → ℂ) (U : B → Matrix.unitaryGroup A ℂ) (b : B) :
    (∑ a : A, rotatedMass v U (b, a)) = blockMass v b :=
  unitary_mulVec_mass (U b) (v b)

/-- First mass moments under the product Haar law are integrable. -/
theorem integrable_rotatedMass (v : B → A → ℂ) (x : B × A) :
    Integrable (fun U => rotatedMass v U x) blockProbability :=
  by
    change Integrable (fun U : B → Matrix.unitaryGroup A ℂ =>
      ‖((U x.1 : Matrix A A ℂ) *ᵥ v x.1) x.2‖ ^ 2) (Measure.pi (fun _ => unitaryProbability))
    exact integrable_comp_eval (μ := fun _ : B => unitaryProbability) (i := x.1)
      (integrable_mulVec_mass (v x.1) x.2)

/-- Product-law first coordinate moment. -/
theorem integral_rotatedMass (v : B → A → ℂ) (x : B × A) :
    (∫ U, rotatedMass v U x ∂blockProbability) = blockMass v x.1 / (Fintype.card A : ℝ) := by
  have h := integral_comp_eval (μ := fun _ : B => unitaryProbability) (i := x.1)
    (integrable_mulVec_mass (v x.1) x.2).aestronglyMeasurable
  calc
    _ = ∫ U : Matrix.unitaryGroup A ℂ,
        ‖((U : Matrix A A ℂ) *ᵥ v x.1) x.2‖ ^ 2 ∂unitaryProbability := h
    _ = _ := integral_mulVec_mass (v x.1) x.2

omit [Fintype B] in
/-- Each coordinate mass is continuous on the finite product group. -/
theorem continuous_rotatedMass (v : B → A → ℂ) (x : B × A) :
    Continuous (fun U : B → Matrix.unitaryGroup A ℂ => rotatedMass v U x) :=
  (((continuous_apply x.2).comp
    (((continuous_subtype_val).comp (continuous_apply x.1)).matrix_mulVec continuous_const)).norm.pow 2)

/-- Integrability of all coordinate products is proved on the compact product
space, before invoking any moment formula. -/
theorem integrable_rotatedMass_product (v : B → A → ℂ) (x y : B × A) :
    Integrable (fun U => rotatedMass v U x * rotatedMass v U y) blockProbability := by
  have hc (z : B × A) : Continuous (fun U : B → Matrix.unitaryGroup A ℂ => rotatedMass v U z) :=
    (((continuous_apply z.2).comp
      (((continuous_subtype_val).comp (continuous_apply z.1)).matrix_mulVec continuous_const)).norm.pow 2)
  exact ((hc x).mul (hc y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Same-block second moments under the product Haar measure retain
exactly the complex `W(W+1)` denominator and diagonal excess. -/
theorem integral_rotatedMass_same (v : B → A → ℂ) (b : B) (a c : A) :
    (∫ U, rotatedMass v U (b, a) * rotatedMass v U (b, c) ∂blockProbability) =
      blockMass v b ^ 2 / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) +
      if a = c then blockMass v b ^ 2 /
        ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) else 0 := by
  have h := integral_comp_eval (μ := fun _ : B => unitaryProbability) (i := b)
    (integrable_mulVec_mass_product (v b) a c).aestronglyMeasurable
  calc
    _ = ∫ U : Matrix.unitaryGroup A ℂ,
        ‖((U : Matrix A A ℂ) *ᵥ v b) a‖ ^ 2 *
          ‖((U : Matrix A A ℂ) *ᵥ v b) c‖ ^ 2 ∂unitaryProbability := h
    _ = _ := integral_mulVec_mass_product (v b) a c

/-- Distinct-block coordinate products factor under the constructed product
Haar law. Independence is proved by the finite product measure construction. -/
theorem integral_rotatedMass_distinct (v : B → A → ℂ) (b d : B) (hbd : b ≠ d) (a c : A) :
    (∫ U, rotatedMass v U (b, a) * rotatedMass v U (d, c) ∂blockProbability) =
      (blockMass v b / (Fintype.card A : ℝ)) *
        (blockMass v d / (Fintype.card A : ℝ)) := by
  have hi : iIndepFun (fun b (U : B → Matrix.unitaryGroup A ℂ) => U b) blockProbability :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hc (b : B) (a : A) : Measurable (fun U : Matrix.unitaryGroup A ℂ =>
      ‖((U : Matrix A A ℂ) *ᵥ v b) a‖ ^ 2) :=
    (((continuous_apply a).comp
      (continuous_subtype_val.matrix_mulVec continuous_const)).norm.pow 2).measurable
  have h := (hi.indepFun hbd).comp (hc b a) (hc d c)
  have heq := h.integral_fun_mul_eq_mul_integral
    (integrable_rotatedMass v (b, a)).aestronglyMeasurable
    (integrable_rotatedMass v (d, c)).aestronglyMeasurable
  change (∫ U, rotatedMass v U (b, a) * rotatedMass v U (d, c) ∂blockProbability) =
    (∫ U, rotatedMass v U (b, a) ∂blockProbability) *
      (∫ U, rotatedMass v U (d, c) ∂blockProbability) at heq
  rw [heq, integral_rotatedMass, integral_rotatedMass]

end BlockBand.QUE.Haar
