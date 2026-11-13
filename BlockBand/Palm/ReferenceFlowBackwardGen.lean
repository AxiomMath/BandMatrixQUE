module

public import BlockBand.Palm.ReferenceFlowBackwardCalc

/-!
# Backward equation of the reference flow: the generator as a linear functional

`refGenerator r κ s g z` depends on `g` only through `Dg(z)` and `D²g(z)`, linearly:
`refGenerator r κ s g z = genL (r s) (κ s) z (Dg z) + genQ (r s) (κ s) z (D²g z)` for continuous
linear functionals `genL`, `genQ` (`refGenerator_eq_gen`). Hence the generator commutes with
averages whose derivatives are the averages of the derivatives (`integral_refGenerator`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow.Backward

open MeasureTheory Set Filter Matrix BlockBand.Palm.ReferenceFlow
open BlockBand.Internal.Contracts.TransmissionFlow (rotX rotY)

variable {N p : ℕ}

/-- Evaluation `Q ↦ Q u v` of a bilinear form. -/
def ev2 (u v : RefState N p) : (RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ v).comp
    (ContinuousLinearMap.apply ℝ (RefState N p →L[ℝ] ℝ) u)

@[simp] theorem ev2_apply (u v : RefState N p) (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ) :
    ev2 u v Q = Q u v := rfl

/-- First-order part of the generator. -/
def genL (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (z : RefState N p) :
    (RefState N p →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (1 / 4 : ℝ) • ∑ i : Fin N, ∑ j : Fin N,
      (if i < j then ρ i j • (ContinuousLinearMap.apply ℝ ℝ (lmul (rotX i j) (lmul (rotX i j) z)) +
        ContinuousLinearMap.apply ℝ ℝ (lmul (rotY i j) (lmul (rotY i j) z))) else 0) +
    ∑ i : Fin N, (κ i * (-(1 / 2 : ℝ))) • ContinuousLinearMap.apply ℝ ℝ (rowProj i z)

/-- Second-order part of the generator. -/
def genQ (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (z : RefState N p) :
    (RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (1 / 4 : ℝ) • ∑ i : Fin N, ∑ j : Fin N,
      (if i < j then ρ i j • (ev2 (lmul (rotX i j) z) (lmul (rotX i j) z) +
        ev2 (lmul (rotY i j) z) (lmul (rotY i j) z)) else 0) +
    ∑ i : Fin N, (κ i * (1 / 4 : ℝ)) • ∑ α : Fin p,
      (ev2 (unitEntry i α) (unitEntry i α) +
        ev2 (Complex.I • unitEntry i α) (Complex.I • unitEntry i α))

theorem genL_apply (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (z : RefState N p)
    (L : RefState N p →L[ℝ] ℝ) :
    genL ρ κ z L = (1 / 4 : ℝ) * ∑ i : Fin N, ∑ j : Fin N,
        (if i < j then ρ i j * (L (lmul (rotX i j) (lmul (rotX i j) z)) +
          L (lmul (rotY i j) (lmul (rotY i j) z))) else 0) +
      ∑ i : Fin N, (κ i * (-(1 / 2 : ℝ))) * L (rowProj i z) := by
  unfold genL
  simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    FunLike.coe_sum, Finset.sum_apply, smul_eq_mul]
  congr 2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [mul_add]

theorem genQ_apply (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (z : RefState N p)
    (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ) :
    genQ ρ κ z Q = (1 / 4 : ℝ) * ∑ i : Fin N, ∑ j : Fin N,
        (if i < j then ρ i j * (Q (lmul (rotX i j) z) (lmul (rotX i j) z) +
          Q (lmul (rotY i j) z) (lmul (rotY i j) z)) else 0) +
      ∑ i : Fin N, (κ i * (1 / 4 : ℝ)) * ∑ α : Fin p,
        (Q (unitEntry i α) (unitEntry i α) +
          Q (Complex.I • unitEntry i α) (Complex.I • unitEntry i α)) := by
  unfold genQ
  simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    FunLike.coe_sum, Finset.sum_apply, smul_eq_mul, ev2_apply]
  congr 2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [mul_add]

/-- **The generator is linear in `(Dg, D²g)`.** -/
theorem refGenerator_eq_gen (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (s : ℝ)
    (g : RefState N p → ℝ) (z : RefState N p) :
    refGenerator r κ s g z = genL (r s) (κ s) z (fderiv ℝ g z) +
      genQ (r s) (κ s) z (fderiv ℝ (fderiv ℝ g) z) := by
  rw [genL_apply, genQ_apply]
  unfold refGenerator vfSq D2
  have h1 : ∀ i j : Fin N, (if i < j then r s i j *
      ((fderiv ℝ (fderiv ℝ g) z (lmul (rotX i j) z) (lmul (rotX i j) z) +
        fderiv ℝ g z (lmul (rotX i j) (lmul (rotX i j) z))) +
      (fderiv ℝ (fderiv ℝ g) z (lmul (rotY i j) z) (lmul (rotY i j) z) +
        fderiv ℝ g z (lmul (rotY i j) (lmul (rotY i j) z)))) else 0) =
      (if i < j then r s i j * (fderiv ℝ g z (lmul (rotX i j) (lmul (rotX i j) z)) +
        fderiv ℝ g z (lmul (rotY i j) (lmul (rotY i j) z))) else 0) +
      (if i < j then r s i j * (fderiv ℝ (fderiv ℝ g) z (lmul (rotX i j) z) (lmul (rotX i j) z) +
        fderiv ℝ (fderiv ℝ g) z (lmul (rotY i j) z) (lmul (rotY i j) z)) else 0) := by
    intro i j
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => (Finset.sum_congr rfl fun j _ => h1 i j).trans
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h2 : ∀ i : Fin N, κ s i * (-(1 / 2 : ℝ) * fderiv ℝ g z (rowProj i z) +
      (1 / 4 : ℝ) * ∑ α : Fin p,
        (fderiv ℝ (fderiv ℝ g) z (unitEntry i α) (unitEntry i α) +
          fderiv ℝ (fderiv ℝ g) z (Complex.I • unitEntry i α) (Complex.I • unitEntry i α))) =
      (κ s i * (-(1 / 2 : ℝ))) * fderiv ℝ g z (rowProj i z) +
      (κ s i * (1 / 4 : ℝ)) * ∑ α : Fin p,
        (fderiv ℝ (fderiv ℝ g) z (unitEntry i α) (unitEntry i α) +
          fderiv ℝ (fderiv ℝ g) z (Complex.I • unitEntry i α) (Complex.I • unitEntry i α)) :=
    fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib]
  ring

theorem integral_ite_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (c : Prop)
    [Decidable c] (F : Ω → ℝ) :
    ∫ ω, (if c then F ω else 0) ∂P = if c then ∫ ω, F ω ∂P else 0 := by
  split_ifs <;> simp

theorem integrable_ite_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (c : Prop)
    [Decidable c] {F : Ω → ℝ} (hF : Integrable F P) :
    Integrable (fun ω => if c then F ω else 0) P := by
  split_ifs
  · exact hF
  · exact integrable_zero _ _ _

/-- The second-order part commutes with averages (evaluated through `integral_apply`). -/
theorem integral_genQ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (z : RefState N p)
    {Q : Ω → RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ}
    (hI : ∀ u v, Integrable (fun ω => Q ω u v) P)
    (hE : ∀ u v, ∫ ω, Q ω u v ∂P = (∫ ω, Q ω ∂P) u v) :
    ∫ ω, genQ ρ κ z (Q ω) ∂P = genQ ρ κ z (∫ ω, Q ω ∂P) := by
  simp only [genQ_apply]
  have hT : ∀ i j : Fin N, Integrable (fun ω => if i < j then ρ i j *
      (Q ω (lmul (rotX i j) z) (lmul (rotX i j) z) +
        Q ω (lmul (rotY i j) z) (lmul (rotY i j) z)) else 0) P := fun i j =>
    integrable_ite_zero _ (((hI _ _).add (hI _ _)).const_mul _)
  have hU : ∀ i : Fin N, Integrable (fun ω => (κ i * (1 / 4 : ℝ)) * ∑ α : Fin p,
      (Q ω (unitEntry i α) (unitEntry i α) +
        Q ω (Complex.I • unitEntry i α) (Complex.I • unitEntry i α))) P := fun i =>
    (integrable_finsetSum _ fun α _ => (hI _ _).add (hI _ _)).const_mul _
  rw [integral_add ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      hT i j).const_mul _) (integrable_finsetSum _ fun i _ => hU i),
    integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hT i j,
    integral_finsetSum _ fun i _ => hU i]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hT i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_ite_zero, integral_const_mul, integral_add (hI _ _) (hI _ _), hE, hE]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hV : ∀ α : Fin p, Integrable (fun ω => Q ω (unitEntry i α) (unitEntry i α) +
        Q ω (Complex.I • unitEntry i α) (Complex.I • unitEntry i α)) P := fun α =>
      (hI _ _).add (hI _ _)
    rw [integral_const_mul, integral_finsetSum _ fun α _ => hV α]
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_add (hI _ _) (hI _ _), hE, hE]

/-- **The generator commutes with averages** whose first and second derivatives at `z` are the
averages of the derivatives. -/
theorem integral_refGenerator {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (s : ℝ) (z : RefState N p)
    {h : Ω → RefState N p → ℝ} {B₁ B₂ : ℝ}
    (hm1 : AEStronglyMeasurable (fun ω => fderiv ℝ (h ω) z) P)
    (hm2 : AEStronglyMeasurable (fun ω => fderiv ℝ (fderiv ℝ (h ω)) z) P)
    (hb1 : ∀ᵐ ω ∂P, ‖fderiv ℝ (h ω) z‖ ≤ B₁) (hb2 : ∀ᵐ ω ∂P, ‖fderiv ℝ (fderiv ℝ (h ω)) z‖ ≤ B₂)
    (hd1 : fderiv ℝ (fun z => ∫ ω, h ω z ∂P) z = ∫ ω, fderiv ℝ (h ω) z ∂P)
    (hd2 : fderiv ℝ (fderiv ℝ (fun z => ∫ ω, h ω z ∂P)) z =
      ∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z ∂P) :
    ∫ ω, refGenerator r κ s (h ω) z ∂P = refGenerator r κ s (fun z => ∫ ω, h ω z ∂P) z := by
  have hi1 := Integrable.of_bound (E := RefState N p →L[ℝ] ℝ) hm1 B₁ hb1
  have hi2 := Integrable.of_bound (E := RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ) hm2 B₂ hb2
  have hI : ∀ u v, Integrable (fun ω => fderiv ℝ (fderiv ℝ (h ω)) z u v) P := fun u v =>
    (hi2.apply_continuousLinearMap u).apply_continuousLinearMap v
  have hE : ∀ u v, ∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z u v ∂P =
      (∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z ∂P) u v := fun u v => by
    rw [ContinuousLinearMap.integral_apply hi2,
      ContinuousLinearMap.integral_apply (hi2.apply_continuousLinearMap u)]
  simp_rw [refGenerator_eq_gen]
  have hI1 := (genL (r s) (κ s) z).integrable_comp hi1
  have e1 := (genL (r s) (κ s) z).integral_comp_comm hi1
  have hI2 : Integrable (fun ω => genQ (r s) (κ s) z (fderiv ℝ (fderiv ℝ (h ω)) z)) P := by
    simp only [genQ_apply]
    refine ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_ite_zero _ (((hI _ _).add (hI _ _)).const_mul _)).const_mul _).add
      (integrable_finsetSum _ fun i _ =>
        (integrable_finsetSum _ fun α _ => (hI _ _).add (hI _ _)).const_mul _)
  rw [hd1, hd2, ← e1, ← integral_genQ (r s) (κ s) z hI hE]
  exact integral_add hI1 hI2

end BlockBand.Palm.ReferenceFlow.Backward
