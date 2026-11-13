module

public import BlockBand.Wegner.PassiveLogCore.AbsorberMonotonicity
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Integration of the regulated passive logarithmic determinant score

This module supplies the analytic step following the Jacobi sign calculation
for the passive log bound.  The determinant along a real affine
matrix line is differentiated by restricting its complex determinant
polynomial to the real axis.  The chain rule for squared norm and real
logarithm then identifies the derivative of the regulated passive log with the
Jacobi score.  Positivity of that score gives monotonicity along every
positive-semidefinite absorber ray.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix Polynomial Set
open scoped ComplexOrder Matrix

namespace BlockBand.Wegner.PassiveLogCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation of the formal determinant line polynomial is the determinant
of the corresponding affine matrix line. -/
theorem eval_detLinePoly (M Q : Matrix ι ι ℂ) (z : ℂ) :
    (detLinePoly M Q).eval z = (M + z • Q).det := by
  change (Polynomial.evalRingHom z)
      (M.map (C : ℂ →+* ℂ[X]) +
        (X : ℂ[X]) • Q.map (C : ℂ →+* ℂ[X])).det =
    (M + z • Q).det
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp
  ring

/-- Real derivative of the determinant along a complex affine matrix line.
The value is Jacobi's formula at the point of the line, under the explicit
invertibility hypothesis at that point. -/
theorem hasDerivAt_det_real_affine
    (M Q : Matrix ι ι ℂ) (s : ℝ)
    (hs : IsUnit (M + (s : ℂ) • Q).det) :
    HasDerivAt (fun t : ℝ => (M + (t : ℂ) • Q).det)
      ((M + (s : ℂ) • Q).det *
        ((M + (s : ℂ) • Q)⁻¹ * Q).trace) s := by
  let Ms := M + (s : ℂ) • Q
  let p := detLinePoly Ms Q
  have hshift : HasDerivAt (fun t : ℝ => p.eval ((t - s : ℝ) : ℂ))
      (p.derivative.eval 0) s := by
    have hsub : HasDerivAt (fun t : ℝ => t - s) 1 s :=
      (hasDerivAt_id s).sub_const s
    have hsubComplex : HasDerivAt
        (fun t : ℝ => ((t - s : ℝ) : ℂ)) 1 s := hsub.ofReal_comp
    have hc := HasDerivAt.comp_of_eq s (p.hasDerivAt (0 : ℂ)) hsubComplex
      (show (0 : ℂ) = ((s - s : ℝ) : ℂ) by simp)
    convert hc using 1
    funext t
    rfl
    simp
  have hjac : p.derivative.eval 0 = Ms.det * (Ms⁻¹ * Q).trace :=
    eval_derivative_detLinePoly Ms Q (by simpa [Ms] using hs)
  rw [hjac] at hshift
  convert hshift using 1
  simp only [p, eval_detLinePoly, Ms]
  funext t
  congr 1
  ext i j
  simp
  ring

/-- The regulated absorbed matrix at path parameter `s`. -/
def regulatedAbsorberMatrix
    (A Γ H : Matrix ι ι ℂ) (η s : ℝ) : Matrix ι ι ℂ :=
  A + Complex.I • (Γ + s • H + η • (1 : Matrix ι ι ℂ))

/-- Half the logarithm of the squared determinant modulus along a regulated
absorber path.  This equals `log ‖det‖` while avoiding a square-root derivative. -/
def regulatedAbsorberLogPath
    (A Γ H : Matrix ι ι ℂ) (η s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log
    (Complex.normSq (regulatedAbsorberMatrix A Γ H η s).det)

/-- The determinant of the regulated absorber path has the Jacobi derivative
at every nonnegative path parameter. -/
theorem hasDerivAt_det_regulatedAbsorberMatrix
    (A Γ H : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hΓ : Γ.PosSemidef) (hH : H.PosSemidef)
    {η s : ℝ} (hη : 0 < η) (hs : 0 ≤ s) :
    HasDerivAt (fun t : ℝ => (regulatedAbsorberMatrix A Γ H η t).det)
      ((regulatedAbsorberMatrix A Γ H η s).det *
        ((regulatedAbsorberMatrix A Γ H η s)⁻¹ *
          (Complex.I • H)).trace) s := by
  let M := A + Complex.I • (Γ + η • (1 : Matrix ι ι ℂ))
  have hΓs : (Γ + s • H).PosSemidef := hΓ.add (hH.smul hs)
  have hinv : IsUnit (regulatedAbsorberMatrix A Γ H η s).det := by
    simpa [regulatedAbsorberMatrix, add_assoc, add_left_comm, add_comm] using
      isUnit_det_add_I_smul_add_pos_regulator hA hΓs hη
  have hline := hasDerivAt_det_real_affine M (Complex.I • H) s
  have hlineInv : IsUnit (M + (s : ℂ) • (Complex.I • H)).det := by
    convert hinv using 1
    congr 1
    ext i j
    simp [M, regulatedAbsorberMatrix]
    ring
  have hd := hline hlineInv
  have hmatrix (t : ℝ) :
      regulatedAbsorberMatrix A Γ H η t =
        M + (t : ℂ) • (Complex.I • H) := by
    ext i j
    simp [M, regulatedAbsorberMatrix]
    ring
  simpa only [hmatrix] using hd

/-- Derivative formula for the regulated passive logarithm.  At every
`0 ≤ s`, its derivative is the real Jacobi score
`Re tr(M(s)⁻¹ iH)`. -/
theorem hasDerivAt_regulatedAbsorberLogPath
    (A Γ H : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hΓ : Γ.PosSemidef) (hH : H.PosSemidef)
    {η s : ℝ} (hη : 0 < η) (hs : 0 ≤ s) :
    HasDerivAt (regulatedAbsorberLogPath A Γ H η)
      (((regulatedAbsorberMatrix A Γ H η s)⁻¹ *
        (Complex.I • H)).trace.re) s := by
  let Z := (regulatedAbsorberMatrix A Γ H η s).det
  let T := ((regulatedAbsorberMatrix A Γ H η s)⁻¹ *
    (Complex.I • H)).trace
  have hdet : HasDerivAt
      (fun t : ℝ => (regulatedAbsorberMatrix A Γ H η t).det)
      (Z * T) s := by
    simpa [Z, T] using
      hasDerivAt_det_regulatedAbsorberMatrix A Γ H hA hΓ hH hη hs
  have hnorm : HasDerivAt
      (fun t : ℝ => ‖(regulatedAbsorberMatrix A Γ H η t).det‖ ^ 2)
      (2 * inner ℝ Z (Z * T)) s := hdet.norm_sq
  have hZunit : IsUnit Z := by
    have hΓs : (Γ + s • H).PosSemidef := hΓ.add (hH.smul hs)
    simpa [Z, regulatedAbsorberMatrix, add_assoc, add_left_comm, add_comm] using
      isUnit_det_add_I_smul_add_pos_regulator hA hΓs hη
  have hZne : Z ≠ 0 := IsUnit.ne_zero hZunit
  have hlog : HasDerivAt
      (fun y => Real.log
        (Complex.normSq (regulatedAbsorberMatrix A Γ H η y).det))
      ((2 * inner ℝ Z (Z * T)) / Complex.normSq Z) s := by
    simpa [Complex.sq_norm, Z] using
      (hnorm.log (by
        simpa [Complex.sq_norm, Z] using
          (Complex.normSq_pos.mpr hZne).ne'))
  have hcalc :
      (1 / 2 : ℝ) *
          ((2 * inner ℝ Z (Z * T)) / Complex.normSq Z) =
        T.re := by
    simp
    field_simp [(Complex.normSq_pos.mpr hZne).ne']
    simp [Complex.normSq_apply]
    ring
  convert hlog.const_mul (1 / 2 : ℝ) using 1
  · rfl
  · exact hcalc.symm

/-- The regulated passive logarithm is monotone along every PSD absorber ray
on the nonnegative half-line. -/
theorem monotoneOn_regulatedAbsorberLogPath
    (A Γ H : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hΓ : Γ.PosSemidef) (hH : H.PosSemidef)
    {η : ℝ} (hη : 0 < η) :
    MonotoneOn (regulatedAbsorberLogPath A Γ H η) (Set.Ici 0) := by
  let f := regulatedAbsorberLogPath A Γ H η
  let f' := fun s : ℝ =>
    ((regulatedAbsorberMatrix A Γ H η s)⁻¹ * (Complex.I • H)).trace.re
  have hd : ∀ s ∈ Set.Ici (0 : ℝ), HasDerivAt f (f' s) s := by
    intro s hs
    exact hasDerivAt_regulatedAbsorberLogPath A Γ H hA hΓ hH hη hs
  apply monotoneOn_of_deriv_nonneg (convex_Ici (𝕜 := ℝ) 0)
  · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact (hd s hs.le).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hs0 : 0 ≤ s := hs.le
    have hΓs : (Γ + s • H).PosSemidef := hΓ.add (hH.smul hs0)
    rw [(hd s hs0).deriv]
    have hscore :=
      regulated_jacobiScore_nonneg A (Γ + s • H) H hA hΓs hH hη
    change 0 ≤
      ((regulatedAbsorberMatrix A Γ H η s)⁻¹ *
        (Complex.I • H)).trace.re
    convert hscore using 1
    congr 3

/-- Regulated passive-log increment between path parameters `0` and `a`. -/
def regulatedPassiveLogIncrement
    (A Q : Matrix ι ι ℂ) (η a : ℝ) : ℝ :=
  regulatedAbsorberLogPath A 0 Q η a -
    regulatedAbsorberLogPath A 0 Q η 0

/-- The regulated `0 ≤ Q ≤ I` comparison for the passive log.

The Loewner interval is represented by the explicit conditions that `Q` and
`I - Q` are positive semidefinite.  For `a ≥ 0`, the regulated passive-log
increment is nonnegative and bounded by the full-absorber increment. -/
theorem regulatedPassiveLogIncrement_nonneg_le_full
    (A Q : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    (hIQ : ((1 : Matrix ι ι ℂ) - Q).PosSemidef)
    {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) :
    0 ≤ regulatedPassiveLogIncrement A Q η a ∧
      regulatedPassiveLogIncrement A Q η a ≤
        regulatedPassiveLogIncrement A (1 : Matrix ι ι ℂ) η a := by
  have hmonoQ :=
    monotoneOn_regulatedAbsorberLogPath A 0 Q hA
      Matrix.PosSemidef.zero hQ hη
  have hlo :
      regulatedAbsorberLogPath A 0 Q η 0 ≤
        regulatedAbsorberLogPath A 0 Q η a :=
    hmonoQ (by simp) ha ha
  have hbase :
      regulatedAbsorberLogPath A 0 Q η 0 =
        regulatedAbsorberLogPath A 0 (1 : Matrix ι ι ℂ) η 0 := by
    simp [regulatedAbsorberLogPath, regulatedAbsorberMatrix]
  have hmonoComplement :=
    monotoneOn_regulatedAbsorberLogPath A (a • Q)
      ((1 : Matrix ι ι ℂ) - Q) hA (hQ.smul ha) hIQ hη
  have hu := hmonoComplement (by simp) ha ha
  have hu' :
      regulatedAbsorberLogPath A 0 Q η a ≤
        regulatedAbsorberLogPath A 0 (1 : Matrix ι ι ℂ) η a := by
    convert hu using 1 <;>
      simp [regulatedAbsorberLogPath, regulatedAbsorberMatrix]
    all_goals congr 3; ext i j; simp; ring
  constructor <;>
    simp only [regulatedPassiveLogIncrement] <;> linarith

end BlockBand.Wegner.PassiveLogCore
