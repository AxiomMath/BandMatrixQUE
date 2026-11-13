module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpCoordinateIBP

/-!
# Transfer of the sharp coordinate test to the Gaussian ring

Hermitian support of the background marginal and measurability of the reconstructed
resolvent entries and of the signed error on the product space: the facts needed to apply
the exact reconstructed-background product law to the conjugate fluctuation moment, from the
conditioned IBPs to the original random matrix law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSharpCoordinateIBP

open Matrix MeasureTheory ProbabilityTheory
open ERGaussianCoordinate ERResolventMomentIBP ERProfile
open ERComplementBackgroundReconstruction
open scoped BigOperators NNReal

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The background marginal is supported on Hermitian matrices.  Thus all
resolvent bounds used after disintegration apply almost everywhere, rather
than being imposed as an extra hypothesis on the product law. -/
theorem Law.offdiagBackground_ae_isHermitian
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) :
    ∀ᵐ B ∂M.P.map
      (fun ω => offdiagBackground (M.H ω) q₀.1.1 q₀.1.2),
      B.IsHermitian := by
  have hmap := Law.measurable_offdiagBackground_via_complement M q₀ hne
  apply (ae_map_iff hmap.aemeasurable ?_).2
  · filter_upwards [] with ω
    exact actual_offdiagBackground_isHermitian M q₀.1.1 q₀.1.2 ω
  · have hpred : Measurable
        (fun B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
          ∀ i j, starRingEnd ℂ (B j i) = B i j) := by
      apply Measurable.forall
      intro i
      apply Measurable.forall
      intro j
      exact (Complex.continuous_conj.measurable.comp
        Matrix.measurable_apply).eq Matrix.measurable_apply
    apply hpred.setOf.congr
    ext B
    simp only [Set.mem_ofPred_eq, Matrix.IsHermitian]
    constructor
    · intro h
      ext i j
      exact h i j
    · intro h i j
      exact congrFun (congrFun h i) j

/-- Joint measurability of a conditioned source-inverse entry in the two real
coordinates and an arbitrary background matrix. -/
theorem measurable_sourceInverse_productEntry
    (p : Params) (a b i j : Site p.n p.W) (z : ℂ) :
    Measurable (fun v : (ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        sourceInverse (coordinateMatrix v.2 a b v.1.1 v.1.2) z i j) := by
  let P := fun v : (ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
    coordinateMatrix v.2 a b v.1.1 v.1.2 -
      z • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
  have hP : Measurable P := by
    apply Matrix.measurable_iff.mpr
    intro u v
    dsimp [P, coordinateMatrix]
    fun_prop
  unfold sourceInverse
  change Measurable (fun v => (Ring.inverse (P v).det • (P v).adjugate) i j)
  rw [show (fun v => (Ring.inverse (P v).det • (P v).adjugate) i j) =
      (fun v => (P v).det⁻¹ * (P v).adjugate i j) by
        funext v
        rw [Matrix.smul_apply]
        simp]
  have hinv : Measurable (fun v => (P v).det⁻¹) :=
    (continuous_id.matrix_det.measurable.comp hP).inv
  have hadj : Measurable (fun v => (P v).adjugate i j) :=
    (continuous_id.matrix_adjugate.measurable.comp hP).eval_matrix
  exact hinv.mul hadj

/-- Joint measurability of the full signed error on the coordinate/background
product space. -/
theorem measurable_coordinateSignedError_product
    (p : Params) (a b x y : Site p.n p.W) (z : ℂ) :
    Measurable (fun v : (ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        coordinateSignedError p v.2 a b x y z v.1.1 v.1.2) := by
  unfold coordinateSignedError
  apply Finset.measurable_sum
  intro k _
  exact measurable_const.mul
    ((measurable_sourceInverse_productEntry p a b k y z).sub measurable_const)

end ERSharpCoordinateIBP
end GaussianRing
end ERNative.BlockBand
