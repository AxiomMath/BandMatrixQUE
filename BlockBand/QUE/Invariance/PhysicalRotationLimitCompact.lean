module
public import BlockBand.QUE.Invariance.PhysicalRotationApproximation
public import BlockBand.QUE.Invariance.PhysicalRotationLaw
public import BlockBand.Counting.PhysicalSpectralIntensity
public import BlockBand.Model.Construction.PhysicalSpectralLaplace
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The rotation error of a compactly supported marked test

For a compactly supported continuous test `F`, `markedRotationTestError F R a b` is the sup
distance on the strip `[-R, R] ×` marks between `F` rotated by `a` and by `b`; it is nonnegative,
tends to zero as `a_j → a`, and bounds `|F(rot_a z) - F(rot_b z)|` on the strip.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Invariance
open MeasureTheory Filter BlockBand.Model.Construction
open scoped Topology

abbrev MarkedRotationStrip (R : ℝ) := ↥(Set.Icc (-R) R) × MassProfile

instance markedRotationStrip_compact (R : ℝ) : CompactSpace (MarkedRotationStrip R) := by
  let : CompactSpace ↥(Set.Icc (-R) R) := isCompact_iff_compactSpace.mp isCompact_Icc
  infer_instance

/-- Rotated test restricted to a compact spectral strip and all marks. -/
def markedRotationStripTest (F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ)
    (R : ℝ) : C(Torus, C(MarkedRotationStrip R, ℝ)) :=
  (⟨fun q : Torus × MarkedRotationStrip R =>
    F (markedLocationRotation q.1 (q.2.1,q.2.2)),
    F.continuous.comp (continuous_markedLocationRotation_joint.comp
      (continuous_fst.prodMk ((continuous_snd.fst.subtype_val).prodMk continuous_snd.snd)))⟩ :
    C(Torus × MarkedRotationStrip R, ℝ)).curry

/-- The sup distance on the compact strip between the test rotated by `a` and by `b`. -/
def markedRotationTestError (F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ)
    (R : ℝ) (a b : Torus) : ℝ :=
  dist (markedRotationStripTest F R a) (markedRotationStripTest F R b)

theorem markedRotationTestError_nonneg
    (F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (R : ℝ) (a b : Torus) :
    0 ≤ markedRotationTestError F R a b := dist_nonneg

theorem markedRotationTestError_tendsto_zero
    (F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (R : ℝ)
    (as : ℕ → Torus) (a : Torus) (ha : Tendsto as atTop (𝓝 a)) :
    Tendsto (fun j => markedRotationTestError F R (as j) a) atTop (𝓝 0) := by
  simpa only [markedRotationTestError, dist_self, Function.comp_def] using
    ((markedRotationStripTest F R).continuous.tendsto a |>.comp ha).dist
      (tendsto_const_nhds (x := markedRotationStripTest F R a))

theorem markedRotationTestError_pointwise
    (F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (R : ℝ)
    (a b : Torus) (z : MarkedSpectralSpace) (hz : z.1 ∈ Set.Icc (-R) R) :
    |F (markedLocationRotation a z)-F (markedLocationRotation b z)| ≤
      markedRotationTestError F R a b := by
  exact ContinuousMap.dist_apply_le_dist (f := markedRotationStripTest F R a)
    (g := markedRotationStripTest F R b) (⟨z.1,hz⟩,z.2)

/-- The Laplace map is one-Lipschitz on nonnegative coordinates. -/
theorem abs_exp_neg_sub_le {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    |Real.exp (-x)-Real.exp (-y)| ≤ |x-y| := by
  wlog hxy : x≤y generalizing x y
  · simpa only [abs_sub_comm] using this hy hx (le_of_not_ge hxy)
  have he : Real.exp (-y) = Real.exp (-x)*Real.exp (x-y) := by
    rw [← Real.exp_add];congr 1;ring
  have hlow := Real.add_one_le_exp (x-y)
  have htop := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have hnonneg := Real.exp_pos (-x)
  have hdiff : 0≤1-Real.exp (x-y) := by
    linarith [Real.exp_le_one_iff.mpr (sub_nonpos.mpr hxy)]
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hxy))),
    abs_of_nonpos (sub_nonpos.mpr hxy),he]
  nlinarith

end BlockBand.QUE.Invariance
