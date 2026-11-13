module

public import BlockBand.Model.GaussianRing

/-!
# Real-coordinate construction of the physical Gaussian ring

The independent real Gaussian coordinates of the physical model, their product law, and the
measurable Hermitian reconstruction of a matrix from them; the candidate physical law is the
pushforward of the product law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Parameters

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate NNReal

/-- Independent real labels: diagonal reals and two strict-upper components.
Redundant labels outside the strict upper triangle have variance zero. -/
abbrev GaussianCoordinate (p : BlockBand.Parameters) :=
  p.Site ⊕ (p.Site × p.Site × Bool)

/-- The canonical row-major site index is injective. -/
theorem siteIndex_injective (p : BlockBand.Parameters) :
    Function.Injective p.siteIndex := by
  rintro ⟨k, a⟩ ⟨l, b⟩ h
  have ha : a.val < p.W := a.isLt
  have hb : b.val < p.W := b.isLt
  have he : k.val * p.W + a.val = l.val * p.W + b.val := h
  have hab : a.val = b.val := by
    have hm := congrArg (fun t : ℕ => t % p.W) he
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hm
  have hkl : k.val = l.val := by
    have hm : k.val * p.W = l.val * p.W := by omega
    exact Nat.eq_of_mul_eq_mul_right p.W_pos hm
  exact Prod.ext (ZMod.val_injective p.n hkl) (Fin.ext hab)

/-- Every physical entry variance is nonnegative, including the zero band. -/
theorem entryVariance_nonneg (p : BlockBand.Parameters) (x y : p.Site) :
    0 ≤ p.entryVariance x y := by
  unfold entryVariance
  split_ifs
  · exact div_nonneg p.c_pos.le (Nat.cast_nonneg _)
  · exact div_nonneg p.b_pos.le (Nat.cast_nonneg _)
  · exact le_rfl

/-- Real variance of an independent coordinate. -/
def gaussianCoordinateVariance (p : BlockBand.Parameters) : p.GaussianCoordinate → ℝ≥0
  | .inl x => ⟨p.entryVariance x x, p.entryVariance_nonneg x x⟩
  | .inr (x, y, _) =>
      if p.siteIndex x < p.siteIndex y then
        ⟨p.entryVariance x y / 2, div_nonneg (p.entryVariance_nonneg x y) (by norm_num)⟩
      else 0

/-- The product probability measure of centered real Gaussians. -/
def gaussianCoordinatesLaw (p : BlockBand.Parameters) :
    ProbabilityMeasure (p.GaussianCoordinate → ℝ) :=
  ⟨Measure.pi (fun i => gaussianReal 0 (p.gaussianCoordinateVariance i)), inferInstance⟩

/-- Hermitian reconstruction. Lower entries are the conjugates of the upper
entries; diagonal entries use only their independent real label. -/
def gaussianReconstruction (p : BlockBand.Parameters)
    (z : p.GaussianCoordinate → ℝ) : p.SiteMatrix := fun x y =>
  if x = y then (z (.inl x) : ℂ)
  else if p.siteIndex x < p.siteIndex y then
    (z (.inr (x, y, false)) : ℂ) + Complex.I * (z (.inr (x, y, true)) : ℂ)
  else
    (z (.inr (y, x, false)) : ℂ) - Complex.I * (z (.inr (y, x, true)) : ℂ)

/-- Reconstruction is measurable on the full real coordinate space. -/
theorem measurable_gaussianReconstruction (p : BlockBand.Parameters) :
    Measurable p.gaussianReconstruction := by
  classical
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  unfold gaussianReconstruction
  split_ifs <;> fun_prop

/-- Every reconstruction, without a probability exceptional set, is Hermitian. -/
theorem gaussianReconstruction_isHermitian (p : BlockBand.Parameters)
    (z : p.GaussianCoordinate → ℝ) : (p.gaussianReconstruction z).IsHermitian := by
  classical
  ext x y
  simp only [Matrix.conjTranspose_apply, gaussianReconstruction]
  by_cases hxy : x = y
  · subst y
    simp
  · have hyx : y ≠ x := Ne.symm hxy
    have hne : p.siteIndex x ≠ p.siteIndex y := fun h => hxy (p.siteIndex_injective h)
    by_cases hlt : p.siteIndex x < p.siteIndex y
    · have hnlt : ¬p.siteIndex y < p.siteIndex x := by omega
      simp [hxy, hyx, hlt, hnlt]
    · have hylt : p.siteIndex y < p.siteIndex x := by omega
      simp [hxy, hyx, hlt, hylt, sub_eq_add_neg]

/-- The candidate physical law is the measurable Gaussian pushforward. Its characteristic
identity is proved separately. -/
def gaussianMatrixLaw (p : BlockBand.Parameters) : ProbabilityMeasure p.SiteMatrix :=
  p.gaussianCoordinatesLaw.map p.gaussianReconstruction

/-- The candidate physical law has Hermitian support. -/
theorem gaussianMatrixLaw_ae_isHermitian (p : BlockBand.Parameters) :
    ∀ᵐ H ∂(p.gaussianMatrixLaw : Measure p.SiteMatrix), H.IsHermitian := by
  change ∀ᵐ H ∂Measure.map p.gaussianReconstruction
    (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)), H.IsHermitian
  rw [ae_map_iff p.measurable_gaussianReconstruction.aemeasurable]
  · filter_upwards with z
    exact p.gaussianReconstruction_isHermitian z
  · exact (isClosed_eq (by fun_prop : Continuous (fun H : p.SiteMatrix => H.conjTranspose))
      continuous_id).measurableSet

end BlockBand.Parameters
