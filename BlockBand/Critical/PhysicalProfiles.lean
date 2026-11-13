module

public import BlockBand.Critical.PhysicalFiniteReadback
public import BlockBand.Critical.FiniteProfiles
public import BlockBand.Model.Observables
public import BlockBand.Foundations.Spectral.OrderedEigenpairs
public import Mathlib

/-!
# Finite physical circle profiles

The block masses of a normalized site vector define a probability measure on the circle
`ℝ/ℤ`, with atoms at the ring points `k/n`.  Its integral of a continuous test `q` equals the
quadratic form of the block-diagonal source matrix multiplying block `k` by `q(k/n)`.
Combined with the eigenpair readback, almost surely the source derivatives of the entire
determinant recover these profile integrals for every eigenvector of the Gaussian ring.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory Matrix
open scoped BigOperators Matrix ENNReal

/-- The physical ring point `k/n`, in `ℝ/ℤ` rather than a rescaled interval. -/
def ringProfilePoint (p : BlockBand.Parameters) (k : ZMod p.n) : Torus :=
  QuotientAddGroup.mk ((k.val : ℝ) / p.n)

/-- Block mass of a site vector; no averaging over internal coordinates. -/
def vectorBlockMass (p : BlockBand.Parameters) (v : p.Site → ℂ) (k : ZMod p.n) : ℝ :=
  ∑ a : Fin p.W, ‖v (k, a)‖ ^ 2

/-- Product-index summation transfers site normalization to blocks. -/
theorem sum_vectorBlockMass (p : BlockBand.Parameters) (v : p.Site → ℂ) :
    ∑ k, p.vectorBlockMass v k = ∑ x : p.Site, ‖v x‖ ^ 2 := by
  simp only [vectorBlockMass, Fintype.sum_prod_type]

/-- The finite atomic profile measure, before packaging its unit mass. -/
def vectorProfileMeasure (p : BlockBand.Parameters) (v : p.Site → ℂ) : Measure Torus :=
  ∑ k : ZMod p.n, ENNReal.ofReal (p.vectorBlockMass v k) •
    Measure.dirac (p.ringProfilePoint k)

/-- A normalized vector gives a probability measure. -/
theorem vectorProfileMeasure_isProbability (p : BlockBand.Parameters)
    (v : p.Site → ℂ) (hv : (∑ x : p.Site, ‖v x‖ ^ 2) = 1) :
    IsProbabilityMeasure (p.vectorProfileMeasure v) := by
  constructor
  rw [vectorProfileMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [p.sum_vectorBlockMass, hv, ENNReal.ofReal_one]
  · intro k _
    exact Finset.sum_nonneg fun a _ => sq_nonneg ‖v (k, a)‖

/-- Constructed probability profile of a normalized site vector. -/
def vectorMassProfile (p : BlockBand.Parameters) (v : p.Site → ℂ)
    (hv : (∑ x : p.Site, ‖v x‖ ^ 2) = 1) : MassProfile :=
  ⟨p.vectorProfileMeasure v, p.vectorProfileMeasure_isProbability v hv⟩

/-- The constructed profile has exactly the physical finite profile integral. -/
theorem integral_vectorMassProfile (p : BlockBand.Parameters) (v : p.Site → ℂ)
    (hv : (∑ x : p.Site, ‖v x‖ ^ 2) = 1) (q : ContinuousMap Torus ℝ) :
    ∫ r, q r ∂(p.vectorMassProfile v hv : Measure Torus) =
      BlockBand.Critical.finiteProfileValue Finset.univ (p.vectorBlockMass v)
        (fun k => q (p.ringProfilePoint k)) := by
  change (∫ r, q r ∂p.vectorProfileMeasure v) = _
  rw [vectorProfileMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac,
      vectorBlockMass, smul_eq_mul, BlockBand.Critical.finiteProfileValue]
    apply Finset.sum_congr rfl
    intro k _
    rw [ENNReal.toReal_ofReal (Finset.sum_nonneg fun a _ => sq_nonneg ‖v (k,a)‖)]
  · intro k _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

/-- Block-diagonal physical source, multiplying block `k` by `q(k/n)`. -/
def profileSourceMatrix (p : BlockBand.Parameters) (q : ContinuousMap Torus ℝ) : p.SiteMatrix :=
  Matrix.diagonal fun x => (q (p.ringProfilePoint x.1) : ℂ)

/-- The unit source is exactly `I`. -/
theorem profileSourceMatrix_one (p : BlockBand.Parameters) :
    p.profileSourceMatrix (ContinuousMap.const Torus (1 : ℝ)) = 1 := by
  simp [profileSourceMatrix]

/-- Exact quadratic-source/block-mass identity for every vector. -/
theorem quadratic_profileSourceMatrix (p : BlockBand.Parameters) (v : p.Site → ℂ)
    (q : ContinuousMap Torus ℝ) :
    dotProduct (star v) ((p.profileSourceMatrix q) *ᵥ v) =
      ((BlockBand.Critical.finiteProfileValue Finset.univ (p.vectorBlockMass v)
        (fun k => q (p.ringProfilePoint k)) : ℝ) : ℂ) := by
  simp only [profileSourceMatrix, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply,
    BlockBand.Critical.finiteProfileValue, vectorBlockMass]
  rw [Fintype.sum_prod_type]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  rw [← Complex.normSq_eq_norm_sq]
  apply Complex.ext <;> simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- The circle profile integrates every physical source
quadratic form, retaining complex source readback and real profile integral. -/
theorem quadratic_profileSourceMatrix_eq_integral (p : BlockBand.Parameters)
    (v : p.Site → ℂ) (hv : (∑ x : p.Site, ‖v x‖ ^ 2) = 1)
    (q : ContinuousMap Torus ℝ) :
    dotProduct (star v) ((p.profileSourceMatrix q) *ᵥ v) =
      ((∫ r, q r ∂(p.vectorMassProfile v hv : Measure Torus) : ℝ) : ℂ) := by
  rw [p.integral_vectorMassProfile]
  exact p.quadratic_profileSourceMatrix v q

/-- Mathlib's Hermitian eigenvectors are normalized. -/
theorem hermitian_siteMass_sum {p : BlockBand.Parameters} (H : p.SiteMatrix)
    (hH : H.IsHermitian) (k : p.Site) :
    (∑ x : p.Site, ‖(hH.eigenvectorBasis k) x‖ ^ 2) = 1 := by
  rw [← EuclideanSpace.norm_sq_eq, hH.eigenvectorBasis.orthonormal.norm_eq_one]
  simp

/-- Probability profile of a Hermitian eigenvector. -/
def hermitianMassProfile {p : BlockBand.Parameters} (H : p.SiteMatrix)
    (hH : H.IsHermitian) (k : p.Site) : MassProfile :=
  p.vectorMassProfile ⇑(hH.eigenvectorBasis k) (hermitian_siteMass_sum H hH k)

/-- Physical Gaussian derivative and profile readback on the circle.  For each fixed
real `E`, all eigenvalues and source indices share one full-measure event under the
model law.  This is a finite identity, with source scale `W⁻²` and the negative root
sign, for both ring parities and all admissible parameters. -/
theorem GaussianRingModel.ae_all_eigenpair_profile_readback
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (E : ℝ) {m : ℕ}
    (q : Fin (m + 1) → ContinuousMap Torus ℝ)
    (hq : q 0 = ContinuousMap.const Torus (1 : ℝ)) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∃ hH : H.IsHermitian,
      ∃ hA : (H - (E : ℂ) • (1 : p.SiteMatrix)).det ≠ 0,
      ∀ k : p.Site,
        let Q := fun a => p.profileSourceMatrix (q a)
        let A := H - (E : ℂ) • (1 : p.SiteMatrix)
        let z := -(p.W : ℂ)^2 * ((hH.eigenvalues k : ℂ)-(E : ℂ))
        BlockBand.Critical.finiteSourcePartial A Q p.W hA z 0 ≠ 0 ∧
          ∀ a : Fin (m + 1),
            BlockBand.Critical.finiteSourcePartial A Q p.W hA z a /
              BlockBand.Critical.finiteSourcePartial A Q p.W hA z 0 =
                ((∫ r, q a r ∂(hermitianMassProfile H hH k : Measure Torus) : ℝ) : ℂ) := by
  have hQ : (fun a => p.profileSourceMatrix (q a)) 0 = 1 := by
    change p.profileSourceMatrix (q 0) = 1
    rw [hq, p.profileSourceMatrix_one]
  filter_upwards [model.ae_all_eigenpair_source_readback E
    (fun a => p.profileSourceMatrix (q a)) hQ] with H hread
  obtain ⟨hH, hA, hr⟩ := hread
  refine ⟨hH, hA, ?_⟩
  intro k
  refine ⟨(hr k).1, ?_⟩
  intro a
  rw [(hr k).2 a]
  exact p.quadratic_profileSourceMatrix_eq_integral
    ⇑(hH.eigenvectorBasis k) (hermitian_siteMass_sum H hH k) (q a)

end BlockBand.Parameters
