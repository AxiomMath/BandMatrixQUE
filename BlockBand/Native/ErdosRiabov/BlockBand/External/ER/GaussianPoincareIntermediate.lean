module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpResolventWeightedDysonAssembly
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpCoordinateIndexReorganization
public import BlockBand.Native.ErdosRiabov.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedPoincare
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Gaussian coordinates of the ER matrix

The finite Gaussian coordinate space of the Gaussian-ring matrix, used for the Gaussian
Poincaré step: every upper-triangular entry has a Gaussian law
(`Law.hasGaussianLaw_upperEntry`), the full upper-entry coordinate vector is jointly Gaussian
(`Law.hasGaussianLaw_upperCoordinateVector`) with independent real component pairs
(`upperRealCoordinates_iIndep`), and the matrix is recovered pointwise from these coordinates
by a reconstruction that is Hermitian for every coordinate vector
(`matrixOfUpperCoordinates`).

Source normalization: Erdos–Riabov, arXiv:2506.06441v1, the finite Gaussian
coordinate Poincare step in the fluctuation-averaging proof of Theorem 3.3.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERGaussianPoincareIntermediate

open Matrix MeasureTheory ProbabilityTheory
open ERProfile ERSharpCoordinateIBP ERFluctuationMoments
open ERProductCoordinateAnalysis ERGaussianCoordinate ERConcrete
open ERNative.BlockBand.External.CEH.FiniteGaussianPoincare
open scoped BigOperators NNReal RealInnerProductSpace

local instance (p : Params) : NeZero p.n := p.nNeZero
local instance (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance (p : Params) : Fintype (UpperPair p) := Fintype.ofFinite _
local instance (p : Params) : DecidableEq (UpperPair p) := Classical.decEq _

/-- Every upper-triangular complex entry has a Gaussian law as a
two-dimensional real random vector.  For a strict entry this is the proved
independent pair of real Gaussian components; for a diagonal entry it is the
real Gaussian embedded in `ℂ`, using the almost-sure zero imaginary part. -/
theorem Law.hasGaussianLaw_upperEntry
    {p : Params} (M : Law p) (q : UpperPair p) :
    HasGaussianLaw (upperEntryFamily M q) M.P := by
  rcases q with ⟨⟨a, b⟩, hab⟩
  by_cases hne : a ≠ b
  · have hlaws := actual_coordinate_laws M a b hab hne
    let v : NNReal :=
      ⟨ERProfile.siteCovariance p a b / 2,
        div_nonneg (varianceProfile_nonneg p a b) (by norm_num)⟩
    change
      HasLaw (fun ω => (M.H ω a b).re) (gaussianReal 0 v) M.P ∧
      HasLaw (fun ω => (M.H ω a b).im) (gaussianReal 0 v) M.P ∧
      IndepFun (fun ω => (M.H ω a b).re) (fun ω => (M.H ω a b).im) M.P
      at hlaws
    have : IsGaussian (gaussianReal 0 v) := isGaussian_gaussianReal 0 v
    have hpair : HasGaussianLaw
        (fun ω => ((M.H ω a b).re, (M.H ω a b).im)) M.P :=
      hlaws.2.2.hasGaussianLaw hlaws.1.hasGaussianLaw hlaws.2.1.hasGaussianLaw
    have hcomplex :=
      hpair.map Complex.equivRealProdCLM.symm.toContinuousLinearMap
    apply hcomplex.congr
    filter_upwards [] with ω
    simp [upperEntryFamily, Complex.equivRealProdCLM_symm_apply]
  · have hab' : a = b := Classical.not_not.mp hne
    subst b
    have hreal :=
      (M.diagonal_re_law a).hasGaussianLaw.map Complex.ofRealCLM
    apply hreal.congr
    filter_upwards [M.diagonal_im_zero a] with ω hω
    apply Complex.ext
    · simp [upperEntryFamily]
    · simp [upperEntryFamily, hω]

/-- The complete finite upper-entry coordinate vector of the ER matrix
is jointly Gaussian.  This puts the abstract `Law` on a finite Gaussian coordinate space;
it follows from the upper-entry independence of the law and the preceding coordinate laws. -/
theorem Law.hasGaussianLaw_upperCoordinateVector
    {p : Params} (M : Law p) :
    HasGaussianLaw (fun ω q => upperEntryFamily M q ω) M.P := by
  exact M.upper_independent.hasGaussianLaw
    (fun q => Law.hasGaussianLaw_upperEntry M q)

/-- Real and imaginary component pair of one selected upper entry. -/
abbrev UpperRealPair := ℝ × ℝ

/-- Extract the two scalar components of each upper entry. -/
def upperRealCoordinates {p : Params} (M : Law p) (ω : M.Ω)
    (q : UpperPair p) : UpperRealPair :=
  ((M.H ω q.1.1 q.1.2).re, (M.H ω q.1.1 q.1.2).im)

/-- The extracted pairs remain jointly independent. -/
theorem upperRealCoordinates_iIndep
    {p : Params} (M : Law p) :
    iIndepFun (fun q ω => upperRealCoordinates M ω q) M.P := by
  exact M.upper_independent.comp
    (fun _ => fun z : ℂ => (z.re, z.im)) (fun _ => by fun_prop)

/-- `siteLE` is total: if `a ≤ b` fails, then `b ≤ a`. -/
theorem siteLE_reverse_of_not {p : Params} (a b : Site p.n p.W)
    (h : ¬ siteLE p a b) : siteLE p b a := by
  unfold siteLE at h ⊢
  exact Nat.le_of_lt (Nat.lt_of_not_ge h)

/-- Hermitian reconstruction of a full matrix from its selected upper
coordinates. -/
def matrixOfUpperCoordinates {p : Params} (u : UpperPair p → ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ := fun a b =>
  if hab : a = b then
    ((u ⟨(a, b), hab ▸ (by unfold siteLE; exact le_rfl)⟩).re : ℂ)
  else if h : siteLE p a b then u ⟨(a, b), h⟩
  else star (u ⟨(b, a), siteLE_reverse_of_not a b h⟩)

/-- The reconstruction is Hermitian for every coordinate vector, including
away from the support of the Gaussian law: diagonal coordinates are
projected to their real part.  This global property is needed to make the
nonreal resolvent a smooth deterministic function on the entire finite real
coordinate space, rather than merely almost everywhere. -/
theorem matrixOfUpperCoordinates_isHermitian
    {p : Params} (u : UpperPair p → ℂ) :
    (matrixOfUpperCoordinates u).IsHermitian := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [matrixOfUpperCoordinates, Matrix.conjTranspose_apply]
  · by_cases h : siteLE p a b
    · have h' : ¬ siteLE p b a := by
        intro hba
        exact hab (ERComplementBackgroundReconstruction.siteLE_antisymm h hba)
      simp [matrixOfUpperCoordinates, hab, Ne.symm hab, h, h',
        Matrix.conjTranspose_apply]
    · have hba : siteLE p b a := siteLE_reverse_of_not a b h
      simp [matrixOfUpperCoordinates, hab, Ne.symm hab, h, hba,
        Matrix.conjTranspose_apply]

/-- The Hermitian matrix is recovered pointwise from its finite upper
coordinate vector. -/
theorem Law.matrixOfUpperCoordinates_actual
    {p : Params} (M : Law p) (ω : M.Ω) :
    matrixOfUpperCoordinates (fun q => upperEntryFamily M q ω) = M.H ω := by
  ext a b
  by_cases hab : a = b
  · subst b
    have haa := congrFun (congrFun (M.isHermitian ω) a) a
    have him : (M.H ω a a).im = 0 := by
      rw [Matrix.conjTranspose_apply] at haa
      have := congrArg Complex.im haa
      simp at this
      linarith
    apply Complex.ext
    · simp [matrixOfUpperCoordinates, upperEntryFamily]
    · simp [matrixOfUpperCoordinates, upperEntryFamily, him]
  · by_cases h : siteLE p a b
    · simp [matrixOfUpperCoordinates, upperEntryFamily, hab, h]
    · have hH := congrFun (congrFun (M.isHermitian ω) a) b
      simpa [matrixOfUpperCoordinates, upperEntryFamily, hab, h,
        Matrix.conjTranspose_apply] using hH

end ERGaussianPoincareIntermediate
end GaussianRing
end ERNative.BlockBand
