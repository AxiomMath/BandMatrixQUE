module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ProductCoordinateAnalysis
public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.CauchyResolventBound

/-!
# A concrete finite moment step for the Gaussian ER fluctuation

Dimension-free entrywise bounds at a deterministic nonreal resolvent scale: every entry of a
Hermitian resolvent is bounded by `1 / Im z` (`norm_matrixResolvent_entry_le`), and every
entry of the resolvent error is bounded by `actualWardScale z = 1 / Im z + |m(z)|`
(`norm_resolventError_entry_le`). Together with row stochasticity of the variance profile,
this bounds the signed covariance-weighted error pointwise.

This is a coarse Ward-scale bound. It does not assert stochastic domination or a local law.

Source: Erdős–Riabov, arXiv:2506.06441v1, deterministic resolvent and Ward
bounds used in the fluctuation-averaging proof of Theorem 3.3.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERActualWardBound

open Matrix MeasureTheory ProbabilityTheory ERLocalLaw ERConcrete
  ERFluctuationMoments ERProductCoordinateAnalysis
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator

local instance (p : Params) : NeZero p.n := p.nNeZero
local instance (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance (p : Params) : Fintype (UpperPair p) := Fintype.ofFinite _
local instance (p : Params) : DecidableEq (UpperPair p) := Classical.decEq _

/-!
## Product pushforward for a selected upper coordinate
-/

/-!
## Dimension-free entrywise resolvent bound
-/

private theorem norm_matrix_entry_le_l2_opNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (i j : ι) :
    ‖M i j‖ ≤ ‖M‖ := by
  let e : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j 1)
  let y : EuclideanSpace ℂ ι :=
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M e
  have hcoord : ‖y.ofLp i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).le_opNorm e
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hyi : y.ofLp i = M i j := by simp [y, e]
  calc
    ‖M i j‖ = ‖y.ofLp i‖ := congrArg norm hyi.symm
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖ * ‖e‖ := hop
    _ = ‖M‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM, he, mul_one]

/-- For positive imaginary height, every entry of a Hermitian resolvent is
bounded by the reciprocal height, with no dimension-dependent constant. -/
theorem norm_matrixResolvent_entry_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (i j : ι) :
    ‖matrixResolvent A z i j‖ ≤ (z.im)⁻¹ := by
  let B : Matrix ι ι ℂ := (z.re : ℂ) • 1 - A
  have hB : B.IsHermitian :=
    Matrix.isHermitian_one.smul (RCLike.conj_ofReal z.re) |>.sub hA
  have hzero : (0 : Matrix ι ι ℂ).PosSemidef := Matrix.PosSemidef.zero
  have hpencil : cauchyResolventPencil B 0 z.im 0 =
      z • (1 : Matrix ι ι ℂ) - A := by
    ext a b
    simp [cauchyResolventPencil, B, Complex.ext_iff]
    constructor <;> ring
  have hnorm : ‖(cauchyResolventPencil B 0 z.im 0)⁻¹‖ ≤ (z.im)⁻¹ :=
    norm_cauchyResolventPencil_nonsing_inv_le B 0 hB hzero hz (by simp)
  rw [hpencil] at hnorm
  exact (norm_matrix_entry_le_l2_opNorm (matrixResolvent A z) i j).trans hnorm

/-!
## Pointwise control of the resolvent error
-/

/-- The deterministic dimension-free scale used below. -/
def actualWardScale (z : ℂ) : ℝ :=
  (z.im)⁻¹ + ‖erSemicircleStieltjes z‖

/-- Every resolvent-error entry is bounded at positive height by the
resolvent scale plus the scalar semicircle comparison. -/
theorem norm_resolventError_entry_le
    {p : Params} (M : Law p) {z : ℂ} (hz : 0 < z.im)
    (ω : M.Ω) (a y : Site p.n p.W) :
    ‖resolventError M z ω a y‖ ≤ actualWardScale z := by
  calc
    ‖resolventError M z ω a y‖
        ≤ ‖green M z ω a y‖ + ‖semicircleMatrix p z a y‖ := norm_sub_le _ _
    _ ≤ (z.im)⁻¹ + ‖erSemicircleStieltjes z‖ := by
      gcongr
      · simpa [green] using
          norm_matrixResolvent_entry_le (M.H ω) (M.H_hermitian ω) hz a y
      · by_cases h : a = y <;> simp [semicircleMatrix, h]
    _ = actualWardScale z := rfl

/-!
## The concrete finite recursion
-/

end ERActualWardBound
end GaussianRing
end ERNative.BlockBand
