module
public import BlockBand.QUE.Invariance.PhysicalRotationGrid
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Grid approximation of torus rotations

Every real angle `x` is approximated by the grid angle `⌊n x⌋/n` with error at most `1/n`
(`physicalRotationApproximation_real_error`), so the grid rotations converge to every rotation of
the torus as the number of blocks `n` diverges (`physicalRotationApproximation_tendsto`).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Invariance
open Filter
open scoped Topology
open BlockBand.Model.Construction

def physicalRotationApproximation (p : Parameters) (x : ℝ) : Torus :=
  physicalProfileGrid p (⌊(p.n : ℝ)*x⌋ : ZMod p.n)

/-- The modular grid angle equals the quotient of the real floor ratio. -/
theorem physicalRotationApproximation_eq (p : Parameters) (x : ℝ) :
    physicalRotationApproximation p x = QuotientAddGroup.mk ((⌊(p.n : ℝ)*x⌋ : ℝ)/p.n) := by
  rw [physicalRotationApproximation, physicalProfileGrid_eq_toAddCircle,
    ZMod.toAddCircle_intCast]

/-- Real representatives have uniform rounding error at most one over n. -/
theorem physicalRotationApproximation_real_error (p : Parameters) (x : ℝ) :
    |((⌊(p.n : ℝ)*x⌋ : ℝ)/(p.n : ℝ))-x| ≤ 1/(p.n : ℝ) := by
  have hn : (0 : ℝ)<p.n := Nat.cast_pos.mpr p.n_pos
  have hl := Int.floor_le ((p.n : ℝ)*x)
  have hu := Int.lt_floor_add_one ((p.n : ℝ)*x)
  have hratio : ((⌊(p.n : ℝ)*x⌋ : ℝ)/(p.n : ℝ)) ≤ x :=
    (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hl)
  rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
  apply (le_div_iff₀ hn).mpr
  have hcancel : ((⌊(p.n : ℝ)*x⌋ : ℝ)/(p.n : ℝ))*(p.n : ℝ) =
    (⌊(p.n : ℝ)*x⌋ : ℝ) := div_mul_cancel₀ _ hn.ne'
  nlinarith

/-- Grid angles converge to every real-lifted angle as the number of blocks diverges. -/
theorem physicalRotationApproximation_tendsto (ps : ℕ → Parameters) (x : ℝ)
    (hn : Tendsto (fun j => ((ps j).n : ℝ)) atTop atTop) :
    Tendsto (fun j => physicalRotationApproximation (ps j) x) atTop
      (𝓝 (QuotientAddGroup.mk x : Torus)) := by
  have hi : Tendsto (fun j => 1/((ps j).n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hn
  have he : Tendsto (fun j => |((⌊((ps j).n : ℝ)*x⌋ : ℝ)/((ps j).n : ℝ))-x|)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun j => physicalRotationApproximation_real_error (ps j) x) hi
  have hr : Tendsto (fun j => ((⌊((ps j).n : ℝ)*x⌋ : ℝ)/((ps j).n : ℝ))) atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using he
  simp only [physicalRotationApproximation_eq]
  exact (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.tendsto.comp hr
end BlockBand.QUE.Invariance
