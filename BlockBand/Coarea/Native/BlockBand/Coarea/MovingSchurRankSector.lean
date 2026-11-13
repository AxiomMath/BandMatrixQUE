module

public import BlockBand.Coarea.Native.BlockBand.Coarea.RankSector
public import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Moving Schur crossings and fixed ordered-rank sectors

The Schur inertia bookkeeping at a moving simple crossing.  The fixed ordered-rank predicate of
the coarea theorem is stated as an exact sum, rather than by solving for the retained rank with
truncated subtraction.  The file also records the local no-double-counting consequence of the
strict downward crossing: near the crossing, the selected branch has the sign of `t - s`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix Filter
open scoped ComplexOrder Topology

/-- The full zero has fixed one-based ordered rank `r + 1` exactly when the
exterior negative count plus the retained negative count plus one is `r + 1`.

Normalization: the retained block comes first, `N_-` counts strictly negative
eigenvalues, and the crossing zero occupies position `N_- + 1`.  The statement
uses only addition, so it does not hide a side condition behind truncated
natural-number subtraction. -/
theorem orderedZeroRank_fromBlocks_eq_iff
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (D : Matrix n n ℂ) [Invertible D]
    (hA : A.IsHermitian) (hD : D.IsHermitian)
    (r : Fin (Fintype.card (m ⊕ n))) :
    let hFull : (Matrix.fromBlocks A B Bᴴ D).IsHermitian :=
      Matrix.isHermitian_fromBlocks_iff.mpr
        ⟨hA, rfl, Matrix.conjTranspose_conjTranspose B, hD⟩
    let hInv : (⅟D).IsHermitian := by
      rw [Matrix.invOf_eq_nonsing_inv D]
      exact hD.inv
    let hSchur : (A - B * ⅟D * Bᴴ).IsHermitian :=
      hA.sub (Matrix.isHermitian_mul_mul_conjTranspose B hInv)
    orderedZeroRank hFull = r.val + 1 ↔
      negativeEigenvalueCount hD + negativeEigenvalueCount hSchur + 1 =
        r.val + 1 := by
  dsimp only
  rw [orderedZeroRank_fromBlocks A B D hA hD]
  simp only [orderedZeroRank, Nat.add_assoc]

/-- A differentiable scalar branch with a strictly negative derivative at a
zero crosses downward there: locally its sign is the sign of `t - s`.

This is the local interval/no-double-counting statement used for a selected
simple Schur branch.  It makes no claim about other eigenvalue
branches or about global uniqueness of the crossing. -/
theorem eventually_sign_eq_of_strict_downward_crossing
    {e : ℝ → ℝ} {e' t : ℝ}
    (hederiv : HasDerivAt e e' t) (hslope : e' < 0)
    (hezero : e t = 0) :
    ∀ᶠ s in 𝓝 t, SignType.sign (e s) = SignType.sign (t - s) := by
  apply eventually_nhdsWithin_sign_eq_of_deriv_neg
  · simpa [hederiv.deriv] using hslope
  · exact hezero

/-- Fixed ordered-rank sector and local sign change at a simple moving Schur
crossing.

The non-pole hypothesis is the invertibility of the exterior block `D`.  Simplicity and
normalization are carried by `SimpleHermitianEigenpair`.  At the crossing, reconstruction gives
a full null vector; the fixed-rank condition is equivalent to the exact
exterior-plus-retained negative-count formula; and the selected branch crosses
from positive to negative locally. -/
theorem movingSchurRankSector_iff
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (D : Matrix n n ℂ) [Invertible D]
    (hA : A.IsHermitian) (hD : D.IsHermitian)
    {S : ℝ → Matrix m m ℂ} {vCurve : ℝ → m → ℂ} {e : ℝ → ℝ}
    {v' : m → ℂ} {e' t : ℝ}
    (hSt : S t = A - B * ⅟D * Bᴴ)
    (hsimple : SimpleHermitianEigenpair (S t) (e t) (vCurve t))
    (hezero : e t = 0)
    (hSderiv : HasDerivAt S
      (-(schurClock (schurTransfer Bᴴ D))) t)
    (hvderiv : HasDerivAt vCurve v' t)
    (hederiv : HasDerivAt e e' t)
    (heigenpair : ∀ s : ℝ, S s *ᵥ vCurve s = (e s : ℂ) • vCurve s)
    (r : Fin (Fintype.card (m ⊕ n))) :
    let hFull : (Matrix.fromBlocks A B Bᴴ D).IsHermitian :=
      Matrix.isHermitian_fromBlocks_iff.mpr
        ⟨hA, rfl, Matrix.conjTranspose_conjTranspose B, hD⟩
    let hInv : (⅟D).IsHermitian := by
      rw [Matrix.invOf_eq_nonsing_inv D]
      exact hD.inv
    let hSchur : (A - B * ⅟D * Bᴴ).IsHermitian :=
      hA.sub (Matrix.isHermitian_mul_mul_conjTranspose B hInv)
    e' < 0 ∧
      (orderedZeroRank hFull = r.val + 1 ↔
        negativeEigenvalueCount hD + negativeEigenvalueCount hSchur + 1 =
          r.val + 1) ∧
      Matrix.fromBlocks A B Bᴴ D *ᵥ
          schurReconstruction Bᴴ D (vCurve t) = 0 ∧
      (∀ᶠ s in 𝓝 t, SignType.sign (e s) = SignType.sign (t - s)) := by
  dsimp only
  have hbase := rankSector_of_simpleSchurCrossing A B D hA hD hSt hsimple
    hezero hSderiv hvderiv hederiv heigenpair
  dsimp only at hbase
  refine ⟨hbase.1, ?_, hbase.2.2, ?_⟩
  · exact orderedZeroRank_fromBlocks_eq_iff A B D hA hD r
  · exact eventually_sign_eq_of_strict_downward_crossing hederiv hbase.1 hezero

end CoareaNative.BlockBand
