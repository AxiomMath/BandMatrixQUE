module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Internal.Contracts.Transmission
public import BlockBand.Counting.SpectralScaling
public import BlockBand.Model.Construction.OrderedEigenvalues

/-!
# Relative localization: eigenvalue labels and Weyl displacement

For a Hermitian `H : Matrix (Fin N) (Fin N) ℂ`:
* `freshEigenvalue_monotone` : `freshEigenvalue H` (increasing rank) is monotone;
* `freshEigenvalue_eq_dyson` : `freshEigenvalue H k = dysonEigenvalue N H k.rev` (nonincreasing
  labels, defined through the Hermitian part `(H + Hᴴ)/2`);
* `abs_freshEigenvalue_sub_le` (Weyl) : if `‖(A - B)x‖ ≤ ε‖x‖` for all `x` (`l2Norm`), then
  `|λ_k(A) - λ_k(B)| ≤ ε` for every rank `k`, the form of the displacement clause of
  `SpectralGoodEventContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Model.Construction

variable {N : ℕ}

theorem freshEigenvalue_eq_eigenvalues₀ {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (k : Fin N) :
    freshEigenvalue H k = hH.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm k).rev := by
  rw [freshEigenvalue, rawIncreasingEigenvalue_eq _ _ hH]
  rfl

/-- The increasing eigenvalues are monotone in the rank. -/
theorem freshEigenvalue_monotone {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    Monotone (freshEigenvalue H) := by
  intro i j hij
  rw [freshEigenvalue_eq_eigenvalues₀ hH, freshEigenvalue_eq_eigenvalues₀ hH]
  exact hH.eigenvalues₀_antitone (Fin.rev_le_rev.mpr (show Fin.cast _ i ≤ Fin.cast _ j from hij))

theorem eigenvalues₀_congr {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : A = B) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  subst h; rfl

/-- The nonincreasing labels of `dysonEigenvalue` are the reversal of the increasing ones. -/
theorem freshEigenvalue_eq_dyson {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (k : Fin N) : freshEigenvalue H k = dysonEigenvalue N H k.rev := by
  have h2 : H + Hᴴ = ((2 : ℝ) : ℂ) • H := by
    rw [hH.eq, show ((2 : ℝ) : ℂ) = 2 by norm_num, two_smul]
  have hS : (((2 : ℝ) : ℂ) • H).IsHermitian := h2 ▸ isHermitian_add_transpose_self H
  have hsc := BlockBand.Counting.eigenvaluesOrdered_positiveScale hH 2 two_pos hS
  unfold dysonEigenvalue
  rw [eigenvalues₀_congr (isHermitian_add_transpose_self H) hS h2, hsc,
    freshEigenvalue_eq_eigenvalues₀ hH]
  have : (Fin.cast (Fintype.card_fin N).symm k).rev = Fin.cast (Fintype.card_fin N).symm k.rev := by
    ext; simp [Fin.val_rev]
  rw [this]
  ring

/-- **Weyl's inequality.** An `l2Norm` operator bound on `A - B` bounds every rank displacement. -/
theorem abs_freshEigenvalue_sub_le {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {ε : ℝ} (h : ∀ x : Fin N → ℂ, l2Norm ((A - B) *ᵥ x) ≤ ε * l2Norm x)
    (k : Fin N) : |freshEigenvalue A k - freshEigenvalue B k| ≤ ε := by
  rw [freshEigenvalue_eq_eigenvalues₀ hA, freshEigenvalue_eq_eigenvalues₀ hB]
  simp only [Matrix.IsHermitian.eigenvalues₀]
  apply LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le
    (isSymmetric_toEuclideanLin_iff.mpr hA) (isSymmetric_toEuclideanLin_iff.mpr hB)
    finrank_euclideanSpace (fun x ↦ ?_)
  have hx := h (WithLp.ofLp x)
  rw [← map_sub, Matrix.toLpLin_apply]
  simpa only [l2Norm, EuclideanSpace.norm_eq, WithLp.ofLp_toLp] using hx

end BlockBand.Palm.RelativeLocalization
