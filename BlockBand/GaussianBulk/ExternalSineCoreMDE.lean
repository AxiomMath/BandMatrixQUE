module

public import Mathlib
public import BlockBand.GaussianBulk.ExternalSineCoreUnitary
public import BlockBand.GaussianBulk.SaddleIdentities

/-!
# The matrix boundary MDE is the scalar MDE of the spectrum

Object: the boundary matrix Dyson equation
`IsBoundaryMDE t F E M`, i.e. `(F - (E + t⟨M⟩)) M = 1` with `Im M ≻ 0`, for a Hermitian `F` on
`ℂ^N`, real `t` and `E`. Conclusion: with `d = spectralSource F` (increasing eigenvalues of
`F`, with multiplicity), the scalar `m = ⟨M⟩ = CEH.normalizedTrace M` solves the scalar finite
MDE `FiniteMDE d E t m` of `SaddleIdentities` (`m = N⁻¹ ∑_j (d_j - E - t m)⁻¹`), and every
`d_j - (E + t m)` is nonzero. Only the resolvent identity is used (the positivity clause of
`IsBoundaryMDE` is not needed). This feeds the saddle lemmas
(`hasDerivAt_saddlePhase_zero`, `norm_mde_le_inv_sqrt`, `saddlePoint_im_lower`, ...) at
`d = spectralSource F`, `m = ⟨M⟩`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Matrix
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs

/-- Resolvent trace for a unitary diagonalization: if `F = U diag(d) U*` and
`(F - w) M = 1`, then every `d_j - w ≠ 0` and `Tr M = ∑_j (d_j - w)⁻¹`. -/
theorem trace_eq_sum_inv_of_resolvent {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (d : Fin N → ℝ) (F : Matrix (Fin N) (Fin N) ℂ)
    (hFD : F = (U : Matrix (Fin N) (Fin N) ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
      (U : Matrix (Fin N) (Fin N) ℂ)ᴴ)
    (w : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) (hM : (F - w • (1 : Matrix (Fin N) (Fin N) ℂ)) * M = 1) :
    (∀ j, (d j : ℂ) - w ≠ 0) ∧ M.trace = ∑ j, ((d j : ℂ) - w)⁻¹ := by
  set V : Matrix (Fin N) (Fin N) ℂ := (U : Matrix (Fin N) (Fin N) ℂ) with hV
  have hVV : Vᴴ * V = 1 := Matrix.UnitaryGroup.star_mul_self U
  have hVV' : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (d i : ℂ)) with hD
  set X : Matrix (Fin N) (Fin N) ℂ := Vᴴ * M * V with hX
  have hDX : (D - w • (1 : Matrix (Fin N) (Fin N) ℂ)) * X = 1 := by
    have h1 : D - w • (1 : Matrix (Fin N) (Fin N) ℂ) =
        Vᴴ * (F - w • (1 : Matrix (Fin N) (Fin N) ℂ)) * V := by
      rw [hFD, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        hVV]
      congr 1
      simp only [← Matrix.mul_assoc, hVV, Matrix.one_mul]
      rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
    rw [h1, hX]
    calc Vᴴ * (F - w • (1 : Matrix (Fin N) (Fin N) ℂ)) * V * (Vᴴ * M * V)
        = Vᴴ * ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ)) * (V * Vᴴ) * M) * V := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hVV', Matrix.mul_one, hM, Matrix.mul_one, hVV]
  have hentry : ∀ j, ((d j : ℂ) - w) * X j j = 1 := by
    intro j
    have := congrFun (congrFun hDX j) j
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hD, Matrix.sub_apply,
      Matrix.diagonal_mul, Matrix.smul_apply, Matrix.one_apply_eq] at this
    rw [sub_mul, ← this, smul_eq_mul]
  have hne : ∀ j, (d j : ℂ) - w ≠ 0 := fun j h => by
    have := hentry j
    rw [h, zero_mul] at this
    exact zero_ne_one this
  refine ⟨hne, ?_⟩
  have htr : M.trace = X.trace := by
    rw [hX, Matrix.trace_mul_cycle, hVV', Matrix.one_mul]
  rw [htr, Matrix.trace]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.diag_apply]
  exact (eq_inv_of_mul_eq_one_right (hentry j))

/-- Matrix to scalar MDE: if `M` solves the boundary MDE for the Hermitian source `F`
at `(t, E)`, then `m = ⟨M⟩` solves the scalar finite MDE for the increasing eigenvalues
`d = spectralSource F`, and `d_j ≠ E + t m` for every `j`. -/
theorem finiteMDE_of_boundaryMDE {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian)
    (t E : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) (h : IsBoundaryMDE t F E M) :
    FiniteMDE (spectralSource F hF) E t (CEH.normalizedTrace M) ∧
      ∀ j, ((spectralSource F hF j : ℝ) : ℂ) - saddlePoint E t (CEH.normalizedTrace M) ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_unitary_diagonal_spectralSource F hF
  obtain ⟨hne, htr⟩ := trace_eq_sum_inv_of_resolvent U (spectralSource F hF) F hU
    ((E : ℂ) + (t : ℂ) * CEH.normalizedTrace M) M h.1
  refine ⟨?_, hne⟩
  unfold FiniteMDE finiteStieltjes complexMean saddlePoint
  conv_lhs => rw [show CEH.normalizedTrace M = (N : ℂ)⁻¹ * M.trace from rfl, htr]
  push_cast
  rfl

end BlockBand.GaussianBulk
