module

public import BlockBand.Critical.MatrixClosing.CollarFunction
public import BlockBand.Critical.Collar.Density.CondSchurSigma
public import BlockBand.Critical.Collar.Density.Conditional

/-!
# Matrix closing, mean clause: the middle-only shift of the conditional density

The shift of the middle eigenvalue is covered by the sharp conditional collar comparison, with the
same `H` and `L` and an unchanged Gaussian conditioning. Deterministic, plus the a.e. simple
spectrum of `F + A⁰` under the traceless law.

* `freshProjector_add_smul_one_of_simple`: on simple spectrum, `P_ℓ(K + r) = P_ℓ(K)` (`r` real).
* `sigma_add_smul_one`: `Σ_{F+r}(e + r) = Σ_F(e)` for Hermitian `F` (canonical density).
* `collarTopBlock_middle`, `collarTW_middle`, `collarFW_middle`: at `(e + s, X - s)` the blocks
  `D`, `T` are unchanged and `F` becomes `F - s`.
* **`condCollarDensity_middle`**: the conditional top density at `(e + s, X - s)` is `TΣ_F(s)T*`
  with the unshifted `T`, `F`, i.e. the middle-shifted density.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Mean

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Coarea.FreshPalm
open scoped ComplexOrder

variable {N : ℕ}

theorem freshProjector_isHermitian (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    (freshProjector K ℓ).IsHermitian := by
  unfold freshProjector IsHermitian
  rw [conjTranspose_vecMulVec, star_star]

theorem freshProjector_mul_conj_of_simple {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : SimpleSpectrum K) (m : Fin N) :
    freshProjector K m * K = ((freshEigenvalue K m : ℝ) : ℂ) • freshProjector K m := by
  have h := congrArg conjTranspose (hK.mul_freshProjector m)
  rw [conjTranspose_mul, hK.1.eq, (freshProjector_isHermitian K m).eq, conjTranspose_smul,
    (freshProjector_isHermitian K m).eq, Complex.star_def, Complex.conj_ofReal] at h
  exact h

/-- On simple spectrum, a matrix `M` with `KM = λ_ℓ M` satisfies `P_ℓ M = M`. -/
theorem freshProjector_mul_of_eigen {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : SimpleSpectrum K) (ℓ : Fin N) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : K * M = ((freshEigenvalue K ℓ : ℝ) : ℂ) • M) : freshProjector K ℓ * M = M := by
  have hzero : ∀ m, m ≠ ℓ → freshProjector K m * M = 0 := by
    intro m hm
    have h1 : ((freshEigenvalue K m : ℝ) : ℂ) • (freshProjector K m * M) =
        ((freshEigenvalue K ℓ : ℝ) : ℂ) • (freshProjector K m * M) := by
      rw [← smul_mul, ← freshProjector_mul_conj_of_simple hK m, Matrix.mul_assoc, hM, Matrix.mul_smul]
    have h2 : (((freshEigenvalue K m : ℝ) : ℂ) - ((freshEigenvalue K ℓ : ℝ) : ℂ)) •
        (freshProjector K m * M) = 0 := by rw [sub_smul, h1, sub_self]
    have hne : ((freshEigenvalue K m : ℝ) : ℂ) - ((freshEigenvalue K ℓ : ℝ) : ℂ) ≠ 0 := by
      rw [sub_ne_zero, Ne, Complex.ofReal_inj]
      exact fun h => hm (hK.2 h)
    exact (smul_eq_zero.1 h2).resolve_left hne
  calc freshProjector K ℓ * M = ∑ m, freshProjector K m * M := by
        rw [Finset.sum_eq_single ℓ (fun m _ hm => hzero m hm) (by simp)]
    _ = (∑ m, freshProjector K m) * M := by rw [Finset.sum_mul]
    _ = M := by rw [hK.sum_freshProjector, Matrix.one_mul]

/-- **The fresh projector is invariant under a real shift** (simple spectrum). -/
theorem freshProjector_add_smul_one_of_simple {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : SimpleSpectrum K) (r : ℝ) (ℓ : Fin N) :
    freshProjector (K + (r : ℂ) • 1) ℓ = freshProjector K ℓ := by
  have hK' := hK.add_smul_one r
  have hlam := freshEigenvalue_add_smul_one hK.1 r ℓ
  set P := freshProjector K ℓ
  set P' := freshProjector (K + (r : ℂ) • 1) ℓ
  have h1 : K * P' = ((freshEigenvalue K ℓ : ℝ) : ℂ) • P' := by
    have h := hK'.mul_freshProjector ℓ
    rw [hlam, add_mul, smul_mul, Matrix.one_mul] at h
    rw [Complex.ofReal_add, add_smul] at h
    exact add_right_cancel h
  have h2 : (K + (r : ℂ) • 1) * P = ((freshEigenvalue (K + (r : ℂ) • 1) ℓ : ℝ) : ℂ) • P := by
    rw [hlam, add_mul, smul_mul, Matrix.one_mul, hK.mul_freshProjector, Complex.ofReal_add,
      add_smul]
  have hPP' : P * P' = P' := freshProjector_mul_of_eigen hK ℓ h1
  have hP'P : P' * P = P := freshProjector_mul_of_eigen hK' ℓ h2
  have hP := (freshProjector_isHermitian K ℓ).eq
  have hP' := (freshProjector_isHermitian (K + (r : ℂ) • 1) ℓ).eq
  calc P' = P * P' := hPP'.symm
    _ = Pᴴ * P'ᴴ := by rw [hP, hP']
    _ = (P' * P)ᴴ := (conjTranspose_mul _ _).symm
    _ = P := by rw [hP'P, hP]

/-- **Real shift of the canonical density**: `Σ_{F+r}(e + r) = Σ_F(e)`. -/
theorem sigma_add_smul_one (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {c : ℝ} (hc : 0 < c) (r e : ℝ) :
    sigma (F + (r : ℂ) • 1) c (e + r) = sigma F c e := by
  ext i j
  simp only [sigma, Matrix.of_apply]
  refine Finset.sum_congr rfl fun ℓ _ => integral_congr_ae ?_
  filter_upwards [Collar.Density.ae_simpleSpectrum_add_traceless hF hc hN] with A0 hA0
  have heq : F + (r : ℂ) • 1 + A0 = (F + A0) + (r : ℂ) • 1 := by abel
  simp only [palmWeight]
  rw [heq, freshEigenvalue_add_smul_one hA0.1, freshProjector_add_smul_one_of_simple hA0]
  congr 2
  unfold BlockBand.Palm.scalarWeight
  congr 1
  ring

/-!
## The middle-only shift in the conditional collar variables
-/

section Collar

open Collar.Density

variable {W : ℕ}

theorem collarTopBlock_middle (e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) :
    collarTopBlock (e + s) (X - (s : ℂ) • 1) ω = collarTopBlock e X ω := by
  unfold collarTopBlock
  push_cast
  rw [add_smul]
  abel

theorem collarTW_middle (e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) :
    collarTW (e + s) (X - (s : ℂ) • 1) ω = collarTW e X ω := by
  unfold collarTW collarT
  rw [collarTopBlock_middle]

theorem collarFW_middle (e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) :
    collarFW (e + s) (X - (s : ℂ) • 1) ω = collarFW e X ω + ((-s : ℝ) : ℂ) • 1 := by
  unfold collarFW collarF
  rw [collarTopBlock_middle]
  ext i j
  simp only [submatrix_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, smul_eq_mul]
  push_cast
  split_ifs <;> ring

/-- **The middle-only shift of the conditional density**: at energy `e + s` and old response
`X - s` the conditional top density is `T Σ_F(s) T*` with the unshifted `T`, `F` (`D` unchanged). -/
theorem condCollarDensity_middle (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e s : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {ω : LayerSample W .common} (hA : ∀ k, (ω.1 k).IsHermitian) :
    condCollarDensity b (e + s) (X - (s : ℂ) • 1) ω =
      collarTW e X ω * sigma (collarFW e X ω) (1 - 2 * b) s * (collarTW e X ω)ᴴ := by
  have hc : 0 < 1 - 2 * b := by linarith
  have h := sigma_add_smul_one hW (collarFW_isHermitian e hX hA) hc (-s) s
  rw [add_neg_cancel] at h
  unfold condCollarDensity
  rw [collarTW_middle, collarFW_middle, h]

end Collar

end BlockBand.Critical.MatrixClosing.Mean
