module

public import BlockBand.SourceProcess.PhysApprox.ConjSymLaw
public import BlockBand.SourceProcess.RawTag.UpdPathFacts
public import BlockBand.SourceProcess.Closing.Defs

/-!
# The path objects at the conjugated path

For Hermitian GUE blocks (almost surely), with `ω̄ = conjPath ω`:
* `fullPathMatrix_conjPath`: `𝓜(ω̄) = 𝓜(ω)ᵀ` (`E` and `z_∂ 1` are symmetric);
* `fullInverse_conjPath`, `scatteringMatrix_conjPath`: `G(ω̄) = G(ω)ᵀ`, `𝕊(ω̄) = 𝕊(ω)ᵀ`;
* `tagResponse_conjPath`: `Y(ω̄) = conj(𝕊 Y 𝕊ᴴ)` (boundary identity `G₂₁ = 𝕊𝒰ᴴ`);
* `farTransmission_conjPath`: `T_far(ω̄) = conj(1 - S_ff S_ffᴴ)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.Closing
open scoped ComplexConjugate

section Generic

variable {l m n : Type*}

theorem matConj_mul [Fintype m] (M : Matrix l m ℂ) (N : Matrix m n ℂ) :
    matConj (M * N) = matConj M * matConj N :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem matConj_sub (M N : Matrix m n ℂ) : matConj (M - N) = matConj M - matConj N :=
  Matrix.map_sub _ (map_sub (starRingEnd ℂ)) M N

theorem matConj_one [DecidableEq n] : matConj (1 : Matrix n n ℂ) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem conjTranspose_transpose' (M : Matrix m n ℂ) : (Mᵀ)ᴴ = matConj M := by
  ext i j
  simp [matConj_apply]

theorem transpose_eq_matConj_conjTranspose (M : Matrix m n ℂ) : Mᵀ = matConj Mᴴ := by
  ext i j
  simp [matConj_apply]

theorem matConj_conjTranspose (M : Matrix m n ℂ) : matConj Mᴴ = (matConj M)ᴴ := by
  ext i j
  simp [matConj_apply]

theorem transpose_eq_matConj_of_isHermitian {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    Mᵀ = matConj M := by
  ext i j
  simp only [transpose_apply, matConj_apply]
  exact (hM.apply j i).symm

theorem trace_matConj [Fintype n] (M : Matrix n n ℂ) : (matConj M).trace = conj M.trace := by
  simp [Matrix.trace, matConj_apply]

theorem re_trace_matConj [Fintype n] (M : Matrix n n ℂ) : (matConj M).trace.re = M.trace.re := by
  rw [trace_matConj, Complex.conj_re]

end Generic

variable {W : ℕ}

/-- Entrywise conjugation of a path sample. -/
def sampleConj {r : ℕ} (p : PathSample W r) : PathSample W r :=
  (fun i => matConj (p.1 i), fun i => matConj (p.2.1 i), fun j => matConj (p.2.2 j))

theorem pathAt_conjPath (n : ℕ) (ω : GrowthPath W) :
    pathAt W n (conjPath ω) = sampleConj (pathAt W n ω) := by
  simp only [pathAt, conjPath, sampleConj, matConj_conjTranspose]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext j
  fin_cases j <;> rfl

theorem pathMatrix_sampleConj {r : ℕ} (p : PathSample W r) :
    pathMatrix (sampleConj p) = matConj (pathMatrix p) := by
  ext x y
  simp only [pathMatrix, sampleConj, matConj_apply]
  split_ifs <;> simp

theorem pathPortCoupling_sampleConj {r : ℕ} (p : PathSample W r) :
    pathPortCoupling (sampleConj p) = matConj (pathPortCoupling p) := by
  ext x y
  simp only [pathPortCoupling, sampleConj, matConj_apply]
  split_ifs <;> simp

/-- `𝓜(ω̄) = 𝓜(ω)ᵀ` for Hermitian blocks. -/
theorem fullPathMatrix_conjPath (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    fullPathMatrix b E W n (conjPath ω) = (fullPathMatrix b E W n ω)ᵀ := by
  have hH := BlockBand.Transmission.Bridge.pathMatrix_pathAt_isHermitian n ω hA
  set H := pathMatrix (pathAt W n ω)
  set C := pathPortCoupling (pathAt W n ω)
  have e1 : matConj H - (E : ℂ) • 1 = (H - (E : ℂ) • 1)ᵀ := by
    rw [transpose_sub, transpose_smul, transpose_one, transpose_eq_matConj_of_isHermitian hH]
  have e2 : matConj C = Cᴴᵀ := by
    rw [transpose_eq_matConj_conjTranspose, conjTranspose_conjTranspose]
  have e3 : (matConj C)ᴴ = Cᵀ := by
    rw [transpose_eq_matConj_conjTranspose, matConj_conjTranspose]
  have e4 : boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
      (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))ᵀ := by
    rw [transpose_smul, transpose_one]
  rw [fullPathMatrix, fullPathMatrix, fromBlocks_transpose, pathAt_conjPath,
    pathMatrix_sampleConj, pathPortCoupling_sampleConj, ← e1, ← e2, ← e3, ← e4]

/-- `G(ω̄) = G(ω)ᵀ` for Hermitian blocks. -/
theorem fullInverse_conjPath (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    fullInverse b E W n (conjPath ω) = (fullInverse b E W n ω)ᵀ := by
  rw [fullInverse, fullInverse, fullPathMatrix_conjPath b E n ω hA]
  exact (transpose_nonsing_inv _).symm

theorem boundaryResolvent_conjPath (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    boundaryResolvent b E W n (conjPath ω) = (boundaryResolvent b E W n ω)ᵀ := by
  rw [boundaryResolvent, boundaryResolvent, fullInverse_conjPath b E n ω hA]
  ext i j
  rfl

/-- `𝕊(ω̄) = 𝕊(ω)ᵀ` for Hermitian blocks. -/
theorem scatteringMatrix_conjPath (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    scatteringMatrix b E W n (conjPath ω) = (scatteringMatrix b E W n ω)ᵀ := by
  rw [scatteringMatrix, scatteringMatrix, boundaryResolvent_conjPath b E n ω hA, transpose_sub,
    transpose_one, transpose_smul]

/-- `𝒰(ω̄) = (𝕊𝒰ᴴ)ᵀ` (boundary identity `G₂₁ = 𝕊𝒰ᴴ`). -/
theorem boundaryToInterior_conjPath (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    boundaryToInterior b E W n (conjPath ω) =
      (scatteringMatrix b E W n ω * (boundaryToInterior b E W n ω)ᴴ)ᵀ := by
  rw [← BlockBand.SourceProcess.RawTag.fullInverse_21_eq b E n ω hA, boundaryToInterior,
    fullInverse_conjPath b E n ω hA]
  ext i j
  rfl

theorem matConj_tagProjection (n k : ℕ) : matConj (tagProjection W n k) = tagProjection W n k := by
  ext x y
  simp only [tagProjection, matConj_apply, diagonal_apply]
  split_ifs <;> simp

/-- **`Y(ω̄) = conj(𝕊 Y 𝕊ᴴ)`** for Hermitian blocks. -/
theorem tagResponse_conjPath (b E : ℝ) (n k : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    tagResponse b E W n k (conjPath ω) =
      matConj (scatteringMatrix b E W n ω * tagResponse b E W n k ω *
        (scatteringMatrix b E W n ω)ᴴ) := by
  have e : scatteringMatrix b E W n ω * ((boundaryToInterior b E W n ω)ᴴ *
      tagProjection W n k * boundaryToInterior b E W n ω) * (scatteringMatrix b E W n ω)ᴴ =
      (scatteringMatrix b E W n ω * (boundaryToInterior b E W n ω)ᴴ) * tagProjection W n k *
        (scatteringMatrix b E W n ω * (boundaryToInterior b E W n ω)ᴴ)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [tagResponse, tagResponse, boundaryToInterior_conjPath b E n ω hA, conjTranspose_transpose',
    transpose_eq_matConj_conjTranspose, e]
  simp only [matConj_mul, matConj_tagProjection]

theorem farReflection_conjPath (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    farReflection b E W n (conjPath ω) = (farReflection b E W n ω)ᵀ := by
  rw [farReflection, farReflection, scatteringMatrix_conjPath b E n ω hA]
  ext i j
  rfl

/-- `T_far(ω̄) = conj(1 - S_ff S_ffᴴ)` for Hermitian blocks. -/
theorem farTransmission_conjPath (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    farTransmission b E W n (conjPath ω) =
      matConj (1 - farReflection b E W n ω * (farReflection b E W n ω)ᴴ) := by
  rw [farTransmission, farReflection_conjPath b E n ω hA, conjTranspose_transpose',
    transpose_eq_matConj_conjTranspose, matConj_sub, matConj_one, matConj_mul]

end BlockBand.SourceProcess.PhysApprox
