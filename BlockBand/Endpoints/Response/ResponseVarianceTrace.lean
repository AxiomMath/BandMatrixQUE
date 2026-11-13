module

public import BlockBand.Endpoints.Response.ResponseVarianceTraceAlgebra

/-!
# The signed response trace bound

Statement (`rvSignedTraceBound_holds : RvSignedTraceBound`). For `x ≥ 0`, `0 ≤ y < 1` and
`c = rvD_const x y = 2(x + y) + 2(y²/(1-y) + x²)`: for every `0 < b < 1/2`, every real energy
`-2 < e < 2`, every `W, r`, every signed `q` and every sample `ω` with Hermitian blocks and
invertible full path matrix,
`|∂_q(F_L+F_R)| ≤ 4η((x + y)|Re Tr B_q| + c √g ‖B_q‖_HS)`, with `η = Im z_b(e)`,
`g = Tr T_L` (`rvConductance`), `B_q = rvSourceGram` and `‖·‖_HS = √hsSq`.

The proof reduces to the abstract two-port algebra (`rvD_abstract_bound`):
* `rvD_portInclusion_sum`: `J₀J₀* + J₁J₁* = I`;
* `rvD_sourceGram_sub`: `B_{q₊} - B_{q₋} = B_q` (`sourceDiag` is linear in `q`);
* `rvD_signedDeriv_eq`: `∂_q(F_L+F_R) = Re DF(T₀)[Ṫ₀[B_q]] + Re DF(T₁)[Ṫ₁[B_q]]` (linearity of
  the zero-source derivative in the source Gram matrix).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator ComplexConjugate

variable {W n : ℕ}

theorem rvD_portInclusion_sum :
    portInclusion W 0 * (portInclusion W 0)ᴴ + portInclusion W 1 * (portInclusion W 1)ᴴ = 1 := by
  ext ⟨i, a⟩ ⟨j, c⟩
  simp only [Matrix.add_apply, mul_apply, conjTranspose_apply, portInclusion, of_apply, one_apply,
    Prod.mk.injEq]
  fin_cases i <;> fin_cases j <;> by_cases h : a = c <;> simp [h]

/-- The zero-source scattering matrix is the pencil scattering matrix of `𝓜`. -/
theorem rvD_scattering_eq (b e : ℝ) (ω : GrowthPath W) :
    scatteringMatrix b e W n ω =
      pencilScattering (etaZ b e) (leadInclusion W n) (fullPathMatrix b e W n ω) := by
  rw [← absorbedScattering_zero b e (fun _ => 0) ω,
    absorbedScattering_eq (q := fun _ => 0) (fun _ => le_rfl), absorbedPencil_zero]

/-- Unitarity at zero source: `𝕊₀*𝕊₀ = I` (Hermitian blocks, invertible `𝓜`). -/
theorem rvD_scattering_unitary {b e : ℝ} {ω : GrowthPath W} (hH : ∀ k, (ω.1 k).IsHermitian)
    (hM : IsUnit (fullPathMatrix b e W n ω).det) :
    (pencilScattering (etaZ b e) (leadInclusion W n) (fullPathMatrix b e W n ω))ᴴ *
      pencilScattering (etaZ b e) (leadInclusion W n) (fullPathMatrix b e W n ω) = 1 := by
  have hW := fullPathMatrix_ward (b := b) (E := e) (n := n) hH
  have hW' : fullPathMatrix b e W n ω - (fullPathMatrix b e W n ω)ᴴ =
      ((2 : ℂ) * Complex.I) • (((etaZ b e : ℝ) : ℂ) • (leadInclusion W n * (leadInclusion W n)ᴴ) +
        0) := by
    rw [hW, add_zero, smul_smul]
    congr 1
    push_cast
    ring
  have h := pencilScattering_gram hM hW'
  rw [h]
  simp

theorem rvD_sourceDiag_sub (q : ℝ → ℝ) :
    sourceDiag W n (posPart q) - sourceDiag W n (negPart q) = sourceDiag W n q := by
  rw [sourceDiag, sourceDiag, sourceDiag, diagonal_sub]
  congr 1
  funext z
  rcases z with s | a
  · simp only [Sum.elim_inl]
    rw [← Complex.ofReal_sub, ← sub_div, posPart_sub_negPart]
  · simp

/-- `B_{q₊} - B_{q₋} = B_q`. -/
theorem rvD_sourceGram_sub (b e : ℝ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    pencilSourceGram (fullPathMatrix b e W n ω) (sourceRoot W n (posPart q)) (leadInclusion W n) -
      pencilSourceGram (fullPathMatrix b e W n ω) (sourceRoot W n (negPart q))
        (leadInclusion W n) = rvSourceGram b e W n q ω := by
  rw [pencilSourceGram_sourceRoot (q := posPart q) (fun t => le_max_right _ _),
    pencilSourceGram_sourceRoot (q := negPart q) (fun t => le_max_right _ _), ← Matrix.sub_mul, ← Matrix.mul_sub,
    rvD_sourceDiag_sub]
  rfl

theorem rvD_sourceGram_isHermitian (b e : ℝ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    (rvSourceGram b e W n q ω).IsHermitian := by
  refine isHermitian_conjTranspose_mul_mul _ ?_
  rw [sourceDiag]
  refine isHermitian_diagonal_of_self_adjoint _ ?_
  funext z
  rcases z with s | a
  · simp only [Pi.star_apply, Sum.elim_inl, Complex.star_def, Complex.conj_ofReal]
  · simp

/-- Linearity: the sample-wise signed derivative is the zero-source derivative along the signed
source Gram matrix `B_q`. -/
theorem rvD_signedDeriv_eq (b e x y : ℝ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    rvSignedDeriv b e x y W n q ω =
      (ratioDetDeriv x y
          (portDefectOf (pencilScattering (etaZ b e) (leadInclusion W n)
            (fullPathMatrix b e W n ω)) (portInclusion W 0))
          (rvD_defectDeriv (etaZ b e) (pencilScattering (etaZ b e) (leadInclusion W n)
            (fullPathMatrix b e W n ω)) (rvSourceGram b e W n q ω) (portInclusion W 0))).re +
        (ratioDetDeriv x y
          (portDefectOf (pencilScattering (etaZ b e) (leadInclusion W n)
            (fullPathMatrix b e W n ω)) (portInclusion W 1))
          (rvD_defectDeriv (etaZ b e) (pencilScattering (etaZ b e) (leadInclusion W n)
            (fullPathMatrix b e W n ω)) (rvSourceGram b e W n q ω) (portInclusion W 1))).re := by
  have hT : ∀ (R : Matrix (FullSite W n) (FullSite W n) ℂ) (i : Fin 2),
      pencilPortDefect (etaZ b e) (leadInclusion W n) (fullPathMatrix b e W n ω) R
        (portInclusion W i) 0 =
      portDefectOf (pencilScattering (etaZ b e) (leadInclusion W n) (fullPathMatrix b e W n ω))
        (portInclusion W i) := fun R i => by
    rw [pencilPortDefect, absorbedPencil_zero]
  have hD : ∀ (R : Matrix (FullSite W n) (FullSite W n) ℂ) (i : Fin 2),
      pencilPortDefectDeriv (etaZ b e) (leadInclusion W n) (fullPathMatrix b e W n ω) R
        (portInclusion W i) =
      rvD_defectDeriv (etaZ b e) (pencilScattering (etaZ b e) (leadInclusion W n)
        (fullPathMatrix b e W n ω)) (pencilSourceGram (fullPathMatrix b e W n ω) R
          (leadInclusion W n)) (portInclusion W i) := fun R i => rfl
  rw [← rvD_sourceGram_sub, rvD_defectDeriv_sub, rvD_defectDeriv_sub, ratioDetDeriv_sub,
    ratioDetDeriv_sub, Complex.sub_re, Complex.sub_re]
  simp only [rvSignedDeriv, portRatioDeriv, Fin.sum_univ_two, hT, hD]
  ring

/-- The signed response trace bound (via the exact signed ratio derivative identity). For fixed
`x ≥ 0`, `0 ≤ y < 1` the constant `c = rvD_const x y = 2(x + y) + 2(y²/(1-y) + x²)` works: for
every sample with Hermitian blocks and invertible full path matrix, at every bulk real energy and
every signed `q`, `|∂_q(F_L+F_R)| ≤ 4η((x + y)|Re Tr B_q| + c √g ‖B_q‖_HS)`. -/
theorem rvSignedTraceBound_holds : RvSignedTraceBound := by
  intro x y hx hy0 hy1
  refine ⟨rvD_const x y, rvD_const_nonneg hx hy0 hy1, ?_⟩
  intro b e hb0 hb1 he1 he2 W r q ω hH hM
  rw [rvD_signedDeriv_eq, rvConductance, portDefect_eq, rvD_scattering_eq]
  exact rvD_abstract_bound hx hy0 hy1 (etaZ_nonneg (by linarith) he1 he2)
    (rvD_scattering_unitary hH hM) rvD_portInclusion_sum (portInclusion_conjTranspose_mul 0)
    (portInclusion_conjTranspose_mul 1) (rvD_sourceGram_isHermitian b e q ω)

end BlockBand.Endpoints
