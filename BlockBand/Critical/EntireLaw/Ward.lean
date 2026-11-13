module

public import BlockBand.Critical.GlobalSource.Statement
public import BlockBand.Critical.Bridges.Scattering
public import BlockBand.Layers.ScalarRecursion
public import BlockBand.Layers.MatchedScalar

/-!
# The entire law: `probeGram 𝒦 = M_pr`

* `fullInverse_ward` (deterministic, Hermitian path blocks; also for a singular path matrix);
* `imPart_complexSourceK`, **`probeGram_complexSourceData`** (`probeGram (data 0) = data 1`);
* for the global probes of `GlobalSource`: `globalProbeGram_eq` (`B_W = V*V`) and
  `globalProbeGram_posSemidef` (`B_W ⪰ 0`);
* `etaZ_pos`: `η > 0` in the bulk.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CriticalEntire
open scoped ComplexConjugate ComplexOrder

/-- `η = Im z_∂(E) > 0` in the bulk (`0 < b < 1`, `|E| < 2`). -/
theorem etaZ_pos {b E : ℝ} (hb : b < 1) (hE : -2 < E ∧ E < 2) : 0 < etaZ b E := by
  set κ := min (2 + E) (2 - E) with hκ
  have hκpos : 0 < κ := lt_min (by linarith [hE.1]) (by linarith [hE.2])
  have hmem : E ∈ bulkInterval κ := by
    refine ⟨?_, ?_⟩
    · have := min_le_left (2 + E) (2 - E); linarith
    · have := min_le_right (2 + E) (2 - E); linarith
  obtain ⟨h1, h2⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval hb hκpos hmem
  exact lt_of_lt_of_le h1 h2

/-- `M - Mᴴ` for the full path matrix with two matched leads: only the lead block
`z_∂ - conj z_∂ = 2iη` survives (the path part is Hermitian). -/
theorem fullPathMatrix_sub_conjTranspose (b E : ℝ) (W n : ℕ) (ω : GrowthPath W)
    (hH : (pathMatrix (pathAt W n ω)).IsHermitian) :
    fullPathMatrix b E W n ω - (fullPathMatrix b E W n ω)ᴴ =
      Matrix.fromBlocks 0 0 0 ((2 * (etaZ b E : ℂ) * Complex.I) • 1) := by
  have hsubB : ∀ {α β γ δ : Type} (A A' : Matrix α γ ℂ) (B B' : Matrix α δ ℂ)
      (C C' : Matrix β γ ℂ) (D D' : Matrix β δ ℂ),
      Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
        Matrix.fromBlocks (A - A') (B - B') (C - C') (D - D') := by
    intro α β γ δ A A' B B' C C' D D'
    ext (i | i) (j | j) <;> rfl
  unfold fullPathMatrix
  rw [Matrix.fromBlocks_conjTranspose, hsubB]
  have h1 : (pathMatrix (pathAt W n ω) - (E : ℂ) • 1) -
      (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)ᴴ = 0 := by
    rw [Matrix.conjTranspose_sub, hH.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  have h2 : boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))ᴴ =
      (2 * (etaZ b E : ℂ) * Complex.I) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, ← sub_smul]
    congr 1
    unfold etaZ
    apply Complex.ext
    · simp
    · simp; ring
  rw [h1, h2, sub_self, conjTranspose_conjTranspose, sub_self]

/-- **Ward identity for the interior block** (`Im 𝒦 = -η V*V` in matrix
form): for Hermitian path blocks, `G₁₁ - G₁₁ᴴ = -2iη G₁₂ G₁₂ᴴ` with `G` the inverse of the full
path matrix (also when `G` is the totalized inverse `0` of a singular matrix). -/
theorem fullInverse_ward (b E : ℝ) (W n : ℕ) (ω : GrowthPath W)
    (hH : (pathMatrix (pathAt W n ω)).IsHermitian) :
    (fullInverse b E W n ω).toBlocks₁₁ - ((fullInverse b E W n ω).toBlocks₁₁)ᴴ =
      -(2 * (etaZ b E : ℂ) * Complex.I) •
        ((fullInverse b E W n ω).toBlocks₁₂ * ((fullInverse b E W n ω).toBlocks₁₂)ᴴ) := by
  set M := fullPathMatrix b E W n ω with hM
  set G := fullInverse b E W n ω with hG
  set c : ℂ := 2 * (etaZ b E : ℂ) * Complex.I with hc
  by_cases hu : IsUnit M.det
  · have hGM : G * M = 1 := Matrix.nonsing_inv_mul M hu
    have hMG : M * G = 1 := Matrix.mul_nonsing_inv M hu
    have hGh : Mᴴ * Gᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hGM, Matrix.conjTranspose_one]
    have hkey : G - Gᴴ = G * (Mᴴ - M) * Gᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hGh, Matrix.mul_one, hGM,
        Matrix.one_mul]
    have hD : Mᴴ - M = -Matrix.fromBlocks 0 0 0 (c • 1) := by
      rw [← fullPathMatrix_sub_conjTranspose b E W n ω hH, neg_sub]
    have hblk : G = Matrix.fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₁ G.toBlocks₂₂ :=
      (Matrix.fromBlocks_toBlocks G).symm
    have h11 : (G - Gᴴ).toBlocks₁₁ = G.toBlocks₁₁ - (G.toBlocks₁₁)ᴴ := by
      ext i j
      simp [Matrix.toBlocks₁₁, Matrix.conjTranspose_apply]
    rw [← h11, hkey, hD, hblk]
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.mul_neg,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, Matrix.fromBlocks_neg]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  · have h0 : G = 0 := Matrix.nonsing_inv_apply_not_isUnit M hu
    rw [h0]
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.mul_apply]

/-- **Ward identity.** For Hermitian path blocks and any source columns `𝒥`,
`Im(𝒥* G₁₁ 𝒥) = -η (G₁₂ᴴ𝒥)ᴴ (G₁₂ᴴ𝒥)`, with `Im K = (K - K*)/(2i)` (`Critical.imPart`) and
`G₁₂ = boundaryToInterior`. -/
theorem imPart_sources (b E : ℝ) (W n : ℕ) (ω : GrowthPath W)
    (hH : (pathMatrix (pathAt W n ω)).IsHermitian) {ι : Type*} [Fintype ι]
    (Jc : Matrix (Fin n × Fin W) ι ℂ) :
    BlockBand.Internal.Contracts.Critical.imPart (Jcᴴ * (fullInverse b E W n ω).toBlocks₁₁ * Jc) =
      -((etaZ b E : ℝ) : ℂ) • (((boundaryToInterior b E W n ω)ᴴ * Jc)ᴴ *
        ((boundaryToInterior b E W n ω)ᴴ * Jc)) := by
  have hw := fullInverse_ward b E W n ω hH
  unfold BlockBand.Internal.Contracts.Critical.imPart boundaryToInterior
  have hsub : Jcᴴ * (fullInverse b E W n ω).toBlocks₁₁ * Jc -
      (Jcᴴ * (fullInverse b E W n ω).toBlocks₁₁ * Jc)ᴴ =
      Jcᴴ * ((fullInverse b E W n ω).toBlocks₁₁ - ((fullInverse b E W n ω).toBlocks₁₁)ᴴ) * Jc := by
    simp only [Matrix.conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc]
  rw [hsub, hw, Matrix.conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul]
  have hη : (2 * Complex.I)⁻¹ * -(2 * (etaZ b E : ℂ) * Complex.I) = -((etaZ b E : ℝ) : ℂ) := by
    field_simp
  rw [hη]
  congr 1
  simp only [Matrix.mul_assoc]

/-- The path blocks of the length-`n` path read from a grown sample are Hermitian when the
grown blocks `A_0, …, A_{n-1}` are. -/
theorem pathMatrix_pathAt_isHermitian {W n : ℕ} (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) : (pathMatrix (pathAt W n ω)).IsHermitian :=
  BlockBand.Layers.srec_pathMatrix_isHermitian _ fun _ => hA _

/-- **Ward identity for the source data.** When the grown blocks are Hermitian (a full-measure
event), `Im 𝒦 = -η M_pr` for the source data `𝒦 = complexSourceData … 0` and
`M_pr = V_pr*V_pr = complexSourceData … 1` (`V_pr = probeFrame`). -/
theorem imPart_complexSourceK (b E : ℝ) {np : ℕ} (W n : ℕ) (τ m : Fin np → ℝ)
    (x : ProbedPath W np) (hA : ∀ k, (x.1.1 k).IsHermitian) :
    BlockBand.Internal.Contracts.Critical.imPart (complexSourceData b E W n τ m x 0) =
      -((etaZ b E : ℝ) : ℂ) • complexSourceData b E W n τ m x 1 := by
  simp only [complexSourceData, Matrix.cons_val_zero, Matrix.cons_val_one,
    complexSourceK, probeFrame]
  exact imPart_sources b E W n x.1 (pathMatrix_pathAt_isHermitian x.1 hA) _

/-- `probeGram 𝒦 = M_pr`: the matrix `B = -η⁻¹ Im 𝒦` is the component `M_pr` of the source data, for
`η ≠ 0` and Hermitian grown blocks. With `Bridges.imPart_eq_matrixImaginaryPart` this also reads
`-η⁻¹ matrixImaginaryPart 𝒦 = M_pr`. -/
theorem probeGram_complexSourceData (b E : ℝ) (hη : etaZ b E ≠ 0) {np : ℕ} (W n : ℕ)
    (τ m : Fin np → ℝ) (x : ProbedPath W np) (hA : ∀ k, (x.1.1 k).IsHermitian) :
    probeGram b E (complexSourceData b E W n τ m x 0) = complexSourceData b E W n τ m x 1 := by
  unfold probeGram
  rw [imPart_complexSourceK b E W n τ m x hA, smul_smul]
  have : -(((etaZ b E)⁻¹ : ℝ) : ℂ) * -((etaZ b E : ℝ) : ℂ) = 1 := by
    rw [neg_mul_neg, ← Complex.ofReal_mul, inv_mul_cancel₀ hη, Complex.ofReal_one]
  rw [this, one_smul]

/-- The probe columns `Z = (ζ_1, …, ζ_J)` of the global probes on the remaining path. -/
def globalProbeColumns (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (g : Fin J → BlockBand.Critical.GlobalSource.PathSite W n → ℂ) :
    Matrix (BlockBand.Critical.GlobalSource.PathSite W n) (Fin J) ℂ :=
  fun x a => BlockBand.Critical.GlobalSource.globalProbeVector W n (Q a) (g a) x

/-- `𝒦_W = Zᴴ G_lead Z`. -/
theorem globalProbeMatrix_eq_mul (b E : ℝ) (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (x : BlockBand.Critical.GlobalSource.GlobalProbeSample W n J) :
    BlockBand.Critical.GlobalSource.globalProbeMatrix b E W n Q x =
      (globalProbeColumns W n Q x.2)ᴴ * BlockBand.Critical.GlobalSource.leadInverse b E W n x.1 *
        globalProbeColumns W n Q x.2 := by
  ext a c
  simp only [BlockBand.Critical.GlobalSource.globalProbeMatrix, Matrix.mul_apply,
    dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, globalProbeColumns, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  ring

/-- **For the global probes, `B_W = V*V ⪰ 0`** with `V = G₁₂ᴴ Z`
(`B_W = -η⁻¹ Im 𝒦_W ⪰ 0`), for `η ≠ 0` and Hermitian grown blocks. -/
theorem globalProbeGram_eq (b E : ℝ) (hη : etaZ b E ≠ 0) (W n : ℕ) {J : ℕ}
    (Q : Fin J → C(Torus, ℝ)) (x : BlockBand.Critical.GlobalSource.GlobalProbeSample W n J)
    (hA : ∀ k, (x.1.1 k).IsHermitian) :
    BlockBand.Critical.GlobalSource.globalProbeGram b E W n Q x =
      ((boundaryToInterior b E W (BlockBand.Critical.GlobalSource.probePathLength n) x.1)ᴴ *
          globalProbeColumns W n Q x.2)ᴴ *
        ((boundaryToInterior b E W (BlockBand.Critical.GlobalSource.probePathLength n) x.1)ᴴ *
          globalProbeColumns W n Q x.2) := by
  unfold BlockBand.Critical.GlobalSource.globalProbeGram probeGram
  rw [globalProbeMatrix_eq_mul]
  unfold BlockBand.Critical.GlobalSource.leadInverse
  rw [imPart_sources b E W _ x.1 (pathMatrix_pathAt_isHermitian x.1 hA), smul_smul]
  have : -(((etaZ b E)⁻¹ : ℝ) : ℂ) * -((etaZ b E : ℝ) : ℂ) = 1 := by
    rw [neg_mul_neg, ← Complex.ofReal_mul, inv_mul_cancel₀ hη, Complex.ofReal_one]
  rw [this, one_smul]

theorem globalProbeGram_posSemidef (b E : ℝ) (hη : etaZ b E ≠ 0) (W n : ℕ) {J : ℕ}
    (Q : Fin J → C(Torus, ℝ)) (x : BlockBand.Critical.GlobalSource.GlobalProbeSample W n J)
    (hA : ∀ k, (x.1.1 k).IsHermitian) :
    (BlockBand.Critical.GlobalSource.globalProbeGram b E W n Q x).PosSemidef := by
  rw [globalProbeGram_eq b E hη W n Q x hA]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end BlockBand.Critical.EntireLaw
