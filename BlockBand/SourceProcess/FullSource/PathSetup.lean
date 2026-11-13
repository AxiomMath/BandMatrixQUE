module

public import BlockBand.SourceProcess.FullSource.LayerStep
public import BlockBand.Transmission.PathScalar.Holds

/-!
# The near-end-grown path as past coordinates ⊗ fresh layer

Bookkeeping for the conditional (Fubini) form of
the tag recursion: every length-`j` object is a measurable function of the
past coordinates `pastCoords W j`, and the step `j → j+1` is a function of
`(pastCoords W j, freshSample W j)`, whose law is `pastLaw ⊗ freshLaw`.

* `pastXX`, `pastU`, `pastS`: `𝕏_j`, `𝒰_j`, the tag factor `P_k𝒰_j` of the past;
* `tagResponse_eq_factor`: `Y_{j;k} = (P_k𝒰_j)*(P_k𝒰_j)`;
* `growthSigma_mono`: the growth σ-algebras increase;
* `lintegral_indicator_step`: the generic Fubini step on a past event.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar
open scoped ENNReal

variable {W : ℕ}

/-! ## Past functions -/

/-- `𝕏_j` as a function of the past coordinates. -/
def pastXX (E : ℝ) (W j : ℕ) (p : PastSample W j) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  pathSchur E (pathOfPast W j p)

/-- The full path matrix of a path sample (as in `fullPathMatrix`). -/
def fullMat (b E : ℝ) {n : ℕ} (q : PathSample W n) : Matrix (FullSite W n) (FullSite W n) ℂ :=
  Matrix.fromBlocks (pathMatrix q - (E : ℂ) • 1) (pathPortCoupling q) (pathPortCoupling q)ᴴ
    (boundaryZ b E • 1)

/-- `𝒰_j` as a function of the past coordinates. -/
def pastU (b E : ℝ) (W j : ℕ) (p : PastSample W j) : Matrix (Fin j × Fin W) (Fin 2 × Fin W) ℂ :=
  ((fullMat b E (pathOfPast W j p))⁻¹).toBlocks₁₂

/-- The tag factor `P_k𝒰_j` as a function of the past coordinates. -/
def pastS (b E : ℝ) (W j k : ℕ) (p : PastSample W j) : Matrix (Fin j × Fin W) (Fin 2 × Fin W) ℂ :=
  tagProjection W j k * pastU b E W j p

theorem pastXX_eq (E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    pathSchur E (pathAt W j ω) = pastXX E W j (pastCoords W j ω) := by
  rw [pathAt_eq_pathOfPast]; rfl

theorem boundaryToInterior_eq_past (b E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    boundaryToInterior b E W j ω = pastU b E W j (pastCoords W j ω) := by
  rw [boundaryToInterior, fullInverse, fullPathMatrix, pathAt_eq_pathOfPast]; rfl

theorem tagProjection_conjTranspose (j k : ℕ) : (tagProjection W j k)ᴴ = tagProjection W j k := by
  rw [tagProjection, Matrix.diagonal_conjTranspose]
  congr 1; funext x
  by_cases h : k < j ∧ x.1.val = j - 1 - k <;> simp [h]

theorem tagProjection_mul_self (j k : ℕ) :
    tagProjection W j k * tagProjection W j k = tagProjection W j k := by
  rw [tagProjection, Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  by_cases h : k < j ∧ x.1.val = j - 1 - k <;> simp [h]

/-- `Y_{j;k} = (P_k𝒰_j)*(P_k𝒰_j)`. -/
theorem tagResponse_eq_factor (b E : ℝ) (j k : ℕ) (ω : GrowthPath W) :
    tagResponse b E W j k ω = (pastS b E W j k (pastCoords W j ω))ᴴ *
      pastS b E W j k (pastCoords W j ω) := by
  rw [tagResponse, pastS, ← boundaryToInterior_eq_past, Matrix.conjTranspose_mul,
    tagProjection_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (tagProjection W j k) (tagProjection W j k), tagProjection_mul_self]

/-- `X_j = nearSchur z 𝕏_j` as a function of the past (unabsorbed). -/
theorem pathX_eq_past (b E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    pathX b E W j ω = nearSchur (boundaryZ b E) (pastXX E W j (pastCoords W j ω)) := by
  rw [pathX_eq, pastXX_eq]

theorem measurable_fullMat (b E : ℝ) (n : ℕ) :
    Measurable fun q : PathSample W n => fullMat b E q := by
  have hC := measurable_pathPortCoupling (W := W) n
  have hP := measurable_pathMatrix (W := W) n
  refine Measurable.of_eval_matrix _ fun x y => ?_
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [fullMat, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply]
  · exact hP.eval_matrix.sub measurable_const
  · exact hC.eval_matrix
  · exact (measurable_matrix_conjTranspose' hC).eval_matrix
  · exact measurable_const

theorem measurable_pastXX (E : ℝ) (j : ℕ) : Measurable (pastXX E W j) :=
  (measurable_pathSchur E j).comp (measurable_pathOfPast j)

theorem measurable_pastU (b E : ℝ) (j : ℕ) : Measurable (pastU b E W j) := by
  have h := measurable_matrix_inv.comp ((measurable_fullMat (W := W) b E j).comp
    (measurable_pathOfPast j))
  exact Measurable.of_eval_matrix _ fun _ _ => h.eval_matrix

theorem measurable_pastS (b E : ℝ) (j k : ℕ) : Measurable (pastS b E W j k) :=
  measurable_matrix_mul' measurable_const (measurable_pastU b E j)

/-- Hermitian past blocks give a Hermitian `𝕏_j`. -/
theorem pastXX_isHermitian (E : ℝ) {j : ℕ} {p : PastSample W j} (hp : p ∈ hermPast W j) :
    (pastXX E W j p).IsHermitian := by
  have h := pathSchur_isHermitian E j (extendPast p) (fun k => by
    simp only [extendPast]; split_ifs
    · exact hp _
    · exact Matrix.isHermitian_zero)
  rwa [pastXX_eq, pastCoords_extendPast] at h

/-! ## The filtration -/

/-- Restriction of past coordinates from length `j` to length `i ≤ j`. -/
def restrictPast {i j : ℕ} (h : i ≤ j) (p : PastSample W j) : PastSample W i :=
  (fun l => p.1 (Fin.castLE h l), fun l => p.2 (Fin.castLE (by omega) l))

theorem pastCoords_restrict {i j : ℕ} (h : i ≤ j) (ω : GrowthPath W) :
    pastCoords W i ω = restrictPast h (pastCoords W j ω) := rfl

theorem measurable_restrictPast {i j : ℕ} (h : i ≤ j) :
    Measurable (restrictPast (W := W) h) :=
  (Measurable.of_eval fun _ => (measurable_pi_apply _).comp measurable_fst).prodMk
    (Measurable.of_eval fun _ => (measurable_pi_apply _).comp measurable_snd)

/-- The growth σ-algebras increase with the length. -/
theorem growthSigma_mono {i j : ℕ} (h : i ≤ j) : growthSigma W i ≤ growthSigma W j := by
  rw [growthSigma_eq_comap, growthSigma_eq_comap]
  have : pastCoords W i = restrictPast h ∘ pastCoords W j := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_restrictPast h).comap_le

/-! ## The generic Fubini step -/

/-- **One conditional step on a past event**: if `Z ≤ Φ(past, fresh)` on the event and the
fresh integral of `Φ` is at most `Ψ(past)` there, then `E[1_G Z] ≤ E[1_G Ψ(past)]`. -/
theorem lintegral_indicator_step {Ω P F : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
    [MeasurableSpace F] {μ : Measure Ω} {μP : Measure P} {ν : Measure F} [SFinite μP]
    [IsProbabilityMeasure ν] {π : Ω → P} {φ : Ω → F} (hπ : Measurable π) (hφ : Measurable φ)
    (hmap : μ.map (fun ω => (π ω, φ ω)) = μP.prod ν) {G : Set P} (hG : MeasurableSet G)
    {Φ : P × F → ℝ≥0∞} (hΦ : Measurable Φ) {Ψ : P → ℝ≥0∞} (hΨ : Measurable Ψ)
    {Z : Ω → ℝ≥0∞} (hZ : ∀ᵐ ω ∂μ, π ω ∈ G → Z ω ≤ Φ (π ω, φ ω))
    (hstep : ∀ᵐ p ∂μP, p ∈ G → ∫⁻ f, Φ (p, f) ∂ν ≤ Ψ p) :
    ∫⁻ ω, (π ⁻¹' G).indicator Z ω ∂μ ≤ ∫⁻ ω, (π ⁻¹' G).indicator (fun ω => Ψ (π ω)) ω ∂μ := by
  have hπφ : Measurable fun ω => (π ω, φ ω) := hπ.prodMk hφ
  have hG' : MeasurableSet (Prod.fst ⁻¹' G : Set (P × F)) := measurable_fst hG
  have hm1 : Measurable ((Prod.fst ⁻¹' G : Set (P × F)).indicator Φ) := hΦ.indicator hG'
  have hm2 : Measurable ((Prod.fst ⁻¹' G : Set (P × F)).indicator fun q => Ψ q.1) :=
    (hΨ.comp measurable_fst).indicator hG'
  calc ∫⁻ ω, (π ⁻¹' G).indicator Z ω ∂μ
      ≤ ∫⁻ ω, (Prod.fst ⁻¹' G : Set (P × F)).indicator Φ (π ω, φ ω) ∂μ :=
        lintegral_mono_ae (hZ.mono fun ω h => by
          by_cases hω : π ω ∈ G
          · simp only [Set.indicator, Set.mem_preimage, hω, ite_true]; exact h hω
          · simp [Set.indicator, hω])
    _ = ∫⁻ q, (Prod.fst ⁻¹' G : Set (P × F)).indicator Φ q ∂(μP.prod ν) := by
        rw [← hmap, lintegral_map hm1 hπφ]
    _ = ∫⁻ p, ∫⁻ f, (Prod.fst ⁻¹' G : Set (P × F)).indicator Φ (p, f) ∂ν ∂μP :=
        lintegral_prod _ hm1.aemeasurable
    _ = ∫⁻ p, G.indicator (fun p => ∫⁻ f, Φ (p, f) ∂ν) p ∂μP := by
        congr 1; funext p
        by_cases hp : p ∈ G <;> simp [Set.indicator, hp]
    _ ≤ ∫⁻ p, G.indicator Ψ p ∂μP := lintegral_mono_ae (hstep.mono fun p h => by
          by_cases hp : p ∈ G
          · simp only [Set.indicator, hp, ite_true]; exact h hp
          · simp [Set.indicator, hp])
    _ = ∫⁻ p, ∫⁻ f, (Prod.fst ⁻¹' G : Set (P × F)).indicator (fun q => Ψ q.1) (p, f) ∂ν ∂μP := by
        congr 1; funext p
        by_cases hp : p ∈ G <;> simp [Set.indicator, hp]
    _ = ∫⁻ q, (Prod.fst ⁻¹' G : Set (P × F)).indicator (fun q => Ψ q.1) q ∂(μP.prod ν) :=
        (lintegral_prod _ hm2.aemeasurable).symm
    _ = ∫⁻ ω, (Prod.fst ⁻¹' G : Set (P × F)).indicator (fun q => Ψ q.1) (π ω, φ ω) ∂μ := by
        rw [← hmap, lintegral_map hm2 hπφ]
    _ = ∫⁻ ω, (π ⁻¹' G).indicator (fun ω => Ψ (π ω)) ω ∂μ := rfl

end BlockBand.SourceProcess.FullSource
