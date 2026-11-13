module

public import BlockBand.Transmission.PassiveCovariance.MeanIdentify
public import BlockBand.Transmission.PassiveCovariance.DressedTrace

/-!
# Multi-letter dressed trace–matrix covariances in operator norm

Law `layerLaw W b .oneBlockOnePort` (= `freshLaw W b`), deterministic passive `X` (`Y ⪰ 0`),
Euclidean operator norm on `2W × 2W` layer matrices, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`.

* `blkTr F r = W⁻¹ Tr F_{rr}` (normalized block trace).
* `wordTraceCov`: for dressed words `w₁, w₂` (`wordVal`, letters `𝒢, K̂𝒢, 𝒢ᴴ, (K̂𝒢)ᴴ`) of
  length `≤ L_w` with insertions `≤ K_d`, `‖E[blkTr(w₁) w₂] - E[blkTr(w₁)] E[w₂]‖ ≤ C/W²`,
  with all integrability. This extends `dressed_traceCov` (one-letter traces, bilinear
  forms) to multi-letter traces and the full operator norm. Constants depend on
  `b, E, L_w, K_d` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The normalized block trace `W⁻¹ Tr F_{rr}`. -/
def blkTr (F : LayerMat W) (r : Fin 2) : ℂ := (W : ℂ)⁻¹ * (blkAt F r r).trace

/-- Every layer site is a block site. -/
theorem exists_siteOf (α : LayerSite W .oneBlockOnePort) : ∃ (r : Fin 2) (x : Fin W), α = siteOf r x := by
  have h0 : ∀ a : Fin 1, a = 0 := fun a => Subsingleton.elim _ _
  rcases α with ⟨i0, x⟩ | ⟨i0, x⟩ <;> rw [h0 i0]
  exacts [⟨0, x, rfl⟩, ⟨1, x, rfl⟩]

theorem blkAt_covMat (μ : Measure (LayerSample W .oneBlockOnePort))
    (f : LayerSample W .oneBlockOnePort → ℂ) (U : LayerSample W .oneBlockOnePort → LayerMat W)
    (s t : Fin 2) : blkAt (covMat μ f U) s t = covMat μ f (fun ω => blkAt (U ω) s t) := by
  ext x y; rfl

/-- `Cov(Σ_i f_i, Σ_j U_j) = Σ_i Σ_j Cov(f_i, U_j)` under integrability. -/
theorem covMat_sum_sum {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι] [Fintype κ]
    (f : ι → Ω → ℂ) (U : κ → Ω → Matrix (Fin W) (Fin W) ℂ) (hf : ∀ i, Integrable (f i) μ)
    (hU : ∀ j x y, Integrable (fun ω => U j ω x y) μ)
    (hfU : ∀ i j x y, Integrable (fun ω => f i ω * U j ω x y) μ) :
    covMat μ (fun ω => ∑ i, f i ω) (fun ω => ∑ j, U j ω) = ∑ i, ∑ j, covMat μ (f i) (U j) := by
  ext x y
  simp only [covMat, matrixExpect, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.sum_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hfU i j x y,
    integral_finsetSum _ fun i _ => hf i, integral_finsetSum _ fun j _ => hU j x y,
    Finset.sum_mul_sum]
  simp_rw [integral_finsetSum _ fun j _ => hfU _ j x y]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]

/-- Multi-letter dressed trace–matrix covariance in operator norm. -/
theorem wordTraceCov (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ₁ : ℕ, ℓ₁ ≤ Lw → ∀ (wd₁ : Fin ℓ₁ → Fin 4)
      (D₁ : Fin (ℓ₁ + 1) → LayerMat W), (∀ j, ‖D₁ j‖ ≤ Kd) → ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw →
      ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W), (∀ j, ‖D₂ j‖ ≤ Kd) →
      ∀ r : Fin 2,
        Integrable (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r)
          (layerLaw W b .oneBlockOnePort) ∧
        (∀ α β, Integrable (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂ α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        (∀ α β, Integrable (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r *
          wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂ α β) (layerLaw W b .oneBlockOnePort)) ∧
        ‖covMat (layerLaw W b .oneBlockOnePort)
            (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r)
            (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂)‖ ≤ C / (W : ℝ) ^ 2 := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C₀, W₀, h⟩ := hA.traceMatrix b hb0 hb _ hκ Lw Kd
  refine ⟨4 * (4 ^ Lw * 4 ^ Lw * max C₀ 0), W₀, by positivity,
    fun W hW X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ r => ?_⟩
  set μ := layerLaw W b .oneBlockOnePort
  set z := boundaryZ b E
  -- the passive pieces
  set f : (Fin ℓ₁ → Fin 2 × Fin 2) → LayerSample W .oneBlockOnePort → ℂ := fun π ω =>
    (W : ℂ)⁻¹ * (passiveWord E z X (pathWd wd₁ π) (pathD ℓ₁ D₁ r r π) ω).trace
  set U : Fin 2 → Fin 2 → (Fin ℓ₂ → Fin 2 × Fin 2) → LayerSample W .oneBlockOnePort →
      Matrix (Fin W) (Fin W) ℂ := fun s t π ω => passiveWord E z X (pathWd wd₂ π) (pathD ℓ₂ D₂ s t π) ω
  have hf : ∀ ω, blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r = ∑ π, f π ω := fun ω => by
    rw [blkTr, blkAt_wordVal, Matrix.trace_sum, Finset.mul_sum]
  have hU : ∀ ω s t, blkAt (wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂) s t = ∑ π, U s t π ω :=
    fun ω s t => blkAt_wordVal b E X ω ℓ₂ wd₂ D₂ s t
  have hpc : ∀ s t π₁ π₂, Integrable (f π₁) μ ∧ (∀ x y, Integrable (fun ω => U s t π₂ ω x y) μ) ∧
      (∀ x y, Integrable (fun ω => f π₁ ω * U s t π₂ ω x y) μ) ∧
      ‖covMat μ (f π₁) (U s t π₂)‖ ≤ C₀ / (W : ℝ) ^ 2 := fun s t π₁ π₂ =>
    h W hW E (mem_bulkInterval_min E) _ (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX
      ℓ₁ ℓ₂ hℓ₁ hℓ₂ (pathWd wd₁ π₁) (pathD ℓ₁ D₁ r r π₁) (pathWd wd₂ π₂) (pathD ℓ₂ D₂ s t π₂)
      (norm_pathD_le ℓ₁ D₁ hD₁ r r π₁) (norm_pathD_le ℓ₂ D₂ hD₂ s t π₂)
  have hπ : ∀ π : Fin ℓ₁ → Fin 2 × Fin 2, Integrable (f π) μ :=
    fun π => (hpc 0 0 π fun _ => (0, 0)).1
  have hent : ∀ ω (s t : Fin 2) (x y : Fin W),
      wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂ (siteOf s x) (siteOf t y) = ∑ π, U s t π ω x y :=
    fun ω s t x y => by
      have := congrFun (congrFun (hU ω s t) x) y
      simpa [blkAt, Matrix.sum_apply] using this
  have hfi : Integrable (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r) μ := by
    simp only [hf]; exact integrable_finsetSum _ fun π _ => hπ π
  refine ⟨hfi, fun α β => ?_, fun α β => ?_, ?_⟩
  · obtain ⟨s, x, rfl⟩ := exists_siteOf α
    obtain ⟨t, y, rfl⟩ := exists_siteOf β
    simp only [hent]
    exact integrable_finsetSum _ fun π _ => (hpc s t (fun _ => (0, 0)) π).2.1 x y
  · obtain ⟨s, x, rfl⟩ := exists_siteOf α
    obtain ⟨t, y, rfl⟩ := exists_siteOf β
    simp only [hent, hf, Finset.sum_mul, Finset.mul_sum]
    exact integrable_finsetSum _ fun π₂ _ => integrable_finsetSum _ fun π₁ _ =>
      (hpc s t π₁ π₂).2.2.1 x y
  · have hblk : ∀ s t, ‖blkAt (covMat μ (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r)
        (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂)) s t‖ ≤
          4 ^ Lw * 4 ^ Lw * max C₀ 0 / (W : ℝ) ^ 2 := fun s t => by
      rw [blkAt_covMat]
      have e1 : (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r) =
          fun ω => ∑ π, f π ω := funext hf
      have e2 : (fun ω => blkAt (wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂) s t) =
          fun ω => ∑ π, U s t π ω := funext fun ω => hU ω s t
      rw [e1, e2, covMat_sum_sum f (U s t) hπ (fun π => (hpc s t (fun _ => (0, 0)) π).2.1)
        (fun π₁ π₂ => (hpc s t π₁ π₂).2.2.1)]
      have hC : 0 ≤ max C₀ 0 / (W : ℝ) ^ 2 := by positivity
      calc ‖∑ π₁, ∑ π₂, covMat μ (f π₁) (U s t π₂)‖
          ≤ ∑ _π₁ : Fin ℓ₁ → Fin 2 × Fin 2, ∑ _π₂ : Fin ℓ₂ → Fin 2 × Fin 2,
              max C₀ 0 / (W : ℝ) ^ 2 :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun π₁ _ => (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun π₂ _ => (hpc s t π₁ π₂).2.2.2.trans
                (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))))
        _ = (4 : ℝ) ^ ℓ₁ * (4 ^ ℓ₂ * (max C₀ 0 / (W : ℝ) ^ 2)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_prod,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
        _ ≤ (4 : ℝ) ^ Lw * (4 ^ Lw * (max C₀ 0 / (W : ℝ) ^ 2)) := by
            gcongr <;> norm_num
        _ = _ := by ring
    calc _ ≤ _ := norm_layerMat_le' _
      _ ≤ _ := add_le_add (add_le_add (add_le_add (hblk 0 0) (hblk 0 1)) (hblk 1 0)) (hblk 1 1)
      _ = _ := by ring

end BlockBand.Transmission.SourceMixing
