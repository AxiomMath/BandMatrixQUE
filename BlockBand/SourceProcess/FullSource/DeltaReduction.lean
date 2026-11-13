module

public import BlockBand.SourceProcess.FullSource.DeltaMoments

/-!
# Reduction of `FullSourceEstimates.mean`/`fluct` to one-port statements on `Δ`

By the Ward identity `𝓔 = ι(ΔF) + (ΔF)*ι*` (`ward_full`, a.s.), which is linear in
`Δ = K𝒢₁₁K - K`, the two remaining fields of `FullSourceEstimates` follow from two statements
about the **one-port** fresh layer at a passive input `X`:

* `DeltaFluctuation`: on a scalar domain `δ₀(X) ≤ d₀`,
  `‖x*(Δ - EΔ)y‖_{L^p} ≤ C_p W^{-1/2}‖x‖‖y‖` (the gradient argument for the
  functional `x*K𝒢₁₁Ky`, both gradient factors `K𝒢₁₁`, `𝒢₁₁K` bounded);
* `DeltaMean`: on a scalar domain, `‖EΔ‖ ≤ C(δ₀(X) + W⁻²)` (from `EΔ = ΩKM + O(W⁻²)` with
  `‖Ω‖ ≤ C(δ₀ + W⁻²)`, keeping `K` inside the remainder).

This file proves `fluct_of_delta`, `mean_of_delta` (the off-domain part of `mean` from
`delta_integrable`), with `‖F‖ ≤ η⁻¹ + (2η)⁻¹` and `‖ι‖ ≤ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- The one-port fluctuation bound for `Δ` on a scalar domain. -/
def DeltaFluctuation : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDistance0 b E X ≤ d₀ →
      ∀ x y : Fin W → ℂ,
        eLpNorm (fun ω => bilinear x (freshDelta b E X ω -
            matrixExpect (freshLaw W b) (freshDelta b E X)) y) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm x * vecNorm y)

/-- The one-port mean bound for `Δ` on a scalar domain. -/
def DeltaMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ d₀ : ℝ, 0 < d₀ ∧
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDistance0 b E X ≤ d₀ →
        ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤
          C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2)

/-- `ι(DF) + (DF)*ι*`. -/
def wardOf (D : Matrix (Fin W) (Fin W) ℂ) (F : Matrix (Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (nearSel W)ᴴ * (D * F) + (D * F)ᴴ * nearSel W

theorem wardOf_sub (D D' : Matrix (Fin W) (Fin W) ℂ) (F : Matrix (Fin W) (Fin 2 × Fin W) ℂ) :
    wardOf D F - wardOf D' F = wardOf (D - D') F := by
  simp only [wardOf, Matrix.sub_mul, Matrix.mul_sub, conjTranspose_sub]; abel

theorem norm_wardOf_le (D : Matrix (Fin W) (Fin W) ℂ) (F : Matrix (Fin W) (Fin 2 × Fin W) ℂ) :
    ‖wardOf D F‖ ≤ 2 * (‖D‖ * ‖F‖) := by
  have hι : ‖nearSel W‖ ≤ 1 := by
    have := norm_nearSel_mul_le (W := W) 1
    rw [Matrix.mul_one] at this; exact this.trans norm_one_matrix_le
  have hι' : ‖(nearSel W)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hι
  have hDF := Matrix.l2_opNorm_mul D F
  have h1 : ‖(nearSel W)ᴴ * (D * F)‖ ≤ ‖D‖ * ‖F‖ :=
    (Matrix.l2_opNorm_mul _ _).trans
      (by nlinarith [norm_nonneg (D * F), norm_nonneg ((nearSel W)ᴴ)])
  have h2 : ‖(D * F)ᴴ * nearSel W‖ ≤ ‖D‖ * ‖F‖ := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    nlinarith [norm_nonneg (D * F), norm_nonneg (nearSel W)]
  exact (norm_add_le _ _).trans (by linarith)

theorem integrable_bilinear {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}
    (D : Ω → Matrix n n ℂ) (hD : ∀ x y, Integrable (fun ω => D ω x y) μ) (u v : n → ℂ) :
    Integrable (fun ω => bilinear u (D ω) v) μ := by
  simp only [bilinear, dotProduct, mulVec]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_finsetSum _ fun j _ => (hD i j).mul_const _).const_mul _

theorem entry_eq_bilinear {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (a c : n) :
    M a c = bilinear (Pi.single a 1) M (Pi.single c 1) := by
  simp [bilinear, mulVec, dotProduct, Pi.single_apply]

/-- `E[ι(DF) + (DF)*ι*] = ι(EDF) + (EDF)*ι*`. -/
theorem matrixExpect_wardOf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (D : Ω → Matrix (Fin W) (Fin W) ℂ) (hD : ∀ x y, Integrable (fun ω => D ω x y) μ)
    (F : Matrix (Fin W) (Fin 2 × Fin W) ℂ) :
    matrixExpect μ (fun ω => wardOf (D ω) F) = wardOf (matrixExpect μ D) F := by
  ext a c
  rw [entry_eq_bilinear (wardOf (matrixExpect μ D) F), wardOf, bilinear_ward,
    bilinear_matrixExpect D _ _ hD, bilinear_matrixExpect D _ _ hD]
  have hs : star (∫ ω, bilinear (nearSel W *ᵥ Pi.single c 1) (D ω) (F *ᵥ Pi.single a 1) ∂μ) =
      ∫ ω, star (bilinear (nearSel W *ᵥ Pi.single c 1) (D ω) (F *ᵥ Pi.single a 1)) ∂μ :=
    integral_conj.symm
  have hi2 := integrable_bilinear D hD (nearSel W *ᵥ Pi.single c 1) (F *ᵥ Pi.single a 1)
  have hi2' : Integrable (fun ω => star (bilinear (nearSel W *ᵥ Pi.single c 1) (D ω)
      (F *ᵥ Pi.single a 1))) μ :=
    hi2.norm.mono' hi2.aestronglyMeasurable.star (Filter.Eventually.of_forall fun _ => by simp)
  rw [hs, ← integral_add (integrable_bilinear D hD _ _) hi2']
  simp only [matrixExpect, Matrix.of_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  rw [entry_eq_bilinear (wardOf (D ω) F), wardOf, bilinear_ward]

/-- The lower bound `η ≥ η₀ = (1-b)κ/4` on the bulk interval. -/
theorem etaZ_ge {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) : (1 - b) * κ / 4 ≤ etaZ b E := by
  have hE' := hE
  obtain ⟨h1, h2⟩ := hE'
  exact (disk_bounds hb0 hb hκ hE
    (boundaryZ_mem_paramDisk (by linarith) (by linarith) (by linarith))).1

/-- The a.s. Ward form of `𝓔` and of `E𝓔`, for `X = nearSchur z 𝕏`. -/
theorem ward_ae {b E : ℝ} (hb0 : 0 < b) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂freshLaw W b, wardNoise b E XX ω =
      wardOf (freshDelta b E (nearSchur (boundaryZ b E) XX) ω) (wardF b E XX) := by
  filter_upwards [ae_good W hb0 hW] with ω hω
  exact ward_full b E hXX hη hω.1 hω.2

end BlockBand.SourceProcess.FullSource
