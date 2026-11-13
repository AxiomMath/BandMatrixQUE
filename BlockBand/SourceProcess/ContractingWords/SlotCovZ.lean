module

public import BlockBand.SourceProcess.ContractingWords.SlotCovArith

/-!
# Centered slot bilinears

The centered bilinear `zc = u*(T_σ - ET_σ)v` of a transported separator: it is integrable, centered
and has bounded moments (`zc_facts`), and for `σ = I` the covariance of two of them is the
bilinear covariance of the Ward noise (`zc_ward`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The centered slot bilinear. -/
def zc (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (σ : Separator)
    (u v : Fin 2 × Fin W → ℂ) (y : LayerSample W .oneBlockOnePort) : ℂ :=
  bilinear u (transportedSep b E XX σ y - matrixExpect (freshLaw W b) (transportedSep b E XX σ)) v

theorem zc_facts {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {σ : Separator}
    (hT : ∀ i j, Integrable (fun y => transportedSep b E XX σ y i j) (freshLaw W b))
    (u v : Fin 2 × Fin W → ℂ) {β : ℝ} (hβ : 0 ≤ β)
    (hL2 : eLpNorm (zc b E XX σ u v) (ENNReal.ofReal 2) (freshLaw W b) ≤ ENNReal.ofReal β) :
    AEStronglyMeasurable (zc b E XX σ u v) (freshLaw W b) ∧
      Integrable (zc b E XX σ u v) (freshLaw W b) ∧ ∫ y, zc b E XX σ u v y ∂freshLaw W b = 0 ∧
      Integrable (fun y => ‖zc b E XX σ u v y‖ ^ 2) (freshLaw W b) ∧
      ∫ y, ‖zc b E XX σ u v y‖ ^ 2 ∂freshLaw W b ≤ β ^ 2 := by
  have hTE : ∀ i j, Integrable (fun y => (transportedSep b E XX σ y -
      matrixExpect (freshLaw W b) (transportedSep b E XX σ)) i j) (freshLaw W b) :=
    fun i j => (hT i j).sub (integrable_const _)
  have hint : Integrable (zc b E XX σ u v) (freshLaw W b) := integrable_bilinear_of hTE u v
  have hm := hint.aestronglyMeasurable
  have h2 : eLpNorm (zc b E XX σ u v) ((2 : ℕ) : ℝ≥0∞) (freshLaw W b) ≤ ENNReal.ofReal β := by
    simpa using hL2
  obtain ⟨hi2, hb2⟩ := moments_of_eLpNorm hm hβ h2 2 (by norm_num) le_rfl
  refine ⟨hm, hint, ?_, hi2, hb2⟩
  show ∫ y, bilinear u (transportedSep b E XX σ y -
    matrixExpect (freshLaw W b) (transportedSep b E XX σ)) v ∂freshLaw W b = 0
  rw [FullSource.integral_bilinear _ hTE, matrixExpect_sub_const _ _ hT, sub_self]
  simp [bilinear]

theorem zc_ward (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hT : ∀ i j, Integrable (fun y => transportedSep b E XX .id y i j) (freshLaw W b))
    (u v u' v' : Fin 2 × Fin W → ℂ) :
    ∫ y, zc b E XX .id u v y * zc b E XX .id u' v' y ∂freshLaw W b =
      bilinearCovariance (freshLaw W b) (wardNoise b E XX) u v u' v' := by
  have h1 := matrixExpect_sub_one hT
  have h2 : ∀ y, wardNoise b E XX y - matrixExpect (freshLaw W b) (wardNoise b E XX) =
      transportedSep b E XX .id y - matrixExpect (freshLaw W b) (transportedSep b E XX .id) :=
    fun y => by rw [← h1, transportedSep_id]; abel
  simp only [bilinearCovariance, zc, h2]

end BlockBand.SourceProcess.ContractingWords
