module

public import BlockBand.SourceProcess.ContractingWords.StepFinal
public import BlockBand.SourceProcess.CompleteSourceGap.MeanCases
public import BlockBand.SourceProcess.CompleteSourceGap.GapIdentity

/-!
# The ordinary transported separators `NN*`, `NPN*`: exact algebra

For every `ω` (no a.s. qualifier), `X = nearSchur z 𝕏`:

* `transportedSep_id`: `N·I·N* = I + 𝓔` (`𝓔 = wardNoise`);
* `transportedSep_proj`: `N·P·N* = ι*(LL*)ι` (`ι = nearSel`, `LL* = freshU b E X`), from
  `N ι* = ι* L`;
* `matrixExpect_sub_one`, `matrixExpect_proj`: the means; `bilinear_proj`: the centered
  bilinear form of `NPN*` is `(ιu)*(U - EU)(ιv)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.Bridge
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `N·I·N* = I + 𝓔`. -/
theorem transportedSep_id (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    transportedSep b E XX .id ω = 1 + wardNoise b E XX ω := by
  simp only [transportedSep, sepOf, Matrix.mul_one, wardNoise, add_sub_cancel]

/-- `N·P·N* = ι*(LL*)ι`. -/
theorem transportedSep_proj (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    transportedSep b E XX .proj ω =
      (nearSel W)ᴴ * freshU b E (nearSchur (boundaryZ b E) XX) ω * nearSel W := by
  have h := freshTransport_mul_nearSel_conj b E XX ω
  have h' : nearSel W * (freshTransport b E XX ω)ᴴ =
      (freshL b E (nearSchur (boundaryZ b E) XX) ω)ᴴ * nearSel W := by
    have := congrArg Matrix.conjTranspose h
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using this
  rw [transportedSep, sepOf, ← FullSourceCovariance.nearSel_conj_mul_nearSel, freshU,
    ← Matrix.mul_assoc, h, Matrix.mul_assoc, h']
  simp only [Matrix.mul_assoc]

theorem matrixExpect_sub_const {Ω n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : Ω → Matrix n n ℂ) (A : Matrix n n ℂ)
    (hU : ∀ i j, Integrable (fun ω => U ω i j) μ) :
    matrixExpect μ (fun ω => U ω - A) = matrixExpect μ U - A := by
  ext i j
  simp only [matrixExpect, Matrix.of_apply, Matrix.sub_apply]
  rw [integral_sub (hU i j) (integrable_const _), integral_const]
  simp

/-- `E[NN*] - I = E𝓔`. -/
theorem matrixExpect_sub_one {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : ∀ i j, Integrable (fun y => transportedSep b E XX .id y i j) (freshLaw W b)) :
    matrixExpect (freshLaw W b) (transportedSep b E XX .id) - 1 =
      matrixExpect (freshLaw W b) (wardNoise b E XX) := by
  rw [← matrixExpect_sub_const _ _ hT]
  congr 1
  funext y
  rw [transportedSep_id, add_sub_cancel_left]

/-- `E[NPN*] = ι*(EU)ι`. -/
theorem matrixExpect_proj (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    matrixExpect (freshLaw W b) (transportedSep b E XX .proj) =
      (nearSel W)ᴴ * matrixExpect (freshLaw W b) (freshU b E (nearSchur (boundaryZ b E) XX)) *
        nearSel W := by
  rw [← matrixExpect_lift]
  congr 1
  funext y
  exact transportedSep_proj b E XX y

/-- The centered `NN*` is the centered `𝓔`. -/
theorem bilinear_id {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : ∀ i j, Integrable (fun y => transportedSep b E XX .id y i j) (freshLaw W b))
    (u v : Fin 2 × Fin W → ℂ) (ω : LayerSample W .oneBlockOnePort) :
    bilinear u (transportedSep b E XX .id ω -
        matrixExpect (freshLaw W b) (transportedSep b E XX .id)) v =
      bilinear u (wardNoise b E XX ω - matrixExpect (freshLaw W b) (wardNoise b E XX)) v := by
  rw [← matrixExpect_sub_one hT, transportedSep_id]
  congr 1
  abel

/-- The centered `NPN*` is the centered `U = LL*` between `ιu` and `ιv`. -/
theorem bilinear_proj (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (u v : Fin 2 × Fin W → ℂ) (ω : LayerSample W .oneBlockOnePort) :
    bilinear u (transportedSep b E XX .proj ω -
        matrixExpect (freshLaw W b) (transportedSep b E XX .proj)) v =
      bilinear (nearSel W *ᵥ u) (freshU b E (nearSchur (boundaryZ b E) XX) ω -
        matrixExpect (freshLaw W b) (freshU b E (nearSchur (boundaryZ b E) XX)))
        (nearSel W *ᵥ v) := by
  rw [transportedSep_proj, matrixExpect_proj, ← FullSource.bilinear_sandwich']
  congr 1
  simp only [Matrix.mul_assoc, ← Matrix.mul_sub, Matrix.sub_mul]

/-- `‖ι*Mι‖ ≤ ‖M‖`. -/
theorem norm_lift_le (M : Matrix (Fin W) (Fin W) ℂ) : ‖(nearSel W)ᴴ * M * nearSel W‖ ≤ ‖M‖ :=
  norm_sandwich_le M _ norm_nearSel_le

/-- `‖E[NPN*] - P‖ ≤ ‖EU - I‖`. -/
theorem norm_mean_proj_le (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ‖matrixExpect (freshLaw W b) (transportedSep b E XX .proj) - sepOf b E XX .proj‖ ≤
      ‖matrixExpect (freshLaw W b) (freshU b E (nearSchur (boundaryZ b E) XX)) - 1‖ := by
  rw [matrixExpect_proj, sepOf, ← FullSourceCovariance.nearSel_conj_mul_nearSel]
  have e : (nearSel W)ᴴ * nearSel W =
      (nearSel W)ᴴ * (1 : Matrix (Fin W) (Fin W) ℂ) * nearSel W := by rw [Matrix.mul_one]
  rw [e, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact norm_lift_le _

end BlockBand.SourceProcess.ContractingWords
