module

public import BlockBand.SourceProcess.ClosedIdent.Defs
public import BlockBand.SourceProcess.ClosedPath.TimeS
public import BlockBand.SourceProcess.FullSourceStops.CurrentSpectral
public import BlockBand.SourceProcess.SourcePins.AtomFinite
public import BlockBand.Transmission.Bridge.PencilAE
public import BlockBand.Transmission.LawDuality.PowerBridge

/-!
# The entrance at finite width: near and far transmission

The closed coordinates take their entrance from the **far** transmission
`T_far = I − S_ffᴴS_ff` at `n_s = ⌊Ws⌋` (`physTseq`, sorted eigenvalues), while the transmission
limit `μ(s)` and the cap event `physCapEvent` use the **near** transmission `T_{n_s}`
(`transmissionProcess`). This file proves that they agree.

* `charpoly_near_eq_far` (deterministic): for a unitary two-port `𝕊`,
  `charpoly(1 − 𝕊₀₀ᴴ𝕊₀₀) = charpoly(1 − 𝕊₁₁ᴴ𝕊₁₁)`. Chain: `1 − 𝕊₀₀ᴴ𝕊₀₀ = 𝕊₁₀ᴴ𝕊₁₀ ∼ 𝕊₁₀𝕊₁₀ᴴ
  = 1 − 𝕊₁₁𝕊₁₁ᴴ ∼ 1 − 𝕊₁₁ᴴ𝕊₁₁`. All blocks are `W × W`, so the full spectra agree.
* `coe_traceMeasure_eq_seq` (deterministic): for Hermitian `T`, `traceMeasure T` is the
  `seqTraceMeasure` of its padded decreasing eigenvalues.
* **`ae_transmissionProcess_eq_seq`**: a.s., `μ_W(s) = seqTraceMeasure (physTseq b E s W)`.
* **`ae_physCapEvent_iff`**: a.s., `ω ∈ physCapEvent ↔ seqTraceMeasure (physTseq) ∈ capSet K h`.
  So the physical cap event is the model cap event `entEvent physTseq (capSet K h)` up to a null
  set.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedReduce

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedIdent BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.FullSourceStops BlockBand.SourceProcess.SourcePins
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal

variable {W : ℕ}

/-- **Near and far transmission of a unitary two-port have the same characteristic
polynomial.** -/
theorem charpoly_near_eq_far (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (h1 : Sᴴ * S = 1)
    (h2 : S * Sᴴ = 1) :
    (1 - (portBlock S 0 0)ᴴ * portBlock S 0 0).charpoly =
      (1 - (portBlock S 1 1)ᴴ * portBlock S 1 1).charpoly := by
  have c00 := congrArg (fun M => portBlock M 0 0) h1
  have r11 := congrArg (fun M => portBlock M 1 1) h2
  simp only [portBlock_mul, portBlock_conjTranspose, portBlock_one, ite_true] at c00 r11
  have e1 : 1 - (portBlock S 0 0)ᴴ * portBlock S 0 0 = (portBlock S 1 0)ᴴ * portBlock S 1 0 := by
    rw [← c00]; abel
  have e2 : portBlock S 1 0 * (portBlock S 1 0)ᴴ = 1 - portBlock S 1 1 * (portBlock S 1 1)ᴴ := by
    rw [← r11]; abel
  rw [e1, Matrix.charpoly_mul_comm, e2, charpoly_one_sub_mul_comm]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem sum_eig_eq_ennreal {T : Matrix n n ℂ} (hT : T.IsHermitian) (g : ℝ → ℝ≥0∞) :
    ∑ i, g (hT.eigenvalues i) = ∑ i ∈ Finset.range (Fintype.card n), g (padEig hT i) := by
  have e1 : ∑ i, g (hT.eigenvalues i) = ∑ j, g (hT.eigenvalues₀ j) :=
    Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun j => g (hT.eigenvalues₀ j))
  rw [e1, ← Fin.sum_univ_eq_sum_range (fun i => g (padEig hT i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [padEig, j.2]

/-- **A finite trace measure is the trace measure of its padded eigenvalue sequence.** -/
theorem coe_traceMeasure_eq_seq {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    (traceMeasure T : Measure unitInterval) = seqTraceMeasure (padEig hT) := by
  ext A hA
  rw [BlockBand.Transmission.LawDuality.traceMeasure_eq_sum hT, FiniteMeasure.toMeasure_sum, Measure.coe_finsetSum,
    Finset.sum_apply, seqTraceMeasure, Measure.sum_apply _ hA,
    tsum_eq_sum (s := Finset.range (Fintype.card n)) fun k hk => by
      rw [padEig_eq_zero hT (not_lt.1 (by simpa using hk))]; simp]
  rw [sum_eig_eq_ennreal hT
    (fun x => ((Real.toNNReal x • unitDirac (toUnit x) : FiniteMeasure unitInterval) :
      Measure unitInterval) A)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [FiniteMeasure.toMeasure_smul]
  simp [unitDirac, Measure.dirac_apply' _ hA, ENNReal.ofReal]

variable {b E : ℝ}

/-- `T_r = 1 − 𝕊₀₀ᴴ𝕊₀₀` (Hermitian path blocks, invertible pencil, `Im z > 0`). -/
theorem pathTransmission_eq_near (r : ℕ) (ω : GrowthPath W) (hA : ∀ k, (ω.1 k).IsHermitian)
    (hη : 0 < (boundaryZ b E).im) (hF : IsUnit (pathMatrix (pathAt W r ω) - (E : ℂ) • 1)) :
    pathTransmission b E (fun _ => 0) W r ω =
      1 - (portBlock (scatteringMatrix b E W r ω) 0 0)ᴴ *
        portBlock (scatteringMatrix b E W r ω) 0 0 := by
  have hX := pathSchur_isHermitian E r ω hA
  have hD : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) -
      portBlock (pathSchur E (pathAt W r ω)) 1 1) :=
    BlockBand.Transmission.portPencil_isUnit _ (by
      ext x y; simpa [portBlock, Matrix.conjTranspose_apply] using
        congrFun (congrFun hX (1, x)) (1, y)) hη
  have hS00 : portBlock (twoPortScattering b E (pathSchur E (pathAt W r ω))) 0 0 =
      passiveS b E (nearSchur (boundaryZ b E) (pathSchur E (pathAt W r ω))) := by
    rw [passiveS, ← portBlock_twoPortResolvent_zero_zero b E _ hD]
    ext x y; simp [twoPortScattering, portBlock, Matrix.one_apply]; left; ring
  rw [pathTransmission, ← pathX, pathX_eq, scatteringMatrix_eq b E r ω hF, hS00,
    passiveTransmission_eq_one_sub]

/-- **Near and far transmission have the same characteristic polynomial**, a.s. for all lengths. -/
theorem ae_charpoly_near_eq_far (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ r, (pathTransmission b E (fun _ => 0) W r ω).charpoly =
      (farTransmission b E W r ω).charpoly := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [ae_growth_isHermitian W b, ae_isUnit_pathPencil_growth hb hW E] with ω hA hF r
  obtain ⟨h1, h2⟩ := twoPortScattering_unitary b E _ (pathSchur_isHermitian E r ω hA) hη
  rw [← scatteringMatrix_eq b E r ω (hF r)] at h1 h2
  rw [pathTransmission_eq_near r ω hA hη (hF r), farTransmission, farReflection]
  exact charpoly_near_eq_far _ h1 h2

/-- **The entrance identity at finite width**: a.s., the near transmission trace
measure `μ_W(s)` is the trace measure of the sorted far transmission eigenvalues `physTseq`. -/
theorem ae_transmissionProcess_eq_seq (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (s : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, (transmissionProcess b E (fun _ => 0) W s ω : Measure unitInterval) =
      seqTraceMeasure (physTseq b E s W ω) := by
  filter_upwards [ae_charpoly_near_eq_far hb hE1 hE2 hW] with ω hc
  have e : traceMeasure (pathTransmission b E (fun _ => 0) W (closeLen s W) ω) =
      traceMeasure (farTransmission b E W (closeLen s W) ω) := by
    unfold traceMeasure; rw [hc]
  rw [transmissionProcess, e, coe_traceMeasure_eq_seq (isHermitian_farTransmission b E W _ ω)]
  rfl

/-- **The cap events match** at finite width: a.s.,
`physCapEvent = entEvent physTseq (capSet K h)`. -/
theorem ae_physCapEvent_iff (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W)
    (s h : ℝ) (K : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, ω ∈ physCapEvent b E s h K W ↔
      ω ∈ entEvent (physTseq b E s W) (capSet K h) := by
  filter_upwards [ae_transmissionProcess_eq_seq hb hE1 hE2 hW s] with ω hω
  change _ ∈ capSet K h ↔ _ ∈ capSet K h
  rw [hω]

end BlockBand.SourceProcess.ClosedReduce
