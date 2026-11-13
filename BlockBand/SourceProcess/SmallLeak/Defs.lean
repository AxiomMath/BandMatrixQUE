module

public import BlockBand.SourceProcess.ClosingLeak.PathLeak
public import BlockBand.SourceProcess.FullSourceStops.CurrentStep

/-!
# Omitted far flux and omitted leakage along the path

At the closing time `s` (length `n_s = ⌊Ws⌋`) put `F_s = farEmbed A_-`, the far input projection
of the omitted modes `t_i ≤ h²` (`omittedProj`). Along the path `j ≥ n_s`:
* `omittedFlux j = Re Tr(F_s 𝕊_jᴴ P 𝕊_j F_s) = ‖P𝕊_jF_s‖²_F`, the flux from the omitted far
  inputs to the near output at length `j` (the paper's `g_A^in`, equal to `4η²Tr X`);
* `omittedLeak q j = Re Tr(F_s Q_j(q))`, the leaked interval-source mass (the paper's `ℓ_A`).

The statement `SmallChannelLeakage` is about `omittedLeak q ⌊WT⌋` (`omittedLeak_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.FullSourceStops BlockBand.SourceProcess.ClosingAux
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ClosingLeak
open scoped Matrix

variable {W : ℕ}

/-- `F_s = farEmbed A_-`: the omitted far inputs chosen at `n_s = ⌊Ws⌋` (cutoff `h`). -/
def farOmitted (b E h s : ℝ) (W : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω)

/-- `P' = 𝕊ᴴP𝕊` at length `j`. -/
def nearOut (b E : ℝ) (W j : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (scatteringMatrix b E W j ω)ᴴ * nearProjection W * scatteringMatrix b E W j ω

/-- **The omitted far flux** `g_j = Re Tr(F_s P'_j F_s)`. -/
def omittedFlux (b E h s : ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  (farOmitted b E h s W ω * nearOut b E W j ω * farOmitted b E h s W ω).trace.re

/-- **The omitted leakage** `ℓ_j = Re Tr(F_s Q_j(q))`. -/
def omittedLeak (b E h s : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  (farOmitted b E h s W ω * intervalSource b E W j q ω).trace.re

theorem omittedLeak_eq (b E h s T : ℝ) (q : ℝ → ℝ) (W : ℕ) (ω : GrowthPath W) :
    (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
      intervalSource b E W ⌊(W : ℝ) * T⌋₊ q ω).trace.re =
      omittedLeak b E h s q W ⌊(W : ℝ) * T⌋₊ ω := rfl

theorem farOmitted_conjTranspose (b E h s : ℝ) (W : ℕ) (ω : GrowthPath W) :
    (farOmitted b E h s W ω)ᴴ = farOmitted b E h s W ω := by
  rw [farOmitted, farEmbed_conjTranspose, omittedProj_conjTranspose]

theorem nearProjection_conjTranspose : (nearProjection W)ᴴ = nearProjection W := by
  rw [nearProjection, Matrix.diagonal_conjTranspose]
  congr 1; funext x; by_cases h : x.1 = 0 <;> simp [h]

theorem nearProjection_mul_self : nearProjection W * nearProjection W = nearProjection W := by
  rw [nearProjection, Matrix.diagonal_mul_diagonal]
  congr 1; funext x; by_cases h : x.1 = 0 <;> simp [h]

/-- `g_j = Re Tr((P𝕊F)ᴴ(P𝕊F))`. -/
theorem omittedFlux_eq (b E h s : ℝ) (W j : ℕ) (ω : GrowthPath W) :
    omittedFlux b E h s W j ω =
      ((nearProjection W * scatteringMatrix b E W j ω * farOmitted b E h s W ω)ᴴ *
        (nearProjection W * scatteringMatrix b E W j ω * farOmitted b E h s W ω)).trace.re := by
  set F := farOmitted b E h s W ω
  set S := scatteringMatrix b E W j ω
  set P := nearProjection W
  have hF : Fᴴ = F := farOmitted_conjTranspose b E h s W ω
  have hP : Pᴴ = P := nearProjection_conjTranspose
  have e : (P * S * F)ᴴ * (P * S * F) = F * (Sᴴ * P * S) * F := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF, hP]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, nearProjection_mul_self]
  rw [e]; rfl

theorem omittedFlux_nonneg (b E h s : ℝ) (W j : ℕ) (ω : GrowthPath W) :
    0 ≤ omittedFlux b E h s W j ω := by
  rw [omittedFlux_eq]
  exact trace_factor_re_nonneg _

theorem measurable_farOmitted (b E h s : ℝ) : Measurable (farOmitted (W := W) b E h s) :=
  measurable_farEmbed (measurable_omittedProj b E h _)

theorem measurable_omittedFlux (b E h s : ℝ) (j : ℕ) :
    Measurable (omittedFlux (W := W) b E h s j) := by
  have hF := measurable_farOmitted (W := W) b E h s
  have hS := measurable_scatteringMatrix (W := W) b E j
  have hP : Measurable fun ω : GrowthPath W =>
      (scatteringMatrix b E W j ω)ᴴ * nearProjection W * scatteringMatrix b E W j ω :=
    measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hS)
      measurable_const) hS
  exact measurable_trace_re (measurable_matrix_mul' (measurable_matrix_mul' hF hP) hF)

theorem measurable_omittedLeak (b E h s : ℝ) (q : ℝ → ℝ) (j : ℕ) :
    Measurable (omittedLeak (W := W) b E h s q j) :=
  measurable_trace_re (measurable_matrix_mul' (measurable_farOmitted b E h s)
    (measurable_intervalSource b E j q))

end BlockBand.SourceProcess.SmallLeak
