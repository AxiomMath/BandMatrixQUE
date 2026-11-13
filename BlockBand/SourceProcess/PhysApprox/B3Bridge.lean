module

public import BlockBand.SourceProcess.PhysApprox.B3Pins

/-!
# The closed complex process at the final length and at the start

* **The final length**: at `j = ⌊WT⌋` the closed process (time-`s` closing data,
  `physClosingMapAt`) is the closed data of `closedSourceData`:
  `b3ClosedKAt_final` (`𝒦_cl`), `b3ClosedFrameAt_final_probe` (probe columns = `closedFrame`),
  and `closedSourceData_eq_model` (the coordinates `𝒦, M_pr, B_pr` of `closedSourceData` are
  those of `modelSourceData` of the closed process, for **every** time-`s` frame). The fourth
  coordinate is the estimate `ComplexClosedCurrent`.
* **The start**: at `j = ⌊Ws⌋`, no tag is present (`s < τ_i`), so the closed `𝒦` vanishes
  (`b3ClosedKAt_start`, `Kc₀ = 0`); with the time-`s` frame of `physCurFrame` the closed Gram
  state is `initialGram K (Fin np) t h`, almost surely, for every probe sample and phase
  (`ae_b3ClosedGramAt_start`, from `ae_gramPair_closedCurFrame_timeS`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ClosedSum

variable {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ} {W : ℕ}

/-!
## The final length
-/

/-- **The closed `𝒦` at the final length is the `closedK`.** -/
theorem b3ClosedKAt_final (T : ℝ) (y : ProbedPath W np × ℝ) :
    b3ClosedKAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ y =
      PhysApprox.closedK b E s T h τ m W (phase y.2) y.1 := rfl

/-- **The probe columns of the closed frame at the final length are the `closedFrame`.** -/
theorem b3ClosedFrameAt_final_probe (T : ℝ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ) :
    (b3ClosedFrameAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ Vs y).submatrix id Sum.inr =
      PhysApprox.closedFrame b E s T h τ m W (phase y.2) y.1 := by
  ext z i
  simp only [submatrix_apply, id_eq, b3ClosedFrameAt, PhysApprox.closedFrame, mul_apply,
    b3OpenFrameAt, of_apply, Sum.elim_inr, physClosingMapAt_final]

/-- The probe block of `Fᴴ P F` is the Gram form of the probe columns of `F`. -/
theorem probeBlock_conjTranspose_mul {ι π : Type*} [Fintype ι] (F : Matrix ι (SrcCol K π) ℂ)
    (P : Matrix ι ι ℂ) :
    probeBlock (Fᴴ * P * F) = (F.submatrix id Sum.inr)ᴴ * P * F.submatrix id Sum.inr := rfl

/-- **The first three coordinates of `closedSourceData` are model coordinates of the closed
process at the final length**, for every time-`s` frame `V_s`. -/
theorem closedSourceData_eq_model (T : ℝ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    (r : Fin 4) (hr : r ≠ 3) :
    PhysApprox.closedSourceData b E s T h τ m W (phase y.2) y.1 r =
      modelSourceData (srcSignature K (Fin np)) (b3ClosedKAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ y)
        (b3ClosedGramAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ Vs y) r := by
  have h1 : probeBlock (b3ClosedGramAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ Vs y).1 =
      (PhysApprox.closedFrame b E s T h τ m W (phase y.2) y.1)ᴴ *
        PhysApprox.closedFrame b E s T h τ m W (phase y.2) y.1 := by
    have := probeBlock_conjTranspose_mul (b3ClosedFrameAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ Vs y) 1
    simp only [Matrix.mul_one, b3ClosedFrameAt_final_probe] at this
    exact this
  have h2 : probeBlock (b3ClosedGramAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ Vs y).2 =
      (PhysApprox.closedFrame b E s T h τ m W (phase y.2) y.1)ᴴ * nearProjection W *
        PhysApprox.closedFrame b E s T h τ m W (phase y.2) y.1 := by
    have := probeBlock_conjTranspose_mul (b3ClosedFrameAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ Vs y)
      (nearPortProj W)
    rw [b3ClosedFrameAt_final_probe] at this
    exact this
  fin_cases r
  · rfl
  · exact h1.symm
  · exact h2.symm
  · exact absurd rfl hr

/-!
## The start
-/

/-- No tag column is present at the start length `⌊Ws⌋` when every tag is born after `s`. -/
theorem probeColumns_start (hτ : ∀ i, s < τ i) (g : Fin np → Fin W → ℂ) :
    probeColumns W (closeLen s W) τ m g = 0 := by
  ext x i
  have hle : closeLen s W ≤ ⌊(W : ℝ) * τ i⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (hτ i).le (Nat.cast_nonneg W))
  simp [probeColumns, not_lt.2 hle]

theorem probeFrame_start (hτ : ∀ i, s < τ i) (x : ProbedPath W np) :
    probeFrame b E W (closeLen s W) τ m x = 0 := by
  simp [probeFrame, probeColumns_start hτ]

/-- **The closed `𝒦` vanishes at the start** (`Kc₀ = 0`: no probes at `s`). -/
theorem b3ClosedKAt_start (hτ : ∀ i, s < τ i) (y : ProbedPath W np × ℝ) :
    b3ClosedKAt b E s h τ m W (closeLen s W) y = 0 := by
  simp [b3ClosedKAt, complexSourceK, probeFrame_start hτ, probeColumns_start hτ]

/-- With `V_s` the current block of `physCurFrame`, the open frame at `⌊Ws⌋` is
`physCurFrame` (no tag present). -/
theorem b3OpenFrameAt_start (hτ : ∀ i, s < τ i) (x : ProbedPath W np) :
    b3OpenFrameAt b E s τ m W (closeLen s W)
        (fun ω => curBlock (physCurFrame b E s h K (Fin np) W ω)) x =
      physCurFrame b E s h K (Fin np) W x.1 := by
  ext z (k | i)
  · simp [b3OpenFrameAt, curBlock, stepProd]
  · simp only [b3OpenFrameAt, of_apply, Sum.elim_inr, probeFrame_start hτ, Matrix.zero_apply]
    simp [physCurFrame, curFrame, mul_apply, initialFrame]

/-- **The closed Gram process starts at `initialGram`**, almost surely, for every probe sample
and phase (`ae_closedGramAt_start` with tags in place of sampled probes). -/
theorem ae_b3ClosedGramAt_start (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W)
    (hτ : ∀ i, s < τ i) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (g : Fin np → Fin W → ℂ) (θ : ℝ),
      b3ClosedGramAt b E s h τ m W (closeLen s W)
          (fun ω => curBlock (physCurFrame b E s h K (Fin np) W ω)) ((ω, g), θ) =
        initialGram K (Fin np) (physTseq b E s W ω) h := by
  filter_upwards [ae_gramPair_closedCurFrame_timeS (s := s) (Fin np) hb hE1 hE2 hW]
    with ω hG g θ
  rw [b3ClosedGramAt, b3ClosedFrameAt, b3OpenFrameAt_start hτ (ω, g)]
  exact hG K h (phase θ)

end BlockBand.SourceProcess.PhysApprox.B3
