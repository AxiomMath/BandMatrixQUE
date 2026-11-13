module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm
public import BlockBand.SourceProcess.PhysApprox.B3DecayDefs

/-!
# The closed step form with explicit frames; the near-rows identity

* **`closedStepForm_explicit`**: the a.e. closed exact update of `closedStep_core` with the frames
  exhibited: `u = clipVec √R (1_{A_i} closedNearU)`, `v = clipVec √R (1_{A_i} closedNearV)`.
* **`closedStep_indicator`**: the same without clipping,
  `Z_i = 1_{A_i}·closedNearU*Δ(X_cl, F_i)closedNearV` a.e. (`A_i = b3AliveM`).
* **`nearS_one_add_closingZ`** (algebra, near-rows identity (I*)): for unitary `𝕊`, `|z| = 1`,
  `1 - zN` invertible, `ΠΠᴴ = A`, `Πιᴴ = 0`: `ι𝕊(1 + Z) = ι𝕊C(z)C(z)ᴴ`. Only `ι𝕊Zᴴ = 0` is used
  (from `𝕊𝕊ᴴ = 1`, `ιΠᴴ = 0`); no property of the probe frame is needed.
* **`closedNearV_eq_closedPS`**, **`ae_closedNearV_eq_closedPS`**: hence
  `closedNearV l = ι*·b3ClosedPS·V_cl e_l` (`V_cl e_l` the probe column of `b3ClosedFrameAt`)
  surely under unitarity, `|z| = 1`, `1 - zN` invertible, and `closedLaw`-a.e. for all `l`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit
open BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.PhysApprox.ClosedForm

variable {W np K : ℕ}

/-!
## (a) Explicit frames
-/

/-- **The closed exact update with the explicit clipped frames** (those of `closedStep_core`). -/
theorem closedStepForm_explicit {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (hW : 1 ≤ W)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (R : ℝ) {i : ℕ}
    (hi : 1 ≤ i) (hsi : closeLen s W ≤ i) (ij : Fin np × Fin np)
    (h1 : ⌊(W : ℝ) * τ ij.1⌋₊ < i) (h2 : ⌊(W : ℝ) * τ ij.2⌋₊ < i) :
    kStopStep b E s h τ m R W i Vs ij =ᵐ[closedLaw b W np] fun y =>
      bilinear (clipVec (Real.sqrt R)
          ((b3AliveM b E s h τ m R W i Vs).indicator (closedNearU b E s h τ m W i ij.1) y))
        (freshDelta b E (b3ClosedX b E s h τ m W i y) (freshSample W i y.1.1))
        (clipVec (Real.sqrt R)
          ((b3AliveM b E s h τ m R W i Vs).indicator (closedNearV b E s h τ m W i ij.2) y)) := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  set Al := b3AliveM (np := np) b E s h τ m R W i Vs with hAl
  filter_upwards [kStopStep_ae_eq (by linarith) hE1 hE2 s h τ m R W i Vs ij,
    ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
    ae_closedPhase_good (W := W) (np := np) b E s h i] with y hZ hP hQ
  obtain ⟨hA, hF, hB, hS⟩ := hP
  obtain ⟨hU, hU', hY, h4⟩ := hQ
  have hR := h4.resolve_left (isUnit_closedR0 b E h s i y.1.1 hA hη (hF i)).ne_zero
  have hX := passive_closedNearX b E s h hh i y.1.1 y.2 hη (hS i) (isUnit_iff_ne_zero.2 hU)
    (isUnit_iff_ne_zero.2 hR)
  rw [hZ, kStopStepM]
  by_cases hy : y ∈ Al
  · have htr : ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re < R := hy.2 i hsi le_rfl
    have hu := norm_closedNearU_le b E s h τ m i Vs ij.1 y htr
    have hv := norm_closedNearV_le b E s h hh τ m i Vs ij.2 y (hS i) (isUnit_iff_ne_zero.2 hU) htr
    rw [← hAl, Set.indicator_of_mem hy, Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    simp only [clipVec, hu, hv, ↓reduceIte]
    exact closedK_step b E s h τ m hi y hA hη (hF i) (hF (i + 1)) (hB (i + 1))
      (isUnit_iff_ne_zero.2 hU) (isUnit_iff_ne_zero.2 hU') (isUnit_iff_ne_zero.2 hY)
      (isUnit_iff_ne_zero.2 hR) hX h1 h2
  · rw [← hAl, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    simp [clipVec, bilinear, vecNorm]

/-- **The closed exact update on the alive set, unclipped**:
`Z_i = 1_{A_i}·closedNearU*Δ(X_cl, F_i)closedNearV` a.e. -/
theorem closedStep_indicator {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (hW : 1 ≤ W)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (R : ℝ) {i : ℕ}
    (hi : 1 ≤ i) (hsi : closeLen s W ≤ i) (ij : Fin np × Fin np)
    (h1 : ⌊(W : ℝ) * τ ij.1⌋₊ < i) (h2 : ⌊(W : ℝ) * τ ij.2⌋₊ < i) :
    kStopStep b E s h τ m R W i Vs ij =ᵐ[closedLaw b W np]
      (b3AliveM b E s h τ m R W i Vs).indicator fun y =>
        bilinear (closedNearU b E s h τ m W i ij.1 y)
          (freshDelta b E (b3ClosedX b E s h τ m W i y) (freshSample W i y.1.1))
          (closedNearV b E s h τ m W i ij.2 y) := by
  filter_upwards [closedStepForm_explicit hb0 hb hE1 hE2 s h hh τ m hW Vs R hi hsi ij h1 h2,
    ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
    ae_closedPhase_good (W := W) (np := np) b E s h i] with y hy hP hQ
  rw [hy]
  by_cases hA : y ∈ b3AliveM b E s h τ m R W i Vs
  · have htr : ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re < R := hA.2 i hsi le_rfl
    have hu := norm_closedNearU_le b E s h τ m i Vs ij.1 y htr
    have hv := norm_closedNearV_le b E s h hh τ m i Vs ij.2 y (hP.2.2.2 i)
      (isUnit_iff_ne_zero.2 hQ.1) htr
    rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    simp only [clipVec, hu, hv, ↓reduceIte]
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]
    simp [clipVec, bilinear, vecNorm]

/-!
## (b) The near-rows identity
-/

/-- **(I*)**, algebra: `ι𝕊(1 + Z) = ι𝕊C(z)C(z)ᴴ` for unitary `𝕊`, `|z| = 1`. -/
theorem nearS_one_add_closingZ {P : Type*} [Fintype P] [DecidableEq P] {k : Type*}
    {S A Pi : Matrix P P ℂ} {z : ℂ} {ns : Matrix k P ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1) (hz : z * star z = 1)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (hPins : Pi * nsᴴ = 0) :
    ns * S * (1 + closingZ S A Pi z) =
      ns * S * (closingMap S A Pi z * (closingMap S A Pi z)ᴴ) := by
  have hnsPi : ns * Piᴴ = 0 := by
    have := congrArg conjTranspose hPins
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
  have hZ : ns * S * (closingZ S A Pi z)ᴴ = 0 := by
    simp only [closingZ, conjTranspose_smul, conjTranspose_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc ns S Sᴴ, hS, Matrix.mul_one, hnsPi, Matrix.zero_mul, smul_zero]
  rw [closingMap_mul_conj hA2 hAH hPi hS hz hU, Matrix.mul_add (ns * S) (1 + _), hZ, add_zero]

theorem nearSel_mul_nearPortProj : nearSel W * nearPortProj W = nearSel W := by
  ext x c
  rw [nearPortProj, Matrix.mul_diagonal]
  by_cases hc : c = (0, x)
  · subst hc; simp [nearSel]
  · simp [nearSel, hc]

/-- **(I*)**: `closedNearV l = ι*·b3ClosedPS·V_cl e_l` under unitarity, `|z| = 1`, `1 - zN`
invertible (no alive-set condition needed). -/
theorem closedNearV_eq_closedPS (b E s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (l : Fin np)
    (y : ProbedPath W np × ℝ)
    (hS : scatteringMatrix b E W j y.1.1 * (scatteringMatrix b E W j y.1.1)ᴴ = 1)
    (hU : IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W j y.1.1)
      (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det) :
    closedNearV b E s h τ m W j l y = nearSel W *ᵥ (b3ClosedPS b E s h W j y.1.1 (phase y.2) *ᵥ
      fun a => b3ClosedFrameAt b E s h τ m W j Vs y a (Sum.inr l)) := by
  set S := scatteringMatrix b E W j y.1.1
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) y.1.1)
  have hA2 : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have key := nearS_one_add_closingZ hA2 hAH hPi hS (phase_mul_star y.2) hU
    (farEmbed_mul_nearSel_conj (W := W) _)
  rw [closedFrame_col, b3ClosedPS, closedNearV, physClosingZAt]
  simp only [mulVec_mulVec]
  congr 1
  simp only [Matrix.mul_assoc] at key ⊢
  rw [← Matrix.mul_assoc (nearSel W) (nearPortProj W), nearSel_mul_nearPortProj]
  exact key

/-- **(I*) almost surely**, at every length and every probe column. -/
theorem ae_closedNearV_eq_closedPS {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (hW : 1 ≤ W) (j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    ∀ᵐ y ∂closedLaw b W np, ∀ l, closedNearV b E s h τ m W j l y =
      nearSel W *ᵥ (b3ClosedPS b E s h W j y.1.1 (phase y.2) *ᵥ
        fun a => b3ClosedFrameAt b E s h τ m W j Vs y a (Sum.inr l)) := by
  filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
    ae_closedPhase_good (W := W) (np := np) b E s h j] with y hP hQ l
  exact closedNearV_eq_closedPS b E s h hh τ m j Vs l y (hP.2.2.2 j) (isUnit_iff_ne_zero.2 hQ.1)

end BlockBand.SourceProcess.PhysApprox.B3

