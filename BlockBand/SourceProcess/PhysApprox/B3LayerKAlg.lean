module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm
public import BlockBand.SourceProcess.PhysApprox.B3DecayDefs
public import BlockBand.SourceProcess.FullSourceCovariance.WardTensor

/-!
# The closed `𝒦` mean factor is the closed contracting coordinate `Q^{P𝕊}`

The closed exact update (`closedK_step`) is `Δ𝒦_cl = u_k*Δ(X_cl, F)v_l` with
`u_k = ι*C_j(z)*V_je_k` (`closedNearU`) and `v_l = ι*𝕊_j(1 + Z_j(z))V_je_l` (`closedNearV`).
Here, deterministically:

* `nearSel_mul_closingGram` (pure algebra): `ι𝕊C(z)C(z)ᴴ = ι𝕊(1 + Z(z))` for unitary `𝕊`,
  `|z| = 1`, `ΠΠᴴ = A`, `Πιᴴ = 0`, `1 - zN` invertible. Proof: `CCᴴ = 1 + Z + Zᴴ`
  (`closingMap_mul_conj`) and `ι𝕊Zᴴ = z̄ι𝕊𝕊ᴴΠᴴ(⋯) = z̄ιΠᴴ(⋯) = 0`.
* **`b3ContrCoord_zero_inr`**: `u_k*v_l = Q^{P𝕊_cl}_{(pr k),(pr l)}(j)`, the closed contracting
  coordinate `b3ContrCoord … 0 (inr k) (inr l)`. So the first-order part
  `⟨EΔ⟩·u_k*v_l` of the closed `𝒦` mean is a contracting coordinate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit
open BlockBand.Transmission.Bridge

variable {W np K : ℕ}

/-- **`ι𝕊C(z)C(z)ᴴ = ι𝕊(1 + Z(z))`** (lossless closing, near rows). -/
theorem nearSel_mul_closingGram {P k : Type*} [Fintype P] [DecidableEq P] [Fintype k]
    {S A Pi : Matrix P P ℂ} {z : ℂ} {ns : Matrix k P ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1) (hz : z * star z = 1)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (hPins : Pi * nsᴴ = 0) :
    ns * S * (closingMap S A Pi z * (closingMap S A Pi z)ᴴ) =
      ns * (S * (1 + closingZ S A Pi z)) := by
  have h1 : ns * Piᴴ = 0 := by
    have := congrArg conjTranspose hPins
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
  have hZ : ns * S * (closingZ S A Pi z)ᴴ = 0 := by
    simp only [closingZ, conjTranspose_smul, conjTranspose_mul, Matrix.mul_smul]
    rw [show ns * S * (Sᴴ * Piᴴ * ((1 - z • closingN S A Pi)⁻¹)ᴴ) =
        ns * (S * Sᴴ) * Piᴴ * ((1 - z • closingN S A Pi)⁻¹)ᴴ by simp only [Matrix.mul_assoc],
      hS, Matrix.mul_one, h1, Matrix.zero_mul, smul_zero]
  rw [closingMap_mul_conj hA2 hAH hPi hS hz hU, Matrix.mul_add, hZ, add_zero, Matrix.mul_assoc]

theorem nearPortProj_eq_nearSel : nearPortProj W = (nearSel W)ᴴ * nearSel W := by
  rw [FullSourceCovariance.nearSel_conj_mul_nearSel]
  rfl

/-- **The closed `𝒦` mean factor is a closed contracting coordinate**: `u_k*v_l = Q^{P𝕊_cl}`
at the probe columns, for unitary `𝕊_j`, `|z| = 1` and `1 - zN_j` invertible. -/
theorem b3ContrCoord_zero_inr (b E s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (k l : Fin np)
    (y : ProbedPath W np × ℝ)
    (hS : scatteringMatrix b E W j y.1.1 * (scatteringMatrix b E W j y.1.1)ᴴ = 1)
    (hU : IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W j y.1.1)
      (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det) :
    b3ContrCoord b E s h τ m W j Vs 0 (Sum.inr k) (Sum.inr l) y =
      star (closedNearU b E s h τ m W j k y) ⬝ᵥ closedNearV b E s h τ m W j l y := by
  set S := scatteringMatrix b E W j y.1.1
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) y.1.1)
  set z := phase y.2
  set C := closingMap S A Pi z with hC
  have hA2 : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have hM : nearPortProj W * S * C * Cᴴ =
      (nearSel W)ᴴ * (nearSel W * (S * (1 + closingZ S A Pi z))) := by
    rw [← nearSel_mul_closingGram hA2 hAH hPi hS (phase_mul_star y.2) hU
      (farEmbed_mul_nearSel_conj _), nearPortProj_eq_nearSel]
    simp only [Matrix.mul_assoc]
    rfl
  have hcol : ∀ i : Fin np, (fun a => b3ClosedFrameAt b E s h τ m W j Vs y a (Sum.inr i)) =
      Cᴴ *ᵥ probeCol b E τ m W j i y.1 := fun i => closedFrame_col b E s h τ m j Vs i y
  rw [b3ContrCoord, entry_eq_dot, hcol, hcol]
  have hPS : b3ContrSep b E s h W j y.1.1 (phase y.2) 0 = nearPortProj W * S * C := rfl
  rw [hPS, mulVec_mulVec, hM, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [closedNearU, closedNearV, physClosingZAt, ← mulVec_mulVec]
  rfl

end BlockBand.SourceProcess.PhysApprox.B3
