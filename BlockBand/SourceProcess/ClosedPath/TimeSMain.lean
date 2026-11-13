module

public import BlockBand.SourceProcess.ClosedPath.TimeS
public import BlockBand.SourceProcess.ClosedPath.Commute

/-!
# The closed frame at time `s` is exactly `initialGram`

`physClosingMapAt b E s h W n ω z` is the closing map with the time-`s` closing data
(`A_-`, `Π` at `n_s`) and the scattering matrix at length `n`; `physClosingMap` is the case
`n = ⌊WT⌋` (`physClosingMapAt_final`, `rfl`). **Closing at time `s`** is `n = n_s`.

* **`gramPair_physCurFrame`**: if `𝕊(n_s)𝕊(n_s)ᴴ = 1` and every retained mode among the first `K`
  has `t_k < 1`, then `gramPair P (physCurFrame) = initialGram K π (physTseq) h`.
* `omitted_mul_physCurFrame`: `A_-` kills the retained current columns.
* **`closedCurFrame_eq`**: for every `n` and every phase `z`, `C_n(z)ᴴ V_s = V_s` (no
  invertibility needed): closing does not move the retained current columns.
* **`gramPair_closedCurFrame_timeS`**: hence the closed frame at time `s` has Gram state exactly
  `initialGram` — the a.s. initial condition, not only its law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedPath

open Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedLimit
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic

variable {W : ℕ} {b E s h : ℝ} {K : ℕ} {ω : GrowthPath W}

/-- The closing map with the time-`s` data at the length `n`. -/
def physClosingMapAt (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  closingMap (scatteringMatrix b E W n ω) (farEmbed (omittedProj b E h W (closeLen s W) ω))
    (farEmbed (closingPairing b E h W (closeLen s W) ω)) z

theorem physClosingMapAt_final (T : ℝ) (z : ℂ) :
    physClosingMapAt b E s h W ⌊(W : ℝ) * T⌋₊ ω z = physClosingMap b E s T h W ω z := rfl

theorem nearPortProj_conjTranspose : (nearPortProj W)ᴴ = nearPortProj W := by
  simp only [nearPortProj, diagonal_conjTranspose]
  congr 1; funext x; by_cases hx : x.1 = 0 <;> simp [hx]

theorem nearPortProj_mul_self : nearPortProj W * nearPortProj W = nearPortProj W := by
  simp only [nearPortProj, diagonal_mul_diagonal]
  congr 1; funext x; split_ifs <;> simp

theorem physOutProj_conjTranspose : (physOutProj b E s W ω)ᴴ = physOutProj b E s W ω := by
  rw [physOutProj, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    nearPortProj_conjTranspose, Matrix.mul_assoc]

theorem physOutProj_mul_self
    (hS : scatteringMatrix b E W (closeLen s W) ω * (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1) :
    physOutProj b E s W ω * physOutProj b E s W ω = physOutProj b E s W ω := by
  set S := scatteringMatrix b E W (closeLen s W) ω
  calc physOutProj b E s W ω * physOutProj b E s W ω
      = Sᴴ * nearPortProj W * (S * Sᴴ) * nearPortProj W * S := by
        simp only [physOutProj, S, Matrix.mul_assoc]
    _ = _ := by
        rw [hS, Matrix.mul_one, Matrix.mul_assoc _ (nearPortProj W) (nearPortProj W),
          nearPortProj_mul_self]; rfl

theorem one_sub_mul_physOutProj_mul_physF
    (hS : scatteringMatrix b E W (closeLen s W) ω * (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1) :
    (1 - nearPortProj W) * physOutProj b E s W ω * physF b E s h K W ω =
      physF b E s h K W ω * tDiag K (physTseq b E s W ω) := by
  have hS' := mul_eq_one_comm.mp hS
  have e := farInj_conj_outProj_farInj (scatteringMatrix b E W (closeLen s W) ω)
  rw [← farTransmission_eq_of_unitary hS'] at e
  rw [one_sub_nearPortProj, physF]
  calc farInj W * (farInj W)ᴴ * physOutProj b E s W ω * (farInj W * physFw b E s h K W ω)
      = farInj W * ((farInj W)ᴴ * physOutProj b E s W ω * farInj W) *
          physFw b E s h K W ω := by simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [physOutProj] at *
        rw [e, Matrix.mul_assoc, farTransmission_mul_physFw, ← Matrix.mul_assoc]

/-- **The physical current frame at time `s` has Gram state `initialGram`.** -/
theorem gramPair_physCurFrame (π : Type*)
    (hS : scatteringMatrix b E W (closeLen s W) ω * (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1) :
    gramPair (nearPortProj W) (physCurFrame b E s h K π W ω) =
      initialGram K π (physTseq b E s W ω) h :=
  gramPair_curFrame π nearPortProj_conjTranspose nearPortProj_mul_self physOutProj_conjTranspose
    (physOutProj_mul_self hS) nearPortProj_mul_physF physF_conj_mul_self
    (one_sub_mul_physOutProj_mul_physF hS)
    (fun k hk => ⟨lt_of_le_of_lt (sq_nonneg h) hk, hlt k hk⟩)

theorem omittedProj_mul_physFw :
    omittedProj b E h W (closeLen s W) ω * physFw b E s h K W ω = 0 := by
  ext a k
  have e := cfc_mulVec_of_eigen (isHermitian_farTransmission b E W (closeLen s W) ω)
    (omitIndicator h) (farTransmission_mulVec_physFarVec (b := b) (E := E) (s := s) (ω := ω) k.val)
  simp only [mul_apply, physFw, of_apply, Matrix.zero_apply]
  split_ifs with hk
  · have hz := congrFun e a
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, omitIndicator,
      show ¬ physTseq b E s W ω k.val ≤ h ^ 2 from not_le.mpr hk, ↓reduceIte] at hz
    simpa [omittedProj] using hz
  · simp

/-- `A_-` kills the retained current columns. -/
theorem omitted_mul_physCurFrame (π : Type*) :
    farEmbed (omittedProj b E h W (closeLen s W) ω) * physCurFrame b E s h K π W ω = 0 := by
  set A := farEmbed (omittedProj b E h W (closeLen s W) ω)
  have hN : A * nearPartners (nearPortProj W) (physOutProj b E s W ω) (physF b E s h K W ω)
      (physTseq b E s W ω) = 0 := by
    simp only [nearPartners, ← Matrix.mul_assoc, A, farEmbed_mul_nearPortProj, Matrix.zero_mul]
  have hF : A * physF b E s h K W ω = 0 := by
    rw [physF, ← Matrix.mul_assoc, farEmbed_mul_farInj, Matrix.mul_assoc, omittedProj_mul_physFw,
      Matrix.mul_zero]
  have hΦ : A * pairFrame (nearPortProj W) (physOutProj b E s W ω) (physF b E s h K W ω)
      (physTseq b E s W ω) = 0 := by
    ext x ⟨k, σ⟩
    have : (A * pairFrame (nearPortProj W) (physOutProj b E s W ω) (physF b E s h K W ω)
        (physTseq b E s W ω)) x (k, σ) = (A * pairBlock (nearPortProj W) (physOutProj b E s W ω)
          (physF b E s h K W ω) (physTseq b E s W ω) σ) x k := by
      simp only [mul_apply, pairFrame, of_apply]
    rw [this]
    fin_cases σ <;> simp [pairBlock, hN, hF]
  rw [physCurFrame, curFrame, ← Matrix.mul_assoc, hΦ, Matrix.zero_mul]

/-- **Closing does not move the retained current columns**: `C_n(z)ᴴ V_s = V_s`. -/
theorem closedCurFrame_eq (π : Type*) (n : ℕ) (z : ℂ) :
    (physClosingMapAt b E s h W n ω z)ᴴ * physCurFrame b E s h K π W ω =
      physCurFrame b E s h K π W ω := by
  refine closingMap_conj_fix ?_ ?_ (omitted_mul_physCurFrame π)
  · rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  · rw [farEmbed_mul, omittedProj_mul_closingPairing]

/-- **The frame closed at time `s` has Gram state exactly `initialGram`**, for every phase. -/
theorem gramPair_closedCurFrame_timeS (π : Type*) (z : ℂ)
    (hS : scatteringMatrix b E W (closeLen s W) ω * (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1) :
    gramPair (nearPortProj W) ((physClosingMapAt b E s h W (closeLen s W) ω z)ᴴ *
      physCurFrame b E s h K π W ω) = initialGram K π (physTseq b E s W ω) h := by
  rw [closedCurFrame_eq, gramPair_physCurFrame π hS hlt]

end BlockBand.SourceProcess.ClosedPath
