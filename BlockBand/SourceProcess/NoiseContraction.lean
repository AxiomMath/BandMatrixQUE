module

public import BlockBand.SourceProcess.GramMatrices

/-!
# Crossed noise coefficients of the Gram dynamics

The four-frame contraction of the noise covariance `D₀(P ⊗ P' + P' ⊗ P)/2` in the Gram
coordinates `M`, `B`, the resulting drift cancellations for `M` and `B`, and the vanishing of
all noise coefficients on the face where the near rank is zero.
-/

@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess
open Matrix

/-- Four-frame contraction of `D₀(P ⊗ P' + P' ⊗ P)/2`, with crossed entry indices `(il, kj)`. -/
def crossedGramCoefficient {ι κ : Type*} [Fintype ι]
    (D0 : ℂ) (P Pprime : Matrix ι ι ℂ) (V W : Matrix ι κ ℂ)
    (i j k l : κ) : ℂ :=
  D0 / 2 * ((Vᴴ * P * W) i l * (Wᴴ * Pprime * V) k j +
    (Vᴴ * Pprime * W) i l * (Wᴴ * P * V) k j)

/-- The `MM` coefficient. -/
theorem crossed_coefficient_MM {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D0 : ℂ) (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (i j k l : κ) :
    crossedGramCoefficient D0 P (gramProjection P V D) V V i j k l =
      D0 / 2 * (nearGram P V i l * gramC0 (sourceGram V) (nearGram P V) D k j +
        gramC0 (sourceGram V) (nearGram P V) D i l * nearGram P V k j) := by
  simp only [crossedGramCoefficient, gram_sandwich_C0, nearGram]

/-- The `MB` coefficient, with the adjoint on the `kj` factor `C1`. -/
theorem crossed_coefficient_MB {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D0 : ℂ) (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (hP : P * P = P) (hPH : Pᴴ = P) (hDH : Dᴴ = D) (i j k l : κ) :
    crossedGramCoefficient D0 P (gramProjection P V D) V (P * V) i j k l =
      D0 / 2 * (nearGram P V i l *
        (gramC1 (sourceGram V) (nearGram P V) D)ᴴ k j +
        gramC1 (sourceGram V) (nearGram P V) D i l * nearGram P V k j) := by
  have hpv : P * (P * V) = P * V := by
    rw [← Matrix.mul_assoc, hP]
  have h1 : Vᴴ * P * (P * V) = nearGram P V := by
    simp only [nearGram, Matrix.mul_assoc, hpv]
  have h2 : (P * V)ᴴ * gramProjection P V D * V =
      (gramC1 (sourceGram V) (nearGram P V) D)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hPH, Matrix.mul_assoc] using
      gram_sandwich_C1_adjoint P V D hP hPH hDH
  have h3 : Vᴴ * gramProjection P V D * (P * V) =
      gramC1 (sourceGram V) (nearGram P V) D := by
    simpa only [Matrix.mul_assoc] using gram_sandwich_C1 P V D hP
  have h4 : (P * V)ᴴ * P * V = nearGram P V := by
    simp [Matrix.conjTranspose_mul, hPH, nearGram, Matrix.mul_assoc, hP]
  simp only [crossedGramCoefficient, h1, h2, h3, h4]

/-- BB coefficient for the two projected frames. -/
theorem crossed_coefficient_BB {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D0 : ℂ) (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (hP : P * P = P) (hPH : Pᴴ = P) (i j k l : κ) :
    crossedGramCoefficient D0 P (gramProjection P V D) (P * V) (P * V) i j k l =
      D0 / 2 * (nearGram P V i l * gramC2 (nearGram P V) D k j +
        gramC2 (nearGram P V) D i l * nearGram P V k j) := by
  have hpv : P * (P * V) = P * V := by
    rw [← Matrix.mul_assoc, hP]
  have h1 : (P * V)ᴴ * P * (P * V) = nearGram P V := by
    simp only [Matrix.conjTranspose_mul, hPH, nearGram, Matrix.mul_assoc, hpv]
  have h2 : (P * V)ᴴ * gramProjection P V D * (P * V) = gramC2 (nearGram P V) D := by
    simpa only [Matrix.conjTranspose_mul, hPH, Matrix.mul_assoc] using
      gram_sandwich_C2 P V D hP
  simp only [crossedGramCoefficient, h1, h2]

/-- Equal-rank idempotents give the near contraction `Naux - g` (the coefficient used for the
drift cancellation of `B`). -/
theorem near_projection_overlap {ι : Type*} [Fintype ι]
    (P Pprime : Matrix ι ι ℂ) (hP : P * P = P) (hPprime : Pprime * Pprime = Pprime)
    (hrank : Pprime.trace = P.trace) :
    (Pprime * P).trace = P.trace - currentConductance P Pprime := by
  have h := fullCurrent_near_trace P Pprime hP hPprime hrank
  simp only [fullCurrent, Matrix.sub_mul, Matrix.trace_sub, hP] at h
  linear_combination h

/-- Drift cancellation for `M` at the source variance. -/
theorem gram_norm_drift_cancellation (D0 Naux : ℂ) {κ : Type*} [Fintype κ]
    (B : Matrix κ κ ℂ) :
    (-(D0 * Naux / 4)) • B + (-(D0 * Naux / 4)) • B +
      (D0 * Naux / 2) • B = 0 := by
  rw [← add_smul, ← add_smul]
  have h : -(D0 * Naux / 4) + -(D0 * Naux / 4) + D0 * Naux / 2 = 0 := by ring
  rw [h, zero_smul]

/-- The projected drift of `B` is `-D₀ g B/2` after the `Naux` cancellation. -/
theorem gram_near_drift_cancellation (D0 Naux g : ℂ) {κ : Type*} [Fintype κ]
    (B : Matrix κ κ ℂ) :
    (-(D0 * Naux / 4)) • B + (-(D0 * Naux / 4)) • B +
      (D0 * (Naux - g) / 2) • B = (-(D0 * g / 2)) • B := by
  rw [← add_smul, ← add_smul]
  congr 1
  ring

/-- On the face where the near rank is zero, every noise coefficient vanishes pointwise (a
statement about the generator at the boundary only). -/
theorem near_zero_noise_coefficients {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D0 : ℂ) (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (hP : P * P = P) (hPH : Pᴴ = P) (hDH : Dᴴ = D)
    (hB : nearGram P V = 0) (i j k l : κ) :
    crossedGramCoefficient D0 P (gramProjection P V D) V V i j k l = 0 ∧
    crossedGramCoefficient D0 P (gramProjection P V D) V (P * V) i j k l = 0 ∧
    crossedGramCoefficient D0 P (gramProjection P V D) (P * V) (P * V) i j k l = 0 := by
  rw [crossed_coefficient_MM, crossed_coefficient_MB D0 P V D hP hPH hDH,
    crossed_coefficient_BB D0 P V D hP hPH]
  simp [hB]

end BlockBand.SourceProcess
