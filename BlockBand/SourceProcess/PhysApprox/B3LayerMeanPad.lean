module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanChain
public import BlockBand.SourceProcess.ClosedPath.Commute
public import BlockBand.SourceProcess.Closing.PhysHardy
public import BlockBand.Transmission.SchurPassivity
public import BlockBand.Transmission.Bridge.Scattering

/-!
# The padded closed scatterer is unitary; `nearSchur(b3ChainXX) = b3ClosedX`

Abstract closing data `S, A, Π` on a finite index type, `O = ΠᴴΠ`, `C = C(z)`
(`closingMap`), `𝕊_pad = (1 - O)𝕊C(1 - A) + ΠᴴA` (`padScat`; `b3PadScatter` is `padScat` of the
path data, by `rfl`).

* **`padScat_unitary`**: `𝕊_padᴴ𝕊_pad = 1` from `𝕊ᴴ𝕊 = 1`, `A = Aᴴ = A²`, `ΠΠᴴ = A`,
  `AΠ = Π`, `|z| = 1` and `1 - zN` invertible. Route: with `Y = C(1 - A)`, `(1 - A)Y = 1 - A`
  and `ΠSY = z̄AY` (closing feedback), `KᴴK = YᴴY - (AY)ᴴ(AY) = 1 - A` for `K = (1 - O)SY`;
  `(1 - O)Πᴴ = 0`; `(ΠᴴA)ᴴ(ΠᴴA) = A`.
* **`cayley_isHermitian`**: `z₀ - 2iη(1 - U)⁻¹` is Hermitian for unitary `U` with
  `1 - U` invertible and `Im z₀ = η`.
* **`nearSel_b3PadScatter`** (the near-block identity): `ι*𝕊_padι = 1 - 2iη R_cl` with
  `R_cl = closedNearR = ι*ℝ_jC_j(z)ι`. No hypothesis.
* **`nearSchur_b3ChainXX`**: if `b3ChainXX` is Hermitian, `η > 0` and `1 - 𝕊_pad` is
  invertible, then `nearSchur z_∂ (b3ChainXX) = closedNearX` (`= b3ClosedX`).
* **`b3ChainXX_good`**: with `𝕊_j` unitary, `|z| = 1`, `h² < 1`, `1 - zN_j` and
  `1 - 𝕊_pad` invertible: `b3ChainXX` is Hermitian and `nearSchur = b3ClosedX`.

The invertibility of `1 - 𝕊_pad` is the hypothesis `B3PadInvertible`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3LayerMean

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.Transmission.Bridge
open scoped ComplexConjugate ComplexOrder

/-!
## Abstract closing algebra
-/

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The padded closed scatterer `𝕊_pad = (1 - ΠᴴΠ)𝕊C(z)(1 - A) + ΠᴴA`. -/
def padScat (S A Pi : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (1 - Piᴴ * Pi) * S * closingMap S A Pi z * (1 - A) + Piᴴ * A

theorem compl_mul_self' {A : Matrix ι ι ℂ} (hAA : A * A = A) : (1 - A) * (1 - A) = 1 - A := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hAA]; simp

theorem compl_mul_A {A : Matrix ι ι ℂ} (hAA : A * A = A) : (1 - A) * A = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, hAA, sub_self]

theorem A_mul_compl {A : Matrix ι ι ℂ} (hAA : A * A = A) : A * (1 - A) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, hAA, sub_self]

/-- **The padded closed scatterer is unitary.** -/
theorem padScat_unitary {S A Pi : Matrix ι ι ℂ} {z : ℂ} (hS : Sᴴ * S = 1) (hAH : Aᴴ = A)
    (hAA : A * A = A) (hPi : Pi * Piᴴ = A) (hAPi : A * Pi = Pi) (hz : star z * z = 1)
    (hU : IsUnit (1 - z • closingN S A Pi).det) :
    (padScat S A Pi z)ᴴ * padScat S A Pi z = 1 := by
  set C := closingMap S A Pi z with hCdef
  set O := Piᴴ * Pi with hOdef
  set Y := C * (1 - A) with hYdef
  have hPiA : Piᴴ * A = Piᴴ := by rw [← hAH, ← conjTranspose_mul, hAPi]
  have hOH : Oᴴ = O := by rw [hOdef, conjTranspose_mul, conjTranspose_conjTranspose]
  have hOPi : (1 - O) * Piᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hOdef, Matrix.mul_assoc, hPi, hPiA, sub_self]
  have hOO : (1 - O)ᴴ * (1 - O) = 1 - O := by
    have hO2 : O * O = O := by
      rw [hOdef, Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPi, ← Matrix.mul_assoc, hPiA]
    rw [conjTranspose_sub, conjTranspose_one, hOH, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hO2]; simp
  have hcY : (1 - A) * Y = 1 - A := by
    rw [hYdef, ← Matrix.mul_assoc, compl_mul_closingMap hAA hAPi, compl_mul_self' hAA]
  have hfb : A * C = z • (Pi * S * C) := closingMap_feedback hAA hAPi hU
  have hPiSY : Pi * (S * Y) = star z • (A * Y) := by
    have : Pi * S * C = star z • (A * C) := by
      rw [hfb, smul_smul, hz, one_smul]
    rw [hYdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, this, Matrix.smul_mul, Matrix.mul_assoc]
  set K := (1 - O) * S * Y with hKdef
  have hK : (1 - O) * S * C * (1 - A) = K := by rw [hKdef, hYdef]; simp only [Matrix.mul_assoc]
  have hKK : Kᴴ * K = 1 - A := by
    have e1 : Kᴴ * K = Yᴴ * (Sᴴ * ((1 - O)ᴴ * (1 - O)) * S) * Y := by
      simp only [hKdef, conjTranspose_mul, Matrix.mul_assoc]
    have e2 : Sᴴ * (1 - O) * S = 1 - (Pi * S)ᴴ * (Pi * S) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hS, conjTranspose_mul, hOdef]
      simp only [Matrix.mul_assoc]
    have e3 : (Pi * S * Y)ᴴ * (Pi * S * Y) = (A * Y)ᴴ * (A * Y) := by
      rw [Matrix.mul_assoc Pi, hPiSY, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, star_star, mul_comm, hz, one_smul]
    have e4 : Yᴴ * Y = (1 - A) + (A * Y)ᴴ * (A * Y) := by
      have hsplit : Y = (1 - A) * Y + A * Y := by rw [Matrix.sub_mul, Matrix.one_mul]; abel
      have hx : ((1 - A) * Y)ᴴ * (A * Y) = 0 := by
        rw [hcY, conjTranspose_sub, conjTranspose_one, hAH, ← Matrix.mul_assoc,
          compl_mul_A hAA, Matrix.zero_mul]
      have hx' : (A * Y)ᴴ * ((1 - A) * Y) = 0 := by
        rw [← conjTranspose_conjTranspose ((1 - A) * Y), ← conjTranspose_mul, hx,
          conjTranspose_zero]
      have hd : ((1 - A) * Y)ᴴ * ((1 - A) * Y) = 1 - A := by
        rw [hcY, conjTranspose_sub, conjTranspose_one, hAH, compl_mul_self' hAA]
      calc Yᴴ * Y = ((1 - A) * Y + A * Y)ᴴ * ((1 - A) * Y + A * Y) := by rw [← hsplit]
        _ = ((1 - A) * Y)ᴴ * ((1 - A) * Y) + ((1 - A) * Y)ᴴ * (A * Y) +
            ((A * Y)ᴴ * ((1 - A) * Y) + (A * Y)ᴴ * (A * Y)) := by
          rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
        _ = (1 - A) + (A * Y)ᴴ * (A * Y) := by rw [hd, hx, hx']; abel
    rw [e1, hOO, e2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, e4]
    have e5 : Yᴴ * ((Pi * S)ᴴ * (Pi * S)) * Y = (Pi * S * Y)ᴴ * (Pi * S * Y) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [e5, e3]; abel
  have hPiO : Pi * (1 - O) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hOdef, ← Matrix.mul_assoc, hPi, hAPi, sub_self]
  have hLK : (Piᴴ * A)ᴴ * K = 0 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hKdef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pi (1 - O), hPiO]
    simp
  have hKL : Kᴴ * (Piᴴ * A) = 0 := by
    rw [← conjTranspose_conjTranspose (Kᴴ * (Piᴴ * A)), conjTranspose_mul,
      conjTranspose_conjTranspose, hLK, conjTranspose_zero]
  have hLL : (Piᴴ * A)ᴴ * (Piᴴ * A) = A := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hAH, Matrix.mul_assoc,
      ← Matrix.mul_assoc Pi, hPi, hAA, hAA]
  rw [padScat, hK, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hKK, hKL,
    hLK, hLL]
  abel

/-- **Cayley inverse of a unitary**: `z₀ - 2iη(1 - U)⁻¹` is Hermitian when `Im z₀ = η`. -/
theorem cayley_isHermitian {U : Matrix ι ι ℂ} (hU2 : U * Uᴴ = 1) (hD : IsUnit (1 - U).det)
    {z₀ : ℂ} {η : ℝ} (hz₀ : z₀.im = η) :
    (z₀ • (1 : Matrix ι ι ℂ) - (((2 * η : ℝ) : ℂ) * Complex.I) • (1 - U)⁻¹).IsHermitian := by
  set Wm := (1 - U)⁻¹ with hWdef
  set c : ℂ := ((2 * η : ℝ) : ℂ) * Complex.I with hcdef
  have hW1 : Wm * (1 - U) = 1 := nonsing_inv_mul _ hD
  have hWU : 1 - Wm = -(Wm * U) := by
    rw [Matrix.mul_sub, Matrix.mul_one] at hW1
    rw [← hW1]; abel
  have hWh : Wmᴴ = 1 - Wm := by
    rw [hWdef, conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_one]
    refine Matrix.inv_eq_left_inv ?_
    rw [hWU, Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hU2,
      Matrix.mul_one, neg_sub, ← hW1, Matrix.mul_sub, Matrix.mul_one]
  have hc : star c = -c := by
    simp only [hcdef, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]; ring
  have hz : star z₀ = z₀ - c := by
    have := Complex.sub_conj z₀
    rw [hz₀] at this
    simp only [Complex.star_def, hcdef]
    rw [← this]; ring
  rw [IsHermitian, conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, conjTranspose_one,
    hWh, hc, hz]
  module

end Abstract

/-!
## The path data
-/

variable {W : ℕ}

theorem lm_nearSel_mul_farEmbed (X : Matrix (Fin W) (Fin W) ℂ) : nearSel W * farEmbed X = 0 := by
  ext x y
  simp only [nearSel, farEmbed, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h1 h2 <;> simp_all

theorem lm_farEmbed_mul_nearSel_conj (X : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed X * (nearSel W)ᴴ = 0 := by
  ext x y; simp [nearSel, farEmbed, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem lm_nearSel_mul_conj : nearSel W * (nearSel W)ᴴ = 1 := by
  ext x y
  simp only [nearSel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [Finset.sum_eq_single (0, x)] <;> simp_all
  · rw [ite_eq_right hxy]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h1 : c = (0, x) <;> by_cases h2 : c = (0, y) <;> simp_all

/-- `b3PadScatter` is `padScat` of the path data. -/
theorem b3PadScatter_eq (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    B3.b3PadScatter b E s h W j ω z = padScat (scatteringMatrix b E W j ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω)) z := rfl

/-- **The near-block identity** `ι*𝕊_padι = 1 - 2iη R_cl`. -/
theorem nearSel_b3PadScatter (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    nearSel W * B3.b3PadScatter b E s h W j ω z * (nearSel W)ᴴ =
      1 - (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) • B3.closedNearR b E s h W j ω z := by
  set A := farEmbed (omittedProj b E h W (closeLen s W) ω)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) ω)
  set S := scatteringMatrix b E W j ω
  set C := physClosingMapAt b E s h W j ω z
  have hAA : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAPi : A * Pi = Pi := by rw [farEmbed_mul, omittedProj_mul_closingPairing]
  have hO : nearSel W * (1 - Piᴴ * Pi) = nearSel W := by
    rw [farEmbed_conjTranspose, farEmbed_mul, Matrix.mul_sub, Matrix.mul_one,
      lm_nearSel_mul_farEmbed, sub_zero]
  have hA : (1 - A) * (nearSel W)ᴴ = (nearSel W)ᴴ := by
    rw [Matrix.sub_mul, Matrix.one_mul, lm_farEmbed_mul_nearSel_conj, sub_zero]
  have hL : nearSel W * (Piᴴ * A) = 0 := by
    rw [farEmbed_conjTranspose, ← Matrix.mul_assoc, lm_nearSel_mul_farEmbed, Matrix.zero_mul]
  have hC : nearSel W * C * (nearSel W)ᴴ = 1 := by
    have hX : nearSel W * ((1 - z • closingN S A Pi)⁻¹ * (z • closingT S A Pi)) = 0 := by
      rw [← A_mul_closingX hAA hAPi, ← Matrix.mul_assoc, lm_nearSel_mul_farEmbed,
        Matrix.zero_mul]
    change nearSel W * closingMap S A Pi z * (nearSel W)ᴴ = 1
    rw [closingMap, Matrix.mul_add, hX, add_zero, Matrix.mul_assoc, hA, lm_nearSel_mul_conj]
  have e : nearSel W * B3.b3PadScatter b E s h W j ω z * (nearSel W)ᴴ =
      nearSel W * S * C * (nearSel W)ᴴ := by
    change nearSel W * ((1 - Piᴴ * Pi) * S * C * (1 - A) + Piᴴ * A) * (nearSel W)ᴴ = _
    rw [Matrix.mul_add, Matrix.add_mul, hL, Matrix.zero_mul, add_zero]
    simp only [← Matrix.mul_assoc, hO]
    rw [Matrix.mul_assoc _ (1 - A), hA]
  rw [e]
  change nearSel W * (1 - ((2 * etaZ b E : ℝ) * Complex.I) • boundaryResolvent b E W j ω) * C *
    (nearSel W)ᴴ = _
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, hC, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul]
  rfl

/-- `portBlock M 0 0 = ι*Mι`. -/
theorem portBlock_zero_zero_eq (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    portBlock M 0 0 = nearSel W * M * (nearSel W)ᴴ := by
  ext x y
  simp [portBlock, nearSel, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- **`nearSchur(b3ChainXX) = closedNearX`**, for a Hermitian chain state with `1 - 𝕊_pad`
invertible. -/
theorem nearSchur_b3ChainXX {b E s h : ℝ} {np W j : ℕ} {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hH : (B3.b3ChainXX b E s h W j y).IsHermitian)
    (hD : IsUnit (1 - B3.b3PadScatter b E s h W j y.1.1 (phase y.2)).det) :
    nearSchur (boundaryZ b E) (B3.b3ChainXX b E s h W j y) =
      B3.closedNearX b E s h W j y.1.1 (phase y.2) := by
  set U := B3.b3PadScatter b E s h W j y.1.1 (phase y.2)
  set XX := B3.b3ChainXX b E s h W j y
  set c : ℂ := ((2 * etaZ b E : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    have : ((2 * etaZ b E : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * etaZ b E ≠ 0)
    exact mul_ne_zero this Complex.I_ne_zero
  have hzim : 0 < (boundaryZ b E).im := hη
  have hres : twoPortResolvent b E XX = c⁻¹ • (1 - U) := by
    have e : boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - XX =
        c • (1 - U)⁻¹ := by
      change boundaryZ b E • 1 - (boundaryZ b E • 1 - c • (1 - U)⁻¹) = _
      abel
    rw [twoPortResolvent, e]
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul, mul_nonsing_inv _ hD, inv_mul_cancel₀ hc, one_smul]
  have hD11 : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1) :=
    BlockBand.Transmission.portPencil_isUnit _
      (BlockBand.SourceProcess.FullSource.portBlock_isHermitian hH 1) hzim
  have h00 := portBlock_twoPortResolvent_zero_zero b E XX hD11
  rw [hres, portBlock_zero_zero_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, lm_nearSel_mul_conj, nearSel_b3PadScatter, sub_sub_cancel,
    smul_smul, inv_mul_cancel₀ hc, one_smul] at h00
  have hX : IsUnit (BlockBand.Transmission.portPencil (nearSchur (boundaryZ b E) XX)
      (boundaryZ b E)) := by
    have hP := BlockBand.SourceProcess.FullSource.nearSchur_passive hzim hH
    apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
    rw [BlockBand.Transmission.matrixImaginaryPart_portPencil_general, sub_eq_add_neg]
    exact (Matrix.PosDef.one.smul hzim).add_posSemidef hP
  have hX' : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) -
      nearSchur (boundaryZ b E) XX) := hX
  rw [B3.closedNearX, h00, passiveResolvent, Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hX'), sub_sub_cancel]

/-- **The padded chain state is Hermitian with the closed near Schur matrix**, given the unitary
`𝕊_j`, `|z| = 1`, `h² < 1` and the invertibilities of `1 - zN_j` and `1 - 𝕊_pad`. -/
theorem b3ChainXX_good {b E s h : ℝ} {np W j : ℕ} (τ m : Fin np → ℝ) {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hh : h ^ 2 < 1)
    (hS : (scatteringMatrix b E W j y.1.1)ᴴ * scatteringMatrix b E W j y.1.1 = 1)
    (hU : IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W j y.1.1)
      (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det)
    (hD : IsUnit (1 - B3.b3PadScatter b E s h W j y.1.1 (phase y.2)).det) :
    (B3.b3ChainXX b E s h W j y).IsHermitian ∧
      nearSchur (boundaryZ b E) (B3.b3ChainXX b E s h W j y) =
        B3.b3ClosedX b E s h τ m W j y := by
  have hAH : (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))ᴴ =
      farEmbed (omittedProj b E h W (closeLen s W) y.1.1) := by
    rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAA : farEmbed (omittedProj b E h W (closeLen s W) y.1.1) *
      farEmbed (omittedProj b E h W (closeLen s W) y.1.1) =
        farEmbed (omittedProj b E h W (closeLen s W) y.1.1) := by
    rw [farEmbed_mul, omittedProj_mul_self]
  have hPi : farEmbed (closingPairing b E h W (closeLen s W) y.1.1) *
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))ᴴ =
        farEmbed (omittedProj b E h W (closeLen s W) y.1.1) := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have hAPi : farEmbed (omittedProj b E h W (closeLen s W) y.1.1) *
      farEmbed (closingPairing b E h W (closeLen s W) y.1.1) =
        farEmbed (closingPairing b E h W (closeLen s W) y.1.1) := by
    rw [farEmbed_mul, omittedProj_mul_closingPairing]
  have hz : star (phase y.2) * phase y.2 = 1 := by
    have h1 : ‖phase y.2‖ = 1 := by simp [phase, Complex.norm_exp_ofReal_mul_I]
    rw [Complex.star_def, Complex.conj_mul', h1]; simp
  have hunit := padScat_unitary hS hAH hAA hPi hAPi hz hU
  rw [← b3PadScatter_eq] at hunit
  have hunit2 := mul_eq_one_comm.mp hunit
  have hHerm : (B3.b3ChainXX b E s h W j y).IsHermitian :=
    cayley_isHermitian hunit2 hD (z₀ := boundaryZ b E) (η := etaZ b E) rfl
  exact ⟨hHerm, nearSchur_b3ChainXX hη hHerm hD⟩

end BlockBand.SourceProcess.PhysApprox.B3LayerMean
