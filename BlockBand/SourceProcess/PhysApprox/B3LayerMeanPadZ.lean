module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanRetained
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanNear
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanCurrent

/-!
# The phase-padded Cayley state, a.s. invertible with no extra hypothesis

The padding of `b3PadScatter` is the decoupled reflection `ΠᴴA` with phase `1`; its a.s.
invertibility needs the hypothesis `B3PadZeroDet`. Here the padding carries the closing phase:
`𝕊'_pad = (1 - O)𝕊C(z)(1 - A) + zΠᴴA` (`b3PadScatterZ`), `𝕏'_pad = z_∂ - 2iη(1 - 𝕊'_pad)⁻¹`
(`b3ChainXXz`). The near rows are unchanged (`PΠᴴ = 0`), so nearSchur, separators, current and
near rows are those of `b3ChainXX`, and:

* `padScatZ_unitary`: `𝕊'_pad` is unitary (same hypotheses as `padScat_unitary`);
* `one_sub_padScatZ_eq_corner`: `1 - 𝕊'_pad(z) = R₀ + z(-ΠᴴA) + zL(1 - zN)⁻¹T`,
  `R₀ = 1 - (1 - O)𝕊(1 - A)`;
* **`ae_isUnit_one_sub_b3PadScatterZ`** (with no extra hypothesis): `R₀` is invertible for
  every unitary `𝕊` with `1 - 𝕊` invertible (`isUnit_one_sub_retained`), and a.s.
  `𝕊_n = 1 - 2iη(z_∂ - 𝕏_n)⁻¹` with `𝕏_n` Hermitian; then the affine corner lemma gives a.e. phase.
* **`b3CayleyChainZ_holds : B3PadTransportZ → B3CayleyChainZ`**, hence
  **`b3ClosedChainPin_of_z`** and **`b3ClosedChainNearPin_of_z`**;
  `b3CayleySepZ_holds : B3PadGrowthZ → B3CayleySepZ`.

The hypotheses `B3PadTransportZ` (frame transport by `b3ChainXXz`; it depends only on the near
rows, hence is the same statement as `B3PadTransport` up to the witness) and `B3PadGrowthZ` are
proved as `B3.b3PadTransportZ_holds` and `B3.b3PadGrowthZ_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3LayerMean

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ContractingWords (currentOf)
open BlockBand.SourceProcess.ClosedSummedProof (contrGram)
open BlockBand.SourceProcess.PhysApprox.B3 BlockBand.SourceProcess.PhysApprox.ClosedForm
open BlockBand.Transmission.Bridge
open scoped ComplexOrder

/-!
## Abstract
-/

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The phase-padded closed scatterer `(1 - ΠᴴΠ)𝕊C(z)(1 - A) + zΠᴴA`. -/
def padScatZ (S A Pi : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (1 - Piᴴ * Pi) * S * closingMap S A Pi z * (1 - A) + z • (Piᴴ * A)

theorem padScatZ_eq (S A Pi : Matrix ι ι ℂ) (z : ℂ) :
    padScatZ S A Pi z = padScat S A Pi z + (z - 1) • (Piᴴ * A) := by
  rw [padScatZ, padScat, sub_smul, one_smul]; abel

/-- **The phase-padded scatterer is unitary.** -/
theorem padScatZ_unitary {S A Pi : Matrix ι ι ℂ} {z : ℂ} (hS : Sᴴ * S = 1) (hAH : Aᴴ = A)
    (hAA : A * A = A) (hPi : Pi * Piᴴ = A) (hAPi : A * Pi = Pi) (hz : star z * z = 1)
    (hU : IsUnit (1 - z • closingN S A Pi).det) :
    (padScatZ S A Pi z)ᴴ * padScatZ S A Pi z = 1 := by
  set K := (1 - Piᴴ * Pi) * S * closingMap S A Pi z * (1 - A)
  set L := Piᴴ * A
  have h1 := padScat_unitary hS hAH hAA hPi hAPi hz hU
  have hPiA : Piᴴ * A = Piᴴ := by rw [← hAH, ← conjTranspose_mul, hAPi]
  have hLL : Lᴴ * L = A := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hAH, Matrix.mul_assoc,
      ← Matrix.mul_assoc Pi, hPi, hAA, hAA]
  have hKL : Kᴴ * L = 0 := by
    have hOPi : (1 - Piᴴ * Pi)ᴴ * Piᴴ = 0 := by
      rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPi, hPiA, sub_self]
    simp only [K, L, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - Piᴴ * Pi)ᴴ, hOPi]; simp
  have hKK : Kᴴ * K = 1 - A := by
    have e : (padScat S A Pi z)ᴴ * padScat S A Pi z = Kᴴ * K + Kᴴ * L + (Kᴴ * L)ᴴ + Lᴴ * L := by
      rw [padScat, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        conjTranspose_mul Kᴴ L, conjTranspose_conjTranspose]; abel
    rw [hKL, conjTranspose_zero, hLL, h1] at e
    rw [← sub_eq_zero]; rw [← sub_eq_zero] at e
    rw [show Kᴴ * K - (1 - A) = -(1 - (Kᴴ * K + 0 + 0 + A)) by abel, e, neg_zero]
  change (K + z • L)ᴴ * (K + z • L) = 1
  rw [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hKK, hKL,
    hz, one_smul, hLL]
  have hLK : Lᴴ * K = 0 := by
    rw [← conjTranspose_conjTranspose (Lᴴ * K), conjTranspose_mul, conjTranspose_conjTranspose,
      hKL, conjTranspose_zero]
  rw [hLK]; simp

theorem one_sub_padScatZ_eq_corner {S A Pi : Matrix ι ι ℂ} (z : ℂ) (hAA : A * A = A) :
    1 - padScatZ S A Pi z = (1 - (1 - Piᴴ * Pi) * S * (1 - A)) + z • (-(Piᴴ * A)) +
      z • ((-((1 - Piᴴ * Pi) * S)) * (1 - z • closingN S A Pi)⁻¹ * closingT S A Pi) := by
  have e1 : (1 - Piᴴ * Pi) * S * closingMap S A Pi z * (1 - A) =
      (1 - Piᴴ * Pi) * S * (1 - A) +
        z • ((1 - Piᴴ * Pi) * S * (1 - z • closingN S A Pi)⁻¹ * closingT S A Pi) := by
    simp only [closingMap, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, compl_mul_self' hAA, closingT_mul_compl hAA]
  rw [padScatZ, e1]
  simp only [Matrix.neg_mul, smul_neg]
  abel

end Abstract

/-!
## The path objects
-/

variable {W np K : ℕ}

/-- **The phase-padded closed scatterer** at length `j`. -/
def b3PadScatterZ (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  padScatZ (scatteringMatrix b E W j ω) (farEmbed (omittedProj b E h W (closeLen s W) ω))
    (farEmbed (closingPairing b E h W (closeLen s W) ω)) z

/-- **The phase-padded Cayley state** `z_∂ - 2iη(1 - 𝕊'_pad)⁻¹`. -/
def b3ChainXXz (b E s h : ℝ) {np : ℕ} (W j : ℕ) (y : ProbedPath W np × ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
    (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) • (1 - b3PadScatterZ b E s h W j y.1.1 (phase y.2))⁻¹

theorem nearSel_padding_zero (b E h : ℝ) (n : ℕ) (ω : GrowthPath W) (z : ℂ) :
    nearSel W * (z • ((farEmbed (closingPairing b E h W n ω))ᴴ *
      farEmbed (omittedProj b E h W n ω))) = 0 := by
  rw [Matrix.mul_smul, farEmbed_conjTranspose, ← Matrix.mul_assoc, lm_nearSel_mul_farEmbed,
    Matrix.zero_mul, smul_zero]

theorem nearPortProj_padding_zero (b E h : ℝ) (n : ℕ) (ω : GrowthPath W) (z : ℂ) :
    ClosedLimit.nearPortProj W * (z • ((farEmbed (closingPairing b E h W n ω))ᴴ *
      farEmbed (omittedProj b E h W n ω))) = 0 := by
  rw [Matrix.mul_smul, farEmbed_conjTranspose, ← Matrix.mul_assoc,
    B3Cur.nearPortProj_mul_farEmbed, Matrix.zero_mul, smul_zero]

theorem b3PadScatterZ_eq (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    b3PadScatterZ b E s h W j ω z = b3PadScatter b E s h W j ω z +
      (z • ((farEmbed (closingPairing b E h W (closeLen s W) ω))ᴴ *
        farEmbed (omittedProj b E h W (closeLen s W) ω)) -
      (farEmbed (closingPairing b E h W (closeLen s W) ω))ᴴ *
        farEmbed (omittedProj b E h W (closeLen s W) ω)) := by
  rw [b3PadScatterZ, padScatZ_eq, b3PadScatter_eq, sub_smul, one_smul]

theorem nearSel_b3PadScatterZ (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    nearSel W * b3PadScatterZ b E s h W j ω z * (nearSel W)ᴴ =
      1 - (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) • closedNearR b E s h W j ω z := by
  have h1 := nearSel_padding_zero (W := W) b E h (closeLen s W) ω z
  have h2 := nearSel_padding_zero (W := W) b E h (closeLen s W) ω 1
  rw [one_smul] at h2
  rw [b3PadScatterZ_eq, Matrix.mul_add, Matrix.mul_sub, h1, h2, sub_zero, add_zero,
    nearSel_b3PadScatter]

theorem nearPortProj_mul_b3PadScatterZ (b E s h : ℝ) (n : ℕ) (ω : GrowthPath W) (z : ℂ) :
    ClosedLimit.nearPortProj W * b3PadScatterZ b E s h W n ω z =
      ClosedLimit.nearPortProj W * scatteringMatrix b E W n ω *
        physClosingMapAt b E s h W n ω z *
        (1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) := by
  have h1 := nearPortProj_padding_zero (W := W) b E h (closeLen s W) ω z
  have h2 := nearPortProj_padding_zero (W := W) b E h (closeLen s W) ω 1
  rw [one_smul] at h2
  rw [b3PadScatterZ_eq, Matrix.mul_add, Matrix.mul_sub, h1, h2, sub_zero, add_zero,
    nearPortProj_mul_b3PadScatter]

/-!
## Almost-sure invertibility, with no extra hypothesis
-/

/-- `1 - 𝕊_n` is a.s. invertible (it is `2iη(z_∂ - 𝕏_n)⁻¹`, `𝕏_n` Hermitian). -/
theorem ae_isUnit_one_sub_scattering {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ n, IsUnit (1 - scatteringMatrix b E W n ω) := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [ae_growth_isHermitian W b, ae_isUnit_pathPencil_growth hb hW E] with ω hA hF n
  have hXX := pathSchur_isHermitian E n ω hA
  have hP : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      pathSchur E (pathAt W n ω)) := BlockBand.Transmission.portPencil_isUnit _ hXX hη
  have hc : (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    have hη' : 0 < etaZ b E := hη
    have : ((2 * etaZ b E : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * etaZ b E ≠ 0)
    exact mul_ne_zero this Complex.I_ne_zero
  have e : 1 - scatteringMatrix b E W n ω = (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
      (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        pathSchur E (pathAt W n ω))⁻¹ := by
    rw [scatteringMatrix, boundaryResolvent_eq b E n ω (hF n), twoPortResolvent, sub_sub_cancel]
  rw [e, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 hc)).mul
    (Matrix.isUnit_nonsing_inv_det_iff.2 ((Matrix.isUnit_iff_isUnit_det _).1 hP))

theorem measurable_b3PadScatterZ (b E s h : ℝ) (n : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ => b3PadScatterZ b E s h W n y.1.1 (phase y.2) := by
  have hz : Measurable fun y : ProbedPath W np × ℝ => phase y.2 :=
    measurable_phase.comp measurable_snd
  have hω : Measurable fun y : ProbedPath W np × ℝ => y.1.1 := measurable_fst.comp measurable_fst
  have hA := measurable_farEmbed ((measurable_omittedProj b E h (closeLen s W)).comp hω)
  have hP := measurable_farEmbed ((measurable_closingPairing b E h (closeLen s W)).comp hω)
  have e : (fun y : ProbedPath W np × ℝ => b3PadScatterZ b E s h W n y.1.1 (phase y.2)) =
      fun y => b3PadScatter b E s h W n y.1.1 (phase y.2) +
        (phase y.2 • ((farEmbed (closingPairing b E h W (closeLen s W) y.1.1))ᴴ *
          farEmbed (omittedProj b E h W (closeLen s W) y.1.1)) -
        (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))ᴴ *
          farEmbed (omittedProj b E h W (closeLen s W) y.1.1)) := by
    funext y; exact b3PadScatterZ_eq b E s h W n y.1.1 (phase y.2)
  rw [e]
  have hL := measurable_matrix_mul' (measurable_matrix_conjTranspose' hP) hA
  exact measurable_matrix_add (measurable_b3PadScatter b E s h n)
    (measurable_matrix_sub (measurable_matrix_cmul hz hL) hL)

/-- **`1 - 𝕊'_pad` is invertible for a.e. sample, at every length `n ≥ n_s`** (with no extra hypothesis). -/
theorem ae_isUnit_one_sub_b3PadScatterZ {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (s h : ℝ) (hh : h ^ 2 < 1) (hW : 1 ≤ W) (n : ℕ) :
    ∀ᵐ y ∂closedLaw b W np, IsUnit (1 - b3PadScatterZ b E s h W n y.1.1 (phase y.2)).det := by
  have h0 : ∀ᵐ ω ∂growthPathLaw W b,
      IsUnit (1 - (1 - (farEmbed (closingPairing b E h W (closeLen s W) ω))ᴴ *
          farEmbed (closingPairing b E h W (closeLen s W) ω)) * scatteringMatrix b E W n ω *
        (1 - farEmbed (omittedProj b E h W (closeLen s W) ω))).det := by
    filter_upwards [ae_scattering_unitary hb hE1 hE2 hW,
      ae_isUnit_one_sub_scattering hb hE1 hE2 hW] with ω hU h1
    set A := farEmbed (omittedProj b E h W (closeLen s W) ω)
    set Pi := farEmbed (closingPairing b E h W (closeLen s W) ω)
    have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
    have hAA : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
    have hPi : Pi * Piᴴ = A := by
      rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
    have hAPi : A * Pi = Pi := by rw [farEmbed_mul, omittedProj_mul_closingPairing]
    have hOH : (Piᴴ * Pi)ᴴ = Piᴴ * Pi := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
    have hOO : Piᴴ * Pi * (Piᴴ * Pi) = Piᴴ * Pi := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPi, ← Matrix.mul_assoc, ← hAH,
        ← conjTranspose_mul, hAPi]
    have hR := isUnit_one_sub_retained (mul_eq_one_comm.mp (hU n).1) hAH hAA hOH hOO (h1 n)
    exact (Matrix.isUnit_iff_isUnit_det _).1 hR
  have hq : Measure.QuasiMeasurePreserving (fun x : ProbedPath W np => x.1)
      (probedPathLaw W np b) (growthPathLaw W b) := Measure.quasiMeasurePreserving_fst
  have h1 := hq.ae (p := fun ω => IsUnit (1 - (1 - (farEmbed (closingPairing b E h W
      (closeLen s W) ω))ᴴ * farEmbed (closingPairing b E h W (closeLen s W) ω)) *
        scatteringMatrix b E W n ω * (1 - farEmbed (omittedProj b E h W (closeLen s W) ω))).det)
    h0
  have hm : Measurable fun y : ProbedPath W np × ℝ =>
      (1 - b3PadScatterZ b E s h W n y.1.1 (phase y.2)).det :=
    measurable_det_comp (measurable_matrix_sub measurable_const
      (measurable_b3PadScatterZ b E s h n))
  have hs := hm (measurableSet_singleton 0).compl
  have key : ∀ᵐ y ∂closedLaw b W np,
      y ∈ (fun y : ProbedPath W np × ℝ =>
        (1 - b3PadScatterZ b E s h W n y.1.1 (phase y.2)).det) ⁻¹' {0}ᶜ := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).2 ?_
    filter_upwards [h1] with x hx
    have hAA : farEmbed (omittedProj b E h W (closeLen s W) x.1) *
        farEmbed (omittedProj b E h W (closeLen s W) x.1) =
          farEmbed (omittedProj b E h W (closeLen s W) x.1) := by
      rw [farEmbed_mul, omittedProj_mul_self]
    filter_upwards [ae_isUnit_corner_affine _
      (-((farEmbed (closingPairing b E h W (closeLen s W) x.1))ᴴ *
        farEmbed (omittedProj b E h W (closeLen s W) x.1)))
      (-((1 - (farEmbed (closingPairing b E h W (closeLen s W) x.1))ᴴ *
          farEmbed (closingPairing b E h W (closeLen s W) x.1)) * scatteringMatrix b E W n x.1))
      (closingN (scatteringMatrix b E W n x.1)
        (farEmbed (omittedProj b E h W (closeLen s W) x.1))
        (farEmbed (closingPairing b E h W (closeLen s W) x.1)))
      (closingT (scatteringMatrix b E W n x.1)
        (farEmbed (omittedProj b E h W (closeLen s W) x.1))
        (farEmbed (closingPairing b E h W (closeLen s W) x.1))) hx] with θ hθ
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [b3PadScatterZ, one_sub_padScatZ_eq_corner _ hAA]
    exact hθ.ne_zero
  filter_upwards [key] with y hy
  exact isUnit_iff_ne_zero.2 hy

/-!
## The chain clauses for the phase-padded state
-/

theorem twoPortScattering_b3ChainXXz {b E s h : ℝ} {n : ℕ} {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hD : IsUnit (1 - b3PadScatterZ b E s h W n y.1.1 (phase y.2)).det) :
    twoPortScattering b E (b3ChainXXz b E s h W n y) =
      b3PadScatterZ b E s h W n y.1.1 (phase y.2) := by
  set U := b3PadScatterZ b E s h W n y.1.1 (phase y.2)
  set c : ℂ := ((2 * etaZ b E : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    have : ((2 * etaZ b E : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * etaZ b E ≠ 0)
    exact mul_ne_zero this Complex.I_ne_zero
  have hres : twoPortResolvent b E (b3ChainXXz b E s h W n y) = c⁻¹ • (1 - U) := by
    have e : boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        b3ChainXXz b E s h W n y = c • (1 - U)⁻¹ := by
      change boundaryZ b E • 1 - (boundaryZ b E • 1 - c • (1 - U)⁻¹) = _
      abel
    rw [twoPortResolvent, e]
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul, mul_nonsing_inv _ hD, inv_mul_cancel₀ hc, one_smul]
  change 1 - c • twoPortResolvent b E (b3ChainXXz b E s h W n y) = U
  rw [hres, smul_smul, mul_inv_cancel₀ hc, one_smul, sub_sub_cancel]

theorem b3ChainXXz_good {b E s h : ℝ} {n : ℕ} (τ m : Fin np → ℝ) {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hh : h ^ 2 < 1)
    (hS : (scatteringMatrix b E W n y.1.1)ᴴ * scatteringMatrix b E W n y.1.1 = 1)
    (hU : IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W n y.1.1)
      (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det)
    (hD : IsUnit (1 - b3PadScatterZ b E s h W n y.1.1 (phase y.2)).det) :
    (b3ChainXXz b E s h W n y).IsHermitian ∧
      nearSchur (boundaryZ b E) (b3ChainXXz b E s h W n y) = b3ClosedX b E s h τ m W n y := by
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) y.1.1)
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAA : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have hAPi : A * Pi = Pi := by rw [farEmbed_mul, omittedProj_mul_closingPairing]
  have hz : star (phase y.2) * phase y.2 = 1 := by
    have h1 : ‖phase y.2‖ = 1 := by simp [phase, Complex.norm_exp_ofReal_mul_I]
    rw [Complex.star_def, Complex.conj_mul', h1]; simp
  have hunit := padScatZ_unitary hS hAH hAA hPi hAPi hz hU
  have hunit2 := mul_eq_one_comm.mp hunit
  have hHerm : (b3ChainXXz b E s h W n y).IsHermitian :=
    cayley_isHermitian hunit2 hD (z₀ := boundaryZ b E) (η := etaZ b E) rfl
  refine ⟨hHerm, ?_⟩
  -- the near Schur matrix, as for `b3ChainXX`
  set U := b3PadScatterZ b E s h W n y.1.1 (phase y.2)
  set XX := b3ChainXXz b E s h W n y
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
      (BlockBand.SourceProcess.FullSource.portBlock_isHermitian hHerm 1) hzim
  have h00 := portBlock_twoPortResolvent_zero_zero b E XX hD11
  rw [hres, portBlock_zero_zero_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, lm_nearSel_mul_conj, nearSel_b3PadScatterZ, sub_sub_cancel,
    smul_smul, inv_mul_cancel₀ hc, one_smul] at h00
  have hX : IsUnit (BlockBand.Transmission.portPencil (nearSchur (boundaryZ b E) XX)
      (boundaryZ b E)) := by
    have hP := BlockBand.SourceProcess.FullSource.nearSchur_passive hzim hHerm
    apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
    rw [BlockBand.Transmission.matrixImaginaryPart_portPencil_general, sub_eq_add_neg]
    exact (Matrix.PosDef.one.smul hzim).add_posSemidef hP
  have hX' : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) -
      nearSchur (boundaryZ b E) XX) := hX
  rw [b3ClosedX, closedNearX, h00, passiveResolvent, Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hX'), sub_sub_cancel]

theorem b3SepAt_b3ChainXXz {b E s h : ℝ} (τ m : Fin np → ℝ) {n : ℕ}
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hD : IsUnit (1 - b3PadScatterZ b E s h W n y.1.1 (phase y.2)).det) :
    B3SepAt b E s h τ m W n Vs (b3ChainXXz b E s h W n y) y := by
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1)
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAP : (1 - A) * ClosedLimit.nearPortProj W = ClosedLimit.nearPortProj W := by
    rw [Matrix.sub_mul, Matrix.one_mul, farEmbed_mul_nearPortProj, sub_zero]
  have hPA : ClosedLimit.nearPortProj W * (1 - A) = ClosedLimit.nearPortProj W := by
    rw [Matrix.mul_sub, Matrix.mul_one, B3Cur.nearPortProj_mul_farEmbed, sub_zero]
  obtain ⟨h0, h1, h2, h3⟩ := sep_core (U := b3PadScatterZ b E s h W n y.1.1 (phase y.2))
    (V := b3ClosedFrameAt b E s h τ m W n Vs y) nearPortProj_conjTranspose hAH
    (nearPortProj_mul_b3PadScatterZ b E s h n y.1.1 (phase y.2))
    (A_mul_b3ClosedFrameAt b E s h τ m n Vs y) hAP hPA
  intro σ
  have hS := twoPortScattering_b3ChainXXz (s := s) (h := h) (n := n) (y := y) hη hD
  fin_cases σ
  · simp only [b3ContrSep, b3ClosedPS, contrSepOf, sepOf, hS]; exact h0
  · simp only [b3ContrSep, b3ClosedPS, contrSepOf, sepOf, hS]; exact h1
  · simp only [b3ContrSep, b3ClosedPS, contrSepOf, sepOf, hS]; exact h2
  · simp only [b3ContrSep, b3ClosedPS, contrSepOf, sepOf, hS]; exact h3

theorem contrGram_b3ChainXXz {b E s h : ℝ} (τ m : Fin np → ℝ) {n : ℕ}
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hD : IsUnit (1 - b3PadScatterZ b E s h W n y.1.1 (phase y.2)).det) :
    contrGram b E (b3ChainXXz b E s h W n y) (b3ClosedFrameAt b E s h τ m W n Vs y) =
      b3CovZ b E np τ m s h K W Vs n y := by
  have hsep := b3SepAt_b3ChainXXz τ m Vs hη hD
  have hsum : ∀ f : Separator → ℝ,
      ∑ σ ∈ ClosedSummedProof.contrSepSet, f σ = ∑ i : Fin 4, f (contrSepOf i) := by
    intro f
    simp [ClosedSummedProof.contrSepSet, contrSepOf, Fin.sum_univ_four, add_assoc]
  rw [contrGram, hsum, b3CovZ, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [b3ContrCoord, hsep σ]

theorem currentOf_b3ChainXXz {b E s h : ℝ} {n : ℕ} {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hD : IsUnit (1 - b3PadScatterZ b E s h W n y.1.1 (phase y.2)).det) :
    currentOf b E (b3ChainXXz b E s h W n y) =
      (ClosedLimit.nearPortProj W * scatteringMatrix b E W n y.1.1 *
          physClosingMapAt b E s h W n y.1.1 (phase y.2) *
          (1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1)))ᴴ *
        (ClosedLimit.nearPortProj W * scatteringMatrix b E W n y.1.1 *
          physClosingMapAt b E s h W n y.1.1 (phase y.2) *
          (1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1))) -
        ClosedLimit.nearPortProj W := by
  rw [← nearPortProj_mul_b3PadScatterZ]
  set U := b3PadScatterZ b E s h W n y.1.1 (phase y.2)
  rw [currentOf, twoPortScattering_b3ChainXXz hη hD]
  change Uᴴ * ClosedLimit.nearPortProj W * U - ClosedLimit.nearPortProj W =
    (ClosedLimit.nearPortProj W * U)ᴴ * (ClosedLimit.nearPortProj W * U) -
      ClosedLimit.nearPortProj W
  congr 1
  rw [conjTranspose_mul, nearPortProj_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (ClosedLimit.nearPortProj W) (ClosedLimit.nearPortProj W),
    nearPortProj_mul_self]

theorem nearSel_twoPortScattering_b3ChainXXz {b E s h : ℝ} (τ m : Fin np → ℝ) {n : ℕ}
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hD : IsUnit (1 - b3PadScatterZ b E s h W n y.1.1 (phase y.2)).det) :
    nearSel W * twoPortScattering b E (b3ChainXXz b E s h W n y) *
        b3ClosedFrameAt b E s h τ m W n Vs y =
      nearSel W * b3ClosedPS b E s h W n y.1.1 (phase y.2) *
        b3ClosedFrameAt b E s h τ m W n Vs y := by
  have hV : (1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1)) *
      b3ClosedFrameAt b E s h τ m W n Vs y = b3ClosedFrameAt b E s h τ m W n Vs y := by
    rw [Matrix.sub_mul, Matrix.one_mul, A_mul_b3ClosedFrameAt, sub_zero]
  rw [twoPortScattering_b3ChainXXz hη hD, ← nearSel_mul_nearPortProj,
    Matrix.mul_assoc (nearSel W), nearPortProj_mul_b3PadScatterZ, Matrix.mul_assoc,
    Matrix.mul_assoc, hV]
  simp only [b3ClosedPS, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (ClosedLimit.nearPortProj W) (ClosedLimit.nearPortProj W),
    nearPortProj_mul_self]

theorem measurable_b3ChainXXz (b E s h : ℝ) (n : ℕ) :
    Measurable (b3ChainXXz (np := np) b E s h W n) :=
  measurable_matrix_sub measurable_const (measurable_matrix_cmul measurable_const
    (measurable_matrix_inv.comp (measurable_matrix_sub measurable_const
      (measurable_b3PadScatterZ b E s h n))))

theorem b3ChainXXz_b3Ext {b E s h : ℝ} {n j : ℕ} (hs : closeLen s W ≤ n) (hnj : n ≤ j)
    (y : ProbedPath W np × ℝ) :
    b3ChainXXz b E s h W n (b3Ext W j y) = b3ChainXXz b E s h W n y := by
  simp only [b3Ext, b3ChainXXz, b3PadScatterZ, padScatZ,
    ClosedSumProof.scatteringMatrix_extPast hnj,
    Modul.omittedProj_extPast b E h (hs.trans hnj),
    Modul.closingPairing_extPast b E h (hs.trans hnj)]

/-!
## The hypotheses and the reductions
-/

/-- **Hypothesis `B3PadTransportZ`** (LayerK): the closed frame is transported by `b3ChainXXz`. -/
def B3PadTransportZ : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        b3ClosedFrameAt b E s h τ m W (j + 1) (Vs W) y =
          (freshTransport b E (b3ChainXXz b E s h W j y) (freshSample W j y.1.1))ᴴ *
            b3ClosedFrameAt b E s h τ m W j (Vs W) y

/-- **Hypothesis `B3PadGrowthZ`** (LayerK): `b3ChainXXz` grows by the fresh Schur step. -/
def B3PadGrowthZ : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        b3ChainXXz b E s h W (j + 1) y =
          freshTwoPortSchur E (b3ChainXXz b E s h W j y) (freshSample W j y.1.1)

/-- The chain property of `b3ChainXXz` (`B3CayleyChain` for the phase-padded state). -/
def B3CayleyChainZ : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      B3ClosedChainAt b E s h τ m R W j (Vs W) (b3ChainXXz b E s h W j) 1

/-- The separator property of `b3ChainXXz` (`B3CayleySep` for the phase-padded state). -/
def B3CayleySepZ : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        B3SepAt b E s h τ m W j (Vs W) (b3ChainXXz b E s h W j y) y ∧
        b3ChainXXz b E s h W (j + 1) y =
          freshTwoPortSchur E (b3ChainXXz b E s h W j y) (freshSample W j y.1.1) ∧
        B3SepAt b E s h τ m W (j + 1) (Vs W) (b3ChainXXz b E s h W (j + 1) y) y

/-- **`B3CayleyChainZ` from the transport hypothesis alone.** -/
theorem b3CayleyChainZ_holds (hT : B3PadTransportZ) : B3CayleyChainZ := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb, hE1, hE2, hη, hh⟩ := frameDomain_facts hF
  filter_upwards [hT b E np τ m T s h K Vs hF R,
    b3ClosedCurrentFrame_holds b E np τ m T s h K Vs hF R, eventually_ge_atTop 1] with
    W hTW hJW hW j hj
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
  refine ⟨measurable_b3ChainXXz b E s h j, fun y => b3ChainXXz_b3Ext hjc le_rfl y, ?_⟩
  filter_upwards [ae_isUnit_one_sub_b3PadScatterZ (np := np) hb hE1 hE2 s h hh hW j,
    ae_closedPhase_good (W := W) (np := np) b E s h j, hTW j hj, hJW j hj,
    ae_closed_scattering_unitary hb hE1 hE2 hW] with y hDy hPy hTy hJy hSy hyA
  obtain ⟨hHerm, hNS⟩ := b3ChainXXz_good τ m hη hh (hSy j) (isUnit_iff_ne_zero.2 hPy.1) hDy
  refine ⟨hHerm, hNS, hTy hyA, ?_, ?_⟩
  · rw [currentOf_b3ChainXXz hη hDy]; exact hJy hyA
  · rw [contrGram_b3ChainXXz τ m (Vs W) hη hDy, one_mul]

/-- **`B3CayleySepZ` from the growth hypothesis alone.** -/
theorem b3CayleySepZ_holds (hG : B3PadGrowthZ) : B3CayleySepZ := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb, hE1, hE2, hη, hh⟩ := frameDomain_facts hF
  filter_upwards [hG b E np τ m T s h K Vs hF R, eventually_ge_atTop 1] with W hGW hW j hj
  filter_upwards [ae_isUnit_one_sub_b3PadScatterZ (np := np) hb hE1 hE2 s h hh hW j,
    ae_isUnit_one_sub_b3PadScatterZ (np := np) hb hE1 hE2 s h hh hW (j + 1), hGW j hj] with
    y h0 h1 hg hyA
  exact ⟨b3SepAt_b3ChainXXz τ m (Vs W) hη h0, hg hyA, b3SepAt_b3ChainXXz τ m (Vs W) hη h1⟩

/-- **`B3ClosedChainPin` from the transport hypothesis alone** (phase-padded witness). -/
theorem b3ClosedChainPin_of_z (hT : B3PadTransportZ) : B3ClosedChainPin := by
  intro b E np τ m T s h K Vs hF R
  exact ⟨1, zero_le_one, (b3CayleyChainZ_holds hT b E np τ m T s h K Vs hF R).mono
    fun W hW j hj => ⟨_, hW j hj⟩⟩

/-- **`B3ClosedChainNearPin` from the transport hypothesis alone** (phase-padded witness). -/
theorem b3ClosedChainNearPin_of_z (hT : B3PadTransportZ) : B3ClosedChainNearPin := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb, hE1, hE2, hη, hh⟩ := frameDomain_facts hF
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [b3CayleyChainZ_holds hT b E np τ m T s h K Vs hF R,
    eventually_ge_atTop 1] with W hCW hW j hj
  refine ⟨b3ChainXXz b E s h W j, hCW j hj, ?_⟩
  filter_upwards [ae_isUnit_one_sub_b3PadScatterZ (np := np) hb hE1 hE2 s h hh hW j] with y hy _
  exact nearSel_twoPortScattering_b3ChainXXz τ m (Vs W) hη hy

end BlockBand.SourceProcess.PhysApprox.B3LayerMean
