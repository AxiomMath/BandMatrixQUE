module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanCurrent
public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm

/-!
# Reduction of `B3PadInvertible` to a phase-free path hypothesis

* `one_sub_padScat_eq_corner` (algebra): `1 - 𝕊_pad(z) = G + z·L(1 - zN)⁻¹T` with the
  **phase-free** `G = 1 - (1 - O)𝕊(1 - A) - ΠᴴA = 1 - 𝕊_pad(0)`, `L = -(1 - O)𝕊`, `T = Π𝕊(1 - A)`.
* Hence, by `ae_isUnit_corner` (a polynomial in the phase), `1 - 𝕊_pad(z)` is
  invertible for a.e. phase as soon as `G` is invertible; and `1 - zN` is invertible for a.e.
  phase by `ae_closedPhase_good`.
* **Hypothesis `B3PadZeroDet`** (phase-free): for a.e. path, `G_n` is invertible at every length
  `n ≥ n_s`. (`𝕊_pad(0)` is a contraction; an eigenvalue `1` needs a retained input `v` and an
  omitted `a` with `(1 - 𝕊)v = Πᴴa - a` and `Π𝕊v = 0`, a codimension-one condition on the path.)
* **`b3PadInvertible_of_zeroDet : B3PadZeroDet → B3PadInvertible`**.
* **`b3CayleyChain_of_zeroDet : B3PadZeroDet → B3PadTransport → B3CayleyChain`** and
  `b3ClosedChainPin_of_zeroDet` (using `b3ClosedCurrentFrame_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3LayerMean

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.PhysApprox.B3 BlockBand.SourceProcess.PhysApprox.ClosedForm
open BlockBand.Transmission.Bridge

variable {W np : ℕ}

/-!
## The corner form of `1 - 𝕊_pad(z)`
-/

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The phase-free part `G = 1 - 𝕊_pad(0)`. -/
def padZero (S A Pi : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  1 - (1 - Piᴴ * Pi) * S * (1 - A) - Piᴴ * A

theorem one_sub_padScat_eq_corner {S A Pi : Matrix ι ι ℂ} (z : ℂ) (hAA : A * A = A) :
    1 - padScat S A Pi z = padZero S A Pi + z • ((-((1 - Piᴴ * Pi) * S)) *
      (1 - z • closingN S A Pi)⁻¹ * closingT S A Pi) := by
  have e1 : (1 - Piᴴ * Pi) * S * closingMap S A Pi z * (1 - A) =
      (1 - Piᴴ * Pi) * S * (1 - A) +
        z • ((1 - Piᴴ * Pi) * S * (1 - z • closingN S A Pi)⁻¹ * closingT S A Pi) := by
    simp only [closingMap, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, compl_mul_self' hAA, closingT_mul_compl hAA]
  rw [padScat, e1, padZero]
  simp only [Matrix.neg_mul, smul_neg]
  abel

end Abstract

/-!
## Almost every phase
-/

theorem measurable_b3PadScatter (b E s h : ℝ) (n : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ => b3PadScatter b E s h W n y.1.1 (phase y.2) := by
  have hω : Measurable fun y : ProbedPath W np × ℝ => y.1.1 := measurable_fst.comp measurable_fst
  have hz : Measurable fun y : ProbedPath W np × ℝ => phase y.2 :=
    measurable_phase.comp measurable_snd
  have hS := (measurable_scatteringMatrix b E n).comp hω
  have hA := measurable_farEmbed ((measurable_omittedProj b E h (closeLen s W)).comp hω)
  have hP := measurable_farEmbed ((measurable_closingPairing b E h (closeLen s W)).comp hω)
  have hC := measurable_physClosingMapAt_comp b E s h n hω hz
  have hPh := measurable_matrix_conjTranspose' hP
  exact measurable_matrix_add (measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_matrix_mul' (measurable_matrix_sub measurable_const
      (measurable_matrix_mul' hPh hP)) hS) hC) (measurable_matrix_sub measurable_const hA))
    (measurable_matrix_mul' hPh hA)

/-- **Hypothesis `B3PadZeroDet`** (phase-free): `G_n = 1 - 𝕊_pad,n(0)` is a.s. invertible. -/
def B3PadZeroDet : Prop :=
  ∀ (b E : ℝ), 0 < b → b < 1 / 2 → -2 < E → E < 2 → ∀ (s h : ℝ), 0 < h → h < 1 →
    ∀ W : ℕ, 1 ≤ W → ∀ n, closeLen s W ≤ n → ∀ᵐ ω ∂growthPathLaw W b,
      IsUnit (padZero (scatteringMatrix b E W n ω)
        (farEmbed (omittedProj b E h W (closeLen s W) ω))
        (farEmbed (closingPairing b E h W (closeLen s W) ω))).det

/-- `1 - 𝕊_pad` is invertible for a.e. sample of the closed law, given the path hypothesis at `n`. -/
theorem ae_isUnit_one_sub_b3PadScatter (b E s h : ℝ) (n : ℕ)
    (h0 : ∀ᵐ ω ∂growthPathLaw W b,
      IsUnit (padZero (scatteringMatrix b E W n ω)
        (farEmbed (omittedProj b E h W (closeLen s W) ω))
        (farEmbed (closingPairing b E h W (closeLen s W) ω))).det) :
    ∀ᵐ y ∂closedLaw b W np, IsUnit (1 - b3PadScatter b E s h W n y.1.1 (phase y.2)).det := by
  have hq : Measure.QuasiMeasurePreserving (fun x : ProbedPath W np => x.1)
      (probedPathLaw W np b) (growthPathLaw W b) := Measure.quasiMeasurePreserving_fst
  have h1 : ∀ᵐ x ∂probedPathLaw W np b,
      IsUnit (padZero (scatteringMatrix b E W n x.1)
        (farEmbed (omittedProj b E h W (closeLen s W) x.1))
        (farEmbed (closingPairing b E h W (closeLen s W) x.1))).det :=
    hq.ae (p := fun ω => IsUnit (padZero (scatteringMatrix b E W n ω)
        (farEmbed (omittedProj b E h W (closeLen s W) ω))
        (farEmbed (closingPairing b E h W (closeLen s W) ω))).det) h0
  have hm : Measurable fun y : ProbedPath W np × ℝ =>
      (1 - b3PadScatter b E s h W n y.1.1 (phase y.2)).det :=
    measurable_det_comp (measurable_matrix_sub measurable_const
      (measurable_b3PadScatter b E s h n))
  have hs := hm (measurableSet_singleton 0).compl
  have key : ∀ᵐ y ∂closedLaw b W np,
      y ∈ (fun y : ProbedPath W np × ℝ =>
        (1 - b3PadScatter b E s h W n y.1.1 (phase y.2)).det) ⁻¹' {0}ᶜ := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).2 ?_
    filter_upwards [h1] with x hx
    have hAA : farEmbed (omittedProj b E h W (closeLen s W) x.1) *
        farEmbed (omittedProj b E h W (closeLen s W) x.1) =
          farEmbed (omittedProj b E h W (closeLen s W) x.1) := by
      rw [farEmbed_mul, omittedProj_mul_self]
    filter_upwards [ae_isUnit_corner _
      (-((1 - (farEmbed (closingPairing b E h W (closeLen s W) x.1))ᴴ *
          farEmbed (closingPairing b E h W (closeLen s W) x.1)) * scatteringMatrix b E W n x.1))
      (closingN (scatteringMatrix b E W n x.1)
        (farEmbed (omittedProj b E h W (closeLen s W) x.1))
        (farEmbed (closingPairing b E h W (closeLen s W) x.1)))
      (closingT (scatteringMatrix b E W n x.1)
        (farEmbed (omittedProj b E h W (closeLen s W) x.1))
        (farEmbed (closingPairing b E h W (closeLen s W) x.1))) hx] with θ hθ
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [b3PadScatter_eq, one_sub_padScat_eq_corner _ hAA]
    exact hθ.ne_zero
  filter_upwards [key] with y hy
  exact isUnit_iff_ne_zero.2 hy

/-- **`B3PadInvertible` from the phase-free hypothesis.** -/
theorem b3PadInvertible_of_zeroDet (h0 : B3PadZeroDet) : B3PadInvertible := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, -, -, hh0, hh1, -⟩ := hF
  filter_upwards [eventually_ge_atTop 1] with W hW n hn
  filter_upwards [ae_isUnit_one_sub_b3PadScatter (np := np) b E s h n
      (h0 b E hb0 hb hE1 hE2 s h hh0 hh1 W hW n hn),
    ae_closedPhase_good (W := W) (np := np) b E s h n] with y h1 h2
  exact ⟨isUnit_iff_ne_zero.2 h2.1, h1⟩

/-- **`B3CayleyChain` from the phase-free hypothesis and the transport hypothesis.** -/
theorem b3CayleyChain_of_zeroDet (h0 : B3PadZeroDet) (hT : B3PadTransport) : B3CayleyChain :=
  b3CayleyChain_of_pad (b3PadInvertible_of_zeroDet h0) hT b3ClosedCurrentFrame_holds

/-- **`B3ClosedChainPin` from the phase-free hypothesis and the transport hypothesis.** -/
theorem b3ClosedChainPin_of_zeroDet (h0 : B3PadZeroDet) (hT : B3PadTransport) :
    B3ClosedChainPin :=
  b3ClosedChainPin_of_cayley (b3CayleyChain_of_zeroDet h0 hT)

end BlockBand.SourceProcess.PhysApprox.B3LayerMean
