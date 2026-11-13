module

public import BlockBand.SourceProcess.ComplexCoupled.SubDrift
public import BlockBand.SourceProcess.CoupledFrames.NativeSum
public import BlockBand.SourceProcess.CoupledFrames.ShiftMain
public import BlockBand.SourceProcess.ComplexConstruct.KBornLoc

/-!
# Complex weighted increments after a stopping time are Itô

* `isNativeItoProcess_cshift`: for a complex Itô process `A` (drift `b`, diffusion `σ`), an
  augmented stopping time `θ` and an `𝓕_θ`-measurable (unbounded) complex weight `ζ`, the process
  `ζ (A - A^θ)` is Itô with drift `1{θ < s} ζ b` and diffusion `1{θ < s} ζ σ`. Proof: real
  and imaginary parts of `ζ` and `isNativeItoProcess_shift`.
* `isNativeItoProcess_tRep`: the same for the finite weighted sums `tRep θ w A`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.CoupledFrames BlockBand.SourceProcess.ComplexConstruct

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]

/-- **Complex weighted increments after a stopping time.** -/
theorem isNativeItoProcess_cshift {A b : ℝ≥0 → DriverSample S κ → ℂ}
    {σ : κ → ℝ≥0 → DriverSample S κ → ℂ} (hA : IsNativeItoProcess μ A b σ)
    {θ : DriverSample S κ → WithTop ℝ≥0} (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ)
    {ζ : DriverSample S κ → ℂ} (hζ : StronglyMeasurable[hθ.measurableSpace] ζ) :
    IsNativeItoProcess μ (fun t x => ζ x * (A t x - stoppedProcess A θ t x))
      (fun t x => if θ x < (t : WithTop ℝ≥0) then ζ x * b t x else 0)
      (fun a t x => if θ x < (t : WithTop ℝ≥0) then ζ x * σ a t x else 0) := by
  have hre : StronglyMeasurable[hθ.measurableSpace] (fun x => (ζ x).re) :=
    Complex.continuous_re.comp_stronglyMeasurable hζ
  have him : StronglyMeasurable[hθ.measurableSpace] (fun x => (ζ x).im) :=
    Complex.continuous_im.comp_stronglyMeasurable hζ
  set L : ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℂ Complex.I
  have h1 := isNativeItoProcess_shift hA hθ hre
  have h2 := isNativeItoProcess_shift (hA.map_clm L) hθ him
  have h := isNativeItoProcess_add h1 h2
  have hL : ∀ z : ℂ, L z = Complex.I * z := fun z => by
    simp [L, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hsplit : ∀ (x : DriverSample S κ) (z : ℂ),
      (ζ x).re • z + (ζ x).im • (Complex.I * z) = ζ x * z := fun x z => by
    conv_rhs => rw [← Complex.re_add_im (ζ x)]
    simp only [Complex.real_smul]
    ring
  convert h using 1
  · funext t x
    simp only [shiftProc, stoppedProcess_eq_stopTime, hL, ← mul_sub, hsplit]
  · funext t x
    simp only [onAfter, hL]
    split_ifs
    · exact (hsplit x _).symm
    · simp
  · funext a t x
    simp only [onAfter, hL]
    split_ifs
    · exact (hsplit x _).symm
    · simp

variable {ι' : Type*} [Fintype ι']

/-- **Weighted sums of increments after a stopping time.** -/
theorem isNativeItoProcess_tRep {A b : ι' → ℝ≥0 → DriverSample S κ → ℂ}
    {σ : ι' → κ → ℝ≥0 → DriverSample S κ → ℂ} (hA : ∀ y, IsNativeItoProcess μ (A y) (b y) (σ y))
    {θ : DriverSample S κ → WithTop ℝ≥0} (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ)
    {w : ι' → DriverSample S κ → ℂ} (hw : ∀ y, StronglyMeasurable[hθ.measurableSpace] (w y)) :
    IsNativeItoProcess μ (tRep θ w A)
      (fun t x => ∑ y, if θ x < (t : WithTop ℝ≥0) then w y x * b y t x else 0)
      (fun a t x => ∑ y, if θ x < (t : WithTop ℝ≥0) then w y x * σ y a t x else 0) :=
  isNativeItoProcess_finsetSum Finset.univ fun y _ => isNativeItoProcess_cshift (hA y) hθ (hw y)

end BlockBand.SourceProcess.ComplexCoupled
