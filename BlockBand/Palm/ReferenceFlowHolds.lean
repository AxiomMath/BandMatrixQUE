module

public import BlockBand.Palm.ReferenceFlowAssembly
public import BlockBand.Palm.ReferenceFlowContraction
public import BlockBand.Palm.RelativeLocalizationHolds

/-!
# Finite speed of the reference kernel

The kernel contraction of the reflected rotation flow, and the finite-speed bound for the
reference kernel `K_s` obtained from the mass identity `E|(K_s)_{kj}|²` and the finite-speed
estimate of the relative localization theorem.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Set Filter Matrix BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow LinearRotationFlowContract
  massGenerator)
open BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic
open BlockBand.Palm.RelativeLocalization.StochasticBridge
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobeniusBorelSpace

variable {N : ℕ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c : ℝ}
  {𝓝 : ℝ≥0 → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}

/-- **Contraction of the reference kernel**, from the Itô product rule. -/
theorem kernelContracts_of
    (hProd : ItoProductRuleFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ)
      (Matrix (Fin N) (Fin N) ℂ) (Matrix (Fin N) (Fin N) ℂ))
    (hac : a ≤ c) (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l)
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝) :
    KernelContracts μ κ a c (refKernel c 𝓝) := by
  intro b hb
  have h := rotationFlow_contraction_conjTranspose hProd hac (continuousOn_reflect hr)
    (continuousOn_reflect hκ) (fun _ k l => hrs _ k l) (fun _ k l => hr0 _ k l) h𝓝 b
    (fun x hx k => hb _ (mapsTo_reflect hx) k)
  filter_upwards [h] with y hy s hs v
  have hv := hy (c - s).toNNReal v
  rwa [Real.coe_toNNReal _ (sub_nonneg.2 hs.2)] at hv

/-- `E_aux Σ_j w_j |(K_s)_{kj}|² = Σ_j w_j E_aux |(K_s)_{kj}|²` for a reference flow. -/
theorem integral_sum_kernel {K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}
    (hKL : IsReferenceFlow μ r κ a c K L) (hκ0 : ∀ x k, 0 ≤ κ x k) {s : ℝ} (hs : s ∈ Icc a c)
    (k : Fin N) (w : Fin N → ℝ) :
    ∫ y, ∑ j, w j * ‖K s y k j‖ ^ 2 ∂driverLaw (κ := RotIdx N) μ =
      ∑ j, w j * ∫ y, ‖K s y k j‖ ^ 2 ∂driverLaw (κ := RotIdx N) μ := by
  have hb : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ j, ‖K s y k j‖ ≤ 1 := by
    filter_upwards [hKL.contraction 0 (fun x _ k => hκ0 x k)] with y hy j
    exact norm_entry_le_of_contraction (fun v => by simpa using hy s hs v) k j
  have hi : ∀ j, Integrable (fun y => ‖K s y k j‖ ^ 2) (driverLaw (κ := RotIdx N) μ) := by
    intro j
    have hm : Measurable fun y => ‖K s y k j‖ ^ 2 :=
      ((continuous_norm.pow 2).measurable).comp
        ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp (hKL.measurable_kernel s)))
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards [hb] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hy j, norm_nonneg (K s y k j)]
  rw [integral_finsetSum _ fun j _ => (hi j).const_mul (w j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- The mass identity combined with the reference finite-speed estimate, for every reference flow of
the path. -/
theorem referenceKernelFiniteSpeed_of (hRL : RelativeLocalizationContract) :
    ReferenceKernelFiniteSpeedStatement := by
  intro A c r₀ s₀ v₀ hfc b₀ hb₀ Cw D
  obtain ⟨N₀, hN₀⟩ := hRL.reference_finite_speed A c r₀ s₀ v₀ hfc b₀ hb₀ Cw D
  refine ⟨N₀, fun N hN F E hF => ?_⟩
  intro t a ℓ w S _ μ _
  refine (measure_mono ?_).trans (hN₀ N hN F E hF)
  rintro ω ⟨k, hk, K, L, hKL, hbig⟩
  refine ⟨k, hk, fun s k j => ∫ y, ‖K s y k j‖ ^ 2 ∂driverLaw (κ := RotIdx N) μ, ?_, ?_⟩
  · rw [referenceGenerator_eq_massGenerator]
    exact hKL.mass
  · refine hbig.trans_eq (setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_)
    rw [integral_sum_kernel hKL (refDamping_nonneg F a b₀ ω ℓ) hs k]

/-- `ReferenceKernelFiniteSpeedStatement`, through `relativeLocalization_holds`. -/
theorem referenceKernelFiniteSpeed_holds (hIto : ∀ N, SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N, DysonBrownianMotion N)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    ReferenceKernelFiniteSpeedStatement :=
  referenceKernelFiniteSpeed_of
    (BlockBand.Palm.RelativeLocalization.relativeLocalization_holds hIto hStop hDBM hLp hIBP)

end BlockBand.Palm.ReferenceFlow
