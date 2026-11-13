module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Backward
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The linear rotation flow: `LinearRotationFlowContract`

Measure: `driverLaw μ` on `DriverSample S ((Fin N × Fin N) × Fin 2)` (any measurable `S : Type`,
probability `μ`); filtration: the null-augmented `driverAugmented μ`; matrices with the
Frobenius norm. Coefficients: `r` continuous, symmetric, `≥ 0` and `κ` continuous, `≥ 0` on
`[a,c]`, read at the clamped time.

| Clause | Theorem | Proof |
|---|---|---|
| existence | `exists_isRotationFlow` | time-dependent Picard iteration, radial truncation, contraction |
| uniqueness | `isRotationFlow_unique` | Gronwall comparison |
| forward mass equation | `forwardMassSolution_of_isRotationFlow` | second-moment identity |
| backward propagator | `backwardPropagator_of_isRotationFlow` | `backward_of_forward` |

Dependencies: the SDE toolkit (Picard space, Gronwall comparison
`stoppedProcess_ae_eq_of_lipschitz`, horizon gluing), the continuous stopped integral
(`nativeAdaptedLimit`), the Itô product rule `ItoNative.itoProductRuleFor_holds`, a
radial retraction, and Frobenius-norm helpers.
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open BlockBand.Internal.Contracts.TransmissionFlow

/-- **`LinearRotationFlowContract N` holds** for every `N`. -/
theorem linearRotationFlowContract_holds (N : ℕ) : LinearRotationFlowContract N := by
  intro S _ μ _ r κ a c hac hrc hκc hs hr hk
  exact ⟨fun s _ => exists_isRotationFlow hac hrc hκc hs hr hk s,
    fun s _ M M' hM hM' => isRotationFlow_unique hac hrc hκc hs hr hk hM hM',
    fun s hsI M hM v₀ => forwardMassSolution_of_isRotationFlow hac hrc hκc hs hr hk hsI hM v₀,
    fun Mf hMf => backwardPropagator_of_isRotationFlow hac hrc hκc hs hr hk Mf hMf⟩

end BlockBand.SourceProcess.Stochastic.RotationFlow
