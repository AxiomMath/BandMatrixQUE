module

public import BlockBand.Transmission.DualBoundary.LawConv
public import BlockBand.Transmission.DualBoundary.Unique

/-!
# The boundary dual identity and the assembly of `DualBoundaryStartContract`

* **`boundaryDualLawValue_of`**: under `InteriorDualLawOne`, for every critical limit
  `IsTransmissionLimit b E κ P μ` (`0 < b < 1/2`, `−2 < E < 2`, absorption profile `κ`),
  every `t > 0` and every boundary start `IsDualStart ![x] ![y]` with `y < 1`, *every*
  boundary realization at `D₀ = transportD0 b E` has `dualTransform = E_P F_{x,y}(μ_t)`
  (the law of `truncDualState` is unique (`dualBoundaryStart_unique`), `dualTransform` depends
  only on it (`dualTransform_eq_of_map_eq`), and the lift's value is `dualTransform_lift_eq`).
* **`dualBoundaryStart_of (hInt : InteriorDualLawOne) : DualBoundaryStartContract`**:
  `exists_ := DualEntrance.dualBoundaryStart_exists`, `unique := dualBoundaryStart_unique`,
  `firstMoment := dualBoundaryStart_firstMoment` (all three unconditional), `law` from
  `boundaryDualLawValue_of` and `exists_` at `transportD0 b E > 0`.
* **`dualBoundaryStart_of_transmissionLaw`**: the same from `TransmissionLawContract`
  (through `interiorDualLawOne_of`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.DualLift
open scoped NNReal ENNReal

/-- **Every boundary realization has the value `E_P F_{x,y}(μ_t)`.** -/
theorem boundaryDualLawValue_of (hInt : InteriorDualLawOne) {b : ℝ} (hb : 0 < b)
    (hb2 : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {κ : ℝ → ℝ}
    (hκ : IsAbsorptionProfile κ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (hP : IsTransmissionLimit b E κ P μ) {t : ℝ}
    (ht : 0 < t) {x y : ℝ} (hxy : IsDualStart ![x] ![y]) (hy1 : y < 1) :
    BoundaryDualLawValue E κ t (transportD0 b E) ![x] ![y]
      (∫ ω, transmissionRatio ![x] ![y] (μ t ω) ∂P) := by
  intro Ω' m' 𝓖' P' N X Y h
  have hD0 := transportD0_pos hb hE1 hE2
  obtain ⟨F⟩ := nonempty_liftFamily hD0 (isLiftStart_of_dualStart hxy)
  have hB := isBoundaryDualProcess_lift hD0 hxy F
  rw [dualTransform_eq_of_map_eq E hκ.1 ht.le h hB
    (dualBoundaryStart_unique _ hD0 x y hxy _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hB)]
  exact dualTransform_lift_eq hInt hb hb2 hE1 hE2 hκ hP hxy hy1 F ht

/-- **The assembly, conditional on the interior `p = 1` transmission law.** -/
theorem dualBoundaryStart_of (hInt : InteriorDualLawOne) : DualBoundaryStartContract where
  exists_ := DualEntrance.dualBoundaryStart_exists
  unique := dualBoundaryStart_unique
  firstMoment := dualBoundaryStart_firstMoment
  law := fun _ hb hb2 _ hE1 hE2 _ hκ _ _ _ _ hP _ ht x y hxy hy1 =>
    ⟨DualEntrance.dualBoundaryStart_exists _ (transportD0_pos hb hE1 hE2) x y hxy,
      boundaryDualLawValue_of hInt hb hb2 hE1 hE2 hκ hP ht hxy hy1⟩

/-- **The assembly from the `TransmissionLawContract`.** -/
theorem dualBoundaryStart_of_transmissionLaw (h : TransmissionLawContract) :
    DualBoundaryStartContract :=
  dualBoundaryStart_of (interiorDualLawOne_of h)

end BlockBand.Transmission.DualBoundary
