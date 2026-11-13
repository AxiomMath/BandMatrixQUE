module

public import BlockBand.Palm.ReferenceFlowAssembly
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Main

/-!
# Weak continuity of the kernel law: the statement

* `RefKernelLawContinuity N`: the kernel law depends continuously on the coefficients, in the weak
  topology, along uniformly convergent sequences of admissible coefficients. It is proved as
  `refKernelLawContinuity`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory Set Filter Topology
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow)
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Palm.ReferenceFlow
open scoped NNReal

variable {N : ℕ}

/-- The coefficient hypotheses of `LinearRotationFlowContract` on `[a, c]`. -/
def Admissible (a c : ℝ) (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) : Prop :=
  ContinuousOn r (Icc a c) ∧ ContinuousOn κ (Icc a c) ∧ (∀ x k l, r x k l = r x l k) ∧
    (∀ x k l, 0 ≤ r x k l) ∧ ∀ x k, 0 ≤ κ x k

open Classical in

/-- One fixed reflected rotation flow on `DriverSample Unit (RotIdx N)`, started at `a`, for the
coefficients `(r, κ)` on `[a, u]`. It is the constant `1` if `a ≤ u` or admissibility fails. -/
def canonFlow (a u : ℝ) (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) :
    ℝ≥0 → DriverSample Unit (RotIdx N) → Matrix (Fin N) (Fin N) ℂ :=
  if h : a ≤ u ∧ Admissible a u r κ then
    Classical.choose (exists_reflectedFlow
      (BlockBand.SourceProcess.Stochastic.RotationFlow.linearRotationFlowContract_holds N)
      (Measure.dirac ()) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
  else fun _ _ => 1

/-- `canonFlow` is a reflected rotation flow when the hypotheses hold. -/
theorem canonFlow_isRotationFlow {a u : ℝ} {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ}
    (hau : a ≤ u) (h : Admissible a u r κ) :
    IsRotationFlow (Measure.dirac ()) (reflectRate a u r) (reflectDamp a u κ) a u a
      (canonFlow a u r κ) := by
  have hh : a ≤ u ∧ Admissible a u r κ := ⟨hau, h⟩
  rw [canonFlow, dite_eq_left_of_eq_true (eq_true hh)]
  exact Classical.choose_spec (exists_reflectedFlow
    (BlockBand.SourceProcess.Stochastic.RotationFlow.linearRotationFlowContract_holds N)
    (Measure.dirac ()) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2)

/-- The law of the reference kernel `K_s = (𝓝_{u−s})ᴴ` of `canonFlow` with terminal time `u`. -/
def refKernelLaw (a u s : ℝ) (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) :
    Measure (Matrix (Fin N) (Fin N) ℂ) :=
  (driverLaw (κ := RotIdx N) (Measure.dirac ())).map (refKernel u (canonFlow a u r κ) s)

/-- Along a sequence of admissible coefficients converging uniformly on `[a, u]`, the kernel laws
converge weakly, tested against bounded continuous functions. -/
def RefKernelLawContinuity (N : ℕ) : Prop :=
  ∀ (a u s : ℝ), a ≤ u → s ∈ Icc a u →
  ∀ (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (rn : ℕ → ℝ → Fin N → Fin N → ℝ)
    (κn : ℕ → ℝ → Fin N → ℝ),
    Admissible a u r κ → (∀ n, Admissible a u (rn n) (κn n)) →
    TendstoUniformlyOn (fun n x => (rn n x, κn n x)) (fun x => (r x, κ x)) atTop (Icc a u) →
    ∀ φ : Matrix (Fin N) (Fin N) ℂ → ℝ, Continuous φ → (∃ C, ∀ M, |φ M| ≤ C) →
      Tendsto (fun n => ∫ M, φ M ∂refKernelLaw a u s (rn n) (κn n)) atTop
        (𝓝 (∫ M, φ M ∂refKernelLaw a u s r κ))

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
