module

public import BlockBand.SourceProcess.ComplexCoupled.Shift
public import BlockBand.SourceProcess.ModelExist.TransDef
public import BlockBand.SourceProcess.ModelExist.TransAlg

/-!
# Born increments of an ambient process are Itô

* `bInc θ λ A e`: for an ambient complex coordinate family `A_{(x,x')}`, the born increment
  `Σ_{x,x'} conj(λ_y)_x (λ_z)_{x'} (A_{xx'} - A_{xx'}^{θ_y ∨ θ_z})` of the coordinate `e = (r,y,z)`.
  For `A = gramCompensated 𝒢` this is `bornRep`.
* `isNativeItoProcess_bInc`: it is Itô with the switched drift and diffusion
  `Σ 1{θ_e < s} bCoef (·)`.
* `ite_sum_eq_cf`: off the birth times the switched coefficients are the congruence coefficients
  `cf (bornL θ λ s)` of `Lᴴ (·) L`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.ModelExist BlockBand.SourceProcess.CoupledFrames

variable {Ω : Type*} {c c' : Type*} [Fintype c'] {ι' : Type*}

/-- The born increment of the coordinate `e`. -/
def bInc (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ) (A : ι' → c' → c' → ℝ≥0 → Ω → ℂ)
    (r : ι') (y z : c) (t : ℝ≥0) (ω : Ω) : ℂ :=
  ∑ x, ∑ x', bCoef lam (0, y, z) ω x x' * (A r x x' t ω - stoppedProcess (A r x x')
    (bTime θ (0, y, z)) t ω)

omit [Fintype c'] in
theorem bTime_fst (θ : c → Ω → ℝ≥0) (r : Fin 2) (y z : c) :
    bTime θ (r, y, z) = bTime θ (0, y, z) := rfl

omit [Fintype c'] in
theorem bCoef_fst (lam : c → Ω → c' → ℂ) (r : Fin 2) (y z : c) :
    bCoef lam (r, y, z) = bCoef lam (0, y, z) := rfl

theorem bornRep_eq_bInc (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ)
    (N : Fin 2 × c' × c' → ℝ≥0 → Ω → ℂ) (r : Fin 2) (y z : c) :
    bornRep θ lam N (r, y, z) = bInc θ lam (fun r x x' => N (r, x, x')) r y z := rfl

theorem bInc_zero (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ) (A : ι' → c' → c' → ℝ≥0 → Ω → ℂ)
    (r : ι') (y z : c) (ω : Ω) : bInc θ lam A r y z 0 ω = 0 := by
  have h0 : ∀ q : WithTop ℝ≥0, stopTime q 0 = 0 := fun q => le_antisymm (stopTime_le _ 0) zero_le
  simp [bInc, stoppedProcess_eq_stopTime, h0]

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]

/-- **Born increments are Itô.** -/
theorem isNativeItoProcess_bInc {θ : c → DriverSample S κ → ℝ≥0}
    {lam : c → DriverSample S κ → c' → ℂ}
    (hθ : ∀ y, Measurable[driverAugmented (κ := κ) μ 0] (θ y))
    (hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace] (lam y))
    {A β : ι' → c' → c' → ℝ≥0 → DriverSample S κ → ℂ}
    {σ : ι' → c' → c' → κ → ℝ≥0 → DriverSample S κ → ℂ}
    (hA : ∀ r x x', IsNativeItoProcess μ (A r x x') (β r x x') (σ r x x')) (r : ι') (y z : c) :
    IsNativeItoProcess μ (bInc θ lam A r y z)
      (fun t ω => ∑ x, ∑ x', if bTime θ (0, y, z) ω < (t : WithTop ℝ≥0) then
        bCoef lam (0, y, z) ω x x' * β r x x' t ω else 0)
      (fun a t ω => ∑ x, ∑ x', if bTime θ (0, y, z) ω < (t : WithTop ℝ≥0) then
        bCoef lam (0, y, z) ω x x' * σ r x x' a t ω else 0) :=
  isNativeItoProcess_finsetSum Finset.univ fun x _ =>
    isNativeItoProcess_finsetSum Finset.univ fun x' _ =>
      isNativeItoProcess_cshift (hA r x x') (isStoppingTime_bTime hθ (0, y, z))
        (stronglyMeasurable_bCoef hθ hlam (0, y, z) x x')

omit [Fintype c'] in
/-- The switched congruence coefficient off the birth time. -/
theorem cf_eq_ite_lt [Fintype c] (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ) (t : ℝ≥0) (ω : Ω)
    (y z : c) (x x' : c') (ht : (t : WithTop ℝ≥0) ≠ bTime θ (0, y, z) ω) :
    cf (bornL θ lam t ω) y z x x' =
      if bTime θ (0, y, z) ω < (t : WithTop ℝ≥0) then bCoef lam (0, y, z) ω x x' else 0 := by
  rw [cf_bornL θ lam t ω 0]
  by_cases h : bTime θ (0, y, z) ω < (t : WithTop ℝ≥0)
  · rw [ite_eq_left h.le, ite_eq_left h]
  · have h' : ¬ bTime θ (0, y, z) ω ≤ (t : WithTop ℝ≥0) := fun h' =>
      h (lt_of_le_of_ne h' (Ne.symm ht))
    rw [ite_eq_right h, ite_eq_right h']

/-- **Off the birth times, the switched sums are the congruence sums.** -/
theorem ite_sum_eq_cf [Fintype c] (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ) (t : ℝ≥0) (ω : Ω)
    (y z : c) (F : c' → c' → ℂ) (ht : (t : WithTop ℝ≥0) ≠ bTime θ (0, y, z) ω) :
    (∑ x, ∑ x', if bTime θ (0, y, z) ω < (t : WithTop ℝ≥0) then
        bCoef lam (0, y, z) ω x x' * F x x' else 0) =
      ∑ x, ∑ x', cf (bornL θ lam t ω) y z x x' * F x x' := by
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  rw [cf_eq_ite_lt θ lam t ω y z x x' ht]
  split_ifs <;> simp

omit [Fintype c'] in
/-- A time different from every birth time is different from every coordinate birth time. -/
theorem ne_bTime {θ : c → Ω → ℝ≥0} {t : ℝ≥0} {ω : Ω}
    (ht : ∀ y, (t : WithTop ℝ≥0) ≠ ((θ y ω : ℝ≥0) : WithTop ℝ≥0)) (r : Fin 2) (y z : c) :
    (t : WithTop ℝ≥0) ≠ bTime θ (r, y, z) ω := by
  unfold bTime
  rcases max_choice (θ y ω) (θ z ω) with h | h <;> rw [h]
  · exact ht y
  · exact ht z

end BlockBand.SourceProcess.ComplexCoupled
