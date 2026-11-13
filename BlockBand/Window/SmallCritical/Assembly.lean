module

public import BlockBand.Window.SmallCritical.Variance
public import BlockBand.Window.SmallCritical.Atoms

/-!
# The small-ratio critical theorem: assembly

`smallCritical_holds` proves `WindowAngular.SmallCriticalContract` from the window transfer
theorem and the mode bound (hypotheses `WindowTransferContract` and `ModeBoundContract`). The three
fields of the structure:

* the field `variance` (`smallCritical_variance`), uniform over `0 < τ ≤ 1`, `P ∈ 𝔏_{τ,b,E}`,
  spectral weights `w` and smooth `φ` with `‖φ - φ̄‖_∞ ≤ M`;
* the field `mode` (`smallCritical_mode`), uniform over `0 < τ ≤ T`, `P`, `w` and integers
  `m ≠ 0`;
* the field `diffuse` (below): a.s. every profile mark of the limit lies in `H^{-s}` for all
  `s > 0` (`sobolev_window_ae`) and has no atoms (`atoms_window_ae`), over the countable families of
  windows `windowWeight R` and exponents `1/(k+1)`.

Law: every critical subsequential marked limit `IsCriticalMarkedLimit τ b E hb hb' P`
(arbitrary realizations, critical sequence and strictly increasing subsequence); no
identification or uniqueness of the critical law is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.WindowAngular
open scoped ENNReal NNReal

/-- The diffuse clause of the small-ratio critical theorem: almost surely every profile mark of
the limit lies in `H^{-s}` for all `s > 0` and has no atoms. -/
theorem smallCritical_diffuse (hWT : WindowTransferContract)
    (hMode : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      ModeBoundContract b θ T hb hb') :
    ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), E ^ 2 < 4 →
      ∀ τ : ℝ, 0 < τ → ∀ P : ProbabilityMeasure MarkedPointMeasure,
        IsCriticalMarkedLimit τ b E hb hb' P →
        ∀ᵐ ξ ∂(P : Measure MarkedPointMeasure), ∀ x : MarkedSpectralSpace,
          ξ.marked.measure {x} ≠ 0 →
            (∀ σ : ℝ, 0 < σ → Summable (fun m : ℤ =>
              (1 + 4 * Real.pi ^ 2 * (m : ℝ) ^ 2) ^ (-σ) *
                ‖∫ r, fourier m r ∂(x.2 : Measure Torus)‖ ^ 2)) ∧
            ∀ r : Torus, (x.2 : Measure Torus) {r} = 0 := by
  intro b hb hb' E hE τ hτ P hP
  have hS : ∀ k R : ℕ, ∀ᵐ ξ ∂(P : Measure MarkedPointMeasure), ∀ x : MarkedSpectralSpace,
      ξ.marked.measure {x} ≠ 0 → |x.1| < R + 2 →
        Summable (fun m : ℤ => (1 + 4 * Real.pi ^ 2 * (m : ℝ) ^ 2) ^ (-(1 / ((k : ℝ) + 1))) *
          ‖∫ r, fourier m r ∂(x.2 : Measure Torus)‖ ^ 2) := fun k R =>
    sobolev_window_ae hWT hMode hE hτ hP R (by positivity)
      (by rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hA := fun R : ℕ => atoms_window_ae hWT hMode hE hτ hP R
  filter_upwards [ae_all_iff.2 fun k => ae_all_iff.2 fun R => hS k R, ae_all_iff.2 hA]
    with ξ hξS hξA x hx
  have hxR : |x.1| < (⌈|x.1|⌉₊ : ℝ) + 2 := by
    have := Nat.le_ceil |x.1|
    linarith
  refine ⟨fun σ hσ => ?_, hξA _ x hx hxR⟩
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hσ
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (hξS k _ x hx hxR)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le
  · have : 0 ≤ 4 * Real.pi ^ 2 * (m : ℝ) ^ 2 := by positivity
    linarith
  · linarith

/-- The small-ratio critical theorem (`WindowAngular.SmallCriticalContract`), from the window
transfer theorem and the mode bound only. -/
theorem smallCritical_holds (hWT : WindowTransferContract)
    (hMode : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      ModeBoundContract b θ T hb hb') :
    SmallCriticalContract where
  variance := smallCritical_variance hWT hMode
  mode := smallCritical_mode hWT hMode
  diffuse := smallCritical_diffuse hWT hMode

end BlockBand.Window.SmallCritical
