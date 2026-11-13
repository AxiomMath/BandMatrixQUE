module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Analysis.Convex.Mul

/-!
# Conditional expectation tools for the martingale part of `tight`

* `integral_mul_condExp`: `∫ Z E[f|m] = ∫ Z f` for `m`-measurable `Z` with `Zf` integrable;
  `integral_mul_sub_condExp`: `∫ Z (f - E[f|m]) = 0`.
* `condExp_pow_le` (conditional Jensen, even powers): `E[d|m]ⁿ ≤ E[dⁿ|m]` a.e.;
  `integrable_condExp_pow`.
* `integral_mul_sq_sub_condExp_le`: `∫ Y (d - E[d|m])² ≤ ∫ Y d²` for bounded `m`-measurable
  `Y ≥ 0` (conditional variance `≤` conditional second moment).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory Set

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem integrable_of_norm_le {f g : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : Integrable g μ) (h : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ g ω) : Integrable f μ :=
  Integrable.mono' hg hf h

/-- **Pull-out, integral form**: `∫ Z E[f|m] = ∫ Z f`. -/
theorem integral_mul_condExp (hm : m ≤ m0) [IsFiniteMeasure μ] {Z f : Ω → ℝ}
    (hZ : StronglyMeasurable[m] Z) (hZf : Integrable (fun ω => Z ω * f ω) μ)
    (hf : Integrable f μ) :
    ∫ ω, Z ω * μ[f | m] ω ∂μ = ∫ ω, Z ω * f ω ∂μ := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have h := condExp_mul_of_stronglyMeasurable_left (μ := μ) hZ hZf hf
  rw [← integral_condExp hm (f := fun ω => Z ω * f ω)]
  exact (integral_congr_ae h).symm

theorem integrable_mul_condExp {Z f : Ω → ℝ}
    (hZ : StronglyMeasurable[m] Z) (hZf : Integrable (fun ω => Z ω * f ω) μ)
    (hf : Integrable f μ) : Integrable (fun ω => Z ω * μ[f | m] ω) μ :=
  integrable_condExp.congr (condExp_mul_of_stronglyMeasurable_left (μ := μ) hZ hZf hf)

/-- `∫ Z (f - E[f|m]) = 0`. -/
theorem integral_mul_sub_condExp (hm : m ≤ m0) [IsFiniteMeasure μ] {Z f : Ω → ℝ}
    (hZ : StronglyMeasurable[m] Z) (hZf : Integrable (fun ω => Z ω * f ω) μ)
    (hf : Integrable f μ) :
    ∫ ω, Z ω * (f ω - μ[f | m] ω) ∂μ = 0 := by
  simp only [mul_sub]
  rw [integral_sub hZf (integrable_mul_condExp hZ hZf hf), integral_mul_condExp hm hZ hZf hf,
    sub_self]

/-- **Conditional Jensen for even powers**: `E[d|m]ⁿ ≤ E[dⁿ|m]` a.e. -/
theorem condExp_pow_le (hm : m ≤ m0) [IsFiniteMeasure μ] {d : Ω → ℝ} {n : ℕ} (hn : Even n)
    (hd : Integrable d μ) (hdn : Integrable (fun ω => d ω ^ n) μ) :
    (fun ω => μ[d | m] ω ^ n) ≤ᵐ[μ] μ[fun ω => d ω ^ n | m] := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  exact ConvexOn.map_condExp_le_univ (φ := fun x : ℝ => x ^ n) hm (hn.convexOn_pow)
    (continuous_pow n).lowerSemicontinuous hd hdn

theorem integrable_condExp_pow (hm : m ≤ m0) [IsFiniteMeasure μ] {d : Ω → ℝ} {n : ℕ}
    (hn : Even n) (hd : Integrable d μ) (hdn : Integrable (fun ω => d ω ^ n) μ) :
    Integrable (fun ω => μ[d | m] ω ^ n) μ := by
  refine integrable_of_norm_le ?_ (integrable_condExp (m := m) (f := fun ω => d ω ^ n)) ?_
  · exact ((stronglyMeasurable_condExp.mono hm).pow n).aestronglyMeasurable
  · filter_upwards [condExp_pow_le hm hn hd hdn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hn.pow_nonneg _)]
    exact hω

theorem integral_condExp_pow_le (hm : m ≤ m0) [IsFiniteMeasure μ] {d : Ω → ℝ} {n : ℕ}
    (hn : Even n) (hd : Integrable d μ) (hdn : Integrable (fun ω => d ω ^ n) μ) :
    ∫ ω, μ[d | m] ω ^ n ∂μ ≤ ∫ ω, d ω ^ n ∂μ := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  calc ∫ ω, μ[d | m] ω ^ n ∂μ ≤ ∫ ω, μ[fun ω => d ω ^ n | m] ω ∂μ :=
        integral_mono_ae (integrable_condExp_pow hm hn hd hdn) integrable_condExp
          (condExp_pow_le hm hn hd hdn)
    _ = ∫ ω, d ω ^ n ∂μ := integral_condExp hm

/-- `|xy| ≤ (x² + y²)/2`, as an integrability criterion. -/
theorem integrable_mul_of_sq {f g : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ)
    (hg2 : Integrable (fun ω => g ω ^ 2) μ) : Integrable (fun ω => f ω * g ω) μ := by
  refine integrable_of_norm_le (hf.mul hg) (hf2.add hg2) (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_abs (f ω), sq_abs (g ω), sq_nonneg (|f ω| - |g ω|)]

/-- **Conditional variance**: `∫ Y (d - E[d|m])² ≤ ∫ Y d²` for `m`-measurable `0 ≤ Y ≤ C`. -/
theorem integral_mul_sq_sub_condExp_le (hm : m ≤ m0) [IsFiniteMeasure μ] {Y d : Ω → ℝ}
    (hY : StronglyMeasurable[m] Y) (hY0 : ∀ ω, 0 ≤ Y ω) {C : ℝ} (hYC : ∀ ω, Y ω ≤ C)
    (hdm : AEStronglyMeasurable d μ) (hd : Integrable d μ)
    (hd2 : Integrable (fun ω => d ω ^ 2) μ) :
    ∫ ω, Y ω * (d ω - μ[d | m] ω) ^ 2 ∂μ ≤ ∫ ω, Y ω * d ω ^ 2 ∂μ := by
  set g := μ[d | m]
  have hgm : AEStronglyMeasurable g μ := (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  have hg2 : Integrable (fun ω => g ω ^ 2) μ := integrable_condExp_pow hm even_two hd hd2
  have hYm : AEStronglyMeasurable Y μ := (hY.mono hm).aestronglyMeasurable
  have hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ C := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 ω)]; exact hYC ω
  have hYd2 : Integrable (fun ω => Y ω * d ω ^ 2) μ := hd2.bdd_mul hYm hYb
  have hYg2 : Integrable (fun ω => Y ω * g ω ^ 2) μ := hg2.bdd_mul hYm hYb
  have hgd : Integrable (fun ω => g ω * d ω) μ := integrable_mul_of_sq hgm hdm hg2 hd2
  have hZd : Integrable (fun ω => (Y ω * g ω) * d ω) μ := by
    have := hgd.bdd_mul hYm hYb
    exact this.congr (Filter.Eventually.of_forall fun ω => by simp only; ring)
  have hZ : StronglyMeasurable[m] fun ω => Y ω * g ω := hY.mul stronglyMeasurable_condExp
  have h0 := integral_mul_sub_condExp hm hZ hZd hd
  have hcross : Integrable (fun ω => (Y ω * g ω) * (d ω - g ω)) μ := by
    have h1 := integrable_mul_condExp hZ hZd hd
    exact (hZd.sub h1).congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.sub_apply, g]; ring)
  have hpt : ∀ ω, Y ω * (d ω - g ω) ^ 2 =
      Y ω * d ω ^ 2 - 2 * ((Y ω * g ω) * (d ω - g ω)) - Y ω * g ω ^ 2 := fun ω => by ring
  simp_rw [hpt]
  have e1 : ∫ ω, (Y ω * d ω ^ 2 - 2 * ((Y ω * g ω) * (d ω - g ω)) - Y ω * g ω ^ 2) ∂μ =
      ∫ ω, (Y ω * d ω ^ 2 - 2 * ((Y ω * g ω) * (d ω - g ω))) ∂μ - ∫ ω, Y ω * g ω ^ 2 ∂μ :=
    integral_sub (hYd2.sub (hcross.const_mul 2)) hYg2
  have e2 : ∫ ω, (Y ω * d ω ^ 2 - 2 * ((Y ω * g ω) * (d ω - g ω))) ∂μ =
      ∫ ω, Y ω * d ω ^ 2 ∂μ - ∫ ω, 2 * ((Y ω * g ω) * (d ω - g ω)) ∂μ :=
    integral_sub hYd2 (hcross.const_mul 2)
  rw [e1, e2, integral_const_mul, h0]
  have : 0 ≤ ∫ ω, Y ω * g ω ^ 2 ∂μ :=
    integral_nonneg fun ω => mul_nonneg (hY0 ω) (sq_nonneg _)
  linarith

end BlockBand.SourceProcess.FullSourceGenerator
