module

public import BlockBand.Coarea.Native.BlockBand.External.PSSS.Interface
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Expected empirical spectral measure

This file packages the multiplicity-counted expected spectrum of a finite
Hermitian random matrix as a finite Borel measure.  It is the measure-theoretic
bridge needed to turn the interval form of the PSSS counting estimate into
bounds for Poisson kernels in the one-block projected-Wegner argument.

The normalization is the unnormalised empirical measure: every eigenvalue has
mass one, so the total mass is the matrix dimension.  All statements are
finite-dimensional and uniform in the deterministic Hermitian deformation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory
open scoped BigOperators ENNReal

universe u

/-- The expected, unnormalised empirical spectral measure of a deformed block
GUE matrix. Each ordered eigenvalue contributes its pushforward probability
law, including multiplicity. -/
def BlockGUE.expectedSpectralMeasure
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d)) : Measure ℝ :=
  ∑ i : Fin (Fintype.card (BlockGUE.Index d)),
    M.P.map (fun ω => orderedEigenvalue (BlockGUE.deformed M A₀ ω) i)

private theorem measurable_deformed
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d)) :
    Measurable (fun ω => BlockGUE.deformed M A₀ ω) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro x y
  exact measurable_const.add (M.measurable_entry x y)

/-- Integration against the expected empirical spectral measure is expectation
of the finite eigenvalue sum. -/
theorem BlockGUE.lintegral_expectedSpectralMeasure
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂BlockGUE.expectedSpectralMeasure M A₀ =
      ∫⁻ ω, ∑ i : Fin (Fintype.card (BlockGUE.Index d)),
        f (orderedEigenvalue (BlockGUE.deformed M A₀ ω) i) ∂M.P := by
  rw [BlockGUE.expectedSpectralMeasure, lintegral_finsetSum_measure]
  have heig (i : Fin (Fintype.card (BlockGUE.Index d))) :
      Measurable (fun ω => orderedEigenvalue (BlockGUE.deformed M A₀ ω) i) :=
    (measurable_orderedEigenvalue i).comp (measurable_deformed M A₀)
  simp_rw [lintegral_map hf (heig _)]
  rw [lintegral_finsetSum]
  intro i _hi
  exact hf.comp (heig i)

/-- On a Borel set, the expected empirical spectral measure is the expected
multiplicity count. -/
theorem BlockGUE.expectedSpectralMeasure_apply
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (s : Set ℝ) (hs : MeasurableSet s) :
    BlockGUE.expectedSpectralMeasure M A₀ s =
      ∫⁻ ω, (BlockGUE.intervalCount M A₀ s ω : ℝ≥0∞) ∂M.P := by
  rw [← lintegral_indicator_one hs]
  change (∫⁻ x, s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) x ∂
      BlockGUE.expectedSpectralMeasure M A₀) = _
  rw [BlockGUE.lintegral_expectedSpectralMeasure M A₀
    (s.indicator (fun _ : ℝ => (1 : ℝ≥0∞))) (measurable_const.indicator hs)]
  apply lintegral_congr
  intro ω
  rw [BlockGUE.intervalCount, eigenCount_def]
  simp [Set.indicator, Finset.sum_boole]

/-- Closed intervals recover exactly the count appearing in `PSSSInput`. -/
theorem BlockGUE.expectedSpectralMeasure_Icc
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d)) (a b : ℝ) :
    BlockGUE.expectedSpectralMeasure M A₀ (Set.Icc a b) =
      ∫⁻ ω, (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ≥0∞) ∂M.P :=
  BlockGUE.expectedSpectralMeasure_apply M A₀ _ measurableSet_Icc

/-- The order-one PSSS interval estimate is exactly domination of the expected
spectral measure on closed intervals.  The constant and dimension normalization
are unchanged; no density or Radon–Nikodym conclusion is asserted here. -/
theorem psss_expectedSpectralMeasure_Icc_le
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (hab : a ≤ b) :
    BlockGUE.expectedSpectralMeasure M A₀ (Set.Icc a b) ≤
      ENNReal.ofReal
        (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) := by
  rw [BlockGUE.expectedSpectralMeasure_Icc]
  let N : M.Ω → ℝ := fun ω =>
    (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)
  have hN : Integrable N M.P := by
    simpa [N] using input.factorialIntegrable hd M A₀ a b 1
  have hconvert : ENNReal.ofReal (∫ ω, N ω ∂M.P) =
      ∫⁻ ω, (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ≥0∞) ∂M.P := by
    rw [ofReal_integral_eq_lintegral_ofReal hN
      (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _)]
    apply lintegral_congr
    intro ω
    simp [N]
  rw [← hconvert]
  apply ENNReal.ofReal_le_ofReal
  simpa [N] using input.factorialCount hd M A₀ a b hab 1 (by norm_num)

end CoareaNative.BlockBand
