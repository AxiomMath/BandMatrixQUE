module

public import BlockBand.Native.PSSS.BlockBand.Spectral.Measurable.Counts
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Source-independent spectral and factorial-induction lemmas for PSSS

This module isolates the finite-spectrum, atomlessness, measurability, endpoint,
and falling-factorial arguments used in the PSSS proof.  It deliberately does
not reproduce the APSSS quadratic-ratio estimate.  The matrix-specific input to
the last theorem is only the already established one-step fixed-vector bound.

The spectral statements are made for finite real eigenvalue lists.  This is the
right abstraction for the source-independent part: Hermitian diagonalization
supplies such a list, while no matrix density or resolvent estimate is assumed
here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

universe u

/-- Multiplicity-counted membership of a finite real spectrum. -/
def finiteSpectralCount {ι : Type*} [Fintype ι] (eig : ι → ℝ) (s : Set ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => eig i ∈ s).card

open scoped Classical in
/-- Indicator-sum form of a finite spectral count. -/
theorem finiteSpectralCount_eq_sum {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (s : Set ℝ) :
    finiteSpectralCount eig s = ∑ i, if eig i ∈ s then 1 else 0 := by
  classical
  simp [finiteSpectralCount]

/-- Pointwise convergence of finitely many eigenvalue branches preserves a
closed-interval count once neither endpoint belongs to the limiting spectrum. -/
theorem eventually_finiteSpectralCount_Icc_eq_of_tendsto {n : ℕ}
    (eig : ℝ → Fin n → ℝ) (μ : Fin n → ℝ) {a b : ℝ}
    (ha : ∀ i, μ i ≠ a) (hb : ∀ i, μ i ≠ b)
    (heig : ∀ i, Tendsto (fun t => eig t i) atTop (𝓝 (μ i))) :
    ∀ᶠ t in atTop,
      finiteSpectralCount (eig t) (Set.Icc a b) =
        finiteSpectralCount μ (Set.Icc a b) := by
  have hi : ∀ i : Fin n, ∀ᶠ t in atTop,
      (eig t i ∈ Set.Icc a b ↔ μ i ∈ Set.Icc a b) := by
    intro i
    have hca : ∀ᶠ t in atTop, (a ≤ eig t i ↔ a ≤ μ i) := by
      rcases lt_or_gt_of_ne (ha i) with hlt | hgt
      · filter_upwards [(heig i).eventually_lt_const hlt] with t ht
        simp [not_le.mpr ht, not_le.mpr hlt]
      · filter_upwards [(heig i).eventually_const_le hgt] with t ht
        exact iff_of_true ht hgt.le
    have hcb : ∀ᶠ t in atTop, (eig t i ≤ b ↔ μ i ≤ b) := by
      rcases lt_or_gt_of_ne (hb i) with hlt | hgt
      · filter_upwards [(heig i).eventually_le_const hlt] with t ht
        exact iff_of_true ht hlt.le
      · filter_upwards [(heig i).eventually_const_lt hgt] with t ht
        simp [not_le.mpr ht, not_le.mpr hgt]
    filter_upwards [hca, hcb] with t hta htb
    simpa only [Set.mem_Icc] using and_congr hta htb
  have hall : ∀ᶠ t in atTop, ∀ i : Fin n,
      (eig t i ∈ Set.Icc a b ↔ μ i ∈ Set.Icc a b) :=
    Filter.eventually_all.mpr hi
  filter_upwards [hall] with t ht
  simp only [finiteSpectralCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ht i

/-- Arithmetic adapter for a noncommuting positive rank-one interlacing theorem
proved at matrix level: a one-count loss implies the PSSS falling-factorial
inequality. -/
theorem descFactorial_pred_le_of_count_le_succ
    {N Nτ m : ℕ} (hcount : N ≤ Nτ + 1) :
    (N - 1).descFactorial m ≤ Nτ.descFactorial m := by
  exact Nat.descFactorial_le m (Nat.sub_le_iff_le_add.mpr hcount)

end PSSSNative.BlockBand.PSSS
