module

public import BlockBand.Coarea.Native.BlockBand.Counting.ScaledExponential
public import BlockBand.Coarea.Native.BlockBand.Counting.UnfoldedMarkedConfiguration

/-!
# PSSS factorial counts with an independent random Hermitian background

The external PSSS estimate is uniform in every deterministic Hermitian deformation.
Consequently it remains valid when the deformation is random but independent of the
GUE blocks.  This module represents that independence by the product probability law
`ν.prod M.P`, proves joint measurability and product integrability, and removes the
conditioning with Fubini.

Only the Hermitian background is used.  An absorber cannot enter a Hermitian eigenvalue
count, so any jointly carried absorber data are specialized away; no independence
between an auxiliary background and absorber is asserted.  The resulting declarations
cover all falling-factorial orders and the unfolded exponential estimate.  They do not
identify the concrete `GaussianRing.Law` with a single multi-block `BlockGUE.Law`; that
joint-law transport is needed for the physical `C / sqrt c` specialization.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Set
open scoped BigOperators

universe u v

/-- A BlockGUE matrix with an auxiliary random Hermitian deformation.  The product
sample is ordered as `(background sample, GUE sample)`. -/
def BlockGUE.randomBackgroundDeformed
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index d))
    (z : Ξ × M.Ω) : HermitianMatrix (BlockGUE.Index d) :=
  BlockGUE.deformed M (A₀ z.1) z.2

/-- Joint measurability of the independently deformed BlockGUE matrix. -/
theorem BlockGUE.measurable_randomBackgroundDeformed
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index d))
    (hA₀ : Measurable A₀) :
    Measurable (BlockGUE.randomBackgroundDeformed M A₀) := by
  apply Measurable.subtype_mk
  have hA : Measurable (fun ξ =>
      (A₀ ξ : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)) :=
    measurable_subtype_coe.comp hA₀
  rw [Matrix.measurable_iff]
  intro x y
  exact ((Matrix.measurable_iff.mp hA x y).comp measurable_fst).add
    ((M.measurable_entry x y).comp measurable_snd)

/-- Closed-interval count for a BlockGUE with an independent random Hermitian
background. -/
def BlockGUE.randomBackgroundIntervalCount
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (z : Ξ × M.Ω) : ℕ :=
  BlockGUE.intervalCount M (A₀ z.1) (Set.Icc a b) z.2

/-- Random-background interval counts are jointly measurable. -/
theorem BlockGUE.measurable_randomBackgroundIntervalCount
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index d))
    (hA₀ : Measurable A₀) (a b : ℝ) :
    Measurable (BlockGUE.randomBackgroundIntervalCount M A₀ a b) :=
  (measurable_eigenCount_Icc a b).comp
    (BlockGUE.measurable_randomBackgroundDeformed M A₀ hA₀)

/-- Product-law integrability of every random-background falling factorial.
The order-zero case is handled separately; positive orders use the uniform PSSS
estimate to dominate the conditional absolute integral. -/
theorem psss_randomBackground_factorialIntegrable
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index d))
    (hA₀ : Measurable A₀)
    (a b : ℝ) (hab : a ≤ b) (r : ℕ) :
    Integrable (fun z =>
      ((BlockGUE.randomBackgroundIntervalCount M A₀ a b z).descFactorial r : ℝ))
      (ν.prod M.P) := by
  let N := BlockGUE.randomBackgroundIntervalCount M A₀ a b
  let F : Ξ × M.Ω → ℝ := fun z => ((N z).descFactorial r : ℝ)
  let q := input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)
  have hN : Measurable N :=
    BlockGUE.measurable_randomBackgroundIntervalCount M A₀ hA₀ a b
  have hdesc : Measurable (fun n : ℕ => n.descFactorial r) := measurable_from_nat
  have hcast : Measurable (fun n : ℕ => (n : ℝ)) := measurable_from_nat
  have hF : Measurable F := hcast.comp (hdesc.comp hN)
  have hq : 0 ≤ q :=
    mul_nonneg (mul_nonneg input.C_nonneg (Nat.cast_nonneg _)) (sub_nonneg.mpr hab)
  rw [show (fun z =>
      ((BlockGUE.randomBackgroundIntervalCount M A₀ a b z).descFactorial r : ℝ)) =
      F by rfl]
  rw [integrable_prod_iff hF.aestronglyMeasurable]
  constructor
  · filter_upwards with ξ
    simpa [F, N, BlockGUE.randomBackgroundIntervalCount,
      BlockGUE.randomBackgroundDeformed] using
      input.factorialIntegrable hd M (A₀ ξ) a b r
  · apply (integrable_const (q ^ r)).mono'
      hF.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards with ξ
    have hnonneg : ∀ ω, 0 ≤ F (ξ, ω) := fun _ => Nat.cast_nonneg _
    rw [show (∫ ω, ‖F (ξ, ω)‖ ∂M.P) = ∫ ω, F (ξ, ω) ∂M.P by
      apply integral_congr_ae
      filter_upwards with ω
      exact Real.norm_of_nonneg (hnonneg ω)]
    rw [Real.norm_of_nonneg (integral_nonneg fun ω => hnonneg ω)]
    cases r with
    | zero =>
        simp [F, N, q]
    | succ r =>
        simpa [F, N, q, BlockGUE.randomBackgroundIntervalCount,
          BlockGUE.randomBackgroundDeformed] using
          input.factorialCount hd M (A₀ ξ) a b hab (r + 1)
            (Nat.succ_le_succ (Nat.zero_le r))

/-- **Random-background PSSS falling-factorial estimate.**  Conditioning on the
single auxiliary variable and applying Fubini preserves the exact deterministic
constant for every positive order. -/
theorem psss_randomBackground_factorialCount
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index d))
    (hA₀ : Measurable A₀)
    (a b : ℝ) (hab : a ≤ b) (r : ℕ) (hr : 1 ≤ r) :
    ∫ z, ((BlockGUE.randomBackgroundIntervalCount M A₀ a b z).descFactorial r : ℝ)
        ∂(ν.prod M.P) ≤
      (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) ^ r := by
  let F : Ξ × M.Ω → ℝ := fun z =>
    ((BlockGUE.randomBackgroundIntervalCount M A₀ a b z).descFactorial r : ℝ)
  let q := input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)
  have hprod : Integrable F (ν.prod M.P) :=
    psss_randomBackground_factorialIntegrable input hd M ν A₀ hA₀ a b hab r
  rw [show (fun z =>
      ((BlockGUE.randomBackgroundIntervalCount M A₀ a b z).descFactorial r : ℝ)) =
      F by rfl, integral_prod F hprod]
  have hinner : Integrable (fun ξ => ∫ ω, F (ξ, ω) ∂M.P) ν :=
    hprod.integral_prod_left
  calc
    (∫ ξ, ∫ ω, F (ξ, ω) ∂M.P ∂ν) ≤ ∫ _ξ, q ^ r ∂ν := by
      apply integral_mono hinner (integrable_const (q ^ r))
      intro ξ
      simpa [F, q, BlockGUE.randomBackgroundIntervalCount,
        BlockGUE.randomBackgroundDeformed] using
        input.factorialCount hd M (A₀ ξ) a b hab r hr
    _ = q ^ r := integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)
    _ = (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) ^ r := rfl

/-- Random-background exponential count estimate obtained from the complete family of
falling-factorial bounds. -/
theorem psss_randomBackground_countExponential
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index d))
    (hA₀ : Measurable A₀)
    (a b t : ℝ) (hab : a ≤ b) (ht : 0 ≤ t) :
    let q := input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)
    ∫ z, Real.exp (t *
        (BlockGUE.randomBackgroundIntervalCount M A₀ a b z : ℝ)) ∂(ν.prod M.P) ≤
      Real.exp (q * (Real.exp t - 1)) := by
  dsimp only
  let N := BlockGUE.randomBackgroundIntervalCount M A₀ a b
  let D := Fintype.card (BlockGUE.Index d)
  let q := input.C * (D : ℝ) * (b - a)
  have hq : 0 ≤ q :=
    mul_nonneg (mul_nonneg input.C_nonneg (Nat.cast_nonneg _)) (sub_nonneg.mpr hab)
  apply integral_exp_count_le_of_factorialMoments (ν.prod M.P) N D q t
  · intro z
    calc
      N z ≤ eigenCount (BlockGUE.randomBackgroundDeformed M A₀ z) Set.univ :=
        eigenCount_mono _ (Set.subset_univ _)
      _ = D := by simp [D]
  · exact hq
  · exact ht
  · intro r hrange
    exact psss_randomBackground_factorialIntegrable
      input hd M ν A₀ hA₀ a b hab r
  · intro r hrange
    cases r with
    | zero => simp [N]
    | succ r =>
        simpa [N, q, D] using
          psss_randomBackground_factorialCount input hd M ν A₀ hA₀
            a b hab (r + 1) (Nat.succ_le_succ (Nat.zero_le r))

/-- Count in the physical interval corresponding to an unfolded window, with an
independent random Hermitian background. -/
def BlockGUE.randomBackgroundUnfoldedIntervalCount
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index d))
    (e L ρ R : ℝ) (z : Ξ × M.Ω) : ℕ :=
  BlockGUE.randomBackgroundIntervalCount M A₀
    (e - R / (L * ρ)) (e + R / (L * ρ)) z

/-- **Unfolded exponential count with an independent random background.**  Under the
dimension bound of the paper, the estimate is independent of the background law and of
`L`. -/
theorem psss_randomBackground_unfoldedCountExponential
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index d))
    (hA₀ : Measurable A₀)
    (e L ρ R t : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hdim : (Fintype.card (BlockGUE.Index d) : ℝ) ≤ L)
    (ht : 0 ≤ t) :
    ∫ z, Real.exp (t *
        (BlockGUE.randomBackgroundUnfoldedIntervalCount M A₀ e L ρ R z : ℝ))
        ∂(ν.prod M.P) ≤
      Real.exp (2 * R * (input.C / ρ) * (Real.exp t - 1)) := by
  let a := e - R / (L * ρ)
  let b := e + R / (L * ρ)
  have hLρ : 0 < L * ρ := mul_pos hL hρ
  have hab : a ≤ b := by
    dsimp [a, b]
    have : 0 ≤ R / (L * ρ) := div_nonneg hR hLρ.le
    linarith
  have hbase := psss_randomBackground_countExponential
    input hd M ν A₀ hA₀ a b t hab ht
  change (∫ z, Real.exp (t *
    (BlockGUE.randomBackgroundIntervalCount M A₀ a b z : ℝ)) ∂(ν.prod M.P)) ≤ _
  calc
    (∫ z, Real.exp (t *
        (BlockGUE.randomBackgroundIntervalCount M A₀ a b z : ℝ)) ∂(ν.prod M.P)) ≤
      Real.exp ((input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) *
        (Real.exp t - 1)) := hbase
    _ ≤ Real.exp (2 * R * (input.C / ρ) * (Real.exp t - 1)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _
        (sub_nonneg.mpr (Real.one_le_exp ht))
      have hCdim : input.C * (Fintype.card (BlockGUE.Index d) : ℝ) ≤
          input.C * L := mul_le_mul_of_nonneg_left hdim input.C_nonneg
      have hwidth : b - a = 2 * R / (L * ρ) := by
        dsimp [a, b]
        ring
      rw [hwidth]
      calc
        input.C * (Fintype.card (BlockGUE.Index d) : ℝ) *
            (2 * R / (L * ρ)) ≤
          (input.C * L) * (2 * R / (L * ρ)) := by
            exact mul_le_mul_of_nonneg_right hCdim
              (div_nonneg (mul_nonneg (by norm_num) hR) hLρ.le)
        _ = 2 * R * (input.C / ρ) := by field_simp

end CoareaNative.BlockBand
