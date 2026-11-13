module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedFiniteStageSuccessor
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.PublicGUECoordinateTransport
public import BlockBand.Native.PSSS.BlockBand.Counting.PhysicalMultiBlockCountConstruction

/-!
# PSSS root assembly

This module contains the endpoint, integrability, and exact-law adapters for the
PSSS factorial-count induction.  The successor step is supplied by
the separate Perron bridge; this file never changes the fixed
predecessor interval `Icc a b`, the auxiliary mesh `Ioo (-ξ) ξ`, or
the coefficient `10` established below that bridge.

The successor step needs an order-independent threshold: some `K ≥ 1` such that every `C ≥ K` carries
`PublicFactorialAtOrder C r` to `PublicFactorialAtOrder C (r + 1)`.  A
successor theorem which merely chooses a new constant after seeing `r` is not
strong enough to construct the single constant stored in `PSSSInput`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators

universe u

/-- The real descending-factorial count of a supplied normalized block-GUE law
is measurable, including for a degenerate closed interval and order zero. -/
theorem measurable_blockGUE_descFactorialCount
    {k : ℕ} {dims : Fin k → ℕ} {hd : ∀ j, 0 < dims j}
    (M : BlockGUE.Law.{u} dims hd)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (a b : ℝ) (r : ℕ) :
    Measurable (fun ω =>
      ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ)) := by
  have hH : Measurable (BlockGUE.deformed M A₀) := by
    apply Measurable.subtype_mk
    rw [Matrix.measurable_iff]
    intro x y
    exact measurable_const.add (M.measurable_entry x y)
  have hcount : Measurable (fun ω =>
      BlockGUE.intervalCount M A₀ (Set.Icc a b) ω) := by
    exact (measurable_eigenCount_Icc a b).comp hH
  have hdesc : Measurable (fun n : ℕ => n.descFactorial r) :=
    measurable_from_nat
  have hcast : Measurable (fun n : ℕ => (n : ℝ)) :=
    measurable_from_nat
  exact hcast.comp (hdesc.comp hcount)

/-- Every supplied-law descending-factorial count is integrable for elementary
finite-dimensional reasons.  This is the endpoint/integral adapter and does
not use the analytic successor estimate. -/
theorem blockGUE_descFactorial_integrable
    {k : ℕ} {dims : Fin k → ℕ} (hd : ∀ j, 0 < dims j)
    (M : BlockGUE.Law.{u} dims hd)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r : ℕ) :
    Integrable (fun ω =>
      ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ)) M.P := by
  apply Integrable.of_bound
    (measurable_blockGUE_descFactorialCount M A₀ a b r).aestronglyMeasurable
    ((Fintype.card (BlockGUE.Index dims) : ℝ) ^ r)
  filter_upwards with ω
  let N := BlockGUE.intervalCount M A₀ (Set.Icc a b) ω
  change ‖(N.descFactorial r : ℝ)‖ ≤
    (Fintype.card (BlockGUE.Index dims) : ℝ) ^ r
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have hcount : N ≤
        Fintype.card (BlockGUE.Index dims) := by
    exact PSSSNative.BlockBand.GaussianRing.eigenCount_le_dimension
      (BlockGUE.deformed M A₀ ω) (Set.Icc a b)
  simpa only [Nat.cast_pow] using
    (Nat.cast_le.mpr ((Nat.descFactorial_le_pow N r).trans
      (Nat.pow_le_pow_left hcount r)) : (N.descFactorial r : ℝ) ≤ _)

/-- Exact distributional transport of the factorial count from an arbitrary
supplied normalized block-GUE law to the public block-product law. -/
theorem blockGUE_descFactorial_identDistrib_public
    {k : ℕ} {dims : Fin k → ℕ} (hd : ∀ j, 0 < dims j)
    (M : BlockGUE.Law.{u} dims hd)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r : ℕ) :
    IdentDistrib
      (fun ω => ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ))
      (fun G => ((eigenCount (publicBlockDeformation A₀ G)
        (Set.Icc a b)).descFactorial r : ℝ)) M.P
      (BlockGUE.publicBlockProductMeasure dims hd) := by
  let q : HermitianMatrix (BlockGUE.Index dims) → ℝ := fun H =>
    ((eigenCount H (Set.Icc a b)).descFactorial r : ℝ)
  have hq : Measurable q := by
    have hdesc : Measurable (fun n : ℕ => n.descFactorial r) :=
      measurable_from_nat
    have hcast : Measurable (fun n : ℕ => (n : ℝ)) :=
      measurable_from_nat
    exact hcast.comp (hdesc.comp (measurable_eigenCount_Icc a b))
  have hM := (hasLaw_map hq.aemeasurable).fun_comp
    (M.hasLaw_deformed_publicBlockProduct A₀)
  have hpublic : HasLaw
      (fun G : BlockGUE.PublicBlockSample dims =>
        (publicBlockDeformation A₀ G))
      (BlockGUE.publicDeformedBlockProductMeasure dims hd A₀)
      (BlockGUE.publicBlockProductMeasure dims hd) := by
    refine ⟨?_, ?_⟩
    · have hdeform : Measurable (fun G : BlockGUE.PublicBlockSample dims =>
          publicBlockDeformation A₀ G) := by
        apply Measurable.subtype_mk
        rw [Matrix.measurable_iff]
        intro x y
        exact measurable_const.add
          ((BlockGUE.measurable_hermitianMatrix_entry x y).comp
            (BlockGUE.measurable_publicBlockDiagonal dims))
      exact hdeform.aemeasurable
    · exact (BlockGUE.publicDeformedBlockProductMeasure_eq_map_assembly
        dims hd A₀).symm
  have hpublicq := (hasLaw_map hq.aemeasurable).fun_comp hpublic
  simpa only [q, Function.comp_def, BlockGUE.intervalCount] using
    hM.identDistrib hpublicq

/-- A public closed-interval factorial estimate transports without loss to the
Bochner integral of every supplied normalized block-GUE law. -/
theorem PublicFactorialAtOrder.integral_law_le
    {C : ℝ} {r : ℕ} (h : PublicFactorialAtOrder C r) (hC : 0 ≤ C)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ j, 0 < dims j)
    (M : BlockGUE.Law.{u} dims hd)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (hab : a ≤ b) :
    ∫ ω, ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ) ∂M.P
      ≤ (C * (Fintype.card (BlockGUE.Index dims) : ℝ) * (b - a)) ^ r := by
  rw [(blockGUE_descFactorial_identDistrib_public hd M A₀ a b r).integral_eq]
  rw [blockGUE_dimension]
  push_cast
  have hmeas : Measurable (fun G : BlockGUE.PublicBlockSample dims =>
      ((eigenCount (publicBlockDeformation A₀ G)
        (Set.Icc a b)).descFactorial r : ℝ)) := by
    have hdesc : Measurable (fun n : ℕ => n.descFactorial r) :=
      measurable_from_nat
    have hcast : Measurable (fun n : ℕ => (n : ℝ)) :=
      measurable_from_nat
    exact hcast.comp (hdesc.comp
      (measurable_publicBlockDeformation_eigenCount_Icc dims A₀ a b))
  have hint : Integrable (fun G : BlockGUE.PublicBlockSample dims =>
      ((eigenCount (publicBlockDeformation A₀ G)
        (Set.Icc a b)).descFactorial r : ℝ))
      (BlockGUE.publicBlockProductMeasure dims hd) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable
      ((Fintype.card (BlockGUE.Index dims) : ℝ) ^ r)
    filter_upwards with G
    let N := eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b)
    change ‖(N.descFactorial r : ℝ)‖ ≤
      (Fintype.card (BlockGUE.Index dims) : ℝ) ^ r
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hcount : N ≤
        Fintype.card (BlockGUE.Index dims) := by
      exact PSSSNative.BlockBand.GaussianRing.eigenCount_le_dimension
        (publicBlockDeformation A₀ G) (Set.Icc a b)
    simpa only [Nat.cast_pow] using
      (Nat.cast_le.mpr ((Nat.descFactorial_le_pow N r).trans
        (Nat.pow_le_pow_left hcount r)) : (N.descFactorial r : ℝ) ≤ _)
  have hnonneg : 0 ≤ C * (∑ j, (dims j : ℝ)) * (b - a) := by
    positivity
  let F := fun G : BlockGUE.PublicBlockSample dims =>
    ((eigenCount (publicBlockDeformation A₀ G)
      (Set.Icc a b)).descFactorial r : ℝ)
  have hFnonneg : ∀ᵐ G ∂BlockGUE.publicBlockProductMeasure dims hd,
      0 ≤ F G := by
    filter_upwards with G
    exact Nat.cast_nonneg _
  have hof :
      ENNReal.ofReal (∫ G, F G ∂BlockGUE.publicBlockProductMeasure dims hd) =
        ∫⁻ G, ENNReal.ofReal (F G)
          ∂BlockGUE.publicBlockProductMeasure dims hd :=
    ofReal_integral_eq_lintegral_ofReal hint hFnonneg
  have hint_nonneg :
      0 ≤ ∫ G, F G ∂BlockGUE.publicBlockProductMeasure dims hd :=
    integral_nonneg_of_ae hFnonneg
  change (∫ G, F G ∂BlockGUE.publicBlockProductMeasure dims hd) ≤ _
  rw [← ENNReal.toReal_ofReal hint_nonneg, hof]
  rw [show (C * (∑ j, (dims j : ℝ)) * (b - a)) ^ r =
      (ENNReal.ofReal
        (C * (∑ j, (dims j : ℝ)) * (b - a)) ^ r).toReal by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hnonneg]]
  apply ENNReal.toReal_mono (by simp)
  simpa only [F, ENNReal.ofReal_natCast] using h dims hd A₀ a b hab

end PSSSNative.BlockBand.PSSS
