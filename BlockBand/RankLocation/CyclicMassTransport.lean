module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Loss-free cyclic mass-law transport

Under a cyclic symmetry of the law and of the block masses `p_k`, tilting the law by the density
`n p_k` (or `(n/2)(p_k + p_l)`) gives a probability measure under which every invariant
observable has the same law, the same expectations and the same `L^p` norms, with no
`n`-dependent loss.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.RankLocation.MassTransport

open MeasureTheory
open scoped BigOperators ENNReal

/-- Cyclic symmetry data at one fixed deterministic eigenvalue rank. The covariance direction
`k - s` matches the inverse-image reindexing convention of the physical model. -/
structure CyclicMassSymmetry {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) [NeZero n] where
  shift : ZMod n → Ω → Ω
  mass : ZMod n → Ω → ℝ≥0∞
  preserving : ∀ s, MeasurePreserving (shift s) μ μ
  measurable_mass : ∀ k, Measurable (mass k)
  sum_mass : ∀ᵐ ω ∂μ, ∑ k, mass k ω = 1
  covariant : ∀ s k, ∀ᵐ ω ∂μ, mass k (shift s ω) = mass (k - s) ω

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {n : ℕ} [NeZero n]

/-- The normalized single-block mass tilt, with density `n p_k`. -/
def blockMassMeasure (S : CyclicMassSymmetry μ n) (k : ZMod n) : Measure Ω :=
  μ.withDensity (fun ω => (n : ℝ≥0∞) * S.mass k ω)

/-- The normalized pair mass tilt, with density `(n/2)(p_k + p_l)` (any pair, not only adjacent
ones). -/
def pairMassMeasure (S : CyclicMassSymmetry μ n) (k l : ZMod n) : Measure Ω :=
  μ.withDensity (fun ω => ((n : ℝ≥0∞) / 2) * (S.mass k ω + S.mass l ω))

/-- Covariance and invariant tests give equal joint weighted moments at every
site, not merely equal marginal distributions of the site masses. -/
theorem lintegral_mass_mul_eq
    (S : CyclicMassSymmetry μ n) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (hFinv : ∀ s, ∀ᵐ ω ∂μ, F (S.shift s ω) = F ω) (k l : ZMod n) :
    (∫⁻ ω, S.mass k ω * F ω ∂μ) = ∫⁻ ω, S.mass l ω * F ω ∂μ := by
  let s : ZMod n := k - l
  have hindex : k - s = l := by dsimp [s]; abel
  calc
    _ = ∫⁻ ω, S.mass k (S.shift s ω) * F (S.shift s ω) ∂μ :=
      ((S.preserving s).lintegral_comp ((S.measurable_mass k).mul hF)).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [S.covariant s k, hFinv s] with ω hmass htest
      rw [hmass, htest, hindex]

/-- `E[n p_k F] = E[F]` for every nonnegative measurable invariant `F`, by averaging the joint
moments and using the unit total mass. -/
theorem lintegral_scaled_mass_mul_eq
    (S : CyclicMassSymmetry μ n) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (hFinv : ∀ s, ∀ᵐ ω ∂μ, F (S.shift s ω) = F ω) (k : ZMod n) :
    (∫⁻ ω, ((n : ℝ≥0∞) * S.mass k ω) * F ω ∂μ) = ∫⁻ ω, F ω ∂μ := by
  calc
    _ = (n : ℝ≥0∞) * ∫⁻ ω, S.mass k ω * F ω ∂μ := by
      simp_rw [mul_assoc]
      exact lintegral_const_mul _ ((S.measurable_mass k).mul hF)
    _ = ∑ l : ZMod n, ∫⁻ ω, S.mass l ω * F ω ∂μ := by
      simp_rw [← lintegral_mass_mul_eq S F hF hFinv k]
      simp [ZMod.card]
    _ = ∫⁻ ω, (∑ l : ZMod n, S.mass l ω) * F ω ∂μ := by
      rw [← lintegral_finsetSum]
      · congr 1
        funext ω
        exact (Finset.sum_mul _ _ _).symm
      · intro l _
        exact (S.measurable_mass l).mul hF
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [S.sum_mass] with ω hω
      rw [hω, one_mul]

/-- Pair version `E[(n/2)(p_k + p_l) F] = E[F]`, including infinite moments. -/
theorem lintegral_scaled_pair_mass_mul_eq
    (S : CyclicMassSymmetry μ n) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (hFinv : ∀ s, ∀ᵐ ω ∂μ, F (S.shift s ω) = F ω) (k l : ZMod n) :
    (∫⁻ ω, (((n : ℝ≥0∞) / 2) * (S.mass k ω + S.mass l ω)) * F ω ∂μ) =
      ∫⁻ ω, F ω ∂μ := by
  calc
    _ = ((n : ℝ≥0∞) / 2) *
        ((∫⁻ ω, S.mass k ω * F ω ∂μ) + ∫⁻ ω, S.mass l ω * F ω ∂μ) := by
      simp_rw [mul_assoc, add_mul]
      rw [lintegral_const_mul _ (show Measurable (fun ω =>
          S.mass k ω * F ω + S.mass l ω * F ω) from
          ((S.measurable_mass k).mul hF).add ((S.measurable_mass l).mul hF)),
        lintegral_add_left (show Measurable (fun ω => S.mass k ω * F ω) from
          (S.measurable_mass k).mul hF)]
    _ = (n : ℝ≥0∞) * ∫⁻ ω, S.mass k ω * F ω ∂μ := by
      rw [← lintegral_mass_mul_eq S F hF hFinv k l, ← two_mul, ← mul_assoc]
      rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    _ = _ := by
      have hscalar : (∫⁻ ω, ((n : ℝ≥0∞) * S.mass k ω) * F ω ∂μ) =
          (n : ℝ≥0∞) * ∫⁻ ω, S.mass k ω * F ω ∂μ := by
        simp_rw [mul_assoc]
        exact lintegral_const_mul _ ((S.measurable_mass k).mul hF)
      exact hscalar.symm.trans (lintegral_scaled_mass_mul_eq S F hF hFinv k)

/-- A nonnegative invariant observable has the same expectation under the block-mass law and the
original law. -/
theorem lintegral_blockMassMeasure_eq
    (S : CyclicMassSymmetry μ n) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (hFinv : ∀ s, ∀ᵐ ω ∂μ, F (S.shift s ω) = F ω) (k : ZMod n) :
    (∫⁻ ω, F ω ∂blockMassMeasure S k) = ∫⁻ ω, F ω ∂μ := by
  have hdensity := lintegral_withDensity_eq_lintegral_mul μ
    (show Measurable (fun ω => (n : ℝ≥0∞) * S.mass k ω) from
      measurable_const.mul (S.measurable_mass k)) hF
  exact hdensity.trans (lintegral_scaled_mass_mul_eq S F hF hFinv k)

/-- The pair-mass law preserves every nonnegative invariant expectation. -/
theorem lintegral_pairMassMeasure_eq
    (S : CyclicMassSymmetry μ n) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (hFinv : ∀ s, ∀ᵐ ω ∂μ, F (S.shift s ω) = F ω) (k l : ZMod n) :
    (∫⁻ ω, F ω ∂pairMassMeasure S k l) = ∫⁻ ω, F ω ∂μ := by
  have hdensity := lintegral_withDensity_eq_lintegral_mul μ
    (show Measurable (fun ω => ((n : ℝ≥0∞) / 2) * (S.mass k ω + S.mass l ω)) from
      measurable_const.mul ((S.measurable_mass k).add (S.measurable_mass l))) hF
  exact hdensity.trans (lintegral_scaled_pair_mass_mul_eq S F hF hFinv k l)

/-- The block-mass tilt is a probability measure. -/
theorem isProbabilityMeasure_blockMassMeasure
    (S : CyclicMassSymmetry μ n) [IsProbabilityMeasure μ] (k : ZMod n) :
    IsProbabilityMeasure (blockMassMeasure S k) := by
  constructor
  have h := lintegral_blockMassMeasure_eq S (fun _ => 1) measurable_const
    (fun _ => Filter.Eventually.of_forall fun _ => rfl) k
  simpa using h

/-- The pair-mass tilt is a probability measure. -/
theorem isProbabilityMeasure_pairMassMeasure
    (S : CyclicMassSymmetry μ n) [IsProbabilityMeasure μ] (k l : ZMod n) :
    IsProbabilityMeasure (pairMassMeasure S k l) := by
  constructor
  have h := lintegral_pairMassMeasure_eq S (fun _ => 1) measurable_const
    (fun _ => Filter.Eventually.of_forall fun _ => rfl) k l
  simpa using h

/-- Equal pushforward laws for every measurable invariant observable `X` (for instance the whole
ordered spectrum). -/
theorem map_blockMassMeasure_eq
    {Y : Type*} [MeasurableSpace Y] (S : CyclicMassSymmetry μ n)
    (X : Ω → Y) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω) (k : ZMod n) :
    Measure.map X (blockMassMeasure S k) = Measure.map X μ := by
  classical
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hX hA, Measure.map_apply hX hA]
  have hF : Measurable ((X ⁻¹' A).indicator (fun _ : Ω => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hA.preimage hX)
  have hinv : ∀ s, ∀ᵐ ω ∂μ,
      (X ⁻¹' A).indicator (fun _ : Ω => (1 : ℝ≥0∞)) (S.shift s ω) =
        (X ⁻¹' A).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω := by
    intro s
    filter_upwards [hXinv s] with ω hω
    change (if X (S.shift s ω) ∈ A then (1 : ℝ≥0∞) else 0) =
      (if X ω ∈ A then (1 : ℝ≥0∞) else 0)
    rw [hω]
  simpa [lintegral_indicator (hA.preimage hX)] using lintegral_blockMassMeasure_eq S
    ((X ⁻¹' A).indicator (fun _ : Ω => (1 : ℝ≥0∞))) hF hinv k

/-- The complete invariant observable law is also unchanged by pair bias. -/
theorem map_pairMassMeasure_eq
    {Y : Type*} [MeasurableSpace Y] (S : CyclicMassSymmetry μ n)
    (X : Ω → Y) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω) (k l : ZMod n) :
    Measure.map X (pairMassMeasure S k l) = Measure.map X μ := by
  classical
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hX hA, Measure.map_apply hX hA]
  have hF : Measurable ((X ⁻¹' A).indicator (fun _ : Ω => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hA.preimage hX)
  have hinv : ∀ s, ∀ᵐ ω ∂μ,
      (X ⁻¹' A).indicator (fun _ : Ω => (1 : ℝ≥0∞)) (S.shift s ω) =
        (X ⁻¹' A).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω := by
    intro s
    filter_upwards [hXinv s] with ω hω
    change (if X (S.shift s ω) ∈ A then (1 : ℝ≥0∞) else 0) =
      (if X ω ∈ A then (1 : ℝ≥0∞) else 0)
    rw [hω]
  simpa [lintegral_indicator (hA.preimage hX)] using lintegral_pairMassMeasure_eq S
    ((X ⁻¹' A).indicator (fun _ : Ω => (1 : ℝ≥0∞))) hF hinv k l

/-- All extended `L^p` norms of measurable real functions of `X` are unchanged, including
`p = ∞`. -/
theorem eLpNorm_comp_blockMassMeasure_eq
    {Y : Type*} [MeasurableSpace Y] (S : CyclicMassSymmetry μ n)
    (X : Ω → Y) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (F : Y → ℝ) (hF : Measurable F) (p : ℝ≥0∞) (k : ZMod n) :
    eLpNorm (F ∘ X) p (blockMassMeasure S k) = eLpNorm (F ∘ X) p μ := by
  rw [← eLpNorm_map_measure hF.aestronglyMeasurable hX.aemeasurable,
    map_blockMassMeasure_eq S X hX hXinv k,
    eLpNorm_map_measure hF.aestronglyMeasurable hX.aemeasurable]

/-- Pair-law counterpart for every extended `L^p` order. -/
theorem eLpNorm_comp_pairMassMeasure_eq
    {Y : Type*} [MeasurableSpace Y] (S : CyclicMassSymmetry μ n)
    (X : Ω → Y) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (F : Y → ℝ) (hF : Measurable F) (p : ℝ≥0∞) (k l : ZMod n) :
    eLpNorm (F ∘ X) p (pairMassMeasure S k l) = eLpNorm (F ∘ X) p μ := by
  rw [← eLpNorm_map_measure hF.aestronglyMeasurable hX.aemeasurable,
    map_pairMassMeasure_eq S X hX hXinv k l,
    eLpNorm_map_measure hF.aestronglyMeasurable hX.aemeasurable]

/-- `L^p` membership transfers in both directions for functions of the invariant observable. -/
theorem memLp_comp_blockMassMeasure_iff
    {Y : Type*} [MeasurableSpace Y] (S : CyclicMassSymmetry μ n)
    (X : Ω → Y) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (F : Y → ℝ) (hF : Measurable F) (p : ℝ≥0∞) (k : ZMod n) :
    MemLp (F ∘ X) p (blockMassMeasure S k) ↔ MemLp (F ∘ X) p μ := by
  simp only [MemLp,
    eLpNorm_comp_blockMassMeasure_eq S X hX hXinv F hF p k]

/-- Pair-law `L^p` membership transfer. -/
theorem memLp_comp_pairMassMeasure_iff
    {Y : Type*} [MeasurableSpace Y] (S : CyclicMassSymmetry μ n)
    (X : Ω → Y) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (F : Y → ℝ) (hF : Measurable F) (p : ℝ≥0∞) (k l : ZMod n) :
    MemLp (F ∘ X) p (pairMassMeasure S k l) ↔ MemLp (F ∘ X) p μ := by
  simp only [MemLp,
    eLpNorm_comp_pairMassMeasure_eq S X hX hXinv F hF p k l]

/-- Equality of the real `L^p` seminorms of measurable functions of `X`. -/
theorem lpNorm_comp_blockMassMeasure_eq
    {Y : Type*} [MeasurableSpace Y] (S : CyclicMassSymmetry μ n)
    (X : Ω → Y) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (F : Y → ℝ) (hF : Measurable F) (p : ℝ≥0∞) (k : ZMod n) :
    lpNorm (F ∘ X) p (blockMassMeasure S k) = lpNorm (F ∘ X) p μ := by
  unfold lpNorm
  rw [eLpNorm_comp_blockMassMeasure_eq S X hX hXinv F hF p k]

/-- Pair-law equality of the real `L^p` seminorms. -/
theorem lpNorm_comp_pairMassMeasure_eq
    {Y : Type*} [MeasurableSpace Y] (S : CyclicMassSymmetry μ n)
    (X : Ω → Y) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (F : Y → ℝ) (hF : Measurable F) (p : ℝ≥0∞) (k l : ZMod n) :
    lpNorm (F ∘ X) p (pairMassMeasure S k l) = lpNorm (F ∘ X) p μ := by
  unfold lpNorm
  rw [eLpNorm_comp_pairMassMeasure_eq S X hX hXinv F hF p k l]

end BlockBand.RankLocation.MassTransport
