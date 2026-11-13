module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiWeightedPerronLimit
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedSphereInsertion
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.SingleBlockDOSLimit

/-!
# Weighted public-law Perron and Fatou passage

This is the successor split before selected-block reduction.
The weight is exactly `(N_[a,b] - 1).descFactorial r`.  For `a < b`, Perron
inversion and Fatou are performed under the public block-product law.
The degenerate case `a = b` is proved separately from endpoint nullity rather
than forced through a strict-interval theorem.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The public spectral Perron sum is the regulated resolvent integral. -/
theorem publicBlockPerronApprox_eq_resolventIntegral
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (G : BlockGUE.PublicBlockSample dims) (a b : ℝ) (n : ℕ) :
    publicBlockPerronApprox A₀ a b n G =
      ENNReal.ofReal ((1 / Real.pi) * ∫ x : ℝ in a..b,
        -(((((publicBlockDeformation A₀ G).1 -
          (x : ℂ) • (1 : Matrix (BlockGUE.Index dims)
            (BlockGUE.Index dims) ℂ) +
          Complex.I • (canonicalWegnerEta n •
            (1 : Matrix (BlockGUE.Index dims)
              (BlockGUE.Index dims) ℂ)))⁻¹).trace).im)) := by
  let H := publicBlockDeformation A₀ G
  have heta : 0 < canonicalWegnerEta n := canonicalWegnerEta_pos n
  have hpoint : (fun x : ℝ =>
      -(((((H.1 - (x : ℂ) •
        (1 : Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ) +
        Complex.I • (canonicalWegnerEta n •
          (1 : Matrix (BlockGUE.Index dims)
            (BlockGUE.Index dims) ℂ)))⁻¹).trace).im))) =
      fun x : ℝ => ∑ j : Fin (Fintype.card (BlockGUE.Index dims)),
        canonicalWegnerEta n /
          ((orderedEigenvalue H j - x) ^ 2 + canonicalWegnerEta n ^ 2) := by
    funext x
    exact neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
      H x heta
  unfold publicBlockPerronApprox
  congr 1
  rw [show publicBlockDeformation A₀ G = H from rfl, hpoint,
    intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [integral_poissonKernel_shift]
  · intro j _hj
    exact (continuous_const.div (by fun_prop) (fun x => by positivity)).intervalIntegrable _ _

/-- Perron approximant multiplied by the successor predecessor. -/
def publicBlockWeightedPerronApprox
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r n : ℕ) (G : BlockGUE.PublicBlockSample dims) : ℝ≥0∞ :=
  (((eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) - 1).descFactorial r :
    ℕ) : ℝ≥0∞) * publicBlockPerronApprox A₀ a b n G

/-- Every weighted public Perron approximant is measurable. -/
theorem measurable_publicBlockWeightedPerronApprox
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r n : ℕ) :
    Measurable (publicBlockWeightedPerronApprox A₀ a b r n) := by
  unfold publicBlockWeightedPerronApprox
  have hcount := measurable_publicBlockDeformation_eigenCount_Icc dims A₀ a b
  have hpredNat : Measurable (fun G : BlockGUE.PublicBlockSample dims =>
      eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) - 1) := by
    fun_prop
  have hpred : Measurable (fun G : BlockGUE.PublicBlockSample dims =>
      (((eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) - 1).descFactorial r :
        ℕ) : ℝ≥0∞)) :=
    Measurable.ennreal_descFactorial _ hpredNat r
  exact hpred.mul (measurable_publicBlockPerronApprox dims A₀ a b n)

/-- At endpoint-null samples, the weighted public Perron approximants converge
pointwise to the exact successor-factorial integrand. -/
theorem tendsto_publicBlockWeightedPerronApprox
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (G : BlockGUE.PublicBlockSample dims) {a b : ℝ} (hab : a < b)
    (ha : eigenCount (publicBlockDeformation A₀ G) {a} = 0)
    (hb : eigenCount (publicBlockDeformation A₀ G) {b} = 0)
    (r : ℕ) :
    Tendsto (fun n => publicBlockWeightedPerronApprox A₀ a b r n G) atTop
      (𝓝 ((eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) : ℝ≥0∞) *
        (((eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) - 1).descFactorial r :
          ℕ) : ℝ≥0∞))) := by
  let q := (eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) - 1).descFactorial r
  have h := tendsto_weighted_canonicalEta_integral_negImTrace
    (publicBlockDeformation A₀ G) hab ha hb q
  rw [show ((eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) : ℝ≥0∞) *
      (q : ℝ≥0∞)) = (q : ℝ≥0∞) *
        (eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) : ℝ≥0∞) by
      ac_rfl]
  simpa only [publicBlockWeightedPerronApprox,
    publicBlockPerronApprox_eq_resolventIntegral, q] using h

/-- **Weighted public-law Fatou passage for a nondegenerate interval.** -/
theorem publicBlock_lintegral_factorial_succ_le_liminf_weightedPerron
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (hDOS : SingleBlockDOS C₀)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a < b) (r : ℕ) :
    (∫⁻ G,
      ((eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b)).descFactorial
        (r + 1) : ℝ≥0∞)
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
    liminf (fun n => ∫⁻ G,
      publicBlockWeightedPerronApprox A₀ a b r n G
      ∂BlockGUE.publicBlockProductMeasure dims hd) atTop := by
  let μ := BlockGUE.publicBlockProductMeasure dims hd
  have hend : ∀ᵐ G ∂μ,
      eigenCount (publicBlockDeformation A₀ G) {a} = 0 ∧
      eigenCount (publicBlockDeformation A₀ G) {b} = 0 :=
    (ae_publicBlock_eigenCount_singleton_eq_zero hC₀ hDOS dims hd A₀ a).and
      (ae_publicBlock_eigenCount_singleton_eq_zero hC₀ hDOS dims hd A₀ b)
  calc
    _ = ∫⁻ G, liminf (fun n =>
        publicBlockWeightedPerronApprox A₀ a b r n G) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hend] with G hG
      have ht := tendsto_publicBlockWeightedPerronApprox
        A₀ G hab hG.1 hG.2 r
      rw [ht.liminf_eq]
      rw [descFactorial_succ_split, Nat.cast_mul]
    _ ≤ _ := lintegral_liminf_le fun n =>
      measurable_publicBlockWeightedPerronApprox dims A₀ a b r n

/-- On a singleton interval the public successor factorial integral is exactly
zero.  This is the `a = b` case, independent of strict Perron inversion. -/
theorem publicBlock_lintegral_factorial_succ_Icc_self_eq_zero
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (hDOS : SingleBlockDOS C₀)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (a : ℝ) (r : ℕ) :
    (∫⁻ G,
      ((eigenCount (publicBlockDeformation A₀ G) (Set.Icc a a)).descFactorial
        (r + 1) : ℝ≥0∞)
      ∂BlockGUE.publicBlockProductMeasure dims hd) = 0 := by
  calc
    _ = ∫⁻ _G, (0 : ℝ≥0∞) ∂BlockGUE.publicBlockProductMeasure dims hd := by
      apply lintegral_congr_ae
      filter_upwards
        [ae_publicBlock_eigenCount_singleton_eq_zero hC₀ hDOS dims hd A₀ a]
        with G hG
      simp [Set.Icc_self, hG]
    _ = 0 := lintegral_zero

end PSSSNative.BlockBand.PSSS
