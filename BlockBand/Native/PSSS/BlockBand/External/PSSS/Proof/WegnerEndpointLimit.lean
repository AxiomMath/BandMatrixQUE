module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerPerronPassage

/-!
# Endpoint-free Fatou passage for the public block product

The closed-interval estimate is obtained by applying the sharp Perron bound on
strictly enlarged intervals and then shrinking the enlargement.  This avoids
assuming endpoint nullity: eigenvalues in the original closed interval lie in
the interior of every enlarged interval.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

private def interiorPerronPartial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : HermitianMatrix ι) (a b δ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ r ∈ Finset.univ.filter (fun r => orderedEigenvalue H r ∈ Set.Icc a b),
    (1 / Real.pi) *
      (Real.arctan ((orderedEigenvalue H r - (a - δ)) / canonicalWegnerEta n) -
       Real.arctan ((orderedEigenvalue H r - (b + δ)) / canonicalWegnerEta n)))

private theorem tendsto_interiorPerronPartial {ι : Type*}
    [Fintype ι] [DecidableEq ι] (H : HermitianMatrix ι)
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    Tendsto (interiorPerronPartial H a b δ) atTop
      (𝓝 (eigenCount H (Set.Icc a b) : ℝ≥0∞)) := by
  let S := Finset.univ.filter (fun r => orderedEigenvalue H r ∈ Set.Icc a b)
  let f : ℕ → Fin (Fintype.card ι) → ℝ := fun n r =>
    (1 / Real.pi) *
      (Real.arctan ((orderedEigenvalue H r - (a - δ)) / canonicalWegnerEta n) -
       Real.arctan ((orderedEigenvalue H r - (b + δ)) / canonicalWegnerEta n))
  have hterm : ∀ r ∈ S, Tendsto (fun n => f n r) atTop (𝓝 1) := by
    intro r hr
    have hrmem : orderedEigenvalue H r ∈ Set.Icc a b := by
      simpa [S] using hr
    have hleft : orderedEigenvalue H r ≠ a - δ := by linarith [hrmem.1]
    have hright : orderedEigenvalue H r ≠ b + δ := by linarith [hrmem.2]
    have hbase := (tendsto_normalized_integral_poissonKernel_shift
      (show a - δ < b + δ by linarith) hleft hright).comp
        tendsto_canonicalWegnerEta_nhdsGT_zero
    have hmem : orderedEigenvalue H r ∈ Set.Icc (a - δ) (b + δ) := by
      constructor <;> linarith [hrmem.1, hrmem.2]
    rw [show (fun eta : ℝ => (1 / Real.pi) *
          ∫ x : ℝ in a - δ..b + δ,
            eta / ((orderedEigenvalue H r - x) ^ 2 + eta ^ 2)) =
        fun eta : ℝ => (1 / Real.pi) *
          (Real.arctan ((orderedEigenvalue H r - (a - δ)) / eta) -
           Real.arctan ((orderedEigenvalue H r - (b + δ)) / eta)) by
      funext eta
      rw [integral_poissonKernel_shift]] at hbase
    simpa only [f, hmem, ite_true, Function.comp_def] using hbase
  have hsum : Tendsto (fun n => ∑ r ∈ S, f n r) atTop (𝓝 (S.card : ℝ)) := by
    simpa using tendsto_finsetSum S hterm
  have hof := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsum
  change Tendsto (fun n => ENNReal.ofReal (∑ r ∈ S, f n r)) atTop
    (𝓝 (eigenCount H (Set.Icc a b) : ℝ≥0∞))
  rw [show eigenCount H (Set.Icc a b) = S.card by
    rw [eigenCount_def]
    congr 1
    ext r
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]]
  simpa only [Function.comp_def, ENNReal.ofReal_natCast] using hof

private theorem interiorPerronPartial_le_publicBlockPerronApprox_expanded
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (G : BlockGUE.PublicBlockSample dims) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (n : ℕ) :
    interiorPerronPartial (publicBlockDeformation A₀ G) a b δ n ≤
      publicBlockPerronApprox A₀ (a - δ) (b + δ) n G := by
  unfold interiorPerronPartial publicBlockPerronApprox
  apply ENNReal.ofReal_le_ofReal
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro r hr _hrnot
  have heta : 0 < canonicalWegnerEta n := canonicalWegnerEta_pos n
  have hquot :
      (orderedEigenvalue (publicBlockDeformation A₀ G) r - (b + δ)) /
          canonicalWegnerEta n ≤
      (orderedEigenvalue (publicBlockDeformation A₀ G) r - (a - δ)) /
          canonicalWegnerEta n := by
    apply div_le_div_of_nonneg_right _ heta.le
    linarith
  exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.arctan_mono hquot))

/-- Fatou on a strictly enlarged interval controls the expected count on the
original closed interval, without any endpoint-nullity assumption. -/
theorem publicBlock_lintegral_eigenCount_Icc_le_expanded {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hDOS : SingleBlockDOS C₀)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    (∫⁻ G, (eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) : ℝ≥0∞)
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
      ENNReal.ofReal (C₀ * (∑ j, (dims j : ℝ)) * ((b - a) + 2 * δ)) := by
  let μ := BlockGUE.publicBlockProductMeasure dims hd
  let q : ℕ → BlockGUE.PublicBlockSample dims → ℝ≥0∞ := fun n G =>
    interiorPerronPartial (publicBlockDeformation A₀ G) a b δ n
  let p : ℕ → BlockGUE.PublicBlockSample dims → ℝ≥0∞ := fun n G =>
    publicBlockPerronApprox A₀ (a - δ) (b + δ) n G
  have hq_tendsto : ∀ G, Tendsto (fun n => q n G) atTop
      (𝓝 (eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) : ℝ≥0∞)) := by
    intro G
    exact tendsto_interiorPerronPartial (publicBlockDeformation A₀ G) hab hδ
  have hpoint : ∀ G,
      (eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) : ℝ≥0∞) ≤
        liminf (fun n => p n G) atTop := by
    intro G
    rw [← (hq_tendsto G).liminf_eq]
    apply Filter.liminf_le_liminf
      (by
        filter_upwards with n
        exact interiorPerronPartial_le_publicBlockPerronApprox_expanded
          A₀ G hab hδ n)
      (by isBoundedDefault) (by isBoundedDefault)

  calc
    (∫⁻ G, (eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) : ℝ≥0∞) ∂μ) ≤
        ∫⁻ G, liminf (fun n => p n G) atTop ∂μ :=
      lintegral_mono hpoint
    _ ≤ liminf (fun n => ∫⁻ G, p n G ∂μ) atTop := by
      apply lintegral_liminf_le
      intro n
      exact measurable_publicBlockPerronApprox dims A₀ (a - δ) (b + δ) n
    _ ≤ ENNReal.ofReal (C₀ * (∑ j, (dims j : ℝ)) * ((b - a) + 2 * δ)) := by
      apply Filter.liminf_le_of_frequently_le'
      apply Filter.Eventually.frequently
      filter_upwards with n
      convert lintegral_publicBlockPerronApprox_le_sharp hC₀ hDOS dims hd A₀
        (show a - δ ≤ b + δ by linarith) n using 1
      congr 2
      ring

/-- Shrinking the strict enlargement gives the exact closed-interval constant.
No endpoint regularity is assumed; it is a consequence below. -/
theorem publicBlock_lintegral_eigenCount_Icc_le_of_singleBlockDOS {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hDOS : SingleBlockDOS C₀)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a ≤ b) :
    (∫⁻ G, (eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) : ℝ≥0∞)
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
      ENNReal.ofReal (C₀ * (∑ j, (dims j : ℝ)) * (b - a)) := by
  let K : ℝ := C₀ * ∑ j, (dims j : ℝ)
  have hreal : Tendsto
      (fun n => K * ((b - a) + 2 * canonicalWegnerEta n)) atTop
      (𝓝 (K * (b - a))) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.mul
      (tendsto_const_nhds.add
        (tendsto_const_nhds.mul tendsto_canonicalWegnerEta_zero))
  have henn : Tendsto
      (fun n => ENNReal.ofReal (K * ((b - a) + 2 * canonicalWegnerEta n))) atTop
      (𝓝 (ENNReal.ofReal (K * (b - a)))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply ge_of_tendsto henn
  filter_upwards with n
  simpa only [K] using publicBlock_lintegral_eigenCount_Icc_le_expanded
    hC₀ hDOS dims hd A₀ hab (canonicalWegnerEta_pos n)

/-- Every fixed energy is almost surely absent from the spectrum of the public
block-product deformation.  This is derived from the sharp interval estimate,
not postulated as an endpoint certificate. -/
theorem ae_publicBlock_eigenCount_singleton_eq_zero {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hDOS : SingleBlockDOS C₀)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (e : ℝ) :
    ∀ᵐ G ∂BlockGUE.publicBlockProductMeasure dims hd,
      eigenCount (publicBlockDeformation A₀ G) {e} = 0 := by
  let μ := BlockGUE.publicBlockProductMeasure dims hd
  have hzero :
      (∫⁻ G, (eigenCount (publicBlockDeformation A₀ G) {e} : ℝ≥0∞) ∂μ) = 0 := by
    apply le_zero_iff.mp
    simpa only [Set.Icc_self, sub_self, mul_zero, ENNReal.ofReal_zero] using
      publicBlock_lintegral_eigenCount_Icc_le_of_singleBlockDOS
        hC₀ hDOS dims hd A₀ (a := e) (b := e) le_rfl
  have hmeas : Measurable (fun G : BlockGUE.PublicBlockSample dims =>
      (eigenCount (publicBlockDeformation A₀ G) {e} : ℝ≥0∞)) := by
    have hn := (measurable_eigenCount_Icc e e).comp
      (measurable_publicBlockDeformation dims A₀)
    exact (measurable_of_countable
      (f := fun n : ℕ => (n : ℝ≥0∞))).comp (by
        simpa only [Set.Icc_self, Function.comp_def] using hn)
  have hae := (lintegral_eq_zero_iff hmeas).mp hzero
  filter_upwards [hae] with G hG
  have hG' : (eigenCount (publicBlockDeformation A₀ G) {e} : ℝ≥0∞) = 0 := by
    simpa only [Pi.zero_apply] using hG
  exact_mod_cast hG'

/-- The sharp multiblock Wegner estimate follows from the sharp one-block DOS
estimate with no dimension or normalization loss. -/
theorem wegnerBound_of_singleBlockDOS {C : ℝ}
    (hC : 1 ≤ C) (hDOS : SingleBlockDOS C) : WegnerBound C := by
  intro k dims hd A₀ a b hab
  exact publicBlock_lintegral_eigenCount_Icc_le_of_singleBlockDOS
    hC hDOS dims hd A₀ hab

/-- **PSSS multiblock Wegner estimate.**  The constant is absolute and the
right-hand side is exactly total block dimension times interval length. -/
theorem wegner : ∃ C : ℝ, 1 ≤ C ∧ WegnerBound C := by
  obtain ⟨C, hC, hDOS⟩ := singleBlock_dos
  exact ⟨C, hC, wegnerBound_of_singleBlockDOS hC hDOS⟩

end PSSSNative.BlockBand.PSSS
