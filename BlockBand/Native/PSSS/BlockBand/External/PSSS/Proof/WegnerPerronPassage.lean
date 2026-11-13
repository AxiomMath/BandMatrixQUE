module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerFrozenIdentification
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECanonicalWegnerTonelli

/-!
# Perron–Stieltjes preparation for the public block product

The arctangent Perron approximant of the eigenvalue count of `[a, b]` at height `η_n` is the
energy integral over `(a, b]` of `1/π` times the regulated resolvent trace. With the Wegner bound
for the regulated trace, its expectation under the public block-GUE product is at most
`C₀ (∑ⱼ dims j) (b - a)`, uniformly in `n`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- Public-block Perron kernel along the standard positive-height sequence. -/
def publicBlockPerronKernel {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (n : ℕ)
    (G : BlockGUE.PublicBlockSample dims) (e : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.pi) *
    publicBlockRegulatedTrace A₀ e (canonicalWegnerEta n) G

/-- Public-block finite spectral Perron approximant. -/
def publicBlockPerronApprox {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (a b : ℝ) (n : ℕ)
    (G : BlockGUE.PublicBlockSample dims) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ r : Fin (Fintype.card (BlockGUE.Index dims)),
    (1 / Real.pi) *
      (Real.arctan ((orderedEigenvalue (publicBlockDeformation A₀ G) r - a) /
          canonicalWegnerEta n) -
       Real.arctan ((orderedEigenvalue (publicBlockDeformation A₀ G) r - b) /
          canonicalWegnerEta n)))

lemma measurable_publicBlockDeformation {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) :
    Measurable (publicBlockDeformation A₀) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro x y
  exact measurable_const.add
    ((BlockGUE.measurable_hermitianMatrix_entry x y).comp
      (BlockGUE.measurable_publicBlockDiagonal dims))

/-- The public Perron approximant is measurable in the complete block sample. -/
theorem measurable_publicBlockPerronApprox {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (a b : ℝ) (n : ℕ) :
    Measurable (publicBlockPerronApprox A₀ a b n) := by
  unfold publicBlockPerronApprox
  apply Measurable.ennreal_ofReal
  apply Finset.measurable_sum
  intro r hr
  have hlam : Measurable (fun G : BlockGUE.PublicBlockSample dims =>
      orderedEigenvalue (publicBlockDeformation A₀ G) r) :=
    (measurable_orderedEigenvalue r).comp
      (measurable_publicBlockDeformation dims A₀)
  exact measurable_const.mul
    ((Real.continuous_arctan.measurable.comp
      ((hlam.sub measurable_const).div_const _)).sub
     (Real.continuous_arctan.measurable.comp
      ((hlam.sub measurable_const).div_const _)))

/-- Joint sample/energy measurability of the public Perron kernel. -/
theorem measurable_uncurry_publicBlockPerronKernel {k : ℕ}
    (dims : Fin k → ℕ) (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (n : ℕ) : Measurable (Function.uncurry (publicBlockPerronKernel A₀ n)) := by
  unfold publicBlockPerronKernel publicBlockRegulatedTrace
  dsimp only [Function.uncurry]
  have hfun : (fun p : BlockGUE.PublicBlockSample dims × ℝ =>
      -((((((publicBlockDeformation A₀ p.1).1 -
        (p.2 : ℂ) • (1 : Matrix (BlockGUE.Index dims)
          (BlockGUE.Index dims) ℂ)) +
        Complex.I • (canonicalWegnerEta n •
          (1 : Matrix (BlockGUE.Index dims)
            (BlockGUE.Index dims) ℂ)))⁻¹).trace).im)) =
      fun p => ∑ r : Fin (Fintype.card (BlockGUE.Index dims)),
        canonicalWegnerEta n /
          ((orderedEigenvalue (publicBlockDeformation A₀ p.1) r - p.2) ^ 2 +
            canonicalWegnerEta n ^ 2) := by
    funext p
    exact neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
      (publicBlockDeformation A₀ p.1) p.2 (canonicalWegnerEta_pos n)
  change Measurable (fun p : BlockGUE.PublicBlockSample dims × ℝ =>
    ENNReal.ofReal (1 / Real.pi) * ENNReal.ofReal
      (-((((((publicBlockDeformation A₀ p.1).1 -
        (p.2 : ℂ) • (1 : Matrix (BlockGUE.Index dims)
          (BlockGUE.Index dims) ℂ)) + Complex.I • (canonicalWegnerEta n •
        (1 : Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ)))⁻¹).trace).im)))
  convert (by
    have hs : Measurable (fun p : BlockGUE.PublicBlockSample dims × ℝ =>
        ENNReal.ofReal (∑ r : Fin (Fintype.card (BlockGUE.Index dims)),
          canonicalWegnerEta n /
            ((orderedEigenvalue (publicBlockDeformation A₀ p.1) r - p.2) ^ 2 +
              canonicalWegnerEta n ^ 2))) := by
      apply Measurable.ennreal_ofReal
      apply Finset.measurable_sum
      intro r hr
      have hlam : Measurable (fun p : BlockGUE.PublicBlockSample dims × ℝ =>
        orderedEigenvalue (publicBlockDeformation A₀ p.1) r) :=
      (measurable_orderedEigenvalue r).comp
        ((measurable_publicBlockDeformation dims A₀).comp measurable_fst)
      exact measurable_const.div
        (((hlam.sub measurable_snd).pow_const 2).add measurable_const)
    have hc : Measurable (fun _ : BlockGUE.PublicBlockSample dims × ℝ =>
        ENNReal.ofReal (1 / Real.pi)) := measurable_const
    exact hc.mul hs : Measurable
        (fun p : BlockGUE.PublicBlockSample dims × ℝ =>
          ENNReal.ofReal (1 / Real.pi) * ENNReal.ofReal
            (∑ r : Fin (Fintype.card (BlockGUE.Index dims)),
              canonicalWegnerEta n /
                ((orderedEigenvalue (publicBlockDeformation A₀ p.1) r - p.2) ^ 2 +
                  canonicalWegnerEta n ^ 2)))) using 1
  funext p
  rw [congrFun hfun p]

/-- The spectral Perron approximant is exactly the half-open energy lower
integral of the public regulated kernel. -/
theorem publicBlockPerronApprox_eq_lintegral_Ioc {k : ℕ}
    {dims : Fin k → ℕ} (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (G : BlockGUE.PublicBlockSample dims) (n : ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    publicBlockPerronApprox A₀ a b n G =
      ∫⁻ e in Set.Ioc a b, publicBlockPerronKernel A₀ n G e := by
  let H := publicBlockDeformation A₀ G
  let g : ℝ → ℝ := fun e =>
    -(((((H.1 - (e : ℂ) • (1 : Matrix (BlockGUE.Index dims)
      (BlockGUE.Index dims) ℂ)) + Complex.I • (canonicalWegnerEta n •
        (1 : Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ)))⁻¹).trace).im)
  have hfun : g = fun e => ∑ r : Fin (Fintype.card (BlockGUE.Index dims)),
      canonicalWegnerEta n /
        ((orderedEigenvalue H r - e) ^ 2 + canonicalWegnerEta n ^ 2) := by
    funext e
    exact neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
      H e (canonicalWegnerEta_pos n)
  have hg : Continuous g := by
    rw [hfun]
    apply continuous_finsetSum
    intro r hr
    exact continuous_const.div (by fun_prop) (fun e => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _)
      (sq_pos_of_pos (canonicalWegnerEta_pos n))))
  have hnonneg : ∀ e, 0 ≤ g e := by
    intro e
    rw [hfun]
    apply Finset.sum_nonneg
    intro r hr
    exact div_nonneg (canonicalWegnerEta_pos n).le (by positivity)
  have hreal : (∑ r : Fin (Fintype.card (BlockGUE.Index dims)),
      (1 / Real.pi) *
        (Real.arctan ((orderedEigenvalue H r - a) / canonicalWegnerEta n) -
         Real.arctan ((orderedEigenvalue H r - b) / canonicalWegnerEta n))) =
      (1 / Real.pi) * ∫ e : ℝ in a..b, g e := by
    rw [hfun, intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [integral_poissonKernel_shift]
    · intro r hr
      exact (continuous_const.div (by fun_prop) (fun e => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _)
      (sq_pos_of_pos (canonicalWegnerEta_pos n))))).intervalIntegrable _ _
  unfold publicBlockPerronApprox publicBlockPerronKernel
  change ENNReal.ofReal (∑ r : Fin (Fintype.card (BlockGUE.Index dims)),
      (1 / Real.pi) *
        (Real.arctan ((orderedEigenvalue H r - a) / canonicalWegnerEta n) -
         Real.arctan ((orderedEigenvalue H r - b) / canonicalWegnerEta n))) =
    ∫⁻ e in Set.Ioc a b, ENNReal.ofReal (1 / Real.pi) * ENNReal.ofReal (g e)
  rw [hreal]
  rw [lintegral_const_mul]
  · rw [ENNReal.ofReal_mul (by positivity)]
    rw [intervalIntegral.integral_of_le hab,
      ofReal_integral_eq_lintegral_ofReal hg.integrableOn_Ioc
        (Filter.Eventually.of_forall hnonneg)]
  · exact hg.measurable.ennreal_ofReal

/-- Measurability of the full regulated trace in the public sample. -/
theorem measurable_publicBlockRegulatedTrace_sample {k : ℕ}
    (dims : Fin k → ℕ) (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (e eta : ℝ) (heta : 0 < eta) :
    Measurable (publicBlockRegulatedTrace A₀ e eta) := by
  unfold publicBlockRegulatedTrace
  apply Measurable.ennreal_ofReal
  have hfun : (fun G : BlockGUE.PublicBlockSample dims =>
      -((((((publicBlockDeformation A₀ G).1 -
        (e : ℂ) • (1 : Matrix (BlockGUE.Index dims)
          (BlockGUE.Index dims) ℂ)) + Complex.I • (eta •
        (1 : Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ)))⁻¹).trace).im)) =
      fun G => ∑ r : Fin (Fintype.card (BlockGUE.Index dims)),
        eta / ((orderedEigenvalue (publicBlockDeformation A₀ G) r - e) ^ 2 + eta ^ 2) := by
    funext G
    exact neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
      (publicBlockDeformation A₀ G) e heta
  rw [hfun]
  apply Finset.measurable_sum
  intro r hr
  have hlam := (measurable_orderedEigenvalue r).comp
    (measurable_publicBlockDeformation dims A₀)
  exact measurable_const.div
    (((hlam.sub measurable_const).pow_const 2).add measurable_const)

/-- Tonelli and the regulated trace bound give a bound on the expected Perron approximant by the
interval length times `π⁻¹ π C₀ ∑ⱼ dims j`; this is the input for the Fatou limit `n → ∞`. -/
theorem lintegral_publicBlockPerronApprox_le_of_singleBlockDOS {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hDOS : SingleBlockDOS C₀)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    (∫⁻ G, publicBlockPerronApprox A₀ a b n G
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
      ENNReal.ofReal (b - a) *
        (ENNReal.ofReal (1 / Real.pi) *
          ENNReal.ofReal (Real.pi * C₀ * ∑ j, (dims j : ℝ))) := by
  rw [show (fun G => publicBlockPerronApprox A₀ a b n G) =
      fun G => ∫⁻ e in Set.Ioc a b, publicBlockPerronKernel A₀ n G e by
    funext G
    exact publicBlockPerronApprox_eq_lintegral_Ioc A₀ G n hab]
  apply lintegral_lintegral_Ioc_le_length_mul
    (BlockGUE.publicBlockProductMeasure dims hd)
    (publicBlockPerronKernel A₀ n) hab
  · exact measurable_uncurry_publicBlockPerronKernel dims A₀ n
  · intro e he
    unfold publicBlockPerronKernel
    rw [lintegral_const_mul]
    · gcongr
      exact lintegral_publicBlockRegulatedTrace_le_of_singleBlockDOS
        hC₀ hDOS dims hd A₀ e (canonicalWegnerEta_pos n)
    · exact measurable_publicBlockRegulatedTrace_sample dims A₀ e
        (canonicalWegnerEta n) (canonicalWegnerEta_pos n)

/-- The preceding Perron bound simplifies to `C₀ (∑ⱼ dims j) (b - a)`: the factors `π` and `1/π`
cancel. -/
theorem lintegral_publicBlockPerronApprox_le_sharp {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hDOS : SingleBlockDOS C₀)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    (∫⁻ G, publicBlockPerronApprox A₀ a b n G
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
      ENNReal.ofReal (C₀ * (∑ j, (dims j : ℝ)) * (b - a)) := by
  calc
    _ ≤ ENNReal.ofReal (b - a) *
        (ENNReal.ofReal (1 / Real.pi) *
          ENNReal.ofReal (Real.pi * C₀ * ∑ j, (dims j : ℝ))) :=
      lintegral_publicBlockPerronApprox_le_of_singleBlockDOS
        hC₀ hDOS dims hd A₀ hab n
    _ = ENNReal.ofReal (C₀ * (∑ j, (dims j : ℝ)) * (b - a)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.pi),
        ← ENNReal.ofReal_mul (sub_nonneg.mpr hab)]
      congr 1
      field_simp [Real.pi_ne_zero]

end PSSSNative.BlockBand.PSSS
