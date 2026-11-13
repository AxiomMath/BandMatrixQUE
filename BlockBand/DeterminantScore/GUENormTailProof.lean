module

public import BlockBand.DeterminantScore.GUENormTail
public import BlockBand.DeterminantScore.GUENormTailProofGauss
public import BlockBand.DeterminantScore.GUENormTailProofNet

/-!
# Exponential operator-norm tail of `GUE` (proof)

**`gueNormTail_holds`**: with `C = 128`, `c = 1`, for every finite `ι` and `t ≥ 0`,
`GUE_ι(t){G | 128 √(t |ι|) < ‖G‖} ≤ e^{-|ι|}` (Euclidean operator norm
`Matrix.Norms.L2Operator`, `gueMeasure` of `CoareaPalm`).

**`gueMeasure_norm_tail_le`**: the sub-Gaussian form valid at every level: for `t > 0`,
`|ι| > 0` and `u ≥ 0`, `GUE_ι(t){G | 4u < ‖G‖} ≤ 2^{28|ι|} e^{-u²/(32 t)}`.

Proof: `S` a `1/4`-net of the unit ball of `ℂ^ι` by vectors of norm `≤ 2`, `|S| ≤ 2^{14|ι|}`
(`exists_net`); `‖G‖ ≤ 4 max_{s,s' ∈ S} Re(s'* G s)` (`opNorm_le_of_net`); for fixed `s, s'`,
`Re(s'* G s)` is a linear form of the standard real Gaussian coordinates of
`commonCircularIncrementLaw ι 1` with variance `≤ t ‖s‖²‖s'‖² ≤ 16 t`, so Chernoff gives
`P(Re(s'* G s) > u) ≤ e^{-u²/(32t)}` (`gueMeasure_bil_tail`); union bound over `S × S`. At
`u = 32 √(t|ι|)`: `2^{28|ι|} e^{-32|ι|} ≤ e^{-|ι|}`. The cases `|ι| = 0` (`G = 0`) and `t = 0`
(`G = 0` surely) are trivial.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.GUENormTail

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open scoped NNReal ENNReal Matrix.Norms.L2Operator InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inner_toEuclideanCLM_eq_bil (G : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    ⟪y, toEuclideanCLM (n := ι) (𝕜 := ℂ) G x⟫_ℂ = bil (WithLp.ofLp y) (WithLp.ofLp x) G := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanCLM]
  simp only [bil, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul]

omit [DecidableEq ι] in
theorem sum_normSq_ofLp (s : EuclideanSpace ℂ ι) :
    ∑ a, Complex.normSq (WithLp.ofLp s a) = ‖s‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun a _ => (Complex.sq_norm _).symm

/-- **Sub-Gaussian operator-norm tail at every level** (with the net factor `2^{28|ι|}`). -/
theorem gueMeasure_norm_tail_le (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hn : 0 < Fintype.card ι)
    {u : ℝ} (hu : 0 ≤ u) :
    gueMeasure ι t {G | 4 * u < ‖G‖} ≤
      ENNReal.ofReal (2 ^ (28 * Fintype.card ι) * Real.exp (-(u ^ 2 / (2 * (16 * t))))) := by
  set n := Fintype.card ι
  obtain ⟨S, hcard, hS2, hcov⟩ := exists_net hn
  have hsub : {G : Matrix ι ι ℂ | 4 * u < ‖G‖} ⊆
      ⋃ p ∈ S ×ˢ S, {G | u < (bil (WithLp.ofLp p.2) (WithLp.ofLp p.1) G).re} := by
    intro G hG
    by_contra hno
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hno
    have hle := opNorm_le_of_net (toEuclideanCLM (n := ι) (𝕜 := ℂ) G) S hS2 hcov hu
      (fun s hs s' hs' => by
        rw [inner_toEuclideanCLM_eq_bil]
        exact hno (s, s') (Finset.mem_product.2 ⟨hs, hs'⟩))
    rw [← cstar_norm_def] at hle
    exact absurd hG (not_lt.2 hle)
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ p ∈ S ×ˢ S,
      gueMeasure ι t {G | u < (bil (WithLp.ofLp p.2) (WithLp.ofLp p.1) G).re} ≤
        ENNReal.ofReal (Real.exp (-(u ^ 2 / (2 * (16 * t))))) := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    refine gueMeasure_bil_tail t (WithLp.ofLp p.2) (WithLp.ofLp p.1) hu (by positivity) ?_
    rw [sum_normSq_ofLp, sum_normSq_ofLp]
    have a1 : ‖p.1‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg p.1, hS2 _ h1]
    have a2 : ‖p.2‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg p.2, hS2 _ h2]
    calc (t : ℝ) * ‖p.2‖ ^ 2 * ‖p.1‖ ^ 2 ≤ t * 4 * 4 := by gcongr
      _ = 16 * t := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  push_cast
  calc (S.card : ℝ) * S.card ≤ 2 ^ (14 * n) * 2 ^ (14 * n) :=
        mul_le_mul hcard hcard (by positivity) (by positivity)
    _ = 2 ^ (28 * n) := by rw [← pow_add]; ring_nf

/-- **Exponential operator-norm tail of `GUE`** (`GUENormTailStatement`), with `C = 128`, `c = 1`. -/
theorem gueNormTail_holds : GUENormTailStatement := by
  refine ⟨128, 1, by norm_num, by norm_num, fun ι _ _ t => ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · have hE : {G : Matrix ι ι ℂ |
        128 * Real.sqrt ((t : ℝ) * (Fintype.card ι : ℝ)) < ‖G‖} = ∅ := by
      have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hn
      ext G
      have hG : G = 0 := Subsingleton.elim _ _
      simp [hG]
    rw [hE, measure_empty]
    exact zero_le
  rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with ht | ht
  · subst ht
    have hE : MeasurableSet {G : Matrix ι ι ℂ |
        128 * Real.sqrt (((0 : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) < ‖G‖} :=
      measurableSet_lt measurable_const continuous_norm.measurable
    unfold gueMeasure
    rw [Measure.map_apply (continuous_gueSample' 0).measurable hE]
    have hpre : gueSample (ι := ι) 0 ⁻¹' {G : Matrix ι ι ℂ |
        128 * Real.sqrt (((0 : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) < ‖G‖} = ∅ := by
      ext X
      have h0 : gueSample (ι := ι) 0 X = 0 := by
        ext a b
        simp [gueSample]
      simp [h0]
    rw [hpre, measure_empty]
    exact zero_le
  · have htR : (0 : ℝ) < t := by exact_mod_cast ht
    set n := Fintype.card ι
    have h := gueMeasure_norm_tail_le t htR hn (u := 32 * Real.sqrt ((t : ℝ) * n)) (by positivity)
    have e1 : 4 * (32 * Real.sqrt ((t : ℝ) * n)) = 128 * Real.sqrt ((t : ℝ) * n) := by ring
    rw [e1] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : (32 * Real.sqrt ((t : ℝ) * n)) ^ 2 / (2 * (16 * t)) = 32 * n := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
      ring
    rw [hsq]
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    calc (2 : ℝ) ^ (28 * n) * Real.exp (-(32 * n))
        ≤ Real.exp 1 ^ (28 * n) * Real.exp (-(32 * n)) := by gcongr
      _ = Real.exp (-(4 * n)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          push_cast
          ring_nf
      _ ≤ Real.exp (-(1 * n)) := Real.exp_le_exp.2 (by
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          linarith)

end BlockBand.DeterminantScore.GUENormTail
