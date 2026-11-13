module

public import BlockBand.DeterminantScore.GUENormTailProof
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Fixed operator-norm moments of `GUE`

**`gueNormMoment`**: for every `q > 0` there is `C_q ≥ 0` with, for every finite `ι` and
`t ≥ 0`, `∫⁻ ofReal(‖G‖^q) dGUE_ι(t) ≤ ofReal(C_q (t(|ι|+1))^{q/2})` (Euclidean operator norm
`Matrix.Norms.L2Operator`); explicitly `C_q = 170^q (1 + 2qΓ(q))`.

Proof: with `σ = 170√(t|ι|)`, the layer-cake formula for `‖G‖/σ`, the level bound `1` on
`(0,1]` and `GUE{σu < ‖G‖} ≤ 2^{28|ι|} e^{-σ²u²/(512t)} ≤ 2e^{-u}` on `(1,∞)`, and
`∫_0^∞ 2e^{-u}u^{q-1} du = 2Γ(q)`. The cases `|ι| = 0` and `t = 0` are trivial (`G = 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.GUENormTail

open MeasureTheory Set BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-- `∫_{(0,1]} u^{r-1} du = 1/r`. -/
theorem lintegral_Ioc_rpow' {r : ℝ} (hr : 0 < r) :
    (∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ (r - 1))) = ENNReal.ofReal (1 / r) := by
  have hi : IntegrableOn (fun u : ℝ => u ^ (r - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r - 1)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : -1 < r - 1))]
    congr 1
    rw [show r - 1 + 1 = r by ring, Real.one_rpow, Real.zero_rpow hr.ne']
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact Real.rpow_nonneg hu.1.le _

/-- `∫_0^∞ 2e^{-u} u^{p-1} du = 2Γ(p)`, as a lower integral. -/
theorem lintegral_two_exp_rpow {p : ℝ} (hp : 0 < p) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.exp (-s)) * ENNReal.ofReal (s ^ (p - 1)) =
      ENNReal.ofReal (2 * Real.Gamma p) := by
  have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi hp one_pos
  simp only [one_mul, div_one, Real.one_rpow] at hval
  have hI : IntegrableOn (fun s : ℝ => s ^ (p - 1) * Real.exp (-s)) (Ioi 0) := by
    by_contra h
    have h0 := integral_undef h
    rw [hval] at h0
    have := Real.Gamma_pos_of_pos hp
    linarith
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun s : ℝ => 2 * (s ^ (p - 1) * Real.exp (-s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have := Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < s from hs)) (p - 1)
    positivity
  have h := ofReal_integral_eq_lintegral_ofReal (hI.const_mul 2) hnn
  rw [integral_const_mul, hval] at h
  rw [h]
  refine lintegral_congr fun s => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  ring_nf

/-- The moment constant `170^q (1 + 2qΓ(q))`. -/
def gueMomentConst (q : ℝ) : ℝ := 170 ^ q * (1 + 2 * q * Real.Gamma q)

theorem gueMomentConst_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ gueMomentConst q := by
  unfold gueMomentConst
  have := Real.Gamma_pos_of_pos hq
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ 170 by norm_num) q
  positivity

/-- **Fixed operator-norm moments of `GUE`**. -/
theorem gueNormMoment_le {q : ℝ} (hq : 0 < q) (ι : Type) [Fintype ι] [DecidableEq ι]
    (t : ℝ≥0) :
    ∫⁻ G, ENNReal.ofReal (‖G‖ ^ q) ∂gueMeasure ι t ≤
      ENNReal.ofReal (gueMomentConst q * ((t : ℝ) * (Fintype.card ι + 1)) ^ (q / 2)) := by
  have hprob : IsProbabilityMeasure (gueMeasure ι t) := by
    unfold gueMeasure commonCircularIncrementLaw
    infer_instance
  set n := Fintype.card ι
  have hnm : Measurable fun G : Matrix ι ι ℂ => ‖G‖ := continuous_norm.measurable
  -- trivial cases
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hn
    have h0 : ∀ G : Matrix ι ι ℂ, ENNReal.ofReal (‖G‖ ^ q) = 0 := fun G => by
      have hG : G = 0 := Subsingleton.elim _ _
      simp [hG, Real.zero_rpow hq.ne']
    simp only [h0, lintegral_zero]
    exact zero_le
  rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with ht | ht
  · subst ht
    unfold gueMeasure
    rw [lintegral_map (hnm.pow_const q).ennreal_ofReal (continuous_gueSample' 0).measurable]
    have h0 : ∀ X : ι × ι → ℂ, ENNReal.ofReal (‖gueSample (ι := ι) 0 X‖ ^ q) = 0 := fun X => by
      have hX : gueSample (ι := ι) 0 X = 0 := by
        ext a b
        simp [gueSample]
      simp [hX, Real.zero_rpow hq.ne']
    simp only [h0, lintegral_zero]
    exact zero_le
  -- main case
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set σ : ℝ := 170 * Real.sqrt ((t : ℝ) * n)
  have hσ : 0 < σ := by
    have : 0 < Real.sqrt ((t : ℝ) * n) := Real.sqrt_pos.2 (by positivity)
    positivity
  set μ := gueMeasure ι t
  set f : Matrix ι ι ℂ → ℝ := fun G => ‖G‖ / σ
  have hfm : Measurable f := hnm.div_const σ
  -- rescaling
  have hscale : ∫⁻ G, ENNReal.ofReal (‖G‖ ^ q) ∂μ =
      ENNReal.ofReal (σ ^ q) * ∫⁻ G, ENNReal.ofReal (f G ^ q) ∂μ := by
    rw [← lintegral_const_mul _ (hfm.pow_const q).ennreal_ofReal]
    refine lintegral_congr fun G => ?_
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hσ.le _)]
    congr 1
    simp only [f]
    rw [Real.div_rpow (norm_nonneg _) hσ.le]
    field_simp
  -- level bounds
  have hlev1 : ∀ u : ℝ, μ {G | u < f G} ≤ 1 := fun u => prob_le_one
  have hlev2 : ∀ u : ℝ, 1 < u →
      μ {G | u < f G} ≤ ENNReal.ofReal (2 * Real.exp (-u)) := by
    intro u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    have hsub : {G : Matrix ι ι ℂ | u < f G} ⊆ {G | 4 * (σ * u / 4) < ‖G‖} := by
      intro G hG
      simp only [Set.mem_ofPred_eq, f] at hG ⊢
      rw [lt_div_iff₀ hσ] at hG
      linarith
    refine (measure_mono hsub).trans ((gueMeasure_norm_tail_le t htR hn
      (u := σ * u / 4) (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_))
    have hsq : (σ * u / 4) ^ 2 / (2 * (16 * t)) = (28900 / 512) * n * u ^ 2 := by
      simp only [σ]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
      ring
    rw [hsq]
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have hu2 : 1 ≤ u ^ 2 := by nlinarith
    calc (2 : ℝ) ^ (28 * n) * Real.exp (-(28900 / 512 * n * u ^ 2))
        ≤ Real.exp 1 ^ (28 * n) * Real.exp (-(28900 / 512 * n * u ^ 2)) := by gcongr
      _ = Real.exp (28 * n - 28900 / 512 * n * u ^ 2) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          push_cast
          ring_nf
      _ ≤ Real.exp (-u) := Real.exp_le_exp.2 (by nlinarith)
      _ ≤ 2 * Real.exp (-u) := by linarith [Real.exp_pos (-u)]
  -- layer cake
  have hfnn : 0 ≤ᵐ[μ] f := ae_of_all _ fun G => div_nonneg (norm_nonneg _) hσ.le
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul μ hfnn hfm.aemeasurable hq
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hm1 : Measurable fun u : ℝ => ENNReal.ofReal (u ^ (q - 1)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have I1 : (∫⁻ u in Ioc (0 : ℝ) 1, μ {G | u < f G} * ENNReal.ofReal (u ^ (q - 1))) ≤
      ENNReal.ofReal (1 / q) := by
    calc _ ≤ ∫⁻ u in Ioc (0 : ℝ) 1, 1 * ENNReal.ofReal (u ^ (q - 1)) := by
          refine lintegral_mono fun u => ?_
          gcongr
          exact hlev1 u
      _ = _ := by rw [lintegral_const_mul _ hm1, lintegral_Ioc_rpow' hq, one_mul]
  have I2 : (∫⁻ u in Ioi (1 : ℝ), μ {G | u < f G} * ENNReal.ofReal (u ^ (q - 1))) ≤
      ENNReal.ofReal (2 * Real.Gamma q) := by
    calc _ ≤ ∫⁻ u in Ioi (1 : ℝ),
          ENNReal.ofReal (2 * Real.exp (-u)) * ENNReal.ofReal (u ^ (q - 1)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
          gcongr
          exact hlev2 u hu
      _ ≤ ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (2 * Real.exp (-u)) * ENNReal.ofReal (u ^ (q - 1)) :=
          lintegral_mono_set (Ioi_subset_Ioi zero_le_one)
      _ = _ := lintegral_two_exp_rpow hq
  have hmom : ∫⁻ G, ENNReal.ofReal (f G ^ q) ∂μ ≤ ENNReal.ofReal (1 + 2 * q * Real.Gamma q) := by
    rw [hlayer, hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
    calc _ ≤ ENNReal.ofReal q * (ENNReal.ofReal (1 / q) + ENNReal.ofReal (2 * Real.Gamma q)) := by
          gcongr
      _ = ENNReal.ofReal (1 + 2 * q * Real.Gamma q) := by
          have := Real.Gamma_pos_of_pos hq
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul hq.le]
          congr 1
          field_simp
  rw [hscale]
  calc ENNReal.ofReal (σ ^ q) * ∫⁻ G, ENNReal.ofReal (f G ^ q) ∂μ
      ≤ ENNReal.ofReal (σ ^ q) * ENNReal.ofReal (1 + 2 * q * Real.Gamma q) := by gcongr
    _ = ENNReal.ofReal (σ ^ q * (1 + 2 * q * Real.Gamma q)) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hσ.le _)).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hG := Real.Gamma_pos_of_pos hq
        have hσq : σ ^ q ≤ 170 ^ q * ((t : ℝ) * (n + 1)) ^ (q / 2) := by
          simp only [σ]
          rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
            ← Real.rpow_mul (by positivity), show (1 : ℝ) / 2 * q = q / 2 by ring]
          refine mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)) (by positivity)
        unfold gueMomentConst
        calc σ ^ q * (1 + 2 * q * Real.Gamma q)
            ≤ 170 ^ q * ((t : ℝ) * (n + 1)) ^ (q / 2) * (1 + 2 * q * Real.Gamma q) := by
              gcongr
          _ = _ := by ring

/-- **Fixed operator-norm moments of `GUE`**, existential form: for every `q > 0` there is
`C_q ≥ 0` with `E_{GUE_ι(t)} ‖G‖^q ≤ C_q (t(|ι|+1))^{q/2}` for every finite `ι`, `t ≥ 0`. -/
theorem gueNormMoment (q : ℝ) (hq : 0 < q) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : ℝ≥0),
      ∫⁻ G, ENNReal.ofReal (‖G‖ ^ q) ∂gueMeasure ι t ≤
        ENNReal.ofReal (Cq * ((t : ℝ) * (Fintype.card ι + 1)) ^ (q / 2)) :=
  ⟨gueMomentConst q, gueMomentConst_nonneg hq, fun ι _ _ t => gueNormMoment_le hq ι t⟩

end BlockBand.DeterminantScore.GUENormTail
