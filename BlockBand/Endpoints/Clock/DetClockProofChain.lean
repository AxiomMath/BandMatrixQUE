module

public import BlockBand.Endpoints.Clock.DetClockProofDeriv
public import BlockBand.Endpoints.Clock.DetClockStatement

/-!
# The deterministic-clock lemma: integrating the one-step bound along the one-ended chain

* `remainder_eq_integral`: for `a > 0`, `r^D_{W,j}(a) = E stepDefect(X_j, Q_j)` (expectation over
  the first `j` layers): the law of the first `j+1` layers is (past) ⊗ (fresh layer)
  (`ClockMixingProb.measurePreserving_initLast`), the new clock is `Q_{j+1} = L*Q_jL + (q/W²)C`
  (`Q_succ`), Fubini uses the joint measurability of `(past, fresh) ↦ F_a(Q_{j+1})`, and the
  second derivative is taken under the integral (`integral_deriv_deriv`).
* `pastWeight_moment`: `E Λ_j⁹ ≤ B` along the chain, from `OpenInputsMoments` (jets, clock) and
  the clock-mixing lemma (`Z_j`, `√S_j`) at moment order `9`.
* These two results are used in a sibling module to prove `detClockEvolutionD_of`: **the
  deterministic-clock lemma, uniformly in the initial `‖D‖ ≤ ε`**, from `PassiveSourceMixingContract`, `PassiveCovarianceContract`, `GaussianAbsorptionContract`,
  `OnePortWeightedCovarianceContract` and `OpenInputsMoments`. `δ_{W,j} = C W^{-3/2}` for large
  `W`, so `Σ_{j₀ ≤ j ≤ TW} δ_{W,j} = O(W^{-1/2})`. `detClockEvolution_of` is the case `D = 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

namespace DetClockProof

open ClockMixingAlg ClockMixingProb

variable {W : ℕ}

/-!
## 1. The remainder is the expectation of the one-step defect
-/

/-- The new Laplace function as a function of (past, fresh layer). -/
def chainG (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) (a : ℝ)
    (p : (Fin j → OneEndedLayer W) × OneEndedLayer W) : ℝ :=
  detLaplace ((freshL b E (oneEndedX E D j p.1) p.2)ᴴ * oneEndedQ b E q D j p.1 *
      freshL b E (oneEndedX E D j p.1) p.2 +
    (((q (((j + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ)) : ℂ) •
      freshC b E (oneEndedX E D j p.1) p.2) a

/-- **Joint measurability** of `(past, fresh) ↦ F_a(Q_{j+1})` (for Fubini along the chain). -/
theorem measurable_chainG (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (a : ℝ) : Measurable (chainG b E q D j a) := by
  have hp : Measurable (fun p : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      (oneEndedX E D j p.1, p.2)) := ((meas_X E D j).comp measurable_fst).prodMk measurable_snd
  have hL := (meas_freshL (W := W) b E).comp hp
  have hC := (meas_freshC (W := W) b E).comp hp
  have hQ : Measurable (fun p : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      oneEndedQ b E q D j p.1) := (meas_Q b E q D j).comp measurable_fst
  have hM : Measurable (fun p : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      (freshL b E (oneEndedX E D j p.1) p.2)ᴴ * oneEndedQ b E q D j p.1 *
        freshL b E (oneEndedX E D j p.1) p.2 +
      (((q (((j + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ)) : ℂ) •
        freshC b E (oneEndedX E D j p.1) p.2) :=
    (meas_mul (meas_mul (meas_conjTranspose hL) hQ) hL).add (meas_smul _ hC)
  exact measurable_detLaplace hM a

theorem chainG_posSemidef {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (p : (Fin j → OneEndedLayer W) × OneEndedLayer W) :
    ((freshL b E (oneEndedX E D j p.1) p.2)ᴴ * oneEndedQ b E q D j p.1 *
        freshL b E (oneEndedX E D j p.1) p.2 +
      (((q (((j + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ)) : ℂ) •
        freshC b E (oneEndedX E D j p.1) p.2).PosSemidef := by
  have h1 := (Q_posSemidef b E hq D j p.1).conjTranspose_mul_mul_same
    (freshL b E (oneEndedX E D j p.1) p.2)
  refine PosSemidef.add (by simpa [Matrix.mul_assoc] using h1)
    ((freshC_posSemidef b E _ _).smul (Complex.zero_le_real.mpr
      (div_nonneg (hq _) (sq_nonneg _))))

/-- `F_a(Q_{j+1}) = chainG(past, fresh)` (`Q_succ`). -/
theorem detLaplace_succ (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) (a : ℝ)
    (ω : Fin (j + 1) → OneEndedLayer W) :
    detLaplace (oneEndedQ b E q D (j + 1) ω) a = chainG b E q D j a (Fin.init ω, ω (Fin.last j)) := by
  rw [Q_succ]; rfl

/-- **The remainder is the expectation of the one-step defect** (for `a > 0`), and the defect is
integrable along the chain. -/
theorem remainder_eq_integral (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun ω => stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
        (oneEndedQ b E q D j ω)) (oneEndedLaw W b j) ∧
      detClockRemainderD W b E q D j a = ∫ ω, stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a
        (oneEndedX E D j ω) (oneEndedQ b E q D j ω) ∂oneEndedLaw W b j := by
  set qv := q (((j + 1 : ℕ) : ℝ) / W) with hqv
  have hGm : Measurable (chainG b E q D j a) := measurable_chainG b E q D j a
  have hGb : ∀ p, |chainG b E q D j a p| ≤ 1 := fun p => by
    unfold chainG
    rw [abs_of_pos (detLaplace_pos (chainG_posSemidef hq D j p) ha.le)]
    exact detLaplace_le_one (chainG_posSemidef hq D j p) ha.le
  have hGi : Integrable (chainG b E q D j a) ((oneEndedLaw W b j).prod (freshLaw W b)) :=
    Integrable.of_bound hGm.aestronglyMeasurable 1 (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact hGb p)
  have hmp : MeasurePreserving (fun ω : Fin (j + 1) → OneEndedLayer W =>
      (Fin.init ω, ω (Fin.last j))) (oneEndedLaw W b (j + 1))
      ((oneEndedLaw W b j).prod (freshLaw W b)) := measurePreserving_initLast (freshLaw W b) j
  -- `E F_a(Q_{j+1}) = E_past E_fresh G`
  have E1 : openClockLaplaceWD W b E q D (j + 1) a =
      ∫ ω', ∫ ξ, chainG b E q D j a (ω', ξ) ∂freshLaw W b ∂oneEndedLaw W b j := by
    unfold openClockLaplaceWD
    simp_rw [detLaplace_succ]
    have h2 : ∫ ω, chainG b E q D j a (Fin.init ω, ω (Fin.last j)) ∂oneEndedLaw W b (j + 1) =
        ∫ p, chainG b E q D j a p ∂((oneEndedLaw W b j).prod (freshLaw W b)) := by
      rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hGm.aestronglyMeasurable]
    rw [h2, integral_prod _ hGi]
  have hQm := meas_Q b E q D j
  have hQp : ∀ ω, (oneEndedQ b E q D j ω).PosSemidef := Q_posSemidef b E hq D j
  have E3 := integral_deriv_deriv (oneEndedLaw W b j) hQm hQp ha
  -- integrability of the pieces
  have i1 : Integrable (fun ω' => ∫ ξ, chainG b E q D j a (ω', ξ) ∂freshLaw W b)
      (oneEndedLaw W b j) := hGi.integral_prod_left
  have i2 : Integrable (fun ω' => detLaplace (oneEndedQ b E q D j ω') a) (oneEndedLaw W b j) := by
    refine Integrable.of_bound (measurable_detLaplace hQm a).aestronglyMeasurable 1
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (detLaplace_pos (hQp ω) ha.le)]
    exact detLaplace_le_one (hQp ω) ha.le
  have i3 : Integrable (fun ω' => detLaplace (oneEndedQ b E q D j ω') a *
      ((resolventWeight (oneEndedQ b E q D j ω') a).trace.re ^ 2 +
        ((resolventWeight (oneEndedQ b E q D j ω') a) ^ 2).trace.re)) (oneEndedLaw W b j) := by
    refine Integrable.of_bound ?_ (2 * (W : ℝ) ^ 2) (ae_of_all _ fun ω => ?_)
    · refine ((measurable_detLaplace hQm a).mul ?_).aestronglyMeasurable
      refine ((Complex.measurable_re.comp (meas_trace (measurable_resolventWeight hQm a))).pow_const
        2).add (Complex.measurable_re.comp (meas_trace ?_))
      simp only [pow_two]
      exact meas_mul (measurable_resolventWeight hQm a) (measurable_resolventWeight hQm a)
    · have hQ := hQp ω
      have hT0 := re_trace_resolventWeight_nonneg hQ ha.le
      have hT := trace_weight_le_card hQ ha.le
      have hT2 := trace_weight_sq_le hQ ha.le
      have hT20 : 0 ≤ ((resolventWeight (oneEndedQ b E q D j ω) a) ^ 2).trace.re := by
        rw [trace_resolventWeight_sq_eq_sum hQ ha.le, Complex.ofReal_re]; positivity
      have hsq := pow_le_pow_left₀ hT0 hT 2
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (detLaplace_pos hQ ha.le),
        abs_of_nonneg (by positivity)]
      calc _ ≤ 1 * (2 * (W : ℝ) ^ 2) := mul_le_mul (detLaplace_le_one hQ ha.le) (by linarith)
            (by positivity) zero_le_one
        _ = _ := one_mul _
  have hstep : (fun ω => stepDefect W b E qv a (oneEndedX E D j ω) (oneEndedQ b E q D j ω)) =
      fun ω => (∫ ξ, chainG b E q D j a (ω, ξ) ∂freshLaw W b) - detLaplace (oneEndedQ b E q D j ω) a -
        (W : ℝ)⁻¹ * (transportD0 b E / 2 * (detLaplace (oneEndedQ b E q D j ω) a *
          ((resolventWeight (oneEndedQ b E q D j ω) a).trace.re ^ 2 +
            ((resolventWeight (oneEndedQ b E q D j ω) a) ^ 2).trace.re)) -
          dStar b * qv * a * detLaplace (oneEndedQ b E q D j ω) a) := by
    funext ω; rfl
  have iS : Integrable (fun ω => stepDefect W b E qv a (oneEndedX E D j ω)
      (oneEndedQ b E q D j ω)) (oneEndedLaw W b j) := by
    rw [hstep]
    exact (i1.sub i2).sub (((i3.const_mul _).sub (i2.const_mul _)).const_mul _)
  refine ⟨iS, ?_⟩
  rw [hstep]
  have i4 : Integrable (fun ω => transportD0 b E / 2 * (detLaplace (oneEndedQ b E q D j ω) a *
      ((resolventWeight (oneEndedQ b E q D j ω) a).trace.re ^ 2 +
        ((resolventWeight (oneEndedQ b E q D j ω) a) ^ 2).trace.re))) (oneEndedLaw W b j) :=
    i3.const_mul _
  have i5 : Integrable (fun ω => dStar b * qv * a * detLaplace (oneEndedQ b E q D j ω) a)
      (oneEndedLaw W b j) := i2.const_mul _
  have i12 : Integrable (fun ω => (∫ ξ, chainG b E q D j a (ω, ξ) ∂freshLaw W b) -
      detLaplace (oneEndedQ b E q D j ω) a) (oneEndedLaw W b j) := i1.sub i2
  have i45 : Integrable (fun ω => transportD0 b E / 2 * (detLaplace (oneEndedQ b E q D j ω) a *
      ((resolventWeight (oneEndedQ b E q D j ω) a).trace.re ^ 2 +
        ((resolventWeight (oneEndedQ b E q D j ω) a) ^ 2).trace.re)) -
      dStar b * qv * a * detLaplace (oneEndedQ b E q D j ω) a) (oneEndedLaw W b j) := i4.sub i5
  rw [integral_sub i12 (i45.const_mul _), integral_sub i1 i2, integral_const_mul,
    integral_sub i4 i5, integral_const_mul, integral_const_mul, ← E1]
  unfold detClockRemainderD
  rw [hqv]
  unfold openClockLaplaceWD
  unfold openClockLaplaceWD at E1
  linear_combination (-(W : ℝ)⁻¹ * (transportD0 b E / 2)) * E3

/-!
## 2. The moments of the past weight along the chain
-/

/-- `Λ_j = 1 + γ_j + W(δ₀ + δ₁) + √W(|Z_j| + √S_j)` has `E Λ_j⁹ ≤ (1 + g + c + c')⁹` once
`‖γ_j‖₉ ≤ g`, `‖δ₀‖₉ + ‖δ₁‖₉ ≤ c/W`, `‖Z_j‖₉ + ‖√S_j‖₉ ≤ c'/√W`. -/
theorem pastWeight_moment {b E : ℝ} {s : ℂ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    {D : Matrix (Fin W) (Fin W) ℂ} {j : ℕ} (hW : 0 < (W : ℝ)) {g c c' : ℝ} (hg : 0 ≤ g)
    (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hγ : eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) ≤
      ENNReal.ofReal g)
    (hδ : eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal 9)
        (oneEndedLaw W b j) +
      eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal 9)
        (oneEndedLaw W b j) ≤ ENNReal.ofReal (c / W))
    (hZS : eLpNorm (openClockZ b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) +
      eLpNorm (openClockSqrtS b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) ≤
        ENNReal.ofReal (c' / Real.sqrt W)) :
    Integrable (fun ω => pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω) ^ 9)
        (oneEndedLaw W b j) ∧
      ∫ ω, pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω) ^ 9
        ∂oneEndedLaw W b j ≤ (1 + g + c + c') ^ 9 := by
  set μ := oneEndedLaw W b j with hμ
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 9 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hd0 : eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal 9) μ ≤
      ENNReal.ofReal (c / W) := le_trans le_self_add hδ
  have hd1 : eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal 9) μ ≤
      ENNReal.ofReal (c / W) := le_trans le_add_self hδ
  have hd0m := aestronglyMeasurable_of_eLpNorm_ne_top
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd0)
  have hd1m := aestronglyMeasurable_of_eLpNorm_ne_top
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd1)
  have hγm := (meas_gamma b E q D j).aestronglyMeasurable (μ := μ)
  have hZm := (meas_openClockZ b E q D j).aestronglyMeasurable (μ := μ)
  have hSm := (meas_openClockSqrtS b E q D j).aestronglyMeasurable (μ := μ)
  have hsW0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  -- the four pieces
  have b1 : eLpNorm (fun _ : Fin j → OneEndedLayer W => (1 : ℝ)) (ENNReal.ofReal 9) μ ≤
      ENNReal.ofReal 1 := by
    rw [eLpNorm_const_prob _ (by simp)]; simp
  have b3 : eLpNorm (fun ω => (W : ℝ) * (jetDistance0 b E (oneEndedX E D j ω) +
      jetDistance1 b E s (oneEndedX E D j ω))) (ENNReal.ofReal 9) μ ≤ ENNReal.ofReal c := by
    rw [eLpNorm_real_mul_le, abs_of_pos hW]
    have h := (eLpNorm_add_le (f := fun ω => jetDistance0 b E (oneEndedX E D j ω))
      (g := fun ω => jetDistance1 b E s (oneEndedX E D j ω)) hp1).trans hδ
    calc ENNReal.ofReal W * eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω) +
          jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal 9) μ
        ≤ ENNReal.ofReal W * ENNReal.ofReal (c / W) := by gcongr; exact h
      _ = ENNReal.ofReal c := by
        rw [← ENNReal.ofReal_mul hW.le]; congr 1; field_simp
  have b4 : eLpNorm (fun ω => Real.sqrt W * (‖openClockZ b E q D j ω‖ +
      openClockSqrtS b E q D j ω)) (ENNReal.ofReal 9) μ ≤ ENNReal.ofReal c' := by
    rw [eLpNorm_real_mul_le, abs_of_pos hsW0]
    have h1 := eLpNorm_add_le (f := fun ω => ‖openClockZ b E q D j ω‖)
      (g := openClockSqrtS b E q D j) hp1 (μ := μ)
    rw [eLpNorm_norm _ hZm] at h1
    calc ENNReal.ofReal (Real.sqrt W) * eLpNorm (fun ω => ‖openClockZ b E q D j ω‖ +
          openClockSqrtS b E q D j ω) (ENNReal.ofReal 9) μ
        ≤ ENNReal.ofReal (Real.sqrt W) * ENNReal.ofReal (c' / Real.sqrt W) := by
          gcongr; exact h1.trans hZS
      _ = ENNReal.ofReal c' := by
        rw [← ENNReal.ofReal_mul hsW0.le]; congr 1; field_simp
  have hΛe : (fun ω => pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω)) =
      (fun ω => (1 : ℝ) + oneEndedGamma b E q D j ω +
        (W : ℝ) * (jetDistance0 b E (oneEndedX E D j ω) + jetDistance1 b E s (oneEndedX E D j ω)) +
        Real.sqrt W * (‖openClockZ b E q D j ω‖ + openClockSqrtS b E q D j ω)) := by
    funext ω; rfl
  have m3 : AEStronglyMeasurable (fun ω => (W : ℝ) * (jetDistance0 b E (oneEndedX E D j ω) +
      jetDistance1 b E s (oneEndedX E D j ω))) μ := (hd0m.add hd1m).const_mul _
  have m4 : AEStronglyMeasurable (fun ω => Real.sqrt W * (‖openClockZ b E q D j ω‖ +
      openClockSqrtS b E q D j ω)) μ := (hZm.norm.add hSm).const_mul _
  have hΛ : eLpNorm (fun ω => pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω))
      (ENNReal.ofReal 9) μ ≤ ENNReal.ofReal (1 + g + c + c') := by
    rw [hΛe]
    refine (eLpNorm_add_le (μ := μ) (f := fun ω => (1 : ℝ) + oneEndedGamma b E q D j ω +
        (W : ℝ) * (jetDistance0 b E (oneEndedX E D j ω) + jetDistance1 b E s (oneEndedX E D j ω)))
      (g := fun ω => Real.sqrt W * (‖openClockZ b E q D j ω‖ + openClockSqrtS b E q D j ω))
      hp1).trans ?_
    refine (add_le_add (eLpNorm_add_le (μ := μ) (f := fun ω => (1 : ℝ) + oneEndedGamma b E q D j ω)
      (g := fun ω => (W : ℝ) * (jetDistance0 b E (oneEndedX E D j ω) +
        jetDistance1 b E s (oneEndedX E D j ω))) hp1) b4).trans ?_
    refine (add_le_add (add_le_add (eLpNorm_add_le (μ := μ) (f := fun _ => (1 : ℝ))
      (g := oneEndedGamma b E q D j) hp1) b3) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add b1 hγ) le_rfl) le_rfl).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (by norm_num) hg, ← ENNReal.ofReal_add (by positivity) hc,
      ← ENNReal.ofReal_add (by positivity) hc']
  have h := integral_rpow_le (r := 9) (by norm_num) (by positivity) hΛ
  have hnn : ∀ ω, 0 ≤ pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω) := by
    intro ω
    unfold pastWeight
    have h1 := trace_re_nonneg (Q_posSemidef b E hq D j ω)
    have h2 : 0 ≤ jetDistance0 b E (oneEndedX E D j ω) := norm_nonneg _
    have h3 : 0 ≤ jetDistance1 b E s (oneEndedX E D j ω) := norm_nonneg _
    have h4 := hsSandwich_nonneg (oneEndedQ b E q D j ω) (passiveF b E (oneEndedX E D j ω))
    have h5 : 0 ≤ (W : ℝ) * (jetDistance0 b E (oneEndedX E D j ω) +
        jetDistance1 b E s (oneEndedX E D j ω)) := mul_nonneg hW.le (add_nonneg h2 h3)
    have h6 : 0 ≤ Real.sqrt W * (‖(oneEndedQ b E q D j ω * passiveF b E (oneEndedX E D j ω)).trace‖ +
        hsSandwich (oneEndedQ b E q D j ω) (passiveF b E (oneEndedX E D j ω))) :=
      mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (norm_nonneg _) h4)
    linarith
  have he : ∀ ω, |pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω)| ^ (9 : ℝ) =
      pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω) ^ 9 := by
    intro ω
    rw [abs_of_nonneg (hnn ω), show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp_rw [he] at h
  rw [show ((1 + g + c + c') ^ (9 : ℝ)) = (1 + g + c + c') ^ 9 by
    rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]] at h
  exact h

end DetClockProof

end BlockBand.Endpoints.Clock
