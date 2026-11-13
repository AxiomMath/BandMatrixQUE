module

public import BlockBand.SourceProcess.ContractingWords.SummedPath

/-!
# The summed step on the path: moments of the dominating variable

`domM_moments`: every moment of the dominating variable `domM` of a finite set of nonempty words
is bounded uniformly in `W ≥ W₀`, `E` in the bulk, the tag births and `εW ≤ j < TW`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {W nT nI : ℕ}

theorem productValue_single (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (ω : GrowthPath W) (w : TraceWord nT nI) :
    productValue b E k q W j ω [w] = wordValue b E k q W j ω w := by
  simp [productValue]

/-- **Uniform moments of the dominating variable.** -/
theorem domM_moments (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) {b κI : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κI) {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q)
    (S : Finset (TraceWord nT nI)) (hS : ∀ w ∈ S, w ≠ []) {ε T : ℝ} (hε : 0 < ε)
    (hεT : ε < T) (n : ℕ) :
    ∃ (B : ℝ) (W₀ : ℕ), 0 ≤ B ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ (k : Fin nT → ℕ) (j : ℕ), ε * W ≤ j → ((j + 1 : ℕ) : ℝ) ≤ T * W →
        ∫⁻ ω, ENNReal.ofReal (domM b E k q j S ω) ^ n ∂growthPathLaw W b ≤
          ENNReal.ofReal B := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · refine ⟨1, 0, zero_le_one, fun W _ E _ k j _ _ => ?_⟩
    subst hn
    have : IsProbabilityMeasure (growthPathLaw W b) := by
      simp only [growthPathLaw]; infer_instance
    simp
  obtain ⟨C, W₀, hC⟩ := productValue_eLpNorm_le hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq
    (S.sup List.length) ε T n hε hεT (by exact_mod_cast hn)
  set C' := max C 0
  refine ⟨(1 + 2 * S.card * C') ^ n, W₀, by positivity,
    fun W hW E hE k j hj hjT => ?_⟩
  have : IsProbabilityMeasure (growthPathLaw W b) := by
    simp only [growthPathLaw]; infer_instance
  have hj' : ε * W ≤ ((j + 1 : ℕ) : ℝ) := hj.trans (by push_cast; linarith)
  have hjT' : (j : ℝ) ≤ T * W := le_trans (by push_cast; linarith) hjT
  have hpn : ENNReal.ofReal (n : ℝ) = (n : ℝ≥0∞) := ENNReal.ofReal_natCast n
  have hw : ∀ i : ℕ, ε * W ≤ i → (i : ℝ) ≤ T * W → ∀ w ∈ S,
      eLpNorm (fun ω => ‖wordValue b E k q W i ω w‖) (n : ℝ≥0∞) (growthPathLaw W b) ≤
        ENNReal.ofReal C' := by
    intro i hi1 hi2 w hwS
    rw [eLpNorm_norm _ (measurable_wordValue b E k q i w).aestronglyMeasurable, ← hpn]
    have h := hC W hW E hE k i hi1 hi2 [w] (fun v hv => by
      simp only [List.mem_singleton] at hv; rw [hv]; exact hS w hwS)
      (by simp [productDegree]; exact Finset.le_sup (f := List.length) hwS)
    simp only [productValue_single] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hn1 : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
  have hdom : eLpNorm (domM b E k q j S) (n : ℝ≥0∞) (growthPathLaw W b) ≤
      ENNReal.ofReal (1 + 2 * S.card * C') := by
    have e : domM (W := W) b E k q j S = (fun _ => (1 : ℝ)) + ∑ w ∈ S,
        ((fun ω => ‖wordValue b E k q W j ω w‖) +
          fun ω => ‖wordValue b E k q W (j + 1) ω w‖) := by
      funext ω; simp [domM, Finset.sum_apply]
    rw [e]
    refine (eLpNorm_add_le hn1).trans ?_
    have h1 : eLpNorm (fun _ : GrowthPath W => (1 : ℝ)) (n : ℝ≥0∞) (growthPathLaw W b) ≤
        ENNReal.ofReal 1 := by
      refine (eLpNorm_le_of_ae_bound aestronglyMeasurable_const (C := 1)
        (Eventually.of_forall fun _ => by simp)).trans ?_
      simp
    have h2 : eLpNorm (∑ w ∈ S, ((fun ω => ‖wordValue b E k q W j ω w‖) +
        fun ω => ‖wordValue b E k q W (j + 1) ω w‖)) (n : ℝ≥0∞) (growthPathLaw W b) ≤
        ∑ w ∈ S, (ENNReal.ofReal C' + ENNReal.ofReal C') :=
      (eLpNorm_sum_le hn1).trans (Finset.sum_le_sum fun w hwS => (eLpNorm_add_le hn1).trans
        (add_le_add (hw j hj hjT' w hwS) (hw (j + 1) hj' hjT w hwS)))
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_add (le_max_right _ _)
      (le_max_right _ _), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    congr 1; ring
  refine (lintegral_pow_le_of_eLpNorm (fun ω => (zero_le_one.trans (one_le_domM b E k q j S ω)))
    (measurable_domM b E k q j S).aestronglyMeasurable hn hdom).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_pow (by positivity)]

end BlockBand.SourceProcess.ContractingWords
