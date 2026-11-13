module

public import BlockBand.SourceProcess.ContractingWords.EarlyPins
public import BlockBand.SourceProcess.ContractingWords.SummedMain

/-!
# The summed step with any tag births

`summedStepAll_of`: `SummedStepAll` follows from the per-word drift, covariance and increment
bounds with any births (`OrdinaryDriftStepAll`, `OrdinaryCovStepAll`, `OrdinaryIncrementAll`),
through a Taylor expansion of the polynomial in the words and moment bounds for the words.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory MvPolynomial
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open scoped ENNReal

/-- **`SummedStepAll`** from the input hypotheses and the per-word hypotheses with any births
(through `summedStep_of`; the birth hypothesis is only passed to the per-word hypotheses).
-/
theorem summedStepAll_of (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hD : OrdinaryDriftStepAll)
    (hCv : OrdinaryCovStepAll) (hI : OrdinaryIncrementAll) : SummedStepAll := by
  intro b hb0 hb κI hκ nT nI q hq Φ hΦ ε T K hε hεT
  have hSord : ∀ w ∈ Φ.vars, IsOrdinaryWord w := hΦ
  have hSne : ∀ w ∈ Φ.vars, w ≠ [] := fun w hw => (hΦ w hw).1
  have hlen : ∀ w ∈ Φ.vars, w.length ≤ Φ.vars.sup List.length := fun w hw =>
    Finset.le_sup (f := List.length) hw
  choose Cf Nf hCf hTf using fun Ψ : TracePoly nT nI => taylor_bound Φ.vars Ψ
  obtain ⟨f1, f2, f3, f4, f5⟩ := momIdx_facts Nf Φ
  choose Bm Wm hBm0 hBm using fun n =>
    domM_moments hMT hGA hLp hSR hb0 hb hκ hq Φ.vars hSne hε hεT n
  obtain ⟨C1, ρ1, W1, hC1, hρ1, hρ1', hD'⟩ :=
    hD b hb0 hb κI hκ nT nI q hq (Φ.vars.sup List.length) ε T K hε hεT
  obtain ⟨C2, ρ2, W2, hC2, hρ2, hρ2', hC'⟩ :=
    hCv b hb0 hb κI hκ nT nI q hq (Φ.vars.sup List.length) ε T K hε hεT
  obtain ⟨C3, W3, hC3, hI'⟩ :=
    hI b hb0 hb κI hκ nT nI q hq (Φ.vars.sup List.length) ε T K 6 hε hεT (by norm_num)
  have hsq : ∀ n, 0 ≤ Bm n ^ (1 / 2 : ℝ) := fun n => Real.rpow_nonneg (hBm0 n) _
  have hK1 : 0 ≤ kOne Cf Nf (fun n => Bm n ^ (1 / 2 : ℝ)) Φ :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hCf _) (hsq _)
  have hK2 : 0 ≤ kTwo Cf Nf (fun n => Bm n ^ (1 / 2 : ℝ)) Φ :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hCf _) (hsq _)
  have hK3 : 0 ≤ kThree Cf Nf (fun n => Bm n ^ (1 / 2 : ℝ)) Φ := by
    unfold kThree; have := hCf Φ; have := hsq (2 * Nf Φ); positivity
  have hK4 : 0 ≤ kFour Cf Nf (fun n => Bm n ^ (1 / 2 : ℝ)) Φ := Finset.sum_nonneg fun p _ =>
    mul_nonneg (mul_nonneg (hCf _) (hCf _)) (hsq _)
  have hK5 : 0 ≤ kFive Cf Nf (fun n => Bm n ^ (1 / 2 : ℝ)) Φ := by
    unfold kFive; have := hsq (2 * (2 * Nf Φ + 3)); positivity
  have hCm : 0 ≤ max C1 C2 := le_max_of_le_left hC1
  have hρ0 : 0 ≤ max ρ1 ρ2 := le_max_of_le_left hρ1
  refine ⟨(kOne Cf Nf (fun n => Bm n ^ (1 / 2 : ℝ)) Φ + kTwo Cf Nf (fun n => Bm n ^ (1 / 2 : ℝ)) Φ +
      kFour Cf Nf (fun n => Bm n ^ (1 / 2 : ℝ)) Φ) * max C1 C2 +
      (kThree Cf Nf (fun n => Bm n ^ (1 / 2 : ℝ)) Φ + kFive Cf Nf (fun n => Bm n ^ (1 / 2 : ℝ)) Φ) *
        C3 ^ 3, max ρ1 ρ2,
    max (max W1 W2) (max W3 (max ((Finset.range (momIdx Nf Φ + 1)).sup Wm) 1)),
    by positivity, hρ0, max_lt hρ1' hρ2', fun W hW E hE k j hj hjk hjT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW3, hWmax, hW1'⟩ := hW
  have hWm : ∀ n ≤ momIdx Nf Φ, Wm n ≤ W := fun n hn =>
    (Finset.le_sup (f := Wm) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))).trans hWmax
  have hmB : ∀ n ≤ momIdx Nf Φ, ∫⁻ ω, ENNReal.ofReal (domM b E k q j Φ.vars ω) ^ n
      ∂growthPathLaw W b ≤ ENNReal.ofReal (Bm n) := fun n hn =>
    hBm n W (hWm n hn) E hE k j hj hjT
  have hmom : ∀ n ≤ momIdx Nf Φ, ∫⁻ ω, ENNReal.ofReal (domM b E k q j Φ.vars ω) ^ n
      ∂growthPathLaw W b ≠ ⊤ := fun n hn => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmB n hn)
  have hT : ∀ n, 2 * n ≤ momIdx Nf Φ → momT (growthPathLaw W b) (domM b E k q j Φ.vars) n ≤
      ENNReal.ofReal ((fun n => Bm n ^ (1 / 2 : ℝ)) (2 * n)) := fun n hn =>
    momT_le (hBm0 _) (hmB _ hn)
  have h1 := fun w (hw : w ∈ Φ.vars) =>
    hD' W hW1 E hE k j hj hjk hjT w (hSord w hw) (hlen w hw)
  have h2 := fun (p : TraceWord nT nI × TraceWord nT nI) (hp : p ∈ Φ.vars ×ˢ Φ.vars) =>
    hC' W hW2 E hE k j hj hjk hjT p.1 p.2 (hSord _ (Finset.mem_product.mp hp).1)
      (hSord _ (Finset.mem_product.mp hp).2) (hlen _ (Finset.mem_product.mp hp).1)
      (hlen _ (Finset.mem_product.mp hp).2)
  have h3 : ∀ w ∈ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator (wordInc b E k q W j w)) 6
      (growthPathLaw W b) ≤ ENNReal.ofReal (C3 / Real.sqrt W) := fun w hw => by
    have := hI' W hW3 E hE k j hj hjk hjT w (hSord w hw) (hlen w hw)
    rwa [show ENNReal.ofReal 6 = 6 by norm_num] at this
  have hb1 := first_step_bound b E k q K ε j Φ hCf hTf hmom f1 f2 (by omega) hsq hT hW1' hC1
    hρ1 hC2 hρ2 hC3 (le_max_left C1 C2) (le_max_right C1 C2) (le_max_left ρ1 ρ2)
    (le_max_right ρ1 ρ2) h1 h2 h3
  have hb2 := second_step_bound b E k q K ε j Φ hCf hTf hmom f4 f5 hsq hT hW1' hC2 hρ2 hC3
    (le_max_right C1 C2) (le_max_right ρ1 ρ2) h2 h3
  refine ⟨hb1.trans (ENNReal.ofReal_le_ofReal (stepErr_mono ?_ (by positivity) hρ0 le_rfl)),
    hb2.trans (ENNReal.ofReal_le_ofReal (stepErr_mono ?_ (by positivity) hρ0 le_rfl))⟩
  · nlinarith [mul_nonneg hK4 hCm, mul_nonneg hK5 (pow_nonneg hC3 3)]
  · nlinarith [mul_nonneg hK1 hCm, mul_nonneg hK2 hCm, mul_nonneg hK3 (pow_nonneg hC3 3)]

end BlockBand.SourceProcess.ContractingWords
