module

public import BlockBand.SourceProcess.FullSourceGenerator.TightBlocks

/-!
# The discrete modulus with finitely many birth corrections (abstract)

`modulus_births`: if on an event `S` every step of a real process `X` equals a martingale-type
step `d_i` (with the inputs of `modulus_tail`) up to an error `|·| ≤ β_i`, then the
probability that on `S` some window of length `ℓ` moves by more than `3λ + ℓa + κ + κ'` is at most
the bound of `modulus_tail` plus the Markov term `Σ E β_i / κ'`. For the closed Gram process `β_i` is the birth
error of `ClosedSummed` at the (finitely many) birth steps.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Finset
open BlockBand.SourceProcess.FullSourceGenerator

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (G : ℕ → MeasurableSpace Ω) (hG : ∀ i, G i ≤ m0) (hGmono : Monotone G)

include hG hGmono in
/-- **The discrete modulus with birth corrections.** -/
theorem modulus_births (N ℓ : ℕ) (hℓ : 0 < ℓ) (X : ℕ → Ω → ℝ) (S : Set Ω)
    (d f g β : ℕ → Ω → ℝ) (c a lam κ κ' : ℝ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hlam : 0 < lam) (hκ : 0 < κ) (hκ' : 0 < κ')
    (hdm : ∀ i, StronglyMeasurable[G (i + 1)] (d i))
    (hd4 : ∀ i < N * ℓ, Integrable (fun ω => d i ω ^ 4) μ)
    (hf0 : ∀ i ω, 0 ≤ f i ω) (hf : ∀ i < N * ℓ, Integrable (f i) μ)
    (hvar : ∀ i < N * ℓ, μ[fun ω => d i ω ^ 2 | G i] ≤ᵐ[μ] fun ω => c + f i ω)
    (hg0 : ∀ i ω, 0 ≤ g i ω) (hg : ∀ i < N * ℓ, Integrable (g i) μ)
    (hdrift : ∀ i < N * ℓ, ∀ᵐ ω ∂μ, |μ[d i | G i] ω| ≤ a + g i ω)
    (hβ0 : ∀ i ω, 0 ≤ β i ω) (hβ : ∀ i < N * ℓ, Integrable (β i) μ)
    (hstep : ∀ ω ∈ S, ∀ i < N * ℓ, |X (i + 1) ω - X i ω - d i ω| ≤ β i ω) :
    μ {ω | ω ∈ S ∧ ∃ x y, x ≤ y ∧ y ≤ N * ℓ ∧ y ≤ x + ℓ ∧
        3 * lam + ℓ * a + κ + κ' < |X y ω - X x ω|} ≤
      ENNReal.ofReal ((16 * c ^ 2 * ((N : ℝ) * ℓ) * ℓ +
          16 * (∑ i ∈ range (N * ℓ), ∫ ω, f i ω ∂μ) ^ 2 +
          8 * lam ^ 2 * ∑ i ∈ range (N * ℓ), ∫ ω, f i ω ∂μ +
          48 * ∑ i ∈ range (N * ℓ), ∫ ω, d i ω ^ 4 ∂μ) / lam ^ 4) +
        ENNReal.ofReal ((∑ i ∈ range (N * ℓ), ∫ ω, g i ω ∂μ) / κ) +
        ENNReal.ofReal ((∑ i ∈ range (N * ℓ), ∫ ω, β i ω ∂μ) / κ') := by
  set S1 : Set Ω := {ω | κ' ≤ ∑ i ∈ range (N * ℓ), β i ω}
  have hincl : {ω | ω ∈ S ∧ ∃ x y, x ≤ y ∧ y ≤ N * ℓ ∧ y ≤ x + ℓ ∧
        3 * lam + ℓ * a + κ + κ' < |X y ω - X x ω|} ⊆
      {ω | ∃ x y, x ≤ y ∧ y ≤ N * ℓ ∧ y ≤ x + ℓ ∧
        3 * lam + ℓ * a + κ < |∑ i ∈ Finset.Ico x y, d i ω|} ∪ S1 := by
    intro ω ⟨hS, x, y, hxy, hyN, hyx, hgt⟩
    by_cases h1 : ω ∈ S1
    · exact Or.inr h1
    refine Or.inl ⟨x, y, hxy, hyN, hyx, ?_⟩
    simp only [S1, Set.mem_ofPred_eq, not_le] at h1
    have hsub : Finset.Ico x y ⊆ range (N * ℓ) := fun i hi =>
      Finset.mem_range.mpr ((Finset.mem_Ico.mp hi).2.trans_le hyN)
    have htel : X y ω - X x ω = ∑ i ∈ Finset.Ico x y, d i ω +
        ∑ i ∈ Finset.Ico x y, (X (i + 1) ω - X i ω - d i ω) := by
      rw [← Finset.sum_add_distrib]
      simp only [add_sub_cancel]
      rw [Finset.sum_Ico_eq_sub _ hxy, Finset.sum_range_sub (fun k => X k ω),
        Finset.sum_range_sub (fun k => X k ω)]; ring
    have hr : |∑ i ∈ Finset.Ico x y, (X (i + 1) ω - X i ω - d i ω)| ≤
        ∑ i ∈ range (N * ℓ), β i ω :=
      (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i hi =>
        hstep ω hS i (Finset.mem_range.mp (hsub hi))).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hβ0 i ω))
    have := abs_add_le (∑ i ∈ Finset.Ico x y, d i ω)
      (∑ i ∈ Finset.Ico x y, (X (i + 1) ω - X i ω - d i ω))
    rw [← htel] at this
    linarith
  have hβI : Integrable (fun ω => ∑ i ∈ range (N * ℓ), β i ω) μ :=
    integrable_finsetSum _ fun i hi => hβ i (Finset.mem_range.mp hi)
  have hS1 : μ S1 ≤ ENNReal.ofReal ((∑ i ∈ range (N * ℓ), ∫ ω, β i ω ∂μ) / κ') := by
    have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun ω =>
      Finset.sum_nonneg fun i _ => hβ0 i ω) hβI κ'
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hκ', ← integral_finsetSum _ fun i hi => hβ i (Finset.mem_range.mp hi)]
    linarith
  refine (measure_mono hincl).trans ((measure_union_le _ _).trans (add_le_add ?_ hS1))
  exact modulus_tail G hG hGmono N ℓ hℓ d f g c a lam κ hc ha hlam hκ hdm hd4 hf0 hf hvar hg0 hg
    hdrift

end BlockBand.SourceProcess.ClosedSumProof
