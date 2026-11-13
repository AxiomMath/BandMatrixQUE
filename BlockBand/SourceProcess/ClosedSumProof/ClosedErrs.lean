module

public import BlockBand.SourceProcess.ClosedSumProof.ClosedModulus

/-!
# Window sums of the closed errors from `ClosedSummed` and `ClosedFourth`

If `closedSummedErr … e (swapE e) ≤ ε` and `closedFourthErr … e ≤ ε` at width `W`, then on every
window `[j₁, j₁ + L) ⊆ [n_s, ⌊WT⌋)` the drift, bracket, birth and fourth-moment integrands of
`closed_modulus_fixed` are integrable and their window sums are at most `max ε 0`
(`window_errs`, proved in the sibling module `ClosedWindow`). The cap event is replaced by its Borel version (`closedAlive_ae_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ClosingAux
open scoped ENNReal

theorem measurable_drift_comp {c α : Type*} [Fintype c] [MeasurableSpace α] (D0 : ℝ)
    (D : Matrix c c ℂ) (e : Fin 2 × c × c) {G : α → GramState c} (hG : Measurable G) :
    Measurable fun a => gramDriftEntry D0 D e (G a) := by
  have hM : Measurable fun a => (G a).1 := measurable_fst.comp hG
  have hB : Measurable fun a => (G a).2 := measurable_snd.comp hG
  unfold gramDriftEntry gramScalar
  split_ifs
  · exact measurable_const
  · exact (measurable_const.mul (measurable_const.mul (measurable_trace (measurable_matrix_mul'
      (measurable_matrix_mul' (measurable_matrix_mul' measurable_const hM) measurable_const)
        hM)))).neg.mul hB.eval_matrix

theorem measurable_cov_comp {c α : Type*} [Fintype c] [MeasurableSpace α] (D0 : ℝ)
    (D : Matrix c c ℂ) (e e' : Fin 2 × c × c) {G : α → GramState c} (hG : Measurable G) :
    Measurable fun a => gramCovEntry D0 D e e' (G a) := by
  have hM : Measurable fun a => (G a).1 := measurable_fst.comp hG
  have hB : Measurable fun a => (G a).2 := measurable_snd.comp hG
  have hX : ∀ {X Y : α → Matrix c c ℂ}, Measurable X → Measurable Y →
      Measurable fun a => (G a).2 + X a * D * Y a := fun hX hY =>
    measurable_matrix_add hB (measurable_matrix_mul' (measurable_matrix_mul' hX measurable_const) hY)
  have hcb : ∀ {Cl Cr : α → Matrix c c ℂ}, Measurable Cl → Measurable Cr → ∀ i j k l,
      Measurable fun a => crossedBracket D0 (G a).2 (Cl a) (Cr a) i j k l := fun hl hr i j k l => by
    unfold crossedBracket
    exact measurable_const.mul ((hB.eval_matrix.mul hl.eval_matrix).add
      (hr.eval_matrix.mul hB.eval_matrix))
  unfold gramCovEntry BlockBand.SourceProcess.gramC0 BlockBand.SourceProcess.gramC1
    BlockBand.SourceProcess.gramC2
  rcases e with ⟨e1, e2⟩; rcases e' with ⟨f1, f2⟩
  fin_cases e1 <;> fin_cases f1
  · exact hcb (hX hM hM) (hX hM hM) _ _ _ _
  · exact hcb (measurable_matrix_conjTranspose' (hX hM hB)) (hX hM hB) _ _ _ _
  · exact hcb (measurable_matrix_conjTranspose' (hX hM hB)) (hX hM hB) _ _ _ _
  · exact hcb (hX hB hB) (hX hB hB) _ _ _ _

/-- A summed `ℓ¹` bound over the steps gives window integrability and the window sum. -/
theorem window_of_steps {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (U : ℕ → Ω → ℂ)
    (steps : Finset ℕ) (j₁ L N ℓ : ℕ) (hU : ∀ i < L, AEStronglyMeasurable (U (j₁ + i)) μ)
    (hs : ∀ i < L, j₁ + i ∈ steps) (hNL : L ≤ N * ℓ) {ε : ℝ}
    (hB : ∑ j ∈ steps, ∫⁻ y, ‖U j y‖ₑ ∂μ ≤ ENNReal.ofReal ε) (φ : ℕ → Ω → ℝ)
    (hφ : ∀ k < L, φ k = fun y => ‖U (j₁ + k) y‖) (hφ0 : ∀ k, ¬ k < L → φ k = 0) :
    (∀ k < L, Integrable (φ k) μ) ∧ ∑ i ∈ range (N * ℓ), ∫ y, φ i y ∂μ ≤ max ε 0 := by
  have hsub : (range L).map (addLeftEmbedding j₁) ⊆ steps := fun j hj => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact hs i (Finset.mem_range.mp hi)
  have hle : ∑ i ∈ range L, ∫⁻ y, ‖U (j₁ + i) y‖ₑ ∂μ ≤ ENNReal.ofReal ε := by
    refine le_trans ?_ hB
    have e := Finset.sum_map (range L) (addLeftEmbedding j₁) (fun j => ∫⁻ y, ‖U j y‖ₑ ∂μ)
    simp only [addLeftEmbedding_apply] at e
    rw [← e]
    exact Finset.sum_le_sum_of_subset hsub
  have hfin : ∀ i < L, ∫⁻ y, ‖U (j₁ + i) y‖ₑ ∂μ ≠ ⊤ := fun i hi =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((Finset.single_le_sum (f := fun i =>
      ∫⁻ y, ‖U (j₁ + i) y‖ₑ ∂μ) (fun _ _ => zero_le) (Finset.mem_range.mpr hi)).trans hle)
  have hint : ∀ i < L, Integrable (U (j₁ + i)) μ := fun i hi => ⟨hU i hi, (hfin i hi).lt_top⟩
  refine ⟨fun k hk => by rw [hφ k hk]; exact (hint k hk).norm, ?_⟩
  have hsplit : ∑ i ∈ range (N * ℓ), ∫ y, φ i y ∂μ = ∑ i ∈ range L, ∫ y, ‖U (j₁ + i) y‖ ∂μ := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hNL) fun i _ hi => by
      rw [hφ0 i (fun h => hi (Finset.mem_range.mpr h))]; simp]
    exact Finset.sum_congr rfl fun i hi => by rw [hφ i (Finset.mem_range.mp hi)]
  rw [hsplit, Finset.sum_congr rfl fun i hi =>
    integral_norm_eq_lintegral_enorm (hU i (Finset.mem_range.mp hi)),
    ← ENNReal.toReal_sum fun i hi => hfin i (Finset.mem_range.mp hi), ← ENNReal.toReal_ofReal']
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hle

variable {W p K M : ℕ} {b E s T h : ℝ} {q : Fin p → ℝ → ℝ} {R : ℝ}
  {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
  (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M))

/-- The three sums of `closedSummedErr`, displayed. -/
theorem closedSummedErr_eq (e' : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) :
    closedSummedErr b E s T h q R W Vs e e' =
      (∑ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∫⁻ y,
        ‖(closedAlive b E s T h q R W j Vs ∩ noBirth j).indicator (fun y =>
          (lawW b T q M W)[(closedAlive b E s T h q R W j Vs ∩ noBirth j).indicator (fun y =>
            zc b E s T h q W Vs e (j + 1) y - zc b E s T h q W Vs e j y) |
              closedSigma W j p M] y - (W : ℂ)⁻¹ * gramDriftEntry (transportD0 b E)
                (srcSignature K (Fin p × Fin M)) e (closedGramAt b E s T h q W j Vs y)) y‖ₑ
          ∂lawW b T q M W) +
      (∑ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∫⁻ y,
        ‖(closedAlive b E s T h q R W j Vs ∩ noBirth j).indicator (fun y =>
          (lawW b T q M W)[(closedAlive b E s T h q R W j Vs ∩ noBirth j).indicator (fun y =>
            (zc b E s T h q W Vs e (j + 1) y - zc b E s T h q W Vs e j y) *
              (zc b E s T h q W Vs e' (j + 1) y - zc b E s T h q W Vs e' j y)) |
              closedSigma W j p M] y - (W : ℂ)⁻¹ * gramCovEntry (transportD0 b E)
                (srcSignature K (Fin p × Fin M)) e e' (closedGramAt b E s T h q W j Vs y)) y‖ₑ
          ∂lawW b T q M W) +
      (∑ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∫⁻ y,
        ‖(closedAlive b E s T h q R W j Vs \ noBirth j).indicator (fun y =>
          gramEntry e (closedGramAt b E s T h q W (j + 1) Vs y - closedGramAt b E s T h q W j Vs y -
            birthAt b s T q j y)) y‖ₑ ∂lawW b T q M W) := rfl

theorem ofReal_inv_natCast (W : ℕ) : (((W : ℝ)⁻¹ : ℝ) : ℂ) = (W : ℂ)⁻¹ := by push_cast; rfl

theorem gramEntry_sum {c ι : Type*} (e : Fin 2 × c × c) (S : Finset ι) (X : ι → GramState c) :
    gramEntry e (∑ i ∈ S, X i) = ∑ i ∈ S, gramEntry e (X i) := by
  unfold gramEntry
  split_ifs
  · rw [Prod.fst_sum, Matrix.sum_apply]
  · rw [Prod.snd_sum, Matrix.sum_apply]

theorem measurable_gramEntry_birthAt (b s T : ℝ) (q : Fin p → ℝ → ℝ) (j : ℕ) :
    Measurable fun y : SampledPath W p M × ℝ => gramEntry e (birthAt (K := K) b s T q j y) := by
  simp only [birthAt, gramEntry_sum]
  refine Finset.measurable_sum _ fun il _ => ?_
  have hS : MeasurableSet {y : SampledPath W p M × ℝ | y.1.2.1 il = j} := by
    have hm : Measurable fun y : SampledPath W p M × ℝ => y.1.2.1 il :=
      (measurable_pi_apply il).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
    exact hm (measurableSet_singleton j)
  have e1 : (fun y : SampledPath W p M × ℝ => gramEntry e (if y.1.2.1 il = j then
      ((((dStar b * sourceMass s T (q il.1) / M : ℝ)) : ℂ) •
        Matrix.single (Sum.inr il : SrcCol K (Fin p × Fin M)) (Sum.inr il) 1,
      (((dStar b * sourceMass s T (q il.1) / M : ℝ)) : ℂ) •
        Matrix.single (Sum.inr il : SrcCol K (Fin p × Fin M)) (Sum.inr il) 1) else 0)) =
      {y : SampledPath W p M × ℝ | y.1.2.1 il = j}.piecewise
        (fun _ => gramEntry e ((((dStar b * sourceMass s T (q il.1) / M : ℝ)) : ℂ) •
        Matrix.single (Sum.inr il : SrcCol K (Fin p × Fin M)) (Sum.inr il) 1,
      (((dStar b * sourceMass s T (q il.1) / M : ℝ)) : ℂ) •
        Matrix.single (Sum.inr il : SrcCol K (Fin p × Fin M)) (Sum.inr il) 1))
        (fun _ => gramEntry e (0 : GramState (SrcCol K (Fin p × Fin M)))) := by
    funext y
    by_cases hy : y.1.2.1 il = j
    · simp [Set.piecewise, hy]
    · simp [Set.piecewise, hy]
  rw [e1]
  exact Measurable.piecewise hS measurable_const measurable_const

end BlockBand.SourceProcess.ClosedSumProof
