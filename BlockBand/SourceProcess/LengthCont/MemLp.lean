module

public import BlockBand.SourceProcess.LengthCont.Pin
public import BlockBand.SourceProcess.ComplexSourceLaw.MomentsLimit

/-!
# The `L²` conjunct of `LayerIncrementBounds` from `RawTagMoments`

`memLp_incr_of_rawTagMoments`: on the domain, for every `T₀`, eventually in `W`, every one-layer
increment of the source coordinates ending at a length `≤ T₀W` is square integrable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw

theorem sq_sourceCoord_le (b E : ℝ) {np : ℕ} (W : ℕ) (τ m : Fin np → ℝ) (r : Fin 4)
    (i k : Fin np) (s : Bool) (n : ℕ) (x : ProbedPath W np) :
    sourceCoord b E W τ m r i k s n x ^ 2 ≤
      sourceDataMoment 2 (complexSourceData b E W n τ m x) := by
  set y := complexSourceData b E W n τ m x
  have h1 : sourceCoord b E W τ m r i k s n x ^ 2 ≤ ‖y r i k‖ ^ 2 := by
    have : |sourceCoord b E W τ m r i k s n x| ≤ ‖y r i k‖ := by
      unfold sourceCoord
      cases s
      · exact Complex.abs_im_le_norm _
      · exact Complex.abs_re_le_norm _
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : ‖y r i k‖ ^ 2 ≤ sourceDataMoment 2 y := by
    unfold sourceDataMoment
    have hnn : ∀ r' i' k', 0 ≤ ‖y r' i' k'‖ ^ (2 : ℝ) := fun _ _ _ => by positivity
    calc ‖y r i k‖ ^ 2 = ‖y r i k‖ ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ ≤ ∑ k', ‖y r i k'‖ ^ (2 : ℝ) :=
          Finset.single_le_sum (f := fun k' => ‖y r i k'‖ ^ (2 : ℝ))
            (fun k' _ => hnn r i k') (Finset.mem_univ k)
      _ ≤ ∑ i', ∑ k', ‖y r i' k'‖ ^ (2 : ℝ) :=
          Finset.single_le_sum (f := fun i' => ∑ k', ‖y r i' k'‖ ^ (2 : ℝ))
            (fun i' _ => Finset.sum_nonneg fun k' _ => hnn r i' k') (Finset.mem_univ i)
      _ ≤ ∑ r', ∑ i', ∑ k', ‖y r' i' k'‖ ^ (2 : ℝ) :=
          Finset.single_le_sum (f := fun r' => ∑ i', ∑ k', ‖y r' i' k'‖ ^ (2 : ℝ))
            (fun r' _ => Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun k' _ =>
              hnn r' i' k') (Finset.mem_univ r)
  exact h1.trans h2

/-- At a length with a raw tag bound at `p = 2`, every source coordinate is in `L²`. -/
theorem memLp_sourceCoord (b E : ℝ) (hη : 0 < etaZ b E) {np : ℕ} (W n : ℕ)
    (τ m : Fin np → ℝ) (hm : ∀ j, 0 ≤ m j) {C : ℝ} (hraw : RawTagBoundAt b E W n 2 C)
    (r : Fin 4) (i k : Fin np) (s : Bool) :
    MemLp (sourceCoord b E W τ m r i k s n) 2 (probedPathLaw W np b) := by
  have hmeas : Measurable (sourceCoord b E W τ m r i k s n) :=
    (measurable_sourceCoord_sigma b E W τ m r i k s n).mono (probedSigma_le W np n) le_rfl
  have hDm : Measurable fun x => sourceDataMoment 2 (complexSourceData b E W n τ m x) := by
    unfold sourceDataMoment
    refine Finset.measurable_sum _ fun r' _ => Finset.measurable_sum _ fun i' _ =>
      Finset.measurable_sum _ fun k' _ => ?_
    exact (Measurable.comp (g := fun y : SourceData np => y r' i' k')
      (measurable_pi_apply r').eval_matrix
        (measurable_complexSourceData b E W n τ m)).norm.pow_const _
  have hfin := (lintegral_sourceDataMoment_le b E hη n τ m hm one_le_two hraw).trans_lt
    (momentBound_ne_top (etaZ b E) 2 C m).lt_top
  have hDint : Integrable (fun x => sourceDataMoment 2 (complexSourceData b E W n τ m x))
      (probedPathLaw W np b) := by
    refine ⟨hDm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by
      unfold sourceDataMoment; positivity)]
    exact hfin
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  refine hDint.mono' (hmeas.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_sourceCoord_le b E W τ m r i k s n x

/-- **The `L²` conjunct of `LayerIncrementBounds` from `RawTagMoments`**: on the domain, for
every `T₀`, eventually in `W`, every one-layer increment ending at a length `≤ T₀W` is in
`L²`. -/
theorem memLp_incr_of_rawTagMoments (hR : RawTagMoments) (b E : ℝ) {np : ℕ}
    (τ m : Fin np → ℝ) (T : ℝ) (hdom : ComplexSourceLawDomain b E τ m T) (T₀ : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≤ T₀ * W →
      ∀ (r : Fin 4) (i k : Fin np) (s : Bool),
        MemLp (incr (sourceCoord b E W τ m r i k s) n) 2 (probedPathLaw W np b) := by
  obtain ⟨hb0, hb1, hE0, hE1, -, -, hm, -⟩ := hdom
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  obtain ⟨C, W₀, hC⟩ := hR b hb0 hb1 κ hκ T₀ 2 one_le_two
  have hη := Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE0 hE1
  refine ⟨W₀, fun W hW n hn r i k s => ?_⟩
  have hn' : (n : ℝ) ≤ T₀ * W := le_trans (by exact_mod_cast Nat.le_succ n) hn
  exact (memLp_sourceCoord b E hη W (n + 1) τ m hm (hC W hW E hEκ (n + 1) hn) r i k s).sub
    (memLp_sourceCoord b E hη W n τ m hm (hC W hW E hEκ n hn') r i k s)

end BlockBand.SourceProcess.LengthCont
