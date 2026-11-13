module

public import BlockBand.SourceProcess.ComplexUniqueSegment.Model

/-!
# `ComplexFiniteUniqueness` from the joint segment law

The joint segment law `JointSegmentLaw` (between births, the one-time joint law of `(G, 𝒦)`
propagates from a deterministic anchor) implies finite uniqueness `ComplexFiniteUniqueness`.

`complexFiniteUniqueness_of_segment : JointSegmentLaw → ComplexFiniteUniqueness`. Proof:
* time 0: the law of `(G(0), 𝒦(0))` is fixed by the entrance law (`model_map_zero`);
* by strong induction on the number of births `τ_j - s ≤ t`, the one-time joint laws agree at
  every `t ≥ 0`: with no birth in `[0, t]` apply `JointSegmentLaw` from anchor `0`; otherwise
  let `u = max {τ_j - s ≤ t} > 0`. At every `t' < u` fewer births have occurred, so the laws
  agree there; subtracting the deterministic jump and letting `t' ↑ u` along the a.s.
  continuous paths of `(G, 𝒦) - (J, J_𝒦)` (`map_eq_of_forall_lt`) gives equal laws of
  `(G, 𝒦)(u) - (J, J_𝒦)(u)`, hence of `(G, 𝒦)(u)`; then apply `JointSegmentLaw` from the
  deterministic anchor `u` (no birth in `(u, t]`);
* at `(T - s)⁺`, `Φ ∘ modelSourceData` is bounded continuous, so equal laws give equal
  `modelExpectation`.

Only the hypotheses `0 < s`, `s < τ_j` of the domain are used (injectivity of `τ`, `τ_j < T`
and the cutoff `h > 0` are not needed for this half).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUniqueSegment

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.ComplexSplit
open scoped NNReal

attribute [local instance] matrix_pseudoMetrizable matrix_secondCountable jointState_borel
  gramState_borel'

/-- **Finite uniqueness from the joint segment law**: the joint segment law `JointSegmentLaw`
(between births, the one-time joint law of `(G, 𝒦)` propagates from a deterministic anchor)
implies finite uniqueness `ComplexFiniteUniqueness` (same `(b, E, s, τ, m, h, K)` and entrance
law give the same expectation of every bounded continuous test of the final source data). -/
theorem complexFiniteUniqueness_of_segment (h : BlockBand.SourceProcess.ComplexSplit.JointSegmentLaw) :
    BlockBand.SourceProcess.ComplexSourceLaw.ComplexFiniteUniqueness := by
  intro b E np τ m T hdom s hs hτ hc hcpos K entrance Φ Ω₁ m₁ 𝓖₁ Q₁ tseq₁ G₁ K₁ hM₁
    Ω₂ m₂ 𝓖₂ Q₂ tseq₂ G₂ K₂ hM₂
  have := hM₁.prob
  have := hM₂.prob
  -- `S t`: equal one-time joint laws at `t`.
  let S : ℝ≥0 → Prop := fun t =>
    Q₁.map (fun ω => (G₁ t ω, K₁ t ω)) = Q₂.map (fun ω => (G₂ t ω, K₂ t ω))
  have hseg : ∀ a t : ℝ≥0, a ≤ t → (∀ j, ¬ ((a : ℝ) < τ j - s ∧ τ j - s ≤ (t : ℝ))) →
      S a → S t := fun a t hat hj =>
    h b E np τ m T hdom s hs hτ K Ω₁ m₁ 𝓖₁ Q₁ G₁ K₁ hM₁.prob hM₁.solution hM₁.complex
      Ω₂ m₂ 𝓖₂ Q₂ G₂ K₂ hM₂.prob hM₂.solution hM₂.complex a t hat hj
  have h0 : S 0 := by
    change Q₁.map _ = Q₂.map _
    rw [model_map_zero hM₁, model_map_zero hM₂]
  have hempty : ∀ t : ℝ≥0, (∀ j, ¬ τ j - s ≤ (t : ℝ)) → S t := fun t ht =>
    hseg 0 t bot_le (fun j hj => ht j hj.2) h0
  -- Births: the left limit, then the deterministic jump.
  have hbirth : ∀ u : ℝ≥0, 0 < u → (∀ t < u, S t) → S u := by
    intro u hu hlt
    have hsub : ∀ c : JointState K np, Measurable fun y : JointState K np => y - c :=
      fun c => (continuous_id.sub continuous_const).measurable
    have hadd : ∀ c : JointState K np, Measurable fun y : JointState K np => y + c :=
      fun c => (continuous_id.add continuous_const).measurable
    have hX := map_eq_of_forall_lt
      (X₁ := fun t ω => (G₁ t ω, K₁ t ω) - jointJump b E s τ m K t)
      (X₂ := fun t ω => (G₂ t ω, K₂ t ω) - jointJump b E s τ m K t)
      (fun t => (hsub _).comp (model_measurable_joint hM₁ t))
      (fun t => (hsub _).comp (model_measurable_joint hM₂ t))
      (model_continuous_joint hM₁) (model_continuous_joint hM₂) hu
      (fun t ht => map_comp_eq (model_measurable_joint hM₁ t) (model_measurable_joint hM₂ t)
        (hsub (jointJump b E s τ m K t)) (hlt t ht))
    have := map_comp_eq ((hsub _).comp (model_measurable_joint hM₁ u))
      ((hsub _).comp (model_measurable_joint hM₂ u)) (hadd (jointJump b E s τ m K u)) hX
    simpa only [Function.comp_apply, sub_add_cancel] using this
  -- Strong induction on the number of births up to `t`.
  have hall : ∀ n : ℕ, ∀ t : ℝ≥0,
      (Finset.univ.filter fun j => τ j - s ≤ (t : ℝ)).card ≤ n → S t := by
    intro n
    induction n with
    | zero =>
      intro t ht
      refine hempty t fun j hj => ?_
      have hmem : j ∈ Finset.univ.filter fun j => τ j - s ≤ (t : ℝ) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 ht)] at hmem
      simp at hmem
    | succ n ih =>
      intro t ht
      by_cases hne : (Finset.univ.filter fun j => τ j - s ≤ (t : ℝ)).Nonempty
      · obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image _ (fun j => τ j - s) hne
        have hj₀t : τ j₀ - s ≤ (t : ℝ) := (Finset.mem_filter.1 hj₀).2
        have hpos : 0 < τ j₀ - s := sub_pos.2 (hτ j₀)
        set u : ℝ≥0 := (τ j₀ - s).toNNReal with hu_def
        have hu : (u : ℝ) = τ j₀ - s := Real.coe_toNNReal _ hpos.le
        have hut : u ≤ t := by rw [← NNReal.coe_le_coe, hu]; exact hj₀t
        have hSu : S u := by
          refine hbirth u (by rw [← NNReal.coe_pos, hu]; exact hpos) fun t' ht' => ih t' ?_
          have ht'u : (t' : ℝ) < τ j₀ - s := by rw [← hu]; exact_mod_cast ht'
          have hss : (Finset.univ.filter fun j => τ j - s ≤ (t' : ℝ)) ⊂
              (Finset.univ.filter fun j => τ j - s ≤ (t : ℝ)) := by
            refine (Finset.ssubset_iff_of_subset ?_).2 ⟨j₀, hj₀, ?_⟩
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
              have : (t' : ℝ) ≤ t := by
                have := ht'.le.trans hut
                exact_mod_cast this
              linarith
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
              exact ht'u
          exact Nat.lt_succ_iff.1 ((Finset.card_lt_card hss).trans_le ht)
        refine hseg u t hut (fun j hj => ?_) hSu
        have := hmax j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj.2⟩)
        rw [hu] at hj
        linarith [hj.1]
      · exact hempty t fun j hj => hne ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
  -- Evaluation at `T - s`.
  have hT : S (T - s).toNNReal := hall _ _ le_rfl
  have hψ : Measurable fun y : JointState K np =>
      Φ (modelSourceData (srcSignature K (Fin np)) y.2 y.1) :=
    (Φ.continuous.comp (continuous_modelSourceData _)).measurable
  unfold modelExpectation
  rw [← integral_map (model_measurable_joint hM₁ _).aemeasurable hψ.aestronglyMeasurable,
    ← integral_map (model_measurable_joint hM₂ _).aemeasurable hψ.aestronglyMeasurable]
  exact congrArg (fun μ => ∫ y, Φ (modelSourceData (srcSignature K (Fin np)) y.2 y.1) ∂μ) hT

/-- `ComplexSplit.SplitTarget`, i.e. `complexFiniteUniqueness_of_segment` as a `Prop`. -/
theorem splitTarget_holds : BlockBand.SourceProcess.ComplexSplit.SplitTarget :=
  complexFiniteUniqueness_of_segment

example : BlockBand.SourceProcess.ComplexSplit.SplitTarget :=
  (complexFiniteUniqueness_of_segment : BlockBand.SourceProcess.ComplexSplit.SplitTarget)

end BlockBand.SourceProcess.ComplexUniqueSegment
