module
public import BlockBand.SourceProcess.Stochastic.Bridges.Concat
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Products of continuous semimartingales with a given cross bracket

* `IsContinuousSemimartingale.concat`: if `Y₁` (dimension `d₁`, characteristics `(β₁, α₁)`)
  and `Y₂` (dimension `d₂`, `(β₂, α₂)`) are continuous semimartingales, `γ` is a progressive
  `d₁ × d₂` matrix process with a.s. locally integrable entries, and the **cross bracket
  clause is supplied**: along some localizing sequence `ρ_n` of stopping times (`ρ_n → ⊤` a.s.)
  the stopped `N₁^i N₂^j - ∫ γ^{ij}` have martingale modifications. Then the concatenation
  `(Y₁, Y₂)` (through `finSumFinEquiv`) is a continuous semimartingale with drift `(β₁, β₂)`
  and block covariance `[[α₁, γ], [γᵀ, α₂]]`. The localizing sequence is
  `τ₁_n ∧ τ₂_n ∧ ρ_n`. Nothing is claimed about the cross bracket without the hypothesis.
-/

namespace BlockBand.SourceProcess.Stochastic.Bridges
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {d₁ d₂ : ℕ}

omit [MeasurableSpace Ω] in
theorem min_min_swap {α : Type*} [LinearOrder α] (a b c : α) :
    min a (min b c) = min (min a c) b :=
  le_antisymm (le_min (le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_right _ _)))
    ((min_le_right _ _).trans (min_le_left _ _)))
    (le_min ((min_le_left _ _).trans (min_le_left _ _))
      (le_min (min_le_right _ _) ((min_le_left _ _).trans (min_le_right _ _))))

/-- **Concatenation with a given cross bracket.** -/
theorem _root_.BlockBand.Internal.Contracts.Transmission.IsContinuousSemimartingale.concat
    {Y₁ β₁ : ℝ≥0 → Ω → Fin d₁ → ℝ} {α₁ : ℝ≥0 → Ω → Matrix (Fin d₁) (Fin d₁) ℝ}
    {Y₂ β₂ : ℝ≥0 → Ω → Fin d₂ → ℝ} {α₂ : ℝ≥0 → Ω → Matrix (Fin d₂) (Fin d₂) ℝ}
    (H₁ : IsContinuousSemimartingale Q 𝓖 Y₁ β₁ α₁)
    (H₂ : IsContinuousSemimartingale Q 𝓖 Y₂ β₂ α₂)
    {γ : ℝ≥0 → Ω → Matrix (Fin d₁) (Fin d₂) ℝ} (hγ : IsStronglyProgressive 𝓖 γ)
    (hγi : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∀ i j,
      IntegrableOn (fun s : ℝ => γ s.toNNReal ω i j) (Ioc 0 t))
    (hcross : ∃ ρ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime 𝓖 (ρ n)) ∧
      (∀ᵐ ω ∂Q, Tendsto (fun n => ρ n ω) atTop (𝓝 ⊤)) ∧ ∀ n i j,
        HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω =>
          smCompensated Y₁ β₁ i t ω * smCompensated Y₂ β₂ j t ω -
            ∫ s in Ioc (0 : ℝ) t, γ s.toNNReal ω i j) (ρ n))) :
    IsContinuousSemimartingale Q 𝓖 (fun t ω => concatCoord (Y₁ t ω) (Y₂ t ω))
      (fun t ω => concatCoord (β₁ t ω) (β₂ t ω))
      (fun t ω => concatCov (α₁ t ω) (γ t ω) (α₂ t ω)) := by
  obtain ⟨τ₁, hτ₁, hτ₁l, hm₁⟩ := H₁.localizing
  obtain ⟨τ₂, hτ₂, hτ₂l, hm₂⟩ := H₂.localizing
  obtain ⟨ρ, hρ, hρl, hmc⟩ := hcross
  have hc₁ : ∀ᵐ ω ∂Q, ∀ i, Continuous fun t => smCompensated Y₁ β₁ i t ω := by
    filter_upwards [H₁.continuous, H₁.integrable] with ω hω hi i
    exact continuous_smCompensated hω fun t => (hi t).1 i
  have hc₂ : ∀ᵐ ω ∂Q, ∀ i, Continuous fun t => smCompensated Y₂ β₂ i t ω := by
    filter_upwards [H₂.continuous, H₂.integrable] with ω hω hi i
    exact continuous_smCompensated hω fun t => (hi t).1 i
  have hI : ∀ {m n : ℕ} {a : ℝ≥0 → Ω → Matrix (Fin m) (Fin n) ℝ},
      (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∀ i j, IntegrableOn (fun s : ℝ => a s.toNNReal ω i j) (Ioc 0 t)) →
      ∀ᵐ ω ∂Q, ∀ i j, Continuous fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, a s.toNNReal ω i j :=
    fun {_ _ a} ha => by
      filter_upwards [ha] with ω hω i j
      exact continuous_setIntegral_Ioc (g := fun u => a u ω i j) fun t => hω t i j
  have hA₁ := hI (H₁.integrable.mono fun ω h t => (h t).2)
  have hA₂ := hI (H₂.integrable.mono fun ω h t => (h t).2)
  have hG := hI hγi
  refine ⟨fun t => continuous_concatCoord.comp_stronglyMeasurable
      ((H₁.adapted t).prodMk (H₂.adapted t)),
    fun t => continuous_concatCoord.comp_stronglyMeasurable
      ((H₁.progressive t).prodMk (H₂.progressive t)), ?_,
    fun t => continuous_concatCoord.comp_stronglyMeasurable
      ((H₁.drift_progressive t).prodMk (H₂.drift_progressive t)),
    fun t => continuous_concatCov.comp_stronglyMeasurable
      (((H₁.cov_progressive t).prodMk (hγ t)).prodMk (H₂.cov_progressive t)), ?_,
    ⟨fun n ω => min (τ₁ n ω) (min (τ₂ n ω) (ρ n ω)),
      fun n => (hτ₁ n).min ((hτ₂ n).min (hρ n)), ?_, fun n => ⟨fun k => ?_, fun k l => ?_⟩⟩⟩
  · filter_upwards [H₁.continuous, H₂.continuous] with ω h1 h2
    exact continuous_concatCoord.comp (h1.prodMk h2)
  · filter_upwards [H₁.integrable, H₂.integrable, hγi] with ω h1 h2 h3 t
    refine ⟨fun k => ?_, fun k l => ?_⟩
    · obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
      cases s with
      | inl i => simpa only [concatCoord_inl] using (h1 t).1 i
      | inr j => simpa only [concatCoord_inr] using (h2 t).1 j
    · obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
      obtain ⟨s', rfl⟩ := finSumFinEquiv.surjective l
      cases s <;> cases s' <;> simp only [concatCov_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.transpose_apply]
      · exact (h1 t).2 _ _
      · exact h3 t _ _
      · exact h3 t _ _
      · exact (h2 t).2 _ _
  · filter_upwards [hτ₁l, hτ₂l, hρl] with ω a b c
    exact tendsto_min_top a (tendsto_min_top b c)
  · obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
    cases s with
    | inl i =>
      rw [smCompensated_concat_inl]
      exact hasMartingaleModification_stopped_min ((hm₁ n).1 i) (hc₁.mono fun _ h => h i)
        ((hτ₂ n).min (hρ n)) fun ω => min_comm _ _
    | inr j =>
      rw [smCompensated_concat_inr]
      exact hasMartingaleModification_stopped_min ((hm₂ n).1 j) (hc₂.mono fun _ h => h j)
        ((hτ₁ n).min (hρ n)) fun ω => min_min_swap _ _ _
  · obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
    obtain ⟨s', rfl⟩ := finSumFinEquiv.surjective l
    cases s with
    | inl i =>
      cases s' with
      | inl j =>
        refine hasMartingaleModification_stopped_congr
          (hasMartingaleModification_stopped_min ((hm₁ n).2 i j) ?_ ((hτ₂ n).min (hρ n))
            fun ω => min_comm _ _) (ae_of_all _ fun ω t => ?_)
        · filter_upwards [hc₁, hA₁] with ω h1 h2
          exact ((h1 i).mul (h1 j)).sub (h2 i j)
        · simp only [smCompensated, concatCoord_inl, concatCov_apply,
            Matrix.fromBlocks_apply₁₁]
      | inr j =>
        refine hasMartingaleModification_stopped_congr
          (hasMartingaleModification_stopped_min (hmc n i j) ?_ ((hτ₁ n).min (hτ₂ n))
            fun ω => (min_assoc _ _ _).symm) (ae_of_all _ fun ω t => ?_)
        · filter_upwards [hc₁, hc₂, hG] with ω h1 h2 h3
          exact ((h1 i).mul (h2 j)).sub (h3 i j)
        · simp only [smCompensated, concatCoord_inl, concatCoord_inr, concatCov_apply,
            Matrix.fromBlocks_apply₁₂]
    | inr i =>
      cases s' with
      | inl j =>
        refine hasMartingaleModification_stopped_congr
          (hasMartingaleModification_stopped_min (hmc n j i) ?_ ((hτ₁ n).min (hτ₂ n))
            fun ω => (min_assoc _ _ _).symm) (ae_of_all _ fun ω t => ?_)
        · filter_upwards [hc₁, hc₂, hG] with ω h1 h2 h3
          exact ((h1 j).mul (h2 i)).sub (h3 j i)
        · simp only [smCompensated, concatCoord_inl, concatCoord_inr, concatCov_apply,
            Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
          ring
      | inr j =>
        refine hasMartingaleModification_stopped_congr
          (hasMartingaleModification_stopped_min ((hm₂ n).2 i j) ?_ ((hτ₁ n).min (hρ n))
            fun ω => min_min_swap _ _ _)
          (ae_of_all _ fun ω t => ?_)
        · filter_upwards [hc₂, hA₂] with ω h1 h2
          exact ((h1 i).mul (h1 j)).sub (h2 i j)
        · simp only [smCompensated, concatCoord_inr, concatCov_apply,
            Matrix.fromBlocks_apply₂₂]

/-- **Concatenation with an absolutely continuous process** (as for `Y = (λ, v)` in the relative
localization lemma): no cross hypothesis is needed and the covariance is
`[[α, 0], [0, 0]]`. -/
theorem _root_.BlockBand.Internal.Contracts.Transmission.IsContinuousSemimartingale.concat_ac
    {Y β : ℝ≥0 → Ω → Fin d₁ → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d₁) (Fin d₁) ℝ}
    (H : IsContinuousSemimartingale Q 𝓖 Y β α) {v vd : ℝ≥0 → Ω → Fin d₂ → ℝ}
    (hprog : IsStronglyProgressive 𝓖 v) (hvd : IsStronglyProgressive 𝓖 vd)
    (hac : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∀ i, IntegrableOn (fun s : ℝ => vd s.toNNReal ω i) (Ioc 0 t) ∧
      v t ω i = v 0 ω i + ∫ s in Ioc (0 : ℝ) t, vd s.toNNReal ω i) :
    IsContinuousSemimartingale Q 𝓖 (fun t ω => concatCoord (Y t ω) (v t ω))
      (fun t ω => concatCoord (β t ω) (vd t ω)) (fun t ω => concatCov (α t ω) 0 0) := by
  have hzero : ∀ᵐ ω ∂Q, ∀ j t, smCompensated v vd j t ω = 0 := by
    filter_upwards [hac] with ω hω j t
    simp only [smCompensated, (hω t j).2]; ring
  refine H.concat (isContinuousSemimartingale_of_ac hprog hvd hac) (γ := fun _ _ => 0)
    (isStronglyProgressive_const _ _) (ae_of_all _ fun _ _ _ _ => by simp)
    ⟨fun _ _ => ⊤, fun _ => isStoppingTime_top_const, ae_of_all _ fun _ => tendsto_const_nhds,
      fun n i j => ?_⟩
  refine hasMartingaleModification_congr hasMartingaleModification_zero fun t => ?_
  filter_upwards [hzero] with ω hω
  simp [stoppedProcess_eq_stopTime, hω]

end BlockBand.SourceProcess.Stochastic.Bridges
