module
public import BlockBand.SourceProcess.Stochastic.Bridges.Structural
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Concatenation of continuous semimartingales and absolutely continuous processes

* `isContinuousSemimartingale_of_ac`: a progressive process `v` with progressive derivative
  `vd`, whose paths are a.s. `v_t = v_0 + ∫_0^t vd` with `vd` locally integrable, is a
  continuous semimartingale with drift `vd` and covariance `0`.
* `isContinuousSemimartingale_deterministic`: a deterministic `g_t = g_0 + ∫_0^t g'`
  (`g'` Borel, locally integrable) is a continuous semimartingale in `ℝ¹` with drift `g'`.
* `IsContinuousSemimartingale.concat`, proved in the sibling module from the coordinates and
  stopping lemmas here: two continuous semimartingales `Y₁, Y₂` and a
  progressive, a.s. locally integrable cross-covariance `γ` **for which the cross bracket
  clause is given** (along some localizing sequence, the stopped
  `N₁^i N₂^j - ∫ γ^{ij}` have martingale modifications) give the concatenated semimartingale
  with block covariance `[[α₁, γ], [γᵀ, α₂]]`. The localizing sequence is the minimum of the
  three given ones (optional stopping for modifications, `exists_martingale_stoppedProcess`).
-/

namespace BlockBand.SourceProcess.Stochastic.Bridges
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {d d₁ d₂ : ℕ}

/-!
### Coordinates of a concatenation
-/

/-- Joined coordinates `(u, v) ∈ ℝ^{d₁} × ℝ^{d₂} ↦ ℝ^{d₁+d₂}` through `finSumFinEquiv`. -/
def concatCoord (u : Fin d₁ → ℝ) (v : Fin d₂ → ℝ) : Fin (d₁ + d₂) → ℝ :=
  fun k => Sum.elim u v (finSumFinEquiv.symm k)

/-- Block covariance `[[a₁, γ], [γᵀ, a₂]]` in the joined coordinates. -/
def concatCov (a₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (γ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (a₂ : Matrix (Fin d₂) (Fin d₂) ℝ) : Matrix (Fin (d₁ + d₂)) (Fin (d₁ + d₂)) ℝ :=
  Matrix.of fun k l => Matrix.fromBlocks a₁ γ γᵀ a₂ (finSumFinEquiv.symm k) (finSumFinEquiv.symm l)

theorem concatCoord_inl (u : Fin d₁ → ℝ) (v : Fin d₂ → ℝ) (i : Fin d₁) :
    concatCoord u v (finSumFinEquiv (Sum.inl i)) = u i := by simp [concatCoord]

theorem concatCoord_inr (u : Fin d₁ → ℝ) (v : Fin d₂ → ℝ) (j : Fin d₂) :
    concatCoord u v (finSumFinEquiv (Sum.inr j)) = v j := by simp [concatCoord]

@[simp] theorem concatCoord_castAdd (u : Fin d₁ → ℝ) (v : Fin d₂ → ℝ) (i : Fin d₁) :
    concatCoord u v (Fin.castAdd d₂ i) = u i := by simp [concatCoord]

@[simp] theorem concatCoord_natAdd (u : Fin d₁ → ℝ) (v : Fin d₂ → ℝ) (j : Fin d₂) :
    concatCoord u v (Fin.natAdd d₁ j) = v j := by simp [concatCoord]

theorem concatCov_apply (a₁ : Matrix (Fin d₁) (Fin d₁) ℝ)
    (γ : Matrix (Fin d₁) (Fin d₂) ℝ) (a₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (s s' : Fin d₁ ⊕ Fin d₂) :
    concatCov a₁ γ a₂ (finSumFinEquiv s) (finSumFinEquiv s') = Matrix.fromBlocks a₁ γ γᵀ a₂ s s' :=
  by simp [concatCov]

theorem continuous_concatCoord :
    Continuous fun p : (Fin d₁ → ℝ) × (Fin d₂ → ℝ) => concatCoord p.1 p.2 := by
  refine continuous_pi fun k => ?_
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  cases s with
  | inl i => simp only [concatCoord_inl]; fun_prop
  | inr j => simp only [concatCoord_inr]; fun_prop

theorem continuous_concatCov : Continuous fun p : (Matrix (Fin d₁) (Fin d₁) ℝ ×
    Matrix (Fin d₁) (Fin d₂) ℝ) × Matrix (Fin d₂) (Fin d₂) ℝ => concatCov p.1.1 p.1.2 p.2 := by
  refine continuous_pi fun k => continuous_pi fun l => ?_
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  obtain ⟨s', rfl⟩ := finSumFinEquiv.surjective l
  have hc : ∀ {m n : Type} {f : (Matrix (Fin d₁) (Fin d₁) ℝ × Matrix (Fin d₁) (Fin d₂) ℝ) ×
      Matrix (Fin d₂) (Fin d₂) ℝ → Matrix m n ℝ}, Continuous f → ∀ a b,
      Continuous fun p => f p a b := fun hf a b =>
    (continuous_apply b).comp ((continuous_apply a).comp hf)
  cases s <;> cases s' <;> simp only [concatCov_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.transpose_apply]
  · exact hc (continuous_fst.comp continuous_fst) _ _
  · exact hc (continuous_snd.comp continuous_fst) _ _
  · exact hc (continuous_snd.comp continuous_fst) _ _
  · exact hc continuous_snd _ _

omit [MeasurableSpace Ω] in
theorem smCompensated_concat_inl (Y₁ β₁ : ℝ≥0 → Ω → Fin d₁ → ℝ)
    (Y₂ β₂ : ℝ≥0 → Ω → Fin d₂ → ℝ) (i : Fin d₁) :
    smCompensated (fun t ω => concatCoord (Y₁ t ω) (Y₂ t ω))
      (fun t ω => concatCoord (β₁ t ω) (β₂ t ω)) (finSumFinEquiv (Sum.inl i)) =
      smCompensated Y₁ β₁ i := by
  funext t ω; simp only [smCompensated, concatCoord_inl]

omit [MeasurableSpace Ω] in
theorem smCompensated_concat_inr (Y₁ β₁ : ℝ≥0 → Ω → Fin d₁ → ℝ)
    (Y₂ β₂ : ℝ≥0 → Ω → Fin d₂ → ℝ) (j : Fin d₂) :
    smCompensated (fun t ω => concatCoord (Y₁ t ω) (Y₂ t ω))
      (fun t ω => concatCoord (β₁ t ω) (β₂ t ω)) (finSumFinEquiv (Sum.inr j)) =
      smCompensated Y₂ β₂ j := by
  funext t ω; simp only [smCompensated, concatCoord_inr]

/-!
### Stopping tools
-/

/-- The constant stopping time `⊤`. -/
theorem isStoppingTime_top_const : IsStoppingTime 𝓖 (fun _ : Ω => (⊤ : WithTop ℝ≥0)) :=
  fun t => by simp

/-- Stopping a stopped process with a martingale modification once more, at a stopping time
`ρ`, keeps a martingale modification (for a.s. continuous `X`). -/
theorem hasMartingaleModification_stopped_min [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ}
    {τ ρ σ : Ω → WithTop ℝ≥0} (h : HasMartingaleModification Q 𝓖 (stoppedProcess X τ))
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω) (hρ : IsStoppingTime 𝓖 ρ)
    (hσ : ∀ ω, σ ω = min (ρ ω) (τ ω)) :
    HasMartingaleModification Q 𝓖 (stoppedProcess X σ) := by
  obtain ⟨M, hM, hMX⟩ := h
  have hc' : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess X τ t ω := by
    filter_upwards [hc] with ω hω
    exact hω.comp (continuous_stopTime _)
  obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM hMX hc' hρ
  refine ⟨M', hM', fun t => ?_⟩
  rw [stoppedProcess_stoppedProcess'] at hM'X
  have e : σ = fun ω => min (ρ ω) (τ ω) := funext hσ
  rw [e]; exact hM'X t

/-- The minimum of two sequences tending to `⊤` tends to `⊤`. -/
theorem tendsto_min_top {f g : ℕ → WithTop ℝ≥0} (hf : Tendsto f atTop (𝓝 ⊤))
    (hg : Tendsto g atTop (𝓝 ⊤)) : Tendsto (fun n => min (f n) (g n)) atTop (𝓝 ⊤) := by
  simpa using hf.min hg

/-!
### Absolutely continuous and deterministic processes
-/

/-- **Absolutely continuous processes.** A progressive `v` with progressive `vd`, such that
a.s. every path is `v_t = v_0 + ∫_0^t vd` with `vd` locally integrable, is a continuous
semimartingale with drift `vd` and covariance `0` (localizing sequence `⊤`). -/
theorem isContinuousSemimartingale_of_ac {v vd : ℝ≥0 → Ω → Fin d → ℝ}
    (hprog : IsStronglyProgressive 𝓖 v) (hvd : IsStronglyProgressive 𝓖 vd)
    (hac : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∀ i, IntegrableOn (fun s : ℝ => vd s.toNNReal ω i) (Ioc 0 t) ∧
      v t ω i = v 0 ω i + ∫ s in Ioc (0 : ℝ) t, vd s.toNNReal ω i) :
    IsContinuousSemimartingale Q 𝓖 v vd (fun _ _ => 0) := by
  have hzero : ∀ᵐ ω ∂Q, ∀ i t, smCompensated v vd i t ω = 0 := by
    filter_upwards [hac] with ω hω i t
    simp only [smCompensated, (hω t i).2]; ring
  refine ⟨hprog.stronglyAdapted, hprog, ?_, hvd, isStronglyProgressive_const _ _, ?_,
    ⟨fun _ _ => ⊤, fun _ => isStoppingTime_top_const, ae_of_all _ fun _ => tendsto_const_nhds,
      fun _ => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [hac] with ω hω
    have e : (fun t => v t ω) =
        fun (t : ℝ≥0) i => v 0 ω i + ∫ s in Ioc (0 : ℝ) t, vd s.toNNReal ω i :=
      funext fun t => funext fun i => (hω t i).2
    rw [e]
    exact continuous_pi fun i => continuous_const.add
      (continuous_setIntegral_Ioc (g := fun u => vd u ω i) fun t => (hω t i).1)
  · filter_upwards [hac] with ω hω t
    exact ⟨fun i => (hω t i).1, fun i j => by simp⟩
  · refine hasMartingaleModification_congr hasMartingaleModification_zero fun t => ?_
    filter_upwards [hzero] with ω hω
    simp only [stoppedProcess_eq_stopTime, hω]
  · refine hasMartingaleModification_congr hasMartingaleModification_zero fun t => ?_
    filter_upwards [hzero] with ω hω
    simp [stoppedProcess_eq_stopTime, hω]

/-- **Deterministic processes.** If `g_t = g_0 + ∫_0^t g'` with `g'` Borel and locally
integrable, then `t ↦ g_t` (constant in `ω`, dimension `1`) is a continuous semimartingale with
drift `g'` and covariance `0`. -/
theorem isContinuousSemimartingale_deterministic {g gd : ℝ≥0 → ℝ} (hgd : Measurable gd)
    (hint : ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => gd s.toNNReal) (Ioc 0 t))
    (hg : ∀ t, g t = g 0 + ∫ s in Ioc (0 : ℝ) t, gd s.toNNReal) :
    IsContinuousSemimartingale (d := 1) Q 𝓖 (fun t _ _ => g t) (fun t _ _ => gd t)
      (fun _ _ => 0) := by
  have hgc : Continuous g := by
    rw [show g = fun (t : ℝ≥0) => g 0 + ∫ s in Ioc (0 : ℝ) t, gd s.toNNReal from funext hg]
    exact continuous_const.add (continuous_setIntegral_Ioc hint)
  have hprog : ∀ {f : ℝ≥0 → ℝ}, Measurable f →
      IsStronglyProgressive 𝓖 (fun t (_ : Ω) (_ : Fin 1) => f t) := fun hf i =>
    ((measurable_pi_iff.2 fun _ => hf).stronglyMeasurable).comp_measurable
      (measurable_subtype_coe.comp measurable_fst)
  exact isContinuousSemimartingale_of_ac (hprog hgc.measurable) (hprog hgd)
    (ae_of_all _ fun _ t _ => ⟨hint t, hg t⟩)

end BlockBand.SourceProcess.Stochastic.Bridges
