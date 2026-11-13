module

public import BlockBand.Internal.Contracts.Transmission

/-!
# Relative localization: building the semimartingale `(λ, v)`

* `IsContinuousSemimartingale.reindex` : selecting/permuting coordinates `i ↦ Y^{π i}` of a
  continuous semimartingale gives a continuous semimartingale with drift `β ∘ π` and covariance
  `α (π ·) (π ·)` (used to pass from `dysonState`, with eigenvalues and overlaps in nonincreasing
  labels, to the eigenvalue block in increasing labels);
* `IsContinuousSemimartingale.appendFV` : appending finitely many finite-variation
  coordinates `Z` (adapted, progressive, a.s. continuous, with a.s. `Z_t = Z_0 + ∫₀ᵗ γ`) to a
  continuous semimartingale `Y` gives a continuous semimartingale in `ℝ^{d+e}`
  (`finSumFinEquiv` layout) with drift `(β, γ)` and covariance `α` on the `Y` block and `0`
  elsewhere — the mass coordinates `v` of the weighted mass.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory Filter BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem hasMartingaleModification_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {X X' : ℝ≥0 → Ω → E} (h : X = X')
    (hX : HasMartingaleModification Q 𝓖 X) : HasMartingaleModification Q 𝓖 X' := h ▸ hX

/-- An a.s. identically zero process has a martingale modification. -/
theorem hasMartingaleModification_of_ae_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {X : ℝ≥0 → Ω → E} (h : ∀ᵐ ω ∂Q, ∀ t, X t ω = 0) :
    HasMartingaleModification Q 𝓖 X :=
  ⟨0, martingale_zero E 𝓖 Q, fun t => by
    filter_upwards [h] with ω hω
    rw [hω t]; rfl⟩

/-- **Reindexing** of a continuous semimartingale. -/
theorem IsContinuousSemimartingale.reindex {d d' : ℕ} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    {β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
    (hY : IsContinuousSemimartingale Q 𝓖 Y β α) (π : Fin d' → Fin d) :
    IsContinuousSemimartingale Q 𝓖 (fun t ω i => Y t ω (π i)) (fun t ω i => β t ω (π i))
      (fun t ω => Matrix.of fun i j => α t ω (π i) (π j)) := by
  have hv : Continuous fun (y : Fin d → ℝ) (i : Fin d') => y (π i) :=
    continuous_pi fun i => continuous_apply (π i)
  have hm : Continuous fun (A : Matrix (Fin d) (Fin d) ℝ) =>
      (Matrix.of fun i j => A (π i) (π j) : Matrix (Fin d') (Fin d') ℝ) :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (π j)).comp (continuous_apply (π i))
  obtain ⟨τ, hτ, hτlim, hloc⟩ := hY.localizing
  refine ⟨fun t => hv.comp_stronglyMeasurable (hY.adapted t),
    fun t => hv.comp_stronglyMeasurable (hY.progressive t), ?_,
    fun t => hv.comp_stronglyMeasurable (hY.drift_progressive t),
    fun t => hm.comp_stronglyMeasurable (hY.cov_progressive t), ?_,
    ⟨τ, hτ, hτlim, fun n => ⟨fun i => (hloc n).1 (π i), fun i j => (hloc n).2 (π i) (π j)⟩⟩⟩
  · filter_upwards [hY.continuous] with ω hω using hv.comp hω
  · filter_upwards [hY.integrable] with ω hω t
    exact ⟨fun i => (hω t).1 (π i), fun i j => (hω t).2 (π i) (π j)⟩

/-- Concatenation `(x, y) ∈ ℝ^{d+e}` in the `finSumFinEquiv` layout. -/
def sumVec {d e : ℕ} (x : Fin d → ℝ) (y : Fin e → ℝ) : Fin (d + e) → ℝ :=
  fun i => Sum.elim x y (finSumFinEquiv.symm i)

/-- Block covariance: `α` on the first block, zero elsewhere. -/
def blockCov {d e : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin (d + e)) (Fin (d + e)) ℝ :=
  Matrix.of fun i j => match finSumFinEquiv.symm i, finSumFinEquiv.symm j with
    | Sum.inl a, Sum.inl b => A a b
    | _, _ => 0

theorem continuous_sumVec {d e : ℕ} :
    Continuous fun p : (Fin d → ℝ) × (Fin e → ℝ) => sumVec p.1 p.2 := by
  refine continuous_pi fun i => ?_
  unfold sumVec
  rcases h : finSumFinEquiv.symm i with a | b
  · simp only [Sum.elim_inl]; exact (continuous_apply a).comp continuous_fst
  · simp only [Sum.elim_inr]; exact (continuous_apply b).comp continuous_snd

theorem continuous_blockCov {d e : ℕ} :
    Continuous fun A : Matrix (Fin d) (Fin d) ℝ => (blockCov (e := e) A) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blockCov, Matrix.of_apply]
  rcases finSumFinEquiv.symm i with a | b <;> rcases finSumFinEquiv.symm j with c | f
  · exact (continuous_apply c).comp (continuous_apply a)
  all_goals exact continuous_const

/-- **Appending finite-variation coordinates.** -/
theorem IsContinuousSemimartingale.appendFV {d e : ℕ} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    {β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
    (hY : IsContinuousSemimartingale Q 𝓖 Y β α) {Z γ : ℝ≥0 → Ω → Fin e → ℝ}
    (hZa : ∀ t, StronglyMeasurable[𝓖 t] (Z t)) (hZp : IsStronglyProgressive 𝓖 Z)
    (hZc : ∀ᵐ ω ∂Q, Continuous fun t => Z t ω) (hγp : IsStronglyProgressive 𝓖 γ)
    (hγi : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∀ i, MeasureTheory.IntegrableOn
      (fun s : ℝ => γ s.toNNReal ω i) (Set.Ioc 0 t))
    (hZfv : ∀ᵐ ω ∂Q, ∀ t i, smCompensated Z γ i t ω = 0) :
    IsContinuousSemimartingale Q 𝓖 (fun t ω => sumVec (Y t ω) (Z t ω))
      (fun t ω => sumVec (β t ω) (γ t ω)) (fun t ω => blockCov (e := e) (α t ω)) := by
  have hsv := continuous_sumVec (d := d) (e := e)
  obtain ⟨τ, hτ, hτlim, hloc⟩ := hY.localizing
  refine ⟨fun t => hsv.comp_stronglyMeasurable ((hY.adapted t).prodMk (hZa t)),
    fun t => hsv.comp_stronglyMeasurable ((hY.progressive t).prodMk (hZp t)), ?_,
    fun t => hsv.comp_stronglyMeasurable ((hY.drift_progressive t).prodMk (hγp t)),
    fun t => continuous_blockCov.comp_stronglyMeasurable (hY.cov_progressive t), ?_,
    ⟨τ, hτ, hτlim, fun n => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [hY.continuous, hZc] with ω h1 h2 using hsv.comp (h1.prodMk h2)
  · filter_upwards [hY.integrable, hγi] with ω h1 h2 t
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
      rcases x with a | b
      · simpa [sumVec] using (h1 t).1 a
      · simpa [sumVec] using h2 t b
    · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
      obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
      rcases x with a | b <;> rcases y with c | f
      · simpa [blockCov] using (h1 t).2 a c
      all_goals simp [blockCov]
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
    rcases x with a | b
    · refine hasMartingaleModification_congr ?_ ((hloc n).1 a)
      funext t ω; simp [stoppedProcess, smCompensated, sumVec]
    · refine hasMartingaleModification_of_ae_zero ?_
      filter_upwards [hZfv] with ω hω t
      have := hω ((min (t : WithTop ℝ≥0) (τ n ω)).untopA) b
      simpa [stoppedProcess, smCompensated, sumVec] using this
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
    rcases x with a | b <;> rcases y with c | f
    · refine hasMartingaleModification_congr ?_ ((hloc n).2 a c)
      funext t ω; simp [stoppedProcess, smCompensated, sumVec, blockCov]
    all_goals
      refine hasMartingaleModification_of_ae_zero ?_
      filter_upwards [hZfv] with ω hω t
    · have := hω ((min (t : WithTop ℝ≥0) (τ n ω)).untopA) f
      simp only [smCompensated] at this
      simp [stoppedProcess, smCompensated, sumVec, blockCov]
      exact Or.inr this
    · have := hω ((min (t : WithTop ℝ≥0) (τ n ω)).untopA) b
      simp only [smCompensated] at this
      simp [stoppedProcess, smCompensated, sumVec, blockCov]
      exact Or.inl this
    · have := hω ((min (t : WithTop ℝ≥0) (τ n ω)).untopA) b
      simp only [smCompensated] at this
      simp [stoppedProcess, smCompensated, sumVec, blockCov]
      exact Or.inl this

end BlockBand.Palm.RelativeLocalization
