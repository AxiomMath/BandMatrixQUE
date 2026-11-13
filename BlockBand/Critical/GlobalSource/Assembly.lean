module

public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Global Gaussian source: the abstract removal of the sampling cutoff

This file proves the measure-theoretic skeleton of the removal of the sampling cutoff, for laws on an arbitrary
finite-dimensional real inner product space `E` (the matrix space `Matrix (Fin J) (Fin J) ℂ` is
identified with such a space by a linear homeomorphism in a later instantiation). The smooth test
class is the class of characteristic-function tests `x ↦ exp(i⟨t, x⟩)`; they are `C^∞`, bounded,
with `‖D^k‖ ≤ ‖t‖^k`, so they are admissible tests of the Lindeberg bound for
the global probe replacement.

* `tendsto_of_uniform_approx`, `exists_tendsto_of_uniform_approx`: scalar three-`ε` lemmas.
* `exists_tendsto_of_tight_of_tendsto_charFun`: Lévy–Prokhorov: a tight sequence of probability
  measures whose characteristic functions converge pointwise converges weakly, and the limit has
  the limiting characteristic function.
* `exists_tendsto_of_sampling_approx`: if the finite laws `μ_j` are tight, their characteristic
  functions are within `ε_M(t) → 0` of those of sampled laws `ν_{M,j}` for large `j` (uniformly
  in `j`), and `ν_{M,j} → ρ_M` as `j → ∞`, then `ρ_M → κ` and `μ_j → κ` for one `κ`.
* `tendsto_of_sampling_approx`: once `ρ_M → κ` is known, the same approximation gives `μ_j → κ`
  for every further sequence (no tightness needed). This is what makes the limit the same along
  every critical sequence.

All statements are general lemmas with explicit hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory Filter Topology

/-!
## Scalar three-`ε` lemmas
-/

section Scalar

variable {X : Type*} [NormedAddCommGroup X]

/-- If `a_j` is uniformly (for large `j`) within `ε_M` of `b_{M,j}`, `b_{M,j} → c_M` as `j → ∞`,
then `‖c_M - c_{M'}‖ ≤ ε_M + ε_{M'}`. -/
theorem norm_sub_le_of_uniform_approx {a : ℕ → X} {b : ℕ → ℕ → X} {c : ℕ → X} {ε : ℕ → ℝ}
    (happrox : ∀ M, ∀ᶠ j in atTop, ‖a j - b M j‖ ≤ ε M)
    (hb : ∀ M, Tendsto (b M) atTop (𝓝 (c M))) (M M' : ℕ) :
    ‖c M - c M'‖ ≤ ε M + ε M' := by
  have hlim : Tendsto (fun j => ‖b M j - b M' j‖) atTop (𝓝 ‖c M - c M'‖) :=
    ((hb M).sub (hb M')).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [happrox M, happrox M'] with j h1 h2
  calc ‖b M j - b M' j‖ = ‖-(a j - b M j) + (a j - b M' j)‖ := by congr 1; abel
    _ ≤ ‖a j - b M j‖ + ‖a j - b M' j‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ ε M + ε M' := add_le_add h1 h2

/-- **Removal of the cutoff, given the limit**: if `a_j` is uniformly within `ε_M → 0` of
`b_{M,j}` for large `j`, `b_{M,j} → c_M` as `j → ∞`, and `c_M → L`, then `a_j → L`. -/
theorem tendsto_of_uniform_approx {a : ℕ → X} {b : ℕ → ℕ → X} {c : ℕ → X} {ε : ℕ → ℝ} {L : X}
    (hε : Tendsto ε atTop (𝓝 0)) (happrox : ∀ M, ∀ᶠ j in atTop, ‖a j - b M j‖ ≤ ε M)
    (hb : ∀ M, Tendsto (b M) atTop (𝓝 (c M))) (hc : Tendsto c atTop (𝓝 L)) :
    Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have h3 : (0 : ℝ) < δ / 3 := by positivity
  obtain ⟨M, hM1, hM2⟩ : ∃ M, ε M < δ / 3 ∧ ‖c M - L‖ < δ / 3 := by
    have e1 := (hε.eventually (gt_mem_nhds h3))
    have e2 := (tendsto_iff_norm_sub_tendsto_zero.mp hc).eventually (gt_mem_nhds h3)
    exact (e1.and e2).exists
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp ((happrox M).and
    ((tendsto_iff_norm_sub_tendsto_zero.mp (hb M)).eventually (gt_mem_nhds h3)))
  refine ⟨j₀, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := hj₀ j hj
  rw [dist_eq_norm]
  calc ‖a j - L‖ = ‖(a j - b M j) + (b M j - c M) + (c M - L)‖ := by congr 1; abel
    _ ≤ ‖a j - b M j‖ + ‖b M j - c M‖ + ‖c M - L‖ := norm_add₃_le
    _ < δ / 3 + δ / 3 + δ / 3 := by
        have := h1.trans hM1.le
        linarith
    _ = δ := by ring

/-- **Removal of the cutoff, existence of the limit**: in a complete space, if `a_j` is uniformly
within `ε_M → 0` of `b_{M,j}` for large `j` and `b_{M,j} → c_M`, then `c_M` converges to some `L`
and `a_j → L`. -/
theorem exists_tendsto_of_uniform_approx [CompleteSpace X] {a : ℕ → X} {b : ℕ → ℕ → X}
    {c : ℕ → X} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (happrox : ∀ M, ∀ᶠ j in atTop, ‖a j - b M j‖ ≤ ε M)
    (hb : ∀ M, Tendsto (b M) atTop (𝓝 (c M))) :
    ∃ L, Tendsto c atTop (𝓝 L) ∧ Tendsto a atTop (𝓝 L) := by
  have hcauchy : CauchySeq c := by
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    have h2 : (0 : ℝ) < δ / 2 := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hε.eventually (gt_mem_nhds h2))
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have := norm_sub_le_of_uniform_approx happrox hb m n
    have := hN m hm
    have := hN n hn
    linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨L, hL, tendsto_of_uniform_approx hε happrox hb hL⟩

end Scalar

/-!
## Characteristic functions
-/

section CharFun

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Lévy–Prokhorov**: a tight sequence of probability measures on a finite-dimensional real
inner product space whose characteristic functions converge pointwise to `f` converges weakly to
a probability measure `κ` with `charFun κ = f`. -/
theorem exists_tendsto_of_tight_of_tendsto_charFun {μ : ℕ → ProbabilityMeasure E}
    (htight : IsTightMeasureSet {(μ n : Measure E) | n}) {f : E → ℂ}
    (hf : ∀ t, Tendsto (fun n => charFun (μ n : Measure E) t) atTop (𝓝 (f t))) :
    ∃ κ : ProbabilityMeasure E, Tendsto μ atTop (𝓝 κ) ∧ ∀ t, charFun (κ : Measure E) t = f t := by
  have hS : IsTightMeasureSet
      {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range μ} := by
    convert htight using 1
    ext x
    simp
  have hcomp := isCompact_closure_of_isTightMeasureSet hS
  obtain ⟨κ, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  have hκ : ∀ t, charFun (κ : Measure E) t = f t := by
    intro t
    have h1 := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim t
    exact tendsto_nhds_unique h1 ((hf t).comp hφ.tendsto_atTop)
  refine ⟨κ, ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_, hκ⟩
  rw [hκ t]
  exact hf t

/-- **The sampling cutoff is removed after the critical limit, given the limit law.** Let `μ_j` (finite-width laws along one sequence), `ν_{M,j}` (`M`-sampled
finite-width laws) and `ρ_M` (`M`-sampled limit laws) be probability measures on `E`. If for every
`t` the characteristic functions satisfy `‖φ_{μ_j}(t) - φ_{ν_{M,j}}(t)‖ ≤ ε_M(t)` for all large `j`
(the uniform-in-width Lindeberg bound), with `ε_M(t) → 0` as `M → ∞`, if `ν_{M,j} → ρ_M` weakly as
`j → ∞` for each `M`, and if `ρ_M → κ` weakly, then `μ_j → κ` weakly. -/
theorem tendsto_of_sampling_approx {μ : ℕ → ProbabilityMeasure E}
    {ν : ℕ → ℕ → ProbabilityMeasure E} {ρ : ℕ → ProbabilityMeasure E} {κ : ProbabilityMeasure E}
    {ε : ℕ → E → ℝ} (hε : ∀ t, Tendsto (fun M => ε M t) atTop (𝓝 0))
    (happrox : ∀ M t, ∀ᶠ j in atTop,
      ‖charFun (μ j : Measure E) t - charFun (ν M j : Measure E) t‖ ≤ ε M t)
    (hν : ∀ M, Tendsto (ν M) atTop (𝓝 (ρ M))) (hρ : Tendsto ρ atTop (𝓝 κ)) :
    Tendsto μ atTop (𝓝 κ) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  exact tendsto_of_uniform_approx (hε t) (fun M => happrox M t)
    (fun M => ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (hν M) t)
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hρ t)

/-- **The sampling cutoff is removed after the critical limit, existence of the limit.** Same hypotheses as `tendsto_of_sampling_approx` except that the limit
`κ` is not given; instead the finite-width laws `μ_j` are tight (as follows from the uniform source
moments). Then there is one probability measure `κ` with `ρ_M → κ` (the sampled
limit laws converge as `M → ∞`) and `μ_j → κ`. -/
theorem exists_tendsto_of_sampling_approx {μ : ℕ → ProbabilityMeasure E}
    {ν : ℕ → ℕ → ProbabilityMeasure E} {ρ : ℕ → ProbabilityMeasure E}
    {ε : ℕ → E → ℝ} (hε : ∀ t, Tendsto (fun M => ε M t) atTop (𝓝 0))
    (happrox : ∀ M t, ∀ᶠ j in atTop,
      ‖charFun (μ j : Measure E) t - charFun (ν M j : Measure E) t‖ ≤ ε M t)
    (hν : ∀ M, Tendsto (ν M) atTop (𝓝 (ρ M)))
    (htight : IsTightMeasureSet {(μ j : Measure E) | j}) :
    ∃ κ : ProbabilityMeasure E, Tendsto ρ atTop (𝓝 κ) ∧ Tendsto μ atTop (𝓝 κ) := by
  have hL : ∀ t, ∃ L : ℂ, Tendsto (fun M => charFun (ρ M : Measure E) t) atTop (𝓝 L) ∧
      Tendsto (fun j => charFun (μ j : Measure E) t) atTop (𝓝 L) := fun t =>
    exists_tendsto_of_uniform_approx (hε t) (fun M => happrox M t)
      (fun M => ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (hν M) t)
  choose L hLρ hLμ using hL
  obtain ⟨κ, hμκ, hκ⟩ := exists_tendsto_of_tight_of_tendsto_charFun htight hLμ
  refine ⟨κ, ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_, hμκ⟩
  rw [hκ t]
  exact hLρ t

end CharFun

end BlockBand.Critical.GlobalSource
