module

public import BlockBand.Palm.MomentFlow.StepsLongEvent
public import BlockBand.Palm.MomentFlow.EventDisintegrate

/-!
# Long couplings on a measurable good event, and the conditional weighted-sum bound

* `long_coupling_event_bound_measurable`: the statement of `long_coupling_event_bound` with a
  **measurable** bad set (`toMeasurable`, same measure), as needed for disintegration.
* `condExp_weighted_sum_le` (any probability space, sub-σ-algebra `m`): if the weights `w_j` are
  `m`-measurable with `0 ≤ w_j ≤ K`, the observables satisfy `0 ≤ X_j ≤ B`, and
  `∑_j w_j X_j ≤ b` off a measurable `Bad`, then a.e.
  `∑_j w_j E[X_j | m] ≤ b + |J| K B · E[1_Bad | m]` (pull-out of the `m`-measurable weights; no
  conditioning on `Bad`).
* `condExp_weighted_sum_le_of_small`: combined with disintegration
  (`condExp_indicator_compl_small`): there is an `m`-measurable set `B₀` with `P(B₀) ≤ P(Bad)/t` off
  which (a.e.) `∑_j w_j E[X_j | m] ≤ b + |J| K B t`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs

variable {N : ℕ}

/-- The long-coupling bound on the good event, with a measurable bad set. -/
theorem long_coupling_event_bound_measurable (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) {ε : ℝ} (hε : 0 < ε) (hε5 : ε < 1 / 5) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        ∀ q : Fin N → ℂ, ∃ Bad : Set (FlowSample N), MeasurableSet Bad ∧
          flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) Bad ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D)) + ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ ω ∉ Bad, ω.1.IsHermitian → ∀ s ∈ Icc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c,
            HasSimpleSpectrum N (flowMatrix F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s) →
            ∀ i : Fin N,
              |flowEigenvalue F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i - E| ≤ r₀ / 2 →
              ∑ j ∈ Finset.univ.filter
                  (fun j => ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ≤ labelDist i j),
                flowRate F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i j *
                  flowOverlap F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) q s j ω ≤
              2 / (c₁ * ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ / N) * Cst *
                quadForm (freshGamma F c E) q := by
  obtain ⟨c₁, hc₁, Cst, hCst, h⟩ := long_coupling_event_bound hELG hMDE hLp hIBP (A := A) hK hε hε5
  refine ⟨c₁, hc₁, Cst, hCst, fun D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h D
  refine ⟨N₀, fun N hN F E hC q => ?_⟩
  obtain ⟨Bad, hP, hB⟩ := hN₀ N hN F E hC q
  set μ := flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ)))
  refine ⟨toMeasurable μ Bad, measurableSet_toMeasurable _ _, by rw [measure_toMeasurable]; exact hP,
    fun ω hω => hB ω fun h' => hω (subset_toMeasurable _ _ h')⟩

section Abstract

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι]

/-- **Conditional weighted sums** (pull-out of `m`-measurable bounded weights). -/
theorem condExp_weighted_sum_le (hm : m ≤ m0) (w X : ι → Ω → ℝ) {K B b : ℝ} (hb : 0 ≤ b)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hw : ∀ j, StronglyMeasurable[m] (w j))
    (hw0 : ∀ j ω, 0 ≤ w j ω) (hwK : ∀ j ω, w j ω ≤ K) (hX : ∀ j, Measurable (X j))
    (hX0 : ∀ j ω, 0 ≤ X j ω) (hXB : ∀ j ω, X j ω ≤ B) {Bad : Set Ω} (hBad : MeasurableSet Bad)
    (hgood : ∀ ω ∉ Bad, ∑ j, w j ω * X j ω ≤ b) :
    ∀ᵐ ω ∂μ, ∑ j, w j ω * (μ[X j | m]) ω ≤
      b + Fintype.card ι * K * B * (μ[Bad.indicator (fun _ => (1 : ℝ)) | m]) ω := by
  set c : ℝ := Fintype.card ι * K * B
  have hc : 0 ≤ c := by positivity
  set I : Ω → ℝ := Bad.indicator (fun _ => (1 : ℝ))
  have hIint : Integrable I μ := (integrable_const (1 : ℝ)).indicator hBad
  have hwm : ∀ j, StronglyMeasurable (w j) := fun j => (hw j).mono hm
  have hXint : ∀ j, Integrable (X j) μ := fun j =>
    Integrable.of_bound (hX j).aestronglyMeasurable B (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 j ω)]; exact hXB j ω)
  have hwXint : ∀ j, Integrable (w j * X j) μ := fun j =>
    Integrable.of_bound ((hwm j).aestronglyMeasurable.mul (hX j).aestronglyMeasurable) (K * B)
      (Eventually.of_forall fun ω => by
        simp only [Pi.mul_apply, Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (hw0 j ω) (hX0 j ω))]
        exact mul_le_mul (hwK j ω) (hXB j ω) (hX0 j ω) hK)
  -- pointwise domination
  have hpt : ∀ ω, (∑ j, w j * X j) ω ≤ (fun ω => b + c * I ω) ω := by
    intro ω
    simp only [Finset.sum_apply, Pi.mul_apply]
    by_cases hω : ω ∈ Bad
    · have : ∑ j, w j ω * X j ω ≤ c := by
        calc ∑ j, w j ω * X j ω ≤ ∑ _j : ι, K * B := Finset.sum_le_sum fun j _ =>
              mul_le_mul (hwK j ω) (hXB j ω) (hX0 j ω) hK
          _ = c := by simp [c, Finset.sum_const, Finset.card_univ]; ring
      simp only [I, Set.indicator_of_mem hω, mul_one]
      linarith
    · simp only [I, Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact hgood ω hω
  have hsumint : Integrable (∑ j, w j * X j) μ := integrable_finsetSum' _ fun j _ => hwXint j
  have hrint : Integrable (fun ω => b + c * I ω) μ :=
    (integrable_const b).add (hIint.const_mul c)
  have hmono := condExp_mono (m := m) hsumint hrint (Eventually.of_forall hpt)
  have hsum := condExp_finsetSum (s := Finset.univ) (fun j _ => hwXint j) m (μ := μ)
  have hpull : ∀ j, μ[w j * X j | m] =ᵐ[μ] w j * μ[X j | m] := fun j =>
    condExp_mul_of_stronglyMeasurable_left (hw j) (hwXint j) (hXint j)
  have hpullall : ∀ᵐ ω ∂μ, ∀ j, (μ[w j * X j | m]) ω = (w j * μ[X j | m]) ω :=
    ae_all_iff.2 hpull
  have hrhs : μ[fun ω => b + c * I ω | m] =ᵐ[μ] fun ω => b + c * (μ[I | m]) ω := by
    have h1 := condExp_add (integrable_const b) (hIint.const_mul c) m (μ := μ)
    have h2 : μ[fun _ => b | m] = fun _ => b := condExp_const hm b
    have h3 := condExp_smul (μ := μ) c I m
    filter_upwards [h1, h3] with ω e1 e3
    have e : (fun ω => b + c * I ω) = (fun _ => b) + fun ω => c * I ω := rfl
    rw [e, e1, Pi.add_apply, h2]
    have e' : (fun ω => c * I ω) = c • I := rfl
    rw [e', e3]
    simp
  filter_upwards [hmono, hsum, hpullall, hrhs] with ω e1 e2 e3 e4
  rw [e2, Finset.sum_apply, e4] at e1
  have : ∑ j, w j ω * (μ[X j | m]) ω = ∑ j, (μ[w j * X j | m]) ω :=
    Finset.sum_congr rfl fun j _ => by rw [e3 j]; rfl
  rw [this]
  exact e1

/-- The weighted-sum bound combined with disintegration: off an `m`-measurable set of probability
`≤ P(Bad)/t`, a.e. `∑_j w_j E[X_j | m] ≤ b + |J| K B t`. -/
theorem condExp_weighted_sum_le_of_small (hm : m ≤ m0) (w X : ι → Ω → ℝ) {K B b t : ℝ}
    (hb : 0 ≤ b) (hK : 0 ≤ K) (hB : 0 ≤ B) (ht : 0 < t) (hw : ∀ j, StronglyMeasurable[m] (w j))
    (hw0 : ∀ j ω, 0 ≤ w j ω) (hwK : ∀ j ω, w j ω ≤ K) (hX : ∀ j, Measurable (X j))
    (hX0 : ∀ j ω, 0 ≤ X j ω) (hXB : ∀ j ω, X j ω ≤ B) {Bad : Set Ω} (hBad : MeasurableSet Bad)
    (hgood : ∀ ω ∉ Bad, ∑ j, w j ω * X j ω ≤ b) :
    ∃ B₀ : Set Ω, MeasurableSet[m] B₀ ∧ μ.real B₀ ≤ μ.real Bad / t ∧
      ∀ᵐ ω ∂μ, ω ∉ B₀ → ∑ j, w j ω * (μ[X j | m]) ω ≤ b + Fintype.card ι * K * B * t := by
  obtain ⟨B₀, hB₀, hμ, hoff⟩ := condExp_indicator_compl_small (μ := μ) hm hBad.compl ht
  rw [compl_compl] at hμ hoff
  refine ⟨B₀, hB₀, hμ, ?_⟩
  filter_upwards [condExp_weighted_sum_le hm w X hb hK hB hw hw0 hwK hX hX0 hXB hBad hgood]
    with ω hω hωB
  refine hω.trans ?_
  have := hoff ω hωB
  have hc : 0 ≤ (Fintype.card ι : ℝ) * K * B := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this.le hc]

end Abstract

end BlockBand.Palm.MomentFlow
