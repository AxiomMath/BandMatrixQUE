module

public import BlockBand.Transmission.LawDuality.BorelGiry
public import BlockBand.Transmission.LawDuality.Assembly

/-!
# `SubLimitFddUnique`: reduction to joint Giry laws; the one-time case

With `borel_eq_giry` a bounded continuous test `Φ` of `k` random finite
measures is measurable for the product of the Giry σ-algebras, so
`SubLimitFddUnique` is equivalent to equality of the joint Giry laws of
`(μ(τ_1), …, μ(τ_k))`:

* `measurable_fdd`: `ω ↦ (μ(τ_i)(ω))_i` is measurable for a subsequential limit;
* **`SubLimitJointLawUnique`**: the joint-law form of `SubLimitFddUnique` (same quantifiers);
* **`subLimitFddUnique_of_jointLaw`** and **`jointLaw_of_subLimitFddUnique`**: the two forms are
  equivalent (the converse uses that bounded continuous tests determine a finite Borel measure
  on the metrizable space `Fin k → FiniteMeasure [0,1]`);
* **`subLimit_jointLaw_le_one`**: the cases `k = 0` and `k = 1` hold under
  `SubLimitRatioMP` and `RatioDualityPrinciple`, by `subLimit_map_eq`.

The multi-time case `k ≥ 2` needs the conditional stopped backward calculation between two
positive times (`subLimitFddUnique_of_ratioMP`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal BoundedContinuousFunction

/-- **The joint-law form of `SubLimitFddUnique`.** -/
def SubLimitJointLawUnique : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ φ φ' : ℕ → ℕ, Tendsto φ atTop atTop → Tendsto φ' atTop atTop →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval) (Ω' : Type) (_ : MeasurableSpace Ω')
      (P' : Measure Ω') (μ' : ℝ → Ω' → FiniteMeasure unitInterval),
      IsTransmissionSubLimit b E κ φ P μ → IsTransmissionSubLimit b E κ φ' P' μ' →
      ∀ (k : ℕ) (τ : Fin k → ℝ), (∀ i, 0 < τ i) →
        P.map (fun ω i => μ (τ i) ω) = P'.map (fun ω i => μ' (τ i) ω)

theorem measurable_fdd {b E : ℝ} {κ : ℝ → ℝ} {φ : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (h : IsTransmissionSubLimit b E κ φ P μ) {k : ℕ} {τ : Fin k → ℝ} (hτ : ∀ i, 0 < τ i) :
    Measurable fun ω i => μ (τ i) ω :=
  measurable_pi_iff.2 fun i => h.measurable (τ i) (hτ i)

/-- **Joint laws ⇒ `SubLimitFddUnique`.** -/
theorem subLimitFddUnique_of_jointLaw (h : SubLimitJointLawUnique) : SubLimitFddUnique :=
  fun b hb hb2 E hE1 hE2 κ hκ φ φ' hφ hφ' Ω m P μ Ω' m' P' μ' hs hs' k τ hτ Φ =>
    integral_bcf_eq_of_map_eq (measurable_fdd hs hτ) (measurable_fdd hs' hτ)
      (h b hb hb2 E hE1 hE2 κ hκ φ φ' hφ hφ' Ω m P μ Ω' m' P' μ' hs hs' k τ hτ) Φ

/-- **`SubLimitFddUnique` ⇒ joint laws** (bounded continuous tests determine finite Borel
measures on a pseudo-metrizable space). -/
theorem jointLaw_of_subLimitFddUnique (h : SubLimitFddUnique) : SubLimitJointLawUnique := by
  intro b hb hb2 E hE1 hE2 κ hκ φ φ' hφ hφ' Ω m P μ Ω' m' P' μ' hs hs' k τ hτ
  have := hs.prob
  have := hs'.prob
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun Φ => ?_
  rw [integral_map (measurable_fdd hs hτ).aemeasurable Φ.continuous.aestronglyMeasurable,
    integral_map (measurable_fdd hs' hτ).aemeasurable Φ.continuous.aestronglyMeasurable]
  exact h b hb hb2 E hE1 hE2 κ hκ φ φ' hφ hφ' Ω m P μ Ω' m' P' μ' hs hs' k τ hτ Φ

/-- **The one-time cases** (`k ≤ 1`) of `SubLimitJointLawUnique`, from `SubLimitRatioMP` and
`RatioDualityPrinciple`. -/
theorem subLimit_jointLaw_le_one (hMP : SubLimitRatioMP) (hPr : RatioDualityPrinciple)
    {b E : ℝ} {κ : ℝ → ℝ} (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hκ : IsAbsorptionProfile κ) {φ φ' : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hφ' : Tendsto φ' atTop atTop) {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    {μ' : ℝ → Ω' → FiniteMeasure unitInterval}
    (hs : IsTransmissionSubLimit b E κ φ P μ) (hs' : IsTransmissionSubLimit b E κ φ' P' μ')
    {k : ℕ} (hk : k ≤ 1) {τ : Fin k → ℝ} (hτ : ∀ i, 0 < τ i) :
    P.map (fun ω i => μ (τ i) ω) = P'.map (fun ω i => μ' (τ i) ω) := by
  have := hs.prob
  have := hs'.prob
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · have e : ∀ {α : Type} (f : α → Fin 0 → FiniteMeasure unitInterval),
        f = fun _ => (fun i => i.elim0) := fun f => funext fun _ => funext fun i => i.elim0
    rw [e (fun ω i => μ (τ i) ω), e (fun ω i => μ' (τ i) ω), Measure.map_const,
      Measure.map_const, measure_univ, measure_univ]
  · let ι : FiniteMeasure unitInterval → Fin 1 → FiniteMeasure unitInterval := fun ν _ => ν
    have hι : Measurable ι := measurable_pi_iff.2 fun _ => measurable_id
    have e1 : (fun ω i => μ (τ i) ω) = ι ∘ μ (τ 0) := by
      funext ω i; rw [Subsingleton.elim i 0]; rfl
    have e2 : (fun ω i => μ' (τ i) ω) = ι ∘ μ' (τ 0) := by
      funext ω i; rw [Subsingleton.elim i 0]; rfl
    rw [e1, e2, ← Measure.map_map hι (hs.measurable _ (hτ 0)),
      ← Measure.map_map hι (hs'.measurable _ (hτ 0)),
      subLimit_map_eq hb hb2 hE1 hE2 hκ hMP hPr hφ hφ' hs hs' (hτ 0)]

end BlockBand.Transmission.LawDuality
