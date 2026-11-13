module

public import BlockBand.Transmission.LawFinite.CoreFresh

/-!
# One growth step of the near-end path in probability (Fubini over past × fresh)

* `growthPathLaw_map_bond`: `ω.2 k ~ Gin(b/W)`;
* `prod_le_of_section`: `(μ ⊗ ν)(S) ≤ μ(Gᶜ) + c` if the `ν`-sections over a measurable `G` are
  `≤ c`;
* **`step_prob_le`**: if a.s. `X_{r+1} = freshSchur E (Xf(past_r)) fresh_r`
  (`Bridge.growthPathLaw_map_past_fresh`), then `P(q_{r+1} < c) ≤ P(past ∉ G) + δ` whenever
  every past sample in `G` gives `P_fresh(q(X₊) < c) ≤ δ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal

variable {W : ℕ}

theorem growthPathLaw_map_bond (W : ℕ) (b : ℝ) (k : ℕ) :
    (growthPathLaw W b).map (fun ω : GrowthPath W => ω.2 k) =
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) := by
  have : (fun ω : GrowthPath W => ω.2 k) = (fun a : ℕ → Matrix (Fin W) (Fin W) ℂ => a k) ∘ Prod.snd :=
    rfl
  rw [this, ← Measure.map_map (measurable_pi_apply k) measurable_snd, growthPathLaw,
    Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]

/-- Measurability of `a ↦ freshSchur E (X a) (f a)` (built through `measurable_layerSchur`, as
`PathScalar.measurable_freshPortTrace_comp`; composing `measurable_freshSchur_prod` times out). -/
theorem measurable_freshSchur_comp {α : Type*} [MeasurableSpace α] (E : ℝ)
    {X : α → Matrix (Fin W) (Fin W) ℂ} {f : α → LayerSample W .oneBlockOnePort}
    (hX : Measurable X) (hf : Measurable f) :
    Measurable fun a => freshSchur E (X a) (f a) := by
  have hlift : Measurable fun a => (Matrix.of fun (u v : Fin 1 × Fin W) => X a u.2 v.2 :
      Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) :=
    Measurable.of_eval_matrix _ fun u v => hX.eval_matrix
  exact Measurable.of_eval_matrix _ fun x y =>
    (measurable_layerSchur .oneBlockOnePort E hlift hf).eval_matrix

/-- `ν`-sections bounded by `c` on a measurable good set `G`: `(μ ⊗ ν)(S) ≤ μ(Gᶜ) + c`. -/
theorem prod_le_of_section {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    {S : Set (α × β)} (hS : MeasurableSet S) {G : Set α} (hG : MeasurableSet G) {c : ℝ≥0∞}
    (hc : ∀ p ∈ G, ν (Prod.mk p ⁻¹' S) ≤ c) : (μ.prod ν) S ≤ μ Gᶜ + c := by
  rw [Measure.prod_apply hS]
  calc ∫⁻ p, ν (Prod.mk p ⁻¹' S) ∂μ ≤ ∫⁻ p, (Gᶜ.indicator 1 p + c) ∂μ := by
        refine lintegral_mono fun p => ?_
        by_cases hp : p ∈ G
        · rw [Set.indicator_of_notMem (by simpa using hp), zero_add]; exact hc p hp
        · rw [Set.indicator_of_mem (by simpa using hp)]
          exact (prob_le_one).trans le_self_add
    _ = μ Gᶜ + c := by
        rw [lintegral_add_right _ measurable_const, lintegral_indicator_one hG.compl,
          lintegral_const, measure_univ, mul_one]

/-- **One growth step in probability.** If a.s. `X_{r+1} = freshSchur E (Xf(past_r)) fresh_r`
with `Xf` measurable, and for every past sample in a measurable good set `G` the fresh layer
gives `P(q(X₊) < c) ≤ δ`, then `P(q_{r+1} < c) ≤ P_past(Gᶜ) + δ`. -/
theorem step_prob_le {b E : ℝ} (κ : ℝ → ℝ) (r : ℕ) {Xf : PastSample W r → Matrix (Fin W) (Fin W) ℂ}
    (hXf : Measurable Xf)
    (hae : ∀ᵐ ω ∂growthPathLaw W b, pathNearSchur b E κ W (r + 1) ω =
      freshSchur E (Xf (pastCoords W r ω)) (freshSample W r ω))
    {G : Set (PastSample W r)} (hG : MeasurableSet G) {c : ℝ} {δ : ℝ≥0∞}
    (hc : ∀ p ∈ G, freshLaw W b {f | passiveMass b E (freshSchur E (Xf p) f) < c} ≤ δ) :
    growthPathLaw W b {ω | passiveMass b E (pathNearSchur b E κ W (r + 1) ω) < c} ≤
      growthPathLaw W b (pastCoords W r ⁻¹' Gᶜ) + δ := by
  set S : Set (PastSample W r × LayerSample W .oneBlockOnePort) :=
    {q | passiveMass b E (freshSchur E (Xf q.1) q.2) < c}
  have hF : Measurable fun q : PastSample W r × LayerSample W .oneBlockOnePort =>
      passiveMass b E (freshSchur E (Xf q.1) q.2) := by
    exact (SourceMixing.measurable_passiveMass b E).comp
      (measurable_freshSchur_comp E (hXf.comp measurable_fst) measurable_snd)
  have hSm : MeasurableSet S := measurableSet_lt hF measurable_const
  have hg := (measurable_pastCoords W r).prodMk (measurable_freshSample W r)
  have h1 : growthPathLaw W b {ω | passiveMass b E (pathNearSchur b E κ W (r + 1) ω) < c} =
      growthPathLaw W b ((fun ω => (pastCoords W r ω, freshSample W r ω)) ⁻¹' S) := by
    refine measure_congr ?_
    filter_upwards [hae] with ω hω
    simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, hω]
  rw [h1, ← Measure.map_apply hg hSm, growthPathLaw_map_past_fresh,
    ← Measure.map_apply (measurable_pastCoords W r) hG.compl, growthPathLaw_map_pastCoords]
  exact prod_le_of_section _ _ hSm hG hc

end BlockBand.Transmission.LawFinite
