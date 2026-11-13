module

public import BlockBand.Endpoints.Response.ClockEntranceCorePropagation

/-!
# Item (d), part 3: the product structure of the growth step

* `cec_insert j` — overwrite the fresh coordinates `(A_j, B_{j+1}) = (ω.1 j, ω.2 (j+1))` of a
  sample by a fresh one-port layer `ν`.
* `cec_insert_measurePreserving` — `growthPathLaw ⊗ layerLaw .oneBlockOnePort ↦ growthPathLaw`
  is measure preserving (`Measure.infinitePi` marginals): under `growthPathLaw` the fresh layer
  is independent of the old coordinates and has law `layerLaw W b .oneBlockOnePort`.
* `cec_pathAt_insert`, `cec_fresh_insert` — the old path of length `j` does not see the insertion,
  and the inserted layer is the fresh layer of the result.
* `cec_lintegral_le_iterated` — for every `F` (no measurability):
  `∫⁻ F d growthPathLaw ≤ ∫⁻ω ∫⁻ν F(insert(ω, ν)) d layerLaw d growthPathLaw`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory Function
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.CoareaPalm

variable {W : ℕ}

/-- Overwrite one coordinate of an i.i.d. sequence: measure preserving. -/
theorem cec_update_measurePreserving {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (k : ℕ) :
    MeasurePreserving (fun p : (ℕ → α) × α => update p.1 k p.2)
      ((Measure.infinitePi fun _ : ℕ => μ).prod μ) (Measure.infinitePi fun _ : ℕ => μ) := by
  classical
  refine ⟨measurable_update', ?_⟩
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hS : MeasurableSet (Set.pi (↑s : Set ℕ) t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.map_apply measurable_update' hS]
  have hpre : (fun p : (ℕ → α) × α => update p.1 k p.2) ⁻¹' Set.pi (↑s : Set ℕ) t =
      Set.pi (↑(s.erase k) : Set ℕ) t ×ˢ {a | k ∈ s → a ∈ t k} := by
    ext ⟨f, a⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨fun i ⟨hik, his⟩ => ?_, fun hks => ?_⟩
      · simpa [update_of_ne hik] using h i his
      · simpa using h k hks
    · rintro ⟨h1, h2⟩ i his
      by_cases hik : i = k
      · subst hik; simpa using h2 his
      · simpa [update_of_ne hik] using h1 i ⟨hik, his⟩
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi (fun _ => μ) (fun i _ => ht i)]
  by_cases hks : k ∈ s
  · simp only [hks, forall_const, Set.ofPred_mem_eq]
    rw [Finset.prod_erase_mul _ _ hks]
  · simp only [hks, IsEmpty.forall_iff, Set.ofPred_true, measure_univ, mul_one]
    rw [Finset.erase_eq_of_notMem hks]

/-- Insert a fresh one-port layer `ν` at the growth step `j → j + 1`. -/
def cec_insert (j : ℕ) (p : GrowthPath W × LayerSample W .oneBlockOnePort) : GrowthPath W :=
  (update p.1.1 j (p.2.1 0), update p.1.2 (j + 1) (p.2.2 0 0))

/-- **Product structure of the growth step**: inserting an independent fresh layer
(law `layerLaw W b .oneBlockOnePort`) into a `growthPathLaw` sample gives `growthPathLaw`. -/
theorem cec_insert_measurePreserving (W : ℕ) (b : ℝ) (j : ℕ) :
    MeasurePreserving (cec_insert (W := W) j)
      ((growthPathLaw W b).prod (layerLaw W b .oneBlockOnePort)) (growthPathLaw W b) := by
  set μa := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set μb := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  set μA := Measure.infinitePi fun _ : ℕ => μa
  set μB := Measure.infinitePi fun _ : ℕ => μb
  have e1 := measurePreserving_funUnique μa (Fin 1)
  have e2 := (measurePreserving_funUnique μb (Fin 1)).comp
    (measurePreserving_funUnique (Measure.pi fun _ : Fin 1 => μb) (Fin 1))
  have g0 := (MeasurePreserving.id (μA.prod μB)).prod (e1.prod e2)
  have f1 := measurePreserving_prodAssoc μA μB (μa.prod μb)
  have f2 := (MeasurePreserving.id μA).prod
    ((measurePreserving_prodAssoc μB μa μb).symm MeasurableEquiv.prodAssoc)
  have f3 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ := μB) (ν := μa)).prod (MeasurePreserving.id μb))
  have f4 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μa μB μb)
  have f5 := (measurePreserving_prodAssoc μA μa (μB.prod μb)).symm MeasurableEquiv.prodAssoc
  have g6 := (cec_update_measurePreserving μa j).prod (cec_update_measurePreserving μb (j + 1))
  have h := g6.comp (f5.comp (f4.comp (f3.comp (f2.comp (f1.comp g0)))))
  exact h

/-- The old path of length `j` does not see the inserted layer. -/
theorem cec_pathAt_insert (j : ℕ) (p : GrowthPath W × LayerSample W .oneBlockOnePort) :
    pathAt W j (cec_insert j p) = pathAt W j p.1 := by
  simp only [pathAt, cec_insert]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i; simp only; rw [update_of_ne (by omega)]
  · funext i; simp only; rw [update_of_ne (by omega)]
  · funext i
    fin_cases i
    · simp
    · simp

/-- The inserted layer is the fresh layer of the result. -/
theorem cec_fresh_insert (j : ℕ) (p : GrowthPath W × LayerSample W .oneBlockOnePort) :
    cec_fresh (cec_insert j p) j = p.2 := by
  simp only [cec_fresh, cec_insert, update_self]
  refine Prod.ext ?_ ?_
  · funext a; rw [Subsingleton.elim a 0]
  · funext a c; rw [Subsingleton.elim a 0, Subsingleton.elim c 0]

/-- **Iterated bound** (no measurability needed): the integral over the path law is at most the
iterated integral over (old path) × (fresh layer) through the insertion. -/
theorem cec_lintegral_le_iterated (W : ℕ) (b : ℝ) (j : ℕ) (F : GrowthPath W → ENNReal) :
    ∫⁻ ω, F ω ∂growthPathLaw W b ≤
      ∫⁻ ω, ∫⁻ ν, F (cec_insert j (ω, ν)) ∂layerLaw W b .oneBlockOnePort ∂growthPathLaw W b := by
  have : SFinite (layerLaw W b .oneBlockOnePort) := by unfold layerLaw; infer_instance
  have h := cec_insert_measurePreserving W b j
  calc ∫⁻ ω, F ω ∂growthPathLaw W b
      = ∫⁻ ω, F ω ∂((growthPathLaw W b).prod (layerLaw W b .oneBlockOnePort)).map
          (cec_insert j) := by rw [h.map_eq]
    _ ≤ ∫⁻ p, F (cec_insert j p) ∂(growthPathLaw W b).prod (layerLaw W b .oneBlockOnePort) :=
        lintegral_map_le _ h.measurable.aemeasurable
    _ ≤ _ := lintegral_prod_le _

end BlockBand.Endpoints
