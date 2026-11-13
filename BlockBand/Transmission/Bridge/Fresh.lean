module

public import BlockBand.Transmission.Bridge.Marginal

/-!
# Bridge (i), probabilistic half: the fresh layer of the near-end growth step

The growth step `r → r+1` adds the block `A_r` and the near-port bond `B_{r+1}`
(`freshSample W r`). The past coordinates `pastCoords W r` (`A_0, …, A_{r-1}` and
`B_0, …, B_r`) generate `growthSigma W r` by definition. Main results:

* `growthPathLaw_map_past_fresh`: the joint law of `(past, fresh)` is
  `pastLaw W r b ⊗ freshLaw W b`;
* `growthPathLaw_map_freshSample`: the fresh coordinates have law `freshLaw W b`;
* `indepFun_past_fresh`, `indep_growthSigma_fresh`: the fresh layer is independent of
  `growthSigma W r`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix

/-- The past coordinates `(A_0,…,A_{r-1}; B_0,…,B_r)` of the growth sample; they generate
`growthSigma W r` (`growthSigma_eq_comap`). -/
def pastCoords (W r : ℕ) (ω : GrowthPath W) :
    (Fin r → Matrix (Fin W) (Fin W) ℂ) × (Fin (r + 1) → Matrix (Fin W) (Fin W) ℂ) :=
  ((fun k : Fin r => ω.1 k), (fun k : Fin (r + 1) => ω.2 k))

/-- Law of the past coordinates: iid `GUE_W(c/W)` blocks and iid `Gin(b/W)` bonds. -/
def pastLaw (W r : ℕ) (b : ℝ) :
    Measure ((Fin r → Matrix (Fin W) (Fin W) ℂ) × (Fin (r + 1) → Matrix (Fin W) (Fin W) ℂ)) :=
  (Measure.pi fun _ : Fin r => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))).prod
    (Measure.pi fun _ : Fin (r + 1) => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))

/-- The fresh one-port layer of the growth step `r → r+1`: block `A_r`, near-port bond
`B_{r+1}`, as a `Layers` one-block-one-port sample. -/
def freshSample (W r : ℕ) (ω : GrowthPath W) : LayerSample W .oneBlockOnePort :=
  (fun _ => ω.1 r, fun _ _ => ω.2 (r + 1))

theorem growthSigma_eq_comap (W r : ℕ) :
    growthSigma W r = MeasurableSpace.comap (pastCoords W r) inferInstance := rfl

theorem measurable_pastCoords (W r : ℕ) : Measurable (pastCoords W r) :=
  ((Measurable.of_eval fun _ => measurable_pi_apply _).comp measurable_fst).prodMk
    ((Measurable.of_eval fun _ => measurable_pi_apply _).comp measurable_snd)

theorem measurable_freshSample (W r : ℕ) : Measurable (freshSample W r) :=
  (Measurable.of_eval fun _ => (measurable_pi_apply _).comp measurable_fst).prodMk
    (Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp measurable_snd)

instance isProbabilityMeasure_pastLaw (W r : ℕ) (b : ℝ) : IsProbabilityMeasure (pastLaw W r b) := by
  unfold pastLaw; infer_instance

instance isProbabilityMeasure_freshLaw (W : ℕ) (b : ℝ) : IsProbabilityMeasure (freshLaw W b) :=
  isProbabilityMeasure_layerLaw W b _

/-- Rearranging a product of two products. -/
theorem measurePreserving_prodShuffle {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ)
    (μd : Measure δ) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun x : (α × β) × (γ × δ) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd).symm
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm
  have := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  convert this using 1
  funext x; rfl

/-- Reindexing that splits off one coordinate. -/
def splitIndex (n : ℕ) : Fin n ⊕ Fin 1 → ℕ
  | Sum.inl k => k.val
  | Sum.inr _ => n

theorem splitIndex_injective (n : ℕ) : Function.Injective (splitIndex n) := by
  rintro (i | i) (j | j) h <;> simp only [splitIndex] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · exact absurd h (by have := i.isLt; omega)
  · exact absurd h (by have := j.isLt; omega)
  · exact congrArg Sum.inr (Subsingleton.elim _ _)

theorem measurePreserving_split {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun a : ℕ → X => ((fun k : Fin n => a k), fun _ : Fin 1 => a n))
      (Measure.infinitePi fun _ : ℕ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin 1 => μ)) := by
  have h := (measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin 1 => μ)).comp
    (measurePreserving_reindex μ (splitIndex n) (splitIndex_injective n))
  convert h using 1
  funext a; rfl

/-- **Joint law of past and fresh layer**: under the near-end growth
law, `(pastCoords W r, freshSample W r)` has law `pastLaw W r b ⊗ freshLaw W b`. -/
theorem growthPathLaw_map_past_fresh (W r : ℕ) (b : ℝ) :
    (growthPathLaw W b).map (fun ω => (pastCoords W r ω, freshSample W r ω)) =
      (pastLaw W r b).prod (freshLaw W b) := by
  set μA := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set μB := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have hA := measurePreserving_split μA r
  have hB0 := measurePreserving_split μB (r + 1)
  have hU : MeasurePreserving (fun (u : Fin 1 → Matrix (Fin W) (Fin W) ℂ) (_ : Fin 1) => u)
      (Measure.pi fun _ : Fin 1 => μB)
      (Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 => μB) := by
    have := (measurePreserving_funUnique (Measure.pi fun _ : Fin 1 => μB) (Fin 1)).symm
    convert this using 1
    · funext u; rfl
    · rfl
  have hB := ((MeasurePreserving.id (Measure.pi fun _ : Fin (r + 1) => μB)).prod hU).comp hB0
  have hAll := (measurePreserving_prodShuffle _ _ _ _).comp (hA.prod hB)
  have : (pastLaw W r b).prod (freshLaw W b) =
      ((Measure.pi fun _ : Fin r => μA).prod (Measure.pi fun _ : Fin (r + 1) => μB)).prod
        ((Measure.pi fun _ : Fin 1 => μA).prod
          (Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 => μB)) := rfl
  rw [this, ← hAll.map_eq]
  rfl

/-- The fresh coordinates of every growth step have the one-layer law `freshLaw W b`. -/
theorem growthPathLaw_map_freshSample (W r : ℕ) (b : ℝ) :
    (growthPathLaw W b).map (freshSample W r) = freshLaw W b := by
  have h := congrArg (fun ν => ν.map Prod.snd) (growthPathLaw_map_past_fresh W r b)
  rw [Measure.map_map measurable_snd ((measurable_pastCoords W r).prodMk
    (measurable_freshSample W r)), Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

theorem growthPathLaw_map_pastCoords (W r : ℕ) (b : ℝ) :
    (growthPathLaw W b).map (pastCoords W r) = pastLaw W r b := by
  have h := congrArg (fun ν => ν.map Prod.fst) (growthPathLaw_map_past_fresh W r b)
  rw [Measure.map_map measurable_fst ((measurable_pastCoords W r).prodMk
    (measurable_freshSample W r)), Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

/-- The fresh layer is independent of the past coordinates. -/
theorem indepFun_past_fresh (W r : ℕ) (b : ℝ) :
    IndepFun (pastCoords W r) (freshSample W r) (growthPathLaw W b) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_pastCoords W r).aemeasurable
    (measurable_freshSample W r).aemeasurable, growthPathLaw_map_past_fresh,
    growthPathLaw_map_pastCoords, growthPathLaw_map_freshSample]

/-- **Bridge (i), conditional law of the fresh layer**: the fresh layer
`(A_r, B_{r+1})` of the step `r → r+1` is independent of `growthSigma W r` and has law
`freshLaw W b` (`growthPathLaw_map_freshSample`). -/
theorem indep_growthSigma_fresh (W r : ℕ) (b : ℝ) :
    Indep (growthSigma W r) (MeasurableSpace.comap (freshSample W r) inferInstance)
      (growthPathLaw W b) :=
  (IndepFun_iff_Indep _ _ _).mp (indepFun_past_fresh W r b)

end BlockBand.Transmission.Bridge
