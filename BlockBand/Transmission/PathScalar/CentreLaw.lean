module

public import BlockBand.Transmission.PathScalar.CentreSchur

/-!
# Centre growth, law part: one separate-port layer grows `pathLaw W r b` into `pathLaw W (r+2) b`

Main result `newPath_law` (`r ≥ 1`): if `inner ~ pathLaw W r b` and `ℓ ~ layerLaw W b .separate`
are independent, then `newPath inner ℓ ~ pathLaw W (r+2) b`. Ingredients: a 4-factor product
rearrangement (`measurePreserving_prodProdProdComm`), iid reindexing along an equivalence
`ι ⊕ κ ≃ ν` (`map_sumElim_pi`), Ginibre invariance under `ᴴ` (`ginibreMeasure_map_conjTranspose`,
for the old near bond, which becomes the new internal bond `0` as `(B_near)ᴴ`), and the
diagonal marginal of the layer bonds (`map_diag_pi`; the off-diagonal `.separate` bonds are
unused).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.Bridge
open scoped ENNReal NNReal Matrix

variable {W : ℕ}

/-!
## Generic product and iid lemmas
-/

/-- `(A × B) × (C × D) → (A × C) × (B × D)` preserves product measures. -/
theorem measurePreserving_prodProdProdComm {A B C D : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D] (μa : Measure A) (μb : Measure B)
    (μc : Measure C) (μd : Measure D) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun x : (A × B) × (C × D) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd).symm
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm
  exact (((h5.comp h4).comp h3).comp h2).comp h1

/-- iid reindexing along `e : ι ⊕ κ ≃ ν`: `(x, y) ↦ (Sum.elim x y ∘ e.symm)` maps
`μ^ι ⊗ μ^κ` to `μ^ν`. -/
theorem map_sumElim_pi {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ν] (e : ι ⊕ κ ≃ ν) :
    MeasurePreserving (fun x : (ι → X) × (κ → X) => fun i => Sum.elim x.1 x.2 (e.symm i))
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : κ => μ))
      (Measure.pi fun _ : ν => μ) := by
  classical
  have hm : Measurable fun x : (ι → X) × (κ → X) => fun i => Sum.elim x.1 x.2 (e.symm i) := by
    refine Measurable.of_eval fun i => ?_
    rcases h : e.symm i with k | k
    · exact (measurable_pi_apply k).comp measurable_fst
    · exact (measurable_pi_apply k).comp measurable_snd
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : (ι → X) × (κ → X) => fun i => Sum.elim x.1 x.2 (e.symm i)) ⁻¹'
      Set.univ.pi s = (Set.univ.pi fun k => s (e (Sum.inl k))) ×ˢ
        (Set.univ.pi fun k => s (e (Sum.inr k))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      exact ⟨fun k => by simpa using h (e (Sum.inl k)), fun k => by simpa using h (e (Sum.inr k))⟩
    · rintro ⟨h1, h2⟩ i
      rcases h : e.symm i with k | k
      · have := h1 k; rw [← h, Equiv.apply_symm_apply] at this; simpa [h] using this
      · have := h2 k; rw [← h, Equiv.apply_symm_apply] at this; simpa [h] using this
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi,
    ← Fintype.prod_equiv e (fun j => μ (s (e j))) (fun i => μ (s i)) (fun _ => rfl),
    Fintype.prod_sum_type]

/-- The diagonal of an iid double array: `B ↦ (B i i)_i`. -/
theorem map_diag_pi {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    MeasurePreserving (fun (B : ι → ι → X) i => B i i)
      (Measure.pi fun _ : ι => Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) := by
  refine ⟨Measurable.of_eval fun i => (measurable_pi_apply i).comp (measurable_pi_apply i), ?_⟩
  rw [Measure.pi_map_pi (f := fun i (v : ι → X) => v i)
    (fun i => (measurable_pi_apply i).aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : ι => μ) i).map_eq

/-!
## Position equivalences of the grown path
-/

/-- Block positions of the grown path: new end blocks `0 ↦ 0`, `1 ↦ r+1`; old block `i ↦ i+1`. -/
def blockPos (r : ℕ) : Fin 2 ⊕ Fin r ≃ Fin (r + 2) where
  toFun
    | Sum.inl a => ⟨if a.val = 0 then 0 else r + 1, by split_ifs <;> omega⟩
    | Sum.inr i => ⟨i.val + 1, by have := i.isLt; omega⟩
  invFun p :=
    if h0 : p.val = 0 then Sum.inl 0
    else if h1 : p.val = r + 1 then Sum.inl 1
    else Sum.inr ⟨p.val - 1, by have := p.isLt; omega⟩
  left_inv := by
    rintro (a | i)
    · fin_cases a <;> simp
    · have := i.isLt
      have h : ¬ (i.val = r) := by omega
      simp [h]
  right_inv := by
    intro p
    have := p.isLt
    by_cases h0 : p.val = 0
    · simp only [h0, dite_true]; ext; simp [h0]
    · by_cases h1 : p.val = r + 1
      · simp only [h1, dite_true]; ext; simp [h1]
      · simp only [h0, h1, dite_false]; ext; simp; omega

/-- Bond positions of the grown path (`r ≥ 1`): old near port bond `0 ↦ 0`, old far port bond
`1 ↦ r`; old internal bond `j ↦ j+1`. -/
def bondPos (r : ℕ) (hr : 1 ≤ r) : Fin 2 ⊕ Fin (r - 1) ≃ Fin (r + 1) where
  toFun
    | Sum.inl a => ⟨if a.val = 0 then 0 else r, by split_ifs <;> omega⟩
    | Sum.inr j => ⟨j.val + 1, by have := j.isLt; omega⟩
  invFun p :=
    if h0 : p.val = 0 then Sum.inl 0
    else if h1 : p.val = r then Sum.inl 1
    else Sum.inr ⟨p.val - 1, by have := p.isLt; omega⟩
  left_inv := by
    rintro (a | j)
    · fin_cases a
      · simp
      · have h : ¬ (r = 0) := by omega
        simp [h]
    · have := j.isLt
      have h : ¬ (j.val + 1 = r) := by omega
      simp [h]
  right_inv := by
    intro p
    have := p.isLt
    by_cases h0 : p.val = 0
    · simp only [h0, dite_true]; ext; simp [h0]
    · by_cases h1 : p.val = r
      · have hr0 : ¬ r = 0 := by omega
        simp only [h1, hr0, dite_true, dite_false]; ext; simp; omega
      · simp only [h0, h1, dite_false]; ext; simp; omega

/-!
## The law of the grown path
-/

/-- Conjugate-transpose the first of two bonds (the old near port bond becomes the new internal
bond `0` with the `pathMatrix` orientation). -/
def conjFirst (p : Fin 2 → Matrix (Fin W) (Fin W) ℂ) : Fin 2 → Matrix (Fin W) (Fin W) ℂ :=
  fun k => (if k = 0 then Matrix.conjTranspose else id) (p k)

theorem measurePreserving_conjFirst (t : ℝ≥0) :
    MeasurePreserving (conjFirst (W := W))
      (Measure.pi fun _ : Fin 2 => ginibreMeasure (Fin W) (Fin W) t)
      (Measure.pi fun _ : Fin 2 => ginibreMeasure (Fin W) (Fin W) t) := by
  have hmc : Measurable (Matrix.conjTranspose : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ) :=
    Measurable.of_eval_matrix _ fun x y => by
      simp only [Matrix.conjTranspose_apply]
      exact Complex.continuous_conj.measurable.comp Matrix.measurable_apply
  have hf : ∀ k : Fin 2, Measurable
      (if k = 0 then Matrix.conjTranspose else id : Matrix (Fin W) (Fin W) ℂ → _) := fun k => by
    split_ifs
    · exact hmc
    · exact measurable_id
  refine ⟨Measurable.of_eval fun k => (hf k).comp (measurable_pi_apply k), ?_⟩
  rw [show (conjFirst (W := W)) = fun p k => (if k = 0 then Matrix.conjTranspose else id) (p k)
    from rfl, Measure.pi_map_pi (fun k => (hf k).aemeasurable)]
  congr 1
  funext k
  split_ifs
  · exact ginibreMeasure_map_conjTranspose (Fin W) t
  · exact Measure.map_id

/-- `newPath` through the position equivalences. -/
theorem newPath_eq {r : ℕ} (hr : 1 ≤ r) (inner : PathSample W r) (ℓ : LayerSample W .separate) :
    newPath inner ℓ =
      (fun i => Sum.elim ℓ.1 inner.1 ((blockPos r).symm i),
       fun j => Sum.elim (conjFirst inner.2.2) inner.2.1 ((bondPos r hr).symm j),
       fun i => ℓ.2 i i) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    simp only [newPath, blockPos, Equiv.coe_fn_symm_mk]
    split_ifs <;> rfl
  · funext j
    simp only [newPath, bondPos, Equiv.coe_fn_symm_mk]
    split_ifs <;> simp [conjFirst]
  · funext i
    fin_cases i <;> rfl

/-- **One layer of centre growth preserves the path law**: for `r ≥ 1`,
`newPath` maps `pathLaw W r b ⊗ layerLaw W b .separate` to `pathLaw W (r+2) b`. -/
theorem newPath_law (b : ℝ) {r : ℕ} (hr : 1 ≤ r) :
    MeasurePreserving (fun x : PathSample W r × LayerSample W .separate => newPath x.1 x.2)
      ((pathLaw W r b).prod (layerLaw W b .separate)) (pathLaw W (r + 2) b) := by
  set μA := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set μB := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have hP := measurePreserving_prodProdProdComm (Measure.pi fun _ : Fin r => μA)
    ((Measure.pi fun _ : Fin (r - 1) => μB).prod (Measure.pi fun _ : Fin 2 => μB))
    (Measure.pi fun _ : Fin 2 => μA) (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μB)
  have hS := (Measure.measurePreserving_swap (μ := Measure.pi fun _ : Fin r => μA)
    (ν := Measure.pi fun _ : Fin 2 => μA)).prod
    ((Measure.measurePreserving_swap (μ := Measure.pi fun _ : Fin (r - 1) => μB)
      (ν := Measure.pi fun _ : Fin 2 => μB)).prod
      (MeasurePreserving.id (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μB)))
  have hC := (MeasurePreserving.id ((Measure.pi fun _ : Fin 2 => μA).prod
    (Measure.pi fun _ : Fin r => μA))).prod
    (((measurePreserving_conjFirst (W := W) (Real.toNNReal (b / W))).prod
      (MeasurePreserving.id (Measure.pi fun _ : Fin (r - 1) => μB))).prod
      (MeasurePreserving.id (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μB)))
  have hF := (map_sumElim_pi μA (blockPos r)).prod
    ((map_sumElim_pi μB (bondPos r hr)).prod (map_diag_pi μB (ι := Fin 2)))
  have h := ((hF.comp hC).comp hS).comp hP
  have hfun : (fun x : PathSample W r × LayerSample W .separate => newPath x.1 x.2) = fun x =>
      (fun i => Sum.elim x.2.1 x.1.1 ((blockPos r).symm i),
       fun j => Sum.elim (conjFirst x.1.2.2) x.1.2.1 ((bondPos r hr).symm j),
       fun i => x.2.2 i i) :=
    funext fun x => newPath_eq hr x.1 x.2
  rw [hfun]
  exact h

end BlockBand.Transmission.PathScalar
