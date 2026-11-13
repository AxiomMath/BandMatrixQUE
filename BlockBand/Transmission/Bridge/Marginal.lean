module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The length-`r` marginal of the near-end-grown path

Growing at the near end produces, at each length, the same marginal law of the original path.

Main result: `growthPathLaw_map_pathAt` — for every `r ≥ 1`,
`(growthPathLaw W b).map (pathAt W r) = pathLaw W r b`.

The hypothesis `1 ≤ r` is necessary: `pathAt W 0` puts the same bond `B_0` on both ports
(`![ω.2 0, ω.2 0]`), while `pathLaw W 0 b` has two independent port bonds; for `W ≥ 1`,
`b > 0` the two laws differ. No object of the length-`0` path depends on its port bonds
(`pathPortCoupling` has no rows), and the near-end filtration starts at `r = 1`.

Also proved: probability instances for `gueMeasure`, `ginibreMeasure`, `layerLaw`, `pathLaw`
and `growthPathLaw`; invariance of `ginibreMeasure` under `conjTranspose`; and the iid
reindexing lemma `infinitePi_map_reindex` used by the fresh-layer bridge.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ENNReal NNReal ComplexConjugate Matrix

/-! ## Probability instances -/

theorem measurable_gueSample {ι : Type*} [Fintype ι] (t : ℝ≥0) :
    Measurable (gueSample (ι := ι) t) := by
  apply Measurable.of_eval_matrix
  intro a c
  simp only [gueSample, Matrix.of_apply]
  have h1 : Measurable fun X : ι × ι → ℂ => X (a, c) := measurable_pi_apply _
  have h2 : Measurable fun X : ι × ι → ℂ => X (c, a) := measurable_pi_apply _
  exact measurable_const.mul (h1.add (Complex.continuous_conj.measurable.comp h2))

theorem measurable_circularBrownianCoordinates {ι : Type*} :
    Measurable (BlockBand.SourceProcess.circularBrownianCoordinates (ι := ι)) := by
  apply Measurable.of_eval
  intro u
  unfold BlockBand.SourceProcess.circularBrownianCoordinates
  fun_prop

instance isProbabilityMeasure_gueMeasure (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    IsProbabilityMeasure (gueMeasure ι t) := by
  unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

/-- The Ginibre sample map `r ↦ (r(x,y,0) + i r(x,y,1))_{x,y}`. -/
def ginibreSample (ι κ : Type*) (r : ι × κ × Fin 2 → ℝ) : Matrix ι κ ℂ :=
  Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I

theorem measurable_ginibreSample (ι κ : Type*) : Measurable (ginibreSample ι κ) := by
  apply Measurable.of_eval_matrix
  intro x y
  simp only [ginibreSample, Matrix.of_apply]
  have h0 : Measurable fun r : ι × κ × Fin 2 → ℝ => r (x, y, 0) := measurable_pi_apply _
  have h1 : Measurable fun r : ι × κ × Fin 2 → ℝ => r (x, y, 1) := measurable_pi_apply _
  exact (Complex.measurable_ofReal.comp h0).add
    ((Complex.measurable_ofReal.comp h1).mul measurable_const)

theorem ginibreMeasure_eq (ι κ : Type*) [Fintype ι] [Fintype κ] (t : ℝ≥0) :
    ginibreMeasure ι κ t =
      (Measure.pi fun _ : ι × κ × Fin 2 => gaussianReal 0 (t / 2)).map (ginibreSample ι κ) :=
  rfl

instance isProbabilityMeasure_ginibreMeasure (ι κ : Type*) [Fintype ι] [Fintype κ] (t : ℝ≥0) :
    IsProbabilityMeasure (ginibreMeasure ι κ t) := by
  rw [ginibreMeasure_eq]
  infer_instance

instance isProbabilityMeasure_layerLaw (W : ℕ) (b : ℝ) (σ : LayerShape) :
    IsProbabilityMeasure (layerLaw W b σ) := by
  unfold layerLaw; infer_instance

instance isProbabilityMeasure_pathLaw (W r : ℕ) (b : ℝ) :
    IsProbabilityMeasure (pathLaw W r b) := by
  unfold pathLaw; infer_instance

instance isProbabilityMeasure_growthPathLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (growthPathLaw W b) := by
  unfold growthPathLaw; infer_instance

/-! ## Reindexing iid products -/

/-- A finite injective reindexing of an iid infinite product is the finite iid product. -/
theorem infinitePi_map_reindex {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {κ ι : Type*} [Fintype ι] (e : ι → κ) (he : Function.Injective e) :
    (Measure.infinitePi fun _ : κ => μ).map (fun ω i => ω (e i)) =
      Measure.pi fun _ : ι => μ := by
  classical
  have hm : Measurable fun (ω : κ → X) (i : ι) => ω (e i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  let t : κ → Set X := Function.extend e s fun _ => Set.univ
  have ht : ∀ i, t (e i) = s i := fun i => he.extend_apply _ _ _
  have htm : ∀ k, MeasurableSet (t k) := by
    intro k
    by_cases hk : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := hk; rw [ht]; exact hs i
    · simp only [t, Function.extend_apply' _ _ _ hk]; exact MeasurableSet.univ
  have hpre : (fun (ω : κ → X) (i : ι) => ω (e i)) ⁻¹' Set.univ.pi s =
      Set.pi ((Finset.univ.map ⟨e, he⟩ : Finset κ) : Set κ) t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map,
      Finset.coe_univ, Set.image_univ, Set.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro h _ ⟨i, rfl⟩; rw [ht]; exact h i (Set.mem_univ _)
    · intro h i _; rw [← ht]; exact h _ ⟨i, rfl⟩
  rw [hpre, Measure.infinitePi_pi _ (fun k _ => htm k), Finset.prod_map]
  simp only [Function.Embedding.coeFn_mk, ht]

theorem measurePreserving_reindex {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {κ ι : Type*} [Fintype ι] (e : ι → κ) (he : Function.Injective e) :
    MeasurePreserving (fun (ω : κ → X) (i : ι) => ω (e i))
      (Measure.infinitePi fun _ : κ => μ) (Measure.pi fun _ : ι => μ) :=
  ⟨Measurable.of_eval fun _ => measurable_pi_apply _, infinitePi_map_reindex μ e he⟩

/-- A permutation of the coordinates preserves a finite iid product. -/
theorem pi_map_perm {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {ι : Type*} [Fintype ι] (σ : ι ≃ ι) :
    (Measure.pi fun _ : ι => μ).map (fun r i => r (σ i)) = Measure.pi fun _ : ι => μ := by
  classical
  have hm : Measurable fun (r : ι → X) (i : ι) => r (σ i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (r : ι → X) (i : ι) => r (σ i)) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun j => s (σ.symm j) := by
    ext r
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h j; simpa using h (σ.symm j)
    · intro h i; simpa using h (σ i)
  rw [hpre, Measure.pi_pi]
  exact Fintype.prod_equiv σ.symm _ _ (fun _ => rfl)

/-! ## Ginibre invariance under `conjTranspose` -/

/-- `Gin(t)` is invariant under `B ↦ Bᴴ` (the internal bonds of `pathAt` are `B_kᴴ`). -/
theorem ginibreMeasure_map_conjTranspose (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    (ginibreMeasure ι ι t).map Matrix.conjTranspose = ginibreMeasure ι ι t := by
  classical
  let σ : ι × ι × Fin 2 ≃ ι × ι × Fin 2 :=
    { toFun := fun p => (p.2.1, p.1, p.2.2)
      invFun := fun p => (p.2.1, p.1, p.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f : ι × ι × Fin 2 → ℝ → ℝ := fun p x => if p.2.2 = 0 then x else -x
  have hf : ∀ p, Measurable (f p) := by
    intro p; by_cases h : p.2.2 = 0
    · simp only [f, h, ite_true]; exact measurable_id
    · simp only [f, h, ite_false]; exact measurable_neg
  have hfμ : ∀ p, (gaussianReal 0 (t / 2)).map (f p) = gaussianReal 0 (t / 2) := by
    intro p; by_cases h : p.2.2 = 0
    · simp only [f, h, ite_true]; exact Measure.map_id
    · simp only [f, h, ite_false]; rw [gaussianReal_map_neg, neg_zero]
  have hconj : Matrix.conjTranspose ∘ ginibreSample ι ι =
      ginibreSample ι ι ∘ (fun r p => f p (r p)) ∘ (fun r i => r (σ i)) := by
    funext r
    ext x y
    have h1 : (1 : Fin 2) ≠ 0 := by decide
    simp [ginibreSample, f, σ, h1]
  have hmc : Measurable (Matrix.conjTranspose : Matrix ι ι ℂ → Matrix ι ι ℂ) := by
    apply Measurable.of_eval_matrix
    intro x y
    simp only [Matrix.conjTranspose_apply]
    exact Complex.continuous_conj.measurable.comp (Matrix.measurable_apply)
  have hmσ : Measurable fun (r : ι × ι × Fin 2 → ℝ) (i : ι × ι × Fin 2) => r (σ i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hmf : Measurable fun (r : ι × ι × Fin 2 → ℝ) (p : ι × ι × Fin 2) => f p (r p) :=
    Measurable.of_eval fun p => (hf p).comp (measurable_pi_apply p)
  rw [ginibreMeasure_eq, Measure.map_map hmc (measurable_ginibreSample ι ι), hconj,
    ← Measure.map_map (measurable_ginibreSample ι ι) (hmf.comp hmσ),
    ← Measure.map_map hmf hmσ, pi_map_perm,
    Measure.pi_map_pi (fun p => (hf p).aemeasurable)]
  simp only [hfμ]

theorem measurePreserving_conjTranspose_pi {n : Type*} [Fintype n] (ι : Type*) [Fintype ι]
    (t : ℝ≥0) :
    MeasurePreserving (fun (v : n → Matrix ι ι ℂ) i => (v i)ᴴ)
      (Measure.pi fun _ : n => ginibreMeasure ι ι t)
      (Measure.pi fun _ : n => ginibreMeasure ι ι t) := by
  have hmc : Measurable (Matrix.conjTranspose : Matrix ι ι ℂ → Matrix ι ι ℂ) := by
    apply Measurable.of_eval_matrix
    intro x y
    simp only [Matrix.conjTranspose_apply]
    exact Complex.continuous_conj.measurable.comp (Matrix.measurable_apply)
  refine ⟨Measurable.of_eval fun i => hmc.comp (measurable_pi_apply i), ?_⟩
  have := Measure.pi_map_pi (μ := fun _ : n => ginibreMeasure ι ι t)
    (f := fun _ => Matrix.conjTranspose) (fun _ => hmc.aemeasurable)
  rw [this]
  simp only [ginibreMeasure_map_conjTranspose]

/-! ## Bridge (v) -/

/-- Index map of the bonds of the length-`r` path into the growth sequence: internal bond `i`
is `B_{r-1-i}`, near port `B_r`, far port `B_0`. -/
def bondIndex (r : ℕ) : Fin (r - 1) ⊕ Fin 2 → ℕ
  | Sum.inl i => r - 1 - i.val
  | Sum.inr j => if j = 0 then r else 0

theorem bondIndex_injective {r : ℕ} (hr : 1 ≤ r) : Function.Injective (bondIndex r) := by
  rintro (i | i) (j | j) h <;> simp only [bondIndex] at h
  · have := i.isLt; have := j.isLt
    exact congrArg Sum.inl (Fin.ext (by omega))
  · have := i.isLt
    fin_cases j <;> simp at h <;> omega
  · have := j.isLt
    fin_cases i <;> simp at h <;> omega
  · fin_cases i <;> fin_cases j <;> simp_all
    all_goals omega

theorem blockIndex_injective (r : ℕ) : Function.Injective fun i : Fin r => r - 1 - i.val := by
  intro i j h
  have := i.isLt; have := j.isLt
  exact Fin.ext (by simp only at h; omega)

/-- **The marginal of the grown path**: for every length `r ≥ 1`, the length-`r` path read from
the near-end-grown sample has exactly the law `Layers.pathLaw W r b`. -/
theorem growthPathLaw_map_pathAt (W : ℕ) (b : ℝ) {r : ℕ} (hr : 1 ≤ r) :
    (growthPathLaw W b).map (pathAt W r) = pathLaw W r b := by
  set μA := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set μB := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  -- the block part
  have hA : MeasurePreserving (fun (a : ℕ → Matrix (Fin W) (Fin W) ℂ) (i : Fin r) =>
      a (r - 1 - i.val)) (Measure.infinitePi fun _ : ℕ => μA) (Measure.pi fun _ : Fin r => μA) :=
    measurePreserving_reindex μA _ (blockIndex_injective r)
  -- the bond part
  have hB0 := measurePreserving_reindex μB (bondIndex r) (bondIndex_injective hr)
  have hB1 := measurePreserving_sumPiEquivProdPi (fun _ : Fin (r - 1) ⊕ Fin 2 => μB)
  have hB2 := (measurePreserving_conjTranspose_pi (n := Fin (r - 1)) (Fin W)
    (Real.toNNReal (b / W))).prod (MeasurePreserving.id (Measure.pi fun _ : Fin 2 => μB))
  have hB := (hB2.comp hB1).comp hB0
  have hAll := hA.prod hB
  have hfun : pathAt W r = Prod.map
      (fun (a : ℕ → Matrix (Fin W) (Fin W) ℂ) (i : Fin r) => a (r - 1 - i.val))
      ((Prod.map (fun (v : Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ) i => (v i)ᴴ) id ∘
        MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (r - 1) ⊕ Fin 2 =>
          Matrix (Fin W) (Fin W) ℂ)) ∘
        fun (ω : ℕ → Matrix (Fin W) (Fin W) ℂ) j => ω (bondIndex r j)) := by
    funext ω
    simp only [pathAt, Prod.map, Function.comp, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.coe_mk, Equiv.sumPiEquivProdPi_apply, id, bondIndex]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext j
    fin_cases j <;> rfl
  rw [hfun]
  exact hAll.map_eq

end BlockBand.Transmission.Bridge
