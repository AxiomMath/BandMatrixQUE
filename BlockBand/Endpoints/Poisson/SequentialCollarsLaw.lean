module

public import BlockBand.Endpoints.Poisson.SequentialCollarsNetwork
public import BlockBand.Internal.Contracts.Layers

/-!
# Sequential collar removal: the original Gaussian prior and the fresh collar

Items (i) and (iii) of the sequential collars lemma. Item (i), first clause (Steps 1–2 of the
proof): "the selected fresh collar
consists of its three GUE diagonals and its two internal Ginibre bonds, independent of the entire
old network".

* **Law.** `ringCoordLaw n W b`: all blocks `GUE_W(c/W)` (`CoareaPalm.gueMeasure`, `c = 1 - 2b`)
  and all forward bonds `Gin(b/W)` (`Layers.ginibreMeasure`), jointly independent (product
  measure), the same laws as `Layers.pathLaw`. This is the original prior in Gaussian
  coordinates; its identification with `IsPhysicalGaussianRingLaw` is
  `CoordinatePriorIsPhysical`, proved as `coordinatePriorIsPhysical`.
  `collarLaw W b = GUE³ ⊗ Gin²`.
* `hasLaw_freshCollar`: `freshCollar L s k` has law `collarLaw W b`;
  `indepFun_freshCollar_oldCoords`: it is independent of all other coordinates;
  `indepFun_freshCollar_oldNetwork`: hence of the old network `(M_κ, C_o)` at every stage of
  either pairing, for every `κ`. All statements are under the unconditioned prior.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure)
open BlockBand.Internal.Contracts.Layers (ginibreMeasure)

section Law

variable {m n W : ℕ} (L : Fin m → ℕ) (s : ZMod n)

/-- `GUE_d(t)` is a probability measure. -/
theorem isProbabilityMeasure_gue' (ι : Type*) [Fintype ι] (t : NNReal) :
    IsProbabilityMeasure (gueMeasure ι t) := by
  unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

/-- `Gin(t)` is a probability measure. -/
theorem isProbabilityMeasure_gin' (ι κ : Type*) [Fintype ι] [Fintype κ] (t : NNReal) :
    IsProbabilityMeasure (ginibreMeasure ι κ t) := by
  unfold ginibreMeasure
  infer_instance

/-- `GUE_W(c/W)`, `c = 1 - 2b`. -/
abbrev gueBlockLaw (W : ℕ) (b : ℝ) : Measure (Matrix (Fin W) (Fin W) ℂ) :=
  gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))

/-- `Gin(b/W)`. -/
abbrev ginBondLaw (W : ℕ) (b : ℝ) : Measure (Matrix (Fin W) (Fin W) ℂ) :=
  ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))

instance (W : ℕ) (b : ℝ) : IsProbabilityMeasure (gueBlockLaw W b) := isProbabilityMeasure_gue' _ _
instance (W : ℕ) (b : ℝ) : IsProbabilityMeasure (ginBondLaw W b) := isProbabilityMeasure_gin' _ _ _

/-- The original prior in Gaussian coordinates. -/
def ringCoordLaw (n W : ℕ) [NeZero n] (b : ℝ) : Measure (RingCoords n W) :=
  (Measure.pi fun _ : ZMod n => gueBlockLaw W b).prod (Measure.pi fun _ : ZMod n => ginBondLaw W b)

/-- Law of a fresh collar. -/
def collarLaw (W : ℕ) (b : ℝ) : Measure (CollarSample W) :=
  (Measure.pi fun _ : Fin 3 => gueBlockLaw W b).prod (Measure.pi fun _ : Fin 2 => ginBondLaw W b)

instance [NeZero n] (b : ℝ) : IsProbabilityMeasure (ringCoordLaw n W b) := by
  unfold ringCoordLaw; infer_instance

/-- All Gaussian coordinates, indexed by `blocks ⊕ bonds`. -/
def ringCoord : ZMod n ⊕ ZMod n → RingCoords n W → Matrix (Fin W) (Fin W) ℂ
  | Sum.inl p => fun ω => ω.1 p
  | Sum.inr p => fun ω => ω.2 p

/-- Marginal law of each coordinate. -/
def ringCoordMarginal (W : ℕ) (b : ℝ) : ZMod n ⊕ ZMod n → Measure (Matrix (Fin W) (Fin W) ℂ) :=
  Sum.elim (fun _ => gueBlockLaw W b) (fun _ => ginBondLaw W b)

instance (b : ℝ) (i : ZMod n ⊕ ZMod n) : IsProbabilityMeasure (ringCoordMarginal W b i) := by
  cases i <;> simp only [ringCoordMarginal, Sum.elim_inl, Sum.elim_inr] <;> infer_instance

theorem measurable_ringCoord (i : ZMod n ⊕ ZMod n) : Measurable (ringCoord (W := W) i) := by
  cases i
  · exact (measurable_pi_apply _).comp measurable_fst
  · exact (measurable_pi_apply _).comp measurable_snd

theorem hasLaw_ringCoord_vector [NeZero n] (b : ℝ) :
    HasLaw (fun ω i => ringCoord (W := W) i ω) (Measure.pi (ringCoordMarginal W b))
      (ringCoordLaw n W b) := by
  have h := (measurePreserving_sumPiEquivProdPi (ringCoordMarginal (n := n) W b)).symm
  have heq : (fun ω i => ringCoord (W := W) i ω) =
      ⇑(MeasurableEquiv.sumPiEquivProdPi
        fun _ : ZMod n ⊕ ZMod n => Matrix (Fin W) (Fin W) ℂ).symm := by
    funext ω i
    cases i <;> rfl
  rw [heq]
  exact h.hasLaw

/-- Under the prior all coordinates are independent with their GUE / Ginibre marginals. -/
theorem iIndepFun_ringCoord [NeZero n] (b : ℝ) :
    iIndepFun (ringCoord (W := W)) (ringCoordLaw n W b) ∧
      ∀ i, HasLaw (ringCoord (W := W) i) (ringCoordMarginal W b i) (ringCoordLaw n W b) := by
  have hv := hasLaw_ringCoord_vector (n := n) (W := W) b
  have hm : ∀ i, HasLaw (ringCoord (W := W) i) (ringCoordMarginal W b i) (ringCoordLaw n W b) := by
    intro i
    have := (measurePreserving_eval (ringCoordMarginal (n := n) W b) i).comp_hasLaw hv
    exact this
  exact ⟨(iIndepFun_iff_hasLaw_pi_pi hm).mpr hv, hm⟩

/-!
### The fresh collar coordinates
-/

variable {L s}

variable (L s) in
/-- The five coordinates of collar `k`: diagonals at offsets `0,1,2`, bonds at offsets `0,1`. -/
def collarIdx (k : Fin m) : Fin 3 ⊕ Fin 2 → ZMod n ⊕ ZMod n
  | Sum.inl o => Sum.inl (unitPos n L s k o.val)
  | Sum.inr o => Sum.inr (unitPos n L s k o.val)

theorem collarIdx_injective (hL : IsCollarLayout n L) (k : Fin m) :
    Function.Injective (collarIdx L s k) := by
  have := hL.2 k
  rintro (o | o) (o' | o') h <;> simp only [collarIdx, Sum.inl.injEq, Sum.inr.injEq,
    reduceCtorEq] at h
  · exact congrArg Sum.inl (Fin.ext ((unitPos_inj hL s (by omega) (by omega)).mp h).2)
  · exact congrArg Sum.inr (Fin.ext ((unitPos_inj hL s (by omega) (by omega)).mp h).2)

theorem freshCollar_eq (k : Fin m) (ω : RingCoords n W) :
    freshCollar L s k ω = MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin 3 ⊕ Fin 2 => Matrix (Fin W) (Fin W) ℂ)
      (fun j => ringCoord (collarIdx L s k j) ω) := rfl

/-- The fresh collar has the law `GUE³ ⊗ Gin²`. -/
theorem hasLaw_freshCollar [NeZero n] (hL : IsCollarLayout n L) (k : Fin m) (b : ℝ) :
    HasLaw (freshCollar L s k) (collarLaw W b) (ringCoordLaw n W b) := by
  obtain ⟨hI, hm⟩ := iIndepFun_ringCoord (n := n) (W := W) b
  have hI' := hI.precomp (collarIdx_injective (s := s) hL k)
  have hv : HasLaw (fun ω j => ringCoord (W := W) (collarIdx L s k j) ω)
      (Measure.pi fun j => ringCoordMarginal W b (collarIdx L s k j)) (ringCoordLaw n W b) :=
    hI'.hasLaw_pi fun j => hm _
  have hmp := measurePreserving_sumPiEquivProdPi
    (fun j : Fin 3 ⊕ Fin 2 => ringCoordMarginal (n := n) W b (collarIdx L s k j))
  have := hmp.comp_hasLaw hv
  exact this

variable (L s) in
/-- Index set of the old (non-collar-`k`) coordinates. -/
def oldCoordSet [NeZero n] (k : Fin m) : Finset (ZMod n ⊕ ZMod n) :=
  (Finset.univ.image (collarIdx L s k))ᶜ

variable (L s) in
/-- All coordinates outside the selected collar: the entire old network's variables. -/
def oldCoords [NeZero n] (k : Fin m) (ω : RingCoords n W) :
    oldCoordSet L s k → Matrix (Fin W) (Fin W) ℂ :=
  fun i => ringCoord i.1 ω

/-- Item (i), first clause: the fresh collar is independent of all old coordinates. -/
theorem indepFun_freshCollar_oldCoords [NeZero n] (k : Fin m) (b : ℝ) :
    IndepFun (freshCollar L s k) (oldCoords L s k) (ringCoordLaw n W b) := by
  obtain ⟨hI, -⟩ := iIndepFun_ringCoord (n := n) (W := W) b
  have h := hI.indepFun_finset (Finset.univ.image (collarIdx L s k)) (oldCoordSet L s k)
    disjoint_compl_right (measurable_ringCoord)
  have hF : Measurable fun t : (Finset.univ.image (collarIdx L s k) : Finset _) →
      Matrix (Fin W) (Fin W) ℂ =>
      MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 2 => Matrix (Fin W) (Fin W) ℂ)
        (fun j => t ⟨collarIdx L s k j, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩) := by
    refine (MeasurableEquiv.measurable _).comp ?_
    exact Measurable.of_eval fun j => measurable_pi_apply _
  exact h.comp hF measurable_id

/-- The stage matrix is a measurable function of the coordinates. -/
theorem measurable_stageFull [NeZero n] (π : Pairing) (S : Finset (Fin m)) (e : ℝ) (z : ℂ)
    (buf : ℕ) (κ : ℝ) : Measurable (stageFull (W := W) L s π S e z buf κ) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [stageFull, stageHerm, Matrix.add_apply]
  have h1 : ∀ p a b, Measurable fun ω : RingCoords n W => ω.1 p a b :=
    fun p a b => (Matrix.measurable_apply).comp ((measurable_pi_apply p).comp measurable_fst)
  have h2 : ∀ p a b, Measurable fun ω : RingCoords n W => ω.2 p a b :=
    fun p a b => (Matrix.measurable_apply).comp ((measurable_pi_apply p).comp measurable_snd)
  refine Measurable.add (Measurable.add (Measurable.add ?_ ?_) ?_) measurable_const <;>
    split_ifs <;>
    first
    | exact measurable_const
    | exact (h1 _ _ _).sub measurable_const
    | exact h2 _ _ _
    | exact continuous_star.measurable.comp (h2 _ _ _)

theorem mem_oldCoordSet_inl [NeZero n] (k : Fin m) (p : ZMod n) :
    Sum.inl p ∈ oldCoordSet L s k ↔ ¬ InCollar L s k p := by
  simp only [oldCoordSet, Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and]
  apply not_congr
  constructor
  · rintro ⟨(o | o), ho⟩ <;> simp only [collarIdx, Sum.inl.injEq, reduceCtorEq] at ho
    fin_cases o
    · exact Or.inl ho.symm
    · exact Or.inr (Or.inl ho.symm)
    · exact Or.inr (Or.inr ho.symm)
  · rintro (h | h | h)
    · exact ⟨Sum.inl 0, by simp [collarIdx, h]⟩
    · exact ⟨Sum.inl 1, by simp [collarIdx, h]⟩
    · exact ⟨Sum.inl 2, by simp [collarIdx, h]⟩

theorem mem_oldCoordSet_inr [NeZero n] (k : Fin m) (p : ZMod n) :
    Sum.inr p ∈ oldCoordSet L s k ↔ ¬ (p = unitPos n L s k 0 ∨ p = unitPos n L s k 1) := by
  simp only [oldCoordSet, Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and]
  apply not_congr
  constructor
  · rintro ⟨(o | o), ho⟩ <;> simp only [collarIdx, Sum.inr.injEq, reduceCtorEq] at ho
    fin_cases o
    · exact Or.inl ho.symm
    · exact Or.inr ho.symm
  · rintro (h | h)
    · exact ⟨Sum.inr 0, by simp [collarIdx, h]⟩
    · exact ⟨Sum.inr 1, by simp [collarIdx, h]⟩

/-- Entries touching an old site only use old coordinates. -/
theorem stageFull_congr_old (hL : IsCollarLayout n L) (π : Pairing) (S : Finset (Fin m))
    (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) {ω ω' : RingCoords n W}
    (hA : ∀ p, ¬ InCollar L s k p → ω.1 p = ω'.1 p)
    (hB : ∀ p, ¬ (p = unitPos n L s k 0 ∨ p = unitPos n L s k 1) → ω.2 p = ω'.2 p)
    {x y : RingSite n W} (hx : ¬ InCollar L s k x.1) (hy : y.1 ≠ unitPos n L s k 1) :
    stageFull L s π S e z buf κ ω x y = stageFull L s π S e z buf κ ω' x y ∧
      stageFull L s π S e z buf κ ω y x = stageFull L s π S e z buf κ ω' y x := by
  obtain ⟨p, a⟩ := x
  obtain ⟨q, c⟩ := y
  simp only at hx hy ⊢
  have hxB : ¬ (p = unitPos n L s k 0 ∨ p = unitPos n L s k 1) :=
    fun h => hx (h.elim Or.inl (fun h => Or.inr (Or.inl h)))
  have hyB : bondTarget L s π q = p → ¬ (q = unitPos n L s k 0 ∨ q = unitPos n L s k 1) := by
    rintro ht (h | h)
    · rw [h, bondTarget_collar hL π k (by norm_num)] at ht
      exact hx (Or.inr (Or.inl ht.symm))
    · exact hy h
  have hA' := hA p hx
  have hB' := hB p hxB
  by_cases hxy : q = p
  · subst hxy
    constructor <;> simp only [stageFull, stageHerm, Matrix.add_apply, ite_true, hA', hB']
  · have hxy' : ¬ p = q := fun h => hxy h.symm
    constructor <;>
    · simp only [stageFull, stageHerm, Matrix.add_apply, hxy, hxy', ite_false, hB']
      by_cases ht : bondTarget L s π q = p
      · simp only [ht, ite_true, hB q (hyB ht)]
      · simp only [ht, ite_false]

/-- `(M_κ, C_o)` depends only on the old coordinates. -/
theorem oldNetwork_congr [NeZero n] (hL : IsCollarLayout n L) (π : Pairing) (S : Finset (Fin m))
    (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) {ω ω' : RingCoords n W}
    (h : oldCoords L s k ω = oldCoords L s k ω') :
    oldInterior L s π S k e z buf κ ω = oldInterior L s π S k e z buf κ ω' ∧
      oldCoupling L s π S k e z buf κ ω = oldCoupling L s π S k e z buf κ ω' := by
  have hA : ∀ p, ¬ InCollar L s k p → ω.1 p = ω'.1 p := fun p hp =>
    congrFun h ⟨Sum.inl p, (mem_oldCoordSet_inl k p).mpr hp⟩
  have hB : ∀ p, ¬ (p = unitPos n L s k 0 ∨ p = unitPos n L s k 1) → ω.2 p = ω'.2 p :=
    fun p hp => congrFun h ⟨Sum.inr p, (mem_oldCoordSet_inr k p).mpr hp⟩
  constructor
  · ext x y
    exact (stageFull_congr_old hL π S k e z buf κ hA hB x.2.2
      (fun hy => y.2.2 (Or.inr (Or.inl hy)))).1
  · ext x i
    exact (stageFull_congr_old hL π S k e z buf κ hA hB x.2.2
      (unitPos_ne hL (by have := i.1.isLt; omega) (by have := hL.2 k; omega)
        (by have := i.1.isLt; omega))).1

variable (L s) in
/-- Rebuild a full sample from the old coordinates (collar coordinates set to `0`). -/
def glueOld [NeZero n] (k : Fin m) (t : oldCoordSet L s k → Matrix (Fin W) (Fin W) ℂ) :
    RingCoords n W :=
  (fun p => if h : Sum.inl p ∈ oldCoordSet L s k then t ⟨_, h⟩ else 0,
    fun p => if h : Sum.inr p ∈ oldCoordSet L s k then t ⟨_, h⟩ else 0)

theorem measurable_glueOld [NeZero n] (k : Fin m) :
    Measurable (glueOld (W := W) L s k) := by
  refine Measurable.prodMk ?_ ?_ <;>
  · refine Measurable.of_eval fun p => ?_
    split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const

theorem oldCoords_glueOld [NeZero n] (k : Fin m) (ω : RingCoords n W) :
    oldCoords L s k (glueOld L s k (oldCoords L s k ω)) = oldCoords L s k ω := by
  funext ⟨i, hi⟩
  cases i <;> simp [oldCoords, glueOld, ringCoord, hi]

/-- Item (i): the fresh collar is independent of the entire old network `(M_κ, C_o)`. -/
theorem indepFun_freshCollar_oldNetwork [NeZero n] (hL : IsCollarLayout n L) (π : Pairing)
    (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (b : ℝ) :
    IndepFun (freshCollar L s k)
      (fun ω : RingCoords n W =>
        (oldInterior L s π S k e z buf κ ω, oldCoupling L s π S k e z buf κ ω))
      (ringCoordLaw n W b) := by
  set G := fun ω : RingCoords n W =>
    (oldInterior L s π S k e z buf κ ω, oldCoupling L s π S k e z buf κ ω)
  have hG : Measurable G := by
    have hf := measurable_stageFull (W := W) (L := L) (s := s) π S e z buf κ
    refine Measurable.prodMk ?_ ?_
    · exact Measurable.of_eval_matrix _ fun x y => hf.eval_matrix
    · exact Measurable.of_eval_matrix _ fun x y => hf.eval_matrix
  have heq : G = (G ∘ glueOld L s k) ∘ oldCoords L s k := by
    funext ω
    have h := oldNetwork_congr (s := s) hL π S k e z buf κ (oldCoords_glueOld k ω)
    simp only [Function.comp_apply, G, h.1, h.2]
  rw [heq]
  exact (indepFun_freshCollar_oldCoords k b).comp measurable_id (hG.comp (measurable_glueOld k))

end Law

end BlockBand.Endpoints
