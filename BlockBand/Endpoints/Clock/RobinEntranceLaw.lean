module

public import BlockBand.Endpoints.Clock.RobinEntrancePath
public import BlockBand.Endpoints.Clock.ClockMixingStep
public import BlockBand.Endpoints.Clock.OpenClockProbe
public import BlockBand.Layers.ScalarRecursion

/-!
# The Robin entrance lemma: the law of the closed-port clock

The initial bond is independent of the remaining layers, which are those of the one-ended path.
Hence the law of the closed-port clock is a mixture over the initial bond of one-ended clock laws.

## Results

* `mp_robinSplit`: under `growthPathLaw W b`, `ω ↦ (B₀, (A_k, B_{k+1})_{k<n})` is measure
  preserving onto `Gin(b/W) ⊗ oneEndedLaw W b n` (the far bond is independent of the one-ended
  layers, which are i.i.d. `freshLaw`).
* `ae_robinGood`: for every fixed `X₀`, all top blocks `A_j - E - X_j` of the one-ended chain
  are a.s. invertible (`b < 1/2`; `srec_ae_isUnit_top` layer by layer, Fubini).
* `isUnit_fullPathMatrix`, `ae_closedClock_eq`: a.s. the hypotheses of the deterministic
  `closedClock_eq_oneEnded` hold, hence a.s. (for all probes `g`) the closed-port clock equals
  the one-ended clock started at `X₀ = λ⁻¹B₀B₀*`.
* `openProbeLawFrom W b E D j`: the law of `g*Q_j^1 g` under `oneEndedLaw ⊗ CN(0, I_W)` for the
  chain started at a deterministic `X₀ = D` (`openProbeLaw … 1 j` is the case `D = 0`).
* `closedClockLaw_eq`, `integral_closedClockLaw`: for `0 < b < 1/2`, `|E| < 2`, `n ≥ 1`, real
  `λ ≠ 0` with `e^{iθ}(z̄ - λ) = z - λ`: `closedClockLaw W b E n θ` is the `Gin(b/W)`-mixture
  over `B₀` of `openProbeLawFrom W b E (λ⁻¹B₀B₀*) n`; for bounded continuous `f`,
  `E f(closed) = ∫ E f(one-ended from X₀(B₀)) dGin(B₀)`, with an integrable inner integral.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.CoareaPalm
  BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator BoundedContinuousFunction

namespace RobinEntrance

variable {W : ℕ}

/-!
## 1. Joint measurability of the chain in `(X₀, layers)`
-/

/-- `(X₀, ℓ) ↦ X_j` is measurable. -/
theorem meas_X_joint (E : ℝ) (j : ℕ) :
    Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × (Fin j → OneEndedLayer W) =>
      oneEndedX E p.1 j p.2) := by
  induction j with
  | zero => exact measurable_fst
  | succ j ih =>
    have hp : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × (Fin (j + 1) → OneEndedLayer W) =>
        (oneEndedX E p.1 j (Fin.init p.2), p.2 (Fin.last j))) :=
      (ih.comp (measurable_fst.prodMk ((ClockMixingProb.meas_init j).comp measurable_snd))).prodMk
        ((ClockMixingProb.meas_last j).comp measurable_snd)
    have h : (fun p : Matrix (Fin W) (Fin W) ℂ × (Fin (j + 1) → OneEndedLayer W) =>
        oneEndedX E p.1 (j + 1) p.2) = fun p =>
          freshSchur E (oneEndedX E p.1 j (Fin.init p.2)) (p.2 (Fin.last j)) := rfl
    rw [h]
    have h2 := (ClockMixingProb.meas_freshSchur (W := W) E).comp hp
    simpa only [Function.comp_def] using h2

/-- `(X₀, ℓ) ↦ Y_j` (weight `1`) is measurable. -/
theorem meas_Y_joint (b E : ℝ) (j : ℕ) :
    Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × (Fin j → OneEndedLayer W) =>
      oneEndedY b E (fun _ => 1) p.1 j p.2) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hp : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × (Fin (j + 1) → OneEndedLayer W) =>
        (oneEndedX E p.1 j (Fin.init p.2), p.2 (Fin.last j))) :=
      ((meas_X_joint E j).comp (measurable_fst.prodMk
        ((ClockMixingProb.meas_init j).comp measurable_snd))).prodMk
        ((ClockMixingProb.meas_last j).comp measurable_snd)
    have hL := (ClockMixingProb.meas_freshL (W := W) b E).comp hp
    have hYi : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × (Fin (j + 1) → OneEndedLayer W) =>
        oneEndedY b E (fun _ => 1) p.1 j (Fin.init p.2)) :=
      ih.comp (measurable_fst.prodMk ((ClockMixingProb.meas_init j).comp measurable_snd))
    have h : (fun p : Matrix (Fin W) (Fin W) ℂ × (Fin (j + 1) → OneEndedLayer W) =>
        oneEndedY b E (fun _ => 1) p.1 (j + 1) p.2) = fun p =>
          (((1 : ℝ) : ℂ)) • freshC b E (oneEndedX E p.1 j (Fin.init p.2)) (p.2 (Fin.last j)) +
            (freshL b E (oneEndedX E p.1 j (Fin.init p.2)) (p.2 (Fin.last j)))ᴴ *
              oneEndedY b E (fun _ => 1) p.1 j (Fin.init p.2) *
              freshL b E (oneEndedX E p.1 j (Fin.init p.2)) (p.2 (Fin.last j)) := rfl
    rw [h]
    exact (ClockMixingProb.meas_smul _ ((ClockMixingProb.meas_freshC (W := W) b E).comp hp)).add
      (ClockMixingProb.meas_mul (ClockMixingProb.meas_mul
        (ClockMixingProb.meas_conjTranspose hL) hYi) hL)

theorem continuous_robinInitial (lam : ℝ) :
    Continuous (fun B : Matrix (Fin W) (Fin W) ℂ => robinInitial lam B) := by
  unfold robinInitial
  exact (continuous_const (y := (((lam⁻¹ : ℝ) : ℂ)))).smul
    ((continuous_id (X := Matrix (Fin W) (Fin W) ℂ)).matrix_mul
      (continuous_id (X := Matrix (Fin W) (Fin W) ℂ)).matrix_conjTranspose)

/-- The closed clock as a function of `((B₀, layers), g)`. -/
def robinClockFn (b E lam : ℝ) (n : ℕ)
    (x : (Matrix (Fin W) (Fin W) ℂ × (Fin n → OneEndedLayer W)) × (Fin W → ℂ)) : ℝ :=
  quadForm (oneEndedQ b E (fun _ => 1) (robinInitial lam x.1.1) n x.1.2) x.2

theorem measurable_robinClockFn (b E lam : ℝ) (n : ℕ) :
    Measurable (robinClockFn (W := W) b E lam n) := by
  refine OpenClock.measurable_quadForm_comp ?_ measurable_snd
  refine ClockMixingProb.meas_smul _ ?_
  exact (meas_Y_joint b E n).comp
    ((((continuous_robinInitial lam).measurable).comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst))

/-!
## 2. The far bond and the one-ended layers
-/

/-- A finite injective reindexing of an iid infinite product is the finite iid product
(as `LeadFieldLaw.infinitePi_map_reindex`). -/
theorem infinitePi_map_reindex' {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {κ ι : Type*} [Fintype ι] (e : ι → κ) (he : Function.Injective e) :
    MeasurePreserving (fun (ω : κ → X) (i : ι) => ω (e i))
      (Measure.infinitePi fun _ : κ => μ) (Measure.pi fun _ : ι => μ) := by
  classical
  have hm : Measurable fun (ω : κ → X) (i : ι) => ω (e i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
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

/-- `ω ↦ (B₀, (A_k, B_{k+1})_{k<n})`. -/
def robinSplit (n : ℕ) (ω : GrowthPath W) :
    Matrix (Fin W) (Fin W) ℂ × (Fin n → OneEndedLayer W) :=
  (ω.2 0, robinLayers ω n)

/-- **Law of the far bond and the one-ended layers.** Under `growthPathLaw W b`, the far bond
`B₀` and the layers `(A_k, B_{k+1})_{k<n}` are independent, `B₀ ~ Gin(b/W)` and the layers are
`oneEndedLaw W b n`. -/
theorem mp_robinSplit (W : ℕ) (b : ℝ) (n : ℕ) :
    MeasurePreserving (robinSplit (W := W) n) (growthPathLaw W b)
      ((ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))).prod (oneEndedLaw W b n)) := by
  have := fun t => BlockBand.Layers.isProbabilityMeasure_gueMeasure W t
  set μA := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) with hμA
  set μB := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) with hμB
  have hA : MeasurePreserving (fun (a : ℕ → Matrix (Fin W) (Fin W) ℂ) (i : Fin n) => a i.val)
      (Measure.infinitePi fun _ : ℕ => μA) (Measure.pi fun _ : Fin n => μA) :=
    infinitePi_map_reindex' μA _ Fin.val_injective
  have hA1 : MeasurePreserving (fun (v : Fin n → Matrix (Fin W) (Fin W) ℂ) (i : Fin n) =>
      (MeasurableEquiv.funUnique (Fin 1) (Matrix (Fin W) (Fin W) ℂ)).symm (v i))
      (Measure.pi fun _ : Fin n => μA)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin 1 => μA) :=
    measurePreserving_pi _ _ fun _ => (measurePreserving_funUnique μA (Fin 1)).symm
  have hB : MeasurePreserving (fun (a : ℕ → Matrix (Fin W) (Fin W) ℂ) (i : Fin (n + 1)) =>
      a i.val) (Measure.infinitePi fun _ : ℕ => μB) (Measure.pi fun _ : Fin (n + 1) => μB) :=
    infinitePi_map_reindex' μB _ Fin.val_injective
  have hB2 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μB) 0
  have hB1 : MeasurePreserving (fun (v : Fin n → Matrix (Fin W) (Fin W) ℂ) (i : Fin n) =>
      (MeasurableEquiv.funUnique (Fin 1) (Fin 1 → Matrix (Fin W) (Fin W) ℂ)).symm
        ((MeasurableEquiv.funUnique (Fin 1) (Matrix (Fin W) (Fin W) ℂ)).symm (v i)))
      (Measure.pi fun _ : Fin n => μB)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 => μB) :=
    measurePreserving_pi _ _ fun _ =>
      (measurePreserving_funUnique (Measure.pi fun _ : Fin 1 => μB) (Fin 1)).symm.comp
        (measurePreserving_funUnique μB (Fin 1)).symm
  have hB3 := (MeasurePreserving.id μB).prod hB1
  have h1 := hA1.comp hA
  have h2 := (hB3.comp hB2).comp hB
  have h12 := h1.prod h2
  -- rearrangement `(x, (y, z)) ↦ (y, (x, z))`, then `(x, z) ↦ fun i => (x i, z i)`
  set PA := Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin 1 => μA
  set PB := Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 => μB
  have hr1 : MeasurePreserving (MeasurableEquiv.prodAssoc).symm (PA.prod (μB.prod PB))
      ((PA.prod μB).prod PB) :=
    (⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩ :
      MeasurePreserving MeasurableEquiv.prodAssoc ((PA.prod μB).prod PB) _).symm
  have hr2 : MeasurePreserving (Prod.map Prod.swap id) ((PA.prod μB).prod PB)
      ((μB.prod PA).prod PB) :=
    (Measure.measurePreserving_swap).prod (MeasurePreserving.id PB)
  have hr3 : MeasurePreserving MeasurableEquiv.prodAssoc ((μB.prod PA).prod PB)
      (μB.prod (PA.prod PB)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have hr4 := (MeasurePreserving.id μB).prod
    (measurePreserving_arrowProdEquivProdArrow _ _ (Fin n)
      (fun _ => Measure.pi fun _ : Fin 1 => μA)
      (fun _ => Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 => μB)).symm
  have hall := (((hr4.comp hr3).comp hr2).comp hr1).comp h12
  convert hall using 1
  · funext ω
    refine Prod.ext ?_ ?_
    · simp [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodAssoc, robinSplit]
    · funext i
      refine Prod.ext ?_ ?_ <;> funext k
      · simp [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodAssoc, robinSplit, robinLayers,
          robinLayer, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
      · funext k'
        simp [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodAssoc, robinSplit, robinLayers,
          robinLayer, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
          Fin.tail]
  · rfl
  · rfl

/-!
## 3. Invertible top blocks along the chain
-/

/-- All top blocks `A_j - E - X_j` of the first `j` layers are invertible. -/
def robinGood (E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) :
    (j : ℕ) → (Fin j → OneEndedLayer W) → Prop
  | 0, _ => True
  | j + 1, ℓ => robinGood E D j (Fin.init ℓ) ∧
      IsUnit ((ℓ (Fin.last j)).1 0 - (E : ℂ) • 1 - oneEndedX E D j (Fin.init ℓ)).det

theorem robinGood_iff (E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) :
    ∀ n, robinGood E D n (robinLayers ω n) ↔
      ∀ j < n, IsUnit (ω.1 j - (E : ℂ) • 1 - robinX E D ω j).det
  | 0 => by simp [robinGood]
  | n + 1 => by
    have ih := robinGood_iff E D ω n
    change (robinGood E D n (robinLayers ω n) ∧
      IsUnit (ω.1 n - (E : ℂ) • 1 - robinX E D ω n).det) ↔ _
    rw [ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
      · exact h1 j h
      · exact h2
    · intro h
      exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

theorem measurableSet_robinGood (E : ℝ) :
    ∀ j, MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × (Fin j → OneEndedLayer W) |
      robinGood E p.1 j p.2}
  | 0 => by simp [robinGood]
  | j + 1 => by
    have ih := measurableSet_robinGood E j
    have hp : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × (Fin (j + 1) → OneEndedLayer W) =>
        (p.1, Fin.init p.2)) :=
      measurable_fst.prodMk ((ClockMixingProb.meas_init j).comp measurable_snd)
    have hX : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × (Fin (j + 1) → OneEndedLayer W) =>
        (p.2 (Fin.last j)).1 0 - (E : ℂ) • 1 - oneEndedX E p.1 j (Fin.init p.2)) := by
      have hA : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × (Fin (j + 1) → OneEndedLayer W) =>
          (p.2 (Fin.last j)).1 0) :=
        (measurable_pi_apply 0).comp (measurable_fst.comp
          ((ClockMixingProb.meas_last j).comp measurable_snd))
      exact (hA.sub measurable_const).sub ((meas_X_joint E j).comp hp)
    have h2 : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × (Fin (j + 1) → OneEndedLayer W) |
        IsUnit ((p.2 (Fin.last j)).1 0 - (E : ℂ) • 1 - oneEndedX E p.1 j (Fin.init p.2)).det} := by
      simp only [isUnit_iff_ne_zero]
      exact (measurableSet_eq_fun ((continuous_id.matrix_det).measurable.comp hX)
        measurable_const).compl
    exact (hp ih).inter h2

/-- `blockDiag A - E - X̃` on `Fin 1 × Fin W` is `A₀ - E - X` read through
`Fin 1 × Fin W ≃ Fin W`. -/
theorem topBlock_eq_submatrix (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    Internal.Contracts.Layers.blockDiag ω.1 -
        (E : ℂ) • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) -
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) =
      (ω.1 0 - (E : ℂ) • 1 - X).submatrix (Equiv.uniqueProd (Fin W) (Fin 1))
        (Equiv.uniqueProd (Fin W) (Fin 1)) := by
  ext ⟨i, x⟩ ⟨k, y⟩; fin_cases i; fin_cases k
  simp [Internal.Contracts.Layers.blockDiag, Matrix.one_apply]

/-- For every fixed `X`, the top block of a fresh layer is a.s. invertible (`b < 1/2`). -/
theorem ae_isUnit_top {b : ℝ} (hb : b < 1 / 2) (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    ∀ᵐ ω ∂freshLaw W b, IsUnit (ω.1 0 - (E : ℂ) • 1 - X).det := by
  filter_upwards [BlockBand.Layers.srec_ae_isUnit_top hb .oneBlockOnePort E
    (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2)] with ω hω
  rwa [topBlock_eq_submatrix, det_submatrix_equiv_self] at hω

theorem ae_robinGood {b : ℝ} (hb : b < 1 / 2) (E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) :
    ∀ j, ∀ᵐ ℓ ∂oneEndedLaw W b j, robinGood E D j ℓ
  | 0 => Filter.Eventually.of_forall fun _ => trivial
  | j + 1 => by
    have ih := ae_robinGood hb E D j
    have hmp := ClockMixingProb.measurePreserving_initLast (freshLaw W b) j
    set S : Set ((Fin j → OneEndedLayer W) × OneEndedLayer W) :=
      {p | robinGood E D j p.1 ∧ IsUnit (p.2.1 0 - (E : ℂ) • 1 - oneEndedX E D j p.1).det}
    have hSm : MeasurableSet S := by
      have h1 : MeasurableSet {p : (Fin j → OneEndedLayer W) × OneEndedLayer W |
          robinGood E D j p.1} :=
        (measurableSet_robinGood E j).preimage (measurable_const.prodMk measurable_fst)
      have hX : Measurable (fun p : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
          p.2.1 0 - (E : ℂ) • 1 - oneEndedX E D j p.1) :=
        (((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)).sub
          measurable_const).sub ((ClockMixingProb.meas_X E D j).comp measurable_fst)
      have h2 : MeasurableSet {p : (Fin j → OneEndedLayer W) × OneEndedLayer W |
          IsUnit (p.2.1 0 - (E : ℂ) • 1 - oneEndedX E D j p.1).det} := by
        simp only [isUnit_iff_ne_zero]
        exact (measurableSet_eq_fun ((continuous_id.matrix_det).measurable.comp hX)
          measurable_const).compl
      exact h1.inter h2
    have hS : ∀ᵐ p ∂(oneEndedLaw W b j).prod (freshLaw W b), p ∈ S := by
      refine (Measure.ae_prod_iff_ae_ae (p := fun p => p ∈ S) hSm).mpr ?_
      filter_upwards [ih] with r hr
      filter_upwards [ae_isUnit_top hb E (oneEndedX E D j r)] with x hx
      exact ⟨hr, hx⟩
    exact hmp.quasiMeasurePreserving.ae hS

/-!
## 4. The finite path: almost-sure hypotheses and the law of the closed clock
-/

/-- `𝓜` is invertible when the blocks are Hermitian and the bonds invertible (as in
`negativeClock_scattering_of_bonds`). -/
theorem isUnit_fullPathMatrix {b E : ℝ} {n : ℕ} (hn : 0 < n) (hη : 0 < etaZ b E)
    (ω : GrowthPath W) (hH : ∀ k, (ω.1 k).IsHermitian) (hB : ∀ k, IsUnit (ω.2 k).det) :
    IsUnit (fullPathMatrix b E W n ω).det := by
  set P := pathAt W n ω with hP
  set z := boundaryZ b E with hz
  have hzim : 0 < z.im := hη
  have hPH : (pathMatrix P).IsHermitian :=
    NegativeClockScattering.pathMatrix_isHermitian P fun i => hH _
  have hint : ∀ i, IsUnit (P.2.1 i).det := fun i => by
    simp only [hP, pathAt]; rw [det_conjTranspose]; exact (hB _).star
  have hport : ∀ q, IsUnit (P.2.2 q).det := fun q => by
    fin_cases q <;> simp only [hP, pathAt] <;> simp <;> exact (hB _).ne_zero
  have hM : fullPathMatrix b E W n ω = NegativeClockScattering.fullM E z P := rfl
  rw [hM]
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  obtain ⟨ψ, hψ0, hψ⟩ := exists_mulVec_eq_zero_iff.mpr h0
  have hpz := NegativeClockScattering.ports_zero E z hzim P hPH ψ hψ
  obtain ⟨h1, -⟩ := NegativeClockScattering.propagate E z P hn hint hport ψ 0 hψ
    (fun _ => rfl) (fun _ => rfl) (fun c => hpz _)
  apply hψ0
  funext x
  rcases x with x | q
  · exact h1 x
  · exact hpz q

/-- **Almost-sure closed-port reduction.** For `0 < b < 1/2`, `|E| < 2`, `n ≥ 1`, a real
`λ ≠ 0` with `e^{iθ}(z̄ - λ) = z - λ`: `growthPathLaw`-a.s., for every probe `g`, the closed
clock equals the one-ended clock of `robinSplit n ω` started at `X₀ = λ⁻¹B₀B₀*`. -/
theorem ae_closedClock_eq {b E lam θ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E)
    (hE1 : E < 2) {n : ℕ} (hn : 0 < n) (hlam : lam ≠ 0)
    (hcl : phase θ * (star (boundaryZ b E) - lam) = boundaryZ b E - lam) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ g : Fin W → ℂ, closedClock b E W n θ (ω, g) =
      quadForm (oneEndedQ b E (fun _ => 1) (robinInitial lam (ω.2 0)) n (robinLayers ω n)) g := by
  have hη := negativeClock_etaZ_pos (b := b) (by linarith) hE0 hE1
  have htop : ∀ᵐ ω ∂growthPathLaw W b, ∀ j < n,
      IsUnit (ω.1 j - (E : ℂ) • 1 - robinX E (robinInitial lam (ω.2 0)) ω j).det := by
    have h : ∀ᵐ p ∂((ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))).prod
        (oneEndedLaw W b n)), robinGood E (robinInitial lam p.1) n p.2 := by
      have hm : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × (Fin n → OneEndedLayer W) |
          robinGood E (robinInitial lam p.1) n p.2} :=
        (measurableSet_robinGood E n).preimage
          (((continuous_robinInitial lam).measurable.comp measurable_fst).prodMk measurable_snd)
      refine (Measure.ae_prod_iff_ae_ae
        (p := fun p => robinGood E (robinInitial lam p.1) n p.2) hm).mpr ?_
      exact Filter.Eventually.of_forall fun B => ae_robinGood (W := W) hb1 E (robinInitial lam B) n
    filter_upwards [(mp_robinSplit W b n).quasiMeasurePreserving.ae h] with ω hω
    exact (robinGood_iff E _ ω n).mp hω
  filter_upwards [NegativeClockScattering.ae_growth_good W hb0,
    negativeClock_ae_scattering hb0 hb1 hE0 hE1 W n hn, htop] with ω hω hS ht g
  have hM := isUnit_fullPathMatrix hn hη ω hω.1 hω.2
  have hR : IsUnit (1 - phase θ • farReflection (scatteringMatrix b E W n ω)).det :=
    (det_one_sub_smul_ne_zero _ _ (transmission_mul_add_farReflection_mul _ hS.1) hS.2
      (norm_phase θ)).isUnit
  exact closedClock_eq_oneEnded g θ hn hη hω.1 ht hlam hM hR hcl

/-- The law of the one-ended total-mass probe `g* Q_j^1 g` started at a deterministic `X₀ = D`
(`openProbeLaw` is the case `D = 0`). -/
def openProbeLawFrom (W : ℕ) (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) : Measure ℝ :=
  ((oneEndedLaw W b j).prod (circularVectorLaw (Fin W))).map
    (fun p => quadForm (oneEndedQ b E (fun _ => 1) D j p.1) p.2)

/-- **The closed-clock law is a `Gin`-mixture of one-ended laws.** -/
theorem closedClockLaw_eq {b E lam θ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E)
    (hE1 : E < 2) {n : ℕ} (hn : 0 < n) (hlam : lam ≠ 0)
    (hcl : phase θ * (star (boundaryZ b E) - lam) = boundaryZ b E - lam) :
    closedClockLaw W b E n θ =
      (((ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))).prod (oneEndedLaw W b n)).prod
        (circularVectorLaw (Fin W))).map (robinClockFn b E lam n) := by
  have h := ae_closedClock_eq (W := W) hb0 hb1 hE0 hE1 hn hlam hcl
  have hae : closedClock b E W n θ =ᵐ[(growthPathLaw W b).prod (circularVectorLaw (Fin W))]
      (robinClockFn b E lam n ∘ Prod.map (robinSplit n) id) := by
    filter_upwards [(measurePreserving_fst (μ := growthPathLaw W b)
      (ν := circularVectorLaw (Fin W))).quasiMeasurePreserving.ae h] with x hx
    exact hx x.2
  have hmp := (mp_robinSplit W b n).prod (MeasurePreserving.id (circularVectorLaw (Fin W)))
  rw [closedClockLaw, Measure.map_congr hae, ← Measure.map_map (measurable_robinClockFn b E lam n)
    hmp.measurable, hmp.map_eq]

/-- **Disintegration over the far bond.** For every bounded continuous `f`,
`E f(closed clock) = ∫ E f(one-ended probe from X₀(B₀)) dGin(B₀)`, and the inner integral is
`Gin`-integrable. -/
theorem integral_closedClockLaw {b E lam θ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E)
    (hE1 : E < 2) {n : ℕ} (hn : 0 < n) (hlam : lam ≠ 0)
    (hcl : phase θ * (star (boundaryZ b E) - lam) = boundaryZ b E - lam) (f : ℝ →ᵇ ℝ) :
    Integrable (fun B => ∫ x, f x ∂openProbeLawFrom W b E (robinInitial lam B) n)
        (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) ∧
      ∫ x, f x ∂closedClockLaw W b E n θ =
        ∫ B, (∫ x, f x ∂openProbeLawFrom W b E (robinInitial lam B) n)
          ∂ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) := by
  set μ := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  set ν := oneEndedLaw W b n
  set ρ := circularVectorLaw (Fin W)
  have hassoc : MeasurePreserving MeasurableEquiv.prodAssoc ((μ.prod ν).prod ρ)
      (μ.prod (ν.prod ρ)) := ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  set G : Matrix (Fin W) (Fin W) ℂ × ((Fin n → OneEndedLayer W) × (Fin W → ℂ)) → ℝ :=
    fun y => f (robinClockFn b E lam n (MeasurableEquiv.prodAssoc.symm y))
  have hGm : Measurable G := f.continuous.measurable.comp
    ((measurable_robinClockFn b E lam n).comp MeasurableEquiv.prodAssoc.symm.measurable)
  have hGi : Integrable G (μ.prod (ν.prod ρ)) :=
    Integrable.of_bound hGm.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall fun y => f.norm_coe_le_norm _)
  have hinner : ∀ B, ∫ y, G (B, y) ∂(ν.prod ρ) =
      ∫ x, f x ∂openProbeLawFrom W b E (robinInitial lam B) n := by
    intro B
    have hm : Measurable (fun p : (Fin n → OneEndedLayer W) × (Fin W → ℂ) =>
        quadForm (oneEndedQ b E (fun _ => 1) (robinInitial lam B) n p.1) p.2) :=
      OpenClock.measurable_quadForm_comp ((ClockMixingProb.meas_Q b E _ _ n).comp measurable_fst)
        measurable_snd
    rw [openProbeLawFrom, integral_map hm.aemeasurable f.continuous.aestronglyMeasurable]
    rfl
  refine ⟨?_, ?_⟩
  · have := hGi.integral_prod_left
    simp_rw [hinner] at this
    exact this
  · rw [closedClockLaw_eq hb0 hb1 hE0 hE1 hn hlam hcl,
      integral_map (measurable_robinClockFn b E lam n).aemeasurable
        f.continuous.aestronglyMeasurable,
      ← hassoc.symm.integral_comp' (fun y => f (robinClockFn b E lam n y)), integral_prod G hGi]
    simp_rw [hinner]

end RobinEntrance

end BlockBand.Endpoints.Clock
