module

public import Mathlib
public import BlockBand.Wegner.ConditionalCount
public import BlockBand.Internal.Contracts.Inputs

/-!
# Independent `GUE_W(c/W)` blocks as a normalized PSSS block-GUE law

Law: a `BlockModel k W` (`W > 0`) satisfying `IsIndependent c` (`c > 0`): the blocks
`A_j` are independent, each with the concrete Johansson coordinate law
`gueMatrixLaw W (c/W)`, and `(D, Y)` is independent of the block family.
After the reindexing `Fin k × Fin W ≃ Σ j : Fin k, Fin W`, the rescaled block sum
`c^{-1/2} ⊕_j A_j` (`noiseMatrix`) is a `BlockGUE.Law` with blocks of size `W`
(`blockLaw`), hence has exactly the canonical PSSS law. The main result
`blockModel_countFactorial` is the factorial-moment count bound for `H = D + ⊕_j A_j`:
for every closed `[a,b]` and order `r ≥ 1`,
`E (N_H[a,b])_r ≤ (C/√c · kW · (b-a))^r`, with `C` the PSSS constant (chosen first,
uniform in `k, W, c, D, a, b`). Only `PSSS.SourceContract` (through
`conditionalBlockGUECount_holds`) is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

namespace SingularLogLaw

open MeasureTheory ProbabilityTheory Set
open BlockBand.External BlockBand.External.PSSS BlockBand.External.PSSS.BlockGUE
open BlockBand.Counting
open BlockBand.Internal.Contracts.Inputs (gueMatrixLaw BlockModel)
open scoped NNReal

local instance gaussianReal_isProbability'' (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal μ v

/-!
## Coordinates of one Johansson block
-/

section Block

variable {W : ℕ}

/-- The real coordinates `(Re B_ab, Im B_ab)` of the upper entries of a matrix. -/
def upperCoords (B : Matrix (Fin W) (Fin W) ℂ) : Johansson.UpperPair W → ℝ × ℝ :=
  fun p => ((B p.1.1 p.1.2).re, (B p.1.1 p.1.2).im)

theorem measurable_entry (a b : Fin W) :
    Measurable (fun B : Matrix (Fin W) (Fin W) ℂ => B a b) :=
  (measurable_pi_apply b).comp (measurable_pi_apply a)

theorem measurable_upperCoords : Measurable (upperCoords (W := W)) := by
  apply measurable_pi_iff.mpr
  intro p
  exact (Complex.measurable_re.comp (measurable_entry p.1.1 p.1.2)).prodMk
    (Complex.measurable_im.comp (measurable_entry p.1.1 p.1.2))

/-- On the Johansson side, the diagonal imaginary coordinate is ignored. -/
def diagFix (p : Johansson.UpperPair W) : ℝ × ℝ → ℝ × ℝ :=
  if p.1.1 = p.1.2 then fun v => (v.1, 0) else id

theorem measurable_diagFix (p : Johansson.UpperPair W) : Measurable (diagFix p) := by
  unfold diagFix
  split_ifs
  · fun_prop
  · exact measurable_id

theorem upperCoords_gaussianMatrixRaw (z : Johansson.UpperPair W → ℝ × ℝ) :
    upperCoords (Johansson.gaussianMatrixRaw z) = fun p => diagFix p (z p) := by
  funext p
  rcases p with ⟨⟨a, b⟩, hab⟩
  by_cases h : a = b
  · subst h
    simp [upperCoords, Johansson.gaussianMatrixRaw, diagFix]
  · simp [upperCoords, Johansson.gaussianMatrixRaw, diagFix, h, hab, Johansson.complexPair]

/-- The law of one upper coordinate pair of a `GUE_W(S)` matrix. -/
def coordLaw (S : ℝ≥0) (p : Johansson.UpperPair W) : Measure (ℝ × ℝ) :=
  (Johansson.upperEntryMeasure S p).map (diagFix p)

instance coordLaw_isProbability (S : ℝ≥0) (p : Johansson.UpperPair W) :
    IsProbabilityMeasure (coordLaw S p) := by
  have := Johansson.upperEntryMeasure_probability S p
  exact (Measure.isProbabilityMeasure_map_iff (measurable_diagFix p).aemeasurable).mpr this

/-- The upper coordinates of a `GUE_W(S)` matrix are independent with laws `coordLaw`. -/
theorem hasLaw_upperCoords (S : ℝ≥0) :
    HasLaw (upperCoords (W := W)) (Measure.pi (coordLaw S)) (gueMatrixLaw W S) := by
  refine ⟨measurable_upperCoords.aemeasurable, ?_⟩
  have hg : Measurable (fun z : Johansson.UpperPair W → ℝ × ℝ =>
      (Johansson.gaussianMatrix z).1) :=
    measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix
  rw [gueMatrixLaw, Measure.map_map measurable_upperCoords hg]
  have he : (upperCoords ∘ fun z : Johansson.UpperPair W → ℝ × ℝ =>
      (Johansson.gaussianMatrix z).1) = fun z p => diagFix p (z p) := by
    funext z
    exact upperCoords_gaussianMatrixRaw z
  rw [he, Johansson.coordinateMeasure]
  have : ∀ p : Johansson.UpperPair W, IsProbabilityMeasure (Johansson.upperEntryMeasure S p) :=
    Johansson.upperEntryMeasure_probability S
  exact Measure.pi_map_pi (fun p => (measurable_diagFix p).aemeasurable)

/-- One upper coordinate pair has law `coordLaw`. -/
theorem hasLaw_upperCoords_eval (S : ℝ≥0) (p : Johansson.UpperPair W) :
    HasLaw (fun B : Matrix (Fin W) (Fin W) ℂ => upperCoords B p) (coordLaw S p)
      (gueMatrixLaw W S) :=
  (measurePreserving_eval (coordLaw S) p).hasLaw.fun_comp (hasLaw_upperCoords S)

theorem coordLaw_diag (S : ℝ≥0) (a : Fin W) :
    coordLaw S ⟨(a, a), le_rfl⟩ = (gaussianReal 0 S).map (fun x : ℝ => (x, (0 : ℝ))) := by
  rw [coordLaw, Johansson.upperEntryMeasure]
  simp only [↓reduceIte, diagFix]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem coordLaw_offdiag (S : ℝ≥0) (a b : Fin W) (hab : a ≤ b) (hne : a ≠ b) :
    coordLaw S ⟨(a, b), hab⟩ = (gaussianReal 0 (S / 2)).prod (gaussianReal 0 (S / 2)) := by
  rw [coordLaw, Johansson.upperEntryMeasure]
  simp only [hne, ↓reduceIte, diagFix, Measure.map_id]

end Block

/-!
## Generic law lemmas
-/

section Generic

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- Rescaling a centered real Gaussian. -/
theorem hasLaw_gaussian_scale {X : Ω → ℝ} {v w : ℝ≥0} (h : HasLaw X (gaussianReal 0 v) P)
    (s : ℝ) (hw : (w : ℝ) = s ^ 2 * v) :
    HasLaw (fun ω => s * X ω) (gaussianReal 0 w) P := by
  have h0 := gaussianReal_const_mul h s
  rw [mul_zero] at h0
  have he : NNReal.mk (s ^ 2) (sq_nonneg s) * v = w := NNReal.eq (by simp [hw])
  rwa [he] at h0

/-- Rescaling both components of a pair with i.i.d. centered Gaussian law. -/
theorem hasLaw_gaussian_pair_scale {X Y : Ω → ℝ} {v w : ℝ≥0}
    (h : HasLaw (fun ω => (X ω, Y ω)) ((gaussianReal 0 v).prod (gaussianReal 0 v)) P)
    (s : ℝ) (hw : (w : ℝ) = s ^ 2 * v) :
    HasLaw (fun ω => (s * X ω, s * Y ω)) ((gaussianReal 0 w).prod (gaussianReal 0 w)) P := by
  have hg : (gaussianReal 0 v).map (fun x => s * x) = gaussianReal 0 w := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    exact NNReal.eq (by simp [hw])
  have hm : HasLaw (Prod.map (fun x : ℝ => s * x) (fun x : ℝ => s * x))
      ((gaussianReal 0 w).prod (gaussianReal 0 w))
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), hg]
  exact hm.fun_comp h

/-- Conjugating the second component of an i.i.d. centered Gaussian pair. -/
theorem hasLaw_gaussian_pair_neg {X Y : Ω → ℝ} {v : ℝ≥0}
    (h : HasLaw (fun ω => (X ω, Y ω)) ((gaussianReal 0 v).prod (gaussianReal 0 v)) P) :
    HasLaw (fun ω => (X ω, -Y ω)) ((gaussianReal 0 v).prod (gaussianReal 0 v)) P := by
  have hg : (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  have hm : HasLaw (Prod.map (fun x : ℝ => x) (fun x : ℝ => -x))
      ((gaussianReal 0 v).prod (gaussianReal 0 v))
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), hg, Measure.map_id']
  exact hm.fun_comp h

/-- The first component of a variable with law `μ.map (x ↦ (x, 0))`. -/
theorem hasLaw_fst_of_map_zero {X : Ω → ℝ × ℝ} {μ : Measure ℝ}
    (h : HasLaw X (μ.map (fun x : ℝ => (x, (0 : ℝ)))) P) : HasLaw (fun ω => (X ω).1) μ P := by
  have h1 := (hasLaw_map (P := μ.map (fun x : ℝ => (x, (0 : ℝ))))
    measurable_fst.aemeasurable).fun_comp h
  have hid : (Prod.fst ∘ fun x : ℝ => (x, (0 : ℝ))) = id := rfl
  rwa [Measure.map_map measurable_fst (by fun_prop), hid, Measure.map_id] at h1

/-- Marginals and independence of an i.i.d. centered Gaussian pair. -/
theorem hasLaw_of_gaussian_pair [IsFiniteMeasure P] {X Y : Ω → ℝ} {v : ℝ≥0}
    (h : HasLaw (fun ω => (X ω, Y ω)) ((gaussianReal 0 v).prod (gaussianReal 0 v)) P) :
    HasLaw X (gaussianReal 0 v) P ∧ HasLaw Y (gaussianReal 0 v) P ∧ IndepFun X Y P := by
  have hX : HasLaw X (gaussianReal 0 v) P := by
    have h1 := (hasLaw_map (P := (gaussianReal 0 v).prod (gaussianReal 0 v))
      measurable_fst.aemeasurable).fun_comp h
    rwa [Measure.map_fst_prod, measure_univ, one_smul] at h1
  have hY : HasLaw Y (gaussianReal 0 v) P := by
    have h1 := (hasLaw_map (P := (gaussianReal 0 v).prod (gaussianReal 0 v))
      measurable_snd.aemeasurable).fun_comp h
    rwa [Measure.map_snd_prod, measure_univ, one_smul] at h1
  exact ⟨hX, hY, (indepFun_iff_hasLaw_prodMk_prod hX hY).mpr h⟩

/-- Currying a doubly indexed product measure. -/
theorem map_uncurry_pi_pi {ι κ X : Type} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (ν : ι → κ → Measure X) [∀ i j, IsProbabilityMeasure (ν i j)] :
    (Measure.pi fun i => Measure.pi (ν i)).map (fun f (σ : Σ _ : ι, κ) => f σ.1 σ.2) =
      Measure.pi fun σ : (Σ _ : ι, κ) => ν σ.1 σ.2 := by
  have hm : Measurable (fun (f : ι → κ → X) (σ : Σ _ : ι, κ) => f σ.1 σ.2) :=
    measurable_pi_iff.mpr fun σ => (measurable_pi_apply σ.2).comp (measurable_pi_apply σ.1)
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (f : ι → κ → X) (σ : Σ _ : ι, κ) => f σ.1 σ.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun j => s ⟨i, j⟩ := by
    ext f
    simp [Set.mem_pi, Sigma.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_sigma]

/-- A joint product law gives independence. -/
theorem iIndepFun_of_hasLaw_pi {ι X : Type} [Fintype ι] [MeasurableSpace X]
    [IsProbabilityMeasure P] {Y : ι → Ω → X} {ν : ι → Measure X}
    [∀ i, IsProbabilityMeasure (ν i)] (hY : ∀ i, Measurable (Y i))
    (h : HasLaw (fun ω i => Y i ω) (Measure.pi ν) P) : iIndepFun Y P := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY i).aemeasurable)]
  have hm : ∀ i, P.map (Y i) = ν i := fun i =>
    ((measurePreserving_eval ν i).hasLaw.fun_comp h).map_eq
  rw [h.map_eq]
  simp_rw [hm]

/-- Adding deterministic constant members to an independent family keeps it independent. -/
theorem iIndepFun_of_const_off {ι β : Type} [MeasurableSpace β] [IsProbabilityMeasure P]
    {f : ι → Ω → β} (p : ι → Prop) (hc : ∀ i, ¬ p i → ∃ b, ∀ ω, f i ω = b)
    (h : iIndepFun (fun i : Subtype p => f i) P) : iIndepFun f P := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  by_cases hbad : ∃ i ∈ S, ¬ p i ∧ f i ⁻¹' sets i = ∅
  · obtain ⟨i, hi, -, he⟩ := hbad
    have h1 : (⋂ i ∈ S, f i ⁻¹' sets i) = ∅ :=
      Set.subset_empty_iff.mp ((Set.biInter_subset_of_mem hi).trans he.le)
    rw [h1, measure_empty]
    symm
    exact Finset.prod_eq_zero hi (by rw [he, measure_empty])
  · simp only [not_exists, not_and] at hbad
    have huniv : ∀ i ∈ S, ¬ p i → f i ⁻¹' sets i = Set.univ := by
      intro i hi hp
      obtain ⟨b, hb⟩ := hc i hp
      have hbm : b ∈ sets i := by
        by_contra hn
        exact hbad i hi hp (by ext ω; simp [hb, hn])
      ext ω
      simp [hb, hbm]
    have key := h (S.subtype p) (sets := fun i => sets i)
      (fun i hi => hsets i (Finset.mem_subtype.mp hi))
    have hinter : (⋂ i ∈ S, f i ⁻¹' sets i) = ⋂ i ∈ S.subtype p, f i ⁻¹' sets i := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Finset.mem_subtype]
      constructor
      · intro hω i hi
        exact hω i hi
      · intro hω i hi
        by_cases hp : p i
        · exact hω ⟨i, hp⟩ hi
        · have hu := huniv i hi hp
          rw [Set.eq_univ_iff_forall] at hu
          exact hu ω
    have hprod : ∏ i ∈ S, P (f i ⁻¹' sets i) = ∏ i ∈ S.subtype p, P (f i ⁻¹' sets i) := by
      rw [← Finset.prod_filter_mul_prod_filter_not S p]
      rw [Finset.prod_eq_one (s := S.filter (fun i => ¬ p i)) (fun i hi => by
        rw [Finset.mem_filter] at hi
        rw [huniv i hi.1 hi.2, measure_univ]), mul_one]
      exact (Finset.prod_subtype_eq_prod_filter (fun i => P (f i ⁻¹' sets i))).symm
    rw [hinter, hprod]
    exact key

end Generic

/-!
## The rescaled block sum on the PSSS block index
-/

section Noise

variable {k W : ℕ}

/-- `k` blocks of size `W`. -/
abbrev sizes (k W : ℕ) : Fin k → ℕ := fun _ => W

/-- The rescaled block sum `s · ⊕_j B_j` on the PSSS block index `Σ j : Fin k, Fin W`. -/
def noiseMatrix (s : ℝ) (B : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Index (sizes k W)) (Index (sizes k W)) ℂ :=
  fun x y => if x.1 = y.1 then (s : ℂ) * B x.1 x.2 y.2 else 0

theorem noiseMatrix_same (s : ℝ) (B : Fin k → Matrix (Fin W) (Fin W) ℂ) (j : Fin k)
    (a b : Fin W) :
    noiseMatrix s B ⟨j, a⟩ ⟨j, b⟩ = (s : ℂ) * B j a b := by
  simp [noiseMatrix]

theorem noiseMatrix_isHermitian (s : ℝ) (B : Fin k → Matrix (Fin W) (Fin W) ℂ)
    (hB : ∀ j, (B j).IsHermitian) : (noiseMatrix s B).IsHermitian := by
  ext x y
  rcases x with ⟨j, a⟩
  rcases y with ⟨j', b⟩
  simp only [Matrix.conjTranspose_apply, noiseMatrix]
  by_cases h : j = j'
  · subst h
    simp only [↓reduceIte, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [← (hB j).apply a b]
    rfl
  · simp [h, Ne.symm h]

theorem measurable_noiseMatrix (s : ℝ) :
    Measurable (noiseMatrix (k := k) (W := W) s) := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  unfold noiseMatrix
  split_ifs
  · exact measurable_const.mul ((measurable_entry _ _).comp (measurable_pi_apply _))
  · exact measurable_const

/-- The Johansson coordinate carrying a within-block PSSS upper pair. -/
def blockPair (q : UpperPair (sizes k W)) : Σ _ : Fin k, Johansson.UpperPair W :=
  ⟨q.1.1.1, if h : q.1.1.2 ≤ q.1.2.2 then ⟨(q.1.1.2, q.1.2.2), h⟩
    else ⟨(q.1.2.2, q.1.1.2), le_of_not_ge h⟩⟩

theorem indexLE_antisymm'' (d : Fin k → ℕ) (x y : Index d)
    (h1 : indexLE d x y) (h2 : indexLE d y x) : x = y :=
  (Fintype.equivFin (Index d)).injective (Fin.ext (Nat.le_antisymm h1 h2))

theorem blockPair_injective :
    Function.Injective (fun q : {q : UpperPair (sizes k W) // q.1.1.1 = q.1.2.1} =>
      blockPair q.1) := by
  rintro ⟨⟨⟨⟨j, a⟩, ⟨j2, b⟩⟩, hq⟩, hb⟩ ⟨⟨⟨⟨j', a'⟩, ⟨j2', b'⟩⟩, hq'⟩, hb'⟩ he
  simp only at hb hb'
  subst hb hb'
  simp only [blockPair, Sigma.mk.injEq] at he
  obtain ⟨hj, he⟩ := he
  subst hj
  have he' := eq_of_heq he
  by_cases h : a ≤ b <;> by_cases h' : a' ≤ b' <;> simp only [h, h', ↓reduceDIte,
    Subtype.mk.injEq, Prod.mk.injEq] at he'
  · obtain ⟨e1, e2⟩ := he'
    subst e1 e2
    rfl
  · obtain ⟨e1, e2⟩ := he'
    subst e1 e2
    have := indexLE_antisymm'' (sizes k W) _ _ hq hq'
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact absurd (this ▸ le_rfl) h'
  · obtain ⟨e1, e2⟩ := he'
    subst e1 e2
    have := indexLE_antisymm'' (sizes k W) _ _ hq hq'
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact absurd (this ▸ le_rfl) h
  · obtain ⟨e1, e2⟩ := he'
    subst e1 e2
    rfl

/-- The scaled complex entry recovered from the Johansson coordinate of `blockPair`. -/
def pairEntry (s : ℝ) (q : UpperPair (sizes k W)) : ℝ × ℝ → ℂ :=
  fun v => if q.1.1.2 ≤ q.1.2.2 then (s : ℂ) * ((v.1 : ℂ) + (v.2 : ℂ) * Complex.I)
    else (s : ℂ) * star ((v.1 : ℂ) + (v.2 : ℂ) * Complex.I)

theorem measurable_pairEntry (s : ℝ) (q : UpperPair (sizes k W)) :
    Measurable (pairEntry s q) := by
  unfold pairEntry
  split_ifs
  · fun_prop
  · exact measurable_const.mul (continuous_star.measurable.comp (by fun_prop))

theorem noiseMatrix_upper (s : ℝ) (B : Fin k → Matrix (Fin W) (Fin W) ℂ)
    (hB : ∀ j, (B j).IsHermitian) (q : UpperPair (sizes k W)) (hq : q.1.1.1 = q.1.2.1) :
    noiseMatrix s B q.1.1 q.1.2 =
      pairEntry s q (upperCoords (B (blockPair q).1) (blockPair q).2) := by
  rcases q with ⟨⟨⟨j, a⟩, ⟨j2, b⟩⟩, hq'⟩
  simp only at hq
  subst hq
  by_cases h : a ≤ b
  · simp [noiseMatrix, pairEntry, blockPair, upperCoords, h, Complex.re_add_im]
  · simp only [noiseMatrix, pairEntry, blockPair, upperCoords, h, ↓reduceIte, ↓reduceDIte,
      Complex.re_add_im]
    rw [← (hB j).apply a b]

end Noise

/-!
## The block law of an independent block model
-/

section Model

variable {k W : ℕ} (M : BlockModel k W) (c : ℝ)

/-- The Johansson coordinates of all blocks, indexed by `(block, upper pair)`. -/
def blockCoords (σ : Σ _ : Fin k, Johansson.UpperPair W) (w : M.Ω) : ℝ × ℝ :=
  upperCoords (M.A w σ.1) σ.2

theorem measurable_blockCoords (σ : Σ _ : Fin k, Johansson.UpperPair W) :
    Measurable (blockCoords M σ) :=
  ((measurable_pi_apply σ.2).comp measurable_upperCoords).comp
    ((measurable_pi_apply σ.1).comp M.measurable_A)

variable {M c}

/-- One block coordinate pair under `IsIndependent c`. -/
theorem hasLaw_blockCoord (h : M.IsIndependent c) (j : Fin k) (p : Johansson.UpperPair W) :
    HasLaw (fun w => upperCoords (M.A w j) p) (coordLaw (Real.toNNReal (c / W)) p) M.P :=
  (hasLaw_upperCoords_eval _ p).fun_comp (h.1 j)

/-- All block coordinates are independent. -/
theorem iIndepFun_blockCoords (h : M.IsIndependent c) : iIndepFun (blockCoords M) M.P := by
  set S := Real.toNNReal (c / W)
  have hblocks : iIndepFun (fun j w => upperCoords (M.A w j)) M.P :=
    h.2.1.comp (fun _ => upperCoords) (fun _ => measurable_upperCoords)
  have hjoint : HasLaw (fun w j => upperCoords (M.A w j))
      (Measure.pi fun _ : Fin k => Measure.pi (coordLaw (W := W) S)) M.P :=
    hblocks.hasLaw_pi (fun j => (hasLaw_upperCoords S).fun_comp (h.1 j))
  have hm : Measurable (fun (f : Fin k → Johansson.UpperPair W → ℝ × ℝ)
      (σ : Σ _ : Fin k, Johansson.UpperPair W) => f σ.1 σ.2) :=
    measurable_pi_iff.mpr fun σ => (measurable_pi_apply σ.2).comp (measurable_pi_apply σ.1)
  have hcur : HasLaw (fun w σ => blockCoords M σ w)
      (Measure.pi fun σ : (Σ _ : Fin k, Johansson.UpperPair W) => coordLaw S σ.2) M.P := by
    have h1 := (hasLaw_map (P := Measure.pi fun _ : Fin k => Measure.pi (coordLaw (W := W) S))
      hm.aemeasurable).fun_comp hjoint
    rw [map_uncurry_pi_pi (fun (_ : Fin k) (p : Johansson.UpperPair W) => coordLaw S p)] at h1
    exact h1
  exact iIndepFun_of_hasLaw_pi (measurable_blockCoords M) hcur

/-- `Re (A_j)_{aa}` is real Gaussian of variance `c/W`. -/
theorem hasLaw_diag (h : M.IsIndependent c) (j : Fin k) (a : Fin W) :
    HasLaw (fun w => (M.A w j a a).re) (gaussianReal 0 (Real.toNNReal (c / W))) M.P := by
  have h0 := hasLaw_blockCoord h j ⟨(a, a), le_rfl⟩
  rw [coordLaw_diag] at h0
  exact hasLaw_fst_of_map_zero h0

/-- For `a ≠ b`, `(Re A_jab, Im A_jab)` are i.i.d. centered Gaussians of variance `c/(2W)`. -/
theorem hasLaw_offdiag (h : M.IsIndependent c) (j : Fin k) (a b : Fin W) (hab : a ≠ b) :
    HasLaw (fun w => ((M.A w j a b).re, (M.A w j a b).im))
      ((gaussianReal 0 (Real.toNNReal (c / W) / 2)).prod
        (gaussianReal 0 (Real.toNNReal (c / W) / 2))) M.P := by
  rcases le_or_gt a b with hle | hlt
  · have h0 := hasLaw_blockCoord h j ⟨(a, b), hle⟩
    rw [coordLaw_offdiag _ a b hle hab] at h0
    exact h0
  · have h0 := hasLaw_blockCoord h j ⟨(b, a), hlt.le⟩
    rw [coordLaw_offdiag _ b a hlt.le (Ne.symm hab)] at h0
    have h1 := hasLaw_gaussian_pair_neg h0
    refine h1.congr (Filter.Eventually.of_forall fun w => ?_)
    have hh := (M.hermitian_A w j).apply a b
    simp only
    rw [← hh]
    simp

theorem sizes_pos (hW : 0 < W) : ∀ j, 0 < sizes k W j := fun _ => hW

theorem entryVariance_same (j : Fin k) (a b : Fin W) :
    entryVariance (sizes k W) ⟨j, a⟩ ⟨j, b⟩ = 1 / (W : ℝ) := by
  simp [entryVariance]

theorem sq_inv_sqrt (hc : 0 < c) : ((Real.sqrt c)⁻¹) ^ 2 = 1 / c := by
  rw [inv_pow, Real.sq_sqrt hc.le, one_div]

theorem variance_diag (hW : 0 < W) (hc : 0 < c) :
    ((Real.sqrt c)⁻¹) ^ 2 * (Real.toNNReal (c / W) : ℝ) = 1 / (W : ℝ) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [sq_inv_sqrt hc, Real.coe_toNNReal _ (div_nonneg hc.le hW'.le)]
  field_simp

theorem variance_offdiag (hW : 0 < W) (hc : 0 < c) :
    ((Real.sqrt c)⁻¹) ^ 2 * ((Real.toNNReal (c / W) / 2 : ℝ≥0) : ℝ) = 1 / (W : ℝ) / 2 := by
  rw [NNReal.coe_div, NNReal.coe_two, ← mul_div_assoc, variance_diag hW hc]

/-- The rescaled blocks `c^{-1/2} ⊕_j A_j` as a normalized PSSS block-GUE law. -/
def blockLaw (hW : 0 < W) (hc : 0 < c) (h : M.IsIndependent c) : Law.{0} (sizes k W) (sizes_pos hW) where
  Ω := M.Ω
  mΩ := inferInstance
  P := M.P
  probability := inferInstance
  G := fun w => noiseMatrix (Real.sqrt c)⁻¹ (M.A w)
  hermitian := fun w => noiseMatrix_isHermitian _ _ (M.hermitian_A w)
  measurable_entry := fun x y =>
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp
      ((measurable_noiseMatrix _).comp M.measurable_A))
  block_diagonal := by
    intro x y hxy
    exact Filter.Eventually.of_forall fun w => by simp [noiseMatrix, hxy]
  upper_independent := by
    apply iIndepFun_of_const_off (fun q : UpperPair (sizes k W) => q.1.1.1 = q.1.2.1)
    · intro q hq
      exact ⟨0, fun w => by simp [noiseMatrix, hq]⟩
    · have h1 := ((iIndepFun_blockCoords h).precomp blockPair_injective).comp
        (fun q => pairEntry (Real.sqrt c)⁻¹ q.1) (fun q => measurable_pairEntry _ q.1)
      convert h1 using 1
      funext q w
      exact noiseMatrix_upper _ _ (M.hermitian_A w) q.1 q.2
  diagonal_im_zero := by
    intro x
    refine Filter.Eventually.of_forall fun w => ?_
    rcases x with ⟨j, a⟩
    rw [noiseMatrix_same, Complex.im_ofReal_mul]
    have hh := (M.hermitian_A w j).apply a a
    have him : (M.A w j a a).im = 0 := by
      have := congrArg Complex.im hh
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    rw [him, mul_zero]
  diagonal_re_law := by
    intro x
    rcases x with ⟨j, a⟩
    have h0 := hasLaw_gaussian_scale (w := (⟨entryVariance (sizes k W) ⟨j, a⟩ ⟨j, a⟩,
      entryVariance_nonneg (sizes_pos hW) _ _⟩ : ℝ≥0)) (hasLaw_diag h j a) (Real.sqrt c)⁻¹ (by
        rw [variance_diag hW hc]
        exact entryVariance_same j a a)
    refine h0.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [noiseMatrix_same, Complex.re_ofReal_mul]
  offdiag_components_independent := by
    intro x y _ hne hb
    rcases x with ⟨j, a⟩
    rcases y with ⟨j', b⟩
    simp only at hb
    subst hb
    have hab : a ≠ b := fun e => hne (by rw [e])
    have h0 := hasLaw_gaussian_pair_scale (w := (⟨entryVariance (sizes k W) ⟨j, a⟩ ⟨j, b⟩ / 2,
      div_nonneg (entryVariance_nonneg (sizes_pos hW) _ _) (by norm_num)⟩ : ℝ≥0))
      (hasLaw_offdiag h j a b hab) (Real.sqrt c)⁻¹ (by
        rw [variance_offdiag hW hc]
        exact congrArg (· / 2) (entryVariance_same j a b))
    simp only [noiseMatrix_same, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    exact (hasLaw_of_gaussian_pair h0).2.2
  offdiag_re_law := by
    intro x y _ hne hb
    rcases x with ⟨j, a⟩
    rcases y with ⟨j', b⟩
    simp only at hb
    subst hb
    have hab : a ≠ b := fun e => hne (by rw [e])
    have h0 := hasLaw_gaussian_pair_scale (w := (⟨entryVariance (sizes k W) ⟨j, a⟩ ⟨j, b⟩ / 2,
      div_nonneg (entryVariance_nonneg (sizes_pos hW) _ _) (by norm_num)⟩ : ℝ≥0))
      (hasLaw_offdiag h j a b hab) (Real.sqrt c)⁻¹ (by
        rw [variance_offdiag hW hc]
        exact congrArg (· / 2) (entryVariance_same j a b))
    simp only [noiseMatrix_same, Complex.re_ofReal_mul]
    exact (hasLaw_of_gaussian_pair h0).1
  offdiag_im_law := by
    intro x y _ hne hb
    rcases x with ⟨j, a⟩
    rcases y with ⟨j', b⟩
    simp only at hb
    subst hb
    have hab : a ≠ b := fun e => hne (by rw [e])
    have h0 := hasLaw_gaussian_pair_scale (w := (⟨entryVariance (sizes k W) ⟨j, a⟩ ⟨j, b⟩ / 2,
      div_nonneg (entryVariance_nonneg (sizes_pos hW) _ _) (by norm_num)⟩ : ℝ≥0))
      (hasLaw_offdiag h j a b hab) (Real.sqrt c)⁻¹ (by
        rw [variance_offdiag hW hc]
        exact congrArg (· / 2) (entryVariance_same j a b))
    simp only [noiseMatrix_same, Complex.im_ofReal_mul]
    exact (hasLaw_of_gaussian_pair h0).2.1

/-- The rescaled block sum has exactly the canonical PSSS block-GUE law. -/
theorem noiseMatrix_hasLaw (hW : 0 < W) (hc : 0 < c) (h : M.IsIndependent c) :
    HasLaw (fun w => noiseMatrix (Real.sqrt c)⁻¹ (M.A w))
      ((canonicalMatrixMeasure (sizes k W) (sizes_pos hW)).map Subtype.val) M.P :=
  (hasLaw_map measurable_subtype_coe.aemeasurable).fun_comp
    (blockLaw hW hc h).hasLaw_matrix_canonical

end Model

/-!
## The count of `H = D + ⊕_j A_j`
-/

section Count

variable {k W : ℕ}

/-- The block sum as a function of the block family. -/
def blockSumOf (B : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  fun x y => if x.1 = y.1 then B x.1 x.2 y.2 else 0

theorem measurable_blockSumOf : Measurable (blockSumOf (k := k) (W := W)) := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  unfold blockSumOf
  split_ifs
  · exact (measurable_entry _ _).comp (measurable_pi_apply _)
  · exact measurable_const

theorem blockSum_eq (M : BlockModel k W) (w : M.Ω) : M.blockSum w = blockSumOf (M.A w) := rfl

theorem blockSum_isHermitian (M : BlockModel k W) (w : M.Ω) : (M.blockSum w).IsHermitian := by
  ext x y
  rcases x with ⟨j, a⟩
  rcases y with ⟨j', b⟩
  simp only [Matrix.conjTranspose_apply, BlockModel.blockSum]
  by_cases h : j = j'
  · subst h
    simp only [↓reduceIte]
    exact (M.hermitian_A w j).apply a b
  · simp [h, Ne.symm h]

/-- `H = D + ⊕_j A_j` is Hermitian. -/
theorem H_isHermitian (M : BlockModel k W) (w : M.Ω) : (M.H w).IsHermitian :=
  (M.hermitian_D w).add (blockSum_isHermitian M w)

theorem measurable_H (M : BlockModel k W) : Measurable M.H := by
  have hD := M.measurable_D
  have hB := measurable_blockSumOf.comp M.measurable_A
  exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
    ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp hD)).add
      ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp hB))

/-- A measurable retraction of all matrices onto the Hermitian ones. -/
def toHerm {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) : HermitianMatrix ι :=
  if hX : X ∈ {X : Matrix ι ι ℂ | X.IsHermitian} then ⟨X, hX⟩
  else ⟨0, Matrix.isHermitian_zero⟩

theorem measurable_toHerm {ι : Type} [Fintype ι] [DecidableEq ι] :
    Measurable (toHerm (ι := ι)) := by
  unfold toHerm
  exact Measurable.dite (s := {X : Matrix ι ι ℂ | X.IsHermitian})
    (f := fun x => (⟨x.1, x.2⟩ : HermitianMatrix ι))
    (g := fun _ => (⟨0, Matrix.isHermitian_zero⟩ : HermitianMatrix ι))
    (Measurable.subtype_mk measurable_subtype_coe) measurable_const measurableSet_isHermitian

theorem toHerm_of {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) : toHerm X = ⟨X, hX⟩ := by
  unfold toHerm
  split_ifs with h
  · rfl
  · exact absurd hX h

/-- The site reindexing `Fin k × Fin W ≃ Σ j : Fin k, Fin W`. -/
abbrev siteEquiv (k W : ℕ) : Fin k × Fin W ≃ Index (sizes k W) :=
  (Equiv.sigmaEquivProd (Fin k) (Fin W)).symm

/-- Factorial-moment count bound for a block model (the count input of the singular log moment
bound). Law: any `BlockModel k W` (`W > 0`) with `IsIndependent c` (`c > 0`); `H = D + ⊕_j A_j`
with arbitrary (random, independent) Hermitian deformation `D`, no norm bound. One
constant `C > 0` (the PSSS constant) is chosen before `k, W, c, M`, the closed interval
`[a, b]` (`a ≤ b`) and the order `r ≥ 1`. Conclusion: the factorial count of `H` on
`[a, b]` is integrable and `E (N_H[a,b])_r ≤ (C/√c · kW · (b - a))^r`. Uses only
`PSSS.SourceContract`, through `conditionalBlockGUECount_holds`. -/
theorem blockModel_countFactorial (source : PSSS.SourceContract.{0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k W : ℕ), 0 < W → ∀ c : ℝ, 0 < c → ∀ M : BlockModel k W,
      M.IsIndependent c → ∀ (a b : ℝ), a ≤ b → ∀ r : ℕ, 1 ≤ r →
        Integrable (factorialCount
          (fun w => eigenCount (⟨M.H w, H_isHermitian M w⟩ : HermitianMatrix _) (Icc a b)) r)
          M.P ∧
        (∫ w, factorialCount
          (fun w => eigenCount (⟨M.H w, H_isHermitian M w⟩ : HermitianMatrix _) (Icc a b)) r w
            ∂M.P) ≤ (C / Real.sqrt c * ((k * W : ℕ) : ℝ) * (b - a)) ^ r := by
  obtain ⟨C, hC, hcnt⟩ := conditionalBlockGUECount_holds source
  refine ⟨C, hC, ?_⟩
  intro k W hW c hc M h a b hab r hr
  let e := siteEquiv k W
  let G' : M.Ω → HermitianMatrix (Index (sizes k W)) := fun w =>
    hermitianReindex e (toHerm (blockSumOf (M.A w)))
  let D' : M.Ω → HermitianMatrix (Index (sizes k W)) := fun w =>
    hermitianReindex e (toHerm (M.D w))
  have hG' : Measurable G' :=
    (measurable_hermitianReindex e).comp (measurable_toHerm.comp
      (measurable_blockSumOf.comp M.measurable_A))
  have hD' : Measurable D' :=
    (measurable_hermitianReindex e).comp (measurable_toHerm.comp M.measurable_D)
  have hGv : ∀ w, (G' w).1 = Matrix.reindex e e (M.blockSum w) := by
    intro w
    show (hermitianReindex e (toHerm (blockSumOf (M.A w)))).1 = _
    rw [← blockSum_eq, toHerm_of _ (blockSum_isHermitian M w)]
    rfl
  have hDv : ∀ w, (D' w).1 = Matrix.reindex e e (M.D w) := by
    intro w
    show (hermitianReindex e (toHerm (M.D w))).1 = _
    rw [toHerm_of _ (M.hermitian_D w)]
    rfl
  have hlaw : HasLaw (fun w => ((Real.sqrt c)⁻¹ : ℂ) • (G' w).1)
      ((canonicalMatrixMeasure (sizes k W) (sizes_pos hW)).map Subtype.val) M.P := by
    refine (noiseMatrix_hasLaw hW hc h).congr (Filter.Eventually.of_forall fun w => ?_)
    show ((Real.sqrt c)⁻¹ : ℂ) • (G' w).1 = noiseMatrix (Real.sqrt c)⁻¹ (M.A w)
    rw [hGv]
    ext x y
    rcases x with ⟨j, a'⟩
    rcases y with ⟨j', b'⟩
    simp [noiseMatrix, Matrix.reindex_apply, BlockModel.blockSum, e, siteEquiv,
      Complex.ofReal_inv]
  have hind : IndepFun D' G' M.P := by
    have h1 := h.2.2.comp ((measurable_hermitianReindex e).comp (measurable_toHerm.comp
      measurable_fst)) ((measurable_hermitianReindex e).comp (measurable_toHerm.comp
      (measurable_blockSumOf (k := k) (W := W))))
    exact h1
  have hcount : (fun w => eigenCount (⟨(D' w).1 + (G' w).1, (D' w).2.add (G' w).2⟩ :
      HermitianMatrix _) (Icc a b)) =
      fun w => eigenCount (⟨M.H w, H_isHermitian M w⟩ : HermitianMatrix _) (Icc a b) := by
    funext w
    rw [← nativeEigenCount_hermitianReindex e
      (⟨M.H w, H_isHermitian M w⟩ : HermitianMatrix _) (Icc a b)]
    congr 1
    apply Subtype.ext
    show (D' w).1 + (G' w).1 = Matrix.reindex e e (M.H w)
    rw [hGv, hDv]
    ext x y
    rfl
  obtain ⟨hI, hB⟩ := hcnt M.Ω M.P k (sizes k W) (sizes_pos hW) c hc G' D' hG' hD' hlaw hind
    a b hab r hr
  rw [hcount] at hI hB
  refine ⟨hI, hB.trans (le_of_eq ?_)⟩
  congr 3
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end Count

end SingularLogLaw

end BlockBand.Wegner
