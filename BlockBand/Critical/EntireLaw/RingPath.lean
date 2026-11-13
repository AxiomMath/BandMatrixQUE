module

public import BlockBand.Critical.GlobalSource.Measurability
public import BlockBand.Layers.RingDecomposition
public import BlockBand.QUE.Invariance.CyclicLaw

/-!
# The entire law: the physical ring's probes are the path probes

The global Gaussian source statement (`GlobalSource`) is stated with the path law `growthPathLaw`
read at length `n - 3` (the blocks remaining after the collar is removed form an independent
Gaussian path), in the orientation path position `i` = ring block `n-2-i`. This file identifies
that object with the physical ring.

* `measurePreserving_pathAt`: `(growthPathLaw W b).map (pathAt W r) = pathLaw W r b` (`r ≥ 1`).
* `ringPathSample`: the ring path with the collar `{n-1, 0, 1}` removed, read in the `GlobalSource`
  orientation; **`map_ringPathSample`**: its law under `model.law` is `pathLaw W (n-3) b`. Proof:
  reflection invariance of the ring law (path reversal) and `rng_law_eq_map`,
  `rng_mp_split`.
* `ringProbeMatrix`, `ringProbeLaw`; **`map_ringProbe_eq_map_globalProbe`**: for every Borel `F`,
  `F(𝒦_W^{ring})` and `F(𝒦_W)` of `GlobalSource` have the same law.
* `IsRingProbeCriticalLimit`, `isRingProbeCriticalLimit_of_global`: the critical limit of
  `GlobalSource` transfers to the physical ring, along every critical sequence and realization.

No hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.GlobalSource
open scoped ENNReal NNReal

variable {p : Parameters}

/-!
## 1. Finite marginals of the countable product law
-/

/-- Reading finitely many distinct coordinates of an i.i.d. countable product. -/
theorem measurePreserving_infinitePi_comp {ι β : Type*} [Fintype ι] [MeasurableSpace β]
    (μ : Measure β) [IsProbabilityMeasure μ] (g : ι → ℕ) (hg : Function.Injective g) :
    MeasurePreserving (fun (f : ℕ → β) (i : ι) => f (g i))
      (Measure.infinitePi fun _ : ℕ => μ) (Measure.pi fun _ : ι => μ) := by
  classical
  set s : Finset ℕ := Finset.univ.image g with hs
  have hmem : ∀ i, g i ∈ s := fun i => Finset.mem_image_of_mem g (Finset.mem_univ i)
  let e : ι ≃ s := Equiv.ofBijective (fun i => ⟨g i, hmem i⟩) ⟨fun i j h => hg (congrArg
    Subtype.val h), fun ⟨x, hx⟩ => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl⟩⟩
  have h1 : MeasurePreserving (s.restrict : (ℕ → β) → (s → β))
      (Measure.infinitePi fun _ : ℕ => μ) (Measure.pi fun _ : s => μ) :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict _⟩
  have h2 := BlockBand.Layers.pg_mp_reindex μ e.symm
  have hfun : (fun (f : ℕ → β) (i : ι) => f (g i)) =
      (fun (f : s → β) (i : ι) => f (e.symm.symm i)) ∘ s.restrict := by
    funext f i; rfl
  rw [hfun]
  exact h2.comp h1

/-!
## 2. The path of length `r` read from the grown sample has the path law
-/

/-- The bond/port index map `inl i ↦ r-1-i` (internal bond `i`), `inr 0 ↦ r`, `inr 1 ↦ 0`. -/
def bondPortIndex (r : ℕ) : Fin (r - 1) ⊕ Fin 2 → ℕ
  | .inl i => r - 1 - i.val
  | .inr j => if j = 0 then r else 0

theorem bondPortIndex_injective {r : ℕ} (hr : 1 ≤ r) : Function.Injective (bondPortIndex r) := by
  rintro (i | i) (j | j) h
  · simp only [bondPortIndex] at h
    have := i.isLt; have := j.isLt
    exact congrArg Sum.inl (Fin.ext (by omega))
  · have := i.isLt
    simp only [bondPortIndex] at h
    split_ifs at h <;> omega
  · have := j.isLt
    simp only [bondPortIndex] at h
    split_ifs at h <;> omega
  · simp only [bondPortIndex] at h
    congr 1
    rcases BlockBand.Layers.rng_fin2_cases i with rfl | rfl
    · rcases BlockBand.Layers.rng_fin2_cases j with rfl | rfl
      · rfl
      · simp at h; omega
    · rcases BlockBand.Layers.rng_fin2_cases j with rfl | rfl
      · simp at h; omega
      · rfl

/-- **The near-end-grown path read at length `r ≥ 1` has the path law**:
`(growthPathLaw W b).map (pathAt W r) = pathLaw W r b`. The bonds `B_{r-1-i}ᴴ` and the ports `B_r`,
`B_0` are distinct coordinates of the bond sequence, and conjugate transposition preserves the
Ginibre law. -/
theorem measurePreserving_pathAt (W r : ℕ) (hr : 1 ≤ r) (b : ℝ) :
    MeasurePreserving (pathAt W r) (growthPathLaw W b) (pathLaw W r b) := by
  classical
  set μA := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set μB := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have hA : MeasurePreserving (fun (f : ℕ → Matrix (Fin W) (Fin W) ℂ) (i : Fin r) => f (r - 1 - i.val))
      (Measure.infinitePi fun _ : ℕ => μA) (Measure.pi fun _ : Fin r => μA) :=
    measurePreserving_infinitePi_comp μA _ fun i j h => Fin.ext (by
      have := i.isLt; have := j.isLt; omega)
  have hB1 := measurePreserving_infinitePi_comp μB (bondPortIndex r) (bondPortIndex_injective hr)
  have hB2 := BlockBand.Layers.rng_mp_sum_split (ι := Fin (r - 1)) (ι' := Fin 2) μB
  have hct : MeasurePreserving
      (fun (f : Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ) (i : Fin (r - 1)) => (f i)ᴴ)
      (Measure.pi fun _ : Fin (r - 1) => μB) (Measure.pi fun _ : Fin (r - 1) => μB) :=
    measurePreserving_pi _ _ fun _ => BlockBand.Layers.pg_mp_conjTranspose_ginibre _
  have hB := (hct.prod (MeasurePreserving.id (Measure.pi fun _ : Fin 2 => μB))).comp (hB2.comp hB1)
  have hall := hA.prod hB
  unfold growthPathLaw pathLaw
  convert hall using 1
  funext ω
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext j
  rcases BlockBand.Layers.rng_fin2_cases j with rfl | rfl <;> simp [pathAt, bondPortIndex]

/-!
## 3. The physical ring path in the orientation of `GlobalSource`
-/

/-- Ring block `n - 2 - i` (as an element of `ZMod n`) of path position `i`
(`GlobalSource.pathRingBlock`). -/
def ringBlockAt (p : Parameters) (i : ℕ) : ZMod p.n := ((p.n - 2 - i : ℕ) : ZMod p.n)

/-- **The physical path of the ring with the collar `{n-1, 0, 1}` removed**, read in the orientation
of `GlobalSource` (path position `i` = ring block `n-2-i`, port `0` = ring block `n-1`, port `1` =
ring block `1`), as a `PathSample` of length `n - 3`: blocks `H_{n-2-i, n-2-i}`, internal bonds
`H_{n-2-i, n-3-i}`, port bonds `H_{n-2, n-1}`, `H_{2, 1}`. -/
def ringPathSample (p : Parameters) (H : p.SiteMatrix) : PathSample p.W (probePathLength p.n) :=
  (fun i a c => H (ringBlockAt p i.val, a) (ringBlockAt p i.val, c),
    fun i a c => H (ringBlockAt p i.val, a) (ringBlockAt p (i.val + 1), c),
    fun j => if j = 0 then fun a c => H (ringBlockAt p 0, a) (((p.n - 1 : ℕ) : ZMod p.n), c)
      else fun a c => H (ringBlockAt p (p.n - 4), a) (1, c))

theorem measurable_ringPathSample (p : Parameters) : Measurable (ringPathSample p) := by
  have hent : ∀ x y : p.Site, Measurable fun H : p.SiteMatrix => H x y := fun x y =>
    (measurable_pi_apply y).comp (measurable_pi_apply x)
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact Measurable.of_eval fun i => Measurable.of_eval fun a =>
      Measurable.of_eval fun c => hent _ _
  · exact Measurable.of_eval fun i => Measurable.of_eval fun a =>
      Measurable.of_eval fun c => hent _ _
  · refine Measurable.of_eval fun j => ?_
    by_cases hj : j = 0
    · simp only [hj, ↓reduceIte]
      exact Measurable.of_eval fun a => Measurable.of_eval fun c => hent _ _
    · simp only [hj, ↓reduceIte]
      exact Measurable.of_eval fun a => Measurable.of_eval fun c => hent _ _

theorem neg_ringBlockAt (p : Parameters) {i : ℕ} (hi : i + 2 ≤ p.n) :
    -ringBlockAt p i = ((i + 2 : ℕ) : ZMod p.n) := by
  unfold ringBlockAt
  refine neg_eq_of_add_eq_zero_left ?_
  rw [← Nat.cast_add, show i + 2 + (p.n - 2 - i) = p.n by omega, ZMod.natCast_self]

/-- The reflection `(j, a) ↦ (-j, a)` of the ring sites. -/
def ringReflection (p : Parameters) : p.Site ≃ p.Site where
  toFun x := (-x.1, x.2)
  invFun x := (-x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- Reflection maps the ring path in the `GlobalSource` orientation to the split path at the removed
block `0` (`rngSplit 0`: path position `i` = block `i+2`). -/
theorem ringPathSample_reflect (p : Parameters) (ω : BlockBand.Layers.RngSample p) :
    ringPathSample p (p.siteReindexMatrix (ringReflection p) (BlockBand.Layers.rngAssemble p ω)) =
      (BlockBand.Layers.rngSplit 0 ω).2 := by
  have hn := p.n_ge_four
  have hc : ∀ o : ℕ, BlockBand.Layers.rngBlk (0 : ZMod p.n) o = ((o : ℕ) : ZMod p.n) := fun o => by
    simp [BlockBand.Layers.rngBlk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i a c
    have hi := i.isLt
    simp only [probePathLength] at hi
    simp only [ringPathSample, Parameters.siteReindexMatrix, ringReflection, Equiv.coe_fn_mk,
      neg_ringBlockAt p (show i.val + 2 ≤ p.n by omega), BlockBand.Layers.rngAssemble_same,
      BlockBand.Layers.rngSplit, hc]
  · funext i a c
    have hi := i.isLt
    simp only [probePathLength] at hi
    have h1 : ((i.val + 1 + 2 : ℕ) : ZMod p.n) = ((i.val + 2 : ℕ) : ZMod p.n) + 1 := by
      push_cast; ring
    simp only [ringPathSample, Parameters.siteReindexMatrix, ringReflection, Equiv.coe_fn_mk,
      neg_ringBlockAt p (show i.val + 2 ≤ p.n by omega),
      neg_ringBlockAt p (show i.val + 1 + 2 ≤ p.n by omega), h1,
      BlockBand.Layers.rngAssemble_succ, BlockBand.Layers.rngSplit, hc]
  · funext j a c
    rcases BlockBand.Layers.rng_fin2_cases j with rfl | rfl
    · have h2 : ((0 + 2 : ℕ) : ZMod p.n) = ((1 : ℕ) : ZMod p.n) + 1 := by push_cast; ring
      have h3 : -(((p.n - 1 : ℕ) : ZMod p.n)) = ((1 : ℕ) : ZMod p.n) := by
        refine neg_eq_of_add_eq_zero_left ?_
        rw [← Nat.cast_add, show 1 + (p.n - 1) = p.n by omega, ZMod.natCast_self]
      simp only [ringPathSample, Parameters.siteReindexMatrix, ringReflection, Equiv.coe_fn_mk,
        neg_ringBlockAt p (show 0 + 2 ≤ p.n by omega), h2, h3,
        BlockBand.Layers.rngAssemble_pred, BlockBand.Layers.rngSplit, hc, ↓reduceIte,
        Matrix.conjTranspose_apply]
    · have h2 : ((p.n - 4 + 2 : ℕ) : ZMod p.n) = ((p.n - 2 : ℕ) : ZMod p.n) := by
        congr 1; omega
      have h3 : -(1 : ZMod p.n) = ((p.n - 2 : ℕ) : ZMod p.n) + 1 := by
        refine neg_eq_of_add_eq_zero_left ?_
        rw [show ((p.n - 2 : ℕ) : ZMod p.n) + 1 + 1 = ((p.n - 2 + 2 : ℕ) : ZMod p.n) by push_cast; ring,
          show p.n - 2 + 2 = p.n by omega, ZMod.natCast_self]
      simp only [ringPathSample, Parameters.siteReindexMatrix, ringReflection, Equiv.coe_fn_mk,
        neg_ringBlockAt p (show p.n - 4 + 2 ≤ p.n by omega),
        h2, h3, BlockBand.Layers.rngAssemble_succ, BlockBand.Layers.rngSplit, hc]
      simp

/-- **The physical ring path minus the collar, read in the `GlobalSource` orientation, has the path
law of length `n - 3`.** Law: the physical law `model.law`, every admissible `p` (both parities).
Proof: reflection invariance of the ring law (`map_blockSiteReindex`) turns the `GlobalSource`
orientation into that of the ring split, and `rng_mp_split` identifies that path
with `pathLaw W (n-3) b`. -/
theorem map_ringPathSample (model : p.GaussianRingModel) :
    Measure.map (ringPathSample p) (model.law : Measure p.SiteMatrix) =
      pathLaw p.W (probePathLength p.n) p.b := by
  have hrefl : Measure.map (p.siteReindexMatrix (ringReflection p))
      (model.law : Measure p.SiteMatrix) = (model.law : Measure p.SiteMatrix) := by
    refine model.map_siteReindexMatrix _ (fun x y => ?_) p.entryVariance_symm
    have h1 : -y.1 = -x.1 ↔ y.1 = x.1 := neg_inj
    have h2 : (-y.1 = -x.1 + 1 ∨ -y.1 = -x.1 - 1) ↔ (y.1 = x.1 + 1 ∨ y.1 = x.1 - 1) := by
      constructor
      · rintro (h | h)
        · right; linear_combination -h
        · left; linear_combination -h
      · rintro (h | h)
        · right; linear_combination -h
        · left; linear_combination -h
    simp only [Parameters.entryVariance, ringReflection, Equiv.coe_fn_mk, h1, h2]
  have hmeas := measurable_ringPathSample p
  rw [← hrefl, Measure.map_map hmeas (p.measurable_siteReindexMatrix _),
    BlockBand.Layers.rng_law_eq_map model, Measure.map_map
      (hmeas.comp (p.measurable_siteReindexMatrix _)) (BlockBand.Layers.rng_measurable_assemble (p := p))]
  have hfun : (ringPathSample p ∘ p.siteReindexMatrix (ringReflection p)) ∘
      BlockBand.Layers.rngAssemble p = Prod.snd ∘ BlockBand.Layers.rngSplit 0 := by
    funext ω
    exact ringPathSample_reflect p ω
  rw [hfun]
  have : IsProbabilityMeasure (layerLaw p.W p.b .common) := by
    unfold layerLaw; infer_instance
  have hpl : IsProbabilityMeasure (pathLaw p.W (p.n - 3) p.b) := by
    unfold pathLaw; infer_instance
  have hfin : IsFiniteMeasure (pathLaw p.W (p.n - 3) p.b) := inferInstance
  have : SFinite (pathLaw p.W (p.n - 3) p.b) := @instSFiniteOfSigmaFinite _ _ _
    (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  exact ((measurePreserving_snd (μ := layerLaw p.W p.b .common)
    (ν := pathLaw p.W (p.n - 3) p.b)).comp (BlockBand.Layers.rng_mp_split (p := p) 0)).map_eq

/-!
## 4. Global probe matrices of the physical ring
-/

/-- `G_lead` of a path sample: the interior block of the inverse of the path with its two matched
leads (the formula of `fullInverse`, as a function of the path). -/
def pathLeadInverse (b E : ℝ) {W r : ℕ} (π : PathSample W r) :
    Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ :=
  (Matrix.fromBlocks (pathMatrix π - (E : ℂ) • 1) (pathPortCoupling π) (pathPortCoupling π)ᴴ
    (boundaryZ b E • 1))⁻¹.toBlocks₁₁

theorem leadInverse_eq_pathLeadInverse (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    leadInverse b E W n ω = pathLeadInverse b E (pathAt W (probePathLength n) ω) := rfl

/-- `𝒦 = (ζ_a^* G_lead ζ_c)` for a path sample and probe Gaussians. -/
def pathProbeMatrix (b E : ℝ) (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (x : PathSample W (probePathLength n) × (Fin J → PathSite W n → ℂ)) :
    Matrix (Fin J) (Fin J) ℂ :=
  fun a c => star (globalProbeVector W n (Q a) (x.2 a)) ⬝ᵥ
    (pathLeadInverse b E x.1 *ᵥ globalProbeVector W n (Q c) (x.2 c))

theorem globalProbeMatrix_eq_path (b E : ℝ) (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (x : GlobalProbeSample W n J) :
    globalProbeMatrix b E W n Q x = pathProbeMatrix b E W n Q (pathAt W (probePathLength n) x.1, x.2) :=
  rfl

/-- **The physical ring's global probe matrix** `𝒦_W = (ζ_a^* G_lead ζ_c)`:
`G_lead` of the ring path minus the collar (`ringPathSample`), probes on the remaining path. -/
def ringProbeMatrix (p : Parameters) (b E : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (x : p.SiteMatrix × (Fin J → PathSite p.W p.n → ℂ)) : Matrix (Fin J) (Fin J) ℂ :=
  pathProbeMatrix b E p.W p.n Q (ringPathSample p x.1, x.2)

/-- Law of the physical ring and independent circular probe Gaussians on the remaining path. -/
def ringProbeLaw (model : p.GaussianRingModel) (J : ℕ) :
    Measure (p.SiteMatrix × (Fin J → PathSite p.W p.n → ℂ)) :=
  (model.law : Measure p.SiteMatrix).prod (Measure.pi fun _ : Fin J => circularVectorLaw (PathSite p.W p.n))

theorem measurable_pathLeadInverse (b E : ℝ) (W r : ℕ) :
    Measurable (fun π : PathSample W r => pathLeadInverse b E π) := by
  have hM : Measurable (fun π : PathSample W r =>
      Matrix.fromBlocks (pathMatrix π - (E : ℂ) • 1) (pathPortCoupling π) (pathPortCoupling π)ᴴ
        (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))) := by
    have h1 := measurable_pathMatrix (W := W) (r := r)
    have h2 := measurable_pathPortCoupling (W := W) (r := r)
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    rcases x with x | x <;> rcases y with y | y
    · simp only [Matrix.fromBlocks_apply₁₁]
      exact ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp h1)).sub measurable_const
    · simp only [Matrix.fromBlocks_apply₁₂]
      exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp h2)
    · simp only [Matrix.fromBlocks_apply₂₁]
      exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp
        (measurable_conjTranspose.comp h2))
    · simp only [Matrix.fromBlocks_apply₂₂]
      exact measurable_const
  have h := measurable_matrix_inv.comp hM
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  exact (measurable_pi_apply (Sum.inl y)).comp ((measurable_pi_apply (Sum.inl x)).comp h)

theorem measurable_pathProbeMatrix (b E : ℝ) (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) :
    Measurable (pathProbeMatrix b E W n Q) := by
  have hG : Measurable fun x : PathSample W (probePathLength n) × (Fin J → PathSite W n → ℂ) =>
      pathLeadInverse b E x.1 :=
    (measurable_pathLeadInverse b E W (probePathLength n)).comp measurable_fst
  refine Measurable.of_eval fun a => Measurable.of_eval fun c => ?_
  simp only [pathProbeMatrix, dotProduct, Matrix.mulVec, globalProbeVector, Pi.star_apply]
  refine Finset.measurable_sum _ fun x _ => ?_
  refine Measurable.mul ?_ ?_
  · exact (continuous_star : Continuous (star : ℂ → ℂ)).measurable.comp (measurable_const.mul
      ((measurable_pi_apply x).comp ((measurable_pi_apply a).comp measurable_snd)))
  · refine Finset.measurable_sum _ fun y _ => ?_
    exact ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp hG)).mul
      (measurable_const.mul
        ((measurable_pi_apply y).comp ((measurable_pi_apply c).comp measurable_snd)))

/-- **The probe data of the physical ring have the law of the path probe data of `GlobalSource`.**
For every admissible `p` (both parities), every realization of the physical law, every `J`, profiles
`Q` and every measurable `F` of the probe matrix, the law of `F(𝒦_W^{ring})` under
`ringProbeLaw model J` equals the law of `F(𝒦_W)` under `globalProbeLaw p.W p.n J p.b`
(`growthPathLaw` read at length `n - 3`). Both are `(pathLaw W (n-3) b ⊗ probes).map F`. -/
theorem map_ringProbe_eq_map_globalProbe (model : p.GaussianRingModel) (b E : ℝ) {J : ℕ}
    (Q : Fin J → C(Torus, ℝ)) {X : Type*} [MeasurableSpace X]
    (F : Matrix (Fin J) (Fin J) ℂ → X) (hF : Measurable F) :
    Measure.map (fun x => F (ringProbeMatrix p b E Q x)) (ringProbeLaw model J) =
      Measure.map (fun x => F (globalProbeMatrix b E p.W p.n Q x)) (globalProbeLaw p.W p.n J p.b) := by
  have hr : 1 ≤ probePathLength p.n := by unfold probePathLength; have := p.n_ge_four; omega
  have hK : Measurable fun y => F (pathProbeMatrix b E p.W p.n Q y) :=
    hF.comp (measurable_pathProbeMatrix b E p.W p.n Q)
  have h1 : (fun x => F (ringProbeMatrix p b E Q x)) =
      (fun y => F (pathProbeMatrix b E p.W p.n Q y)) ∘ Prod.map (ringPathSample p) id := rfl
  have h2 : (fun x => F (globalProbeMatrix b E p.W p.n Q x)) =
      (fun y => F (pathProbeMatrix b E p.W p.n Q y)) ∘
        Prod.map (pathAt p.W (probePathLength p.n)) id := rfl
  rw [h1, h2, ← Measure.map_map hK ((measurable_ringPathSample p).prodMap measurable_id),
    ← Measure.map_map hK ((measurable_pathAt p.W _).prodMap measurable_id)]
  have : IsProbabilityMeasure (growthPathLaw p.W p.b) := by
    unfold growthPathLaw; infer_instance
  unfold ringProbeLaw globalProbeLaw
  rw [← Measure.map_prod_map _ _ (measurable_ringPathSample p) measurable_id,
    ← Measure.map_prod_map _ _ (measurable_pathAt p.W _) measurable_id,
    map_ringPathSample model, (measurePreserving_pathAt p.W _ hr p.b).map_eq]

/-- **Critical limit of the probe pairs of the physical ring**: along every critical sequence and
every choice of finite realizations, the probe pairs `(𝒦_W, probeGram 𝒦_W)` of the physical ring
converge to `(𝒦, probeGram 𝒦)`, `𝒦 ~ κ`, against every bounded continuous test. It follows from the
critical limit of `GlobalSource` (`isRingProbeCriticalLimit_of_global`). -/
def IsRingProbeCriticalLimit (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (τ : ℝ) {J : ℕ}
    (Q : Fin J → C(Torus, ℝ)) (κ : Measure (Matrix (Fin J) (Fin J) ℂ)) : Prop :=
  ∀ s : CriticalSequence τ, ∀ R : ∀ j, FiniteRealization (s.parameters b hb hb' j),
    ∀ Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ) ℝ,
      Tendsto (fun j => ∫ x, Φ (ringProbeMatrix (s.parameters b hb hb' j) b E Q x,
          probeGram b E (ringProbeMatrix (s.parameters b hb hb' j) b E Q x))
          ∂ringProbeLaw (R j).model J)
        atTop (𝓝 (∫ K, Φ (K, probeGram b E K) ∂κ))

theorem matrix_borelSpace (J : ℕ) : BorelSpace (Matrix (Fin J) (Fin J) ℂ) :=
  inferInstanceAs (BorelSpace (Fin J → Fin J → ℂ))

theorem isRingProbeCriticalLimit_of_global {b E : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {τ : ℝ}
    {J : ℕ} {Q : Fin J → C(Torus, ℝ)} {κ : Measure (Matrix (Fin J) (Fin J) ℂ)}
    (h : IsGlobalProbeCriticalLimit b E τ Q κ) : IsRingProbeCriticalLimit b E hb hb' τ Q κ := by
  intro s R Φ
  have := matrix_borelSpace J
  have hpair : Continuous fun K : Matrix (Fin J) (Fin J) ℂ => (K, probeGram b E K) :=
    continuous_id.prodMk (by
      have h : Continuous fun K : Matrix (Fin J) (Fin J) ℂ => K - Kᴴ :=
        continuous_id.sub continuous_id.matrix_conjTranspose
      unfold probeGram BlockBand.Internal.Contracts.Critical.imPart
      exact (h.const_smul ((2 * Complex.I)⁻¹)).const_smul (-(((etaZ b E)⁻¹ : ℝ) : ℂ)))
  have hΦ : Measurable fun K : Matrix (Fin J) (Fin J) ℂ => Φ (K, probeGram b E K) :=
    (Φ.continuous.comp hpair).measurable
  refine (h s Φ).congr fun j => ?_
  set p := s.parameters b hb hb' j
  have heq := map_ringProbe_eq_map_globalProbe (R j).model b E Q _ hΦ
  have hm1 : Measurable fun x : p.SiteMatrix × (Fin J → PathSite p.W p.n → ℂ) =>
      Φ (ringProbeMatrix p b E Q x, probeGram b E (ringProbeMatrix p b E Q x)) :=
    hΦ.comp ((measurable_pathProbeMatrix b E p.W p.n Q).comp
      ((measurable_ringPathSample p).prodMap measurable_id))
  have hm2 : Measurable fun x : GlobalProbeSample p.W p.n J =>
      Φ (globalProbeMatrix b E p.W p.n Q x, probeGram b E (globalProbeMatrix b E p.W p.n Q x)) :=
    hΦ.comp (measurable_globalProbeMatrix b E p.W p.n Q)
  have e1 := integral_map (μ := ringProbeLaw (R j).model J) hm1.aemeasurable
    (f := fun y : ℝ => y) aestronglyMeasurable_id
  have e2 := integral_map (μ := globalProbeLaw p.W p.n J p.b) hm2.aemeasurable
    (f := fun y : ℝ => y) aestronglyMeasurable_id
  change ∫ x, Φ (globalProbeMatrix b E p.W p.n Q x, probeGram b E (globalProbeMatrix b E p.W p.n Q x))
      ∂globalProbeLaw p.W p.n J p.b = _
  rw [← e2, ← heq, e1]

end BlockBand.Critical.EntireLaw
