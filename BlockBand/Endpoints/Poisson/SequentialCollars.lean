module

public import BlockBand.Endpoints.Poisson.SequentialCollarsComponents
public import BlockBand.Internal.Contracts.Critical

/-!
# The sequential-collars lemma, items (i) and (iii)

We prove items (i) (the fresh collar and the old network) and (iii) (the stage factorization)
of the sequential-collars lemma, stated in `sequentialCollars`.

* Matched ports (`matched_port`): previously removed outer coordinates carry `zI_W` and couple
  to no surviving block other than `portNeighbor` (one-ports).
* `ringCoordLaw_ae_isHermitian`: diagonal samples are a.s. Hermitian (used to remove the two
  non-real invertibility hypotheses of the factorization).
* `CoordinatePriorIsPhysical`: the coordinate prior is the physical law. Stated here and proved
  as `coordinatePriorIsPhysical`. With it, `ringCoordLaw_map_eq_model` and
  `stageFull_cyclic_empty` identify the first cyclic stage with the original ring, and
  `sequentialCollars_locked` restates items (i)/(iii) under `model.law`.
* Here the factorization is stated on the event that `M_κ⁻¹` and `(G-e)⁻¹` exist. That these
  real inverses exist almost surely at a fixed energy is proved separately
  (`ae_isUnit_det_oldInterior`, `ae_isUnit_det_collarMid`), which gives the unconditional a.s.
  factorization `stageMatrix_factorization_ae` (and `stageMatrix_factorization_ae_locked`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers (PathSample pathLaw pathMatrix pathPortCoupling)
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample)

section Combined

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

/-!
### Previously removed outer coordinates are matched auxiliary ports
-/

variable (L s) in
/-- The unique block a matched port couples to: the right port `r_j` couples to the first block
`unitPos j 3` of path `j`; the left port `c_j` couples to the path end bonded to it
(`pathEnd (j-1)` in the cyclic pairing, `pathEnd j` in the box pairing). -/
def portNeighbor : Pairing → Fin m → Fin 2 → ZMod n
  | _, j, 1 => unitPos n L s j 3
  | .cyclic, j, 0 => pathEnd L s ((finRotate m).symm j)
  | .box, j, 0 => pathEnd L s j

/-- Only the path end bonded to it bonds into a left outer block. -/
theorem bondTarget_eq_start (hL : IsCollarLayout n L) (π : Pairing) {q : ZMod n} {j : Fin m}
    (hq : bondTarget L s π q = unitPos n L s j 0) : q = portNeighbor L s π j 0 := by
  cases π
  · exact pred_of_succ_eq_start hL hq
  · by_cases hpe : ∃ i, q = pathEnd L s i
    · obtain ⟨i, rfl⟩ := hpe
      rw [bondTarget_box_pathEnd hL] at hq
      have := ((unitPos_inj hL s (by omega) (by omega)).mp hq).1
      rw [this]; rfl
    · simp only [not_exists] at hpe
      rw [bondTarget_of_ne _ hpe] at hq
      exact absurd (pred_of_succ_eq_start hL hq) (hpe _)

/-- Item (i), last clause: for `j ∈ S`, both outer coordinates of collar `j` carry the matched
scalar diagonal `zI_W`, and the only surviving block they can couple to (in either direction) is
`portNeighbor π j i`: every entry between the port and any other surviving block vanishes. So
each matched port couples to at most one block (through one random bond). -/
theorem matched_port (hL : IsCollarLayout n L) (π : Pairing) {S : Finset (Fin m)} {j : Fin m}
    (hj : j ∈ S) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) :
    (∀ x y : Fin 2 × Fin W,
      stageFull L s π S e z buf κ ω (outerSite L s j x) (outerSite L s j y) =
        (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) x y) ∧
    (∀ (x : Fin 2 × Fin W) (y : RingSite n W), ¬ IsDeleted L s S y.1 →
      y.1 ≠ outerPos L s j x.1 → y.1 ≠ portNeighbor L s π j x.1 →
      stageFull L s π S e z buf κ ω (outerSite L s j x) y = 0 ∧
        stageFull L s π S e z buf κ ω y (outerSite L s j x) = 0) := by
  have hLj := hL.2 j
  constructor
  · intro x y
    have := stageFull_outer_after (s := s) hL π S j e z buf κ ω x y
    rwa [Finset.insert_eq_of_mem hj] at this
  · rintro ⟨c, a⟩ y hyd hy1 hy2
    have hne : outerPos L s j c ≠ y.1 := fun h => hy1 h.symm
    have hxy : outerSite L s j (c, a) ≠ y := fun h => hne (congrArg Prod.fst h)
    have hb1 : bondTarget L s π (outerPos L s j c) ≠ y.1 := by
      simp only [outerPos]
      rw [bondTarget_collar hL π j (outerPos_le c)]
      fin_cases c
      · intro h; exact hyd ⟨j, hj, h.symm⟩
      · intro h; exact hy2 h.symm
    have hb2 : bondTarget L s π y.1 ≠ outerPos L s j c := by
      intro h
      fin_cases c
      · exact hy2 (bondTarget_eq_start hL π h)
      · have := eq_of_bondTarget_eq hL π j (o := 2) (by norm_num) (by omega) h
        exact hyd ⟨j, hj, this⟩
    constructor
    · simp [stageFull, stageHerm, hne, hxy, hb1, hb2]
    · simp [stageFull, stageHerm, Ne.symm hne, Ne.symm hxy, hb1, hb2]

/-!
### GUE samples are almost surely Hermitian
-/

/-- Hermitian matrices form a measurable set. -/
theorem measurableSet_isHermitian :
    MeasurableSet {A : Matrix (Fin W) (Fin W) ℂ | A.IsHermitian} := by
  have : {A : Matrix (Fin W) (Fin W) ℂ | A.IsHermitian} =
      ⋂ a, ⋂ b, {A | star (A b a) = A a b} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h a b => h.apply a b, fun h => Matrix.IsHermitian.ext h⟩
  rw [this]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    measurableSet_eq_fun (continuous_star.measurable.comp Matrix.measurable_apply)
      Matrix.measurable_apply

/-- `GUE_d(t)` samples are Hermitian almost surely. -/
theorem gueMeasure_ae_isHermitian (t : NNReal) :
    ∀ᵐ A ∂(gueMeasure (Fin W) t), A.IsHermitian := by
  have hmeas : Measurable (gueSample (ι := Fin W) t) := by
    refine Measurable.of_eval_matrix _ fun a b => ?_
    simp only [gueSample, Matrix.of_apply]
    exact measurable_const.mul ((measurable_pi_apply _).add
      (continuous_star.measurable.comp (measurable_pi_apply _)))
  unfold gueMeasure
  rw [ae_map_iff hmeas.aemeasurable measurableSet_isHermitian]
  refine Filter.Eventually.of_forall fun X => Matrix.IsHermitian.ext fun a b => ?_
  simp only [gueSample, Matrix.of_apply, star_mul', Complex.star_def, map_add,
    Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- Under the original prior every diagonal block sample is almost surely Hermitian. -/
theorem ringCoordLaw_ae_isHermitian [NeZero n] (b : ℝ) :
    ∀ᵐ ω ∂(ringCoordLaw n W b), ∀ p, (ω.1 p).IsHermitian := by
  rw [ae_all_iff]
  intro p
  have hm := (iIndepFun_ringCoord (n := n) (W := W) b).2 (Sum.inl p)
  exact (hm.ae_iff (measurableSet_setOfPred.mp measurableSet_isHermitian)).mpr
    (gueMeasure_ae_isHermitian _)

/-!
### The coordinate prior and the physical law
-/

/-- The ring matrix assembled from Gaussian coordinates: diagonal blocks `A_k`, forward bonds
`H_{k,k+1} = B_k` and reverse bonds `H_{k+1,k} = B_kᴴ`, as in the definition of the model. -/
def ringMatrix (ω : RingCoords n W) : Matrix (RingSite n W) (RingSite n W) ℂ := fun x y =>
  if x.1 = y.1 then ω.1 x.1 x.2 y.2
  else if y.1 = x.1 + 1 then ω.2 x.1 x.2 y.2
  else if x.1 = y.1 + 1 then star (ω.2 y.1 y.2 x.2) else 0

/-- **The coordinate prior is the physical law**: the diagonal blocks are independent GUE matrices with entry variance
`c/W`, the forward bonds are independent complex Gaussian matrices with entry variance `b/W`, and the reverse
bonds are their adjoints. For every admissible `p`, the push-forward of the coordinate prior
`ringCoordLaw p.n p.W p.b` (built from `gueMeasure` and `ginibreMeasure`) under `ringMatrix` is a probability law
satisfying `IsPhysicalGaussianRingLaw`. Proved as `coordinatePriorIsPhysical`; items (i) and (iii) do not use it,
it only identifies their prior with the physical law (`ringCoordLaw_map_eq_model`). -/
def CoordinatePriorIsPhysical : Prop :=
  ∀ p : Parameters, ∃ law : ProbabilityMeasure p.SiteMatrix,
    (law : Measure p.SiteMatrix) = (ringCoordLaw p.n p.W p.b).map ringMatrix ∧
      p.IsPhysicalGaussianRingLaw law

/-- Under `CoordinatePriorIsPhysical`, the coordinate prior pushes forward to the law of every
realization `model` (uniqueness of the law). -/
theorem ringCoordLaw_map_eq_model (h : CoordinatePriorIsPhysical) (p : Parameters)
    (model : p.GaussianRingModel) :
    (ringCoordLaw p.n p.W p.b).map ringMatrix = (model.law : Measure p.SiteMatrix) := by
  obtain ⟨law, hlaw, hphys⟩ := h p
  have := Parameters.physicalGaussianRingLaw_unique ⟨law, hphys⟩ model
  rw [← hlaw, ← this]

open Classical in
/-- Before any removal, the cyclic stage matrix is the original ring `H - e + iκP_C/W²`. -/
theorem stageFull_cyclic_empty (hL : IsCollarLayout n L) (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ)
    (κ : ℝ) (ω : RingCoords n W) :
    stageFull L s .cyclic ∅ e z buf κ ω =
      ringMatrix ω - (e : ℂ) • 1 + diagonal fun x =>
        ((if InSource L s buf x.1 then κ / (W : ℝ) ^ 2 else 0 : ℝ) : ℂ) * Complex.I := by
  have hn := layout_le hL k
  have hLk := hL.2 k
  have h1 : (1 : ZMod n) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 1 n).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd one_pos this; omega
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd two_pos this; omega
  have hnm : ∀ p : ZMod n, ¬ IsMatched L s ∅ p := by
    rintro p ⟨j, hj, -⟩; simp at hj
  ext ⟨p, a⟩ ⟨q, c⟩
  simp only [stageFull, stageHerm, stageAbsorption, bondTarget, ringMatrix, Matrix.add_apply,
    Matrix.sub_apply, diagonal_apply, Matrix.smul_apply, one_apply, smul_eq_mul, hnm, ite_false,
    Prod.mk.injEq]
  by_cases hxy : p = q
  · subst hxy
    have ha : ¬ p + 1 = p := by intro h; exact h1 (by linear_combination h)
    simp only [ite_true, ha, ite_false, add_zero, true_and]
    by_cases h : a = c
    · subst h; simp
    · simp [h]
  · have hxy' : ¬ q = p := fun h => hxy h.symm
    simp only [hxy, ite_false, false_and, zero_add, add_zero, mul_zero, sub_zero]
    by_cases ha : p + 1 = q
    · subst ha
      have hb : ¬ p + 1 + 1 = p := by
        intro h; apply h2; linear_combination h
      simp [hb]
    · have ha' : ¬ q = p + 1 := fun h => ha h.symm
      by_cases hb : q + 1 = p
      · subst hb
        simp [ha, ha']
      · have hb' : ¬ p = q + 1 := fun h => hb h.symm
        simp [ha, ha', hb, hb']

/-!
### Gaussian paths
-/

variable (L s) in

/-- `p₀, …, p₀+r-1` is an old component of stage `(π, S)` with selected collar `k` which is a Gaussian path: its sites
are old sites; its sample `runSample p₀ r` has the law `pathLaw W r b` under the original prior and is independent
of the fresh collar; on its sites the stage matrix is `pathMatrix - e + i·(source)`, its couplings to the two end
ports `p₀ - 1`, `runRight` are `pathPortCoupling`, and it couples to no other site. -/
def IsActualGaussianPath [NeZero n] (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (e : ℝ)
    (z : ℂ) (buf : ℕ) (b : ℝ) (p₀ : ZMod n) (r : ℕ) : Prop :=
  1 ≤ r ∧ r + 1 < n ∧
  (∀ j < r, ¬ IsDeleted L s S (p₀ + (j : ℕ)) ∧ ¬ InCollar L s k (p₀ + (j : ℕ))) ∧
  HasLaw (runSample (W := W) p₀ r) (pathLaw W r b) (ringCoordLaw n W b) ∧
  IndepFun (freshCollar L s k) (runSample (W := W) p₀ r) (ringCoordLaw n W b) ∧
  ∀ (κ : ℝ) (ω : RingCoords n W),
    (stageFull L s π S e z buf κ ω).submatrix (runSite p₀) (runSite p₀) =
        pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1 +
          diagonal (fun x : Fin r × Fin W =>
            ((stageAbsorption L s S buf κ z.im W (p₀ + (x.1.val : ℕ)) : ℝ) : ℂ) * Complex.I) ∧
    (stageFull L s π S e z buf κ ω).submatrix (runSite p₀) (runPortSite L s π p₀ r) =
        pathPortCoupling (runSample p₀ r ω) ∧
    ∀ (x : Fin r × Fin W) (y : RingSite n W), (∀ j < r, y.1 ≠ p₀ + (j : ℕ)) →
      y.1 ≠ p₀ - 1 → y.1 ≠ runRight L s π p₀ r →
      stageFull L s π S e z buf κ ω (runSite p₀ x) y = 0 ∧
        stageFull L s π S e z buf κ ω y (runSite p₀ x) = 0

/-- Every old run is a Gaussian path (`IsActualGaussianPath`). -/
theorem IsOldRun.isActualGaussianPath [NeZero n] (hL : IsCollarLayout n L) {π : Pairing}
    {S : Finset (Fin m)} {k : Fin m} {p₀ : ZMod n} {r : ℕ} (h : IsOldRun L s π S k p₀ r)
    (e : ℝ) (z : ℂ) (buf : ℕ) (b : ℝ) :
    IsActualGaussianPath (W := W) L s π S k e z buf b p₀ r :=
  ⟨h.one_le, h.lt, fun j hj => ⟨h.not_deleted hj, h.not_inCollar hj⟩,
    hasLaw_runSample p₀ h.one_le (by have := h.lt; omega) b,
    h.indepFun_freshCollar hL b,
    fun κ ω => ⟨h.interior e z buf κ ω, h.ports e z buf κ ω,
      fun x y hy hyl hyr => h.decoupled e z buf κ ω x y hy hyl hyr⟩⟩

/-!
### Comparison with the collar objects of the critical-collar interface

The collar sample, its reaction matrix, its scattering matrix and the old response agree with
the corresponding objects of `BlockBand.Internal.Contracts.Critical`.
-/

/-- The fresh collar as a `Critical.CollarSample`: end diagonals `(A_left, A_right)`, common-port bonds
`(B_left, B_rightᴴ)` to the middle block, middle block `G` on the port index `Fin 1 × Fin W`. -/
def toCriticalCollar (C : CollarSample W) : BlockBand.Internal.Contracts.Critical.CollarSample W :=
  ((![C.1 0, C.1 2], fun a _ => if a = 0 then C.2 0 else (C.2 1)ᴴ),
    (C.1 1).submatrix Prod.snd Prod.snd)

/-- At the matched value `z = z_b(e)` (`boundaryZ b e`), the `K_c`, `U` and `r` of the stage factorization are
`collarReaction`, `collarScattering` (with `s = ν = 0`) and `oldScattering` of the collar kernel theorem. -/
theorem collarKc_eq_collarReaction (b e : ℝ) (C : CollarSample W) :
    collarKc e (BlockBand.Internal.Contracts.Layers.boundaryZ b e).re C =
        BlockBand.Internal.Contracts.Critical.collarReaction b e 0 0 (toCriticalCollar C) ∧
      collarU (BlockBand.Internal.Contracts.Layers.boundaryZ b e).im
          (collarKc e (BlockBand.Internal.Contracts.Layers.boundaryZ b e).re C) =
        BlockBand.Internal.Contracts.Critical.collarScattering b e 0 0 (toCriticalCollar C) ∧
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        oldResponse (BlockBand.Internal.Contracts.Layers.boundaryZ b e) X =
          BlockBand.Internal.Contracts.Critical.oldScattering b e X := by
  open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical in
  have hsh : collarShift e 0 0 = (e : ℂ) := by simp [collarShift]
  let eq1 : Fin 1 × Fin W ≃ Fin W := Equiv.uniqueProd (Fin W) (Fin 1)
  have hbond : bondMatrix .common (toCriticalCollar C).1.2 =
      (collarBondBlock C).submatrix id eq1 := by
    ext ⟨a, x⟩ ⟨c, y⟩
    fin_cases a <;> fin_cases c <;>
      simp [bondMatrix, toCriticalCollar, collarBondBlock, LayerShape.incident, eq1,
        conjTranspose_apply]
  have hmid : (toCriticalCollar C).2 - collarShift e 0 0 • 1 =
      (collarMidBlock e C).submatrix eq1 eq1 := by
    rw [hsh]
    ext ⟨a, x⟩ ⟨c, y⟩
    fin_cases a; fin_cases c
    simp [toCriticalCollar, collarMidBlock, eq1, one_apply]
  have hdiag : BlockBand.Internal.Contracts.Layers.blockDiag (toCriticalCollar C).1.1 -
      (collarShift e 0 0 + ((boundaryZ b e).re : ℂ)) • 1 =
      collarOuterBlock e C - ((boundaryZ b e).re : ℂ) • 1 := by
    rw [hsh]
    ext ⟨i, x⟩ ⟨j, y⟩
    fin_cases i <;> fin_cases j <;>
      simp [BlockBand.Internal.Contracts.Layers.blockDiag, toCriticalCollar, collarOuterBlock,
        one_apply] <;> split_ifs <;> ring
  have hK : collarKc e (boundaryZ b e).re C = collarReaction b e 0 0 (toCriticalCollar C) := by
    unfold collarKc collarK collarReaction
    rw [hdiag, hmid, hbond, inv_submatrix_equiv, conjTranspose_submatrix,
      submatrix_mul_equiv _ _ id eq1 eq1, submatrix_mul_equiv _ _ id eq1 id, submatrix_id_id]
  refine ⟨hK, ?_, fun X => ?_⟩
  · rw [hK]
    unfold collarU collarScattering
    push_cast; ring_nf
  · unfold oldResponse oldScattering
    push_cast; ring_nf

/-!
### The sequential-collars lemma, items (i) and (iii)
-/

/-- **The sequential-collars lemma (i) and (iii)**.

Setting: a ring of `n` blocks of width `W` laid out as `m` units (collar `k` = three blocks at
offsets `0,1,2` from `unitPos k 0`, then the complementary path `k` of `L k ≥ 1` blocks),
`IsCollarLayout n L`; buffer width `buf` (the rounded `RW`) defining the source set `C`
(`InSource`); a real energy `e`, a matched scalar `z` with `Im z > 0`, a source strength `κ`.
Law: the original prior `ringCoordLaw n W b` (independent `GUE_W(c/W)` blocks, `Gin(b/W)`
bonds; identified with the physical law by `ringCoordLaw_map_eq_model` and
`coordinatePriorIsPhysical`, see `sequentialCollars_locked`); no conditioning on earlier stages.

For either pairing `π` and every stage (previously removed set `S`, selected collar `k ∉ S`, any
deterministic order produces such stages):

(i) the fresh collar `freshCollar k` has law `GUE³ ⊗ Gin²` and is independent of all old
coordinates and of the old network `(M_κ, C_o)` for every `κ`; the old components incident to its
two outer coordinates are Gaussian paths (`IsActualGaussianPath`), the right one starting
after the right outer block `unitPos k 2` and the left one ending at the left outer block
`unitPos k 0`, each other end being either the selected collar or a previously removed outer
coordinate; every previously removed outer coordinate is a matched one-port `zI_W`.

(iii) almost surely, for every `κ ≥ 0`, whenever the two real inverses `M_κ⁻¹`, `(G-e)⁻¹` exist
(they exist a.s. at each fixed `κ`: `stageMatrix_factorization_ae` drops this condition),
`det H^before / det H^after = det(G-e) det(K_c+iη)/(2iη)^{2W} · det(I - U r_κ)` with the
prefactor `collarPrefactor e z (freshCollar k ω)` independent of `κ`. Finally the fully matched
models of the two pairings agree up to the deterministic permutation `finalSitePerm`. -/
theorem sequentialCollars [NeZero n] (hL : IsCollarLayout n L) (b : ℝ) (buf : ℕ) (e : ℝ)
    (z : ℂ) (hz : 0 < z.im) :
    (∀ (π : Pairing) (S : Finset (Fin m)) (k : Fin m), k ∉ S →
      -- (i) the fresh collar
      (HasLaw (freshCollar L s k) (collarLaw W b) (ringCoordLaw n W b) ∧
        IndepFun (freshCollar L s k) (oldCoords L s k) (ringCoordLaw n W b) ∧
        (∀ κ : ℝ, IndepFun (freshCollar L s k)
          (fun ω : RingCoords n W =>
            (oldInterior L s π S k e z buf κ ω, oldCoupling L s π S k e z buf κ ω))
          (ringCoordLaw n W b))) ∧
      -- (i) the incident old components are Gaussian paths
      (∃ (pR : ZMod n) (rR : ℕ) (pL : ZMod n) (rL : ℕ),
        IsActualGaussianPath (W := W) L s π S k e z buf b pR rR ∧
        IsActualGaussianPath (W := W) L s π S k e z buf b pL rL ∧
        pR - 1 = unitPos n L s k 2 ∧ runRight L s π pL rL = unitPos n L s k 0 ∧
        (∃ j ∈ insert k S, runRight L s π pR rR = unitPos n L s j 0) ∧
        (∃ j ∈ insert k S, pL - 1 = unitPos n L s j 2)) ∧
      -- (i) previously removed outer coordinates are matched auxiliary ports
      (∀ j ∈ S, ∀ (κ : ℝ) (ω : RingCoords n W),
        (∀ x y : Fin 2 × Fin W,
          stageFull L s π S e z buf κ ω (outerSite L s j x) (outerSite L s j y) =
            (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) x y) ∧
        (∀ (x : Fin 2 × Fin W) (y : RingSite n W), ¬ IsDeleted L s S y.1 →
          y.1 ≠ outerPos L s j x.1 → y.1 ≠ portNeighbor L s π j x.1 →
          stageFull L s π S e z buf κ ω (outerSite L s j x) y = 0 ∧
            stageFull L s π S e z buf κ ω y (outerSite L s j x) = 0)) ∧
      -- (iii) the exact stage factorization
      (∀ᵐ ω ∂(ringCoordLaw n W b), ∀ κ : ℝ, 0 ≤ κ →
        IsUnit (oldInterior L s π S k e z buf κ ω).det →
        IsUnit (collarMidBlock e (freshCollar L s k ω)).det →
        (stageMatrix L s π S e z buf κ ω).det /
            (stageMatrix L s π (insert k S) e z buf κ ω).det =
          collarPrefactor e z (freshCollar L s k ω) *
            (1 - collarU z.im (collarKc e z.re (freshCollar L s k ω)) *
              oldResponse z (oldSchur (oldInterior L s π S k e z buf κ ω)
                (oldCoupling L s π S k e z buf κ ω)
                (oldCoupling L s π S k e z buf κ ω)ᴴ)).det)) ∧
    -- (iii) the two pairings end at the same fully matched model
    (∀ (κ : ℝ) (ω : RingCoords n W),
      stageMatrix L s .box Finset.univ e z buf κ ω =
        (stageMatrix L s .cyclic Finset.univ e z buf κ ω).submatrix (finalSitePerm L s hL)
          (finalSitePerm L s hL)) := by
  refine ⟨fun π S k hk => ⟨⟨hasLaw_freshCollar hL k b, indepFun_freshCollar_oldCoords k b,
      fun κ => indepFun_freshCollar_oldNetwork hL π S k e z buf κ b⟩, ?_,
      fun j hj κ ω => matched_port hL π hj e z buf κ ω, ?_⟩,
    fun κ ω => final_models_agree hL e z buf κ ω⟩
  · cases π
    · obtain ⟨jR, hjR, hR⟩ := runRight_cyclic_right (s := s) hL S k
      obtain ⟨jL, hjL, hLp⟩ := left_port_cyclic_left (s := s) hL S k
      refine ⟨_, _, _, _, (isOldRun_cyclic_right hL S k).isActualGaussianPath hL e z buf b,
        (isOldRun_cyclic_left hL S k).isActualGaussianPath hL e z buf b, ?_,
        runRight_cyclic_left hL S k, ⟨jR, hjR, hR⟩, ⟨jL, hjL, hLp⟩⟩
      rw [← unitPos_succ]; ring
    · have h23 : unitPos n L s k 3 - 1 = unitPos n L s k 2 := by rw [← unitPos_succ]; ring
      exact ⟨_, _, _, _, (isOldRun_box hL S k).isActualGaussianPath hL e z buf b,
        (isOldRun_box hL S k).isActualGaussianPath hL e z buf b, h23, runRight_box hL k,
        ⟨k, Finset.mem_insert_self _ _, runRight_box hL k⟩,
        ⟨k, Finset.mem_insert_self _ _, h23⟩⟩
  · filter_upwards [ringCoordLaw_ae_isHermitian b] with ω hA
    intro κ hκ hM hG
    exact stageMatrix_factorization_of_hermitian hL hk π e z buf ω hA hκ hz hM hG

end Combined

end BlockBand.Endpoints
