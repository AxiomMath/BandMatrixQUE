module

public import BlockBand.Critical.JointRecovery.FiniteIdentity
public import BlockBand.QUE.Invariance.CyclicLaw
public import BlockBand.QUE.Invariance.PhysicalRotationGrid

/-!
# The entire law: ring symmetries and continuity in `q`

* `map_blockSiteReindex`: the exact physical ring law is invariant under every block permutation
  preserving adjacency (`IsRingSymmetry`), in particular rotations `j ↦ j + s` and the reflection
  `j ↦ -j` (from `GaussianRingModel.map_siteReindexMatrix`).
* `finiteEntireDeterminant_transport` (deterministic) and **`finiteEntireLaw_transport`**: the
  law of `D_W` is unchanged when all profiles are transported by a ring symmetry;
  `finiteEntireLaw_rotate` (grid rotations by `s/n`), `finiteEntireLaw_reflect`.
* `isEntireLimit_reflect_iff`: reflection invariance of `IsEntireLimit` (orientation of the
  birth-time axis does not matter).
* **Continuity in `q`** at finite width: `continuous_finiteEntireDeterminant_profile` (for fixed `H`,
  into the compact-open topology) and `continuous_finiteEntireLaw` (weak topology).

Every admissible `p` (both parities), every realization, every real `E`. No hypothesis is used.
Not claimed: invariance of the critical limit under non-grid torus rotations (that would need a
uniform-in-`W` continuity estimate).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CriticalEntire

variable {p : Parameters}

/-!
## 1. Block permutations of the ring
-/

/-- The site permutation `(j, a) ↦ (φ j, a)` induced by a block permutation `φ`. -/
def blockSiteEquiv (p : Parameters) (φ : ZMod p.n ≃ ZMod p.n) : p.Site ≃ p.Site where
  toFun x := (φ x.1, x.2)
  invFun x := (φ.symm x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- A block permutation is a *ring symmetry* if it preserves nearest-neighbour adjacency. -/
def IsRingSymmetry (p : Parameters) (φ : ZMod p.n ≃ ZMod p.n) : Prop :=
  ∀ j j' : ZMod p.n, (φ j' = φ j + 1 ∨ φ j' = φ j - 1) ↔ (j' = j + 1 ∨ j' = j - 1)

/-- Ring symmetries preserve the physical variance profile. -/
theorem entryVariance_blockSiteEquiv {φ : ZMod p.n ≃ ZMod p.n} (hφ : IsRingSymmetry p φ)
    (x y : p.Site) :
    p.entryVariance (blockSiteEquiv p φ x) (blockSiteEquiv p φ y) = p.entryVariance x y := by
  have h1 : φ y.1 = φ x.1 ↔ y.1 = x.1 := φ.injective.eq_iff
  simp only [Parameters.entryVariance, blockSiteEquiv, Equiv.coe_fn_mk, h1, hφ x.1 y.1]

/-- The inverse of a ring symmetry is a ring symmetry. -/
theorem IsRingSymmetry.symm {φ : ZMod p.n ≃ ZMod p.n} (hφ : IsRingSymmetry p φ) :
    IsRingSymmetry p φ.symm := by
  intro j j'
  have := hφ (φ.symm j) (φ.symm j')
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

/-- The rotation `j ↦ j + s` is a ring symmetry. -/
theorem isRingSymmetry_addRight (s : ZMod p.n) : IsRingSymmetry p (Equiv.addRight s) := by
  intro j j'
  simp only [Equiv.coe_addRight]
  constructor
  · rintro (h | h)
    · left; linear_combination h
    · right; linear_combination h
  · rintro (h | h)
    · left; linear_combination h
    · right; linear_combination h

/-- The reflection `j ↦ -j` is a ring symmetry. -/
theorem isRingSymmetry_neg : IsRingSymmetry p (Equiv.neg (ZMod p.n)) := by
  intro j j'
  simp only [Equiv.neg_apply]
  constructor
  · rintro (h | h)
    · right; linear_combination -h
    · left; linear_combination -h
  · rintro (h | h)
    · right; linear_combination -h
    · left; linear_combination -h

/-- **The physical ring law is invariant under every ring symmetry**, in particular under all
rotations and reflections (uniqueness of the law, `map_siteReindexMatrix`). -/
theorem map_blockSiteReindex (model : p.GaussianRingModel) {φ : ZMod p.n ≃ ZMod p.n}
    (hφ : IsRingSymmetry p φ) :
    Measure.map (p.siteReindexMatrix (blockSiteEquiv p φ)) (model.law : Measure p.SiteMatrix) =
      (model.law : Measure p.SiteMatrix) :=
  model.map_siteReindexMatrix _ (entryVariance_blockSiteEquiv hφ) p.entryVariance_symm

/-!
## 2. Transport of the profiles
-/

/-- `Q'` is the transport of `Q` by `φ` on the ring grid: `Q'(j/n) = Q(φ(j)/n)`. -/
def IsProfileTransport (p : Parameters) (φ : ZMod p.n ≃ ZMod p.n) (Q Q' : C(Torus, ℝ)) : Prop :=
  ∀ k : ZMod p.n, Q' (p.ringProfilePoint k) = Q (p.ringProfilePoint (φ k))

theorem profileSourceMatrix_submatrix {φ : ZMod p.n ≃ ZMod p.n} {Q Q' : C(Torus, ℝ)}
    (h : IsProfileTransport p φ Q Q') :
    (p.profileSourceMatrix Q).submatrix (blockSiteEquiv p φ) (blockSiteEquiv p φ) =
      p.profileSourceMatrix Q' := by
  unfold Parameters.profileSourceMatrix
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  simp only [Function.comp_apply, blockSiteEquiv, Equiv.coe_fn_mk, h x.1]

/-- **Deterministic transport of `D_W`**: if `Q'_a` is the transport of `Q_a` by `φ`, then
`D_W[Q'](H) = D_W[Q](H ∘ φ⁻¹)` for every matrix `H`. -/
theorem finiteEntireDeterminant_transport (E : ℝ) {m : ℕ} (φ : ZMod p.n ≃ ZMod p.n)
    {Q Q' : Fin m → C(Torus, ℝ)} (h : ∀ a, IsProfileTransport p φ (Q a) (Q' a))
    (H : p.SiteMatrix) :
    finiteEntireDeterminant p E Q' H =
      finiteEntireDeterminant p E Q (p.siteReindexMatrix (blockSiteEquiv p φ).symm H) := by
  set e := blockSiteEquiv p φ
  have hone : (1 : p.SiteMatrix).submatrix e e = 1 := Matrix.submatrix_one_equiv e
  have hbase : (p.siteReindexMatrix e.symm H - (E : ℂ) • 1).det = (H - (E : ℂ) • 1).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext x y
    have h1 := congrFun (congrFun hone x) y
    simp only [Matrix.submatrix_apply] at h1
    simp [Parameters.siteReindexMatrix, h1]
  have hpencil : ∀ z : Fin m → ℂ,
      BlockBand.Critical.finiteCharacteristicDeterminant (p.siteReindexMatrix e.symm H - (E : ℂ) • 1)
        (fun a => p.profileSourceMatrix (Q a)) (BlockBand.Critical.widthSourceScale p.W) z =
      BlockBand.Critical.finiteCharacteristicDeterminant (H - (E : ℂ) • 1)
        (fun a => p.profileSourceMatrix (Q' a)) (BlockBand.Critical.widthSourceScale p.W) z := by
    intro z
    unfold BlockBand.Critical.finiteCharacteristicDeterminant
      BlockBand.Critical.finiteCharacteristicPencil
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext x y
    have h1 := congrFun (congrFun hone x) y
    have hP : ∀ a, p.profileSourceMatrix (Q a) (e x) (e y) = p.profileSourceMatrix (Q' a) x y :=
      fun a => congrFun (congrFun (profileSourceMatrix_submatrix (h a)) x) y
    simp only [Matrix.submatrix_apply] at h1
    simp [Parameters.siteReindexMatrix, h1, Matrix.sum_apply, hP]
  apply DFunLike.coe_injective
  funext z
  simp only [finiteEntireDeterminant, EntireFunction.coe_ofDifferentiable]
  rw [hpencil, hbase]

/-- **The law of `D_W` is invariant under every ring symmetry of the profiles** (every
admissible `p`, both parities, every realization, every `E`, every family `Q`): if `Q'_a(j/n) =
Q_a(φ(j)/n)` for a ring symmetry `φ`, then `D_W[Q']` and `D_W[Q]` have the same law. -/
theorem finiteEntireLaw_transport (R : FiniteRealization p) (E : ℝ) {m : ℕ}
    {φ : ZMod p.n ≃ ZMod p.n} (hφ : IsRingSymmetry p φ) {Q Q' : Fin m → C(Torus, ℝ)}
    (h : ∀ a, IsProfileTransport p φ (Q a) (Q' a)) :
    finiteEntireLaw R E Q' = finiteEntireLaw R E Q := by
  apply ProbabilityMeasure.toMeasure_injective
  unfold finiteEntireLaw
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
  have hfun : finiteEntireDeterminant p E Q' =
      finiteEntireDeterminant p E Q ∘ p.siteReindexMatrix (blockSiteEquiv p φ).symm := by
    funext H; exact finiteEntireDeterminant_transport E φ h H
  have he : (blockSiteEquiv p φ).symm = blockSiteEquiv p φ.symm := rfl
  rw [hfun, ← Measure.map_map (BlockBand.Critical.JointRecovery.measurable_finiteEntireDeterminant E Q)
    (p.measurable_siteReindexMatrix _), he, map_blockSiteReindex R.model hφ.symm]

/-!
## 3. Rotations and reflections
-/

/-- Rotation of a profile by the torus angle `a`. -/
def rotateProfile (a : Torus) (Q : C(Torus, ℝ)) : C(Torus, ℝ) :=
  Q.comp ⟨fun x => x + a, continuous_id.add continuous_const⟩

/-- Reflection of a profile. -/
def reflectProfile (Q : C(Torus, ℝ)) : C(Torus, ℝ) :=
  Q.comp ⟨fun x => -x, continuous_neg⟩

theorem ringProfilePoint_add (k s : ZMod p.n) :
    p.ringProfilePoint (k + s) = p.ringProfilePoint k + p.ringProfilePoint s :=
  BlockBand.QUE.Invariance.physicalProfileGrid_add p k s

theorem ringProfilePoint_neg (k : ZMod p.n) :
    p.ringProfilePoint (-k) = -p.ringProfilePoint k :=
  BlockBand.QUE.Invariance.physicalProfileGrid_neg p k

/-- **Invariance under grid rotations.** Rotating all profiles by the grid angle `s/n`
does not change the law of `D_W`. -/
theorem finiteEntireLaw_rotate (R : FiniteRealization p) (E : ℝ) {m : ℕ}
    (Q : Fin m → C(Torus, ℝ)) (s : ZMod p.n) :
    finiteEntireLaw R E (fun a => rotateProfile (p.ringProfilePoint s) (Q a)) =
      finiteEntireLaw R E Q := by
  refine finiteEntireLaw_transport R E (isRingSymmetry_addRight s) fun a k => ?_
  simp [rotateProfile, ringProfilePoint_add]

/-- **Invariance under the reflection** `x ↦ -x` of all profiles. -/
theorem finiteEntireLaw_reflect (R : FiniteRealization p) (E : ℝ) {m : ℕ}
    (Q : Fin m → C(Torus, ℝ)) :
    finiteEntireLaw R E (fun a => reflectProfile (Q a)) = finiteEntireLaw R E Q := by
  refine finiteEntireLaw_transport R E isRingSymmetry_neg fun a k => ?_
  simp [reflectProfile, ringProfilePoint_neg]

theorem fullProfile_reflect {k : ℕ} (q : Fin k → C(Torus, ℝ)) :
    fullProfile (fun a => reflectProfile (q a)) = fun a => reflectProfile (fullProfile q a) := by
  funext a
  refine Fin.cases ?_ (fun i => ?_) a
  · simp only [fullProfile, Fin.cons_zero]; rfl
  · simp only [fullProfile, Fin.cons_succ]

/-- **Reflection invariance of `IsEntireLimit` at the critical limit** (the orientation of
the ring, hence of the birth-time axis of `birthDensity`, does not matter). -/
theorem isEntireLimit_reflect_iff {b E : ℝ} {hb : 0 < b} {hb' : b < 1 / 2} {τ : PositiveRatio}
    {k : ℕ} (q : Fin k → C(Torus, ℝ)) (μ : RandomEntire (k + 1)) :
    IsEntireLimit b E hb hb' τ (fun a => reflectProfile (q a)) μ ↔ IsEntireLimit b E hb hb' τ q μ := by
  unfold IsEntireLimit
  simp only [fullProfile_reflect, finiteEntireLaw_reflect]

/-!
## 4. Continuity in the profiles (finite width)
-/

/-- `Q ↦ D_W[Q](H)` is continuous from profile families (uniform topology) to entire functions
(locally uniform topology), for every fixed matrix `H`. -/
theorem continuous_finiteEntireDeterminant_profile (E : ℝ) {m : ℕ} (H : p.SiteMatrix) :
    Continuous (fun Q : Fin m → C(Torus, ℝ) => finiteEntireDeterminant p E Q H) := by
  rw [(EntireFunction.isEmbedding_toContinuousMap (m := m)).continuous_iff]
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hQ : ∀ x : p.Site, ∀ a : Fin m, Continuous fun Q : Fin m → C(Torus, ℝ) =>
      ((Q a (p.ringProfilePoint x.1) : ℝ) : ℂ) := fun x a =>
    Complex.continuous_ofReal.comp
      ((continuous_eval_const (p.ringProfilePoint x.1)).comp (continuous_apply a))
  have hpen : Continuous fun w : (Fin m → C(Torus, ℝ)) × (Fin m → ℂ) =>
      BlockBand.Critical.finiteCharacteristicPencil (H - (E : ℂ) • 1)
        (fun a => p.profileSourceMatrix (w.1 a)) (BlockBand.Critical.widthSourceScale p.W) w.2 := by
    refine continuous_pi fun x => continuous_pi fun y => ?_
    simp only [BlockBand.Critical.finiteCharacteristicPencil, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sum_apply, Parameters.profileSourceMatrix, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with hxy
    · have hQ' : ∀ a, Continuous fun w : (Fin m → C(Torus, ℝ)) × (Fin m → ℂ) =>
          ((w.1 a (p.ringProfilePoint x.1) : ℝ) : ℂ) := fun a => (hQ x a).comp continuous_fst
      fun_prop
    · fun_prop
  have hdet := hpen.matrix_det
  exact hdet.mul continuous_const

/-- **Continuity in `q` of the finite law**: `Q ↦ law(D_W[Q])` is continuous for the weak
topology on `RandomEntire m` (dominated convergence; every realization, every `E`). -/
theorem continuous_finiteEntireLaw (R : FiniteRealization p) (E : ℝ) {m : ℕ} :
    Continuous (fun Q : Fin m → C(Torus, ℝ) => finiteEntireLaw R E Q) := by
  rw [continuous_iff_continuousAt]
  intro Q₀
  unfold ContinuousAt
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro Φ
  have hcont : Continuous fun Q : Fin m → C(Torus, ℝ) =>
      ∫ F, Φ F ∂(finiteEntireLaw R E Q : Measure (EntireFunction m)) := by
    have heq : ∀ Q : Fin m → C(Torus, ℝ),
        ∫ F, Φ F ∂(finiteEntireLaw R E Q : Measure (EntireFunction m)) =
          ∫ H, Φ (finiteEntireDeterminant p E Q H) ∂(R.model.law : Measure p.SiteMatrix) := by
      intro Q
      unfold finiteEntireLaw
      rw [ProbabilityMeasure.toMeasure_map, integral_map
        (BlockBand.Critical.JointRecovery.measurable_finiteEntireDeterminant E Q).aemeasurable
        Φ.continuous.aestronglyMeasurable]
    simp_rw [heq]
    refine continuous_of_dominated (bound := fun _ => ‖Φ‖) (fun Q => ?_)
      (fun Q => Filter.Eventually.of_forall fun H => Φ.norm_coe_le_norm _) (integrable_const _)
      (Filter.Eventually.of_forall fun H => ?_)
    · exact (Φ.continuous.measurable.comp
        (BlockBand.Critical.JointRecovery.measurable_finiteEntireDeterminant E Q)).aestronglyMeasurable
    · exact Φ.continuous.comp (continuous_finiteEntireDeterminant_profile E H)
  exact hcont.continuousAt

end BlockBand.Critical.EntireLaw
