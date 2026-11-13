module

public import BlockBand.Window.Count.GueWindowFactorial
public import BlockBand.Window.Count.SpectralGradientTransfer

/-!
# The one-block PSSS law in real Gaussian coordinates

Proves `GueNativeLaw`: the PSSS one-block law, realized on real Gaussian coordinates, is identified
with `gueMeasure (Fin W) (1/W)` after reindexing.

*Law.* `Ω = ((Fin W × Fin W) × Fin 2) → ℝ` with the standard real Gaussian product
`gaussianProduct 1` (all coordinates `N(0,1)`, independent). The sample is
`G(ω) = reindex e⁻¹ e⁻¹ (gueCoordMap W (1/W) ω)` with the order-compatible equivalence
`e = toFin W : Σ j : Fin 1, Fin W ≃ Fin W`. Then `reindex e e G = gueCoordMap W (1/W)`,
whose law is `gueMeasure (Fin W) (1/W)` by `gueMeasure_eq_map` (definitional).

*Conventions.* `gueCoordMap W t ω a b = √(t/2) (X_ab + conj X_ba)`,
`X_ab = (ω((a,b),0) + i ω((a,b),1))/√2`. Hence `G_aa = √t ω((a,a),0)` (variance `t = 1/W`),
and for `a ≠ b`, `Re G_ab = (√t/2)(ω((a,b),0) + ω((b,a),0))`,
`Im G_ab = (√t/2)(ω((a,b),1) - ω((b,a),1))` (each of variance `t/2`).

## Main result

* `gueNativeLaw_holds : GueNativeLaw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess
open BlockBand.External BlockBand.External.PSSS BlockBand.External.PSSS.BlockGUE
open scoped ENNReal NNReal ComplexConjugate

namespace GueNative

/-!
## Grouping independent families along a dependent index
-/

/-- Dependent grouping lemma: if the family `X i j` indexed by `Σ i, κ i` is mutually
independent, then the grouped families `(X i ·)_i` are mutually independent.
-/
theorem iIndepFun_sigma_curry {ι : Type*} {κ : ι → Type*} {Ω 𝓧 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝓧] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : (i : ι) → κ i → Ω → 𝓧} (mX : ∀ i j, Measurable (X i j))
    (h : iIndepFun (fun (p : (i : ι) × κ i) ω => X p.1 p.2 ω) P) :
    iIndepFun (fun i ω (j : κ i) => X i j ω) P := by
  have : ∀ i j, IsProbabilityMeasure (P.map (X i j)) :=
    fun i j => (Measure.isProbabilityMeasure_map_iff (mX i j).aemeasurable).mpr inferInstance
  have hjoint :=
    (iIndepFun_iff_map_fun_eq_infinitePi_map (fun p : (i : ι) × κ i => mX p.1 p.2)).1 h
  have hgroup : ∀ i, P.map (fun ω j => X i j ω) =
      Measure.infinitePi (fun j => P.map (X i j)) := by
    intro i
    have hi : iIndepFun (fun j => X i j) P :=
      h.precomp (g := fun j : κ i => (⟨i, j⟩ : (i : ι) × κ i)) sigma_mk_injective
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map (mX i)).1 hi
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_pi_iff.mpr (mX i))]
  have hcurry : (fun ω i (j : κ i) => X i j ω) =
      (MeasurableEquiv.piCurry (fun _ _ => 𝓧)) ∘
        (fun ω (p : (i : ι) × κ i) => X p.1 p.2 ω) := rfl
  rw [hcurry, ← Measure.map_map (MeasurableEquiv.piCurry (fun _ _ => 𝓧)).measurable
    (measurable_pi_iff.mpr (fun p => mX p.1 p.2)), hjoint,
    Measure.infinitePi_map_piCurry (fun i j => P.map (X i j))]
  simp_rw [hgroup]

/-!
## The one-block index
-/

theorem card_index (W : ℕ) : Fintype.card (Index (oneBlockSizes W)) = W := by
  rw [blockGUE_dimension]
  simp

/-- The order-compatible identification of the one-block index with `Fin W`. -/
def toFin (W : ℕ) : Index (oneBlockSizes W) ≃ Fin W :=
  (Fintype.equivFin (Index (oneBlockSizes W))).trans (finCongr (card_index W))

theorem toFin_val (W : ℕ) (x : Index (oneBlockSizes W)) :
    (toFin W x).val = (Fintype.equivFin (Index (oneBlockSizes W)) x).val := by
  simp [toFin]

theorem indexLE_iff (W : ℕ) (x y : Index (oneBlockSizes W)) :
    indexLE (oneBlockSizes W) x y ↔ toFin W x ≤ toFin W y := by
  rw [Fin.le_iff_val_le_val, toFin_val, toFin_val]
  rfl

/-- Real Gaussian coordinates of a `W × W` complex matrix. -/
abbrev Coord (W : ℕ) := ((Fin W × Fin W) × Fin 2) → ℝ

/-- The upper pair owning the real coordinate `((a, b), k)`: the sorted pair `{a, b}`. -/
def owner (W : ℕ) (j : (Fin W × Fin W) × Fin 2) : UpperPair (oneBlockSizes W) :=
  if h : j.1.1 ≤ j.1.2 then
    ⟨((toFin W).symm j.1.1, (toFin W).symm j.1.2), by
      rw [indexLE_iff]; simpa using h⟩
  else
    ⟨((toFin W).symm j.1.2, (toFin W).symm j.1.1), by
      rw [indexLE_iff]; simpa using (le_of_not_ge h)⟩

theorem owner_fwd (W : ℕ) (q : UpperPair (oneBlockSizes W)) (k : Fin 2) :
    owner W ((toFin W q.1.1, toFin W q.1.2), k) = q := by
  have hq : toFin W q.1.1 ≤ toFin W q.1.2 := (indexLE_iff W _ _).mp q.2
  unfold owner
  simp only [hq, ↓reduceDIte]
  apply Subtype.ext
  simp

theorem owner_bwd (W : ℕ) (q : UpperPair (oneBlockSizes W)) (k : Fin 2) :
    owner W ((toFin W q.1.2, toFin W q.1.1), k) = q := by
  have hq : toFin W q.1.1 ≤ toFin W q.1.2 := (indexLE_iff W _ _).mp q.2
  unfold owner
  by_cases h : toFin W q.1.2 ≤ toFin W q.1.1
  · have he : q.1.1 = q.1.2 := (toFin W).injective (le_antisymm hq h)
    simp only [h, ↓reduceDIte]
    apply Subtype.ext
    simp only [Equiv.symm_apply_apply]
    exact Prod.ext_iff.mpr ⟨he.symm, he⟩
  · simp only [h, ↓reduceDIte]
    apply Subtype.ext
    simp

/-- The fibre of `owner` over `q`. -/
abbrev Fibre (W : ℕ) (q : UpperPair (oneBlockSizes W)) :=
  {j : (Fin W × Fin W) × Fin 2 // owner W j = q}

/-- Extension by zero of a fibre vector. -/
def extend (W : ℕ) (q : UpperPair (oneBlockSizes W)) (u : Fibre W q → ℝ) : Coord W := by
  classical
  exact fun j => if h : owner W j = q then u ⟨j, h⟩ else 0

theorem measurable_extend (W : ℕ) (q : UpperPair (oneBlockSizes W)) :
    Measurable (extend W q) := by
  classical
  refine measurable_pi_iff.mpr fun j => ?_
  unfold extend
  by_cases h : owner W j = q
  · simp only [h, ↓reduceDIte]; exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]; exact measurable_const

/-- The variance `1/W` of the PSSS normalization. -/
abbrev tW (W : ℕ) : ℝ≥0 := Real.toNNReal (1 / W)

/-- The sample `G = reindex e⁻¹ e⁻¹ (gueCoordMap W (1/W) ω)`. -/
def sample (W : ℕ) (ω : Coord W) : Matrix (Index (oneBlockSizes W)) (Index (oneBlockSizes W)) ℂ :=
  Matrix.reindex (toFin W).symm (toFin W).symm (gueCoordMap W (tW W) ω)

theorem sample_apply (W : ℕ) (ω : Coord W) (x y : Index (oneBlockSizes W)) :
    sample W ω x y = gueCoordMap W (tW W) ω (toFin W x) (toFin W y) := by
  simp [sample]

theorem gueCoordMap_apply (W : ℕ) (t : ℝ≥0) (ω : Coord W) (a b : Fin W) :
    gueCoordMap W t ω a b = (Real.sqrt ((t : ℝ) / 2) : ℂ) *
      (((ω ((a, b), 0) : ℂ) + (ω ((a, b), 1) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ) +
        conj (((ω ((b, a), 0) : ℂ) + (ω ((b, a), 1) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ))) := by
  simp [gueCoordMap, gueSample, circularBrownianCoordinates]

/-- The upper entry as a function of its fibre. -/
def entryOfFibre (W : ℕ) (q : UpperPair (oneBlockSizes W)) (u : Fibre W q → ℝ) : ℂ :=
  gueCoordMap W (tW W) (extend W q u) (toFin W q.1.1) (toFin W q.1.2)

theorem measurable_entryOfFibre (W : ℕ) (q : UpperPair (oneBlockSizes W)) :
    Measurable (entryOfFibre W q) := by
  unfold entryOfFibre
  have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => M (toFin W q.1.1) (toFin W q.1.2) :=
    (continuous_apply _).comp (continuous_apply _)
  exact (hc.measurable.comp (continuous_gueCoordMap W (tW W)).measurable).comp
    (measurable_extend W q)

theorem sample_upper (W : ℕ) (ω : Coord W) (q : UpperPair (oneBlockSizes W)) :
    sample W ω q.1.1 q.1.2 = entryOfFibre W q (fun j => ω j.1) := by
  rw [sample_apply, entryOfFibre, gueCoordMap_apply, gueCoordMap_apply]
  have hf : ∀ k, extend W q (fun j => ω j.1) ((toFin W q.1.1, toFin W q.1.2), k) =
      ω ((toFin W q.1.1, toFin W q.1.2), k) := fun k => by
    simp only [extend, owner_fwd W q k, ↓reduceDIte]
  have hb : ∀ k, extend W q (fun j => ω j.1) ((toFin W q.1.2, toFin W q.1.1), k) =
      ω ((toFin W q.1.2, toFin W q.1.1), k) := fun k => by
    simp only [extend, owner_bwd W q k, ↓reduceDIte]
  rw [hf 0, hf 1, hb 0, hb 1]

/-!
## Coordinate laws
-/

/-- The coordinate product measure. -/
abbrev P (W : ℕ) : Measure (Coord W) := gaussianProduct (fun _ => (1 : ℝ≥0))

instance (W : ℕ) : IsProbabilityMeasure (P W) := by
  unfold P gaussianProduct; infer_instance

theorem iIndepFun_coord (W : ℕ) : iIndepFun (fun j (ω : Coord W) => ω j) (P W) := by
  unfold P gaussianProduct
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem hasLaw_coord (W : ℕ) (j : (Fin W × Fin W) × Fin 2) :
    HasLaw (fun ω : Coord W => ω j) (gaussianReal 0 1) (P W) := by
  unfold P gaussianProduct
  exact ⟨(measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval (fun _ : (Fin W × Fin W) × Fin 2 => gaussianReal 0 1) j).map_eq⟩

theorem hasLaw_gaussian_congr {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {v w : ℝ≥0} (h : HasLaw X (gaussianReal 0 v) μ) (hvw : (v : ℝ) = w) :
    HasLaw X (gaussianReal 0 w) μ := by
  have : v = w := NNReal.eq hvw
  subst this
  exact h

theorem tW_coe {W : ℕ} : ((tW W : ℝ≥0) : ℝ) = 1 / (W : ℝ) :=
  Real.coe_toNNReal _ (by positivity)

theorem entryVariance_one (W : ℕ) (x y : Index (oneBlockSizes W)) :
    entryVariance (oneBlockSizes W) x y = 1 / (W : ℝ) := by
  have h : x.1 = y.1 := Subsingleton.elim _ _
  simp [entryVariance, h]

/-- Diagonal entry: `G_aa = √t ω((a,a),0)`, real. -/
theorem gueCoordMap_diag (W : ℕ) (t : ℝ≥0) (ω : Coord W) (a : Fin W) :
    gueCoordMap W t ω a a = ((Real.sqrt ((t : ℝ) / 2) * (2 / Real.sqrt 2) * ω ((a, a), 0) : ℝ) : ℂ) := by
  rw [gueCoordMap_apply]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.div_ofReal_re, Complex.conj_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.div_ofReal_im, Complex.conj_im]
    ring
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.div_ofReal_re, Complex.conj_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.div_ofReal_im, Complex.conj_im]
    ring

/-- Strict off-diagonal real part. -/
theorem gueCoordMap_re (W : ℕ) (t : ℝ≥0) (ω : Coord W) (a b : Fin W) :
    (gueCoordMap W t ω a b).re =
      Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2 * (ω ((a, b), 0) + ω ((b, a), 0)) := by
  rw [gueCoordMap_apply]
  simp [Complex.div_ofReal_re, Complex.div_ofReal_im]
  ring

/-- Strict off-diagonal imaginary part. -/
theorem gueCoordMap_im (W : ℕ) (t : ℝ≥0) (ω : Coord W) (a b : Fin W) :
    (gueCoordMap W t ω a b).im =
      Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2 * (ω ((a, b), 1) - ω ((b, a), 1)) := by
  rw [gueCoordMap_apply]
  simp [Complex.div_ofReal_re, Complex.div_ofReal_im]
  ring

theorem scale_sq (t : ℝ≥0) :
    (Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2) ^ 2 = (t : ℝ) / 4 := by
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt zero_le_two]; ring

theorem diag_hasLaw {W : ℕ} (hW : 0 < W) (x : Index (oneBlockSizes W)) :
    HasLaw (fun ω : Coord W => (sample W ω x x).re)
      (gaussianReal 0 ⟨entryVariance (oneBlockSizes W) x x,
        entryVariance_nonneg (fun _ => hW) x x⟩) (P W) := by
  set c : ℝ := Real.sqrt (((tW W : ℝ≥0) : ℝ) / 2) * (2 / Real.sqrt 2) with hc
  have hfun : (fun ω : Coord W => (sample W ω x x).re) =
      fun ω => c * ω ((toFin W x, toFin W x), 0) := by
    funext ω
    rw [sample_apply, gueCoordMap_diag, Complex.ofReal_re]
  rw [hfun]
  have h0 := gaussianReal_const_mul (hasLaw_coord W ((toFin W x, toFin W x), 0)) c
  rw [mul_zero] at h0
  refine hasLaw_gaussian_congr h0 ?_
  change c ^ 2 * 1 = entryVariance (oneBlockSizes W) x x
  rw [entryVariance_one, hc, mul_pow, Real.sq_sqrt (by positivity), div_pow,
    Real.sq_sqrt zero_le_two, tW_coe]
  ring

theorem toFin_ne {W : ℕ} {x y : Index (oneBlockSizes W)} (hne : x ≠ y) :
    ((toFin W x, toFin W y), (0 : Fin 2)) ≠ ((toFin W y, toFin W x), 0) ∧
    ((toFin W x, toFin W y), (1 : Fin 2)) ≠ ((toFin W y, toFin W x), 1) := by
  have h : toFin W x ≠ toFin W y := fun h => hne ((toFin W).injective h)
  constructor <;> intro hh <;> exact h (congrArg (fun q => q.1.1) hh)

theorem offdiag_re_hasLaw {W : ℕ} (hW : 0 < W) (x y : Index (oneBlockSizes W)) (hne : x ≠ y) :
    HasLaw (fun ω : Coord W => (sample W ω x y).re)
      (gaussianReal 0 ⟨entryVariance (oneBlockSizes W) x y / 2,
        div_nonneg (entryVariance_nonneg (fun _ => hW) x y) (by norm_num)⟩) (P W) := by
  set s : ℝ := Real.sqrt (((tW W : ℝ≥0) : ℝ) / 2) / Real.sqrt 2 with hs
  set j₁ : (Fin W × Fin W) × Fin 2 := ((toFin W x, toFin W y), 0)
  set j₂ : (Fin W × Fin W) × Fin 2 := ((toFin W y, toFin W x), 0)
  have hfun : (fun ω : Coord W => (sample W ω x y).re) =
      (fun z => s * z) ∘ ((fun ω : Coord W => ω j₁) + fun ω => ω j₂) := by
    funext ω
    simp only [Function.comp_apply, Pi.add_apply]
    rw [sample_apply, gueCoordMap_re]
  have hsum := gaussianReal_add_gaussianReal_of_indepFun
    ((iIndepFun_coord W).indepFun (toFin_ne hne).1) (hasLaw_coord W j₁) (hasLaw_coord W j₂)
  refine ⟨?_, ?_⟩
  · rw [hfun]; fun_prop
  rw [hfun, ← Measure.map_map (by fun_prop : Measurable fun z : ℝ => s * z) (by fun_prop),
    hsum, gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    change s ^ 2 * ((1 : ℝ) + 1) = entryVariance (oneBlockSizes W) x y / 2
    rw [hs, scale_sq, entryVariance_one, tW_coe]
    ring

theorem offdiag_im_hasLaw {W : ℕ} (hW : 0 < W) (x y : Index (oneBlockSizes W)) (hne : x ≠ y) :
    HasLaw (fun ω : Coord W => (sample W ω x y).im)
      (gaussianReal 0 ⟨entryVariance (oneBlockSizes W) x y / 2,
        div_nonneg (entryVariance_nonneg (fun _ => hW) x y) (by norm_num)⟩) (P W) := by
  set s : ℝ := Real.sqrt (((tW W : ℝ≥0) : ℝ) / 2) / Real.sqrt 2 with hs
  set j₁ : (Fin W × Fin W) × Fin 2 := ((toFin W x, toFin W y), 1)
  set j₂ : (Fin W × Fin W) × Fin 2 := ((toFin W y, toFin W x), 1)
  have hneg : HasLaw (fun ω : Coord W => -ω j₂) (gaussianReal 0 1) (P W) := by
    refine ⟨(measurable_pi_apply _).neg.aemeasurable, ?_⟩
    have : (fun ω : Coord W => -ω j₂) = (fun z => -z) ∘ (fun ω => ω j₂) := rfl
    rw [this, ← Measure.map_map (by fun_prop : Measurable fun z : ℝ => -z)
      (measurable_pi_apply _), (hasLaw_coord W j₂).map_eq, gaussianReal_map_neg, neg_zero]
  have hind : IndepFun (fun ω : Coord W => ω j₁) (fun ω => -ω j₂) (P W) :=
    ((iIndepFun_coord W).indepFun (toFin_ne hne).2).comp measurable_id measurable_neg
  have hfun : (fun ω : Coord W => (sample W ω x y).im) =
      (fun z => s * z) ∘ ((fun ω : Coord W => ω j₁) + fun ω => -ω j₂) := by
    funext ω
    simp only [Function.comp_apply, Pi.add_apply]
    rw [sample_apply, gueCoordMap_im, sub_eq_add_neg]
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hind (hasLaw_coord W j₁) hneg
  refine ⟨?_, ?_⟩
  · rw [hfun]; fun_prop
  rw [hfun, ← Measure.map_map (by fun_prop : Measurable fun z : ℝ => s * z) (by fun_prop),
    hsum, gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    change s ^ 2 * ((1 : ℝ) + 1) = entryVariance (oneBlockSizes W) x y / 2
    rw [hs, scale_sq, entryVariance_one, tW_coe]
    ring

theorem offdiag_indep {W : ℕ} (x y : Index (oneBlockSizes W)) :
    IndepFun (fun ω : Coord W => (sample W ω x y).re) (fun ω => (sample W ω x y).im) (P W) := by
  classical
  set a := toFin W x
  set b := toFin W y
  let S : Finset ((Fin W × Fin W) × Fin 2) := {((a, b), 0), ((b, a), 0)}
  let T : Finset ((Fin W × Fin W) × Fin 2) := {((a, b), 1), ((b, a), 1)}
  have hST : Disjoint S T := by
    simp only [S, T, Finset.disjoint_insert_left, Finset.disjoint_insert_right,
      Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    simp
  have h := (iIndepFun_coord W).indepFun_finset S T hST (fun j => measurable_pi_apply j)
  set s : ℝ := Real.sqrt (((tW W : ℝ≥0) : ℝ) / 2) / Real.sqrt 2
  have h1 : ((a, b), (0 : Fin 2)) ∈ S := by simp [S]
  have h2 : ((b, a), (0 : Fin 2)) ∈ S := by simp [S]
  have h3 : ((a, b), (1 : Fin 2)) ∈ T := by simp [T]
  have h4 : ((b, a), (1 : Fin 2)) ∈ T := by simp [T]
  have hc := h.comp (φ := fun u : S → ℝ => s * (u ⟨_, h1⟩ + u ⟨_, h2⟩))
    (ψ := fun u : T → ℝ => s * (u ⟨_, h3⟩ - u ⟨_, h4⟩)) (by fun_prop) (by fun_prop)
  convert hc using 1
  · funext ω; simp only [Function.comp_apply]; rw [sample_apply, gueCoordMap_re]
  · funext ω; simp only [Function.comp_apply]; rw [sample_apply, gueCoordMap_im]

/-- The PSSS one-block law: `Ω = ((Fin W × Fin W) × Fin 2) → ℝ`, `P = gaussianProduct 1`,
`G = sample W` (variance `1/W`). Every field is proved. -/
def law {W : ℕ} (hW : 0 < W) : Law.{0} (oneBlockSizes W) (fun _ => hW) where
  Ω := Coord W
  mΩ := inferInstance
  P := P W
  probability := inferInstance
  G := sample W
  hermitian ω := by
    have h : (gueCoordMap W (tW W) ω).IsHermitian := by
      ext a b
      simp only [gueCoordMap, gueSample, Matrix.conjTranspose_apply, Matrix.of_apply,
        star_mul', star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
      ring
    exact h.submatrix _
  measurable_entry x y := by
    have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => M (toFin W x) (toFin W y) :=
      (continuous_apply _).comp (continuous_apply _)
    have : (fun ω => sample W ω x y) =
        (fun M : Matrix (Fin W) (Fin W) ℂ => M (toFin W x) (toFin W y)) ∘ gueCoordMap W (tW W) := by
      funext ω; exact sample_apply W ω x y
    rw [this]
    exact hc.measurable.comp (continuous_gueCoordMap W (tW W)).measurable
  block_diagonal x y hxy := absurd (Subsingleton.elim _ _) hxy
  upper_independent := by
    have h1 : iIndepFun (fun (p : (q : UpperPair (oneBlockSizes W)) × Fibre W q)
        (ω : Coord W) => ω p.2.1) (P W) :=
      (iIndepFun_coord W).precomp (Equiv.sigmaFiberEquiv (owner W)).injective
    have h2 := iIndepFun_sigma_curry
      (X := fun (q : UpperPair (oneBlockSizes W)) (j : Fibre W q) (ω : Coord W) => ω j.1)
      (fun _ _ => measurable_pi_apply _) h1
    have h3 := h2.comp (fun q => entryOfFibre W q) (fun q => measurable_entryOfFibre W q)
    convert h3 using 1
    funext q ω
    exact sample_upper W ω q
  diagonal_im_zero x := Filter.Eventually.of_forall fun ω => by
    rw [sample_apply, gueCoordMap_diag, Complex.ofReal_im]
  diagonal_re_law x := diag_hasLaw hW x
  offdiag_components_independent x y _ _ _ := offdiag_indep x y
  offdiag_re_law x y _ hne _ := offdiag_re_hasLaw hW x y hne
  offdiag_im_law x y _ hne _ := offdiag_im_hasLaw hW x y hne

theorem reindex_sample (W : ℕ) (ω : Coord W) :
    Matrix.reindex (toFin W) (toFin W) (sample W ω) = gueCoordMap W (tW W) ω := by
  ext a b
  simp [sample]

end GueNative

open GueNative in
/-- `GueNativeLaw` holds (the one-block law identification used in the sharper fresh count).
For every `W ≥ 1` the one-block law `GueNative.law hW` (real Gaussian coordinates, variance `1/W`)
and the order-compatible equivalence `GueNative.toFin W` satisfy
`reindex e e G ∼ gueMeasure (Fin W) (1/W)`. -/
theorem gueNativeLaw_holds : GueNativeLaw := by
  intro W hW
  refine ⟨GueNative.law hW, GueNative.toFin W, ?_⟩
  have hfun : (fun ω => Matrix.reindex (toFin W) (toFin W) ((GueNative.law hW).G ω)) =
      gueCoordMap W (tW W) := by
    funext ω; exact reindex_sample W ω
  refine ⟨?_, aemeasurable_id, ?_⟩
  · rw [hfun]; exact (continuous_gueCoordMap W (tW W)).measurable.aemeasurable
  · rw [hfun, Measure.map_id]
    exact (gueMeasure_eq_map W (tW W)).symm

end BlockBand.Window.Count
