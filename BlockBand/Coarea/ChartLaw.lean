module

public import BlockBand.Model.Construction.GaussianCompatibility
public import BlockBand.Coarea.Native.BlockBand.Model.GaussianRing

/-!
# The physical Gaussian ring as a chart-coordinate Gaussian ring law

*Source law.* A physical model `model : p.GaussianRingModel` for
admissible `p : BlockBand.Parameters` (`n ≥ 4`, `W ≥ 1`, `0 < b < 1/2`): a
probability measure `model.law` on raw complex site matrices `p.SiteMatrix`,
a.e. Hermitian, with the joint characteristic function of the model.

Every field of `GaussianRingModel.toNativeLaw` is proved from
`GaussianRingModel.iIndepFun_gaussianExtraction`,
`GaussianRingModel.gaussianExtraction_coordinate_hasLaw` and the a.e.
Hermitian support of the physical law (`GaussianRingModel.isPhysical`); no input
structure or assumption is added. The truncation `H` agrees with the identity `model.law`-a.e.
(`toNativeLaw_H_ae`). The measure, domain and parameters are finite and exact;
there is no limit or uniformity statement here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Parameters

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-!
### Grouping independent families
-/

/-- Grouping lemma: if the doubly indexed family `X i j` (indexed by `ι × κ`)
is mutually independent, then the grouped families `(X i ·)_i` are mutually
independent. Converse direction of Mathlib's `iIndepFun_uncurry'`. -/
theorem iIndepFun_curry_of_iIndepFun_prod {ι κ Ω 𝓧 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝓧] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → κ → Ω → 𝓧} (mX : ∀ i j, Measurable (X i j))
    (h : iIndepFun (fun (q : ι × κ) ω => X q.1 q.2 ω) P) :
    iIndepFun (fun i ω j => X i j ω) P := by
  have hjoint :=
    (iIndepFun_iff_map_fun_eq_infinitePi_map (fun q : ι × κ => mX q.1 q.2)).1 h
  have hgroup : ∀ i, P.map (fun ω j => X i j ω) =
      Measure.infinitePi (fun j => P.map (X i j)) := by
    intro i
    have hi : iIndepFun (fun j => X i j) P :=
      h.precomp (g := fun j : κ => (i, j)) (fun j j' hjj' => (Prod.ext_iff.1 hjj').2)
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map (mX i)).1 hi
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_pi_iff.mpr (mX i))]
  have hcurry : (fun ω i j => X i j ω) =
      (MeasurableEquiv.curry ι κ 𝓧) ∘ (fun ω (q : ι × κ) => X q.1 q.2 ω) := rfl
  rw [hcurry, ← Measure.map_map (MeasurableEquiv.curry ι κ 𝓧).measurable
    (measurable_pi_iff.mpr (fun q => mX q.1 q.2)), hjoint,
    Measure.infinitePi_map_curry (fun i j => P.map (X i j))]
  simp_rw [hgroup]

/-!
### Parameters
-/

/-- The admissible parameters `(n, W, b)` as a `CoareaNative.BlockBand.Params` record. All
fields are copied; `W ≥ 1` is `0 < W`. It is reducible, so the site type `Site n W` is
reducibly `p.Site`. -/
abbrev toNativeParams (p : BlockBand.Parameters) : CoareaNative.BlockBand.Params where
  n := p.n
  W := p.W
  b := p.b
  n_ge_four := p.n_ge_four
  W_ge_one := p.W_pos
  b_pos := p.b_pos
  b_lt_half := p.b_lt_half

/-- The block count is the current block count. -/
@[simp] theorem toNativeParams_n (p : BlockBand.Parameters) : p.toNativeParams.n = p.n := rfl

/-- The block width is the current block width. -/
@[simp] theorem toNativeParams_W (p : BlockBand.Parameters) : p.toNativeParams.W = p.W := rfl

/-- The bond weight is the current bond weight. -/
@[simp] theorem toNativeParams_b (p : BlockBand.Parameters) : p.toNativeParams.b = p.b := rfl

/-- The diagonal weight `c = 1 - 2b` is the current `c`. -/
@[simp] theorem toNativeParams_c (p : BlockBand.Parameters) : p.toNativeParams.c = p.c := rfl

/-- The total dimension `L = nW` is the current `N = nW`. -/
@[simp] theorem toNativeParams_L (p : BlockBand.Parameters) : p.toNativeParams.L = p.N := rfl

/-- And current site types coincide definitionally:
`Site n W = ZMod n × Fin W = p.Site`.
-/
theorem toNativeParams_site (p : BlockBand.Parameters) :
    CoareaNative.BlockBand.Site p.toNativeParams.n p.toNativeParams.W = p.Site := rfl

/-- The row-major flat index of a site is the current `siteIndex`. -/
theorem toNativeParams_siteIndexEquiv_val (p : BlockBand.Parameters) (x : p.Site) :
    (p.toNativeParams.siteIndexEquiv x).val = p.siteIndex x := by
  rw [CoareaNative.BlockBand.Conventions.ModelParameters.siteIndexEquiv_apply_val]
  simp only [toNativeParams_W, siteIndex]
  ring

/-- The upper-triangular ordering `siteLE` is `siteIndex x ≤ siteIndex y`. -/
theorem toNativeParams_siteLE_iff (p : BlockBand.Parameters) (x y : p.Site) :
    CoareaNative.BlockBand.GaussianRing.siteLE p.toNativeParams x y ↔
      p.siteIndex x ≤ p.siteIndex y := by
  unfold CoareaNative.BlockBand.GaussianRing.siteLE
  rw [toNativeParams_siteIndexEquiv_val, toNativeParams_siteIndexEquiv_val]

/-- For `n ≥ 4` the cyclic labels `k`, `k + 1`, `k - 1` are pairwise distinct. -/
theorem zmod_shifts_ne (p : BlockBand.Parameters) (k : ZMod p.n) :
    k + 1 ≠ k ∧ k - 1 ≠ k ∧ k + 1 ≠ k - 1 := by
  have hcast : ∀ m : ℕ, 0 < m → m < p.n → (m : ZMod p.n) ≠ 0 := by
    intro m hm hmn h
    have hd := (ZMod.natCast_eq_zero_iff m p.n).1 h
    have := Nat.le_of_dvd hm hd
    omega
  have h1 : (1 : ZMod p.n) ≠ 0 := by
    have := hcast 1 (by norm_num) (by have := p.n_ge_four; omega)
    simpa using this
  have h2 : (2 : ZMod p.n) ≠ 0 := by
    have := hcast 2 (by norm_num) (by have := p.n_ge_four; omega)
    simpa using this
  refine ⟨fun h => h1 ?_, fun h => h1 ?_, fun h => h2 ?_⟩
  · linear_combination h
  · linear_combination -h
  · linear_combination h

/-- **R1-M2**: the variance profile of the translated
parameters is the current entry variance, at every pair of sites.
Uses `n ≥ 4`
so that the three additive block indicators are disjoint.
-/
theorem toNativeParams_varianceProfile (p : BlockBand.Parameters) (x y : p.Site) :
    CoareaNative.BlockBand.GaussianRing.varianceProfile p.toNativeParams x y =
      p.entryVariance x y := by
  obtain ⟨d01, d02, d12⟩ := p.zmod_shifts_ne x.1
  unfold CoareaNative.BlockBand.GaussianRing.varianceProfile
    CoareaNative.BlockBand.GaussianRing.blockWeight entryVariance
  simp only [toNativeParams_W, toNativeParams_c]
  by_cases h0 : y.1 = x.1
  · have hp : ¬ y.1 = x.1 + 1 := by rw [h0]; exact fun h => d01 h.symm
    have hm : ¬ y.1 = x.1 - 1 := by rw [h0]; exact fun h => d02 h.symm
    rw [ite_eq_left h0, ite_eq_right hp, ite_eq_right hm, ite_eq_left h0]
    ring
  · by_cases hp : y.1 = x.1 + 1
    · have hm : ¬ y.1 = x.1 - 1 := by rw [hp]; exact d12
      rw [ite_eq_right h0, ite_eq_left hp, ite_eq_right hm, ite_eq_right h0, ite_eq_left (Or.inl hp)]
      ring
    · by_cases hm : y.1 = x.1 - 1
      · rw [ite_eq_right h0, ite_eq_right hp, ite_eq_left hm, ite_eq_right h0, ite_eq_left (Or.inr hm)]
        ring
      · rw [ite_eq_right h0, ite_eq_right hp, ite_eq_right hm, ite_eq_right h0, ite_eq_right (by tauto)]
        ring

/-!
### The law
-/

open Classical in

/-- Pointwise Hermitian sample used by the law: a Hermitian matrix is
kept and a non-Hermitian one (a `model.law`-null event) is replaced by `0`.
-/
def hermitianTruncation (p : BlockBand.Parameters) (X : p.SiteMatrix) : p.SiteMatrix :=
  if X.IsHermitian then X else 0

/-- The Hermitian matrices form a measurable (closed) set. -/
theorem measurableSet_isHermitian (p : BlockBand.Parameters) :
    MeasurableSet {X : p.SiteMatrix | X.IsHermitian} :=
  (isClosed_eq (by fun_prop : Continuous (fun H : p.SiteMatrix => H.conjTranspose))
    continuous_id).measurableSet

/-- The truncated sample is Hermitian at every point. -/
theorem hermitianTruncation_isHermitian (p : BlockBand.Parameters) (X : p.SiteMatrix) :
    (p.hermitianTruncation X).IsHermitian := by
  unfold hermitianTruncation
  split_ifs with h
  · exact h
  · exact Matrix.isHermitian_zero

/-- Each entry of the truncated sample is measurable. -/
theorem measurable_hermitianTruncation_entry (p : BlockBand.Parameters) (x y : p.Site) :
    Measurable (fun X : p.SiteMatrix => p.hermitianTruncation X x y) := by
  classical
  have h : (fun X : p.SiteMatrix => p.hermitianTruncation X x y) =
      fun X => if X.IsHermitian then X x y else 0 := by
    funext X
    unfold hermitianTruncation
    split_ifs <;> rfl
  rw [h]
  exact Measurable.ite (p.measurableSet_isHermitian) (by fun_prop) measurable_const

/-- Under the physical law the truncation is a.e. the identity. -/
theorem GaussianRingModel.hermitianTruncation_ae {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    ∀ᵐ X ∂(model.law : Measure p.SiteMatrix), p.hermitianTruncation X = X := by
  filter_upwards [model.isPhysical.1] with X hX
  simp [hermitianTruncation, hX]

/-- Real Gaussian coordinates assigned to an upper pair and a Boolean slot:
slot `false` is the real diagonal coordinate (diagonal pair) or the real
component (strict upper pair); slot `true` is the imaginary component (it is
an identically-zero redundant label for a diagonal pair). -/
def upperPairCoordinate (p : BlockBand.Parameters) :
    CoareaNative.BlockBand.GaussianRing.UpperPair p.toNativeParams × Bool →
      p.GaussianCoordinate
  | (q, true) => .inr (q.1.1, q.1.2, true)
  | (q, false) => if q.1.1 = q.1.2 then .inl q.1.1 else .inr (q.1.1, q.1.2, false)

/-- Distinct (upper pair, slot) labels use distinct real coordinates. -/
theorem upperPairCoordinate_injective (p : BlockBand.Parameters) :
    Function.Injective p.upperPairCoordinate := by
  rintro ⟨⟨⟨x, y⟩, hq⟩, _ | _⟩ ⟨⟨⟨x', y'⟩, hq'⟩, _ | _⟩ h <;>
    dsimp only [upperPairCoordinate] at h
  · split_ifs at h <;> cases h
    all_goals first | rfl | (subst_vars; rfl)
  · split_ifs at h
    all_goals cases h
  · split_ifs at h
    all_goals cases h
  · cases h
    rfl

/-- An upper pair of distinct sites is strictly increasing in `siteIndex`. -/
theorem siteIndex_lt_of_siteLE {p : BlockBand.Parameters} {x y : p.Site}
    (hxy : CoareaNative.BlockBand.GaussianRing.siteLE p.toNativeParams x y) (hne : x ≠ y) :
    p.siteIndex x < p.siteIndex y := by
  rw [toNativeParams_siteLE_iff] at hxy
  have : p.siteIndex x ≠ p.siteIndex y := fun h => hne (p.siteIndex_injective h)
  omega

/-- **R1-M1**, QUE-recovery law bridge.
Source: the current
physical law `model.law` on `p.SiteMatrix`.
Destination: the contract
`CoareaNative.BlockBand.GaussianRing.Law (p.toNativeParams)` with
`Ω:= p.SiteMatrix`, `P:= model.law` and `H X:= if X.IsHermitian then X else 0`.
All fields are proved from `iIndepFun_gaussianExtraction`,
`gaussianExtraction_coordinate_hasLaw`, Hermitian support, and R1-M2.
-/
def GaussianRingModel.toNativeLaw {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    CoareaNative.BlockBand.GaussianRing.Law p.toNativeParams where
  Ω := p.SiteMatrix
  mΩ := inferInstance
  P := (model.law : Measure p.SiteMatrix)
  probability := inferInstance
  H := p.hermitianTruncation
  H_hermitian := p.hermitianTruncation_isHermitian
  measurable_entry := p.measurable_hermitianTruncation_entry
  upper_independent := by
    have hE := model.iIndepFun_gaussianExtraction
    have h1 := hE.precomp p.upperPairCoordinate_injective
    have h2 := iIndepFun_curry_of_iIndepFun_prod
      (X := fun q j (X : p.SiteMatrix) => p.gaussianExtraction X (p.upperPairCoordinate (q, j)))
      (fun q j => (measurable_pi_apply _).comp p.measurable_gaussianExtraction) h1
    have h3 := h2.comp
      (fun _ (z : Bool → ℝ) => ((z false : ℝ) : ℂ) + ((z true : ℝ) : ℂ) * Complex.I)
      (fun _ => by fun_prop)
    refine (iIndepFun_congr (fun q => ?_)).mp h3
    obtain ⟨⟨x, y⟩, hq⟩ := q
    filter_upwards [model.isPhysical.1] with X hX
    simp only [Function.comp, upperPairCoordinate]
    simp only [hermitianTruncation, hX, ↓reduceIte]
    by_cases hxy : x = y
    · subst hxy
      have hd : starRingEnd ℂ (X x x) = X x x := hX.apply x x
      have him : (X x x).im = 0 := by
        have hi := congrArg Complex.im hd
        simp only [Complex.conj_im] at hi
        linarith
      apply Complex.ext <;> simp [gaussianExtraction, him]
    · have hlt := siteIndex_lt_of_siteLE hq hxy
      simp only [hxy, ↓reduceIte, gaussianExtraction, hlt, Bool.false_eq_true]
      exact Complex.re_add_im (X x y)
  diagonal_im_zero := by
    intro x
    filter_upwards [model.isPhysical.1] with X hX
    have hd : starRingEnd ℂ (p.hermitianTruncation X x x) = p.hermitianTruncation X x x :=
      (p.hermitianTruncation_isHermitian X).apply x x
    have hi := congrArg Complex.im hd
    simp only [Complex.conj_im] at hi
    linarith
  diagonal_re_law := by
    intro x
    have h := model.gaussianExtraction_coordinate_hasLaw (.inl x)
    have hae : (fun X : p.SiteMatrix => (p.hermitianTruncation X x x).re) =ᵐ[
        (model.law : Measure p.SiteMatrix)] fun X => p.gaussianExtraction X (.inl x) := by
      filter_upwards [model.hermitianTruncation_ae] with X hX
      rw [hX]
      rfl
    convert h.congr hae using 3
    apply NNReal.eq
    simp only [CoareaNative.BlockBand.GaussianRing.varianceNNReal, gaussianCoordinateVariance]
    exact p.toNativeParams_varianceProfile x x
  offdiag_components_independent := by
    intro x y hxy hne
    have hlt := siteIndex_lt_of_siteLE hxy hne
    have h := model.iIndepFun_gaussianExtraction.indepFun
      (i := .inr (x, y, false)) (j := .inr (x, y, true)) (Sum.inr_injective.ne (by simp))
    refine h.congr ?_ ?_
    · filter_upwards [model.hermitianTruncation_ae] with X hX
      simp [gaussianExtraction, hlt, hX]
    · filter_upwards [model.hermitianTruncation_ae] with X hX
      simp [gaussianExtraction, hlt, hX]
  offdiag_re_law := by
    intro x y hxy hne
    have hlt := siteIndex_lt_of_siteLE hxy hne
    have h := model.gaussianExtraction_coordinate_hasLaw (.inr (x, y, false))
    have hae : (fun X : p.SiteMatrix => (p.hermitianTruncation X x y).re) =ᵐ[
        (model.law : Measure p.SiteMatrix)] fun X => p.gaussianExtraction X (.inr (x, y, false)) := by
      filter_upwards [model.hermitianTruncation_ae] with X hX
      simp [gaussianExtraction, hlt, hX]
    convert h.congr hae using 2
    refine congrArg (gaussianReal 0) (NNReal.eq ?_)
    simp only [gaussianCoordinateVariance, hlt, ↓reduceIte]
    exact congrArg (· / 2) (p.toNativeParams_varianceProfile x y)
  offdiag_im_law := by
    intro x y hxy hne
    have hlt := siteIndex_lt_of_siteLE hxy hne
    have h := model.gaussianExtraction_coordinate_hasLaw (.inr (x, y, true))
    have hae : (fun X : p.SiteMatrix => (p.hermitianTruncation X x y).im) =ᵐ[
        (model.law : Measure p.SiteMatrix)] fun X => p.gaussianExtraction X (.inr (x, y, true)) := by
      filter_upwards [model.hermitianTruncation_ae] with X hX
      simp [gaussianExtraction, hlt, hX]
    convert h.congr hae using 2
    refine congrArg (gaussianReal 0) (NNReal.eq ?_)
    simp only [gaussianCoordinateVariance, hlt, ↓reduceIte]
    exact congrArg (· / 2) (p.toNativeParams_varianceProfile x y)

/-- The sample space is the current matrix space. -/
theorem GaussianRingModel.toNativeLaw_Ω {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) : model.toNativeLaw.Ω = p.SiteMatrix := rfl

/-- The probability is the current physical law. -/
theorem GaussianRingModel.toNativeLaw_P {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    model.toNativeLaw.P = (model.law : Measure p.SiteMatrix) := rfl

/-- The sample is the Hermitian truncation `if X.IsHermitian then X else 0`. -/
theorem GaussianRingModel.toNativeLaw_H {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (X : p.SiteMatrix) :
    model.toNativeLaw.H X = p.hermitianTruncation X := rfl

/-- **R1-M1**: the sample equals the raw matrix `model.law`-almost surely. -/
theorem GaussianRingModel.toNativeLaw_H_ae {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    ∀ᵐ X ∂(model.law : Measure p.SiteMatrix), model.toNativeLaw.H X = X :=
  model.hermitianTruncation_ae

end BlockBand.Parameters
