module

public import Mathlib
public import BlockBand.Wegner.ConditionalCount
public import BlockBand.External.Johansson.SourceStatement

/-!
# PSSS mean count for one deformed block `GUE_W(c/W)` in Johansson coordinates

The `(√c)⁻¹`-scaled Gaussian matrix, reindexed by an order-compatible equivalence
`Fin W ≃ Σ j : Fin 1, Fin W`, is a `PSSS.BlockGUE.Law` with one block of size `W`
(`ProjectedGUE.gueLaw`; every field is proved). The PSSS source bound at order `r = 1`
then gives `E N_{[a,b]}(F + G) ≤ C/√c · W · (b-a)` with `C` the PSSS constant.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory ProbabilityTheory Set
open BlockBand.External BlockBand.External.PSSS BlockBand.External.PSSS.BlockGUE
open BlockBand.Counting
open scoped NNReal ENNReal

namespace ProjectedGUE

/-- One block of size `W`. -/
abbrev oneBlock (W : ℕ) : Fin 1 → ℕ := fun _ => W

theorem oneBlock_pos {W : ℕ} (hW : 0 < W) : ∀ j, 0 < oneBlock W j := fun _ => hW

theorem card_index (W : ℕ) : Fintype.card (Index (oneBlock W)) = W := by
  rw [blockGUE_dimension]
  simp

/-- The order-compatible identification of the PSSS one-block index with `Fin W`. -/
def toFin (W : ℕ) : Index (oneBlock W) ≃ Fin W :=
  (Fintype.equivFin (Index (oneBlock W))).trans (finCongr (card_index W))

theorem toFin_val (W : ℕ) (x : Index (oneBlock W)) :
    (toFin W x).val = (Fintype.equivFin (Index (oneBlock W)) x).val := by
  simp [toFin]

theorem indexLE_iff (W : ℕ) (x y : Index (oneBlock W)) :
    indexLE (oneBlock W) x y ↔ toFin W x ≤ toFin W y := by
  rw [Fin.le_iff_val_le_val, toFin_val, toFin_val]
  rfl

/-- The Johansson upper pair carrying a PSSS upper pair. -/
def upperMap (W : ℕ) (q : UpperPair (oneBlock W)) : Johansson.UpperPair W :=
  ⟨(toFin W q.1.1, toFin W q.1.2), (indexLE_iff W _ _).mp q.2⟩

theorem upperMap_injective (W : ℕ) : Function.Injective (upperMap W) := by
  rintro ⟨⟨x, y⟩, hxy⟩ ⟨⟨x', y'⟩, hxy'⟩ h
  simp only [upperMap, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := (toFin W).injective h1
  have e2 := (toFin W).injective h2
  subst e1 e2
  rfl

/-- The `(√c)⁻¹`-scaled Gaussian sample, reindexed to the PSSS one-block index. -/
def noiseHerm (W : ℕ) (c : ℝ) (z : Johansson.UpperPair W → ℝ × ℝ) :
    PSSS.HermitianMatrix (Index (oneBlock W)) :=
  hermitianScale (Real.sqrt c)⁻¹ (hermitianReindex (toFin W).symm (Johansson.gaussianMatrix z))

theorem noiseHerm_apply (W : ℕ) (c : ℝ) (z : Johansson.UpperPair W → ℝ × ℝ)
    (x y : Index (oneBlock W)) :
    (noiseHerm W c z).1 x y =
      (((Real.sqrt c)⁻¹ : ℝ) : ℂ) * Johansson.gaussianMatrixRaw z (toFin W x) (toFin W y) :=
  rfl

/-- The upper entry carried by one Johansson coordinate pair, scaled by `s`. -/
def upperValue (s : ℝ) {W : ℕ} (r : Johansson.UpperPair W) (p : ℝ × ℝ) : ℂ :=
  (s : ℂ) * if r.1.1 = r.1.2 then (p.1 : ℂ) else Johansson.complexPair p

theorem measurable_upperValue (s : ℝ) {W : ℕ} (r : Johansson.UpperPair W) :
    Measurable (upperValue s r) := by
  unfold upperValue Johansson.complexPair
  split_ifs <;> fun_prop

theorem gaussianMatrixRaw_upper {W : ℕ} (z : Johansson.UpperPair W → ℝ × ℝ)
    (r : Johansson.UpperPair W) :
    Johansson.gaussianMatrixRaw z r.1.1 r.1.2 =
      if r.1.1 = r.1.2 then ((z r).1 : ℂ) else Johansson.complexPair (z r) := by
  rcases r with ⟨⟨i, j⟩, hij⟩
  by_cases h : i = j
  · subst h
    simp [Johansson.gaussianMatrixRaw]
  · simp [Johansson.gaussianMatrixRaw, h, hij]

theorem noiseHerm_upper (W : ℕ) (c : ℝ) (z : Johansson.UpperPair W → ℝ × ℝ)
    (q : UpperPair (oneBlock W)) :
    (noiseHerm W c z).1 q.1.1 q.1.2 = upperValue (Real.sqrt c)⁻¹ (upperMap W q) (z (upperMap W q)) := by
  rw [noiseHerm_apply]
  have h := gaussianMatrixRaw_upper z (upperMap W q)
  exact congrArg (fun t => (((Real.sqrt c)⁻¹ : ℝ) : ℂ) * t) h

local instance gaussianReal_isProbability' (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal μ v

theorem hasLaw_gaussian_congr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {v w : ℝ≥0} (h : HasLaw X (gaussianReal 0 v) P) (hvw : (v : ℝ) = w) :
    HasLaw X (gaussianReal 0 w) P := by
  have : v = w := NNReal.eq hvw
  subst this
  exact h

theorem entryVariance_oneBlock (W : ℕ) (x y : Index (oneBlock W)) :
    entryVariance (oneBlock W) x y = 1 / (W : ℝ) := by
  have h : x.1 = y.1 := Subsingleton.elim _ _
  simp [entryVariance, h]

/-- The coordinate variance `c/W`. -/
abbrev coordVar (W : ℕ) (c : ℝ) : ℝ≥0 := Real.toNNReal (c / W)

theorem scale_sq_mul {W : ℕ} {c : ℝ} (hc : 0 < c) :
    (Real.sqrt c)⁻¹ ^ 2 * (coordVar W c : ℝ) = 1 / (W : ℝ) := by
  have hc' : (0 : ℝ) ≤ c / W := div_nonneg hc.le (Nat.cast_nonneg W)
  rw [coordVar, Real.coe_toNNReal _ hc', inv_pow, Real.sq_sqrt hc.le]
  field_simp

theorem coord_hasLaw (W : ℕ) (c : ℝ) (r : Johansson.UpperPair W) :
    HasLaw (fun z : Johansson.UpperPair W → ℝ × ℝ => z r)
      (Johansson.upperEntryMeasure (coordVar W c) r)
      (Johansson.coordinateMeasure W (coordVar W c)) := by
  have hU := Johansson.upperEntryMeasure_probability (N := W) (coordVar W c)
  exact (measurePreserving_eval _ r).hasLaw

/-- Joint law of the real and imaginary parts of a strict-upper scaled entry. -/
theorem offdiag_pair_hasLaw {W : ℕ} (hW : 0 < W) (c : ℝ) (hc : 0 < c) (x y : Index (oneBlock W))
    (hxy : indexLE (oneBlock W) x y) (hne : x ≠ y) :
    HasLaw (fun z : Johansson.UpperPair W → ℝ × ℝ =>
        (((noiseHerm W c z).1 x y).re, ((noiseHerm W c z).1 x y).im))
      ((gaussianReal 0 ⟨entryVariance (oneBlock W) x y / 2,
          div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩).prod
        (gaussianReal 0 ⟨entryVariance (oneBlock W) x y / 2,
          div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩))
      (Johansson.coordinateMeasure W (coordVar W c)) := by
  set s : ℝ := (Real.sqrt c)⁻¹ with hs
  let r : Johansson.UpperPair W := ⟨(toFin W x, toFin W y), (indexLE_iff W x y).mp hxy⟩
  have hne' : toFin W x ≠ toFin W y := fun h => hne ((toFin W).injective h)
  have hfun : (fun z : Johansson.UpperPair W → ℝ × ℝ =>
        (((noiseHerm W c z).1 x y).re, ((noiseHerm W c z).1 x y).im)) =
      (Prod.map (fun t : ℝ => s * t) (fun t : ℝ => s * t)) ∘
        (fun z : Johansson.UpperPair W → ℝ × ℝ => z r) := by
    funext z
    have h := gaussianMatrixRaw_upper z r
    simp only [r, hne', ↓reduceIte] at h
    rw [noiseHerm_apply, h]
    simp [Johansson.complexPair, s]
    rfl
  rw [hfun]
  refine HasLaw.comp ?_ (coord_hasLaw W c r)
  refine ⟨(measurable_fst.const_mul _).prodMk (measurable_snd.const_mul _) |>.aemeasurable, ?_⟩
  simp only [Johansson.upperEntryMeasure, r, hne', ↓reduceIte]
  rw [← Measure.map_prod_map _ _ (measurable_const_mul _) (measurable_const_mul _),
    gaussianReal_map_const_mul, mul_zero]
  have hv : (NNReal.mk (s ^ 2) (sq_nonneg _) * (coordVar W c / 2)) =
      ⟨entryVariance (oneBlock W) x y / 2,
          div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩ := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_div, NNReal.coe_ofNat]
    change s ^ 2 * ((coordVar W c : ℝ) / 2) = entryVariance (oneBlock W) x y / 2
    rw [entryVariance_oneBlock, ← scale_sq_mul (W := W) hc, hs]
    ring
  rw [hv]

theorem offdiag_re_hasLaw {W : ℕ} (hW : 0 < W) (c : ℝ) (hc : 0 < c) (x y : Index (oneBlock W))
    (hxy : indexLE (oneBlock W) x y) (hne : x ≠ y) :
    HasLaw (fun z : Johansson.UpperPair W → ℝ × ℝ => ((noiseHerm W c z).1 x y).re)
      (gaussianReal 0 ⟨entryVariance (oneBlock W) x y / 2,
          div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩)
      (Johansson.coordinateMeasure W (coordVar W c)) := by
  have hg : IsProbabilityMeasure (gaussianReal 0 ⟨entryVariance (oneBlock W) x y / 2,
      div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  exact (measurePreserving_fst (μ := gaussianReal 0 ⟨entryVariance (oneBlock W) x y / 2,
          div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩)
    (ν := gaussianReal 0 ⟨entryVariance (oneBlock W) x y / 2,
          div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩)).hasLaw.comp
    (offdiag_pair_hasLaw hW c hc x y hxy hne)

theorem offdiag_im_hasLaw {W : ℕ} (hW : 0 < W) (c : ℝ) (hc : 0 < c) (x y : Index (oneBlock W))
    (hxy : indexLE (oneBlock W) x y) (hne : x ≠ y) :
    HasLaw (fun z : Johansson.UpperPair W → ℝ × ℝ => ((noiseHerm W c z).1 x y).im)
      (gaussianReal 0 ⟨entryVariance (oneBlock W) x y / 2,
          div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩)
      (Johansson.coordinateMeasure W (coordVar W c)) := by
  have hg : IsProbabilityMeasure (gaussianReal 0 ⟨entryVariance (oneBlock W) x y / 2,
      div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  exact (measurePreserving_snd (μ := gaussianReal 0 ⟨entryVariance (oneBlock W) x y / 2,
          div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩)
    (ν := gaussianReal 0 ⟨entryVariance (oneBlock W) x y / 2,
          div_nonneg (entryVariance_nonneg (oneBlock_pos hW) x y) (by norm_num)⟩)).hasLaw.comp
    (offdiag_pair_hasLaw hW c hc x y hxy hne)

/-- The Johansson diagonal coordinate of a PSSS index. -/
def diagPair (W : ℕ) (x : Index (oneBlock W)) : Johansson.UpperPair W :=
  ⟨(toFin W x, toFin W x), le_rfl⟩

theorem noiseHerm_diag_re (W : ℕ) (c : ℝ) (z : Johansson.UpperPair W → ℝ × ℝ)
    (x : Index (oneBlock W)) :
    ((noiseHerm W c z).1 x x).re = (Real.sqrt c)⁻¹ * (z (diagPair W x)).1 := by
  rw [noiseHerm_apply]
  simp [Johansson.gaussianMatrixRaw, diagPair]

theorem noiseHerm_diag_im (W : ℕ) (c : ℝ) (z : Johansson.UpperPair W → ℝ × ℝ)
    (x : Index (oneBlock W)) : ((noiseHerm W c z).1 x x).im = 0 := by
  rw [noiseHerm_apply]
  simp [Johansson.gaussianMatrixRaw]

theorem diag_hasLaw {W : ℕ} (hW : 0 < W) (c : ℝ) (hc : 0 < c) (x : Index (oneBlock W)) :
    HasLaw (fun z : Johansson.UpperPair W → ℝ × ℝ => ((noiseHerm W c z).1 x x).re)
      (gaussianReal 0 ⟨entryVariance (oneBlock W) x x,
        entryVariance_nonneg (oneBlock_pos hW) x x⟩)
      (Johansson.coordinateMeasure W (coordVar W c)) := by
  have hfun : (fun z : Johansson.UpperPair W → ℝ × ℝ => ((noiseHerm W c z).1 x x).re) =
      fun z => (Real.sqrt c)⁻¹ * (z (diagPair W x)).1 := by
    funext z
    exact noiseHerm_diag_re W c z x
  rw [hfun]
  have hU := Johansson.upperEntryMeasure_probability (N := W) (coordVar W c)
  have h1 : HasLaw (fun p : ℝ × ℝ => p.1) (gaussianReal 0 (coordVar W c))
      (Johansson.upperEntryMeasure (coordVar W c) (diagPair W x)) := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    simp only [Johansson.upperEntryMeasure, diagPair, ↓reduceIte]
    rw [Measure.map_map measurable_fst (by fun_prop)]
    exact Measure.map_id
  have hfst : HasLaw (fun z : Johansson.UpperPair W → ℝ × ℝ => (z (diagPair W x)).1)
      (gaussianReal 0 (coordVar W c)) (Johansson.coordinateMeasure W (coordVar W c)) :=
    h1.comp (coord_hasLaw W c _)
  have h0 := gaussianReal_const_mul hfst (Real.sqrt c)⁻¹
  rw [mul_zero] at h0
  refine hasLaw_gaussian_congr h0 ?_
  change (Real.sqrt c)⁻¹ ^ 2 * (coordVar W c : ℝ) = entryVariance (oneBlock W) x x
  rw [scale_sq_mul hc, entryVariance_oneBlock]

theorem measurable_noiseHerm (W : ℕ) (c : ℝ) : Measurable (noiseHerm W c) :=
  (measurable_hermitianScale _).comp
    ((measurable_hermitianReindex _).comp Johansson.measurable_gaussianMatrix)

/-- The `(√c)⁻¹`-scaled Johansson Gaussian matrix with coordinate variance `c/W`, reindexed
by `toFin`, as a PSSS block-GUE law with one block of size `W` (normalization
`GUE_W(1/W)`). Every field is proved. -/
def gueLaw {W : ℕ} (hW : 0 < W) (c : ℝ) (hc : 0 < c) : Law.{0} (oneBlock W) (oneBlock_pos hW) where
  Ω := Johansson.UpperPair W → ℝ × ℝ
  mΩ := inferInstance
  P := Johansson.coordinateMeasure W (coordVar W c)
  probability := Johansson.coordinateMeasure_probability W _
  G z := (noiseHerm W c z).1
  hermitian z := (noiseHerm W c z).2
  measurable_entry x y := (measurable_pi_apply y).comp
    ((measurable_pi_apply x).comp (measurable_subtype_coe.comp (measurable_noiseHerm W c)))
  block_diagonal x y hxy := absurd (Subsingleton.elim _ _) hxy
  upper_independent := by
    have hP := Johansson.coordinateMeasure_probability W (coordVar W c)
    have hU := Johansson.upperEntryMeasure_probability (N := W) (coordVar W c)
    have h0 : iIndepFun (fun (r : Johansson.UpperPair W) (z : Johansson.UpperPair W → ℝ × ℝ) =>
        upperValue (Real.sqrt c)⁻¹ r (z r)) (Johansson.coordinateMeasure W (coordVar W c)) :=
      iIndepFun_pi (fun r => (measurable_upperValue _ r).aemeasurable)
    have h := h0.precomp (upperMap_injective W)
    convert h using 1
    funext q z
    exact noiseHerm_upper W c z q
  diagonal_im_zero x := Filter.Eventually.of_forall (fun z => noiseHerm_diag_im W c z x)
  diagonal_re_law x := diag_hasLaw hW c hc x
  offdiag_components_independent x y hxy hne _ := by
    have hP := Johansson.coordinateMeasure_probability W (coordVar W c)
    exact (indepFun_iff_hasLaw_prodMk_prod (offdiag_re_hasLaw hW c hc x y hxy hne)
      (offdiag_im_hasLaw hW c hc x y hxy hne)).mpr (offdiag_pair_hasLaw hW c hc x y hxy hne)
  offdiag_re_law x y hxy hne _ := offdiag_re_hasLaw hW c hc x y hxy hne
  offdiag_im_law x y hxy hne _ := offdiag_im_hasLaw hW c hc x y hxy hne

end ProjectedGUE

open ProjectedGUE in
/-- PSSS mean count for one deformed block (the single-block input of the projected Wegner
estimate; the PSSS factorial-moment bound at order `r = 1`).

Law: `z ∼ Johansson.coordinateMeasure W (c/W)`, i.e. `(Johansson.gaussianMatrix z).1` has law
`Internal.Contracts.Inputs.gueMatrixLaw W (c/W)` = `GUE_W(c/W)` (diagonal real variance
`c/W`, strict-upper real and imaginary variances `c/(2W)`). Domain: `W > 0`, `c > 0`, every
deterministic Hermitian `F` (no norm bound), every closed `[a,b]` with `a ≤ b`. Observable:
the multiplicity count of eigenvalues of `F + G` in `[a,b]`, as a lintegral.

Uniformity: one constant `C > 0` (the PSSS constant `source.C`) is chosen before `W`, `c`,
`F`, `a`, `b`. Bound: `E N_{[a,b]}(F + G) ≤ C/√c · W · (b-a)`.

Inputs: `PSSS.SourceContract` (`factorialBound`, `factorialIntegrable`),
applied to the one-block law `ProjectedGUE.gueLaw` (all fields proved here) with
deformation `(√c)⁻¹ F` (reindexed) and interval `[(√c)⁻¹a, (√c)⁻¹b]`. -/
theorem gueCoordinate_count_le (source : PSSS.SourceContract.{0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ), 0 < W → ∀ (c : ℝ), 0 < c →
      ∀ (F : Matrix (Fin W) (Fin W) ℂ) (hF : F.IsHermitian) (a b : ℝ), a ≤ b →
        ∫⁻ z, (PSSS.eigenCount
            ⟨F + (Johansson.gaussianMatrix z).1,
              hF.add (Johansson.gaussianMatrix z).2⟩ (Set.Icc a b) : ENNReal)
            ∂(Johansson.coordinateMeasure W (Real.toNNReal (c / W))) ≤
          ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * (b - a)) := by
  refine ⟨source.C, source.C_pos, ?_⟩
  intro W hW c hc F hF a b hab
  set s : ℝ := (Real.sqrt c)⁻¹ with hs_def
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr hc)
  let M := gueLaw hW c hc
  let D : PSSS.HermitianMatrix (Index (oneBlock W)) := hermitianReindex (toFin W).symm ⟨F, hF⟩
  let A₀ := hermitianScale s D
  let I : Set ℝ := Icc (s * a) (s * b)
  have hcount : ∀ z : Johansson.UpperPair W → ℝ × ℝ,
      eigenCount ⟨F + (Johansson.gaussianMatrix z).1, hF.add (Johansson.gaussianMatrix z).2⟩
        (Icc a b) = intervalCount M A₀ I z := by
    intro z
    have h1 : intervalCount M A₀ I z = sumCount (Icc a b)
        (D, hermitianReindex (toFin W).symm (Johansson.gaussianMatrix z)) :=
      sumCount_scale s hs a b (D, hermitianReindex (toFin W).symm (Johansson.gaussianMatrix z))
    have h2 := nativeEigenCount_hermitianReindex (toFin W).symm
      (⟨F + (Johansson.gaussianMatrix z).1, hF.add (Johansson.gaussianMatrix z).2⟩ :
        PSSS.HermitianMatrix (Fin W)) (Icc a b)
    calc eigenCount ⟨F + (Johansson.gaussianMatrix z).1, hF.add (Johansson.gaussianMatrix z).2⟩
          (Icc a b)
        = eigenCount (hermitianReindex (toFin W).symm
            ⟨F + (Johansson.gaussianMatrix z).1, hF.add (Johansson.gaussianMatrix z).2⟩)
          (Icc a b) := h2.symm
      _ = sumCount (Icc a b)
          (D, hermitianReindex (toFin W).symm (Johansson.gaussianMatrix z)) := rfl
      _ = intervalCount M A₀ I z := h1.symm
  have hint := source.factorialIntegrable (oneBlock_pos hW) M A₀ (s * a) (s * b) 1
  have hb := source.factorialBound (oneBlock_pos hW) M A₀ (s * a) (s * b)
    (mul_le_mul_of_nonneg_left hab hs.le) 1 le_rfl
  unfold FactorialMomentBound at hb
  have hlhs : (∫⁻ z, (eigenCount ⟨F + (Johansson.gaussianMatrix z).1,
        hF.add (Johansson.gaussianMatrix z).2⟩ (Icc a b) : ENNReal)
        ∂(Johansson.coordinateMeasure W (Real.toNNReal (c / W)))) =
      ENNReal.ofReal (∫ z, factorialCount (intervalCount M A₀ I) 1 z ∂M.P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => by simp [factorialCount])]
    apply lintegral_congr
    intro z
    rw [hcount z]
    simp [factorialCount]
    rfl
  rw [hlhs]
  apply ENNReal.ofReal_le_ofReal
  refine hb.trans (le_of_eq ?_)
  rw [pow_one, card_index, hs_def]
  ring

end BlockBand.Wegner
