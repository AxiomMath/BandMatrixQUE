module

public import BlockBand.Coarea.ContractClauses

/-!
# Scalar-part decomposition of the fresh pair Gaussian for the pair pole exclusion lemma

* `scalarShiftLaw ι t v`: the law of `G⁰ + ζ I` with `G⁰ ~ GUE_ι(t).map tracelessPart` and an
  independent `ζ ~ N(0, v)`.
* `integral_exp_gueTestPairing_scalarShiftLaw`: for `v = t/|ι|` it has exactly the GUE
  characteristic function against every test pairing (`Σ (D_a - D̄)² + (ΣD)²/d = Σ D_a²`).
* `assemble_scalarShiftLaw_eq`: for every pair splitting law `Pω` (any
  `0 < s` (no upper bound needed here), `t = s/(2W)`, `v = s/(2W)²`),
  `(Pω ⊗ scalarShiftLaw).map assemble = model.law`. Proof: the reassembled characteristic
  function factorises into a `Pω` factor and a pair factor; the pair factor equals that of
  `GUE_S(t)`, so the characteristic function is the physical one, and
  `physicalGaussianRingLaw_unique` applies (the law is Hermitian-supported because `Pω`-a.e.
  the exterior and pair blocks are Hermitian).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.PoleExclusion

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Model.Construction BlockBand.QUE.Fourier
  BlockBand.Coarea BlockBand.Coarea.GUELaw BlockBand.Coarea.ContractClauses
open scoped ENNReal NNReal ComplexConjugate

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The law of `G⁰ + ζ I`, `G⁰ ~ GUE_ι(t).map tracelessPart`, `ζ ~ N(0, v)` independent. -/
def scalarShiftLaw (ι : Type*) [Fintype ι] [DecidableEq ι] (t v : ℝ≥0) :
    Measure (Matrix ι ι ℂ) :=
  (((gueMeasure ι t).map tracelessPart).prod (gaussianReal 0 v)).map
    (fun y => y.1 + (y.2 : ℂ) • (1 : Matrix ι ι ℂ))

theorem continuous_tracelessPart : Continuous (tracelessPart (ι := ι)) := by
  unfold tracelessPart
  exact continuous_id.sub ((continuous_const.mul (continuous_id.matrix_trace)).smul
    continuous_const)

theorem measurable_tracelessPart : Measurable (tracelessPart (ι := ι)) :=
  continuous_tracelessPart.measurable

theorem measurable_scalarAdd :
    Measurable (fun y : Matrix ι ι ℂ × ℝ => y.1 + (y.2 : ℂ) • (1 : Matrix ι ι ℂ)) :=
  (continuous_fst.add ((Complex.continuous_ofReal.comp continuous_snd).smul
    continuous_const)).measurable

instance isProbabilityMeasure_scalarShiftLaw (t v : ℝ≥0) :
    IsProbabilityMeasure (scalarShiftLaw ι t v) := by
  unfold scalarShiftLaw
  have : IsProbabilityMeasure ((gueMeasure ι t).map tracelessPart) :=
    (Measure.isProbabilityMeasure_map_iff measurable_tracelessPart.aemeasurable).2 inferInstance
  exact (Measure.isProbabilityMeasure_map_iff measurable_scalarAdd.aemeasurable).2 inferInstance

theorem gueTestPairing_add_scalar (κ : ι → ℕ) (D : ι → ℝ) (U V : ι → ι → ℝ)
    (G : Matrix ι ι ℂ) (ζ : ℝ) :
    gueTestPairing κ D U V (G + (ζ : ℂ) • (1 : Matrix ι ι ℂ)) =
      gueTestPairing κ D U V G + ζ * ∑ a, D a := by
  unfold gueTestPairing
  have hoff : ∀ a b : ι, (if κ a < κ b then U a b * ((G + (ζ : ℂ) • (1 : Matrix ι ι ℂ)) a b).re +
      V a b * ((G + (ζ : ℂ) • (1 : Matrix ι ι ℂ)) a b).im else 0) =
      if κ a < κ b then U a b * (G a b).re + V a b * (G a b).im else 0 := by
    intro a b
    split_ifs with h
    · have hab : a ≠ b := fun e => by subst e; exact lt_irrefl _ h
      simp [one_apply_ne hab]
    · rfl
  simp_rw [hoff]
  simp only [Matrix.add_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one,
    Complex.add_re, Complex.ofReal_re, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [show ∑ x, ζ * D x = ∑ x, D x * ζ from Finset.sum_congr rfl fun _ _ => mul_comm _ _]
  ring

theorem gueTestPairing_tracelessPart (κ : ι → ℕ) (D : ι → ℝ) (U V : ι → ι → ℝ)
    (G : Matrix ι ι ℂ) :
    gueTestPairing κ D U V (tracelessPart G) =
      gueTestPairing κ (fun a => D a - (∑ b, D b) / Fintype.card ι) U V G := by
  unfold gueTestPairing tracelessPart
  have hoff : ∀ a b : ι, (if κ a < κ b then
      U a b * ((G - (((Fintype.card ι : ℂ))⁻¹ * G.trace) • (1 : Matrix ι ι ℂ)) a b).re +
      V a b * ((G - (((Fintype.card ι : ℂ))⁻¹ * G.trace) • (1 : Matrix ι ι ℂ)) a b).im else 0) =
      if κ a < κ b then U a b * (G a b).re + V a b * (G a b).im else 0 := by
    intro a b
    split_ifs with h
    · have hab : a ≠ b := fun e => by subst e; exact lt_irrefl _ h
      simp [one_apply_ne hab]
    · rfl
  simp_rw [hoff]
  congr 1
  have hc : (((Fintype.card ι : ℂ))⁻¹ * G.trace).re =
      (Fintype.card ι : ℝ)⁻¹ * ∑ b, (G b b).re := by
    rw [show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) by push_cast; rfl,
      Complex.re_ofReal_mul, Matrix.trace, Complex.re_sum]
    rfl
  simp only [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one,
    Complex.sub_re, hc]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
theorem sum_sub_mean_sq (D : ι → ℝ) (hd : (Fintype.card ι : ℝ) ≠ 0) :
    ∑ a, (D a - (∑ b, D b) / Fintype.card ι) ^ 2 =
      ∑ a, D a ^ 2 - (∑ b, D b) ^ 2 / Fintype.card ι := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  field_simp
  ring

/-- `G⁰ + ζ I` has the GUE characteristic function when `v = t/|ι|`. -/
theorem integral_exp_gueTestPairing_scalarShiftLaw (κ : ι → ℕ) (hκ : Function.Injective κ)
    (t v : ℝ≥0) (hd : (Fintype.card ι : ℝ) ≠ 0) (hv : (v : ℝ) = (t : ℝ) / Fintype.card ι)
    (D : ι → ℝ) (U V : ι → ι → ℝ) :
    ∫ G, Complex.exp (Complex.I * (gueTestPairing κ D U V G : ℂ)) ∂scalarShiftLaw ι t v =
      Complex.exp (-(gueTestVariance κ t D U V : ℂ) / 2) := by
  have hmeasP : ∀ D' : ι → ℝ, Measurable fun G : Matrix ι ι ℂ =>
      Complex.exp (Complex.I * (gueTestPairing κ D' U V G : ℂ)) := by
    intro D'
    unfold gueTestPairing
    fun_prop
  unfold scalarShiftLaw
  rw [integral_map measurable_scalarAdd.aemeasurable (hmeasP D).aestronglyMeasurable]
  have hpt : ∀ y : Matrix ι ι ℂ × ℝ,
      Complex.exp (Complex.I * (gueTestPairing κ D U V (y.1 + (y.2 : ℂ) • 1) : ℂ)) =
        Complex.exp (Complex.I * (gueTestPairing κ D U V y.1 : ℂ)) *
          Complex.exp (((∑ a, D a : ℝ) : ℂ) * (y.2 : ℂ) * Complex.I) := by
    intro y
    rw [gueTestPairing_add_scalar, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_prod_mul (fun G : Matrix ι ι ℂ =>
      Complex.exp (Complex.I * (gueTestPairing κ D U V G : ℂ)))
    (fun ζ : ℝ => Complex.exp (((∑ a, D a : ℝ) : ℂ) * (ζ : ℂ) * Complex.I))]
  rw [integral_map measurable_tracelessPart.aemeasurable (hmeasP D).aestronglyMeasurable]
  simp_rw [gueTestPairing_tracelessPart]
  rw [integral_exp_gueTestPairing κ hκ, ← charFun_apply_real, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  unfold gueTestVariance
  rw [sum_sub_mean_sq D hd, hv]
  push_cast
  field_simp
  ring

end Generic

section Physical

variable (p : Parameters) (i : ZMod p.n)

theorem exteriorBlock_assemble (ω : SplitState p i) (G : PairMatrix p i) :
    exteriorBlock p i (assemble p i ω G) = ω.1 := by
  ext x y
  simp [exteriorBlock, assemble, x.2, y.2]

theorem pairBlock_assemble (ω : SplitState p i) (G : PairMatrix p i) :
    pairBlock p i (assemble p i ω G) = ω.2.2 + G := by
  ext x y
  simp [pairBlock, assemble, x.2, y.2]

theorem exteriorBlock_isHermitian {H : p.SiteMatrix} (hH : H.IsHermitian) :
    (exteriorBlock p i H).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  exact hH.apply _ _

theorem pairBlock_isHermitian {H : p.SiteMatrix} (hH : H.IsHermitian) :
    (pairBlock p i H).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  exact hH.apply _ _

theorem blocks_isHermitian_of_assemble (ω : SplitState p i) (G : PairMatrix p i)
    (hH : (assemble p i ω G).IsHermitian) (hG : G.IsHermitian) :
    ω.1.IsHermitian ∧ ω.2.2.IsHermitian := by
  refine ⟨?_, ?_⟩
  · have := exteriorBlock_isHermitian p i hH
    rwa [exteriorBlock_assemble] at this
  · have h := pairBlock_isHermitian p i hH
    rw [pairBlock_assemble] at h
    have : ω.2.2 = (ω.2.2 + G) - G := by abel
    rw [this]
    exact h.sub hG

variable {p i}

/-- Every splitting law is a probability measure. -/
theorem isProbabilityMeasure_of_splitting {model : p.GaussianRingModel} {s : ℝ}
    {Pω : Measure (SplitState p i)} (h : IsPairSplitting p i model s Pω) :
    IsProbabilityMeasure Pω := by
  constructor
  have h1 := congrArg (fun μ : Measure p.SiteMatrix => μ Set.univ) h
  simp only [measure_univ] at h1
  rw [Measure.map_apply (measurable_assemble p i) MeasurableSet.univ, Set.preimage_univ,
    Measure.prod_apply MeasurableSet.univ] at h1
  simpa using h1

/-- `Pω`-almost surely the exterior and pair blocks of a splitting law are Hermitian. -/
theorem ae_blocks_isHermitian {model : p.GaussianRingModel} {s : ℝ}
    {Pω : Measure (SplitState p i)} (h : IsPairSplitting p i model s Pω) :
    ∀ᵐ ω ∂Pω, ω.1.IsHermitian ∧ ω.2.2.IsHermitian := by
  have : IsProbabilityMeasure Pω := isProbabilityMeasure_of_splitting h
  have hH : ∀ᵐ x ∂(Pω.prod (gueMeasure (PairSite p i) (pairTime p s))),
      (assemble p i x.1 x.2).IsHermitian := by
    refine ae_of_ae_map (measurable_assemble p i).aemeasurable ?_
    rw [h]; exact model.isPhysical.1
  have hG := (Measure.quasiMeasurePreserving_snd
    (μ := Pω) (ν := gueMeasure (PairSite p i) (pairTime p s))).ae
      (ae_isHermitian_gueMeasure (ι := PairSite p i) (pairTime p s))
  have hQ : ∀ᵐ x ∂(Pω.prod (gueMeasure (PairSite p i) (pairTime p s))),
      x.1.1.IsHermitian ∧ x.1.2.2.IsHermitian := by
    filter_upwards [hH, hG] with x hx hx'
    exact blocks_isHermitian_of_assemble p i x.1 x.2 hx hx'
  filter_upwards [Measure.ae_ae_of_ae_prod hQ] with ω hω
  exact hω.exists.choose_spec

theorem tracelessPart_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) : (tracelessPart G).IsHermitian := by
  unfold tracelessPart
  refine hG.sub (isHermitian_one.smul ?_)
  have htr : star G.trace = G.trace := by
    rw [← Matrix.trace_conjTranspose, hG.eq]
  change star ((((Fintype.card ι : ℂ))⁻¹ * G.trace)) = _
  rw [star_mul', htr]
  congr 1
  simp

theorem ae_isHermitian_scalarShiftLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (t v : ℝ≥0) :
    ∀ᵐ G ∂scalarShiftLaw ι t v, G.IsHermitian := by
  unfold scalarShiftLaw
  rw [ae_map_iff measurable_scalarAdd.aemeasurable measurableSet_isHermitian]
  have h0 : ∀ᵐ G ∂(gueMeasure ι t).map tracelessPart, G.IsHermitian := by
    rw [ae_map_iff measurable_tracelessPart.aemeasurable measurableSet_isHermitian]
    filter_upwards [ae_isHermitian_gueMeasure (ι := ι) t] with G hG
    exact tracelessPart_isHermitian hG
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := (gueMeasure ι t).map tracelessPart)
    (ν := gaussianReal 0 v)).ae h0] with y hy
  exact hy.add (isHermitian_one.smul (Complex.conj_ofReal y.2))

/-- The reassembled characteristic function depends on the pair law only through its test
characteristic functions. -/
theorem charFun_assemble_congr (Pω : Measure (SplitState p i)) [IsProbabilityMeasure Pω]
    (μ₁ μ₂ : Measure (PairMatrix p i)) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : ∀ (D : PairSite p i → ℝ) (U V : PairSite p i → PairSite p i → ℝ),
      ∫ G, Complex.exp (Complex.I * (gueTestPairing (fun a => p.siteIndex a.1) D U V G : ℂ)) ∂μ₁ =
        ∫ G, Complex.exp (Complex.I * (gueTestPairing (fun a => p.siteIndex a.1) D U V G : ℂ)) ∂μ₂)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    ∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))
        ∂(Pω.prod μ₁).map (fun x => assemble p i x.1 x.2) =
      ∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))
        ∂(Pω.prod μ₂).map (fun x => assemble p i x.1 x.2) := by
  rw [integral_map (measurable_assemble p i).aemeasurable
      (measurable_exp_pairing p d u v).aestronglyMeasurable,
    integral_map (measurable_assemble p i).aemeasurable
      (measurable_exp_pairing p d u v).aestronglyMeasurable]
  have hpt : ∀ x : SplitState p i × PairMatrix p i,
      Complex.exp (Complex.I * (p.coordinatePairing d u v (assemble p i x.1 x.2) : ℂ)) =
        Complex.exp (Complex.I * (p.coordinatePairing d u v (assemble p i x.1 0) : ℂ)) *
          Complex.exp (Complex.I * (gueTestPairing (fun a => p.siteIndex a.1) (fun a => d a.1)
            (fun a b => u a.1 b.1) (fun a b => v a.1 b.1) x.2 : ℂ)) := by
    intro x
    rw [assemble_eq_add, coordinatePairing_add, coordinatePairing_assemble_zero, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_prod_mul (fun ω : SplitState p i =>
      Complex.exp (Complex.I * (p.coordinatePairing d u v (assemble p i ω 0) : ℂ)))
    (fun G : PairMatrix p i => Complex.exp (Complex.I * (gueTestPairing
      (fun a => p.siteIndex a.1) (fun a => d a.1) (fun a b => u a.1 b.1) (fun a b => v a.1 b.1) G : ℂ))),
    integral_prod_mul (fun ω : SplitState p i =>
      Complex.exp (Complex.I * (p.coordinatePairing d u v (assemble p i ω 0) : ℂ)))
    (fun G : PairMatrix p i => Complex.exp (Complex.I * (gueTestPairing
      (fun a => p.siteIndex a.1) (fun a => d a.1) (fun a b => u a.1 b.1) (fun a b => v a.1 b.1) G : ℂ))),
    h]

/-- **Scalar-part decomposition** of the splitting: for every splitting law `Pω`, the fresh
pair Gaussian may be replaced by `G⁰ + ζ I` with `G⁰ ~ GUE_S(t).map tracelessPart` and an
independent `ζ ~ N(0, s/(2W)²)`. -/
theorem assemble_scalarShiftLaw_eq {model : p.GaussianRingModel} {s : ℝ} (hs : 0 < s)
    {Pω : Measure (SplitState p i)} (hsplit : IsPairSplitting p i model s Pω) :
    (Pω.prod (scalarShiftLaw (PairSite p i) (pairTime p s)
        (Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2)))).map (fun x => assemble p i x.1 x.2) =
      (model.law : Measure p.SiteMatrix) := by
  have : IsProbabilityMeasure Pω := isProbabilityMeasure_of_splitting hsplit
  set ν := scalarShiftLaw (PairSite p i) (pairTime p s) (Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2))
  have hW : (0 : ℝ) < 2 * (p.W : ℝ) := by have := p.W_pos; positivity
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * (p.W : ℝ) := by
    rw [card_pairSite]; push_cast; ring
  have hd : (Fintype.card (PairSite p i) : ℝ) ≠ 0 := by rw [hcard]; exact hW.ne'
  have hv : ((Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2) : ℝ≥0) : ℝ) =
      (pairTime p s : ℝ) / Fintype.card (PairSite p i) := by
    rw [pairTime, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity), hcard]
    field_simp
  have hκ : Function.Injective (fun a : PairSite p i => p.siteIndex a.1) :=
    p.siteIndex_injective.comp Subtype.val_injective
  have hchar : ∀ (D : PairSite p i → ℝ) (U V : PairSite p i → PairSite p i → ℝ),
      ∫ G, Complex.exp (Complex.I * (gueTestPairing (fun a => p.siteIndex a.1) D U V G : ℂ)) ∂ν =
        ∫ G, Complex.exp (Complex.I * (gueTestPairing (fun a => p.siteIndex a.1) D U V G : ℂ))
          ∂gueMeasure (PairSite p i) (pairTime p s) := by
    intro D U V
    rw [integral_exp_gueTestPairing_scalarShiftLaw _ hκ _ _ hd hv, integral_exp_gueTestPairing _ hκ]
  set L : Measure p.SiteMatrix :=
    (Pω.prod ν).map (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) with hL
  have hprob : IsProbabilityMeasure L :=
    (Measure.isProbabilityMeasure_map_iff (measurable_assemble p i).aemeasurable).2 inferInstance
  have hherm : ∀ᵐ H ∂L, H.IsHermitian := by
    rw [ae_map_iff (measurable_assemble p i).aemeasurable measurableSet_isHermitian]
    have hω := (Measure.quasiMeasurePreserving_fst (μ := Pω) (ν := ν)).ae
      (ae_blocks_isHermitian hsplit)
    have hG := (Measure.quasiMeasurePreserving_snd (μ := Pω) (ν := ν)).ae
      (ae_isHermitian_scalarShiftLaw (ι := PairSite p i) _ _)
    filter_upwards [hω, hG] with x hx hx'
    exact assemble_isHermitian p i x.1 x.2 hx.1 hx.2 hx'
  have hcf : ∀ (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ),
      ∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ)) ∂L =
        Complex.exp (-(p.coordinateVariance d u v : ℂ) / 2) := by
    intro d u v
    rw [hL, charFun_assemble_congr Pω ν (gueMeasure (PairSite p i) (pairTime p s)) hchar, hsplit]
    exact model.isPhysical.2 d u v
  let PL : ProbabilityMeasure p.SiteMatrix := ⟨L, hprob⟩
  let model' : p.GaussianRingModel := ⟨PL, ⟨hherm, hcf⟩⟩
  have h := BlockBand.Parameters.physicalGaussianRingLaw_unique model' model
  exact congrArg (fun P : ProbabilityMeasure p.SiteMatrix => (P : Measure p.SiteMatrix)) h

/-- The scalar-shift map `((ω, G⁰), ζ) ↦ assemble ω (G⁰ + ζ I)`. -/
def shiftAssemble (w : (SplitState p i × PairMatrix p i) × ℝ) : p.SiteMatrix :=
  assemble p i w.1.1 (w.1.2 + (w.2 : ℂ) • (1 : PairMatrix p i))

theorem measurable_shiftAssemble : Measurable (shiftAssemble (p := p) (i := i)) := by
  have h : Measurable (fun w : (SplitState p i × PairMatrix p i) × ℝ =>
      (w.1.1, w.1.2 + (w.2 : ℂ) • (1 : PairMatrix p i))) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_scalarAdd.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact (measurable_assemble p i).comp h

/-- `model.law` as the image of `(Pω ⊗ GUE.map tracelessPart) ⊗ N(0, s/(2W)²)`. -/
theorem law_eq_map_shiftAssemble {model : p.GaussianRingModel} {s : ℝ} (hs : 0 < s)
    {Pω : Measure (SplitState p i)} (hsplit : IsPairSplitting p i model s Pω) :
    (model.law : Measure p.SiteMatrix) =
      ((Pω.prod ((gueMeasure (PairSite p i) (pairTime p s)).map tracelessPart)).prod
        (gaussianReal 0 (Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2)))).map shiftAssemble := by
  have : IsProbabilityMeasure Pω := isProbabilityMeasure_of_splitting hsplit
  set κ := (gueMeasure (PairSite p i) (pairTime p s)).map tracelessPart
  set N := gaussianReal 0 (Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2))
  have : IsProbabilityMeasure κ :=
    (Measure.isProbabilityMeasure_map_iff measurable_tracelessPart.aemeasurable).2 inferInstance
  rw [← assemble_scalarShiftLaw_eq hs hsplit]
  unfold scalarShiftLaw
  rw [← Measure.map_id (μ := Pω)]
  rw [Measure.map_prod_map Pω (κ.prod N) measurable_id measurable_scalarAdd, Measure.map_id,
    Measure.map_map (measurable_assemble p i) (measurable_id.prodMap measurable_scalarAdd),
    ← (measurePreserving_prodAssoc Pω κ N).map_eq,
    Measure.map_map ((measurable_assemble p i).comp (measurable_id.prodMap measurable_scalarAdd))
      MeasurableEquiv.prodAssoc.measurable]
  rfl

/-- Almost-sure properties of `model.law` hold for almost every `(ω, G⁰)` and
`N(0, s/(2W)²)`-almost every scalar part `ζ`. -/
theorem ae_ae_shift_of_ae {model : p.GaussianRingModel} {s : ℝ} (hs : 0 < s)
    {Pω : Measure (SplitState p i)} (hsplit : IsPairSplitting p i model s Pω)
    {Q : p.SiteMatrix → Prop} (hQ : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), Q H) :
    ∀ᵐ x ∂(Pω.prod ((gueMeasure (PairSite p i) (pairTime p s)).map tracelessPart)),
      ∀ᵐ (ζ : ℝ) ∂gaussianReal 0 (Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2)),
        Q (assemble p i x.1 (x.2 + (ζ : ℂ) • (1 : PairMatrix p i))) := by
  rw [law_eq_map_shiftAssemble hs hsplit] at hQ
  exact Measure.ae_ae_of_ae_prod (ae_of_ae_map measurable_shiftAssemble.aemeasurable hQ)

/-- Integrals against `model.law` as iterated `(ω, G⁰)`- and `ζ`-integrals. -/
theorem lintegral_law_eq {model : p.GaussianRingModel} {s : ℝ} (hs : 0 < s)
    {Pω : Measure (SplitState p i)} (hsplit : IsPairSplitting p i model s Pω)
    {Φ : p.SiteMatrix → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ H, Φ H ∂(model.law : Measure p.SiteMatrix) =
      ∫⁻ x, ∫⁻ (ζ : ℝ), Φ (assemble p i x.1 (x.2 + (ζ : ℂ) • (1 : PairMatrix p i)))
        ∂gaussianReal 0 (Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2))
        ∂(Pω.prod ((gueMeasure (PairSite p i) (pairTime p s)).map tracelessPart)) := by
  rw [law_eq_map_shiftAssemble hs hsplit, lintegral_map hΦ measurable_shiftAssemble,
    lintegral_prod (fun w => Φ (shiftAssemble w)) (hΦ.comp measurable_shiftAssemble).aemeasurable]
  rfl

end Physical

end BlockBand.Coarea.PoleExclusion
