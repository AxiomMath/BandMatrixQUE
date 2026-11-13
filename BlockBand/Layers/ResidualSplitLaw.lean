module

public import BlockBand.Layers.ResidualPair

/-!
# The splitting law of the residual pair (`ResidualSplitLaw`)

The law identification behind the pair splitting, as used in Step 5 of the proof of the
matched-traces theorem. Law: the exact physical law `model.law` (`IsPhysicalGaussianRingLaw`),
every admissible `p` (`n ≥ 4`), adjacent pair `S = {i, i+1}`, and `0 < s < 2 min(c, b)`,
`t = pairTime s = s/(2W)`.

* `rsl_charFun_gue`: for every finite index type, `GUE(t)` has characteristic function
  `exp(-t Q(α, β)/2)` against the full real-linear test `Σ α Re A + β Im A`; in particular it never
  vanishes.
* `rsl_measure_ext`: finite measures on complex matrices are determined by these tests.
* `rsl_pair_add` (variances add): `V(rpLaw s) + GUE_{2W}(s/(2W))` has the law of `V(rpLaw 0)`, i.e.
  `(c - s/2)/W + s/(2W) = c/W` on the diagonal blocks and `(b - s/2)/W + s/(2W) = b/W` on the bond.
* `rsl_law_eq_split0`: `model.law` is the image of `rpLaw 0 ⊗ pathLaw (n-2)` under
  `rpSplitAssemble` followed by reassembly with `G = 0` (rearrangement of `rngLaw`).
* `rsl_isPairSplitting`: `Q = (rpLaw s ⊗ pathLaw (n-2)).map rpSplitAssemble` satisfies
  `IsPairSplitting`.
* `rsl_splitting_unique` (deconvolution): two laws satisfying `IsPairSplitting` at the same `s`
  coincide, because the characteristic function of the added `GUE_{2W}(t)` never vanishes.
* `residualSplitLaw_holds : ResidualSplitLaw`, with no hypothesis.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample PairSite ExteriorSite PairMatrix
  SplitState IsPairSplitting assemble pairTime exteriorBlock couplingBlock pairBlock)
open BlockBand.SourceProcess (commonCircularIncrementLaw circularBrownianCoordinates)
open scoped ENNReal NNReal ComplexConjugate

/-!
## 1. Real-linear tests of complex matrices
-/

section Tests

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The general real-linear test `Σ_{x,y} (α_xy Re M_xy + β_xy Im M_xy)`. -/
def rslTest (α β : ι → κ → ℝ) (M : Matrix ι κ ℂ) : ℝ :=
  ∑ x, ∑ y, (α x y * (M x y).re + β x y * (M x y).im)

theorem rsl_measurable_test (α β : ι → κ → ℝ) : Measurable (rslTest α β) := by
  unfold rslTest
  refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_
  exact (measurable_const.mul (Complex.measurable_re.comp
      ((measurable_pi_apply y).comp (measurable_pi_apply x)))).add
    (measurable_const.mul (Complex.measurable_im.comp
      ((measurable_pi_apply y).comp (measurable_pi_apply x))))

theorem rsl_measurable_expTest (α β : ι → κ → ℝ) :
    Measurable (fun M : Matrix ι κ ℂ => Complex.exp (Complex.I * (rslTest α β M : ℂ))) := by
  have := rsl_measurable_test α β
  fun_prop

theorem rslTest_add (α β : ι → κ → ℝ) (M N : Matrix ι κ ℂ) :
    rslTest α β (M + N) = rslTest α β M + rslTest α β N := by
  unfold rslTest
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.add_apply, Complex.add_re, Complex.add_im]
  ring

/-- Real and imaginary parts of all entries. -/
def rslExtract (M : Matrix ι κ ℂ) : ι × κ × Fin 2 → ℝ :=
  fun k => if k.2.2 = 0 then (M k.1 k.2.1).re else (M k.1 k.2.1).im

omit [Fintype ι] [Fintype κ] in
theorem rsl_measurable_extract : Measurable (rslExtract (ι := ι) (κ := κ)) := by
  refine measurable_pi_iff.mpr fun k => ?_
  unfold rslExtract
  split_ifs
  · exact Complex.measurable_re.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
  · exact Complex.measurable_im.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

omit [Fintype ι] [Fintype κ] in
theorem rsl_assemble_extract (M : Matrix ι κ ℂ) : ginibreAssemble (rslExtract M) = M := by
  ext x y
  apply Complex.ext <;> simp [ginibreAssemble, rslExtract]

theorem rsl_sum_extract (q : ι × κ × Fin 2 → ℝ) (M : Matrix ι κ ℂ) :
    ∑ k, q k * rslExtract M k = rslTest (fun x y => q (x, y, 0)) (fun x y => q (x, y, 1)) M := by
  unfold rslTest
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [rslExtract, Fin.sum_univ_two]

/-- **Uniqueness from characteristic functions**: finite measures on complex matrices with the
same characteristic function against every real-linear test coincide. -/
theorem rsl_measure_ext {μ ν : Measure (Matrix ι κ ℂ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ α β : ι → κ → ℝ,
      ∫ M, Complex.exp (Complex.I * (rslTest α β M : ℂ)) ∂μ =
        ∫ M, Complex.exp (Complex.I * (rslTest α β M : ℂ)) ∂ν) : μ = ν := by
  have hE := rsl_measurable_extract (ι := ι) (κ := κ)
  have key : μ.map rslExtract = ν.map rslExtract := by
    apply BlockBand.Parameters.finiteReal_measure_eq_of_characteristic
    intro q
    have hc : Continuous (fun z : ι × κ × Fin 2 → ℝ =>
        Complex.exp (Complex.I * ((∑ i, q i * z i : ℝ) : ℂ))) := by fun_prop
    rw [integral_map hE.aemeasurable hc.aestronglyMeasurable,
      integral_map hE.aemeasurable hc.aestronglyMeasurable]
    simp only [rsl_sum_extract]
    exact h _ _
  have hid : ∀ ρ : Measure (Matrix ι κ ℂ), (ρ.map rslExtract).map ginibreAssemble = ρ := by
    intro ρ
    rw [Measure.map_map measurable_ginibreAssemble hE]
    have : (ginibreAssemble ∘ rslExtract : Matrix ι κ ℂ → Matrix ι κ ℂ) = id :=
      funext rsl_assemble_extract
    rw [this, Measure.map_id]
  rw [← hid μ, ← hid ν, key]

end Tests

/-!
## 2. The characteristic function of `GUE(t)` on an arbitrary finite index type
-/

section Gue

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem rsl_measurable_cbc :
    Measurable (circularBrownianCoordinates (ι := ι)) := by
  apply Measurable.of_eval
  intro u
  unfold circularBrownianCoordinates
  fun_prop

omit [Fintype ι] in
theorem rsl_measurable_gueSample (t : ℝ≥0) : Measurable (gueSample (ι := ι) t) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [gueSample, Matrix.of_apply]
  have hc : Measurable (fun z : ℂ => conj z) := Complex.continuous_conj.measurable
  fun_prop

theorem rsl_gueMeasure_eq_map (t : ℝ≥0) :
    gueMeasure ι t = (Measure.pi fun _ : (ι × ι) × Fin 2 => gaussianReal 0 (1 : ℝ≥0)).map
      (fun r => gueSample t (circularBrownianCoordinates r)) := by
  rw [gueMeasure, commonCircularIncrementLaw,
    Measure.map_map (rsl_measurable_gueSample t) rsl_measurable_cbc]
  rfl

instance rsl_isProbabilityMeasure_gue (t : ℝ≥0) : IsProbabilityMeasure (gueMeasure ι t) := by
  rw [rsl_gueMeasure_eq_map]
  infer_instance

/-- The `GUE` quadratic form `Q(α, β) = ¼ Σ_{x,y} ((α_xy + α_yx)² + (β_xy - β_yx)²)`. -/
def rslQ (α β : ι → ι → ℝ) : ℝ :=
  ∑ x, ∑ y, ((α x y + α y x) ^ 2 + (β x y - β y x) ^ 2) / 4

/-- The scale `√(t/2)/√2`. -/
def rslScale (t : ℝ≥0) : ℝ := Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2

theorem rsl_scale_sq (t : ℝ≥0) : rslScale t ^ 2 = (t : ℝ) / 4 := by
  rw [rslScale, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
  ring

/-- Coefficients of the test on the real circular coordinates. -/
def rslCoef (t : ℝ≥0) (α β : ι → ι → ℝ) (k : (ι × ι) × Fin 2) : ℝ :=
  if k.2 = 0 then rslScale t * (α k.1.1 k.1.2 + α k.1.2 k.1.1)
  else rslScale t * (β k.1.1 k.1.2 - β k.1.2 k.1.1)

omit [Fintype ι] in
theorem rsl_gueSample_re (t : ℝ≥0) (r : (ι × ι) × Fin 2 → ℝ) (a b : ι) :
    (gueSample t (circularBrownianCoordinates r) a b).re =
      rslScale t * (r ((a, b), 0) + r ((b, a), 0)) := by
  simp [gueSample, circularBrownianCoordinates, Complex.div_ofReal_re, rslScale]
  ring

omit [Fintype ι] in
theorem rsl_gueSample_im (t : ℝ≥0) (r : (ι × ι) × Fin 2 → ℝ) (a b : ι) :
    (gueSample t (circularBrownianCoordinates r) a b).im =
      rslScale t * (r ((a, b), 1) - r ((b, a), 1)) := by
  simp [gueSample, circularBrownianCoordinates, Complex.div_ofReal_im, rslScale]
  ring

theorem rsl_sum_coord (f : (ι × ι) × Fin 2 → ℝ) :
    ∑ k, f k = ∑ a, ∑ b, (f ((a, b), 0) + f ((a, b), 1)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

theorem rsl_sum_swap (F G : ι → ι → ℝ) :
    ∑ x, ∑ y, (F x y + G y x) = ∑ x, ∑ y, (F x y + G x y) := by
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y => G y x)]

theorem rsl_test_gueSample (t : ℝ≥0) (α β : ι → ι → ℝ) (r : (ι × ι) × Fin 2 → ℝ) :
    rslTest α β (gueSample t (circularBrownianCoordinates r)) = ∑ k, rslCoef t α β k * r k := by
  rw [rsl_sum_coord]
  unfold rslTest
  simp only [rsl_gueSample_re, rsl_gueSample_im]
  have h := rsl_sum_swap (fun x y => rslScale t * (α x y * r ((x, y), 0) + β x y * r ((x, y), 1)))
    (fun y x => rslScale t * (α x y * r ((y, x), 0) - β x y * r ((y, x), 1)))
  convert h using 3 with x _ y _
  · ring
  · simp [rslCoef]
    ring

theorem rsl_coef_sq (t : ℝ≥0) (α β : ι → ι → ℝ) :
    ∑ k, ((fun _ => (1 : ℝ≥0)) k : ℝ) * rslCoef t α β k ^ 2 = (t : ℝ) * rslQ α β := by
  rw [rsl_sum_coord]
  unfold rslQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hs := rsl_scale_sq t
  simp only [rslCoef, NNReal.coe_one, one_mul]
  simp only [show ((1 : Fin 2) = 0) ↔ False by decide, ite_true, ite_false]
  rw [mul_pow, mul_pow, hs]
  ring

/-- **Characteristic function of `GUE_ι(t)`** against every real-linear test. -/
theorem rsl_charFun_gue (t : ℝ≥0) (α β : ι → ι → ℝ) :
    ∫ A, Complex.exp (Complex.I * (rslTest α β A : ℂ)) ∂gueMeasure ι t =
      Complex.exp (-(((t : ℝ) * rslQ α β : ℝ) : ℂ) / 2) := by
  have hm : Measurable (fun r : (ι × ι) × Fin 2 → ℝ => gueSample t (circularBrownianCoordinates r)) :=
    (rsl_measurable_gueSample t).comp rsl_measurable_cbc
  rw [rsl_gueMeasure_eq_map, integral_map hm.aemeasurable
    (rsl_measurable_expTest α β).aestronglyMeasurable]
  simp only [rsl_test_gueSample]
  have h := BlockBand.Parameters.gaussianProduct_characteristic
    (fun _ : (ι × ι) × Fin 2 => (1 : ℝ≥0)) (rslCoef t α β)
  rw [rsl_coef_sq] at h
  exact h

theorem rsl_charFun_gue_ne_zero (t : ℝ≥0) (α β : ι → ι → ℝ) :
    ∫ A, Complex.exp (Complex.I * (rslTest α β A : ℂ)) ∂gueMeasure ι t ≠ 0 := by
  rw [rsl_charFun_gue]
  exact Complex.exp_ne_zero _

end Gue

/-!
## 3. Variances add on the pair
-/

section PairAdd

theorem rsl_test_submatrix {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    (e : ι' ≃ ι) (f : κ' ≃ κ) (α β : ι → κ → ℝ) (M : Matrix ι' κ' ℂ) :
    rslTest α β (M.submatrix e.symm f.symm) =
      rslTest (fun u v => α (e u) (f v)) (fun u v => β (e u) (f v)) M := by
  unfold rslTest
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← f.sum_comp]
  simp only [submatrix_apply, Equiv.symm_apply_apply]

theorem rsl_Q_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (α β : ι → ι → ℝ) :
    rslQ α β = rslQ (fun u v => α (e u) (e v)) (fun u v => β (e u) (e v)) := by
  unfold rslQ
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← e.sum_comp]

/-- Bond coefficient (real parts) of a test of a two-block matrix. -/
def rslS {W : ℕ} (α : Fin 2 × Fin W → Fin 2 × Fin W → ℝ) (c c' : Fin W) : ℝ :=
  α (1, c) (0, c') + α (0, c') (1, c)

/-- Bond coefficient (imaginary parts) of a test of a two-block matrix. -/
def rslT {W : ℕ} (β : Fin 2 × Fin W → Fin 2 × Fin W → ℝ) (c c' : Fin W) : ℝ :=
  β (1, c) (0, c') - β (0, c') (1, c)

/-- Diagonal block `j` of a two-block coefficient array. -/
def rslBlk {W : ℕ} (α : Fin 2 × Fin W → Fin 2 × Fin W → ℝ) (j : Fin 2) (c c' : Fin W) : ℝ :=
  α (j, c) (j, c')

theorem rsl_sum4 {W : ℕ} (A B C D : Fin W → Fin W → ℝ) :
    ∑ c, (∑ c', A c c' + ∑ c', B c c') + ∑ c, (∑ c', C c c' + ∑ c', D c c') =
      ∑ c, ∑ c', A c c' + ∑ c, ∑ c', D c c' + ∑ c, ∑ c', (C c c' + B c' c) := by
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun c c' => B c' c)]
  ring

theorem rsl_test_rpMatrix {W : ℕ} (α β : Fin 2 × Fin W → Fin 2 × Fin W → ℝ) (y : RpSample W) :
    rslTest α β (rpMatrix y) =
      rslTest (rslBlk α 0) (rslBlk β 0) (y.1 0) + rslTest (rslBlk α 1) (rslBlk β 1) (y.1 1) +
        rslTest (rslS α) (rslT β) y.2 := by
  unfold rslTest rslS rslT rslBlk
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, rpMatrix]
  simp
  refine (rsl_sum4 _ _ _ _).trans ?_
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  ring

theorem rsl_Q_block {W : ℕ} (α β : Fin 2 × Fin W → Fin 2 × Fin W → ℝ) :
    rslQ α β = rslQ (rslBlk α 0) (rslBlk β 0) + rslQ (rslBlk α 1) (rslBlk β 1) +
      (∑ c, ∑ c', (rslS α c c' ^ 2 + rslT β c c' ^ 2)) / 2 := by
  unfold rslQ rslS rslT rslBlk
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  refine (rsl_sum4 _ _ _ _).trans ?_
  rw [Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun c' _ => ?_
  ring

/-- The variance of a test of the residual pair matrix under `rpLaw W b s`. -/
def rslVarRp (W : ℕ) (b s : ℝ) (α β : Fin 2 × Fin W → Fin 2 × Fin W → ℝ) : ℝ :=
  (Real.toNNReal ((1 - 2 * b - s / 2) / W) : ℝ) *
      (rslQ (rslBlk α 0) (rslBlk β 0) + rslQ (rslBlk α 1) (rslBlk β 1)) +
    (Real.toNNReal ((b - s / 2) / W) : ℝ) / 2 * ∑ c, ∑ c', (rslS α c c' ^ 2 + rslT β c c' ^ 2)

/-- **Characteristic function of the residual pair matrix** under `rpLaw W b s`. -/
theorem rsl_charFun_rpLaw (W : ℕ) (b s : ℝ) (α β : Fin 2 × Fin W → Fin 2 × Fin W → ℝ) :
    ∫ y, Complex.exp (Complex.I * (rslTest α β (rpMatrix y) : ℂ)) ∂rpLaw W b s =
      Complex.exp (-(rslVarRp W b s α β : ℂ) / 2) := by
  have hpt : ∀ y : RpSample W, Complex.exp (Complex.I * (rslTest α β (rpMatrix y) : ℂ)) =
      ((fun j : Fin 2 => Complex.exp (Complex.I *
          (rslTest (rslBlk α j) (rslBlk β j) (y.1 j) : ℂ))) 0 *
        (fun j : Fin 2 => Complex.exp (Complex.I *
          (rslTest (rslBlk α j) (rslBlk β j) (y.1 j) : ℂ))) 1) *
        Complex.exp (Complex.I * (rslTest (rslS α) (rslT β) y.2 : ℂ)) := by
    intro y
    rw [rsl_test_rpMatrix]
    simp only [Complex.ofReal_add, mul_add, Complex.exp_add]
  simp only [hpt]
  unfold rpLaw
  rw [integral_prod_mul (f := fun A : Fin 2 → Matrix (Fin W) (Fin W) ℂ =>
      (fun j : Fin 2 => Complex.exp (Complex.I *
          (rslTest (rslBlk α j) (rslBlk β j) (A j) : ℂ))) 0 *
        (fun j : Fin 2 => Complex.exp (Complex.I *
          (rslTest (rslBlk α j) (rslBlk β j) (A j) : ℂ))) 1)
    (g := fun B => Complex.exp (Complex.I * (rslTest (rslS α) (rslT β) B : ℂ)))]
  have hpi := integral_fintype_prod_eq_prod
    (μ := fun _ : Fin 2 => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b - s / 2) / W)))
    (fun (j : Fin 2) (A : Matrix (Fin W) (Fin W) ℂ) =>
      Complex.exp (Complex.I * (rslTest (rslBlk α j) (rslBlk β j) A : ℂ)))
  simp only [Fin.prod_univ_two] at hpi
  rw [hpi, rsl_charFun_gue, rsl_charFun_gue]
  have hg := rng_charFun_ginibre (W := W) (Real.toNNReal ((b - s / 2) / W)) (rslS α) (rslT β)
  unfold rngGinTest at hg
  unfold rslTest
  rw [hg, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold rslVarRp
  push_cast
  ring

variable {p : Parameters}

/-- The residual pair matrix on the pair sites. -/
def rslV (i : ZMod p.n) (y : RpSample p.W) : PairMatrix p i :=
  (rpMatrix y).submatrix (rpPairEquiv i).symm (rpPairEquiv i).symm

theorem rsl_measurable_V (i : ZMod p.n) : Measurable (rslV (p := p) i) := by
  have hV := rp_measurable_rpMatrix p.W
  exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => pg_entry hV _ _

theorem rsl_measurable_add_V (i : ZMod p.n) :
    Measurable (fun x : RpSample p.W × PairMatrix p i => rslV i x.1 + x.2) := by
  have hV := rsl_measurable_V (p := p) i
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  simp only [Matrix.add_apply]
  exact ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp (hV.comp measurable_fst))).add
    ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd))

theorem rsl_coe_rp {b s : ℝ} (W : ℕ) (hc : s ≤ 2 * (1 - 2 * b)) (hb : s ≤ 2 * b) :
    (Real.toNNReal ((1 - 2 * b - s / 2) / W) : ℝ) = (1 - 2 * b - s / 2) / W ∧
      (Real.toNNReal ((b - s / 2) / W) : ℝ) = (b - s / 2) / W :=
  ⟨Real.coe_toNNReal _ (div_nonneg (by linarith) (Nat.cast_nonneg _)),
    Real.coe_toNNReal _ (div_nonneg (by linarith) (Nat.cast_nonneg _))⟩

/-- **Variances add on the pair**: the residual pair matrix of `rpLaw s` plus an independent
`GUE_{2W}(s/(2W))` has the law of the residual pair matrix of `rpLaw 0` (the physical pair). -/
theorem rsl_pair_add (i : ZMod p.n) {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ 2 * (1 - 2 * p.b))
    (hsb : s ≤ 2 * p.b) :
    ((rpLaw p.W p.b s).prod (gueMeasure (PairSite p i) (pairTime p s))).map
        (fun x => rslV i x.1 + x.2) = (rpLaw p.W p.b 0).map (rslV i) := by
  apply rsl_measure_ext
  intro α β
  rw [integral_map (rsl_measurable_add_V i).aemeasurable
      (rsl_measurable_expTest α β).aestronglyMeasurable,
    integral_map (rsl_measurable_V i).aemeasurable (rsl_measurable_expTest α β).aestronglyMeasurable]
  simp only [rslTest_add, Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [integral_prod_mul (f := fun y => Complex.exp (Complex.I * (rslTest α β (rslV i y) : ℂ)))
    (g := fun G => Complex.exp (Complex.I * (rslTest α β G : ℂ)))]
  simp only [rslV, rsl_test_submatrix]
  rw [rsl_charFun_rpLaw, rsl_charFun_rpLaw, rsl_charFun_gue, ← Complex.exp_add,
    rsl_Q_reindex (rpPairEquiv i), rsl_Q_block]
  congr 1
  unfold rslVarRp
  obtain ⟨h1, h2⟩ := rsl_coe_rp p.W hsc hsb
  obtain ⟨h3, h4⟩ := rsl_coe_rp (b := p.b) (s := 0) p.W (by linarith [p.b_lt_half])
    (by linarith [p.b_pos])
  have ht : ((pairTime p s : ℝ≥0) : ℝ) = s / (2 * (p.W : ℝ)) :=
    Real.coe_toNNReal _ (div_nonneg hs0 (by positivity))
  rw [h1, h2, h3, h4, ht]
  push_cast
  ring

end PairAdd

/-!
## 4. Reassembly and deconvolution: uniqueness of the splitting law
-/

section Unique

variable {p : Parameters} (i : ZMod p.n)

theorem rsl_assemble_pp (ω : SplitState p i) (G : PairMatrix p i) (x y : PairSite p i) :
    assemble p i ω G x.1 y.1 = ω.2.2 x y + G x y := by
  unfold assemble
  rw [dite_eq_left x.2, dite_eq_left y.2]

theorem rsl_assemble_pe (ω : SplitState p i) (G : PairMatrix p i) (x : PairSite p i)
    (y : ExteriorSite p i) : assemble p i ω G x.1 y.1 = star (ω.2.1 y x) := by
  unfold assemble
  rw [dite_eq_left x.2, dite_eq_right y.2]

theorem rsl_assemble_ep (ω : SplitState p i) (G : PairMatrix p i) (x : ExteriorSite p i)
    (y : PairSite p i) : assemble p i ω G x.1 y.1 = ω.2.1 x y := by
  unfold assemble
  rw [dite_eq_right x.2, dite_eq_left y.2]

theorem rsl_assemble_ee (ω : SplitState p i) (G : PairMatrix p i) (x y : ExteriorSite p i) :
    assemble p i ω G x.1 y.1 = ω.1 x y := by
  unfold assemble
  rw [dite_eq_right x.2, dite_eq_right y.2]

/-- `assemble ω G = assemble ω 0 + assemble 0 G`. -/
theorem rsl_assemble_add (ω : SplitState p i) (G : PairMatrix p i) :
    assemble p i ω G = assemble p i ω 0 + assemble p i 0 G := by
  ext x y
  simp only [Matrix.add_apply, assemble]
  split_ifs <;> simp

/-- `assemble ω G = assemble (H_R, C, V + G) 0`. -/
theorem rsl_assemble_shift (ω : SplitState p i) (G : PairMatrix p i) :
    assemble p i ω G = assemble p i (ω.1, ω.2.1, ω.2.2 + G) 0 := by
  ext x y
  simp only [assemble]
  split_ifs <;> simp

theorem rsl_measurable_assemble :
    Measurable (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  unfold assemble
  split_ifs
  · exact (pg_entry (measurable_snd.comp (measurable_snd.comp measurable_fst)) _ _).add
      (pg_entry measurable_snd _ _)
  · exact continuous_star.measurable.comp
      (pg_entry (measurable_fst.comp (measurable_snd.comp measurable_fst)) _ _)
  · exact pg_entry (measurable_fst.comp (measurable_snd.comp measurable_fst)) _ _
  · exact pg_entry (measurable_fst.comp measurable_fst) _ _

theorem rsl_measurable_L : Measurable (fun ω : SplitState p i => assemble p i ω 0) :=
  (rsl_measurable_assemble i).comp (measurable_id.prodMk measurable_const)

/-- The blocks `(H_R, C, V)` of a site matrix. -/
def rslUnassemble (H : p.SiteMatrix) : SplitState p i :=
  (exteriorBlock p i H, couplingBlock p i H, pairBlock p i H)

theorem rsl_measurable_unassemble : Measurable (rslUnassemble (p := p) i) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_) <;>
    exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => pg_entry measurable_id _ _

theorem rsl_unassemble_assemble (ω : SplitState p i) : rslUnassemble i (assemble p i ω 0) = ω := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext x y
    exact rsl_assemble_ee i ω 0 x y
  · ext x y
    exact rsl_assemble_ep i ω 0 x y
  · ext x y
    simp only [rslUnassemble, pairBlock]
    rw [rsl_assemble_pp i ω 0 x y, Matrix.zero_apply, add_zero]

theorem rsl_isProb_of_splitting {model : p.GaussianRingModel} {s : ℝ} {P : Measure (SplitState p i)}
    (h : IsPairSplitting p i model s P) : IsProbabilityMeasure P := by
  have h1 := congrArg (fun μ : Measure p.SiteMatrix => μ Set.univ) h
  rw [Measure.map_apply (rsl_measurable_assemble i) MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod,
    measure_univ (μ := gueMeasure (PairSite p i) (pairTime p s)), mul_one,
    measure_univ (μ := (model.law : Measure p.SiteMatrix))] at h1
  exact ⟨h1⟩

theorem rsl_sum_site (f : p.Site → ℝ) :
    ∑ x, f x = ∑ x : PairSite p i, f x.1 + ∑ x : ExteriorSite p i, f x.1 :=
  (Fintype.sum_subtype_add_sum_subtype _ f).symm

/-- The test of the embedded pair Gaussian is a test of the pair matrix. -/
theorem rsl_test_assemble_zero (α β : p.Site → p.Site → ℝ) (G : PairMatrix p i) :
    rslTest α β (assemble p i 0 G) =
      rslTest (fun x y : PairSite p i => α x.1 y.1) (fun x y => β x.1 y.1) G := by
  unfold rslTest
  simp only [rsl_sum_site i, rsl_assemble_pp, rsl_assemble_pe, rsl_assemble_ep, rsl_assemble_ee,
    Prod.fst_zero, Prod.snd_zero, Matrix.zero_apply, star_zero, zero_add, Complex.zero_re,
    Complex.zero_im, mul_zero, add_zero, Finset.sum_const_zero]

/-- **Factorization** of the characteristic function of the physical law along a splitting. -/
theorem rsl_charFun_split {model : p.GaussianRingModel} {s : ℝ} {P : Measure (SplitState p i)}
    (h : IsPairSplitting p i model s P) (α β : p.Site → p.Site → ℝ) :
    ∫ H, Complex.exp (Complex.I * (rslTest α β H : ℂ)) ∂(model.law : Measure p.SiteMatrix) =
      (∫ ω, Complex.exp (Complex.I * (rslTest α β (assemble p i ω 0) : ℂ)) ∂P) *
        ∫ G, Complex.exp (Complex.I * (rslTest α β (assemble p i 0 G) : ℂ))
          ∂gueMeasure (PairSite p i) (pairTime p s) := by
  have := rsl_isProb_of_splitting i h
  rw [← h, integral_map (rsl_measurable_assemble i).aemeasurable
    (rsl_measurable_expTest α β).aestronglyMeasurable]
  have hpt : ∀ x : SplitState p i × PairMatrix p i,
      Complex.exp (Complex.I * (rslTest α β (assemble p i x.1 x.2) : ℂ)) =
        Complex.exp (Complex.I * (rslTest α β (assemble p i x.1 0) : ℂ)) *
          Complex.exp (Complex.I * (rslTest α β (assemble p i 0 x.2) : ℂ)) := by
    intro x
    rw [rsl_assemble_add i x.1 x.2, rslTest_add, Complex.ofReal_add, mul_add, Complex.exp_add]
  simp only [hpt]
  exact integral_prod_mul (fun ω => Complex.exp (Complex.I * (rslTest α β (assemble p i ω 0) : ℂ)))
    (fun G => Complex.exp (Complex.I * (rslTest α β (assemble p i 0 G) : ℂ)))

/-- **Deconvolution**: the splitting law of the pair splitting at a given `s` is unique (the
characteristic function of `GUE_{2W}(s/(2W))` never vanishes). -/
theorem rsl_splitting_unique {model : p.GaussianRingModel} {s : ℝ} {P₁ P₂ : Measure (SplitState p i)}
    (h₁ : IsPairSplitting p i model s P₁) (h₂ : IsPairSplitting p i model s P₂) : P₁ = P₂ := by
  have := rsl_isProb_of_splitting i h₁
  have := rsl_isProb_of_splitting i h₂
  have hL : P₁.map (fun ω => assemble p i ω 0) = P₂.map (fun ω => assemble p i ω 0) := by
    apply rsl_measure_ext
    intro α β
    rw [integral_map (rsl_measurable_L i).aemeasurable
        (rsl_measurable_expTest α β).aestronglyMeasurable,
      integral_map (rsl_measurable_L i).aemeasurable
        (rsl_measurable_expTest α β).aestronglyMeasurable]
    have e1 := rsl_charFun_split i h₁ α β
    have e2 := rsl_charFun_split i h₂ α β
    have hne : ∫ G, Complex.exp (Complex.I * (rslTest α β (assemble p i 0 G) : ℂ))
        ∂gueMeasure (PairSite p i) (pairTime p s) ≠ 0 := by
      simp only [rsl_test_assemble_zero]
      exact rsl_charFun_gue_ne_zero _ _ _
    exact mul_right_cancel₀ hne (e1.symm.trans e2)
  have hrec : ∀ P : Measure (SplitState p i),
      (P.map (fun ω => assemble p i ω 0)).map (rslUnassemble i) = P := by
    intro P
    rw [Measure.map_map (rsl_measurable_unassemble i) (rsl_measurable_L i)]
    have : (rslUnassemble i ∘ fun ω => assemble p i ω 0) = id := funext (rsl_unassemble_assemble i)
    rw [this, Measure.map_id]
  rw [← hrec P₁, ← hrec P₂, hL]

end Unique

/-!
## 5. The physical law as the residual pair at `s = 0` and the exterior path
-/

section Rearrange

variable {p : Parameters}

/-- Bond offsets from `i`: the pair bond `0`; internal path bonds `k + 2`; port bonds `1, n - 1`. -/
def rslBondOff : Fin 1 ⊕ (Fin (p.n - 2 - 1) ⊕ Fin 2) → ℕ
  | .inl _ => 0
  | .inr (.inl k) => k.val + 2
  | .inr (.inr q) => if q = 0 then 1 else p.n - 1

theorem rslBondOff_lt (u : Fin 1 ⊕ (Fin (p.n - 2 - 1) ⊕ Fin 2)) : rslBondOff u < p.n := by
  have := p.n_ge_four
  rcases u with a | k | q
  · simp only [rslBondOff]; omega
  · simp only [rslBondOff]; omega
  · simp only [rslBondOff]; split_ifs <;> omega

theorem rslBondOff_injective : Function.Injective (rslBondOff (p := p)) := by
  have := p.n_ge_four
  rintro (a | k | q) (a' | k' | q') h <;> simp only [rslBondOff] at h
  · rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero a']
  · exfalso; omega
  · exfalso; split_ifs at h; omega
  · exfalso; omega
  · congr 2; exact Fin.ext (by omega)
  · exfalso; have := k.isLt; split_ifs at h <;> omega
  · exfalso; split_ifs at h; omega
  · exfalso; have := k'.isLt; split_ifs at h <;> omega
  · congr 2
    by_cases ha : q = 0 <;> by_cases ha' : q' = 0
    · rw [ha, ha']
    · rw [ite_eq_left ha, ite_eq_right ha'] at h; omega
    · rw [ite_eq_right ha, ite_eq_left ha'] at h; omega
    · exact rng_fin2_eq ha ha'

theorem rslBondIdx_bijective (i : ZMod p.n) :
    Function.Bijective (fun u : Fin 1 ⊕ (Fin (p.n - 2 - 1) ⊕ Fin 2) => rngBlk i (rslBondOff u)) := by
  have h4 := p.n_ge_four
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro u v h
    rw [rngBlk_eq_iff i (rslBondOff_lt u) (rslBondOff_lt v)] at h
    exact rslBondOff_injective h
  · simp only [Fintype.card_sum, Fintype.card_fin, ZMod.card]
    omega

/-- Block offsets from `i`: the pair blocks `rpPairOff a`, then path block `j` at `j + 2`. -/
def rslBlkOff : Fin 2 ⊕ Fin (p.n - 2) → ℕ
  | .inl a => rpPairOff a
  | .inr j => j.val + 2

theorem rslBlkOff_lt (u : Fin 2 ⊕ Fin (p.n - 2)) : rslBlkOff u < p.n := by
  have := p.n_ge_four
  rcases u with a | j
  · exact rpPairOff_lt a
  · simp only [rslBlkOff]; omega

theorem rslBlkOff_injective : Function.Injective (rslBlkOff (p := p)) := by
  have := p.n_ge_four
  rintro (a | j) (a' | j') h <;> simp only [rslBlkOff, rpPairOff] at h
  · congr 1
    by_cases ha : a = 0 <;> by_cases ha' : a' = 0
    · rw [ha, ha']
    · rw [ite_eq_left ha, ite_eq_right ha'] at h; omega
    · rw [ite_eq_right ha, ite_eq_left ha'] at h; omega
    · exact rng_fin2_eq ha ha'
  · exfalso; split_ifs at h; omega
  · exfalso; split_ifs at h; omega
  · congr 1; exact Fin.ext (by omega)

theorem rslBlkIdx_bijective (i : ZMod p.n) :
    Function.Bijective (fun u : Fin 2 ⊕ Fin (p.n - 2) => rngBlk i (rslBlkOff u)) := by
  have h4 := p.n_ge_four
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro u v h
    rw [rngBlk_eq_iff i (rslBlkOff_lt u) (rslBlkOff_lt v)] at h
    exact rslBlkOff_injective h
  · simp only [Fintype.card_sum, Fintype.card_fin, ZMod.card]
    omega

/-- **The pair split of the ring sample**: the physical pair (blocks `A_{i+1}, A_i`, bond `B_i`)
and the exterior path of the `n - 2` blocks `A_{i+2+j}` (bonds `B_{i+2+k}`, port bonds
`B_{i+1}ᴴ`, `B_{i-1}`). -/
def rslTheta (i : ZMod p.n) (ω : RngSample p) : RpSample p.W × PathSample p.W (p.n - 2) :=
  ((fun a => ω.1 (rngBlk i (rpPairOff a)), ω.2 (rngBlk i 0)),
    (fun j => ω.1 (rngBlk i (j.val + 2)), fun k => ω.2 (rngBlk i (k.val + 2)),
      fun q => if q = 0 then (ω.2 (rngBlk i 1))ᴴ else ω.2 (rngBlk i (p.n - 1))))

/-- The pair split is measure preserving: `rngLaw ∘ rslTheta⁻¹ = rpLaw 0 ⊗ pathLaw (n-2)`. -/
theorem rsl_mp_theta (i : ZMod p.n) :
    MeasurePreserving (rslTheta i) (rngLaw p)
      ((rpLaw p.W p.b 0).prod (pathLaw p.W (p.n - 2) p.b)) := by
  have := fun t => isProbabilityMeasure_gueMeasure p.W t
  set μA := gueMeasure (Fin p.W) (Real.toNNReal ((1 - 2 * p.b) / p.W)) with hμA
  set μB := ginibreMeasure (Fin p.W) (Fin p.W) (Real.toNNReal (p.b / p.W)) with hμB
  have hA1 := rng_ofBijective_reindex μA (rslBlkIdx_bijective i)
  have hA2 := rng_mp_sum_split (ι := Fin 2) (ι' := Fin (p.n - 2)) μA
  have hA := hA2.comp hA1
  have hB1 := rng_ofBijective_reindex μB (rslBondIdx_bijective i)
  have hB2 := rng_mp_sum_split (ι := Fin 1) (ι' := Fin (p.n - 2 - 1) ⊕ Fin 2) μB
  have hB3 := (MeasurePreserving.id (Measure.pi fun _ : Fin 1 => μB)).prod
    (rng_mp_sum_split (ι := Fin (p.n - 2 - 1)) (ι' := Fin 2) μB)
  have hU := measurePreserving_funUnique μB (Fin 1)
  have hP : MeasurePreserving
      (fun (f : Fin 2 → Matrix (Fin p.W) (Fin p.W) ℂ) (j : Fin 2) =>
        if decide (j = 0) then (f j)ᴴ else f j)
      (Measure.pi fun _ : Fin 2 => μB) (Measure.pi fun _ : Fin 2 => μB) :=
    measurePreserving_pi _ _ fun j => rng_mp_conj_or_id _ (decide (j = 0))
  have hB4 := hU.prod ((MeasurePreserving.id (Measure.pi fun _ : Fin (p.n - 2 - 1) => μB)).prod hP)
  have hB := hB4.comp (hB3.comp (hB2.comp hB1))
  have hR := rng_mp_rearrange (Measure.pi fun _ : Fin 2 => μA)
    (Measure.pi fun _ : Fin (p.n - 2) => μA) μB
    ((Measure.pi fun _ : Fin (p.n - 2 - 1) => μB).prod (Measure.pi fun _ : Fin 2 => μB))
  have hall := hR.comp (hA.prod hB)
  have h0 : rpLaw p.W p.b 0 = (Measure.pi fun _ : Fin 2 => μA).prod μB := by
    simp only [rpLaw, hμA, hμB, zero_div, sub_zero]
  rw [h0]
  unfold rngLaw pathLaw
  convert hall using 1
  funext ω
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext a; rfl
  · rfl
  · funext j; rfl
  · funext k; rfl
  · funext q
    by_cases hq : q = 0
    · subst hq; simp [rslTheta, rslBondOff]
    · simp [rslTheta, rslBondOff, hq]

theorem rsl_site_cases (i : ZMod p.n) (x : p.Site) :
    (∃ u, (rpPairEquiv i u).1 = x) ∨ (∃ v, (rpExtEquiv i v).1 = x) := by
  by_cases hx : x.1 = i ∨ x.1 = i + 1
  · exact Or.inl ⟨(rpPairEquiv i).symm ⟨x, hx⟩, by rw [Equiv.apply_symm_apply]⟩
  · exact Or.inr ⟨(rpExtEquiv i).symm ⟨x, hx⟩, by rw [Equiv.apply_symm_apply]⟩

theorem rsl_extEquiv_val (i : ZMod p.n) (j : Fin (p.n - 2)) (x : Fin p.W) :
    (rpExtEquiv i (j, x)).1 = (rngBlk i (j.val + 2), x) := rfl

theorem rsl_ring_pp (i : ZMod p.n) (om : RngSample p) (u v : Fin 2 × Fin p.W) :
    rngAssemble p om (rpPairEquiv i u).1 (rpPairEquiv i v).1 = rpMatrix (rslTheta i om).1 u v := by
  obtain ⟨a, c⟩ := u
  obtain ⟨a', c'⟩ := v
  rw [rpPairEquiv_val, rpPairEquiv_val, rngAssemble_off om i (rpPairOff_lt a) (rpPairOff_lt a')]
  have h4 := p.n_ge_four
  have h2 : (2 : ℕ) ≠ p.n := by omega
  rcases rng_fin2_cases a with rfl | rfl <;> rcases rng_fin2_cases a' with rfl | rfl <;>
    simp [rpPairOff, rpMatrix, rslTheta, h2]

theorem rsl_ring_ee (i : ZMod p.n) (om : RngSample p) (u v : Fin (p.n - 2) × Fin p.W) :
    rngAssemble p om (rpExtEquiv i u).1 (rpExtEquiv i v).1 = pathMatrix (rslTheta i om).2 u v := by
  obtain ⟨j, c⟩ := u
  obtain ⟨j', c'⟩ := v
  have hj := j.isLt
  have hj' := j'.isLt
  rw [rsl_extEquiv_val, rsl_extEquiv_val, rngAssemble_off om i (by omega) (by omega)]
  unfold pathMatrix
  simp only
  by_cases h1 : j = j'
  · subst h1
    simp [rslTheta]
  · have h1' : j.val + 2 ≠ j'.val + 2 := fun h => h1 (Fin.ext (by omega))
    rw [ite_eq_right h1, ite_eq_right h1']
    by_cases h2 : j.val + 1 = j'.val
    · rw [dite_eq_left h2, ite_eq_left (Or.inl (by omega))]
      rfl
    · rw [dite_eq_right h2, ite_eq_right (by omega)]
      by_cases h3 : j'.val + 1 = j.val
      · rw [dite_eq_left h3, ite_eq_left (Or.inl (by omega))]
        rfl
      · rw [dite_eq_right h3, ite_eq_right (by omega)]

theorem rsl_ring_ep (i : ZMod p.n) (om : RngSample p) (u : Fin (p.n - 2) × Fin p.W)
    (v : Fin 2 × Fin p.W) :
    rngAssemble p om (rpExtEquiv i u).1 (rpPairEquiv i v).1 =
      pathPortCoupling (rslTheta i om).2 u v := by
  obtain ⟨j, c⟩ := u
  obtain ⟨a, c'⟩ := v
  have hj := j.isLt
  have h4 := p.n_ge_four
  rw [rsl_extEquiv_val, rpPairEquiv_val, rngAssemble_off om i (by omega) (rpPairOff_lt a)]
  unfold pathPortCoupling
  rcases rng_fin2_cases a with rfl | rfl
  · simp only [rpPairOff, ite_true]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    by_cases h0 : j.val = 0
    · rw [ite_eq_left (Or.inl (by omega)), ite_eq_left (Or.inl ⟨trivial, h0⟩)]
      simp [rslTheta]
    · rw [ite_eq_right (by omega), ite_eq_right (by simp [h0])]
  · simp only [rpPairOff, show ((1 : Fin 2) = 0) ↔ False by decide, ite_false]
    rw [ite_eq_right (by omega)]
    by_cases h0 : j.val + 3 = p.n
    · rw [ite_eq_left (Or.inr ⟨h0, trivial⟩), ite_eq_left (Or.inr ⟨trivial, by omega⟩)]
      simp only [rslTheta, show ((1 : Fin 2) = 0) ↔ False by decide, ite_false]
      rw [show j.val + 2 = p.n - 1 by omega]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by simp; omega)]

/-- **Pointwise reassembly**: the ring matrix is the reassembly (with `G = 0`) of the split state
built from its pair split. -/
theorem rsl_ring_eq (i : ZMod p.n) (om : RngSample p) :
    rngAssemble p om = assemble p i (rpSplitAssemble i (rslTheta i om)) 0 := by
  ext x y
  rcases rsl_site_cases i x with ⟨u, rfl⟩ | ⟨u, rfl⟩ <;>
    rcases rsl_site_cases i y with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · rw [rsl_assemble_pp, rsl_ring_pp]
    simp [rpSplitAssemble]
  · have hne : (rpExtEquiv i v).1.1 ≠ (rpPairEquiv i u).1.1 := fun h =>
      (rpExtEquiv i v).2 (h ▸ (rpPairEquiv i u).2)
    rw [rsl_assemble_pe, ← rngAssemble_star_of_ne om _ _ hne, rsl_ring_ep]
    simp [rpSplitAssemble]
  · rw [rsl_assemble_ep, rsl_ring_ep]
    simp [rpSplitAssemble]
  · rw [rsl_assemble_ee, rsl_ring_ee]
    simp [rpSplitAssemble]

/-- **The physical law at `s = 0`**: `model.law` is the reassembly (with `G = 0`) of the image of
`rpLaw 0 ⊗ pathLaw (n-2)` under `rpSplitAssemble`. -/
theorem rsl_law_eq_split0 (i : ZMod p.n) (model : p.GaussianRingModel) :
    (model.law : Measure p.SiteMatrix) =
      ((rpLaw p.W p.b 0).prod (pathLaw p.W (p.n - 2) p.b)).map
        (fun z => assemble p i (rpSplitAssemble i z) 0) := by
  have hm : Measurable (fun z : RpSample p.W × PathSample p.W (p.n - 2) =>
      assemble p i (rpSplitAssemble i z) 0) :=
    (rsl_measurable_L i).comp (rp_measurable_splitAssemble i)
  rw [rng_law_eq_map, ← (rsl_mp_theta i).map_eq, Measure.map_map hm (rsl_mp_theta i).measurable]
  congr 1
  funext om
  exact rsl_ring_eq i om

end Rearrange

/-!
## 6. The residual splitting law and the conclusion
-/

section Conclusion

variable {p : Parameters}

/-- The split state with exterior path `π` and pair block `V`. -/
def rslFrame (i : ZMod p.n) (π : PathSample p.W (p.n - 2)) (V : PairMatrix p i) : SplitState p i :=
  ((pathMatrix π).submatrix (rpExtEquiv i).symm (rpExtEquiv i).symm,
    (pathPortCoupling π).submatrix (rpExtEquiv i).symm (rpPairEquiv i).symm, V)

theorem rsl_measurable_frame (i : ZMod p.n) :
    Measurable (fun w : PairMatrix p i × PathSample p.W (p.n - 2) => rslFrame i w.2 w.1) := by
  have hP := measurable_pathMatrix p.W (p.n - 2)
  have hC := measurable_pathPortCoupling p.W (p.n - 2)
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ measurable_fst)
  · exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
      pg_entry (hP.comp measurable_snd) _ _
  · exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
      pg_entry (hC.comp measurable_snd) _ _

/-- `((y, π), G) ↦ ((y, G), π)` is measure preserving. -/
theorem rsl_mp_swap {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving (fun x : (α × β) × γ => ((x.1.1, x.2), x.1.2))
      ((μa.prod μb).prod μc) ((μa.prod μc).prod μb) := by
  have h1 := measurePreserving_prodAssoc μa μb μc
  have h2 := (MeasurePreserving.id μa).prod (Measure.measurePreserving_swap (μ := μb) (ν := μc))
  have h3 := (measurePreserving_prodAssoc μa μc μb).symm MeasurableEquiv.prodAssoc
  exact h3.comp (h2.comp h1)

/-- **The residual splitting law satisfies the pair splitting**: for `0 ≤ s ≤ 2 min(c, b)`,
`Q = (rpLaw s ⊗ pathLaw (n-2)).map rpSplitAssemble` with an independent `GUE_{2W}(s/(2W))`
reassembles to the physical law. -/
theorem rsl_isPairSplitting (i : ZMod p.n) (model : p.GaussianRingModel) {s : ℝ} (hs0 : 0 ≤ s)
    (hsc : s ≤ 2 * (1 - 2 * p.b)) (hsb : s ≤ 2 * p.b) :
    IsPairSplitting p i model s
      (((rpLaw p.W p.b s).prod (pathLaw p.W (p.n - 2) p.b)).map (rpSplitAssemble i)) := by
  unfold IsPairSplitting
  rw [rsl_law_eq_split0 i model]
  set γ := gueMeasure (PairSite p i) (pairTime p s) with hγ
  have : IsProbabilityMeasure (pathLaw p.W (p.n - 2) p.b) := pg_isProbabilityMeasure_pathLaw _ _ _
  have : IsProbabilityMeasure (rpLaw p.W p.b s) := rp_isProbabilityMeasure_rpLaw _ _ _
  have : IsProbabilityMeasure (rpLaw p.W p.b 0) := rp_isProbabilityMeasure_rpLaw _ _ _
  have : IsProbabilityMeasure γ := rsl_isProbabilityMeasure_gue _
  have : SFinite (pathLaw p.W (p.n - 2) p.b) := inferInstance
  have : SFinite (rpLaw p.W p.b s) := inferInstance
  have : SFinite γ := inferInstance
  have hS := rp_measurable_splitAssemble (p := p) i
  have e1 : (((rpLaw p.W p.b s).prod (pathLaw p.W (p.n - 2) p.b)).map (rpSplitAssemble i)).prod γ =
      (((rpLaw p.W p.b s).prod (pathLaw p.W (p.n - 2) p.b)).prod γ).map
        (Prod.map (rpSplitAssemble i) id) := by
    rw [← Measure.map_prod_map _ _ hS measurable_id, Measure.map_id]
  have hfun : (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) ∘
      Prod.map (rpSplitAssemble i) id =
      (fun w : PairMatrix p i × PathSample p.W (p.n - 2) => assemble p i (rslFrame i w.2 w.1) 0) ∘
        (Prod.map (fun x : RpSample p.W × PairMatrix p i => rslV i x.1 + x.2) id ∘
          (fun x : (RpSample p.W × PathSample p.W (p.n - 2)) × PairMatrix p i =>
            ((x.1.1, x.2), x.1.2))) := by
    funext z
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    rw [rsl_assemble_shift]
    rfl
  have hF : Measurable (fun w : PairMatrix p i × PathSample p.W (p.n - 2) =>
      assemble p i (rslFrame i w.2 w.1) 0) := (rsl_measurable_L i).comp (rsl_measurable_frame i)
  have hA := (rsl_measurable_add_V (p := p) i).prodMap (measurable_id (α := PathSample p.W (p.n - 2)))
  have hR := rsl_mp_swap (rpLaw p.W p.b s) (pathLaw p.W (p.n - 2) p.b) γ
  rw [e1, Measure.map_map (rsl_measurable_assemble i) (hS.prodMap measurable_id), hfun,
    ← Measure.map_map hF (hA.comp hR.measurable), ← Measure.map_map hA hR.measurable, hR.map_eq,
    ← Measure.map_prod_map _ _ (rsl_measurable_add_V i) measurable_id, Measure.map_id, hγ,
    rsl_pair_add i hs0 hsc hsb,
    ← Measure.map_id (μ := pathLaw p.W (p.n - 2) p.b),
    Measure.map_prod_map _ _ (rsl_measurable_V i) measurable_id, Measure.map_id,
    Measure.map_map hF ((rsl_measurable_V i).prodMap measurable_id)]
  rfl

/-- **`ResidualSplitLaw`** (law identification of the residual pair by deconvolution). -/
theorem residualSplitLaw_holds : ResidualSplitLaw := by
  intro p model i s hs hs2 Pω hP
  have h1 : min (1 - 2 * p.b) p.b ≤ 1 - 2 * p.b := min_le_left _ _
  have h2 : min (1 - 2 * p.b) p.b ≤ p.b := min_le_right _ _
  exact rsl_splitting_unique i hP (rsl_isPairSplitting i model hs.le (by linarith) (by linarith))

end Conclusion

end BlockBand.Layers
