module

public import BlockBand.Coarea.ClockRank
public import BlockBand.Coarea.ContractClauses
public import BlockBand.Coarea.ProjectiveHaar
public import BlockBand.Coarea.RegularAE

/-!
# The coarea theorem: assembly of `formula`, `mass_one`, `pairLaw_formula`, `pairLaw_measure`

Measures: an arbitrary law `Pω` of the split state satisfying `IsPairSplitting` (no
finiteness or σ-finiteness is assumed; Tonelli `lintegral_prod` needs only that `GUE_d(t)` is
s-finite), `GUE_d(t)`, `t = s/d`, Lebesgue measure in `E`, `projectiveHaar` in `v`,
`GUE_{d-1}(t)` in `G'`. Exact identities of `[0,∞]`-valued integrals, every admissible
`Parameters`, model, rank, pair, frame and `0 < s ≤ min(c,b)`; no norm or limit occurs.

* `coarea_formula_of_fixed` (`formula`): Tonelli on `Pω ⊗ GUE_d(t)` for the measurable
  `Function.uncurry Φ`, then `formula_fixed` at `g = Φ ω` (measurable section).
* `coarea_mass_one_of_fixed` (`mass_one`): `formula` with `Φ = 1`; the total mass of
  `Pω ⊗ GUE_d(t)` is that of its image `model.law` under `assemble`, i.e. one.
* `coarea_pairLaw_formula_of_fixed` (`pairLaw_formula`): `formula` with
  `Φ' = ofReal(n/2 · m(assemble ω G)) · Φ`, then the fiber identity `coareaFiber_pairWeight`:
  for `Pω`-a.e. `ω` (`H_R`, `V` Hermitian: `ae_split_isHermitian`), for Lebesgue-a.e. `E`
  (`det(H_R - E) ≠ 0`: `ae_det_shift_ne_zero`), `ν`-a.e. `v` (unit) and `GUE`-a.e. `G'`
  (Hermitian), the integrands agree: if `det M = 0` both vanish (`|det M|² = 0`), if the inertia
  indicator is `0` both vanish, and otherwise `coarea_reconstructed_rank` gives
  `ψ_αψ_α* = LL*/‖L‖²` for the reconstructed (Hermitian) matrix, so `m = ‖v‖²/‖L‖² = ‖L‖⁻²`,
  while `v*𝒟v = ‖L‖²` (`clockSpeed_eq_l2Norm_sq`); hence `v*𝒟v · m = 1`
  (`clockSpeed_mul_pairMass`) and `v*𝒟v · (n/2) m = n/2`.
* `coarea_pairLaw_measure_of_fixed` (`pairLaw_measure`): `physicalPairMeasure` is
  `model.law.withDensity (n/2 · m)`; transport along `assemble` by `IsPairSplitting`
  (`lintegral_map`) and apply `pairLaw_formula` to `Φ = Φ₀ ∘ assemble`.
* `coareaContract_of_formulaFixed`: the full `CoareaContract` from the premise and the clauses
  `coarea_splitting_exists`, `coarea_frame_exists`, `coarea_pairLaw_probability`
  (`ContractClauses`), `coarea_clock`, `coarea_reconstructed_rank` (`ClockRank`),
  `coarea_regular_ae` (`RegularAE`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.CoareaAssembly

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Model.Construction BlockBand.QUE.Fourier
  BlockBand.Coarea
open scoped ENNReal NNReal ComplexConjugate

/-- Definitionally the type of the field `CoareaContract.formula_fixed` (the fixed-`ω` coarea
formula, for `Pω`-a.e. `ω` simultaneously for all measurable `g ≥ 0`). It is the hypothesis of
every reduction below; it follows from the regularity clause by `formula_fixed_of_regularAE`. -/
abbrev FormulaFixedStatement : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (i : ZMod p.n) (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ U, IsPairFrame p i U →
    ∀ᵐ ω ∂Pω, ∀ g : PairMatrix p i → ℝ≥0∞, Measurable g →
      (∫⁻ G, g G ∂(gueMeasure (PairSite p i) (pairTime p s))) =
        coareaFiber p α i s U (clockSpeed p i) ω g

section Lemmas
variable (p : Parameters) (i : ZMod p.n)

/-- For every splitting law, `Pω`-a.e. `ω = (H_R, C, V)` has `H_R` and `V` Hermitian
(from the a.e. Hermitian support of the physical law, transported through `IsPairSplitting`,
and the Hermitian support of GUE). -/
theorem ae_split_isHermitian (model : p.GaussianRingModel) (s : ℝ)
    (Pω : Measure (SplitState p i)) (hP : IsPairSplitting p i model s Pω) :
    ∀ᵐ ω ∂Pω, ω.1.IsHermitian ∧ ω.2.2.IsHermitian := by
  have h0 := model.isPhysical.1
  rw [← hP, ae_map_iff (ContractClauses.measurable_assemble p i).aemeasurable
    measurableSet_isHermitian] at h0
  filter_upwards [Measure.ae_ae_of_ae_prod h0] with ω hω
  obtain ⟨G, hG, hGh⟩ := (hω.and (GUELaw.ae_isHermitian_gueMeasure (ι := PairSite p i)
    (pairTime p s))).exists
  refine ⟨?_, ?_⟩
  · ext x y
    have h := hG.apply x.1 y.1
    simp only [assemble, x.2, y.2, dite_false] at h
    simpa [Matrix.conjTranspose_apply] using h
  · ext x y
    have h := hG.apply x.1 y.1
    have h' := hGh.apply x y
    simp only [assemble, x.2, y.2, dite_true, Subtype.coe_eta, star_add] at h
    rw [Matrix.conjTranspose_apply]
    rw [h'] at h
    exact add_right_cancel h

/-- For every `H_R`, `det(H_R - E) ≠ 0` for Lebesgue-a.e. real `E` (the exceptional set is
contained in the finite root set of the monic characteristic polynomial). -/
theorem ae_det_shift_ne_zero (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) :
    ∀ᵐ E : ℝ, (H_R - (E : ℂ) • 1).det ≠ 0 := by
  have hfin : {E : ℝ | (H_R - (E : ℂ) • 1).det = 0}.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot (H_R.charpoly_monic.ne_zero)).preimage
      (Complex.ofReal_injective.injOn) |>.subset ?_
    intro E hE
    simp only [Set.mem_ofPred_eq] at hE ⊢
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot, Matrix.eval_charpoly]
    have : Matrix.scalar (ExteriorSite p i) (E : ℂ) - H_R = -(H_R - (E : ℂ) • 1) := by
      rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [this, Matrix.det_neg, hE, mul_zero]
  exact measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)

/-- `F(E) = V - C*(H_R - E)⁻¹C` is Hermitian for Hermitian `H_R`, `V` and real `E`. -/
theorem physicalCoareaF_isHermitian (ω : SplitState p i) (h1 : ω.1.IsHermitian)
    (h3 : ω.2.2.IsHermitian) (E : ℝ) :
    (physicalCoareaF ω.1 ω.2.1 ω.2.2 E).IsHermitian := by
  unfold physicalCoareaF physicalCoareaResolvent
  exact h3.sub (Matrix.isHermitian_conjTranspose_mul_mul _ (ClockRank.shift_isHermitian h1 E).inv)

/-- The reconstructed Gaussian `E vv* + U_v(F_v + G')U_v* - F(E)` is Hermitian. -/
theorem reconstructedGaussian_isHermitian
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian) (E : ℝ)
    (v : PairSite p i → ℂ) (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ)
    (hG' : G'.IsHermitian) :
    (reconstructedGaussian p i U ω E v G').IsHermitian := by
  have hF := physicalCoareaF_isHermitian p i ω h1 h3 E
  have hvv : (vecMulVec v (star v)).IsHermitian := by
    ext a b
    simp [vecMulVec, Matrix.conjTranspose_apply, mul_comm]
  have hE : ((E : ℂ) • vecMulVec v (star v)).IsHermitian := by
    rw [IsHermitian, Matrix.conjTranspose_smul, hvv.eq, Complex.star_def, Complex.conj_ofReal]
  unfold reconstructedGaussian
  exact (hE.add (Matrix.isHermitian_mul_mul_conjTranspose _
    ((Matrix.isHermitian_conjTranspose_mul_mul _ hF).add hG'))).sub hF

/-- `Re(w* w) = Σ |w_k|²`. -/
theorem re_star_dotProduct_self {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    (star w ⬝ᵥ w).re = ∑ k, ‖w k‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- `v*𝒟(E)v = ‖L_E v‖²` (`𝒟 = 1 + TᴴT`, `L_E v = (v, -Tv)`), pointwise for every `ω, E, v`. -/
theorem clockSpeed_eq_l2Norm_sq (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) :
    clockSpeed p i ω E v = l2Norm (schurLift p i ω.1 ω.2.1 E v) ^ 2 := by
  set L := schurLift p i ω.1 ω.2.1 E v
  set T := physicalCoareaT ω.1 ω.2.1 E
  have hL2 : l2Norm L ^ 2 = ∑ x, ‖L x‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _)
  have hpair := ClockRank.schurLift_pair p i ω.1 ω.2.1 E v
  have hext := ClockRank.schurLift_ext p i ω.1 ω.2.1 E v
  have hS : ∑ s : PairSite p i, ‖L s.1‖ ^ 2 = ∑ s, ‖v s‖ ^ 2 :=
    Finset.sum_congr rfl fun s _ => by rw [← congrFun hpair s]
  have hR : ∑ r : ExteriorSite p i, ‖L r.1‖ ^ 2 = ∑ r, ‖(T *ᵥ v) r‖ ^ 2 :=
    Finset.sum_congr rfl fun r _ => by rw [show L r.1 = -(T *ᵥ v) r from congrFun hext r, norm_neg]
  rw [hL2, ClockRank.sum_site_real p i, hS, hR, clockSpeed, physicalCoareaD, schurClock,
    Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    re_star_dotProduct_self, re_star_dotProduct_self]

/-- `‖L_E v‖² ≥ ‖v‖² = 1` for unit `v`. -/
theorem one_le_l2Norm_sq_schurLift (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ)
    (hv : l2Norm v = 1) : 1 ≤ l2Norm (schurLift p i ω.1 ω.2.1 E v) ^ 2 := by
  rw [← clockSpeed_eq_l2Norm_sq, clockSpeed, physicalCoareaD, schurClock,
    Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    re_star_dotProduct_self, re_star_dotProduct_self]
  have hv2 : ∑ k, ‖v k‖ ^ 2 = 1 := by
    have h0 : 0 ≤ ∑ k, ‖v k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    have := Real.sq_sqrt h0
    rw [← l2Norm, hv] at this
    linarith
  have : 0 ≤ ∑ k, ‖(physicalCoareaT ω.1 ω.2.1 E *ᵥ v) k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  linarith

/-- On the support of the fiber density the crossing speed times the pair mass of the
reconstructed matrix is one. -/
theorem clockSpeed_mul_pairMass (α : Fin p.N)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian) (E : ℝ)
    (v : PairSite p i → ℂ) (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ)
    (hG' : G'.IsHermitian) (hv : l2Norm v = 1) (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0)
    (hM : (frameM p i U ω E v G').det ≠ 0)
    (hcnt : negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val) :
    clockSpeed p i ω E v * pairMass p i α (assemble p i ω (reconstructedGaussian p i U ω E v G'))
      = 1 := by
  have hH := ContractClauses.assemble_isHermitian p i ω _ h1 h3
    (reconstructedGaussian_isHermitian p i U ω h1 h3 E v G' hG')
  obtain ⟨-, hproj⟩ := ClockRank.coarea_reconstructed_rank p α i U hU ω E v G' hH hv hD hM hcnt
  set L := schurLift p i ω.1 ω.2.1 E v
  set H := assemble p i ω (reconstructedGaussian p i U ω E v G')
  have hpair := ClockRank.schurLift_pair p i ω.1 ω.2.1 E v
  have hv2 : ∑ k, ‖v k‖ ^ 2 = 1 := by
    have h0 : 0 ≤ ∑ k, ‖v k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    have := Real.sq_sqrt h0
    rw [← l2Norm, hv] at this
    linarith
  have hpt : ∀ x, ‖physicalOrderedEigenvector p H α x‖ ^ 2 = (l2Norm L ^ 2)⁻¹ * ‖L x‖ ^ 2 := by
    intro x
    have h := congrArg Complex.re (hproj x x)
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, Complex.ofReal_re] at h
    rw [h]
    norm_cast
  have hm : pairMass p i α H = (l2Norm L ^ 2)⁻¹ := by
    rw [ClockRank.pairMass_eq]
    simp_rw [hpt]
    rw [← Finset.mul_sum]
    have : ∑ s : PairSite p i, ‖L s.1‖ ^ 2 = 1 := by
      rw [← hv2]
      exact Finset.sum_congr rfl fun s _ => by rw [← congrFun hpair s]
    rw [this, mul_one]
  have hpos : l2Norm L ^ 2 ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_l2Norm_sq_schurLift p i ω E v hv)).ne'
  rw [hm, clockSpeed_eq_l2Norm_sq, mul_inv_cancel₀ hpos]

/-- The pair `S` is nonempty (`W ≥ 1`). -/
theorem nonempty_pairSite : Nonempty (PairSite p i) :=
  ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩

/-- Fixed-`ω` replacement of the crossing speed `v*𝒟v` by `n/2` against the pair weight. -/
theorem coareaFiber_pairWeight (α : Fin p.N) (s : ℝ)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian)
    (g : PairMatrix p i → ℝ≥0∞) :
    coareaFiber p α i s U (clockSpeed p i) ω
        (fun G => ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i ω G)) * g G) =
      coareaFiber p α i s U (fun _ _ _ => (p.n : ℝ) / 2) ω g := by
  have := nonempty_pairSite p i
  unfold coareaFiber
  refine lintegral_congr_ae ?_
  filter_upwards [ae_det_shift_ne_zero p i ω.1] with E hE
  refine lintegral_congr_ae ?_
  filter_upwards [ProjectiveHaar.ae_l2Norm_projectiveHaar (PairSite p i)] with v hv
  refine lintegral_congr_ae ?_
  filter_upwards [GUELaw.ae_isHermitian_gueMeasure (ι := FrameIndex p) (pairTime p s)] with G' hG'
  by_cases hM : (frameM p i U ω E v G').det = 0
  · simp [hM]
  by_cases hc : negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
  · have key := clockSpeed_mul_pairMass p i α U hU ω h1 h3 E v G' hG' hv hE hM hc
    have hm0 : 0 ≤ (p.n : ℝ) / 2 *
        pairMass p i α (assemble p i ω (reconstructedGaussian p i U ω E v G')) :=
      mul_nonneg (by positivity) (add_nonneg (physicalOrderedBlockMass_nonneg _ _ _ _)
        (physicalOrderedBlockMass_nonneg _ _ _ _))
    simp only [hc, ↓reduceIte, mul_one]
    rw [← mul_assoc, ← ENNReal.ofReal_mul' hm0]
    congr 2
    linear_combination (coareaConstant (2 * p.W) (pairTime p s) *
        regressionFactor (pairTime p s) E v (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) *
        Complex.normSq (frameM p i U ω E v G').det * ((p.n : ℝ) / 2)) * key
  · simp only [hc, ↓reduceIte, mul_zero, zero_mul]

end Lemmas

/-!
## The four reductions
-/

/-- `CoareaContract.formula` from `formula_fixed` (Tonelli). -/
theorem coarea_formula_of_fixed (hfix : FormulaFixedStatement) :
    ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n)
    (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ U, IsPairFrame p i U →
    ∀ Φ : SplitState p i → PairMatrix p i → ℝ≥0∞, Measurable (Function.uncurry Φ) →
      (∫⁻ x, Φ x.1 x.2 ∂(Pω.prod (gueMeasure (PairSite p i) (pairTime p s)))) =
        coareaRHS p α i s Pω U (clockSpeed p i) Φ := by
  intro p model α i s hs hsc Pω hP U hU Φ hΦ
  rw [lintegral_prod (fun x => Φ x.1 x.2) hΦ.aemeasurable, coareaRHS]
  refine lintegral_congr_ae ?_
  filter_upwards [hfix p model α i s hs hsc Pω hP U hU] with ω hω
  exact hω (Φ ω) (hΦ.comp measurable_prodMk_left)

/-- `CoareaContract.mass_one` from `formula_fixed`. -/
theorem coarea_mass_one_of_fixed (hfix : FormulaFixedStatement) :
    ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n)
    (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ U, IsPairFrame p i U → coareaRHS p α i s Pω U (clockSpeed p i) (fun _ _ => 1) = 1 := by
  intro p model α i s hs hsc Pω hP U hU
  rw [← coarea_formula_of_fixed hfix p model α i s hs hsc Pω hP U hU (fun _ _ => 1)
    measurable_const, lintegral_one]
  have h := congrArg (fun μ : Measure p.SiteMatrix => μ Set.univ) hP
  rw [Measure.map_apply (ContractClauses.measurable_assemble p i) MeasurableSet.univ,
    Set.preimage_univ] at h
  rw [h]
  exact measure_univ

/-- `CoareaContract.pairLaw_formula` from `formula_fixed`. -/
theorem coarea_pairLaw_formula_of_fixed (hfix : FormulaFixedStatement) :
    ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (i : ZMod p.n) (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ U, IsPairFrame p i U →
    ∀ Φ : SplitState p i → PairMatrix p i → ℝ≥0∞, Measurable (Function.uncurry Φ) →
      (∫⁻ x, ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2)) *
          Φ x.1 x.2 ∂(Pω.prod (gueMeasure (PairSite p i) (pairTime p s)))) =
        coareaRHS p α i s Pω U (fun _ _ _ => (p.n : ℝ) / 2) Φ := by
  intro p model α i s hs hsc Pω hP U hU Φ hΦ
  have hw : Measurable (fun x : SplitState p i × PairMatrix p i =>
      ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (((measurable_physicalOrderedBlockMass p α i).add
        (measurable_physicalOrderedBlockMass p α (i + 1))).comp
          (ContractClauses.measurable_assemble p i)))
  rw [coarea_formula_of_fixed hfix p model α i s hs hsc Pω hP U hU
    (fun ω G => ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i ω G)) * Φ ω G)
    (hw.mul hΦ), coareaRHS, coareaRHS]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_split_isHermitian p i model s Pω hP] with ω hω
  exact coareaFiber_pairWeight p i α s U hU ω hω.1 hω.2 (Φ ω)

/-- `CoareaContract.pairLaw_measure` from `formula_fixed`. -/
theorem coarea_pairLaw_measure_of_fixed (hfix : FormulaFixedStatement) :
    ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (i : ZMod p.n) (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ U, IsPairFrame p i U →
    ∀ Φ₀ : p.SiteMatrix → ℝ≥0∞, Measurable Φ₀ →
      (∫⁻ H, Φ₀ H ∂physicalPairMeasure p model α i) =
        coareaRHS p α i s Pω U (fun _ _ _ => (p.n : ℝ) / 2)
          (fun ω G => Φ₀ (assemble p i ω G)) := by
  intro p model α i s hs hsc Pω hP U hU Φ₀ hΦ₀
  have hwt : Measurable (fun H => (physicalPairWeight p α i H : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (measurable_physicalPairWeight p α i)
  rw [← coarea_pairLaw_formula_of_fixed hfix p model α i s hs hsc Pω hP U hU
    (fun ω G => Φ₀ (assemble p i ω G)) (hΦ₀.comp (ContractClauses.measurable_assemble p i)),
    physicalPairMeasure, lintegral_withDensity_eq_lintegral_mul _ hwt hΦ₀, ← hP,
    lintegral_map (hwt.mul hΦ₀) (ContractClauses.measurable_assemble p i)]
  refine lintegral_congr fun x => ?_
  rw [Pi.mul_apply, ← ENNReal.ofReal_coe_nnreal]
  rfl

/-- The whole `CoareaContract` from `formula_fixed` and the proved clauses. -/
theorem coareaContract_of_formulaFixed (hfix : FormulaFixedStatement) : CoareaContract where
  splitting_exists := ContractClauses.coarea_splitting_exists
  frame_exists := ContractClauses.coarea_frame_exists
  clock := ClockRank.coarea_clock
  regular_ae := RegularAE.coarea_regular_ae
  formula := coarea_formula_of_fixed hfix
  formula_fixed := hfix
  mass_one := coarea_mass_one_of_fixed hfix
  reconstructed_rank := ClockRank.coarea_reconstructed_rank
  pairLaw_probability := ContractClauses.coarea_pairLaw_probability
  pairLaw_formula := coarea_pairLaw_formula_of_fixed hfix
  pairLaw_measure := coarea_pairLaw_measure_of_fixed hfix

end BlockBand.Coarea.CoareaAssembly
