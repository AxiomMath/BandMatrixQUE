module

public import BlockBand.Endpoints.Normalization.ExactPalm

/-!
# The exact-Palm proposition, clauses `massReal` and `indexReal`, from the coarea theorem

The signed `massReal` and `indexReal` fields of `Clocks.ExactPalmContract` follow from
`CoareaContract`, with no other input: apply the identities to nonnegative functions, then
subtract their positive and negative parts. The clauses used are those of the nonnegative forms
(`formula_fixed`, `formula`, `reconstructed_rank`), through `exactPalm_mass_of_coarea`,
`exactPalm_index_of_coarea` and the fixed-`ω` fiber identities below. The assembly into
`Clocks.ExactPalmContract` is `exactPalmContract_holds`; the `upper` field is proved separately (`exactPalm_upper_of`).

Proof. Measures: the exact physical law on the left; `Pω`, Lebesgue `de`, `projectiveHaar` and
`GUE_{2W-1}(t)` on the right. Write `f = f⁺ - f⁻`, `f^± = max(±f, 0)`, and apply the `[0,∞]`
identities to `ofReal ∘ f^±`. Finiteness: `|f| ≤ M` and the pair masses are `≤ 2` almost surely
(each block mass is at most the total mass one), so the left sides are at most `2NM` (`mass`)
and `M` (`index`); by the identities the right sides are finite too. A real Bochner integral
of `toReal A - toReal B` with `A, B ≥ 0` a.e.-measurable of finite lower integral is the
difference of the lower integrals (`integral_toReal_sub_toReal`); this is applied at each
nesting level (`integral_integral_eq_toReal_sub`): `(ω, e)` outside, `(v, G')` inside the angular
fiber (`pairSectorFiberReal_eq_toReal_sub`). Finiteness in the outer variables holds almost
everywhere, which is enough. The `ω`-measurability of the energy integral is obtained from its
almost-sure equality with `ω ↦ ∫ dGUE(G) Φ(assemble ω G)`, a section of a jointly measurable
function (`massFiber_ae`, `indexFiber_ae`, from `formula_fixed`). The compact energy support
is not needed for these exact identities (boundedness suffices).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexConjugate

/-!
## Signed integrals from lower integrals
-/

section Abstract

/-- `∫ (A.toReal - B.toReal) = (∫⁻ A).toReal - (∫⁻ B).toReal` for a.e.-measurable `A, B ≥ 0`
of finite lower integral. -/
theorem integral_toReal_sub_toReal {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {A B : X → ℝ≥0∞} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    (hAf : ∫⁻ x, A x ∂μ ≠ ∞) (hBf : ∫⁻ x, B x ∂μ ≠ ∞) :
    ∫ x, ((A x).toReal - (B x).toReal) ∂μ =
      (∫⁻ x, A x ∂μ).toReal - (∫⁻ x, B x ∂μ).toReal := by
  rw [integral_sub (integrable_toReal_of_lintegral_ne_top hA hAf)
    (integrable_toReal_of_lintegral_ne_top hB hBf),
    integral_toReal hA (ae_lt_top' hA hAf), integral_toReal hB (ae_lt_top' hB hBf)]

/-- Two nested levels: if, for a.e. `x` and a.e. `y`, `φ x y = (A x y).toReal - (B x y).toReal`
whenever both are finite, then `∫∫ φ` is the difference of the nested lower integrals of `A`
and `B` (a.e.-measurability at both levels, finite total lower integrals). -/
theorem integral_integral_eq_toReal_sub {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (φ : X → Y → ℝ) (A B : X → Y → ℝ≥0∞)
    (hAi : ∀ᵐ x ∂μ, AEMeasurable (A x) ν) (hBi : ∀ᵐ x ∂μ, AEMeasurable (B x) ν)
    (hAo : AEMeasurable (fun x => ∫⁻ y, A x y ∂ν) μ)
    (hBo : AEMeasurable (fun x => ∫⁻ y, B x y ∂ν) μ)
    (hAf : ∫⁻ x, ∫⁻ y, A x y ∂ν ∂μ ≠ ∞) (hBf : ∫⁻ x, ∫⁻ y, B x y ∂ν ∂μ ≠ ∞)
    (hφ : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, A x y ≠ ∞ → B x y ≠ ∞ →
      φ x y = (A x y).toReal - (B x y).toReal) :
    ∫ x, ∫ y, φ x y ∂ν ∂μ =
      (∫⁻ x, ∫⁻ y, A x y ∂ν ∂μ).toReal - (∫⁻ x, ∫⁻ y, B x y ∂ν ∂μ).toReal := by
  rw [← integral_toReal_sub_toReal hAo hBo hAf hBf]
  refine integral_congr_ae ?_
  filter_upwards [hAi, hBi, ae_lt_top' hAo hAf, ae_lt_top' hBo hBf, hφ]
    with x hAx hBx hAx' hBx' hφx
  rw [← integral_toReal_sub_toReal hAx hBx hAx'.ne hBx'.ne]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top' hAx hAx'.ne, ae_lt_top' hBx hBx'.ne, hφx] with y h1 h2 h3
  exact h3 h1.ne h2.ne

/-- Finite sums: `Σ r = (Σ a).toReal - (Σ b).toReal` when the sums are finite and termwise
`r = a.toReal - b.toReal` for finite terms. -/
theorem sum_eq_toReal_sub {ι : Type*} (s : Finset ι) (a b : ι → ℝ≥0∞) (r : ι → ℝ)
    (ha : ∑ ℓ ∈ s, a ℓ ≠ ∞) (hb : ∑ ℓ ∈ s, b ℓ ≠ ∞)
    (h : ∀ ℓ ∈ s, a ℓ ≠ ∞ → b ℓ ≠ ∞ → r ℓ = (a ℓ).toReal - (b ℓ).toReal) :
    ∑ ℓ ∈ s, r ℓ = (∑ ℓ ∈ s, a ℓ).toReal - (∑ ℓ ∈ s, b ℓ).toReal := by
  have ha' : ∀ ℓ ∈ s, a ℓ ≠ ∞ := fun ℓ hℓ =>
    ne_top_of_le_ne_top ha (Finset.single_le_sum (fun _ _ => bot_le) hℓ)
  have hb' : ∀ ℓ ∈ s, b ℓ ≠ ∞ := fun ℓ hℓ =>
    ne_top_of_le_ne_top hb (Finset.single_le_sum (fun _ _ => bot_le) hℓ)
  rw [ENNReal.toReal_sum ha', ENNReal.toReal_sum hb', ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ℓ hℓ => h ℓ hℓ (ha' ℓ hℓ) (hb' ℓ hℓ)

/-- Positive and negative parts: `max x 0 - max (-x) 0 = x`. -/
theorem max_zero_sub_max_neg_zero (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

theorem max_zero_le_of_abs_le {x M : ℝ} (h : |x| ≤ M) : max x 0 ≤ M :=
  max_le ((le_abs_self x).trans h) ((abs_nonneg x).trans h)

theorem max_neg_zero_le_of_abs_le {x M : ℝ} (h : |x| ≤ M) : max (-x) 0 ≤ M :=
  max_le ((neg_le_abs x).trans h) ((abs_nonneg x).trans h)

end Abstract

/-!
## The signed angular fiber
-/

section Fiber

variable (p : Parameters) (i : ZMod p.n)

/-- **Signed angular fiber.** For `g = h⁺ - h⁻` with `h^± ≥ 0` measurable and finite angular
masses `𝒜_{ℓ,e}[h^±]`, the Bochner fiber `pairSectorFiberReal` (`𝒜_{ℓ,e}[g]`) is
`𝒜_{ℓ,e}[h⁺].toReal - 𝒜_{ℓ,e}[h⁻].toReal`. Measures `projectiveHaar` and `GUE_{2W-1}(t)`;
every exterior `ω`, energy `e`, sector `ℓ` and measurable frame. -/
theorem pairSectorFiberReal_eq_toReal_sub
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : Measurable U)
    (ω : SplitState p i) (e : ℝ) (ℓ : ℕ) (g hp hm : (PairSite p i → ℂ) → ℝ)
    (hpm : Measurable hp) (hmm : Measurable hm) (hp0 : ∀ v, 0 ≤ hp v) (hm0 : ∀ v, 0 ≤ hm v)
    (hg : ∀ v, g v = hp v - hm v)
    (hpf : pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (hp v)) ≠ ∞)
    (hmf : pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (hm v)) ≠ ∞) :
    pairSectorFiberReal p i U ω e ℓ g =
      (pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (hp v))).toReal -
        (pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (hm v))).toReal := by
  have hmeas : ∀ h : (PairSite p i → ℂ) → ℝ, Measurable h →
      Measurable fun q : (PairSite p i → ℂ) × Matrix (FrameIndex p) (FrameIndex p) ℂ =>
        ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
            regressionFactor (pairTime p (pairS p)) e q.1
              (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) *
            Complex.normSq (frameM p i U ω e q.1 q.2).det) *
          (if negativeCount (frameM p i U ω e q.1 q.2) = ℓ then 1 else 0) *
          ENNReal.ofReal (h q.1) := by
    intro h hh
    have hg : Measurable (Function.uncurry fun (_ : ℝ) (v : PairSite p i → ℂ) =>
        ENNReal.ofReal (h v)) := ENNReal.measurable_ofReal.comp (hh.comp measurable_snd)
    have h1 := measurable_sectorIntegrand p i U hU ω ℓ (fun _ v => ENNReal.ofReal (h v)) hg
    have h2 : Measurable fun q : (PairSite p i → ℂ) × Matrix (FrameIndex p) (FrameIndex p) ℂ =>
        ((e, q.1), q.2) := (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    have h3 := h1.comp h2
    simp only [Function.comp_def] at h3
    exact h3
  unfold pairSectorFiber at hpf hmf
  unfold pairSectorFiber pairSectorFiberReal
  refine integral_integral_eq_toReal_sub _
    (fun v G' => ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
            regressionFactor (pairTime p (pairS p)) e v (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) *
            Complex.normSq (frameM p i U ω e v G').det) *
          (if negativeCount (frameM p i U ω e v G') = ℓ then 1 else 0) * ENNReal.ofReal (hp v))
    (fun v G' => ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
            regressionFactor (pairTime p (pairS p)) e v (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) *
            Complex.normSq (frameM p i U ω e v G').det) *
          (if negativeCount (frameM p i U ω e v G') = ℓ then 1 else 0) * ENNReal.ofReal (hm v))
    (ae_of_all _ fun v => ((hmeas hp hpm).comp measurable_prodMk_left).aemeasurable)
    (ae_of_all _ fun v => ((hmeas hm hmm).comp measurable_prodMk_left).aemeasurable)
    (hmeas hp hpm).lintegral_prod_right'.aemeasurable
    (hmeas hm hmm).lintegral_prod_right'.aemeasurable hpf hmf
    (ae_of_all _ fun v => ae_of_all _ fun G' => fun _ _ => ?_)
  have hw : 0 ≤ coareaConstant (2 * p.W) (pairTime p (pairS p)) *
      regressionFactor (pairTime p (pairS p)) e v (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) *
      Complex.normSq (frameM p i U ω e v G').det :=
    mul_nonneg (coareaConstant_mul_regression_nonneg p i _ e v _) (Complex.normSq_nonneg _)
  rw [hg v]
  split_ifs
  · simp only [mul_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hw,
      ENNReal.toReal_ofReal (hp0 v), ENNReal.toReal_ofReal (hm0 v)]
    ring
  · simp only [mul_zero, zero_mul, ENNReal.toReal_zero, sub_zero]

end Fiber

/-!
## The fixed-`ω` fibers (for measurability in `ω`)
-/

section FixedOmega

/-- Fixed-`ω` form of the mass Palm identity (from `CoareaContract.formula_fixed` and
`reconstructed_rank`): for `Pω`-a.e. `ω`, `∫ dGUE(G) Σ_α q_{αS} f(λ_α, p_α)(assemble ω G)` is the
energy integral of the angular sector masses. Same steps as `exactPalm_mass_of_coarea`. -/
theorem massFiber_ae (hC : CoareaContract) (p : Parameters) (model : p.GaussianRingModel)
    (i : ZMod p.n) (Pω : Measure (SplitState p i)) (hP : IsPairSplitting p i model (pairS p) Pω)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    ∀ᵐ ω ∂Pω, (∫⁻ G, ∑ α : Fin p.N, ENNReal.ofReal (pairMass p i α (assemble p i ω G)) *
        f (physicalOrderedEigenvalue p (assemble p i ω G) α)
          (blockMassVector p (assemble p i ω G) α)
        ∂(gueMeasure (PairSite p i) (pairTime p (pairS p)))) =
      ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)) := by
  have hA := ContractClauses.measurable_assemble p i
  have hobsα : ∀ α : Fin p.N, Measurable fun H : p.SiteMatrix =>
      ENNReal.ofReal (pairMass p i α H) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) := fun α =>
    (ENNReal.measurable_ofReal.comp ((measurable_physicalOrderedBlockMass p α i).add
      (measurable_physicalOrderedBlockMass p α (i + 1)))).mul
      (hf.comp ((measurable_physicalOrderedEigenvalue p α).prodMk
        (Measurable.of_eval fun k => measurable_physicalOrderedBlockMass p α k)))
  filter_upwards [ae_split_isHermitian p i model (pairS p) Pω hP,
    ae_all_iff.2 fun α : Fin p.N =>
      hC.formula_fixed p model α i (pairS p) (pairS_pos p) (pairS_le p) Pω hP U hU]
    with ω hω hfix
  have hAω : Measurable fun G : PairMatrix p i => assemble p i ω G :=
    hA.comp measurable_prodMk_left
  rw [lintegral_finsetSum Finset.univ (f := fun (α : Fin p.N) (G : PairMatrix p i) =>
      ENNReal.ofReal (pairMass p i α (assemble p i ω G)) *
        f (physicalOrderedEigenvalue p (assemble p i ω G) α)
          (blockMassVector p (assemble p i ω G) α)) fun α _ => (hobsα α).comp hAω]
  have hfib : ∀ α : Fin p.N,
      (∫⁻ G, ENNReal.ofReal (pairMass p i α (assemble p i ω G)) *
        f (physicalOrderedEigenvalue p (assemble p i ω G) α)
          (blockMassVector p (assemble p i ω G) α)
        ∂(gueMeasure (PairSite p i) (pairTime p (pairS p)))) =
      ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)) := by
    intro α
    refine (hfix α _ ((hobsα α).comp hAω)).trans ?_
    refine coareaFiber_eq_sector p i α U ω _ (fun e v => f e (reconBlockMass p i ω e v))
      fun E hE v hv G' hG' => ?_
    exact mass_integrand p i hC α U hU ω hω.1 hω.2 E hE v hv G' hG' _
      (coareaConstant_mul_regression_nonneg p i _ E v _) f
  rw [Finset.sum_congr rfl fun α _ => hfib α]
  have hgm : Measurable (Function.uncurry fun (e : ℝ) (v : PairSite p i → ℂ) =>
      f e (reconBlockMass p i ω e v)) :=
    hf.comp (measurable_fst.prodMk (measurable_reconBlockMass_joint p i ω))
  have hfibm : ∀ ℓ, Measurable fun e : ℝ =>
      pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)) := fun ℓ =>
    measurable_pairSectorFiber p i U hU.1 ω ℓ (fun e v => f e (reconBlockMass p i ω e v)) hgm
  have hNR : Measurable fun e : ℝ => negativeCount (ω.1 - (e : ℂ) • 1) :=
    (FixedOmega.measurable_negativeCount _).comp (measurable_shift p i ω.1)
  rw [← lintegral_finsetSum Finset.univ (f := fun (α : Fin p.N) (e : ℝ) =>
      ∑ ℓ ∈ Finset.range (2 * p.W),
        (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)))
    fun α _ => Finset.measurable_sum _ fun ℓ _ =>
      (Measurable.ite (measurableSet_eq_fun (hNR.const_add ℓ) measurable_const)
        measurable_const measurable_const).mul (hfibm ℓ)]
  refine lintegral_congr fun e => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [← Finset.sum_mul, sum_rank_indicator p i _ ℓ (Finset.mem_range.1 hℓ), one_mul]

/-- Fixed-`ω` form of the index Palm identity (from `CoareaContract.formula_fixed` and
`reconstructed_rank`): for `Pω`-a.e. `ω`, `∫ dGUE(G) f(λ_α, p_α)(assemble ω G)` is the energy
integral of the rank-`α` sector masses with speed `v*Dv`. -/
theorem indexFiber_ae (hC : CoareaContract) (p : Parameters) (model : p.GaussianRingModel)
    (i : ZMod p.n) (Pω : Measure (SplitState p i)) (hP : IsPairSplitting p i model (pairS p) Pω)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (α : Fin p.N) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    ∀ᵐ ω ∂Pω, (∫⁻ G, f (physicalOrderedEigenvalue p (assemble p i ω G) α)
          (blockMassVector p (assemble p i ω G) α)
        ∂(gueMeasure (PairSite p i) (pairTime p (pairS p)))) =
      ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          pairSectorFiber p i U ω e ℓ
            (fun v => ENNReal.ofReal (clockSpeed p i ω e v) * f e (reconBlockMass p i ω e v)) := by
  have hA := ContractClauses.measurable_assemble p i
  have hobs : Measurable fun H : p.SiteMatrix =>
      f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) :=
    hf.comp ((measurable_physicalOrderedEigenvalue p α).prodMk
      (Measurable.of_eval fun k => measurable_physicalOrderedBlockMass p α k))
  filter_upwards [ae_split_isHermitian p i model (pairS p) Pω hP,
      hC.formula_fixed p model α i (pairS p) (pairS_pos p) (pairS_le p) Pω hP U hU]
    with ω hω hfix
  rw [hfix (fun G => f (physicalOrderedEigenvalue p (assemble p i ω G) α)
      (blockMassVector p (assemble p i ω G) α)) (hobs.comp (hA.comp measurable_prodMk_left))]
  refine coareaFiber_eq_sector p i α U ω _ _ fun E hE v hv G' hG' => ?_
  exact index_integrand p i hC α U hU ω hω.1 hω.2 E hE v hv G' hG' _
    (coareaConstant_mul_regression_nonneg p i _ E v _) f

end FixedOmega

/-!
## Helper facts for the signed clauses
-/

section Helpers

/-- Positive and negative parts of a bounded measurable real observable. -/
theorem signedParts {ι : Type*} [MeasurableSpace ι] (f : ℝ → ι → ℝ)
    (hf : Measurable (Function.uncurry f)) (M : ℝ) (hM : ∀ e x, |f e x| ≤ M) :
    ∃ fp fm : ℝ → ι → ℝ, (∀ e x, 0 ≤ fp e x) ∧ (∀ e x, 0 ≤ fm e x) ∧
      (∀ e x, fp e x ≤ M) ∧ (∀ e x, fm e x ≤ M) ∧ (∀ e x, f e x = fp e x - fm e x) ∧
      Measurable (Function.uncurry fp) ∧ Measurable (Function.uncurry fm) :=
  ⟨fun e x => max (f e x) 0, fun e x => max (-f e x) 0, fun _ _ => le_max_right _ _,
    fun _ _ => le_max_right _ _, fun e x => max_zero_le_of_abs_le (hM e x),
    fun e x => max_neg_zero_le_of_abs_le (hM e x),
    fun e x => (max_zero_sub_max_neg_zero (f e x)).symm,
    hf.max measurable_const, hf.neg.max measurable_const⟩

variable (p : Parameters) (i : ZMod p.n)

theorem pairMass_nonneg (α : Fin p.N) (H : p.SiteMatrix) : 0 ≤ pairMass p i α H :=
  add_nonneg (physicalOrderedBlockMass_nonneg p H α i)
    (physicalOrderedBlockMass_nonneg p H α (i + 1))

/-- Pair masses are at most `2` almost surely (each block mass is at most the total mass one). -/
theorem pairMass_le_two_ae (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ α : Fin p.N, pairMass p i α H ≤ 2 := by
  filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH α
  have hle : ∀ k, physicalOrderedBlockMass p H α k ≤ 1 := fun k => by
    rw [← hH α]
    exact Finset.single_le_sum (fun j _ => physicalOrderedBlockMass_nonneg p H α j)
      (Finset.mem_univ k)
  unfold pairMass
  linarith [hle i, hle (i + 1)]

/-- `H ↦ (λ_α(H), p_α(H))` is measurable. -/
theorem measurable_rankMarks (α : Fin p.N) :
    Measurable fun H : p.SiteMatrix =>
      (physicalOrderedEigenvalue p H α, blockMassVector p H α) :=
  (measurable_physicalOrderedEigenvalue p α).prodMk
    (Measurable.of_eval fun k => measurable_physicalOrderedBlockMass p α k)

/-- The `mass` observable `Σ_α q_{αS} g(λ_α, p_α)` (with `ofReal ∘ g`) is measurable. -/
theorem measurable_massObs (g : ℝ → (ZMod p.n → ℝ) → ℝ) (hg : Measurable (Function.uncurry g)) :
    Measurable fun H : p.SiteMatrix => ∑ α : Fin p.N, ENNReal.ofReal (pairMass p i α H) *
      ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) :=
  Finset.measurable_sum _ fun α _ =>
    (ENNReal.measurable_ofReal.comp ((measurable_physicalOrderedBlockMass p α i).add
      (measurable_physicalOrderedBlockMass p α (i + 1)))).mul
      (ENNReal.measurable_ofReal.comp (hg.comp (measurable_rankMarks p α)))

/-- Finiteness of the `mass` left side for `0 ≤ g ≤ M`: at most `Σ_α 2M` (pair masses `≤ 2`
a.s., probability law). -/
theorem massObs_lintegral_ne_top (model : p.GaussianRingModel) (g : ℝ → (ZMod p.n → ℝ) → ℝ)
    (M : ℝ) (hgM : ∀ e x, g e x ≤ M) :
    (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (pairMass p i α H) *
      ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
      ∂(model.law : Measure p.SiteMatrix)) ≠ ∞ := by
  have hle : (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (pairMass p i α H) *
      ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
      ∂(model.law : Measure p.SiteMatrix)) ≤
      ∫⁻ _H, ∑ _α : Fin p.N, ENNReal.ofReal 2 * ENNReal.ofReal M
        ∂(model.law : Measure p.SiteMatrix) := by
    refine lintegral_mono_ae ?_
    filter_upwards [pairMass_le_two_ae p i model] with H hH
    exact Finset.sum_le_sum fun α _ =>
      mul_le_mul' (ENNReal.ofReal_le_ofReal (hH α)) (ENNReal.ofReal_le_ofReal (hgM _ _))
  refine ne_top_of_le_ne_top ?_ hle
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top

/-- `v ↦ g(e, p(v,e))` is measurable. -/
theorem measurable_section_recon (ω : SplitState p i) (e : ℝ) (g : ℝ → (ZMod p.n → ℝ) → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    Measurable fun v : PairSite p i → ℂ => g e (reconBlockMass p i ω e v) := by
  have h1 := hg.comp (measurable_fst.prodMk (measurable_reconBlockMass_joint p i ω))
  have h2 := h1.comp (measurable_prodMk_left (x := e))
  simp only [Function.comp_def] at h2
  exact h2

/-- `(e, v) ↦ ofReal(g(e, p(v,e)))` is measurable. -/
theorem measurable_ofReal_recon (ω : SplitState p i) (g : ℝ → (ZMod p.n → ℝ) → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry fun (e : ℝ) (v : PairSite p i → ℂ) =>
      ENNReal.ofReal (g e (reconBlockMass p i ω e v))) :=
  ENNReal.measurable_ofReal.comp
    (hg.comp (measurable_fst.prodMk (measurable_reconBlockMass_joint p i ω)))

/-- `e ↦ Σ_ℓ 𝒜_{ℓ,e}[ofReal ∘ g(e, p(·,e))]` is measurable. -/
theorem measurable_massSectorSum (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (hU : Measurable U) (ω : SplitState p i) (g : ℝ → (ZMod p.n → ℝ) → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    Measurable fun e : ℝ => ∑ ℓ ∈ Finset.range (2 * p.W),
      pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (g e (reconBlockMass p i ω e v))) :=
  Finset.measurable_sum _ fun ℓ _ => measurable_pairSectorFiber p i U hU ω ℓ _
    (measurable_ofReal_recon p i ω g hg)

/-- The energy integral of the `mass` sector sum is a.e.-measurable in `ω` (a.s. equal to
`ω ↦ ∫ dGUE(G) Σ_α q_{αS} g(λ_α, p_α)(assemble ω G)`, `massFiber_ae`). -/
theorem aemeasurable_massEnergy (hC : CoareaContract) (model : p.GaussianRingModel)
    (Pω : Measure (SplitState p i)) (hP : IsPairSplitting p i model (pairS p) Pω)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (g : ℝ → (ZMod p.n → ℝ) → ℝ) (hg : Measurable (Function.uncurry g)) :
    AEMeasurable (fun ω => ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
      pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (g e (reconBlockMass p i ω e v)))) Pω := by
  have hae := massFiber_ae hC p model i Pω hP U hU (fun e x => ENNReal.ofReal (g e x))
    (ENNReal.measurable_ofReal.comp hg)
  beta_reduce at hae
  have h1 := ((measurable_massObs p i g hg).comp
    (ContractClauses.measurable_assemble p i)).lintegral_prod_right'
    (ν := gueMeasure (PairSite p i) (pairTime p (pairS p)))
  simp only [Function.comp_def] at h1
  exact h1.aemeasurable.congr hae

/-- Finiteness of the `index` left side for `g ≤ M`: at most `M` (probability law). -/
theorem indexObs_lintegral_ne_top (model : p.GaussianRingModel) (α : Fin p.N)
    (g : ℝ → (ZMod p.n → ℝ) → ℝ) (M : ℝ) (hgM : ∀ e x, g e x ≤ M) :
    (∫⁻ H, ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
      ∂(model.law : Measure p.SiteMatrix)) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_
    (lintegral_mono fun H => ENNReal.ofReal_le_ofReal (hgM (physicalOrderedEigenvalue p H α)
      (blockMassVector p H α)))
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_ne_top

/-- `e ↦ Σ_ℓ 1{ℓ + N_-(H_R - e) = α} 𝒜_{ℓ,e}[(v*Dv) ofReal ∘ g(e, p(·,e))]` is measurable. -/
theorem measurable_indexSectorSum
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (hU : Measurable U) (ω : SplitState p i) (α : Fin p.N) (g : ℝ → (ZMod p.n → ℝ) → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    Measurable fun e : ℝ => ∑ ℓ ∈ Finset.range (2 * p.W),
      (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
      pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (clockSpeed p i ω e v) *
        ENNReal.ofReal (g e (reconBlockMass p i ω e v))) := by
  have hNR : Measurable fun e : ℝ => negativeCount (ω.1 - (e : ℂ) • 1) :=
    (FixedOmega.measurable_negativeCount _).comp (measurable_shift p i ω.1)
  have hgm : Measurable (Function.uncurry fun (e : ℝ) (v : PairSite p i → ℂ) =>
      ENNReal.ofReal (clockSpeed p i ω e v) * ENNReal.ofReal (g e (reconBlockMass p i ω e v))) :=
    (ENNReal.measurable_ofReal.comp (measurable_clockSpeed_joint p i ω)).mul
      (measurable_ofReal_recon p i ω g hg)
  exact Finset.measurable_sum _ fun ℓ _ =>
    (Measurable.ite (measurableSet_eq_fun (hNR.const_add ℓ) measurable_const)
      measurable_const measurable_const).mul (measurable_pairSectorFiber p i U hU ω ℓ _ hgm)

/-- The energy integral of the rank-`α` sector sum is a.e.-measurable in `ω` (a.s. equal to
`ω ↦ ∫ dGUE(G) g(λ_α, p_α)(assemble ω G)`, `indexFiber_ae`). -/
theorem aemeasurable_indexEnergy (hC : CoareaContract) (model : p.GaussianRingModel)
    (Pω : Measure (SplitState p i)) (hP : IsPairSplitting p i model (pairS p) Pω)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (α : Fin p.N) (g : ℝ → (ZMod p.n → ℝ) → ℝ) (hg : Measurable (Function.uncurry g)) :
    AEMeasurable (fun ω => ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
      (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
      pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (clockSpeed p i ω e v) *
        ENNReal.ofReal (g e (reconBlockMass p i ω e v)))) Pω := by
  have hae := indexFiber_ae hC p model i Pω hP U hU α (fun e x => ENNReal.ofReal (g e x))
    (ENNReal.measurable_ofReal.comp hg)
  beta_reduce at hae
  have hobs : Measurable fun H : p.SiteMatrix =>
      ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) :=
    ENNReal.measurable_ofReal.comp (hg.comp (measurable_rankMarks p α))
  have h1 := (hobs.comp (ContractClauses.measurable_assemble p i)).lintegral_prod_right'
    (ν := gueMeasure (PairSite p i) (pairTime p (pairS p)))
  simp only [Function.comp_def] at h1
  exact h1.aemeasurable.congr hae

end Helpers

/-!
## `massReal`
-/

/-- **The exact Palm formula, clause `massReal`** (for bounded measurable real `f` with compact
energy support), from `CoareaContract` (through `exactPalm_mass_of_coarea` and `massFiber_ae`:
`formula_fixed`, `reconstructed_rank`). Measures: the exact physical law on the left; `Pω`,
Lebesgue `de`, `projectiveHaar` and `GUE_{2W-1}(t)` on the right; Bochner integrals, all
integrands integrable.
Exact identity for every admissible `p`, model, pair and frame.
-/
theorem exactPalm_massReal_of_coarea (hC : CoareaContract) :
    ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
    (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
    ∀ U, IsPairFrame p i U → ∀ f : ℝ → (ZMod p.n → ℝ) → ℝ, Measurable (Function.uncurry f) →
      IsBoundedCompactEnergy f →
      (∫ H, ∑ α : Fin p.N, pairMass p i α H *
          f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫ ω, ∫ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          pairSectorFiberReal p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v))
        ∂volume ∂Pω := by
  intro p model i Pω hP U hU f hf hfb
  obtain ⟨⟨M, hM⟩, -⟩ := hfb
  obtain ⟨fp, fm, hfp0, hfm0, hfpM, hfmM, hsub, hfpm, hfmm⟩ := signedParts f hf M hM
  have hA := ContractClauses.measurable_assemble p i
  -- left side
  have hLHS : (∫ H, ∑ α : Fin p.N, pairMass p i α H *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (pairMass p i α H) *
          ENNReal.ofReal (fp (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
        ∂(model.law : Measure p.SiteMatrix)).toReal -
      (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (pairMass p i α H) *
          ENNReal.ofReal (fm (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
        ∂(model.law : Measure p.SiteMatrix)).toReal := by
    rw [← integral_toReal_sub_toReal (measurable_massObs p i fp hfpm).aemeasurable
      (measurable_massObs p i fm hfmm).aemeasurable (massObs_lintegral_ne_top p i model fp M hfpM)
      (massObs_lintegral_ne_top p i model fm M hfmM)]
    refine integral_congr_ae (ae_of_all _ fun H => ?_)
    have hfin : ∀ (g : ℝ → (ZMod p.n → ℝ) → ℝ), ∀ α ∈ (Finset.univ : Finset (Fin p.N)),
        ENNReal.ofReal (pairMass p i α H) *
          ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) ≠ ∞ :=
      fun g α _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    simp only
    rw [ENNReal.toReal_sum (hfin fp), ENNReal.toReal_sum (hfin fm), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pairMass_nonneg p i α H),
      ENNReal.toReal_ofReal (hfp0 _ _), ENNReal.toReal_ofReal (hfm0 _ _), hsub]
    ring
  -- the `[0,∞]` identities for `f^±`
  have hmp := exactPalm_mass_of_coarea hC p model i Pω hP U hU
    (fun e x => ENNReal.ofReal (fp e x)) (ENNReal.measurable_ofReal.comp hfpm)
  have hmm := exactPalm_mass_of_coarea hC p model i Pω hP U hU
    (fun e x => ENNReal.ofReal (fm e x)) (ENNReal.measurable_ofReal.comp hfmm)
  beta_reduce at hmp hmm
  rw [hLHS, hmp, hmm]
  symm
  refine integral_integral_eq_toReal_sub _
    (fun ω e => ∑ ℓ ∈ Finset.range (2 * p.W),
      pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (fp e (reconBlockMass p i ω e v))))
    (fun ω e => ∑ ℓ ∈ Finset.range (2 * p.W),
      pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (fm e (reconBlockMass p i ω e v))))
    (ae_of_all _ fun ω => (measurable_massSectorSum p i U hU.1 ω fp hfpm).aemeasurable)
    (ae_of_all _ fun ω => (measurable_massSectorSum p i U hU.1 ω fm hfmm).aemeasurable)
    (aemeasurable_massEnergy p i hC model Pω hP U hU fp hfpm)
    (aemeasurable_massEnergy p i hC model Pω hP U hU fm hfmm)
    (by rw [← hmp]; exact massObs_lintegral_ne_top p i model fp M hfpM)
    (by rw [← hmm]; exact massObs_lintegral_ne_top p i model fm M hfmM)
    (ae_of_all _ fun ω => ae_of_all _ fun e => fun hAe hBe => ?_)
  refine sum_eq_toReal_sub _ _ _ _ hAe hBe fun ℓ _ ha hb => ?_
  exact pairSectorFiberReal_eq_toReal_sub p i U hU.1 ω e ℓ _
    (fun v => fp e (reconBlockMass p i ω e v)) (fun v => fm e (reconBlockMass p i ω e v))
    (measurable_section_recon p i ω e fp hfpm) (measurable_section_recon p i ω e fm hfmm)
    (fun v => hfp0 _ _) (fun v => hfm0 _ _) (fun v => hsub _ _) ha hb

/-!
## `indexReal`
-/

/-- **The exact Palm formula, clause `indexReal`** (for bounded measurable real `f` with compact
energy support), from `CoareaContract` (through `exactPalm_index_of_coarea` and `indexFiber_ae`:
`formula`, `formula_fixed`, `reconstructed_rank`). Measures: the exact physical law on the left;
`Pω`, Lebesgue `de`, `projectiveHaar` and `GUE_{2W-1}(t)` on the right; Bochner integrals, all
integrands integrable.
Exact identity for every admissible `p`, model, pair, frame and rank.
-/
theorem exactPalm_indexReal_of_coarea (hC : CoareaContract) :
    ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
    (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
    ∀ U, IsPairFrame p i U → ∀ (α : Fin p.N) (f : ℝ → (ZMod p.n → ℝ) → ℝ),
      Measurable (Function.uncurry f) → IsBoundedCompactEnergy f →
      (∫ H, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫ ω, ∫ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          pairSectorFiberReal p i U ω e ℓ
            (fun v => clockSpeed p i ω e v * f e (reconBlockMass p i ω e v))
        ∂volume ∂Pω := by
  intro p model i Pω hP U hU α f hf hfb
  obtain ⟨⟨M, hM⟩, -⟩ := hfb
  obtain ⟨fp, fm, hfp0, hfm0, hfpM, hfmM, hsub, hfpm, hfmm⟩ := signedParts f hf M hM
  have hobs : ∀ g : ℝ → (ZMod p.n → ℝ) → ℝ, Measurable (Function.uncurry g) →
      Measurable fun H : p.SiteMatrix =>
        ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) :=
    fun g hg => ENNReal.measurable_ofReal.comp (hg.comp (measurable_rankMarks p α))
  -- left side
  have hLHS : (∫ H, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      (∫⁻ H, ENNReal.ofReal (fp (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
        ∂(model.law : Measure p.SiteMatrix)).toReal -
      (∫⁻ H, ENNReal.ofReal (fm (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
        ∂(model.law : Measure p.SiteMatrix)).toReal := by
    rw [← integral_toReal_sub_toReal (hobs fp hfpm).aemeasurable (hobs fm hfmm).aemeasurable
      (indexObs_lintegral_ne_top p model α fp M hfpM)
      (indexObs_lintegral_ne_top p model α fm M hfmM)]
    refine integral_congr_ae (ae_of_all _ fun H => ?_)
    simp only
    rw [ENNReal.toReal_ofReal (hfp0 _ _), ENNReal.toReal_ofReal (hfm0 _ _), hsub]
  -- the `[0,∞]` identities for `f^±`
  have hmp := exactPalm_index_of_coarea hC p model i Pω hP U hU α
    (fun e x => ENNReal.ofReal (fp e x)) (ENNReal.measurable_ofReal.comp hfpm)
  have hmm := exactPalm_index_of_coarea hC p model i Pω hP U hU α
    (fun e x => ENNReal.ofReal (fm e x)) (ENNReal.measurable_ofReal.comp hfmm)
  beta_reduce at hmp hmm
  rw [hLHS, hmp, hmm]
  symm
  refine integral_integral_eq_toReal_sub _
    (fun ω (e : ℝ) => ∑ ℓ ∈ Finset.range (2 * p.W),
      (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
      pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (clockSpeed p i ω e v) *
        ENNReal.ofReal (fp e (reconBlockMass p i ω e v))))
    (fun ω (e : ℝ) => ∑ ℓ ∈ Finset.range (2 * p.W),
      (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
      pairSectorFiber p i U ω e ℓ (fun v => ENNReal.ofReal (clockSpeed p i ω e v) *
        ENNReal.ofReal (fm e (reconBlockMass p i ω e v))))
    (ae_of_all _ fun ω => (measurable_indexSectorSum p i U hU.1 ω α fp hfpm).aemeasurable)
    (ae_of_all _ fun ω => (measurable_indexSectorSum p i U hU.1 ω α fm hfmm).aemeasurable)
    (aemeasurable_indexEnergy p i hC model Pω hP U hU α fp hfpm)
    (aemeasurable_indexEnergy p i hC model Pω hP U hU α fm hfmm)
    (by rw [← hmp]; exact indexObs_lintegral_ne_top p model α fp M hfpM)
    (by rw [← hmm]; exact indexObs_lintegral_ne_top p model α fm M hfmM)
    (ae_of_all _ fun ω => ae_of_all _ fun e => fun hAe hBe => ?_)
  refine sum_eq_toReal_sub _ _ _ _ hAe hBe fun ℓ _ ha hb => ?_
  by_cases hc : ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val
  · simp only [hc, ite_true, one_mul] at ha hb ⊢
    have hcs : ∀ g : ℝ → (ZMod p.n → ℝ) → ℝ, (∀ e x, 0 ≤ g e x) →
        (fun v => ENNReal.ofReal (clockSpeed p i ω e v) *
          ENNReal.ofReal (g e (reconBlockMass p i ω e v))) =
        fun v => ENNReal.ofReal (clockSpeed p i ω e v * g e (reconBlockMass p i ω e v)) :=
      fun g _ => funext fun v => (ENNReal.ofReal_mul (clockSpeed_nonneg p i ω e v)).symm
    rw [hcs fp hfp0] at ha ⊢
    rw [hcs fm hfm0] at hb ⊢
    have hcsm : Measurable fun v : PairSite p i → ℂ => clockSpeed p i ω e v := by
      have h1 := (measurable_clockSpeed_joint p i ω).comp (measurable_prodMk_left (x := e))
      simp only [Function.comp_def] at h1
      exact h1
    exact pairSectorFiberReal_eq_toReal_sub p i U hU.1 ω e ℓ _
      (fun v => clockSpeed p i ω e v * fp e (reconBlockMass p i ω e v))
      (fun v => clockSpeed p i ω e v * fm e (reconBlockMass p i ω e v))
      (hcsm.mul (measurable_section_recon p i ω e fp hfpm))
      (hcsm.mul (measurable_section_recon p i ω e fm hfmm))
      (fun v => mul_nonneg (clockSpeed_nonneg p i ω e v) (hfp0 _ _))
      (fun v => mul_nonneg (clockSpeed_nonneg p i ω e v) (hfm0 _ _))
      (fun v => by rw [hsub]; ring) ha hb
  · simp only [hc, ite_false, zero_mul, ENNReal.toReal_zero, sub_zero]

end BlockBand.Endpoints.Normalization
