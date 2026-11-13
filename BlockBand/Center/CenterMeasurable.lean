module

public import BlockBand.Center.CenterRegular
public import BlockBand.Layers.LayerMeasurability

/-!
# Borel measurability of the physical center on Hermitian inputs

The compressed resolvent, the residual, the clipped center formula and the set of Dyson roots
depend continuously or measurably on the input; on Hermitian inputs the root is unique on its
domain, so the center domain is a measurable set and the center is a Borel function.

This is the `measurable` field of `CenterDomainContract`, for every `cst : CenterDomainConstants`,
parameter set, rank and pair. Measure: Borel on `p.SiteMatrix × ℝ` (the entrywise Borel σ-algebra
times that of `ℝ`). The uniqueness of the Dyson root (`ctr_root_unique`) makes the projection
`(H, E, ζ) ↦ (H, E)` injective, and Lusin–Souslin gives measurability. No hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate

section Measurable

variable {p : Parameters} {i : ZMod p.n}

theorem ctr_matchedA_eq (E : ℝ) :
    matchedA E = ((-E / 2 : ℝ) : ℂ) + ((-Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [matchedA]

theorem ctr_continuous_matchedA : Continuous matchedA := by
  have h : matchedA = fun E : ℝ =>
      ((-E / 2 : ℝ) : ℂ) + ((-Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I :=
    funext ctr_matchedA_eq
  rw [h]
  fun_prop

/-- The full shifted matrix is continuous in `(H, E, ζ)`. -/
theorem ctr_continuous_ctrFull :
    Continuous (fun y : (p.SiteMatrix × ℝ) × ℂ => ctrFull p i y.1.1 y.1.2 y.2) := by
  unfold ctrFull
  fun_prop

/-- The compressed resolvent is Borel in `(H, E, ζ)` (totalized inverse). -/
theorem ctr_measurable_compressed :
    Measurable (fun y : (p.SiteMatrix × ℝ) × ℂ => compressedResolvent p i y.1.1 y.1.2 y.2) := by
  have hinv : Measurable (fun y : (p.SiteMatrix × ℝ) × ℂ => (ctrFull p i y.1.1 y.1.2 y.2)⁻¹) :=
    BlockBand.Layers.measurable_matrix_inv.comp ctr_continuous_ctrFull.measurable
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun z => ?_
  exact (measurable_pi_apply z.1).comp ((measurable_pi_apply x.1).comp hinv)

theorem ctr_continuous_pairBlockTrace (k : ZMod p.n) :
    Continuous (fun M : PairMatrix p i => pairBlockTrace p i M k) := by
  unfold pairBlockTrace
  refine continuous_const.mul (continuous_finsetSum _ fun x _ => ?_)
  split_ifs
  · exact (continuous_apply x).comp (continuous_apply x)
  · exact continuous_const

/-- The residual `ε_e` as a continuous function of the resolvent and the reference. -/
def ctrResidualOf (R : PairMatrix p i) (μ : ℂ) : ℝ :=
  Real.sqrt (‖pairBlockTrace p i R i - μ‖ ^ 2 + ‖pairBlockTrace p i R (i + 1) - μ‖ ^ 2)

theorem ctr_continuous_residualOf :
    Continuous (fun q : PairMatrix p i × ℂ => ctrResidualOf q.1 q.2) := by
  unfold ctrResidualOf
  have h1 : Continuous (fun q : PairMatrix p i × ℂ => pairBlockTrace p i q.1 i) :=
    (ctr_continuous_pairBlockTrace i).comp continuous_fst
  have h2 : Continuous (fun q : PairMatrix p i × ℂ => pairBlockTrace p i q.1 (i + 1)) :=
    (ctr_continuous_pairBlockTrace (i + 1)).comp continuous_fst
  exact Real.continuous_sqrt.comp
    (((h1.sub continuous_snd).norm.pow 2).add ((h2.sub continuous_snd).norm.pow 2))

theorem ctr_centerResidual_eq (Hres : p.SiteMatrix) (E : ℝ) :
    centerResidual p i Hres E = ctrResidualOf
      (compressedResolvent p i Hres E ((splitS p : ℂ) * conj (matchedA E))) (conj (matchedA E)) :=
  rfl

theorem ctr_measurable_centerResidual :
    Measurable (fun x : p.SiteMatrix × ℝ => centerResidual p i x.1 x.2) := by
  have hμ : Continuous (fun x : p.SiteMatrix × ℝ => conj (matchedA x.2)) :=
    Complex.continuous_conj.comp (ctr_continuous_matchedA.comp continuous_snd)
  have harg : Measurable (fun x : p.SiteMatrix × ℝ =>
      (x, (splitS p : ℂ) * conj (matchedA x.2))) :=
    measurable_id.prodMk (continuous_const.mul hμ).measurable
  have hR : Measurable (fun x : p.SiteMatrix × ℝ =>
      compressedResolvent p i x.1 x.2 ((splitS p : ℂ) * conj (matchedA x.2))) :=
    Measurable.comp
      (g := fun y : (p.SiteMatrix × ℝ) × ℂ => compressedResolvent p i y.1.1 y.1.2 y.2)
      (f := fun x : p.SiteMatrix × ℝ => (x, (splitS p : ℂ) * conj (matchedA x.2)))
      ctr_measurable_compressed harg
  have hpair : Measurable (fun x : p.SiteMatrix × ℝ =>
      (compressedResolvent p i x.1 x.2 ((splitS p : ℂ) * conj (matchedA x.2)),
        conj (matchedA x.2))) := hR.prodMk hμ.measurable
  have hc : Measurable (fun x : p.SiteMatrix × ℝ => ctrResidualOf
      (compressedResolvent p i x.1 x.2 ((splitS p : ℂ) * conj (matchedA x.2)))
      (conj (matchedA x.2))) :=
    Measurable.comp (g := fun q : PairMatrix p i × ℂ => ctrResidualOf q.1 q.2)
      (f := fun x : p.SiteMatrix × ℝ =>
        (compressedResolvent p i x.1 x.2 ((splitS p : ℂ) * conj (matchedA x.2)),
          conj (matchedA x.2)))
      ctr_continuous_residualOf.measurable hpair
  simp only [ctr_centerResidual_eq]
  exact hc

/-- The clipped center formula as a continuous function of the resolvent. -/
def ctrClipOf (M : PairMatrix p i) : ℝ :=
  max (-1) (min 1 ((splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ * (pairContrast p i * Mᴴ * M).trace).re)

theorem ctr_continuous_clipOf : Continuous (ctrClipOf (p := p) (i := i)) := by
  unfold ctrClipOf
  fun_prop

theorem ctr_measurable_centerFormula :
    Measurable (fun y : (p.SiteMatrix × ℝ) × ℂ => centerFormula p i y.1.1 y.1.2 y.2) :=
  ctr_continuous_clipOf.measurable.comp ctr_measurable_compressed

theorem ctr_measurableSet_hermitian : MeasurableSet {H : p.SiteMatrix | H.IsHermitian} :=
  (isClosed_eq (by fun_prop : Continuous (fun A : p.SiteMatrix => Aᴴ)) continuous_id).measurableSet

theorem ctr_measurableSet_root :
    MeasurableSet {y : (p.SiteMatrix × ℝ) × ℂ | IsDysonRoot p i y.1.1 y.1.2 y.2} := by
  unfold IsDysonRoot
  refine MeasurableSet.inter (measurableSet_lt measurable_const
    (Complex.measurable_im.comp measurable_snd)) (measurableSet_eq_fun measurable_snd ?_)
  exact measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
    ctr_measurable_compressed)

/-- The Borel set `S` of (Hermitian input, energy, root in the disk) in the regular domain. -/
def ctrRootSet (cst : CenterDomainConstants) (α : Fin p.N) : Set ((p.SiteMatrix × ℝ) × ℂ) :=
  {y | y.1.1.IsHermitian ∧ y.1.2 ∈ bulkInterval (rankMargin p α) ∧
    centerResidual p i y.1.1 y.1.2 ≤ cst.ε₁ p.b (rankMargin p α) ∧
    IsDysonRoot p i y.1.1 y.1.2 y.2 ∧
    ‖y.2 - (splitS p : ℂ) * conj (matchedA y.1.2)‖ < cst.ρ₀ p.b (rankMargin p α)}

theorem ctr_measurableSet_rootSet (cst : CenterDomainConstants) (α : Fin p.N) :
    MeasurableSet (ctrRootSet (i := i) cst α) := by
  have hμ : Continuous (fun y : (p.SiteMatrix × ℝ) × ℂ => conj (matchedA y.1.2)) :=
    Complex.continuous_conj.comp (ctr_continuous_matchedA.comp (continuous_snd.comp continuous_fst))
  have h1 : MeasurableSet {y : (p.SiteMatrix × ℝ) × ℂ | y.1.1.IsHermitian} :=
    ctr_measurableSet_hermitian.preimage (measurable_fst.comp measurable_fst)
  have h2 : MeasurableSet {y : (p.SiteMatrix × ℝ) × ℂ | y.1.2 ∈ bulkInterval (rankMargin p α)} :=
    measurableSet_Icc.preimage (measurable_snd.comp measurable_fst)
  have h3 : MeasurableSet {y : (p.SiteMatrix × ℝ) × ℂ |
      centerResidual p i y.1.1 y.1.2 ≤ cst.ε₁ p.b (rankMargin p α)} :=
    measurableSet_le (ctr_measurable_centerResidual.comp measurable_fst) measurable_const
  have h5 : MeasurableSet {y : (p.SiteMatrix × ℝ) × ℂ |
      ‖y.2 - (splitS p : ℂ) * conj (matchedA y.1.2)‖ < cst.ρ₀ p.b (rankMargin p α)} :=
    measurableSet_lt (measurable_snd.sub (continuous_const.mul hμ).measurable).norm
      measurable_const
  exact h1.inter (h2.inter (h3.inter (ctr_measurableSet_root.inter h5)))

theorem ctr_rootSet_injOn (cst : CenterDomainConstants) (α : Fin p.N) :
    Set.InjOn Prod.fst (ctrRootSet (i := i) cst α) := by
  intro y₁ h₁ y₂ h₂ h
  refine Prod.ext h ?_
  have h₂' : IsDysonRoot p i y₁.1.1 y₁.1.2 y₂.2 := by rw [h]; exact h₂.2.2.2.1
  exact ctr_root_unique h₁.1 h₁.2.2.2.1 h₂'

theorem ctr_domain_eq_image (cst : CenterDomainConstants) (α : Fin p.N) :
    {x : p.SiteMatrix × ℝ | x.1.IsHermitian ∧ InCenterDomain p i cst α x.1 x.2} =
      Prod.fst '' ctrRootSet (i := i) cst α := by
  ext x
  constructor
  · rintro ⟨hH, hI, hε, ζ, hr, hd⟩
    exact ⟨(x, ζ), ⟨hH, hI, hε, hr, hd⟩, rfl⟩
  · rintro ⟨y, ⟨hH, hI, hε, hr, hd⟩, rfl⟩
    exact ⟨hH, hI, hε, y.2, hr, hd⟩

/-- On the domain, the selected root is the unique root of `S` over `x`. -/
theorem ctr_dysonRoot_eq_of_mem (cst : CenterDomainConstants) (α : Fin p.N)
    {y : (p.SiteMatrix × ℝ) × ℂ} (hy : y ∈ ctrRootSet (i := i) cst α) :
    dysonRoot p i (cst.ρ₀ p.b (rankMargin p α)) y.1.1 y.1.2 = y.2 :=
  ctr_root_unique hy.1 (ctr_dysonRoot_spec ⟨y.2, hy.2.2.2⟩).1 hy.2.2.2.1

/-- On the domain the indicator-restricted center is the center formula at the root. -/
theorem ctr_center_of_mem (cst : CenterDomainConstants) (α : Fin p.N)
    {y : (p.SiteMatrix × ℝ) × ℂ} (hy : y ∈ ctrRootSet (i := i) cst α) :
    {x : p.SiteMatrix × ℝ | x.1.IsHermitian}.indicator
        (fun x => dysonCenter p i cst α x.1 x.2) y.1 = centerFormula p i y.1.1 y.1.2 y.2 := by
  rw [Set.indicator_of_mem (show y.1 ∈ {x : p.SiteMatrix × ℝ | x.1.IsHermitian} from hy.1)]
  have hdom : InCenterDomain p i cst α y.1.1 y.1.2 := ⟨hy.2.1, hy.2.2.1, y.2, hy.2.2.2⟩
  rw [ctr_dysonCenter_of_mem hdom, ctr_dysonRoot_eq_of_mem cst α hy]

/-- **Measurability of the physical center**,
for every choice of domain constants: the Hermitian-restricted center
`(H, E) ↦ 1_{H Hermitian} j_e(E)` is Borel on `SiteMatrix × ℝ`, and so is the Hermitian part
of the regular domain.
-/
theorem centerDomain_measurable (cst : CenterDomainConstants) :
    ∀ (p : Parameters) (α : Fin p.N) (i : ZMod p.n),
      Measurable ({x : p.SiteMatrix × ℝ | x.1.IsHermitian}.indicator
          (fun x => dysonCenter p i cst α x.1 x.2)) ∧
        MeasurableSet {x : p.SiteMatrix × ℝ | x.1.IsHermitian ∧ InCenterDomain p i cst α x.1 x.2} := by
  intro p α i
  let _ : PolishSpace p.SiteMatrix := inferInstanceAs (PolishSpace (p.Site → p.Site → ℂ))
  set S := ctrRootSet (i := i) cst α
  have hS : MeasurableSet S := ctr_measurableSet_rootSet cst α
  have hinj : Set.InjOn Prod.fst S := ctr_rootSet_injOn cst α
  have hD : MeasurableSet {x : p.SiteMatrix × ℝ | x.1.IsHermitian ∧ InCenterDomain p i cst α x.1 x.2} := by
    rw [ctr_domain_eq_image]
    exact hS.image_of_measurable_injOn measurable_fst hinj
  refine ⟨fun B hB => ?_, hD⟩
  set f := {x : p.SiteMatrix × ℝ | x.1.IsHermitian}.indicator
    (fun x => dysonCenter p i cst α x.1 x.2) with hfdef
  set D := {x : p.SiteMatrix × ℝ | x.1.IsHermitian ∧ InCenterDomain p i cst α x.1 x.2}
  have hDeq : D = Prod.fst '' S := ctr_domain_eq_image cst α
  set T := S ∩ (fun y : (p.SiteMatrix × ℝ) × ℂ => centerFormula p i y.1.1 y.1.2 y.2) ⁻¹' B
  have hT : MeasurableSet (Prod.fst '' T) :=
    (hS.inter (ctr_measurable_centerFormula hB)).image_of_measurable_injOn measurable_fst
      (hinj.mono Set.inter_subset_left)
  have hoff : ∀ x, x ∉ D → f x = 0 := by
    intro x hx
    by_cases hH : x.1.IsHermitian
    · rw [hfdef, Set.indicator_of_mem (show x ∈ {x : p.SiteMatrix × ℝ | x.1.IsHermitian} from hH)]
      unfold dysonCenter
      exact ite_eq_right_of_eq_false _ _ (eq_false fun h => hx ⟨hH, h⟩)
    · rw [hfdef]
      exact Set.indicator_of_notMem (show x ∉ {x : p.SiteMatrix × ℝ | x.1.IsHermitian} from hH) _
  have heq : f ⁻¹' B = Prod.fst '' T ∪ (Dᶜ ∩ {_x | (0 : ℝ) ∈ B}) := by
    ext x
    constructor
    · intro hx
      by_cases hxD : x ∈ D
      · rw [hDeq] at hxD
        obtain ⟨y, hy, rfl⟩ := hxD
        left
        refine ⟨y, ⟨hy, ?_⟩, rfl⟩
        change centerFormula p i y.1.1 y.1.2 y.2 ∈ B
        rw [← ctr_center_of_mem cst α hy]
        exact hx
      · right
        refine ⟨hxD, ?_⟩
        change (0 : ℝ) ∈ B
        rw [← hoff x hxD]
        exact hx
    · rintro (⟨y, ⟨hy, hyB⟩, rfl⟩ | ⟨hxD, h0⟩)
      · change f y.1 ∈ B
        rw [hfdef, ctr_center_of_mem cst α hy]
        exact hyB
      · change f x ∈ B
        rw [hoff x hxD]
        exact h0
  rw [heq]
  exact hT.union (hD.compl.inter (MeasurableSet.const _))

end Measurable

end BlockBand.Center
