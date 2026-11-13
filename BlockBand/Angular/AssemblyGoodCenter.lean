module

public import BlockBand.Angular.AssemblyGoodScore
public import BlockBand.Angular.Assembly
public import BlockBand.Angular.ComparisonLipschitz
public import BlockBand.DeterminantScore.PhysicalColumnMass

/-!
# The good observable of the physical angular estimate

* Blocks: `asm ω = assemble ω 0` inverts `splitOf` on Hermitian matrices (`asm_splitOf`,
  `splitOf_asm`); `edgeSchur (asm ω) E = pairK ω E`.
* `testHat φ u = φ(u/‖u‖)` (`0` at `u = 0`): bounded, invariant under `u ↦ cu`, measurable
  (`φ` is Lipschitz on the sphere).
* `obsG`: the real observable `1_good χ(b₂) (contrast - j_e) ρ(φ)` of `(ω, E, u)`,
  `ρ ∈ {Re, Im}`; `measurable_obsG`, `isLineInvariant_obsG`, `abs_obsG_le` (`≤ 2M`);
  `obsG_pair` (it is `ρ` of the weighted pair-law integrand) and `obsG_schurLift` (on the good
  domain it is the integrand `χ(b₂)(v*Jv/‖v‖² - j_*(J))Φ(v)` of the angular comparison).
* `reconMat` (`reconMat *ᵥ v = L_E v`), `reconLip_obs` (`ReconLip` from
  `IsAngularTest.lipschitz`), `isContraction_pairContrast`, and
  `jStar_pairContrast_eq` (`j_*(J) = (s/2W) Re Tr(J R*R)`, `Γ = s R*R`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.AssemblyGood

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.FiberAngular
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.QUE
open BlockBand.Angular.DetFactor BlockBand.Angular.Ratio BlockBand.Angular.Stein
open BlockBand.Angular.Stein.AngularData BlockBand.Angular.StepTwoGlue BlockBand.Angular.Assembly
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.PairCoareaBridge
open BlockBand.QUE.PhysicalAngularReduction BlockBand.DeterminantScore.PhysicalColumn
open BlockBand.Model.Construction BlockBand.QUE.Fourier BlockBand.Angular.FirstMoment
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## Blocks of `assemble ω 0`
-/

section Blocks

variable (p : BlockBand.Parameters) (i : ZMod p.n)

/-- `assemble ω 0`: the residual matrix with blocks `ω = (H_R, C, V)`. -/
def asm (ω : SplitState p i) : p.SiteMatrix := assemble p i ω 0

theorem splitOf_asm (ω : SplitState p i) : splitOf p i (asm p i ω) = ω := by
  obtain ⟨R, C, V⟩ := ω
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext x y <;>
    simp [splitOf, asm, exteriorBlock, couplingBlock, pairBlock, assemble, x.2, y.2]

theorem asm_splitOf {H : p.SiteMatrix} (hH : H.IsHermitian) : asm p i (splitOf p i H) = H := by
  rw [asm, assemble_splitOf p i hH]
  have : embedPair p i 0 = 0 := by funext x y; simp [embedPair]
  rw [this, add_zero]

theorem exteriorBlock_asm (ω : SplitState p i) : exteriorBlock p i (asm p i ω) = ω.1 :=
  congrArg Prod.fst (splitOf_asm p i ω)

theorem couplingBlock_asm (ω : SplitState p i) : couplingBlock p i (asm p i ω) = ω.2.1 :=
  congrArg (fun x => x.2.1) (splitOf_asm p i ω)

theorem pairBlock_asm (ω : SplitState p i) : pairBlock p i (asm p i ω) = ω.2.2 :=
  congrArg (fun x => x.2.2) (splitOf_asm p i ω)

theorem edgeSchur_asm (ω : SplitState p i) (E : ℝ) : edgeSchur p i (asm p i ω) E = pairK p i ω E := by
  unfold edgeSchur pairK
  rw [exteriorBlock_asm, couplingBlock_asm, pairBlock_asm]

theorem measurable_asm : Measurable (asm p i) :=
  (measurable_assemble p i).comp (measurable_id.prodMk measurable_const)

end Blocks

/-!
## The pole clause
-/

section Pole

variable {n : Type} [Fintype n] [DecidableEq n]

theorem det_sub_eigenvalue_eq_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : n) :
    (A - ((hA.eigenvalues k : ℝ) : ℂ) • 1).det = 0 := by
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨(hA.eigenvectorBasis k).ofLp, ?_, ?_⟩
  · intro h
    have hne := (hA.eigenvectorBasis).orthonormal.ne_zero k
    apply hne
    have : hA.eigenvectorBasis k = WithLp.toLp 2 (hA.eigenvectorBasis k).ofLp := rfl
    rw [this, h]; rfl
  · rw [sub_mulVec, hA.mulVec_eigenvectorBasis, smul_mulVec, one_mulVec, ← Complex.coe_smul,
      sub_self]

/-- **The pole clause of the good domain** for Hermitian `H_R` and `δ > 0`. -/
theorem poleClause_iff {A : Matrix n n ℂ} (hA : A.IsHermitian) {δ : ℝ} (hδ : 0 < δ) (E : ℝ) :
    (∀ μ : ℝ, (A - (μ : ℂ) • 1).det = 0 → δ ≤ |E - μ|) ↔
      (A - (E : ℂ) • 1).det ≠ 0 ∧ ‖(A - (E : ℂ) • 1)⁻¹‖ ≤ δ⁻¹ := by
  constructor
  · intro h
    have hdet : (A - (E : ℂ) • 1).det ≠ 0 := by
      intro h0; have := h E h0; rw [sub_self, abs_zero] at this; linarith
    refine ⟨hdet, ?_⟩
    have hdist : ∀ k, δ ≤ |hA.eigenvalues k - E| := fun k => by
      rw [abs_sub_comm]; exact h _ (det_sub_eigenvalue_eq_zero hA k)
    exact opNorm_resolvent_le hA hδ hdist
  · rintro ⟨hdet, hnorm⟩ μ hμ
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hμ
    set B := A - (E : ℂ) • 1 with hB
    have hBx : B *ᵥ x = ((μ - E : ℝ) : ℂ) • x := by
      have h1 : A *ᵥ x = (μ : ℂ) • x := by
        rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hx; exact hx
      rw [hB, sub_mulVec, h1, smul_mulVec, one_mulVec, ← sub_smul]; push_cast; rfl
    have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.2 hdet)
    have hxe : x = ((μ - E : ℝ) : ℂ) • (B⁻¹ *ᵥ x) := by
      calc x = (B⁻¹ * B) *ᵥ x := by rw [hinv, one_mulVec]
        _ = _ := by rw [← mulVec_mulVec, hBx, mulVec_smul]
    have hpos : 0 < l2Norm x := l2Norm_pos_of_ne_zero hx0
    have hle : l2Norm x ≤ |μ - E| * (δ⁻¹ * l2Norm x) := by
      conv_lhs => rw [hxe]
      rw [l2Norm_smul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (l2Norm_mulVec_le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hnorm hpos.le)
    have hlt' : |μ - E| * δ⁻¹ < 1 := by
      rw [abs_sub_comm, ← div_eq_mul_inv, div_lt_one hδ]; exact hlt
    nlinarith

end Pole

/-!
## The good set
-/

section GoodSet

variable (p : BlockBand.Parameters) (i : ZMod p.n)

/-- The good set `{(ω, E) : asm ω Hermitian, GoodOuter(asm ω, E)}`. -/
def goodSet (cst : CenterDomainConstants) (α : Fin p.N) (M₀ : ℝ) : Set (SplitState p i × ℝ) :=
  {x | (asm p i x.1).IsHermitian ∧ GoodOuter p i cst α M₀ (asm p i x.1) x.2}

theorem goodSet_eq (cst : CenterDomainConstants) (α : Fin p.N) (M₀ : ℝ) :
    goodSet p i cst α M₀ =
      {x | (asm p i x.1).IsHermitian ∧ InCenterDomain p i cst α (asm p i x.1) x.2} ∩
        ({x | (x.1.1 - (x.2 : ℂ) • 1).det ≠ 0 ∧
            ‖(x.1.1 - (x.2 : ℂ) • 1)⁻¹‖ ≤ ((p.W : ℝ) ^ (-M₀))⁻¹} ∩
          {x | ‖x.1.2.2‖ + ‖x.1.2.1‖ ≤ p.W}) := by
  have hδ : 0 < (p.W : ℝ) ^ (-M₀) := Real.rpow_pos_of_pos (by exact_mod_cast p.W_pos) _
  ext x
  simp only [goodSet, GoodOuter, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hH, hD, h2, h3⟩
    have hR : x.1.1.IsHermitian := by
      have := exteriorBlock_isHermitian p i hH; rwa [exteriorBlock_asm] at this
    rw [exteriorBlock_asm] at h2
    rw [pairBlock_asm, couplingBlock_asm] at h3
    exact ⟨⟨hH, hD⟩, (poleClause_iff hR hδ x.2).1 h2, h3⟩
  · rintro ⟨⟨hH, hD⟩, h2, h3⟩
    have hR : x.1.1.IsHermitian := by
      have := exteriorBlock_isHermitian p i hH; rwa [exteriorBlock_asm] at this
    refine ⟨hH, hD, ?_, ?_⟩
    · rw [exteriorBlock_asm]; exact (poleClause_iff hR hδ x.2).2 h2
    · rw [pairBlock_asm, couplingBlock_asm]; exact h3

theorem measurableSet_goodSet {cst : CenterDomainConstants} (hcd : CenterDomainContract cst)
    (α : Fin p.N) (M₀ : ℝ) : MeasurableSet (goodSet p i cst α M₀) := by
  rw [goodSet_eq]
  have hA : Measurable fun x : SplitState p i × ℝ => (asm p i x.1, x.2) :=
    ((measurable_asm p i).comp measurable_fst).prodMk measurable_snd
  have hM : Measurable fun x : SplitState p i × ℝ => x.1.1 - (x.2 : ℂ) • 1 :=
    measurable_matSub measurable_fst.fst (measurable_smul_one measurable_snd)
  refine ((hcd.measurable p α i).2.preimage hA).inter (MeasurableSet.inter ?_ ?_)
  · refine MeasurableSet.inter ?_ ?_
    · exact (measurableSet_eq_fun ((continuous_id.matrix_det).measurable.comp hM)
        measurable_const).compl
    · exact measurableSet_le (continuous_norm.measurable.comp (measurable_inv_matrix.comp hM))
        measurable_const
  · exact measurableSet_le ((continuous_norm.measurable.comp measurable_fst.snd.snd).add
      (continuous_norm.measurable.comp measurable_fst.snd.fst)) measurable_const

end GoodSet

/-!
## Scalar invariance
-/

section Scalar

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quadQuot_smul_complex (B : Matrix ι ι ℂ) (z : ι → ℂ) {c : ℂ} (hc : c ≠ 0) :
    quadQuot B (c • z) = quadQuot B z := by
  unfold quadQuot normSqSum
  have hnum : (∑ a, conj ((c • z) a) * (B *ᵥ (c • z)) a) =
      ((‖c‖ ^ 2 : ℝ) : ℂ) * ∑ a, conj (z a) * (B *ᵥ z) a := by
    rw [mulVec_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    ring
  have hden : (∑ a, ‖(c • z) a‖ ^ 2) = ‖c‖ ^ 2 * ∑ a, ‖z a‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [hnum, Complex.re_ofReal_mul, hden,
    mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hc))]

theorem normalize_smul_complex (c : ℂ) (u : ι → ℂ) :
    FiberAngular.normalize (c • u) = (((‖c‖)⁻¹ : ℝ) * c : ℂ) • FiberAngular.normalize u := by
  unfold FiberAngular.normalize
  rw [l2Norm_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  rw [mul_inv]
  ring

/-- `φ(u/‖u‖)`, and `0` at the origin. -/
def testHat (φ : (ι → ℂ) → ℂ) (u : ι → ℂ) : ℂ := by
  classical
  exact if u = 0 then 0 else φ (FiberAngular.normalize u)

theorem normalize_of_unit {u : ι → ℂ} (hu : l2Norm u = 1) : FiberAngular.normalize u = u := by
  unfold FiberAngular.normalize; rw [hu]; simp

theorem ne_zero_of_l2Norm {u : ι → ℂ} (hu : l2Norm u = 1) : u ≠ 0 := by
  intro h; rw [h] at hu; simp [l2Norm] at hu

theorem testHat_of_unit (φ : (ι → ℂ) → ℂ) {u : ι → ℂ} (hu : l2Norm u = 1) :
    testHat φ u = φ u := by
  unfold testHat; simp only [ne_zero_of_l2Norm hu, ↓reduceIte, normalize_of_unit hu]

theorem norm_testHat_le [Nonempty ι] {φ : (ι → ℂ) → ℂ} {M L : ℝ} (hφ : IsAngularTest φ M L)
    (u : ι → ℂ) : ‖testHat φ u‖ ≤ M := by
  unfold testHat
  split_ifs with hu
  · rw [norm_zero]
    obtain ⟨j⟩ := (inferInstance : Nonempty ι)
    have hj : l2Norm (Pi.single j (1 : ℂ) : ι → ℂ) = 1 := by
      classical
      unfold l2Norm
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp
    exact (norm_nonneg _).trans (hφ.bound _ hj)
  · exact hφ.bound _ (l2Norm_normalize hu)

theorem testHat_smul {φ : (ι → ℂ) → ℂ} {M L : ℝ} (hφ : IsAngularTest φ M L) {c : ℂ}
    (hc : c ≠ 0) (u : ι → ℂ) : testHat φ (c • u) = testHat φ u := by
  unfold testHat
  by_cases hu : u = 0
  · simp [hu]
  simp only [smul_ne_zero hc hu, hu, ↓reduceIte, normalize_smul_complex c u]
  refine hφ.phase _ _ ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hc)]

theorem continuousOn_normalize : ContinuousOn (fun u : ι → ℂ => FiberAngular.normalize u) {0}ᶜ := by
  unfold FiberAngular.normalize
  have h1 : ContinuousOn (fun u : ι → ℂ => ((l2Norm u : ℂ))⁻¹) {0}ᶜ :=
    (Complex.continuous_ofReal.comp continuous_l2Norm).continuousOn.inv₀ fun u hu =>
      Complex.ofReal_ne_zero.2 (l2Norm_pos_of_ne_zero hu).ne'
  exact h1.smul continuousOn_id

theorem measurable_testHat {φ : (ι → ℂ) → ℂ} {M L : ℝ} (hφ : IsAngularTest φ M L) :
    Measurable (testHat φ) := by
  have hc : ContinuousOn (fun u => φ (FiberAngular.normalize u)) {0}ᶜ := by
    intro u₀ hu₀
    have hn := continuousOn_normalize (ι := ι)
    have hcw : ContinuousWithinAt (fun u => L * l2Norm (FiberAngular.normalize u -
        FiberAngular.normalize u₀)) {0}ᶜ u₀ :=
      (continuous_const.mul continuous_l2Norm).continuousAt.comp_continuousWithinAt
        ((hn u₀ hu₀).sub continuousWithinAt_const)
    have h0 : L * l2Norm (FiberAngular.normalize u₀ - FiberAngular.normalize u₀) = 0 := by
      simp [l2Norm]
    have hcw' := hcw.tendsto
    beta_reduce at hcw'
    rw [h0] at hcw'
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hcw'
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hφ.lipschitz _ _ (l2Norm_normalize hu) (l2Norm_normalize hu₀)
  have hm : Measurable fun u => φ (FiberAngular.normalize u) :=
    measurable_of_continuousOn_compl_singleton 0 hc
  unfold testHat
  exact Measurable.ite (measurableSet_singleton 0) measurable_const hm

end Scalar

/-!
## The observable
-/

section Obs

variable (p : BlockBand.Parameters) (i : ZMod p.n)

/-- The center `j_e` on Hermitian residuals, extended by zero. -/
def dCH (cst : CenterDomainConstants) (α : Fin p.N) (x : SplitState p i × ℝ) : ℝ :=
  {y : p.SiteMatrix × ℝ | y.1.IsHermitian}.indicator (fun y => dysonCenter p i cst α y.1 y.2)
    (asm p i x.1, x.2)

/-- **The good observable** `1_good χ(b₂) (contrast - j_e) ρ(φ(u/‖u‖))` at `(ω, E, u)`. -/
def obsG (cst : CenterDomainConstants) (α : Fin p.N) (M₀ R₀ : ℝ) (φ : (p.Site → ℂ) → ℂ)
    (ρ : ℂ → ℝ) (x : SplitState p i × ℝ) (u : p.Site → ℂ) : ℝ :=
  (goodSet p i cst α M₀).indicator 1 x * (stepSixCutoff R₀).χ (pairB2 p i (asm p i x.1) x.2 u) *
    (projContrast p i (lineProjector u) - dCH p i cst α x) * ρ (testHat φ u)

/-- The admissible real parts `ρ ∈ {Re, Im}`. -/
structure IsRealPart (ρ : ℂ → ℝ) : Prop where
  meas : Measurable ρ
  abs_le : ∀ z, |ρ z| ≤ ‖z‖
  sub : ∀ z w, ρ (z - w) = ρ z - ρ w
  ofReal_mul : ∀ (r : ℝ) (z : ℂ), ρ ((r : ℂ) * z) = r * ρ z

theorem isRealPart_re : IsRealPart Complex.re :=
  ⟨Complex.measurable_re, Complex.abs_re_le_norm, Complex.sub_re, Complex.re_ofReal_mul⟩

theorem isRealPart_im : IsRealPart Complex.im :=
  ⟨Complex.measurable_im, Complex.abs_im_le_norm, Complex.sub_im, Complex.im_ofReal_mul⟩

theorem abs_projContrast_lineProjector_le (u : p.Site → ℂ) :
    |projContrast p i (lineProjector u)| ≤ 1 := by
  unfold projContrast projPairMass
  rw [projBlockMass_lineProjector, projBlockMass_lineProjector]
  set a := (∑ a : Fin p.W, ‖u (i, a)‖ ^ 2) / l2Norm u ^ 2
  set b := (∑ a : Fin p.W, ‖u (i + 1, a)‖ ^ 2) / l2Norm u ^ 2
  have ha : 0 ≤ a := div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  have hb : 0 ≤ b := div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  rcases (add_nonneg ha hb).lt_or_eq with h | h
  · rw [abs_div, abs_of_pos h, div_le_one h]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · rw [← h, div_zero, abs_zero]; exact zero_le_one

theorem abs_dCH_le (cst : CenterDomainConstants) (α : Fin p.N) (x : SplitState p i × ℝ) :
    |dCH p i cst α x| ≤ 1 := by
  unfold dCH Set.indicator
  split_ifs
  · exact abs_dysonCenter_le_one p i cst α _ _
  · simp

variable {p i}

theorem abs_obsG_le {cst : CenterDomainConstants} {α : Fin p.N} {M₀ R₀ : ℝ}
    {φ : (p.Site → ℂ) → ℂ} {M L : ℝ} (hφ : IsAngularTest φ M L) {ρ : ℂ → ℝ} (hρ : IsRealPart ρ)
    (x : SplitState p i × ℝ) (u : p.Site → ℂ) :
    |obsG p i cst α M₀ R₀ φ ρ x u| ≤ 2 * M := by
  unfold obsG
  have h1 : |(goodSet p i cst α M₀).indicator (1 : SplitState p i × ℝ → ℝ) x| ≤ 1 := by
    unfold Set.indicator; split_ifs <;> simp
  have h2 : |(stepSixCutoff R₀).χ (pairB2 p i (asm p i x.1) x.2 u)| ≤ 1 := by
    rw [abs_of_nonneg ((stepSixCutoff R₀).nonneg _)]; exact (stepSixCutoff R₀).le _
  have h3 : |projContrast p i (lineProjector u) - dCH p i cst α x| ≤ 2 := by
    have := abs_projContrast_lineProjector_le p i u
    have := abs_dCH_le p i cst α x
    exact (abs_sub _ _).trans (by linarith)
  have h4 : |ρ (testHat φ u)| ≤ M := (hρ.abs_le _).trans (norm_testHat_le hφ u)
  rw [abs_mul, abs_mul, abs_mul]
  have hM := IsAngularTest.bound_nonneg hφ
  calc _ ≤ 1 * 1 * 2 * M := by gcongr
    _ = 2 * M := by ring

theorem pairB2_smul (Hres : p.SiteMatrix) (E : ℝ) {c : ℂ} (hc : c ≠ 0) (u : p.Site → ℂ) :
    pairB2 p i Hres E (c • u) = pairB2 p i Hres E u := by
  unfold pairB2
  have : (fun x : PairSite p i => (c • u) x.1) = c • fun x : PairSite p i => u x.1 := rfl
  rw [this, quadQuot_smul_complex _ _ hc]

theorem isLineInvariant_obsG (cst : CenterDomainConstants) (α : Fin p.N) (M₀ R₀ : ℝ)
    {φ : (p.Site → ℂ) → ℂ} {M L : ℝ} (hφ : IsAngularTest φ M L) (ρ : ℂ → ℝ) :
    IsLineInvariant (obsG p i cst α M₀ R₀ φ ρ) := by
  intro x u c hc
  unfold obsG
  rw [pairB2_smul _ _ hc, lineProjector_smul hc, testHat_smul hφ hc]

theorem measurable_quadQuot {ι : Type} [Fintype ι] :
    Measurable fun y : Matrix ι ι ℂ × (ι → ℂ) => quadQuot y.1 y.2 := by
  unfold quadQuot normSqSum
  refine Measurable.div ?_ ?_
  · refine Complex.measurable_re.comp (Finset.measurable_sum _ fun a _ => ?_)
    exact (continuous_star.measurable.comp ((measurable_pi_apply a).comp measurable_snd)).mul
      ((measurable_pi_apply a).comp (measurable_mulVec' measurable_fst measurable_snd))
  · exact Finset.measurable_sum _ fun a _ =>
      ((measurable_pi_apply a).comp measurable_snd).norm.pow_const 2

theorem measurable_lineProjector {ι : Type} [Fintype ι] :
    Measurable (lineProjector (ι := ι)) := by
  unfold lineProjector
  refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun y => ?_
  exact ((Complex.measurable_ofReal.comp continuous_l2Norm.measurable).pow_const 2).inv.mul
    ((measurable_pi_apply x).mul (continuous_star.measurable.comp (measurable_pi_apply y)))

theorem measurable_projContrast : Measurable (projContrast p i) := by
  unfold projContrast projPairMass projBlockMass
  have hk : ∀ k : ZMod p.n, Measurable fun P : p.Site → p.Site → ℂ =>
      ∑ a : Fin p.W, (P (k, a) (k, a)).re := fun k =>
    Finset.measurable_sum _ fun a _ => Complex.measurable_re.comp
      ((measurable_pi_apply _).comp (measurable_pi_apply _))
  exact ((hk i).sub (hk (i + 1))).div ((hk i).add (hk (i + 1)))

theorem measurable_obsG {cst : CenterDomainConstants} (hcd : CenterDomainContract cst)
    (α : Fin p.N) (M₀ R₀ : ℝ) {φ : (p.Site → ℂ) → ℂ} {M L : ℝ} (hφ : IsAngularTest φ M L)
    {ρ : ℂ → ℝ} (hρ : IsRealPart ρ) :
    Measurable (Function.uncurry (obsG p i cst α M₀ R₀ φ ρ)) := by
  have hx : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) => z.1 := measurable_fst
  have hu : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) => z.2 := measurable_snd
  have hind : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) =>
      (goodSet p i cst α M₀).indicator (1 : SplitState p i × ℝ → ℝ) z.1 :=
    (measurable_const.indicator (measurableSet_goodSet p i hcd α M₀)).comp hx
  have hK : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) =>
      edgeSchur p i (asm p i z.1.1) z.1.2 * edgeSchur p i (asm p i z.1.1) z.1.2 := by
    have : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) =>
        edgeSchur p i (asm p i z.1.1) z.1.2 := by
      simp only [edgeSchur_asm]
      unfold pairK
      exact measurable_matSub (measurable_physF.comp hx) (measurable_smul_one measurable_fst.snd)
    exact measurable_matMul this this
  have hr : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) =>
      (fun x : PairSite p i => z.2 x.1) :=
    measurable_pi_iff.2 fun x => (measurable_pi_apply (x.1 : p.Site)).comp hu
  have hb2 : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) =>
      pairB2 p i (asm p i z.1.1) z.1.2 z.2 := by
    have h := (measurable_quadQuot (ι := PairSite p i)).comp (hK.prodMk hr)
    exact h
  have hchi : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) =>
      (stepSixCutoff R₀).χ (pairB2 p i (asm p i z.1.1) z.1.2 z.2) :=
    (stepSixCutoff R₀).smooth.continuous.measurable.comp hb2
  have hdc : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) => dCH p i cst α z.1 := by
    unfold dCH
    exact (hcd.measurable p α i).1.comp ((((measurable_asm p i).comp measurable_fst).prodMk
      measurable_snd).comp hx)
  have hpc : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) =>
      projContrast p i (lineProjector z.2) :=
    (measurable_projContrast).comp (measurable_lineProjector.comp hu)
  have hφm : Measurable fun z : (SplitState p i × ℝ) × (p.Site → ℂ) => ρ (testHat φ z.2) :=
    hρ.meas.comp ((measurable_testHat hφ).comp hu)
  have heq : Function.uncurry (obsG p i cst α M₀ R₀ φ ρ) = fun z =>
      (goodSet p i cst α M₀).indicator (1 : SplitState p i × ℝ → ℝ) z.1 *
        (stepSixCutoff R₀).χ (pairB2 p i (asm p i z.1.1) z.1.2 z.2) *
        (projContrast p i (lineProjector z.2) - dCH p i cst α z.1) * ρ (testHat φ z.2) := rfl
  rw [heq]
  exact ((hind.mul hchi).mul (hpc.sub hdc)).mul hφm

/-- **The pair side**: with a Hermitian residual and a unit eigenvector, `ρ` of the weighted
pair-law integrand is the observable at `(splitOf(H - G_e), λ_α, ψ_α)`. -/
theorem obsG_pair {model : p.GaussianRingModel} (cst : CenterDomainConstants) (α : Fin p.N)
    (M₀ R₀ : ℝ) (X : PairExtension p model) (G : X.Ω → PairMatrix p i) (φ : (p.Site → ℂ) → ℂ)
    {ρ : ℂ → ℝ} (hρ : IsRealPart ρ) (ω : X.Ω) (hH : (residual p i X G ω).IsHermitian)
    (hψ : l2Norm (physicalOrderedEigenvector p (X.Hm ω) α) = 1) :
    ρ (stepWeight p i cst α M₀ R₀ X G ω * angularIntegrand p i α X (centerOn p i cst α X G) φ ω) =
      obsG p i cst α M₀ R₀ φ ρ (splitOf p i (residual p i X G ω),
        physicalOrderedEigenvalue p (X.Hm ω) α) (physicalOrderedEigenvector p (X.Hm ω) α) := by
  classical
  set ψ := physicalOrderedEigenvector p (X.Hm ω) α
  set E := physicalOrderedEigenvalue p (X.Hm ω) α
  set Hr := residual p i X G ω
  have hasm : asm p i (splitOf p i Hr) = Hr := asm_splitOf p i hH
  unfold stepWeight angularIntegrand obsG
  rw [← mul_assoc, ← Complex.ofReal_mul, hρ.ofReal_mul, testHat_of_unit φ hψ,
    lineProjector_eq_eigenProjector hψ, ← physicalPairContrast_eq_projContrast]
  have hd : dCH p i cst α (splitOf p i Hr, E) = centerOn p i cst α X G ω := by
    unfold dCH centerOn
    rw [hasm, Set.indicator_of_mem (show (Hr, E) ∈ {y : p.SiteMatrix × ℝ | y.1.IsHermitian}
      from hH)]
  have hgw : (goodSet p i cst α M₀).indicator (1 : SplitState p i × ℝ → ℝ) (splitOf p i Hr, E) *
      (stepSixCutoff R₀).χ (pairB2 p i (asm p i (splitOf p i Hr)) E ψ) =
      goodWeight p i cst α M₀ R₀ Hr E ψ := by
    rw [hasm]
    unfold goodWeight
    by_cases hg : GoodOuter p i cst α M₀ Hr E
    · have hmem : (splitOf p i Hr, E) ∈ goodSet p i cst α M₀ :=
        ⟨by show (asm p i (splitOf p i Hr)).IsHermitian; rw [hasm]; exact hH,
          by show GoodOuter p i cst α M₀ (asm p i (splitOf p i Hr)) E; rw [hasm]; exact hg⟩
      rw [Set.indicator_of_mem hmem]
      simp only [hg, ↓reduceIte, Pi.one_apply, one_mul]
    · have hmem : (splitOf p i Hr, E) ∉ goodSet p i cst α M₀ := fun h => hg (by
        have h2 : GoodOuter p i cst α M₀ (asm p i (splitOf p i Hr)) E := h.2
        rwa [hasm] at h2)
      rw [Set.indicator_of_notMem hmem]
      simp only [hg, ↓reduceIte, zero_mul]
  rw [hd, hgw]

end Obs

/-!
## The reconstruction, the contraction and the center
-/

section Recon

variable (p : BlockBand.Parameters) (i : ZMod p.n)

/-- The matrix of `v ↦ L_E v`. -/
def reconMat (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) : Matrix p.Site (PairSite p i) ℂ :=
  fun x y => schurLift p i H_R C E (Pi.single y 1) x

theorem reconMat_mulVec (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (v : PairSite p i → ℂ) :
    reconMat p i H_R C E *ᵥ v = schurLift p i H_R C E v := by
  classical
  funext x
  unfold reconMat
  simp only [mulVec, dotProduct, schurLift]
  split_ifs with hx
  · simp [Pi.single_apply]
  · simp [Pi.single_apply]

theorem reconMat_injective (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) :
    ∀ v, reconMat p i H_R C E *ᵥ v = 0 → v = 0 := by
  intro v hv
  by_contra h
  exact schurLift_ne_zero p i H_R C E h (by rw [← reconMat_mulVec]; exact hv)

theorem recon_reconMat (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (v : PairSite p i → ℂ) :
    recon (reconMat p i H_R C E) v = FiberAngular.normalize (schurLift p i H_R C E v) := by
  unfold recon FiberAngular.normalize; rw [reconMat_mulVec]

theorem reconLip_obs {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {L : Matrix κ ι ℂ} (hL : ∀ v, L *ᵥ v = 0 → v = 0) {φ : (κ → ℂ) → ℂ} {M Lφ : ℝ}
    (hφ : IsAngularTest φ M Lφ) {ρ : ℂ → ℝ} (hρ : IsRealPart ρ) :
    ReconLip L (fun v => ρ (φ (recon L v))) Lφ := by
  intro v v' hv hv'
  have hu : ∀ w : ι → ℂ, w ≠ 0 → l2Norm (recon L w) = 1 := fun w hw =>
    l2Norm_normalize (fun h => hw (hL w h))
  rw [← hρ.sub]
  exact (hρ.abs_le _).trans (hφ.lipschitz _ _ (hu v hv) (hu v' hv'))

theorem abs_obs_le {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {L : Matrix κ ι ℂ} (hL : ∀ v, L *ᵥ v = 0 → v = 0) {φ : (κ → ℂ) → ℂ} {M Lφ : ℝ}
    (hφ : IsAngularTest φ M Lφ) {ρ : ℂ → ℝ} (hρ : IsRealPart ρ) :
    ∀ v, v ≠ 0 → |ρ (φ (recon L v))| ≤ M := fun v hv =>
  (hρ.abs_le _).trans (hφ.bound _ (l2Norm_normalize (fun h => hv (hL v h))))

theorem isContraction_pairContrast : IsContraction (pairContrast p i) := by
  refine ⟨?_, fun x => le_of_eq ?_⟩
  · unfold pairContrast
    rw [IsHermitian, diagonal_conjTranspose]
    congr 1; funext x; by_cases h : x.1.1 = i <;> simp [h]
  · unfold pairContrast normSqSum
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mulVec_diagonal]
    by_cases h : a.1.1 = i <;> simp [h]

/-- **The angular center is the Dyson center**: for angular data with `K = K_e(E)`, `s = splitS`
and the formula `j_e = (s/2W) Re Tr(J R*R)`, `R = (K - ζ)⁻¹`, one has
`j_*(J) = j_e` (`Γ = s R*R`). -/
theorem jStar_pairContrast_eq (D : AngularData (PairSite p i)) {Hres : p.SiteMatrix} {E : ℝ}
    (cst : CenterDomainConstants) (α : Fin p.N) (hK : D.K = edgeSchur p i Hres E)
    (hs : D.s = splitS p)
    (hformula : dysonCenter p i cst α Hres E = ((splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ *
      (pairContrast p i * ((edgeSchur p i Hres E - D.ζ • 1)⁻¹)ᴴ *
        (edgeSchur p i Hres E - D.ζ • 1)⁻¹).trace).re) :
    D.jStar (pairContrast p i) = dysonCenter p i cst α Hres E := by
  rw [hformula]
  unfold AngularData.jStar AngularData.Γ BlockBand.Angular.Reference.angularGamma
  have hR : BlockBand.Angular.Reference.resolvent D.K (conj D.ζ) = (Rz D)ᴴ :=
    (Rz_conjTranspose D).symm
  rw [hR]
  unfold Rz BlockBand.Angular.Reference.resolvent
  rw [← hK, hs, BlockBand.Angular.FiberAngular.card_pairSite, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  set T := (pairContrast p i * ((D.K - D.ζ • 1)⁻¹)ᴴ * (D.K - D.ζ • 1)⁻¹).trace
  have h1 : (2 * (p.W : ℂ))⁻¹ = (((2 * (p.W : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have e : ((splitS p : ℂ) * (((2 * (p.W : ℝ))⁻¹ : ℝ) : ℂ) * T).re =
      splitS p * (2 * (p.W : ℝ))⁻¹ * T.re := by
    rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
  rw [h1, e, smul_eq_mul, Complex.re_ofReal_mul]
  push_cast
  ring

end Recon

/-- **The angular side on the good domain**: at `(ω, E) ∈ goodSet` with angular data `D`
(`D.K = K_e(E)`, `j_*(J) = j_e`) and `v ≠ 0`, the observable at `L_E v` is the integrand
`χ(b₂(v))(Re(v*Jv)/‖v‖² - j_*(J)) ρ(φ(L_E v/‖L_E v‖))` of the angular comparison. -/
theorem obsG_schurLift {p : BlockBand.Parameters} {i : ZMod p.n} {cst : CenterDomainConstants}
    {α : Fin p.N} {M₀ R₀ : ℝ} {φ : (p.Site → ℂ) → ℂ} {ρ : ℂ → ℝ} {x : SplitState p i × ℝ}
    (hx : x ∈ goodSet p i cst α M₀) (D : AngularData (PairSite p i))
    (hK : D.K = edgeSchur p i (asm p i x.1) x.2)
    (hj : D.jStar (pairContrast p i) = dCH p i cst α x) {v : PairSite p i → ℂ} (hv : v ≠ 0) :
    obsG p i cst α M₀ R₀ φ ρ x (schurLift p i x.1.1 x.1.2.1 x.2 v) =
      (stepSixCutoff R₀).χ (D.b₂ v) * (quadQuot (pairContrast p i) v - D.jStar (pairContrast p i)) *
        ρ (φ (recon (reconMat p i x.1.1 x.1.2.1 x.2) v)) := by
  unfold obsG
  rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul, projContrast_lineProjector_schurLift p i _ _ _ hv,
    hj, recon_reconMat]
  have hb : pairB2 p i (asm p i x.1) x.2 (schurLift p i x.1.1 x.1.2.1 x.2 v) = D.b₂ v := by
    unfold pairB2 AngularData.b₂
    rw [hK]
    congr 1
    funext y
    exact schurLift_pair p i _ _ _ v y
  rw [hb]
  unfold testHat
  simp only [schurLift_ne_zero p i _ _ _ hv, ↓reduceIte]

end BlockBand.Angular.AssemblyGood
