module

public import BlockBand.Angular.AssemblyEvents
public import BlockBand.Angular.AssemblyCutoff
public import BlockBand.Angular.FiberAngular
public import BlockBand.DeterminantScore.GUENormTail

/-!
# Assembly of the physical angular estimate

The angular estimate bounds `‖E♯[(v*Jv - j_S)φ(ψ_α)]‖` by `C(M + L_φ)/W` for bulk ranks
`α`, uniformly for `4 ≤ n ≤ TW`. It is assembled here from a bound on the good part and
from the probabilities of the removed events.

* The removed events are bounded by `CenterDomainContract.small` (`q = 2`),
  `PairPoleExclusionContract.pole_probability` (`ε = W^{-4}`: `≤ 6T/(√(2πs) W)`) and the norm
  event, which is split into the pair-row event (`PairRowNormTailStatement`, a Gaussian
  Frobenius moment bound for the ring law) and `‖G_e‖ > W/2 ≥ C√s` (`GUENormTailStatement`).
* On the good event `det(H_R - λ) ≠ 0`, so the eigenvalue equation gives
  `b₂ ≤ ‖G_e‖²` (`PairEigenB2Statement`, from `K₀ψ_S = -G_eψ_S`), hence
  `{good, b₂ > R₀} ⊆ {‖G_e‖ > C√s}` with `R₀ = C²s`; and
  `P♯(G_e ∈ B) ≤ (n/2) GUE(B)` (`extendedPairMeasure_gaussian_le`) with the exponential tail
  `e^{-2cW}` gives `≤ T/(4c²W)`. The regular domain already contains
  `E ∈ bulkInterval (rankMargin)`.
* No width threshold: for `W ≤ W₁` the trivial bound `2M ≤ 2MW₁/W` is used.

`PhysicalAngularLabel b θ T` quantifies over every real `θ`. The assembly is proved for
`0 < θ`; `θ ≥ 1/2` reduces to `θ = 1/4` by monotonicity (`physicalAngularStatement_mono`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Assembly

open MeasureTheory ProbabilityTheory BlockBand.Model.Construction
open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.QUE.Fourier
open BlockBand.QUE.PhysicalAngularReduction BlockBand.Angular.ProjectiveStein
open BlockBand.DeterminantScore.GUENormTail
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## The good outer domain, `b₂` and the weight
-/

section Defs

variable (p : Parameters) (i : ZMod p.n)

/-- The good outer domain of Step 2: `E` in the regular domain of the center
(`InCenterDomain`), `dist(E, Spec H_R) ≥ W^{-M₀}`, and `‖V‖ + ‖C‖ ≤ W` (`V`, `C` the pair
and coupling blocks of the residual `H - G_e`, operator norms). It depends only on the
exterior data and `E`. -/
def GoodOuter (cst : CenterDomainConstants) (α : Fin p.N) (M₀ : ℝ) (Hres : p.SiteMatrix)
    (E : ℝ) : Prop :=
  InCenterDomain p i cst α Hres E ∧
    (∀ μ : ℝ, (exteriorBlock p i Hres - (μ : ℂ) • 1).det = 0 → (p.W : ℝ) ^ (-M₀) ≤ |E - μ|) ∧
    ‖pairBlock p i Hres‖ + ‖couplingBlock p i Hres‖ ≤ p.W

/-- `b₂(v) = ‖K₀v‖²/‖v‖²` at the pair restriction `v` of `ψ`, `K₀ = K_e(E)`. -/
def pairB2 (Hres : p.SiteMatrix) (E : ℝ) (ψ : p.Site → ℂ) : ℝ :=
  quadQuot (edgeSchur p i Hres E * edgeSchur p i Hres E) (fun x : PairSite p i => ψ x.1)

/-- The weight `1_good · χ(b₂)`. -/
def goodWeight (cst : CenterDomainConstants) (α : Fin p.N) (M₀ R₀ : ℝ) (Hres : p.SiteMatrix)
    (E : ℝ) (ψ : p.Site → ℂ) : ℝ := by
  classical
  exact if GoodOuter p i cst α M₀ Hres E then (stepSixCutoff R₀).χ (pairB2 p i Hres E ψ) else 0

/-- The residual `H - G_e` on an extension. -/
def residual {model : p.GaussianRingModel} (X : PairExtension p model)
    (G : X.Ω → PairMatrix p i) (ω : X.Ω) : p.SiteMatrix :=
  X.Hm ω - embedPair p i (G ω)

/-- The weight on an extension. -/
def stepWeight {model : p.GaussianRingModel} (cst : CenterDomainConstants) (α : Fin p.N)
    (M₀ R₀ : ℝ) (X : PairExtension p model) (G : X.Ω → PairMatrix p i) (ω : X.Ω) : ℂ :=
  (goodWeight p i cst α M₀ R₀ (residual p i X G ω) (physicalOrderedEigenvalue p (X.Hm ω) α)
    (physicalOrderedEigenvector p (X.Hm ω) α) : ℂ)

/-- The Dyson center `dysonCenter` on an extension. -/
def centerOn {model : p.GaussianRingModel} (cst : CenterDomainConstants) (α : Fin p.N)
    (X : PairExtension p model) (G : X.Ω → PairMatrix p i) (ω : X.Ω) : ℝ :=
  dysonCenter p i cst α (residual p i X G ω) (physicalOrderedEigenvalue p (X.Hm ω) α)

/-- The integrand `(v*Jv - c) φ(ψ_α)` of the angular estimate. -/
def angularIntegrand {model : p.GaussianRingModel} (α : Fin p.N) (X : PairExtension p model)
    (c : X.Ω → ℝ) (φ : (p.Site → ℂ) → ℂ) (ω : X.Ω) : ℂ :=
  ((physicalPairContrast p α i (X.Hm ω) - c ω : ℝ) : ℂ) *
    φ (physicalOrderedEigenvector p (X.Hm ω) α)

/-- The removed set `{¬good} ∪ {good, b₂ > R₀}`. -/
def removedSet {model : p.GaussianRingModel} (cst : CenterDomainConstants) (α : Fin p.N)
    (M₀ R₀ : ℝ) (X : PairExtension p model) (G : X.Ω → PairMatrix p i) : Set X.Ω :=
  {ω | ¬ GoodOuter p i cst α M₀ (residual p i X G ω) (physicalOrderedEigenvalue p (X.Hm ω) α)} ∪
    {ω | GoodOuter p i cst α M₀ (residual p i X G ω) (physicalOrderedEigenvalue p (X.Hm ω) α) ∧
      R₀ < pairB2 p i (residual p i X G ω) (physicalOrderedEigenvalue p (X.Hm ω) α)
        (physicalOrderedEigenvector p (X.Hm ω) α)}

end Defs

/-!
## Statements combined in the assembly
-/

/-- The good-part bound at one parameter set (constant `C`). -/
def GoodPartAt (p : Parameters) (θ : ℝ) (cst : CenterDomainConstants) (M₀ R₀ C : ℝ) : Prop :=
  ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p θ α → ∀ (i : ZMod p.n)
    (X : PairExtension p model) (G : X.Ω → PairMatrix p i), IsCenterSplitting X G →
    ∀ (φ : (p.Site → ℂ) → ℂ) (M L : ℝ), IsAngularTest φ M L →
      Integrable (fun ω => stepWeight p i cst α M₀ R₀ X G ω *
          angularIntegrand p i α X (centerOn p i cst α X G) φ ω)
        (extendedPairMeasure p α i X.P X.Hm) ∧
      ‖∫ ω, stepWeight p i cst α M₀ R₀ X G ω *
          angularIntegrand p i α X (centerOn p i cst α X G) φ ω
        ∂extendedPairMeasure p α i X.P X.Hm‖ ≤ C * (M + L) / (p.W : ℝ)

/-- **Bound on the good part**: for the domain constants of a center supply and every fixed
`R₀, M₀ ≥ 0` there is `C` with `‖E♯[1_good χ(b₂)(v*Jv - j_S)φ(ψ_α)]‖ ≤ C(M + L_φ)/W` for
`4 ≤ n ≤ TW` (plus integrability of the weighted integrand). -/
def GoodPartStatement (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) : Prop :=
  ∀ cst : CenterDomainConstants, CenterDomainContract cst → ∀ R₀ M₀ : ℝ, 0 ≤ R₀ → 0 ≤ M₀ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n W : ℕ) (hn : 4 ≤ n) (hW : 0 < W), (n : ℝ) ≤ T * (W : ℝ) →
      GoodPartAt ⟨n, W, b, hn, hW, hb, hb'⟩ θ cst M₀ R₀ C

/-- **The eigenvalue equation bounds `b₂`** (`K₀v = -G_N v`, so `b₂(v) ≤ ‖G_N‖²`),
deterministic: if `Hψ = Eψ`, the residual `H - G_e` is Hermitian and `H_R - E` is
invertible, then `b₂ ≤ ‖G_e‖²`. Proved as `pairEigenB2`. -/
def PairEigenB2Statement : Prop :=
  ∀ (p : Parameters) (i : ZMod p.n) (H : p.SiteMatrix) (G : PairMatrix p i),
    (H - embedPair p i G).IsHermitian → ∀ (E : ℝ) (ψ : p.Site → ℂ), H.mulVec ψ = (E : ℂ) • ψ →
      (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0 →
      pairB2 p i (H - embedPair p i G) E ψ ≤ ‖G‖ ^ 2

/-- **Pair-row norm tail**: Gaussian norm tails bound the probability of the pair-row event
by an arbitrarily high negative power of `W`, even after multiplication by `n/2`. For the
ring law, the pair-law probability that `‖H_SS‖ + ‖H_RS‖ > W/2` is at most `C/W`, uniformly
for `n ≤ TW`. -/
def PairRowNormTailStatement : Prop :=
  ∀ b T : ℝ, ∃ C : ℝ, ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n),
      physicalPairMeasure p model α i
          {H | (p.W : ℝ) / 2 < ‖pairBlock p i H‖ + ‖couplingBlock p i H‖} ≤
        ENNReal.ofReal (C / p.W)

/-!
## Removal of the weight
-/

section Removal

variable {p : Parameters} {i : ZMod p.n}

theorem norm_one_sub_stepWeight_le {model : p.GaussianRingModel} (cst : CenterDomainConstants)
    (α : Fin p.N) (M₀ R₀ : ℝ) (X : PairExtension p model) (G : X.Ω → PairMatrix p i)
    (ω : X.Ω) :
    ‖1 - stepWeight p i cst α M₀ R₀ X G ω‖ ≤
      (removedSet p i cst α M₀ R₀ X G).indicator 1 ω := by
  classical
  unfold stepWeight goodWeight
  split_ifs with hg
  · set x := pairB2 p i (residual p i X G ω) (physicalOrderedEigenvalue p (X.Hm ω) α)
      (physicalOrderedEigenvector p (X.Hm ω) α)
    have h1 : ‖(1 : ℂ) - ((stepSixCutoff R₀).χ x : ℂ)‖ = |1 - (stepSixCutoff R₀).χ x| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    refine (abs_one_sub_le_indicator R₀ x).trans ?_
    by_cases hx : R₀ < x
    · rw [Set.indicator_of_mem (show x ∈ Set.Ioi R₀ from hx),
        Set.indicator_of_mem (show ω ∈ removedSet p i cst α M₀ R₀ X G from Or.inr ⟨hg, hx⟩)]
      simp only [Pi.one_apply, le_refl]
    · rw [Set.indicator_of_notMem (show x ∉ Set.Ioi R₀ from hx)]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · rw [Set.indicator_of_mem (show ω ∈ removedSet p i cst α M₀ R₀ X G from Or.inl hg)]
    simp

/-- **Combination at one parameter set**: with the good-part bound `A` and
`P♯(removed) ≤ β`, `‖E♯[(v*Jv - j_S)φ(ψ_α)]‖ ≤ A + 2Mβ`. -/
theorem norm_integral_le_of_removed {model : p.GaussianRingModel} (cst : CenterDomainConstants)
    (α : Fin p.N) (M₀ R₀ : ℝ) (X : PairExtension p model) (G : X.Ω → PairMatrix p i)
    {φ : (p.Site → ℂ) → ℂ} {M L : ℝ} (hφ : IsAngularTest φ M L) {A β : ℝ} (hβ : 0 ≤ β)
    (hint : Integrable (fun ω => stepWeight p i cst α M₀ R₀ X G ω *
          angularIntegrand p i α X (centerOn p i cst α X G) φ ω)
        (extendedPairMeasure p α i X.P X.Hm))
    (hA : ‖∫ ω, stepWeight p i cst α M₀ R₀ X G ω *
          angularIntegrand p i α X (centerOn p i cst α X G) φ ω
        ∂extendedPairMeasure p α i X.P X.Hm‖ ≤ A)
    (hS : extendedPairMeasure p α i X.P X.Hm (removedSet p i cst α M₀ R₀ X G) ≤
      ENNReal.ofReal β) :
    ‖∫ ω, angularIntegrand p i α X (centerOn p i cst α X G) φ ω
        ∂extendedPairMeasure p α i X.P X.Hm‖ ≤ A + 2 * M * β := by
  have := BlockBand.QUE.PairResidual.extendedPairMeasure_isProbability p model α i X
  have hM := IsAngularTest.bound_nonneg hφ
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA
  by_cases hf : Integrable (fun ω => angularIntegrand p i α X (centerOn p i cst α X G) φ ω)
      (extendedPairMeasure p α i X.P X.Hm)
  · have hfB := ae_norm_integrand_le p model α i X (centerOn p i cst α X G)
      (fun ω => abs_dysonCenter_le_one p i cst α _ _) hφ
    have h := norm_integral_le_add_of_weight hf hint hfB (removedSet p i cst α M₀ R₀ X G)
      (norm_one_sub_stepWeight_le cst α M₀ R₀ X G)
    have hreal : (extendedPairMeasure p α i X.P X.Hm).real (removedSet p i cst α M₀ R₀ X G) ≤ β :=
      ENNReal.toReal_le_of_le_ofReal hβ hS
    have : 2 * M * (extendedPairMeasure p α i X.P X.Hm).real (removedSet p i cst α M₀ R₀ X G) ≤
        2 * M * β := mul_le_mul_of_nonneg_left hreal (by positivity)
    linarith
  · rw [integral_undef hf, norm_zero]
    positivity

end Removal

/-!
## The removed events
-/

section Events

variable {p : Parameters} {i : ZMod p.n}

open BlockBand.Angular.PairCoareaBridge in
/-- Under the pair law, the residual is Hermitian and `ψ_α` solves the eigenvalue equation
almost surely. -/
theorem ae_residual_eigen {model : p.GaussianRingModel} (α : Fin p.N)
    (X : PairExtension p model) (G : X.Ω → PairMatrix p i) (hG : IsCenterSplitting X G) :
    ∀ᵐ ω ∂extendedPairMeasure p α i X.P X.Hm, (residual p i X G ω).IsHermitian ∧
      (X.Hm ω).mulVec (physicalOrderedEigenvector p (X.Hm ω) α) =
        (physicalOrderedEigenvalue p (X.Hm ω) α : ℂ) •
          physicalOrderedEigenvector p (X.Hm ω) α := by
  obtain ⟨hGm, hlaw, -⟩ := hG
  have hGh : ∀ᵐ ω ∂X.P, (G ω).IsHermitian := by
    have h := ae_gueMeasure_isHermitian (PairSite p i) (pairTime p (splitS p))
    rw [← hlaw.map_eq, ae_map_iff hGm.aemeasurable
      (measurableSet_isHermitian (PairSite p i))] at h
    exact h
  have hGh' : ∀ᵐ ω ∂extendedPairMeasure p α i X.P X.Hm, (G ω).IsHermitian :=
    (withDensity_absolutelyContinuous _ _).ae_le hGh
  filter_upwards [hGh', BlockBand.QUE.PairResidual.ae_extendedPairMeasure p model α i X
    model.isPhysical.1, BlockBand.QUE.PairResidual.ae_extendedPairMeasure p model α i X
    (physicalOrderedEigenvector_eigenvector_ae p model)] with ω h1 h2 h3
  refine ⟨h2.sub (embedPair_isHermitian p i h1), ?_⟩
  funext x
  rw [h3 α x, Pi.smul_apply, smul_eq_mul]

/-- **The removed set is covered by the excluded events**, for `√R₀ ≤ W/2`:
`P♯(removed) ≤ P♯(¬domain) + P♯(pole) + P♯(pair rows) + P♯(‖G_e‖ > √R₀)`. -/
theorem removedSet_le (hEig : PairEigenB2Statement) {model : p.GaussianRingModel}
    (cst : CenterDomainConstants) (α : Fin p.N) (X : PairExtension p model)
    (G : X.Ω → PairMatrix p i) (hG : IsCenterSplitting X G) (M₀ R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (hW2 : Real.sqrt R₀ ≤ (p.W : ℝ) / 2) :
    extendedPairMeasure p α i X.P X.Hm (removedSet p i cst α M₀ R₀ X G) ≤
      extendedPairMeasure p α i X.P X.Hm
          {ω | ¬ InCenterDomain p i cst α (X.Hm ω - embedPair p i (G ω))
            (physicalOrderedEigenvalue p (X.Hm ω) α)} +
        physicalPairMeasure p model α i
          {H | ∃ μ : ℝ, (exteriorBlock p i H - (μ : ℂ) • 1).det = 0 ∧
            |physicalOrderedEigenvalue p H α - μ| < (p.W : ℝ) ^ (-M₀)} +
        physicalPairMeasure p model α i
          {H | (p.W : ℝ) / 2 < ‖pairBlock p i H‖ + ‖couplingBlock p i H‖} +
        ENNReal.ofReal ((p.n : ℝ) / 2) *
          gueMeasure (PairSite p i) (pairTime p (splitS p)) {g | Real.sqrt R₀ < ‖g‖} := by
  set μ := extendedPairMeasure p α i X.P X.Hm
  set S1 := {ω | ¬ InCenterDomain p i cst α (X.Hm ω - embedPair p i (G ω))
    (physicalOrderedEigenvalue p (X.Hm ω) α)}
  set S2 := {H : p.SiteMatrix | ∃ μ : ℝ, (exteriorBlock p i H - (μ : ℂ) • 1).det = 0 ∧
    |physicalOrderedEigenvalue p H α - μ| < (p.W : ℝ) ^ (-M₀)}
  set S3 := {H : p.SiteMatrix | (p.W : ℝ) / 2 < ‖pairBlock p i H‖ + ‖couplingBlock p i H‖}
  set B := {g : PairMatrix p i | Real.sqrt R₀ < ‖g‖}
  have hB : MeasurableSet B := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hcover : removedSet p i cst α M₀ R₀ X G ≤ᵐ[μ]
      (S1 ∪ X.Hm ⁻¹' S2 ∪ X.Hm ⁻¹' S3 ∪ G ⁻¹' B : Set X.Ω) := by
    filter_upwards [ae_residual_eigen α X G hG] with ω hω hrem
    obtain ⟨hherm, heig⟩ := hω
    have hext : exteriorBlock p i (residual p i X G ω) = exteriorBlock p i (X.Hm ω) :=
      exteriorBlock_sub_embedPair p i _ _
    by_contra hnot
    simp only [Set.mem_union, Set.mem_preimage, not_or] at hnot
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hnot
    have hS1 : InCenterDomain p i cst α (residual p i X G ω)
        (physicalOrderedEigenvalue p (X.Hm ω) α) := by
      by_contra h; exact h1 h
    have hS2 : ∀ μ' : ℝ, (exteriorBlock p i (residual p i X G ω) - (μ' : ℂ) • 1).det = 0 →
        (p.W : ℝ) ^ (-M₀) ≤ |physicalOrderedEigenvalue p (X.Hm ω) α - μ'| := by
      intro μ' hdet
      by_contra hlt
      rw [hext] at hdet
      exact h2 ⟨μ', hdet, lt_of_not_ge hlt⟩
    have hS3 : ‖pairBlock p i (X.Hm ω)‖ + ‖couplingBlock p i (X.Hm ω)‖ ≤ (p.W : ℝ) / 2 :=
      le_of_not_gt h3
    have hS4 : ‖G ω‖ ≤ Real.sqrt R₀ := le_of_not_gt h4
    have hgood : GoodOuter p i cst α M₀ (residual p i X G ω)
        (physicalOrderedEigenvalue p (X.Hm ω) α) := by
      refine ⟨hS1, hS2, ?_⟩
      unfold residual
      rw [pairBlock_sub_embedPair, couplingBlock_sub_embedPair]
      have := norm_sub_le (pairBlock p i (X.Hm ω)) (G ω)
      linarith
    rcases hrem with hbad | ⟨-, hb2⟩
    · exact hbad hgood
    · have hdet : (exteriorBlock p i (X.Hm ω) -
          (physicalOrderedEigenvalue p (X.Hm ω) α : ℂ) • 1).det ≠ 0 := by
        intro h0
        rw [← hext] at h0
        have := hS2 _ h0
        rw [sub_self, abs_zero] at this
        have hpos : 0 < (p.W : ℝ) ^ (-M₀) :=
          Real.rpow_pos_of_pos (by exact_mod_cast p.W_pos) _
        linarith
      have hle := hEig p i (X.Hm ω) (G ω) hherm _ _ heig hdet
      change R₀ < pairB2 p i (X.Hm ω - embedPair p i (G ω)) _ _ at hb2
      have hlt : R₀ < ‖G ω‖ ^ 2 := lt_of_lt_of_le hb2 hle
      have : Real.sqrt R₀ < ‖G ω‖ := by
        rw [← Real.sqrt_sq (norm_nonneg (G ω))]
        exact Real.sqrt_lt_sqrt hR₀ hlt
      linarith
  calc μ (removedSet p i cst α M₀ R₀ X G)
      ≤ μ (S1 ∪ X.Hm ⁻¹' S2 ∪ X.Hm ⁻¹' S3 ∪ G ⁻¹' B) := measure_mono_ae hcover
    _ ≤ μ S1 + μ (X.Hm ⁻¹' S2) + μ (X.Hm ⁻¹' S3) + μ (G ⁻¹' B) := by
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        exact measure_union_le _ _
    _ ≤ _ := by
        gcongr
        · exact extendedPairMeasure_preimage_le α X S2
        · exact extendedPairMeasure_preimage_le α X S3
        · exact extendedPairMeasure_gaussian_le α X G hG hB

end Events

/-!
## Arithmetic of the excluded events
-/

section Arith

theorem exp_tail_le {n W T c : ℝ} (hW : 0 < W) (hc : 0 < c) (hnW : n ≤ T * W) :
    n / 2 * Real.exp (-(c * (2 * W))) ≤ |T| / (4 * c ^ 2 * W) := by
  have hx : 0 ≤ c * (2 * W) := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hE : 2 * c ^ 2 * W ^ 2 ≤ Real.exp (c * (2 * W)) := by nlinarith
  have hpos : 0 < 2 * c ^ 2 * W ^ 2 := by positivity
  rw [Real.exp_neg]
  have h1 : (Real.exp (c * (2 * W)))⁻¹ ≤ (2 * c ^ 2 * W ^ 2)⁻¹ := inv_anti₀ hpos hE
  have hT : n ≤ |T| * W := hnW.trans (mul_le_mul_of_nonneg_right (le_abs_self T) hW.le)
  calc n / 2 * (Real.exp (c * (2 * W)))⁻¹ ≤ (|T| * W) / 2 * (2 * c ^ 2 * W ^ 2)⁻¹ :=
        mul_le_mul (by linarith) h1 (inv_nonneg.2 (Real.exp_pos _).le) (by positivity)
    _ = |T| / (4 * c ^ 2 * W) := by field_simp; ring

theorem pole_arith {n W T s : ℝ} (hW : 1 ≤ W) (hs : 0 < s) (hnW : n ≤ T * W) :
    n * (2 * W) * (2 * W + 1) * W ^ (-(4 : ℝ)) / Real.sqrt (2 * Real.pi * s) ≤
      6 * |T| / Real.sqrt (2 * Real.pi * s) / W := by
  have hW0 : 0 < W := by linarith
  have hsq : 0 < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.2 (by positivity)
  have h4 : W ^ (-(4 : ℝ)) = (W ^ 4)⁻¹ := by
    rw [Real.rpow_neg hW0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h4]
  have hT : n ≤ |T| * W := hnW.trans (mul_le_mul_of_nonneg_right (le_abs_self T) hW0.le)
  have hkey : n * (2 * W) * (2 * W + 1) ≤ 6 * |T| * W ^ 3 := by
    have h1 : 2 * W + 1 ≤ 3 * W := by linarith
    have h2 : n * (2 * W) ≤ |T| * W * (2 * W) := mul_le_mul_of_nonneg_right hT (by positivity)
    calc n * (2 * W) * (2 * W + 1) ≤ |T| * W * (2 * W) * (3 * W) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = 6 * |T| * W ^ 3 := by ring
  rw [div_div, div_le_div_iff₀ hsq (by positivity)]
  have : n * (2 * W) * (2 * W + 1) * (W ^ 4)⁻¹ ≤ 6 * |T| / W := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hW0]
    nlinarith
  rw [le_div_iff₀ hW0] at this
  nlinarith [hsq]

end Arith

/-!
## The assembly
-/

section Main

/-- The Gaussian tail at the pair threshold `√R₀ = C√s`, `R₀ = C²s`. -/
theorem gue_pair_tail_le {C c : ℝ} (hC : 0 < C)
    (htail : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : ℝ≥0),
      gueMeasure ι t {G | C * Real.sqrt ((t : ℝ) * (Fintype.card ι : ℝ)) < ‖G‖} ≤
        ENNReal.ofReal (Real.exp (-(c * (Fintype.card ι : ℝ)))))
    (p : Parameters) (i : ZMod p.n) {s : ℝ} (hs : 0 < s) :
    gueMeasure (PairSite p i) (pairTime p s) {g | Real.sqrt (C ^ 2 * s) < ‖g‖} ≤
      ENNReal.ofReal (Real.exp (-(c * (2 * (p.W : ℝ))))) := by
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * (p.W : ℝ) := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite p i]; push_cast; ring
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have ht : ((pairTime p s : ℝ≥0) : ℝ) * (Fintype.card (PairSite p i) : ℝ) = s := by
    rw [hcard, pairTime, Real.coe_toNNReal _ (by positivity)]
    field_simp
  have hthr : Real.sqrt (C ^ 2 * s) =
      C * Real.sqrt (((pairTime p s : ℝ≥0) : ℝ) * (Fintype.card (PairSite p i) : ℝ)) := by
    rw [ht, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le]
  rw [hthr, ← hcard]
  exact htail (PairSite p i) (pairTime p s)

/-- Monotonicity in `ϑ`: a smaller bulk margin gives a stronger statement. -/
theorem physicalAngularStatement_mono {b θ θ' T : ℝ} {hb : 0 < b} {hb' : b < 1 / 2}
    {w : PairCenterFamily} (hθ : θ' ≤ θ) (h : PhysicalAngularStatement b θ' T hb hb' w) :
    PhysicalAngularStatement b θ T hb hb' w := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun n W hn hW hnW model α hα i => ?_⟩
  exact hbound n W hn hW hnW model α ⟨hθ.trans hα.1, hα.2.trans (by linarith)⟩ i

/-- The bound at one parameter set, with explicit constants (`s = splitS p`, `R₀ = C_t²s`,
`M₀ = 4`). -/
theorem boundAt_of_parts {θ T Cg Cq W₀ Cr Ct ct : ℝ} (p : Parameters)
    (hnW : (p.n : ℝ) ≤ T * (p.W : ℝ)) (w : PairCenterFamily) (cst : CenterDomainConstants)
    (hfam : IsDysonCenterFamily cst w) (hCg : 0 ≤ Cg) (hCt : 0 < Ct) (hct : 0 < ct)
    (htail : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : ℝ≥0),
      gueMeasure ι t {G | Ct * Real.sqrt ((t : ℝ) * (Fintype.card ι : ℝ)) < ‖G‖} ≤
        ENNReal.ofReal (Real.exp (-(ct * (Fintype.card ι : ℝ)))))
    (hgood : GoodPartAt p θ cst 4 (Ct ^ 2 * splitS p) Cg)
    (hsmall : W₀ < (p.W : ℝ) → ∀ (model : p.GaussianRingModel) (α : Fin p.N),
      IsBulkRank p θ α → ∀ (i : ZMod p.n) (X : PairExtension p model)
        (G : X.Ω → PairMatrix p i), IsCenterSplitting X G →
        extendedPairMeasure p α i X.P X.Hm
            {ω | ¬ InCenterDomain p i cst α (X.Hm ω - embedPair p i (G ω))
              (physicalOrderedEigenvalue p (X.Hm ω) α)} ≤
          ENNReal.ofReal (Cq * (p.W : ℝ) ^ (1 - (2 : ℝ))))
    (hrow : ∀ (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n),
      physicalPairMeasure p model α i
          {H | (p.W : ℝ) / 2 < ‖pairBlock p i H‖ + ‖couplingBlock p i H‖} ≤
        ENNReal.ofReal (Cr / p.W))
    (hEig : PairEigenB2Statement) (hPole : PairPoleExclusionContract) :
    PhysicalAngularBoundAt p θ w
      (Cg + 2 * (|Cq| + 6 * |T| / Real.sqrt (2 * Real.pi * splitS p) + |Cr| +
          |T| / (4 * ct ^ 2)) +
        2 * max (max W₀ (2 * Real.sqrt (Ct ^ 2 * splitS p))) 0) := by
  set s : ℝ := splitS p with hsdef
  have hs : 0 < s := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  set R₀ : ℝ := Ct ^ 2 * s with hR₀def
  have hR₀ : 0 ≤ R₀ := by positivity
  set B₁ : ℝ := |Cq| + 6 * |T| / Real.sqrt (2 * Real.pi * s) + |Cr| + |T| / (4 * ct ^ 2)
    with hB₁def
  have hB₁ : 0 ≤ B₁ := by positivity
  set W₁ : ℝ := max (max W₀ (2 * Real.sqrt R₀)) 0 with hW₁def
  have hW₁ : 0 ≤ W₁ := le_max_right _ _
  intro model α hα i φ M L hφ
  set X := (w p model α i).X with hXdef
  obtain ⟨G, hG, hcenter⟩ := hfam p model α i
  have hcfun : (w p model α i).center = centerOn p i cst α X G := funext hcenter
  have hM := IsAngularTest.bound_nonneg hφ
  have hL := IsAngularTest.lip_nonneg hφ
  have hWpos : (0 : ℝ) < (p.W : ℝ) := by exact_mod_cast p.W_pos
  change ‖∫ ω, angularIntegrand p i α X (w p model α i).center φ ω
    ∂extendedPairMeasure p α i X.P X.Hm‖ ≤ _
  rw [hcfun]
  by_cases hlarge : W₁ < (p.W : ℝ)
  · have hW0 : W₀ < (p.W : ℝ) :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hlarge
    have hWR : Real.sqrt R₀ ≤ (p.W : ℝ) / 2 := by
      have : 2 * Real.sqrt R₀ ≤ W₁ := (le_max_right _ _).trans (le_max_left _ _)
      linarith
    obtain ⟨hint, hA⟩ := hgood model α hα i X G hG φ M L hφ
    have hS := removedSet_le hEig cst α X G hG 4 R₀ hR₀ hWR
    have h1 := hsmall hW0 model α hα i X G hG
    have h2 := hPole.pole_probability p model α i s hs le_rfl
      ((p.W : ℝ) ^ (-(4 : ℝ))) (Real.rpow_pos_of_pos hWpos _)
    have h3 := hrow model α i
    have h4 := gue_pair_tail_le hCt htail p i hs
    have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
    have e1 : Cq * (p.W : ℝ) ^ (1 - (2 : ℝ)) ≤ |Cq| / p.W := by
      rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (le_abs_self _) hWpos.le
    have e2 := pole_arith (n := (p.n : ℝ)) (W := (p.W : ℝ)) (T := T) hW1 hs hnW
    have e3 : Cr / (p.W : ℝ) ≤ |Cr| / p.W :=
      div_le_div_of_nonneg_right (le_abs_self _) hWpos.le
    have e4 := exp_tail_le (n := (p.n : ℝ)) (W := (p.W : ℝ)) (T := T) hWpos hct hnW
    have hβ : extendedPairMeasure p α i X.P X.Hm (removedSet p i cst α 4 R₀ X G) ≤
        ENNReal.ofReal (B₁ / p.W) := by
      refine hS.trans ?_
      have hsum : B₁ / p.W = |Cq| / p.W + 6 * |T| / Real.sqrt (2 * Real.pi * s) / p.W +
          |Cr| / p.W + |T| / (4 * ct ^ 2 * p.W) := by
        rw [hB₁def]; field_simp
      rw [hsum, ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
      gcongr
      · exact h1.trans (ENNReal.ofReal_le_ofReal e1)
      · exact h2.trans (ENNReal.ofReal_le_ofReal e2)
      · exact h3.trans (ENNReal.ofReal_le_ofReal e3)
      · calc ENNReal.ofReal ((p.n : ℝ) / 2) *
              gueMeasure (PairSite p i) (pairTime p s) {g | Real.sqrt R₀ < ‖g‖}
            ≤ ENNReal.ofReal ((p.n : ℝ) / 2) *
                ENNReal.ofReal (Real.exp (-(ct * (2 * (p.W : ℝ))))) := by gcongr
          _ = ENNReal.ofReal ((p.n : ℝ) / 2 * Real.exp (-(ct * (2 * (p.W : ℝ))))) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ ≤ ENNReal.ofReal (|T| / (4 * ct ^ 2 * p.W)) := ENNReal.ofReal_le_ofReal e4
    have hfin := norm_integral_le_of_removed cst α 4 R₀ X G hφ (by positivity) hint hA hβ
    refine hfin.trans ?_
    have hrhs : Cg * (M + L) / (p.W : ℝ) + 2 * M * (B₁ / p.W) =
        (Cg * (M + L) + 2 * M * B₁) / p.W := by ring
    rw [hrhs]
    apply div_le_div_of_nonneg_right _ hWpos.le
    nlinarith [mul_nonneg hW₁ (add_nonneg hM hL), mul_nonneg hB₁ hL]
  · have hprob := BlockBand.QUE.PairResidual.extendedPairMeasure_isProbability p model α i X
    have hfB := ae_norm_integrand_le p model α i X (centerOn p i cst α X G)
      (fun ω => abs_dysonCenter_le_one p i cst α _ _) hφ
    have h0 := norm_integral_le_of_norm_le_const hfB
    rw [probReal_univ, mul_one] at h0
    refine h0.trans ?_
    rw [le_div_iff₀ hWpos]
    have hWle : (p.W : ℝ) ≤ W₁ := le_of_not_gt hlarge
    have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
    nlinarith [mul_nonneg hCg (add_nonneg hM hL), mul_nonneg hB₁ (add_nonneg hM hL),
      mul_nonneg hW₁ hL]

/-- **The physical angular estimate from its parts**, for `0 < ϑ < 1/2` and every center
supply `w`: the good part (`GoodPartStatement`), the eigenvalue-equation bound
(`PairEigenB2Statement`), the `GUE` norm tail, the pair-row norm tail and the pole exclusion
`PairPoleExclusionContract` give `PhysicalAngularStatement`. The constant is chosen from
`b, ϑ, T` and the domain constants of `w`, before `n, W`; there is no width threshold. -/
theorem physicalAngularStatement_of_parts {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2)
    (hθ : 0 < θ) (hθ' : θ < 1 / 2) (hGood : GoodPartStatement b θ T hb hb')
    (hEig : PairEigenB2Statement) (hTail : GUENormTailStatement)
    (hRow : PairRowNormTailStatement) (hPole : PairPoleExclusionContract)
    (w : PairCenterFamily) (hw : IsCenterSupply w) :
    PhysicalAngularStatement b θ T hb hb' w := by
  obtain ⟨cst, hfam, hcd⟩ := hw
  obtain ⟨Ct, ct, hCt, hct, htail⟩ := hTail
  have hs : 0 < min (1 - 2 * b) b := lt_min (by linarith) hb
  obtain ⟨Cg, hCg, hgood⟩ := hGood cst hcd (Ct ^ 2 * min (1 - 2 * b) b) 4 (by positivity)
    (by norm_num)
  obtain ⟨Cq, W₀, hsmall⟩ := hcd.small b hb hb' θ T hθ hθ' 2
  obtain ⟨Cr, hrow⟩ := hRow b T
  refine ⟨Cg + 2 * (|Cq| + 6 * |T| / Real.sqrt (2 * Real.pi * min (1 - 2 * b) b) + |Cr| +
      |T| / (4 * ct ^ 2)) + 2 * max (max W₀ (2 * Real.sqrt (Ct ^ 2 * min (1 - 2 * b) b))) 0,
    by positivity, ?_⟩
  intro n W hn hW hnW
  exact boundAt_of_parts ⟨n, W, b, hn, hW, hb, hb'⟩ hnW w cst hfam hCg hCt hct htail
    (hgood n W hn hW hnW) (fun hW0 => hsmall _ rfl hnW hW0) (hrow _ rfl hnW) hEig hPole

/-- **The physical angular estimate** `PhysicalAngularLabel` for every `0 < ϑ`, from the same
hypotheses: the statement at `min ϑ (1/4)` extends to `ϑ` by monotonicity
(`physicalAngularStatement_mono`; see the module docstring). -/
theorem physicalAngularLabel_of_parts {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2)
    (hθ : 0 < θ) (hGood : GoodPartStatement b (min θ (1 / 4)) T hb hb')
    (hEig : PairEigenB2Statement) (hTail : GUENormTailStatement)
    (hRow : PairRowNormTailStatement) (hPole : PairPoleExclusionContract) :
    PhysicalAngularLabel b θ T hb hb' := fun w hw =>
  physicalAngularStatement_mono (min_le_left θ (1 / 4))
    (physicalAngularStatement_of_parts hb hb' (lt_min hθ (by norm_num))
      ((min_le_right θ (1 / 4)).trans_lt (by norm_num)) hGood hEig hTail hRow hPole w hw)

end Main

end BlockBand.Angular.Assembly
