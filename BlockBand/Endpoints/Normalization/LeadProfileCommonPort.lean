module

public import BlockBand.Endpoints.Normalization.LeadProfileCommonPortAlgebra
public import BlockBand.Endpoints.Normalization.LeadProfileAssemblyInterfaces
public import BlockBand.Endpoints.Normalization.LeadFieldLaw
public import BlockBand.Endpoints.Clock.CommonPortRatiosEstimate
public import BlockBand.Layers.ScalarRecursion

/-!
# The physical lead-profile theorem: `LeadCommonPortStep`

**Main result.**
`leadCommonPortStep_of (hCP : CommonPortRatiosContract) (hMT : MatchedTracesContract) :
LeadCommonPortStep`: for `b ∈ (0,1/2)`, `κ, τ₀ > 0`, `T`, `Φ ∈ C_b(𝒫(𝕋))` and `ε > 0` there is
`W₀`; for every admissible `p` with `p.b = b`, `W ≥ W₀`, `τ₀ W ≤ n ≤ T W` and every
`e ∈ bulkInterval κ`, `|gaussianLeadSide p Φ e - leadLeadSide p Φ e| ≤ ε`. Measures: the
Gaussian side `growthPathLaw W b ⊗ layerLaw W b .common ⊗ CN(0, I_W)`, the lead side
`growthPathLaw W b ⊗ CN(0, I_{2W})` (exactly the definitions of `LeadCommonPortStep`).

**Proof.**
1. *Cylinder reduction* (`exists_cylinder_approx`): `Φ` is uniformly within `ε/8` of
   `ψ((∫ φ_i dν)_i)`, `|φ_i| ≤ 1`, `ψ` continuous on the cube.
2. *Ratios* (`cylinderVec_leadProfile_eq_ratioCube`): for every `J` and path `ω`,
   `(∫ φ_i dℛ_Jν^lead(h))_i = ratioCube (Y_{i,J})_i Y d h` with `Y = U*U`,
   `Y_{i,J} = U* diag(φ_i(pt_J)) U`, `-Y ⪯ Y_{i,J} ⪯ Y` and the constant default `d = (φ_i(0))_i`
   (the `δ_0` default of `leadProfile` on `h*Yh = 0`). If `Tr Y = 0` then `U = 0` and both sides
   are the same constant.
3. *Conditional comparison* (`abs_leadSections_sub_le`): Fubini (`prodAssoc`, `integral_prod`)
   writes both sides as `growthPathLaw`-integrals of conditional expectations; on the good event
   (`X = leadSchur e W (n-3) ω` Hermitian, `δ = matchedDistance b e X ≤ δ₀`)
   `CommonPortRatiosContract` (with `k = m`, test `ψ`, one rotation `J` at a time) bounds the
   conditional difference by `ε/2`.
4. *Bad event*: `X` is a.s. Hermitian (`srec_ae_pathSchur_isHermitian` through the measure
   preserving `pathAt`, `LeadFieldLaw.mp_pathAt`); `δ(X)` is the observable of
   `MatchedTracesContract.path` at `r = n - 3 ≥ 1` (`pathPortResolvent = (z_b - pathSchur)⁻¹`),
   so Markov at order `2` gives `P(δ > δ₀) ≤ (|C|√2/(Wδ₀))²`; the conditional difference is at
   most `2‖Φ‖` there.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal Matrix BoundedContinuousFunction ComplexOrder

namespace LeadProfileCommonPort

/-!
## 1. Elementary bounds
-/

theorem abs_avg_le (n : ℕ) (a : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M) (h : ∀ J, |a J| ≤ M) :
    |(n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, a J| ≤ M := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simpa using hM
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_mul, abs_inv, Nat.abs_cast]
  calc (n : ℝ)⁻¹ * |∑ J ∈ Finset.range n, a J| ≤ (n : ℝ)⁻¹ * ∑ _J ∈ Finset.range n, M := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun J _ => h J)
    _ = M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hn'.ne', one_mul]

theorem abs_avg_sub_le (n : ℕ) (a c : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M) (h : ∀ J, |a J - c J| ≤ M) :
    |(n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, a J - (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, c J| ≤ M := by
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  exact abs_avg_le n (fun J => a J - c J) hM h

theorem integrable_of_abs_le' {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

theorem abs_integral_le' {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f : α → ℝ} {M : ℝ} (hb : ∀ x, |f x| ≤ M) : |∫ x, f x ∂μ| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := M)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  simpa [Real.norm_eq_abs] using h

theorem abs_integral_sub_le' {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) {c : ℝ}
    (h : ∀ x, |f x - g x| ≤ c) : |∫ x, f x ∂μ - ∫ x, g x ∂μ| ≤ c := by
  rw [← integral_sub hf hg]
  exact abs_integral_le' μ h

theorem integral_avg {α : Type*} [MeasurableSpace α] (μ : Measure α) (n : ℕ)
    (F : ℕ → α → ℝ) (hF : ∀ J, Integrable (F J) μ) :
    ∫ x, (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, F J x ∂μ =
      (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, ∫ x, F J x ∂μ := by
  rw [integral_const_mul, integral_finsetSum _ fun J _ => hF J]

/-!
## 2. The conditional comparison on a good path
-/

/-- The conditional Gaussian side `E_{A,B,g} n⁻¹ Σ_J Φ(ℛ_J ν^lead(Lg))` at a fixed path. -/
def gaussSection (b e : ℝ) (n W : ℕ) (Φ : MassProfile →ᵇ ℝ) (ω : GrowthPath W) : ℝ :=
  ∫ x, (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n,
      Φ (leadProfile b e n W ω (commonPortProbe b e (leadSchur e W (n - 3) ω) x) J)
    ∂commonPortProbeLaw W b

/-- The conditional lead side `E_h n⁻¹ Σ_J Φ(ℛ_J ν^lead(h))` at a fixed path. -/
def leadSection (b e : ℝ) (n W : ℕ) (Φ : MassProfile →ᵇ ℝ) (ω : GrowthPath W) : ℝ :=
  ∫ h, (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, Φ (leadProfile b e n W ω h J)
    ∂circularVectorLaw (Fin 2 × Fin W)

theorem measurable_leadProfile_section (b e : ℝ) (n W J : ℕ) (ω : GrowthPath W) :
    Measurable (fun h : Fin 2 × Fin W → ℂ => leadProfile b e n W ω h J) := by
  have hg : Measurable (fun h : Fin 2 × Fin W → ℂ => (ω, h)) :=
    measurable_const.prodMk measurable_id
  have h0 := (measurable_leadProfile_joint b e n W J).comp hg
  exact h0

theorem measurable_probe_section (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    Measurable (fun x : LayerSample W .common × (Fin 1 × Fin W → ℂ) =>
      commonPortProbe b e (leadSchur e W r ω) x) := by
  have hg : Measurable (fun x : LayerSample W .common × (Fin 1 × Fin W → ℂ) => (ω, x)) :=
    measurable_const.prodMk measurable_id
  have h0 := (measurable_commonPortProbe_joint b e W r).comp hg
  exact h0

theorem abs_gaussSection_le (b e : ℝ) (n W : ℕ) (Φ : MassProfile →ᵇ ℝ) (ω : GrowthPath W) :
    |gaussSection b e n W Φ ω| ≤ ‖Φ‖ := by
  have := Clock.commonPortRatios_isProbabilityMeasure_probeLaw W b
  exact abs_integral_le' _ fun x => abs_avg_le n _ (norm_nonneg Φ) fun J => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _

theorem abs_leadSection_le (b e : ℝ) (n W : ℕ) (Φ : MassProfile →ᵇ ℝ) (ω : GrowthPath W) :
    |leadSection b e n W Φ ω| ≤ ‖Φ‖ :=
  abs_integral_le' _ fun x => abs_avg_le n _ (norm_nonneg Φ) fun J => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _

/-- **The conditional comparison.** If `Φ` is within `ε₁` of the cylinder functional
`ψ ∘ cylinderVec φ` (`|φ_i| ≤ 1`) and the common-port ratio comparison for the test `ψ` holds
at the old self-energy `X(ω) = leadSchur e W (n-3) ω` with error `ε₂` (for all clocks
`Y ⪰ 0`, `Tr Y > 0`, `-Y ⪯ Y_i ⪯ Y`, measurable defaults), then the conditional sides differ by
at most `2ε₁ + ε₂`. -/
theorem abs_leadSections_sub_le (b e : ℝ) (n W : ℕ) (Φ : MassProfile →ᵇ ℝ) {m : ℕ}
    (φ : Fin m → C(Torus, ℝ)) (hφ : ∀ i x, |φ i x| ≤ 1) (ψ : C(Fin m → Set.Icc (-1 : ℝ) 1, ℝ))
    {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (happrox : ∀ μ : MassProfile, |Φ μ - ψ (cylinderVec φ μ)| ≤ ε₁) (ω : GrowthPath W)
    (hcmp : ∀ (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      (Yt : Fin m → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      Y.PosSemidef → 0 < Y.trace.re → (∀ j, IsSandwichedOn (Yt j) Y) →
      ∀ d : (Fin 2 × Fin W → ℂ) → Fin m → ℝ, Measurable d →
        |(∫ x, ψ (ratioCube Yt Y d (commonPortProbe b e (leadSchur e W (n - 3) ω) x))
            ∂commonPortProbeLaw W b) -
          ∫ h, ψ (ratioCube Yt Y d h) ∂circularVectorLaw (Fin 2 × Fin W)| ≤ ε₂) :
    |gaussSection b e n W Φ ω - leadSection b e n W Φ ω| ≤ 2 * ε₁ + ε₂ := by
  have := Clock.commonPortRatios_isProbabilityMeasure_probeLaw W b
  have := massProfile_opensMeasurableSpace
  set r := n - 3 with hr
  set X := leadSchur e W r ω with hX
  set pr : LayerSample W .common × (Fin 1 × Fin W → ℂ) → Fin 2 × Fin W → ℂ :=
    fun x => commonPortProbe b e X x with hpr
  have hprm : Measurable pr := measurable_probe_section b e W r ω
  set Y := weightedClock b e W r ω (fun _ => 1) with hY
  let Yt : ℕ → Fin m → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    fun J i => weightedClock b e W r ω (fun x => φ i (leadPt n r J x))
  let d : (Fin 2 × Fin W → ℂ) → Fin m → ℝ := fun _ i => φ i 0
  let F : ℕ → (Fin 2 × Fin W → ℂ) → ℝ := fun J h => Φ (leadProfile b e n W ω h J)
  let Ψ : ℕ → (Fin 2 × Fin W → ℂ) → ℝ := fun J h => ψ (cylinderVec φ (leadProfile b e n W ω h J))
  have hΨ : ∀ J h, Ψ J h = ψ (ratioCube (Yt J) Y d h) := fun J h => by
    simp only [Ψ, Yt, d, hY]
    rw [cylinderVec_leadProfile_eq_ratioCube φ b e n W ω h J]
  have hFm : ∀ J, Measurable (F J) := fun J =>
    (measurable_massProfile_bcf Φ).comp (measurable_leadProfile_section b e n W J ω)
  have hΨm : ∀ J, Measurable (Ψ J) := fun J =>
    (ψ.continuous.comp (continuous_cylinderVec φ)).measurable.comp
      (measurable_leadProfile_section b e n W J ω)
  have hFb : ∀ J h, |F J h| ≤ ‖Φ‖ := fun J h => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  have hΨb : ∀ J h, |Ψ J h| ≤ ‖Φ‖ + ε₁ := fun J h => by
    have h1 := happrox (leadProfile b e n W ω h J)
    have h2 := hFb J h
    simp only [F, Ψ] at h1 h2 ⊢
    calc |ψ (cylinderVec φ (leadProfile b e n W ω h J))|
        ≤ |Φ (leadProfile b e n W ω h J)| +
            |Φ (leadProfile b e n W ω h J) - ψ (cylinderVec φ (leadProfile b e n W ω h J))| := by
          have := abs_sub_abs_le_abs_sub (ψ (cylinderVec φ (leadProfile b e n W ω h J)))
            (Φ (leadProfile b e n W ω h J))
          rw [abs_sub_comm (ψ _)] at this
          linarith
      _ ≤ ‖Φ‖ + ε₁ := add_le_add h2 h1
  have hFi : ∀ J, Integrable (F J) (circularVectorLaw (Fin 2 × Fin W)) := fun J =>
    integrable_of_abs_le' _ (hFm J) (hFb J)
  have hΨi : ∀ J, Integrable (Ψ J) (circularVectorLaw (Fin 2 × Fin W)) := fun J =>
    integrable_of_abs_le' _ (hΨm J) (hΨb J)
  have hFpi : ∀ J, Integrable (fun x => F J (pr x)) (commonPortProbeLaw W b) := fun J =>
    integrable_of_abs_le' _ ((hFm J).comp hprm) fun x => hFb J (pr x)
  have hΨpi : ∀ J, Integrable (fun x => Ψ J (pr x)) (commonPortProbeLaw W b) := fun J =>
    integrable_of_abs_le' _ ((hΨm J).comp hprm) fun x => hΨb J (pr x)
  -- the middle (Gaussian-ratio) comparison, one rotation at a time
  have hmid : ∀ J, |(∫ x, Ψ J (pr x) ∂commonPortProbeLaw W b) -
      ∫ h, Ψ J h ∂circularVectorLaw (Fin 2 × Fin W)| ≤ ε₂ := by
    intro J
    simp_rw [hΨ]
    rcases weightedClock_trace_pos_or b e W r ω with hpos | hU
    · refine hcmp Y (Yt J) ?_ hpos ?_ d measurable_const
      · exact weightedClock_posSemidef b e W r ω _ fun _ => zero_le_one
      · intro i
        exact weightedClock_isSandwiched b e W r ω _ fun x => hφ i _
    · have hY0 : Y = 0 := weightedClock_of_zero b e W r ω hU _
      have hconst : ∀ v, ratioCube (Yt J) Y d v = ratioCube (Yt J) Y d 0 := by
        intro v
        have hq : ∀ u : Fin 2 × Fin W → ℂ, quadForm Y u = 0 := by
          intro u; rw [hY0]; simp [quadForm]
        funext i
        simp only [ratioCube, hq, ite_true, d]
      simp_rw [hconst]
      simp only [integral_const, probReal_univ, one_smul, sub_self, abs_zero]
      exact hε₂
  -- assemble
  have hG : gaussSection b e n W Φ ω =
      (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, ∫ x, F J (pr x) ∂commonPortProbeLaw W b :=
    integral_avg _ n (fun J x => F J (pr x)) hFpi
  have hL : leadSection b e n W Φ ω =
      (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, ∫ h, F J h ∂circularVectorLaw (Fin 2 × Fin W) :=
    integral_avg _ n F hFi
  rw [hG, hL]
  refine abs_avg_sub_le n _ _ (by linarith) fun J => ?_
  have h1 : |(∫ x, F J (pr x) ∂commonPortProbeLaw W b) - ∫ x, Ψ J (pr x) ∂commonPortProbeLaw W b|
      ≤ ε₁ := abs_integral_sub_le' _ (hFpi J) (hΨpi J) fun x => happrox _
  have h3 : |(∫ h, Ψ J h ∂circularVectorLaw (Fin 2 × Fin W)) -
      ∫ h, F J h ∂circularVectorLaw (Fin 2 × Fin W)| ≤ ε₁ :=
    abs_integral_sub_le' _ (hΨi J) (hFi J) fun h => by
      rw [abs_sub_comm]; exact happrox _
  have h2 := hmid J
  calc |(∫ x, F J (pr x) ∂commonPortProbeLaw W b) - ∫ h, F J h ∂circularVectorLaw (Fin 2 × Fin W)|
      = |((∫ x, F J (pr x) ∂commonPortProbeLaw W b) - ∫ x, Ψ J (pr x) ∂commonPortProbeLaw W b) +
          ((∫ x, Ψ J (pr x) ∂commonPortProbeLaw W b) -
            ∫ h, Ψ J h ∂circularVectorLaw (Fin 2 × Fin W)) +
          ((∫ h, Ψ J h ∂circularVectorLaw (Fin 2 × Fin W)) -
            ∫ h, F J h ∂circularVectorLaw (Fin 2 × Fin W))| := by ring_nf
    _ ≤ ε₁ + ε₂ + ε₁ := (abs_add_three _ _ _).trans (by linarith)
    _ = 2 * ε₁ + ε₂ := by ring

/-!
## 3. Fubini: both sides as path integrals of the conditional sides
-/

/-- The Gaussian-side integrand on `path × (layer × g)` is jointly measurable. -/
theorem measurable_gaussIntegrand (b e : ℝ) (n W : ℕ) (Φ : MassProfile →ᵇ ℝ) :
    Measurable (fun z : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n,
        Φ (leadProfile b e n W z.1 (commonPortProbe b e (leadSchur e W (n - 3) z.1) z.2) J)) := by
  refine measurable_const.mul (Finset.measurable_sum _ fun J _ => ?_)
  have hpair : Measurable (fun z : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      (z.1, commonPortProbe b e (leadSchur e W (n - 3) z.1) z.2)) :=
    measurable_fst.prodMk (measurable_commonPortProbe_joint b e W (n - 3))
  have h0 := (measurable_leadProfile_joint b e n W J).comp hpair
  exact (measurable_massProfile_bcf Φ).comp h0

/-- The lead-side integrand on `path × h` is jointly measurable. -/
theorem measurable_leadIntegrand (b e : ℝ) (n W : ℕ) (Φ : MassProfile →ᵇ ℝ) :
    Measurable (fun z : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, Φ (leadProfile b e n W z.1 z.2 J)) :=
  measurable_const.mul (Finset.measurable_sum _ fun J _ =>
    (measurable_massProfile_bcf Φ).comp (measurable_leadProfile_joint b e n W J))

theorem gaussianLeadSide_eq_integral (p : Parameters) (Φ : MassProfile →ᵇ ℝ) (e : ℝ) :
    gaussianLeadSide p Φ e = ∫ ω, gaussSection p.b e p.n p.W Φ ω ∂growthPathLaw p.W p.b := by
  have := Clock.commonPortRatios_isProbabilityMeasure_layerLaw p.W p.b
  have := Clock.commonPortRatios_isProbabilityMeasure_probeLaw p.W p.b
  set G : GrowthPath p.W × (LayerSample p.W .common × (Fin 1 × Fin p.W → ℂ)) → ℝ :=
    fun z => (p.n : ℝ)⁻¹ * ∑ J ∈ Finset.range p.n,
      Φ (leadProfile p.b e p.n p.W z.1
        (commonPortProbe p.b e (leadSchur e p.W (p.n - 3) z.1) z.2) J) with hG
  have hmp := measurePreserving_prodAssoc (growthPathLaw p.W p.b) (layerLaw p.W p.b .common)
    (circularVectorLaw (Fin 1 × Fin p.W))
  have h1 : gaussianLeadSide p Φ e =
      ∫ y, G (MeasurableEquiv.prodAssoc y) ∂leadGaussianLaw p := rfl
  rw [h1, leadGaussianLaw, hmp.integral_comp' G]
  have hGi : Integrable G ((growthPathLaw p.W p.b).prod (commonPortProbeLaw p.W p.b)) :=
    integrable_of_abs_le' _ (measurable_gaussIntegrand p.b e p.n p.W Φ) fun z =>
      abs_avg_le _ _ (norm_nonneg Φ) fun J => by
        rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  have h2 := integral_prod G hGi
  exact h2

theorem leadLeadSide_eq_integral (p : Parameters) (Φ : MassProfile →ᵇ ℝ) (e : ℝ) :
    leadLeadSide p Φ e = ∫ ω, leadSection p.b e p.n p.W Φ ω ∂growthPathLaw p.W p.b := by
  have hi : Integrable (fun z : GrowthPath p.W × (Fin 2 × Fin p.W → ℂ) =>
      (p.n : ℝ)⁻¹ * ∑ J ∈ Finset.range p.n, Φ (leadProfile p.b e p.n p.W z.1 z.2 J))
      ((growthPathLaw p.W p.b).prod (circularVectorLaw (Fin 2 × Fin p.W))) :=
    integrable_of_abs_le' _ (measurable_leadIntegrand p.b e p.n p.W Φ) fun z =>
      abs_avg_le _ _ (norm_nonneg Φ) fun J => by
        rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  have h2 := integral_prod _ hi
  exact h2

theorem integrable_gaussSection (b e : ℝ) (n W : ℕ) (Φ : MassProfile →ᵇ ℝ) :
    Integrable (gaussSection b e n W Φ) (growthPathLaw W b) := by
  have := Clock.commonPortRatios_isProbabilityMeasure_probeLaw W b
  have hi : Integrable (fun z : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n,
        Φ (leadProfile b e n W z.1 (commonPortProbe b e (leadSchur e W (n - 3) z.1) z.2) J))
      ((growthPathLaw W b).prod (commonPortProbeLaw W b)) :=
    integrable_of_abs_le' _ (measurable_gaussIntegrand b e n W Φ) fun z =>
      abs_avg_le _ _ (norm_nonneg Φ) fun J => by
        rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  exact hi.integral_prod_left

theorem integrable_leadSection (b e : ℝ) (n W : ℕ) (Φ : MassProfile →ᵇ ℝ) :
    Integrable (leadSection b e n W Φ) (growthPathLaw W b) := by
  have hi : Integrable (fun z : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, Φ (leadProfile b e n W z.1 z.2 J))
      ((growthPathLaw W b).prod (circularVectorLaw (Fin 2 × Fin W))) :=
    integrable_of_abs_le' _ (measurable_leadIntegrand b e n W Φ) fun z =>
      abs_avg_le _ _ (norm_nonneg Φ) fun J => by
        rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  exact hi.integral_prod_left

/-!
## 4. The bad event
-/

/-- **The bad event is small.** For `r ≥ 1`, `0 < δ₀` and an `L²` bound `B ≥ 0` on the matched
distance of the length-`r` path, the event that `X = leadSchur e W r ω` is not Hermitian or has
`δ(X) > δ₀` has `growthPathLaw`-(outer) measure at most `(B/δ₀)²`. -/
theorem growthPathLaw_bad_le (b e : ℝ) (W r : ℕ) (hr : 1 ≤ r) {δ₀ B : ℝ} (hδ₀ : 0 < δ₀)
    (hB0 : 0 ≤ B)
    (hB : eLpNorm (fun y : PathSample W r => matchedDistance b e (pathSchur e y))
      (ENNReal.ofReal 2) (pathLaw W r b) ≤ ENNReal.ofReal B) :
    growthPathLaw W b {ω | ¬ ((leadSchur e W r ω).IsHermitian ∧
        matchedDistance b e (leadSchur e W r ω) ≤ δ₀)} ≤ ENNReal.ofReal ((B / δ₀) ^ (2 : ℝ)) := by
  have hmp := LeadFieldLaw.mp_pathAt W b hr
  have hS1 : growthPathLaw W b {ω | ¬ (leadSchur e W r ω).IsHermitian} = 0 := by
    have hae : ∀ᵐ ω ∂growthPathLaw W b, (leadSchur e W r ω).IsHermitian :=
      hmp.quasiMeasurePreserving.ae (BlockBand.Layers.srec_ae_pathSchur_isHermitian W r b e)
    exact ae_iff.mp hae
  have hmeasT : MeasurableSet {y : PathSample W r | δ₀ < matchedDistance b e (pathSchur e y)} :=
    measurableSet_lt measurable_const
      ((BlockBand.Layers.srec_measurable_matchedDistance b e W).comp
        (BlockBand.Layers.measurable_pathSchur W r e))
  have hT := BlockBand.Layers.srec_markov (p := 2) (by norm_num) hB0 hδ₀ hB
  have hS2 : growthPathLaw W b {ω | δ₀ < matchedDistance b e (leadSchur e W r ω)} ≤
      ENNReal.ofReal ((B / δ₀) ^ (2 : ℝ)) := by
    have he : {ω | δ₀ < matchedDistance b e (leadSchur e W r ω)} =
        pathAt W r ⁻¹' {y | δ₀ < matchedDistance b e (pathSchur e y)} := rfl
    rw [he, hmp.measure_preimage hmeasT.nullMeasurableSet]
    exact (measure_mono fun y (hy : δ₀ < _) => (le_of_lt hy : δ₀ ≤ _)).trans hT
  have hsub : {ω | ¬ ((leadSchur e W r ω).IsHermitian ∧
      matchedDistance b e (leadSchur e W r ω) ≤ δ₀)} ⊆
      {ω | ¬ (leadSchur e W r ω).IsHermitian} ∪
        {ω | δ₀ < matchedDistance b e (leadSchur e W r ω)} := by
    intro ω hω
    by_cases hH : (leadSchur e W r ω).IsHermitian
    · exact Or.inr (lt_of_not_ge fun h => hω ⟨hH, h⟩)
    · exact Or.inl hH
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal ((B / δ₀) ^ (2 : ℝ)) := by rw [hS1]; exact add_le_add le_rfl hS2
    _ = _ := zero_add _

end LeadProfileCommonPort

open LeadProfileCommonPort

/-- **The common-port step of the physical lead-profile theorem** (`LeadCommonPortStep`), from
`ClocksCommonPort.CommonPortRatiosContract` (applied conditionally on the old path at
`X = leadSchur e W (n-3) ω`) and `Layers.MatchedTracesContract.path` (at `r = n - 3`, order `2`,
for the scalar exceptional set `δ > δ₀`). Uniformity: `W₀` depends on `b, κ, τ₀, T, Φ, ε` only, and the
bound holds for every admissible `p` with `p.b = b`, `W ≥ W₀`, `τ₀W ≤ n ≤ TW` and every
`e ∈ bulkInterval κ`.
-/
theorem leadCommonPortStep_of (hCP : CommonPortRatiosContract) (hMT : MatchedTracesContract) :
    LeadCommonPortStep := by
  intro b hb hb' κ τ₀ T hκ hτ₀ Φ ε hε
  obtain ⟨m, φ, ψ, hφ, happrox⟩ := exists_cylinder_approx Φ (ε / 8) (by positivity)
  obtain ⟨δ₀, W₁, hδ₀, hcp⟩ := hCP b hb hb' κ hκ m ψ (ε / 4) (by positivity)
  obtain ⟨ε₀, C, hε₀, hpath⟩ := hMT.path b hb hb' κ T hκ
  set K : ℝ := |C| * Real.sqrt 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨max (max W₁ 1) (max ⌈2 / ε₀⌉₊ (max ⌈4 / τ₀⌉₊
    (⌈4 * ‖Φ‖ * K ^ 2 / (ε * δ₀ ^ 2)⌉₊ + 1))), ?_⟩
  intro p hpb hW hnlo hnhi e he
  subst hpb
  have hW1 : W₁ ≤ p.W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWone : 1 ≤ p.W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWpos : 0 < p.W := hWone
  have hW2 : ⌈2 / ε₀⌉₊ ≤ p.W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW3 : ⌈4 / τ₀⌉₊ ≤ p.W :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hW
  have hW4 : ⌈4 * ‖Φ‖ * K ^ 2 / (ε * δ₀ ^ 2)⌉₊ + 1 ≤ p.W :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hW
  have hWr : (1 : ℝ) ≤ p.W := by exact_mod_cast hWone
  have hWr0 : (0 : ℝ) < p.W := by linarith
  -- `n ≥ 4`, so `r = n - 3 ≥ 1`
  have hn4 : 4 ≤ p.n := by
    have h1 : 4 / τ₀ ≤ (p.W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hW3)
    have h2 : (4 : ℝ) ≤ τ₀ * p.W := by
      have := (div_le_iff₀ hτ₀).mp h1; linarith
    have h3 : (4 : ℝ) ≤ p.n := h2.trans hnlo
    exact_mod_cast h3
  have hr1 : 1 ≤ p.n - 3 := by omega
  have hrT : ((p.n - 3 : ℕ) : ℝ) ≤ T * p.W :=
    le_trans (by exact_mod_cast Nat.sub_le _ _) hnhi
  have h2W : (2 : ℝ) ≤ ε₀ * p.W := by
    have h1 : 2 / ε₀ ≤ (p.W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hW2)
    have := (div_le_iff₀ hε₀).mp h1; linarith
  -- Markov for the scalar exceptional set
  set B : ℝ := K / p.W with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hmk := hpath p.W hWpos 2 le_rfl h2W (p.n - 3) hr1 hrT e he
  have hB : eLpNorm (fun y : PathSample p.W (p.n - 3) => matchedDistance p.b e (pathSchur e y))
      (ENNReal.ofReal 2) (pathLaw p.W (p.n - 3) p.b) ≤ ENNReal.ofReal B := by
    refine le_trans hmk (ENNReal.ofReal_le_ofReal ?_)
    rw [hBdef, hK]
    gcongr
    exact le_abs_self C
  have hbad := growthPathLaw_bad_le p.b e p.W (p.n - 3) hr1 hδ₀ hB0 hB
  -- assemble
  set P := growthPathLaw p.W p.b with hP
  set S := {ω : GrowthPath p.W | ¬ ((leadSchur e p.W (p.n - 3) ω).IsHermitian ∧
    matchedDistance p.b e (leadSchur e p.W (p.n - 3) ω) ≤ δ₀)} with hS
  set S' := toMeasurable P S with hS'
  have hS'm : MeasurableSet S' := measurableSet_toMeasurable P S
  rw [gaussianLeadSide_eq_integral, leadLeadSide_eq_integral,
    ← integral_sub (integrable_gaussSection _ _ _ _ Φ) (integrable_leadSection _ _ _ _ Φ)]
  set g : GrowthPath p.W → ℝ := fun ω => ε / 2 + 2 * ‖Φ‖ * S'.indicator 1 ω with hg
  have hgi : Integrable g P :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).indicator hS'm).const_mul _)
  have hle : ∀ ω, ‖gaussSection p.b e p.n p.W Φ ω - leadSection p.b e p.n p.W Φ ω‖ ≤ g ω := by
    intro ω
    rw [Real.norm_eq_abs]
    by_cases hω : ω ∈ S'
    · simp only [hg, Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have h1 := abs_gaussSection_le p.b e p.n p.W Φ ω
      have h2 := abs_leadSection_le p.b e p.n p.W Φ ω
      have h3 := abs_sub _ _ |>.trans (add_le_add h1 h2)
      linarith
    · simp only [hg, Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hgood : (leadSchur e p.W (p.n - 3) ω).IsHermitian ∧
          matchedDistance p.b e (leadSchur e p.W (p.n - 3) ω) ≤ δ₀ := by
        by_contra hc
        exact hω (subset_toMeasurable P S hc)
      have := abs_leadSections_sub_le p.b e p.n p.W Φ φ hφ ψ (by positivity : (0 : ℝ) ≤ ε / 8)
        (by positivity : (0 : ℝ) ≤ ε / 4) happrox ω
        (fun Y Yt hY htr hsand d hd =>
          hcp p.W hWpos hW1 _ hgood.1 e he hgood.2 Y Yt hY htr hsand d hd)
      linarith
  have hint : ∫ ω, g ω ∂P = ε / 2 + 2 * ‖Φ‖ * P.real S' := by
    have h2 : Integrable (fun ω => 2 * ‖Φ‖ * S'.indicator (1 : GrowthPath p.W → ℝ) ω) P :=
      ((integrable_const (1 : ℝ)).indicator hS'm).const_mul _
    have h3 : ∫ ω, g ω ∂P =
        ∫ ω, ((fun _ => ε / 2) ω + (fun ω => 2 * ‖Φ‖ * S'.indicator 1 ω) ω) ∂P := rfl
    rw [h3, integral_add (integrable_const _) h2, integral_const, integral_const_mul,
      integral_indicator_one hS'm]
    simp [hP]
  have hreal : P.real S' ≤ (B / δ₀) ^ (2 : ℝ) := by
    rw [measureReal_def, hS', measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbad
  have hsmall : 2 * ‖Φ‖ * (B / δ₀) ^ (2 : ℝ) ≤ ε / 2 := by
    rw [Real.rpow_two]
    have hN : 4 * ‖Φ‖ * K ^ 2 / (ε * δ₀ ^ 2) ≤ (p.W : ℝ) := by
      have h1 := Nat.le_ceil (4 * ‖Φ‖ * K ^ 2 / (ε * δ₀ ^ 2))
      have h2 : ((⌈4 * ‖Φ‖ * K ^ 2 / (ε * δ₀ ^ 2)⌉₊ + 1 : ℕ) : ℝ) ≤ p.W := by exact_mod_cast hW4
      push_cast at h2
      linarith
    have hN' : 4 * ‖Φ‖ * K ^ 2 ≤ p.W * (ε * δ₀ ^ 2) := (div_le_iff₀ (by positivity)).mp hN
    have hfrac : (B / δ₀) ^ 2 = K ^ 2 / ((p.W : ℝ) ^ 2 * δ₀ ^ 2) := by
      rw [hBdef]; field_simp
    rw [hfrac, mul_div_assoc', div_le_iff₀ (by positivity)]
    have hWW : (p.W : ℝ) ≤ (p.W : ℝ) ^ 2 := by nlinarith
    have : p.W * (ε * δ₀ ^ 2) ≤ (p.W : ℝ) ^ 2 * (ε * δ₀ ^ 2) :=
      mul_le_mul_of_nonneg_right hWW (by positivity)
    nlinarith
  calc |∫ ω, (gaussSection p.b e p.n p.W Φ ω - leadSection p.b e p.n p.W Φ ω) ∂P|
      = ‖∫ ω, (gaussSection p.b e p.n p.W Φ ω - leadSection p.b e p.n p.W Φ ω) ∂P‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ ω, g ω ∂P := norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hle)
    _ = ε / 2 + 2 * ‖Φ‖ * P.real S' := hint
    _ ≤ ε / 2 + 2 * ‖Φ‖ * (B / δ₀) ^ (2 : ℝ) := by gcongr
    _ ≤ ε := by linarith

end BlockBand.Endpoints.Normalization
