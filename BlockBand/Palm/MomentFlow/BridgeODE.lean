module

public import BlockBand.Palm.MomentFlow.BridgeFlow

/-!
# A regular version of the conditional moments solves the moment flow

Conditionally on the eigenvalue path, the normalized moments
`F(σ, ξ) = E[∏ X_i(σ)^{ξ_i}/ξ_i! | 𝓛]` solve `∂_σ F = 𝓑_σ F`.

**Main theorem** `momentGeneratorBridge`: assuming only `DysonBrownianMotion N`
(clauses (b1) and (b3)), for every Hermitian `F`, every `a < s ≤ c`, every
`q` and every sector `r`, there is `Φ : ℝ → Occ N → FlowSample N → ℝ` with
* `Φ σ ξ = E[mono(X(σ), ξ) | pathSigma F a s c]` almost surely, for each `σ ∈ [s,c]`, `ξ` in the
  `r`-sector (`X_k(σ) = flowOverlap`, increasing labels, `N|q* u_k(σ)|²`);
* for almost every sample `ω`, `σ ↦ Φ σ · ω` solves `IsMomentFlowSolution (flowRate F a ω) r s c`
  (continuous on `[s,c]`, differentiable on `(s,c)` with derivative `momentGenerator (flowRate) Φ`).

*Measure:* `flowLaw N a`. *Proof:* `BridgeIdentity` (integrated conditional identity on the gap
events `B_δ`), `BridgeVersion` (jointly measurable version), `BridgeFlow` (Fubini, pull-out, a.s.
vanishing of the version's increment), then here: `ae_simple` ((b1): almost surely simple spectrum
at every `σ > a` and Hermitian `ω.1`), `ae_exists_gapGood` (the gap events exhaust a full-measure
set, by compactness of `[s,c]`), `psiV` (the continuous version `Φ̃(s) + ∫_{(0,σ-s]} 𝓑 Φ̃`),
`psiV_ae_eq`, and the fundamental theorem of calculus.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N : ℕ}

/-! ## Step 4: almost sure simple spectrum and the gap events -/

/-- From (b1): almost surely `ω.1` is Hermitian and the spectrum is simple at every `σ > a`. -/
theorem ae_simple (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (a : ℝ) :
    ∀ᵐ ω ∂flowLaw N a, ω.1.IsHermitian ∧
      ∀ σ : ℝ, a < σ → HasSimpleSpectrum N (flowMatrix F a ω σ) := by
  obtain ⟨hb1, -, -, -⟩ := hDBM (FlowSample N) (flowLaw N a) (flowFiltration N) (flowBM N)
    (flowInit F) (isHermitianBrownian_flowBM a) (measurable_flowInit F) (flowInit_isHermitian hF)
  filter_upwards [hb1, hermProj_ae_eq (N := N) a] with ω h1 hω
  refine ⟨by rw [← hω]; exact hermPart_isHermitian _, fun σ hσ => ?_⟩
  have ht : (0 : ℝ≥0) < Real.toNNReal (σ - a) := Real.toNNReal_pos.2 (by linarith)
  have := h1 _ ht
  rw [flowInit_add_flowBM, hω, Real.coe_toNNReal _ (by linarith),
    show a + (σ - a) = σ by ring] at this
  exact this

/-- The gap events `B_δ` (rational `δ > 0`) cover a full-measure set. -/
theorem ae_exists_gapGood (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s : ℝ} (has : a < s) (U : ℝ≥0) :
    ∀ᵐ ω ∂flowLaw N a, ∃ δ : ℚ, 0 < δ ∧ ω ∈ gapGood F a δ s U := by
  filter_upwards [ae_simple hDBM hF a] with ω hω
  obtain ⟨hH, hs⟩ := hω
  have hpos : ∀ p : Fin N × Fin N, ∃ δ : ℝ, 0 < δ ∧ (p.1 ≠ p.2 → ∀ v ∈ Icc (0 : ℝ) U,
      δ ≤ |flowEigenvalue F a ω (s + v) p.1 - flowEigenvalue F a ω (s + v) p.2|) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => absurd hp h⟩
    · have hc : ContinuousOn (fun v : ℝ => |flowEigenvalue F a ω (s + v) p.1 -
          flowEigenvalue F a ω (s + v) p.2|) (Icc 0 U) :=
        ((((continuous_flowEigenvalue hF a ω p.1).comp (continuous_const.add continuous_id)).sub
          ((continuous_flowEigenvalue hF a ω p.2).comp
            (continuous_const.add continuous_id))).abs).continuousOn
      obtain ⟨v₀, hv₀, hmin⟩ := isCompact_Icc.exists_isMinOn
        (nonempty_Icc.2 U.2) hc
      refine ⟨_, ?_, fun _ v hv => hmin hv⟩
      have hsim := hs (s + v₀) (by linarith [hv₀.1])
      rw [hasSimpleSpectrum_iff_strictMono (flowMatrix_isHermitian hF a hH _)] at hsim
      exact abs_pos.2 (sub_ne_zero.2 fun e => hp (hsim.injective e))
  choose δf hδf hδle using hpos
  rcases isEmpty_or_nonempty (Fin N × Fin N) with hE | hne
  · refine ⟨1, one_pos, fun v _ _ i j _ => ?_⟩
    exact (hE.false (i, j)).elim
  · obtain ⟨p₀, -, hp₀⟩ := Finset.exists_min_image Finset.univ δf Finset.univ_nonempty
    obtain ⟨δ, hδ0, hδ1⟩ := exists_rat_btwn (hδf p₀)
    refine ⟨δ, by exact_mod_cast hδ0, fun v hv0 hvU i j hij => ?_⟩
    exact hδ1.le.trans ((hp₀ (i, j) (Finset.mem_univ _)).trans
      (hδle (i, j) hij v ⟨hv0, hvU⟩))

/-! ## Step 5: the continuous version -/

/-- `Ψ_ζ(σ) = Φ̃_ζ(s) + ∫_{(0, σ-s]} 𝓑 Φ̃`. -/
def psiV (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ) (U : ℝ) (ζ : Occ N)
    (σ : ℝ) (ω : FlowSample N) : ℝ :=
  Vver F a s c q ζ s ω + ∫ r in Ioc (0 : ℝ) (σ - s), genC F a s U (Vver F a s c q) ζ r ω

theorem psiV_ae_eq (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s c : ℝ} (has : a < s) (q : Fin N → ℂ) (ζ : Occ N) {U : ℝ≥0}
    (hsc : s + U ≤ c) {σ : ℝ} (hσ : σ ∈ Icc s (s + U)) :
    psiV F a s c q U ζ σ =ᵐ[flowLaw N a] Vver F a s c q ζ σ := by
  set u : ℝ≥0 := Real.toNNReal (σ - s)
  have hu' : (u : ℝ) = σ - s := Real.coe_toNNReal _ (by linarith [hσ.1])
  have hu : u ≤ U := by
    rw [← NNReal.coe_le_coe, hu']; linarith [hσ.2]
  have hall : ∀ᵐ ω ∂flowLaw N a, ∀ δ : ℚ, 0 < δ → ω ∈ gapGood F a δ s U →
      incC F a s U (Vver F a s c q) ζ u ω = 0 := by
    rw [ae_all_iff]
    intro δ
    by_cases hδ : (0 : ℚ) < δ
    · filter_upwards [incV_ae_zero hDBM hF has q ζ hsc hu (δ := δ) (by exact_mod_cast hδ)] with
        ω hω _ hB using hω hB
    · exact Filter.Eventually.of_forall fun ω h => absurd h hδ
  filter_upwards [hall, ae_exists_gapGood hDBM hF has U] with ω hω hex
  obtain ⟨δ, hδ, hB⟩ := hex
  have h0 := hω δ hδ hB
  simp only [incC, hu'] at h0
  simp only [psiV]
  rw [show s + (σ - s) = σ by ring] at h0
  linarith

/-! ## Step 6: measurability, continuity and the ODE -/

theorem measurable_integral_Ioc_param {Ω : Type*} [MeasurableSpace Ω] {G : ℝ × Ω → ℝ}
    (hG : Measurable G) (s : ℝ) :
    Measurable (fun p : ℝ × Ω => ∫ r in Ioc (0 : ℝ) (p.1 - s), G (r, p.2)) := by
  have e : (fun p : ℝ × Ω => ∫ r in Ioc (0 : ℝ) (p.1 - s), G (r, p.2)) =
      fun p => ∫ r, (if 0 < r ∧ r ≤ p.1 - s then G (r, p.2) else 0) := by
    funext p
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
    funext r
    simp [Set.indicator, Set.mem_Ioc]
  rw [e]
  have hset : MeasurableSet {x : (ℝ × Ω) × ℝ | 0 < x.2 ∧ x.2 ≤ x.1.1 - s} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd ((measurable_fst.comp measurable_fst).sub_const s))
  have hf : Measurable (fun x : (ℝ × Ω) × ℝ =>
      if 0 < x.2 ∧ x.2 ≤ x.1.1 - s then G (x.2, x.1.2) else 0) :=
    Measurable.ite hset (hG.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
      measurable_const
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem measurable_psiV (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ) (U : ℝ)
    (ζ : Occ N) : Measurable (fun p : ℝ × FlowSample N => psiV F a s c q U ζ p.1 p.2) := by
  have hG := measurable_genC F a s U (f := Vver F a s c q)
    (fun ζ => measurable_momentVersion F a s c q ζ) ζ
  have hI := measurable_integral_Ioc_param hG s
  exact ((measurable_Vver F a s c q ζ s).comp measurable_snd).add hI

/-- The integrand `r ↦ 𝓑 Φ̃` is bounded and measurable along each sample on the gap event. -/
theorem intervalIntegrable_genC_Vver {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a s c δ : ℝ} (hδ : 0 < δ) (q : Fin N → ℂ) {U : ℝ≥0} {ω : FlowSample N}
    (hω : ω ∈ gapGood F a δ s U) (ζ : Occ N) (x y : ℝ) :
    IntervalIntegrable (fun r => genC F a s U (Vver F a s c q) ζ r ω) volume x y := by
  have hm : Measurable (fun r => genC F a s U (Vver F a s c q) ζ r ω) := by
    have h := (measurable_genC F a s U (f := Vver F a s c q)
      (fun ζ => measurable_momentVersion F a s c q ζ) ζ).comp
      (measurable_id.prodMk (measurable_const (a := ω)))
    simpa only [Function.comp_def, id] using h
  refine (intervalIntegrable_iff).2 ?_
  refine Measure.integrableOn_of_bounded (M := genBound N q δ ζ) ?_ hm.aestronglyMeasurable ?_
  · exact (measure_mono Set.uIoc_subset_uIcc).trans_lt (by simp) |>.ne
  · exact Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs]
      exact abs_genC_le hF hδ q (fun ζ σ ω => abs_momentVersion_le F a s c q ζ σ ω) hω ζ r

/-- On the gap event, `σ ↦ Ψ_ζ(σ)` agrees on `[s, ∞)` with the continuous primitive. -/
theorem psiV_eq_primitive {F : Matrix (Fin N) (Fin N) ℂ} {a s c : ℝ} (q : Fin N → ℂ) (U : ℝ)
    (ζ : Occ N) {σ : ℝ} (hσ : s ≤ σ) (ω : FlowSample N) :
    psiV F a s c q U ζ σ ω = Vver F a s c q ζ s ω +
      ∫ r in (0 : ℝ)..(σ - s), genC F a s U (Vver F a s c q) ζ r ω := by
  rw [psiV, intervalIntegral.integral_of_le (by linarith)]

theorem continuousOn_psiV {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s c δ : ℝ}
    (hδ : 0 < δ) (q : Fin N → ℂ) {U : ℝ≥0} {ω : FlowSample N} (hω : ω ∈ gapGood F a δ s U)
    (ζ : Occ N) (T : ℝ) :
    ContinuousOn (fun σ => psiV F a s c q U ζ σ ω) (Icc s T) := by
  have hc : Continuous (fun σ => Vver F a s c q ζ s ω +
      ∫ r in (0 : ℝ)..(σ - s), genC F a s U (Vver F a s c q) ζ r ω) :=
    continuous_const.add ((intervalIntegral.continuous_primitive
      (intervalIntegrable_genC_Vver hF hδ q hω ζ) 0).comp (continuous_id.sub continuous_const))
  exact hc.continuousOn.congr fun σ hσ => psiV_eq_primitive q U ζ hσ.1 ω

theorem continuousOn_rateC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s δ : ℝ}
    (hδ : 0 < δ) {U : ℝ≥0} {ω : FlowSample N} (hω : ω ∈ gapGood F a δ s U) (i j : Fin N) :
    Continuous (fun r => rateC F a s U ω r i j) := by
  by_cases hij : i = j
  · subst hij
    have e : (fun r => rateC F a s U ω r i i) = fun _ => 0 := by
      funext r; simp [rateC, flowRate]
    rw [e]; exact continuous_const
  · have hlam : ∀ k, Continuous (fun r => flowEigenvalue F a ω (s + clampTime U r) k) := fun k =>
      (continuous_flowEigenvalue hF a ω k).comp (continuous_const.add (continuous_clampTime U))
    unfold rateC flowRate
    refine (continuous_const.mul (((hlam i).sub (hlam j)).pow 2)).inv₀ fun r => ?_
    have hm := clampTime_mem U.2 r
    have hg := gap_ge_of_gapGood hF hω hm.1 hm.2 hij
    have hN : (0 : ℝ) < N := by exact_mod_cast i.pos
    have : 0 < (flowEigenvalue F a ω (s + clampTime U r) i -
        flowEigenvalue F a ω (s + clampTime U r) j) ^ 2 := by
      have := abs_pos.1 (lt_of_lt_of_le hδ hg)
      positivity
    exact (mul_pos hN this).ne'

theorem continuousOn_genC_psiV {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a s c δ : ℝ} (hδ : 0 < δ) (q : Fin N → ℂ) {U : ℝ≥0} {ω : FlowSample N}
    (hω : ω ∈ gapGood F a δ s U) (ζ : Occ N) (T : ℝ) :
    ContinuousOn (fun r => genC F a s U (psiV F a s c q U) ζ r ω) (Icc 0 T) := by
  have hψ : ∀ ζ', ContinuousOn (fun r => psiV F a s c q U ζ' (s + r) ω) (Icc 0 T) := by
    intro ζ'
    refine (continuousOn_psiV hF hδ q hω ζ' (s + T)).comp
      (by fun_prop : Continuous fun r : ℝ => s + r).continuousOn fun r hr => ?_
    simp only [Set.mem_Icc]
    constructor <;> linarith [hr.1, hr.2]
  unfold genC momentGenerator
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  exact (((continuousOn_rateC hF hδ hω i j).continuousOn).mul continuousOn_const).mul
    ((hψ _).sub (hψ _))

/-- **The moment-generator identity.** Assuming only `DysonBrownianMotion N`: a regular version of the conditional moments given the eigenvalue
path solves the deterministic moment flow along almost every path. -/
theorem momentGeneratorBridge (hDBM : DysonBrownianMotion N) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) {a s c : ℝ} (has : a < s) (hsc : s ≤ c) (q : Fin N → ℂ) (r : ℕ) :
    ∃ Φ : ℝ → Occ N → FlowSample N → ℝ,
      (∀ σ ∈ Icc s c, ∀ ξ ∈ sector N r,
        Φ σ ξ =ᵐ[flowLaw N a]
          (flowLaw N a)[fun ω => momentMonomial (fun k => flowOverlap F a q σ k ω) ξ |
            pathSigma F a s c]) ∧
      ∀ᵐ ω ∂flowLaw N a, IsMomentFlowSolution (flowRate F a ω) r s c (fun σ ξ => Φ σ ξ ω) := by
  set U : ℝ≥0 := Real.toNNReal (c - s)
  have hU : (U : ℝ) = c - s := Real.coe_toNNReal _ (by linarith)
  have hsU : s + (U : ℝ) = c := by rw [hU]; ring
  have hscU : s + (U : ℝ) ≤ c := hsU.le
  refine ⟨fun σ ξ ω => psiV F a s c q U ξ σ ω, ?_, ?_⟩
  · -- the version property
    intro σ hσ ξ _
    have hσ' : σ ∈ Icc s (s + U) := by rw [hsU]; exact hσ
    refine (psiV_ae_eq hDBM hF has q ξ hscU hσ').trans
      ((momentVersion_ae_eq F a s c q ξ σ).trans (condExp_congr_ae ?_))
    filter_upwards [ae_simple hDBM hF a] with ω hω
    exact clampedMoment_eq q ξ (flowMatrix_isHermitian hF a hω.1 _)
      (hω.2 σ (by linarith [hσ.1]))
  · -- the ODE along almost every path
    have hE2 : ∀ ζ ∈ sector N r, ∀ᵐ ω ∂flowLaw N a,
        ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) U)),
          Vver F a s c q ζ (s + v) ω = psiV F a s c q U ζ (s + v) ω := by
      intro ζ _
      have hmeas : MeasurableSet {x : ℝ × FlowSample N |
          Vver F a s c q ζ (s + x.1) x.2 = psiV F a s c q U ζ (s + x.1) x.2} := by
        have hsh : Measurable (fun x : ℝ × FlowSample N => (s + x.1, x.2)) :=
          ((measurable_const_add s).comp measurable_fst).prodMk measurable_snd
        have h1 : Measurable (fun x : ℝ × FlowSample N => Vver F a s c q ζ (s + x.1) x.2) := by
          have := (measurable_momentVersion F a s c q ζ).comp hsh
          simpa only [Function.comp_def] using this
        have h2 : Measurable (fun x : ℝ × FlowSample N => psiV F a s c q U ζ (s + x.1) x.2) := by
          have := (measurable_psiV F a s c q U ζ).comp hsh
          simpa only [Function.comp_def] using this
        exact measurableSet_eq_fun h1 h2
      refine (Measure.ae_ae_comm (μ := volume.restrict (Icc (0 : ℝ) U)) (ν := flowLaw N a)
        (p := fun v ω => Vver F a s c q ζ (s + v) ω = psiV F a s c q U ζ (s + v) ω) hmeas).1 ?_
      refine ae_restrict_of_forall_mem measurableSet_Icc fun v hv => ?_
      exact (psiV_ae_eq hDBM hF has q ζ hscU ⟨by linarith [hv.1], by linarith [hv.2]⟩).symm
    have hE2' : ∀ᵐ ω ∂flowLaw N a, ∀ ζ ∈ sector N r,
        ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) U)),
          Vver F a s c q ζ (s + v) ω = psiV F a s c q U ζ (s + v) ω :=
      (Filter.eventually_all_finset _).2 hE2
    filter_upwards [hE2', ae_exists_gapGood hDBM hF has U] with ω hω hex
    obtain ⟨δ, hδq, hB⟩ := hex
    have hδ : (0 : ℝ) < δ := by exact_mod_cast hδq
    intro ξ hξ
    refine ⟨continuousOn_psiV hF hδ q hB ξ c, fun σ hσ => ?_⟩
    -- the integral equation with `Ψ` in the integrand
    have hint : ∀ σ' ∈ Icc s c, psiV F a s c q U ξ σ' ω = Vver F a s c q ξ s ω +
        ∫ r in (0 : ℝ)..(σ' - s), genC F a s U (psiV F a s c q U) ξ r ω := by
      intro σ' hσ'
      rw [psiV_eq_primitive q U ξ hσ'.1 ω]
      congr 1
      rw [intervalIntegral.integral_of_le (by linarith [hσ'.1]),
        intervalIntegral.integral_of_le (by linarith [hσ'.1])]
      have hsub : Ioc (0 : ℝ) (σ' - s) ⊆ Icc 0 U :=
        fun r hr => ⟨hr.1.le, by rw [hU]; linarith [hr.2, hσ'.2]⟩
      have hae : ∀ᵐ v ∂(volume.restrict (Ioc (0 : ℝ) (σ' - s))),
          genC F a s U (Vver F a s c q) ξ v ω = genC F a s U (psiV F a s c q U) ξ v ω := by
        have h := ae_restrict_of_ae_restrict_of_subset hsub
          ((Filter.eventually_all_finset (sector N r)).2 fun ζ hζ => hω ζ hζ)
        filter_upwards [h] with v hv
        unfold genC
        exact momentGenerator_congr_sector _ (fun ζ hζ => hv ζ hζ) hξ
      exact setIntegral_congr_ae measurableSet_Ioc ((ae_restrict_iff' measurableSet_Ioc).1 hae)
    -- FTC at `σ - s ∈ (0, U)`
    have hx : σ - s ∈ Ioo (0 : ℝ) U := ⟨by linarith [hσ.1], by rw [hU]; linarith [hσ.2]⟩
    have hcont := continuousOn_genC_psiV hF hδ q hB ξ U (c := c)
    have hderiv : HasDerivAt (fun x => ∫ r in (0 : ℝ)..x, genC F a s U (psiV F a s c q U) ξ r ω)
        (genC F a s U (psiV F a s c q U) ξ (σ - s) ω) (σ - s) := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
      · refine (hcont.mono ?_).intervalIntegrable
        rw [uIcc_of_le hx.1.le]
        exact Icc_subset_Icc le_rfl hx.2.le
      · exact (hcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo _ hx
      · exact hcont.continuousAt (Icc_mem_nhds hx.1 hx.2)
    have hcomp := (hderiv.comp σ ((hasDerivAt_id σ).sub_const s)).const_add
      (Vver F a s c q ξ s ω)
    simp only [Function.comp_def, id, mul_one] at hcomp
    have hev : (fun σ' => psiV F a s c q U ξ σ' ω) =ᶠ[𝓝 σ] fun σ' =>
        Vver F a s c q ξ s ω + ∫ r in (0 : ℝ)..(σ' - s),
          genC F a s U (psiV F a s c q U) ξ r ω := by
      filter_upwards [Ioo_mem_nhds hσ.1 hσ.2] with σ' hσ'
      exact hint σ' (Ioo_subset_Icc_self hσ')
    have hval : genC F a s U (psiV F a s c q U) ξ (σ - s) ω =
        momentGenerator (flowRate F a ω σ) (fun ζ => psiV F a s c q U ζ σ ω) ξ := by
      unfold genC
      rw [rateC_eq (Ioo_subset_Icc_self hx), show s + (σ - s) = σ by ring]
    rw [← hval]
    exact hcomp.congr_of_eventuallyEq hev

end BlockBand.Palm.MomentFlow
