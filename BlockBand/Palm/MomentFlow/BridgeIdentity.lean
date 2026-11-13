module

public import BlockBand.Palm.MomentFlow.BridgeBrownian
public import BlockBand.Palm.MomentFlow.BridgeGenerator

/-!
# The conditional moment-generator identity along the flow (integrated form)

*Statement* (`integrated_moment_identity`): for Hermitian `F`, `a < s`, `u ≥ 0` with `s + u ≤ c`,
every `δ > 0`, every bounded `𝓛 = pathSigma F a s c`-measurable `Λ`, and every configuration `ξ`,
with the `𝓛`-measurable gap event `B_δ = {gaps ≥ δ at the rational times of [s, s+u]}`
(`gapGood`), the random variable
`1_{B_δ} Λ (mono(X(s+u), ξ) - mono(X(s), ξ) - ∫_{(0,u]} (𝓑_{s+r} mono(X(s+r), ·))(ξ) dr)`
is integrable with expectation `0`, where `X_k(σ) = flowOverlap` (`N|q* u_k(σ)|²`, increasing
labels) and `𝓑_σ = flowMomentGenerator F a ω σ` (rates `flowRate`). This is the identity
`E[mono(X(u)) - mono(X(s)) - ∫ 𝓑 mono | 𝓛] = 0` on the events `B_δ`, which exhaust the
non-collision event as `δ ↓ 0`. Measure `flowLaw N a`; no norm or uniformity statement.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Model.Construction
open scoped NNReal

variable {N : ℕ}

/-!
## Continuity of the eigenvalue path
-/

theorem flowMatrix_isHermitian {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (σ : ℝ) : (flowMatrix F a ω σ).IsHermitian :=
  (hF.add hω).add (hermitianBrownian_isHermitian _ _)

/-- Every eigenvalue path is continuous, for every sample. -/
theorem continuous_flowEigenvalue {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    (ω : FlowSample N) (k : Fin N) : Continuous (fun σ => flowEigenvalue F a ω σ k) := by
  by_cases hω : ω.1.IsHermitian
  · have hH := flowMatrix_isHermitian hF a hω
    have hc : Continuous (fun σ => (⟨flowMatrix F a ω σ, hH σ⟩ : HermitianMatrix (Fin N))) :=
      (continuous_flowMatrix F a ω).subtype_mk _
    refine ((continuous_increasingEigenvalue
      (Fin.cast (Fintype.card_fin N).symm k)).comp hc).congr fun σ => ?_
    simp [flowEigenvalue, freshEigenvalue, rawIncreasingEigenvalue_eq _ _ (hH σ)]
  · have hH : ∀ σ, ¬ (flowMatrix F a ω σ).IsHermitian := by
      intro σ h
      apply hω
      have e : ω.1 = flowMatrix F a ω σ - F - hermitianBrownian ω.2 (σ - a) := by
        simp only [flowMatrix]; abel
      rw [e]
      exact (h.sub hF).sub (hermitianBrownian_isHermitian _ _)
    have : (fun σ => flowEigenvalue F a ω σ k) = fun _ => 0 := by
      funext σ; simp [flowEigenvalue, freshEigenvalue, rawIncreasingEigenvalue, hH σ]
    rw [this]; exact continuous_const

/-!
## The gap event `B_δ`
-/

/-- `B_δ`: all eigenvalue gaps are at least `δ` at the rational times of `[s, s+u]`. -/
def gapGood (F : Matrix (Fin N) (Fin N) ℂ) (a δ s : ℝ) (u : ℝ≥0) : Set (FlowSample N) :=
  {ω | ∀ v : ℚ, 0 ≤ (v : ℝ) → (v : ℝ) ≤ u → ∀ i j : Fin N, i ≠ j →
    δ ≤ |flowEigenvalue F a ω (s + v) i - flowEigenvalue F a ω (s + v) j|}

/-- A continuous function `≥ δ` at the rationals of `[0,u]` is `≥ δ` on `[0,u]`. -/
theorem ge_on_Icc_of_rat {φ : ℝ → ℝ} (hφ : Continuous φ) {u δ : ℝ} (hu : 0 ≤ u)
    (h : ∀ v : ℚ, 0 ≤ (v : ℝ) → (v : ℝ) ≤ u → δ ≤ φ v) : ∀ x ∈ Icc 0 u, δ ≤ φ x := by
  have hS : IsClosed {x : ℝ | δ ≤ φ x} := isClosed_le continuous_const hφ
  rcases hu.eq_or_lt with rfl | hpos
  · intro x hx
    have : x = ((0 : ℚ) : ℝ) := by simp; exact le_antisymm hx.2 hx.1
    rw [this]; exact h 0 (by simp) (by simp)
  · have hsub : Ioo 0 u ∩ range ((↑) : ℚ → ℝ) ⊆ {x : ℝ | δ ≤ φ x} := by
      rintro x ⟨hx, v, rfl⟩
      exact h v hx.1.le hx.2.le
    have h1 : Ioo (0 : ℝ) u ⊆ closure (Ioo 0 u ∩ range ((↑) : ℚ → ℝ)) :=
      Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
    have h2 : Icc (0 : ℝ) u ⊆ {x : ℝ | δ ≤ φ x} := by
      rw [← closure_Ioo hpos.ne]
      exact closure_minimal (h1.trans (closure_minimal hsub hS)) hS
    exact fun x hx => h2 hx

theorem gap_ge_of_gapGood {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a δ s : ℝ}
    {u : ℝ≥0} {ω : FlowSample N} (hω : ω ∈ gapGood F a δ s u) {v : ℝ} (hv0 : 0 ≤ v)
    (hvu : v ≤ u) {i j : Fin N} (hij : i ≠ j) :
    δ ≤ |flowEigenvalue F a ω (s + v) i - flowEigenvalue F a ω (s + v) j| := by
  have hc : Continuous (fun x : ℝ => |flowEigenvalue F a ω (s + x) i -
      flowEigenvalue F a ω (s + x) j|) :=
    (((continuous_flowEigenvalue hF a ω i).comp (continuous_const.add continuous_id)).sub
      ((continuous_flowEigenvalue hF a ω j).comp (continuous_const.add continuous_id))).abs
  exact ge_on_Icc_of_rat hc u.2 (fun w hw0 hwu => hω w hw0 hwu i j hij) v ⟨hv0, hvu⟩

/-- `B_δ` is an event of the eigenvalue path on `[s, c]` when `s + u ≤ c`. -/
theorem measurableSet_gapGood (F : Matrix (Fin N) (Fin N) ℂ) (a δ : ℝ) {s c : ℝ} {u : ℝ≥0}
    (huc : s + u ≤ c) : MeasurableSet[pathSigma F a s c] (gapGood F a δ s u) := by
  have e : gapGood F a δ s u = ⋂ v : ℚ, ⋂ (_ : 0 ≤ (v : ℝ) ∧ (v : ℝ) ≤ u), ⋂ i : Fin N,
      ⋂ j : Fin N, ⋂ (_ : i ≠ j), {ω : FlowSample N | δ ≤
        |flowEigenvalue F a ω (s + v) i - flowEigenvalue F a ω (s + v) j|} := by
    ext ω; simp [gapGood, and_imp]
  rw [e]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun hv => MeasurableSet.iInter
    fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  have hσ : s + (v : ℝ) ∈ Icc s c := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hm : Measurable[pathSigma F a s c] (fun ω : FlowSample N =>
      |flowEigenvalue F a ω (s + v) i - flowEigenvalue F a ω (s + v) j|) :=
    continuous_abs.measurable.comp ((measurable_flowEigenvalue_pathSigma F a s c hσ i).sub
      (measurable_flowEigenvalue_pathSigma F a s c hσ j))
  exact hm measurableSet_Ici

/-!
## The Dyson Brownian motion data along the flow
-/

/-- The start time `s - a` of the Dyson Brownian motion. -/
def dysonStart (a s : ℝ) : ℝ≥0 := Real.toNNReal (s - a)

theorem flowInit_add_flowBM_start (F : Matrix (Fin N) (Fin N) ℂ) {a s : ℝ} (has : a ≤ s)
    (ω : FlowSample N) (v : ℝ≥0) :
    flowInit F ω + flowBM N (dysonStart a s + v) ω = flowMatrix F a (hermProj ω) (s + v) := by
  rw [flowInit_add_flowBM]
  congr 1
  simp only [dysonStart, NNReal.coe_add, Real.coe_toNNReal', max_eq_left (sub_nonneg.2 has)]
  ring

theorem flowInit_add_flowBM_isHermitian {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (ω : FlowSample N) (t : ℝ≥0) : (flowInit F ω + flowBM N t ω).IsHermitian :=
  (flowInit_isHermitian hF ω).add ((hermitianBrownian_isHermitian _ _).sub
    (hermitianBrownian_isHermitian _ _))

/-- The eigenvalue-path σ-algebra of the Dyson Brownian motion from the start time. -/
abbrev dysonPathSigma (F : Matrix (Fin N) (Fin N) ℂ) (s₀ : ℝ≥0) : MeasurableSpace (FlowSample N) :=
  ⨆ v : ℝ≥0, MeasurableSpace.comap
    (fun ω => dysonEigenvalue N (flowInit F ω + flowBM N (s₀ + v) ω)) inferInstance

/-- `𝓛`-measurable observables of the Hermitian projection are measurable for the eigenvalue-path
σ-algebra `dysonPathSigma` of the Dyson Brownian motion (relabelling `k ↦ k.rev`). -/
theorem measurable_comp_hermProj {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s c : ℝ}
    (has : a ≤ s) {Λ : FlowSample N → ℝ} (hΛ : Measurable[pathSigma F a s c] Λ) :
    Measurable[dysonPathSigma F (dysonStart a s)] (fun ω => Λ (hermProj ω)) := by
  have hle : MeasurableSpace.comap hermProj (pathSigma F a s c) ≤
      dysonPathSigma F (dysonStart a s) := by
    unfold pathSigma
    simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup₂_le fun σ hσ => iSup_le fun k => ?_
    set v₀ : ℝ≥0 := Real.toNNReal (σ - s)
    have hv : Measurable[dysonPathSigma F (dysonStart a s)]
        (fun ω => dysonEigenvalue N (flowInit F ω + flowBM N (dysonStart a s + v₀) ω)) :=
      Measurable.of_comap_le (le_iSup (fun v : ℝ≥0 => MeasurableSpace.comap
        (fun ω => dysonEigenvalue N (flowInit F ω + flowBM N (dysonStart a s + v) ω))
          inferInstance) v₀)
    have hσv : s + (v₀ : ℝ) = σ := by
      simp only [v₀, Real.coe_toNNReal', max_eq_left (sub_nonneg.2 hσ.1)]; ring
    have hfun : ((fun ω => flowEigenvalue F a ω σ k) ∘ hermProj) =
        (fun y : Fin N → ℝ => y k.rev) ∘
          (fun ω => dysonEigenvalue N (flowInit F ω + flowBM N (dysonStart a s + v₀) ω)) := by
      funext ω
      simp only [Function.comp_apply]
      rw [dysonEigenvalue_rev (flowInit_add_flowBM_isHermitian hF ω _),
        flowInit_add_flowBM_start F has, hσv]
      rfl
    rw [hfun]
    exact ((measurable_pi_apply _).comp hv).comap_le
  exact (hΛ.comp (comap_measurable hermProj)).mono hle le_rfl

/-- On `B_δ` the gap stopping time of level `n > 1/δ` (from `s - a`) is at least `u`. -/
theorem gapStop_ge {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s δ : ℝ} (has : a ≤ s)
    {u : ℝ≥0} {ω : FlowSample N} (hω : hermProj ω ∈ gapGood F a δ s u) {n : ℕ}
    (hn : 1 / (n : ℝ) < δ) :
    (u : WithTop ℝ≥0) ≤ gapStop N (fun t ω => flowInit F ω + flowBM N t ω) (dysonStart a s) n ω := by
  unfold gapStop
  refine le_iInf₂ fun w hw => ?_
  rw [WithTop.coe_le_coe]
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨i, j, hij, hgap⟩ := hw
  have hH := flowInit_add_flowBM_isHermitian hF ω (dysonStart a s + w)
  rw [← Fin.rev_rev i, ← Fin.rev_rev j, dysonEigenvalue_rev hH, dysonEigenvalue_rev hH,
    flowInit_add_flowBM_start F has] at hgap
  have hge := gap_ge_of_gapGood hF hω w.2 (le_of_lt (by exact_mod_cast hlt))
    (i := i.rev) (j := j.rev) (fun h => hij (Fin.rev_injective h))
  simp only [flowEigenvalue] at hge
  exact absurd (hge.trans hgap) (not_le.2 hn)

/-!
## The integrated identity
-/

/-- The CoareaPalm-side integrand `mono(X(s+u)) - mono(X(s)) - ∫_{(0,u]} 𝓑 mono`. -/
def momentIncrement (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ) (ξ : Occ N)
    (s : ℝ) (u : ℝ≥0) (ω : FlowSample N) : ℝ :=
  momentMonomial (fun k => flowOverlap F a q (s + u) k ω) ξ -
    momentMonomial (fun k => flowOverlap F a q s k ω) ξ -
    ∫ r in Ioc (0 : ℝ) u, flowMomentGenerator F a ω (s + r)
      (fun ζ => momentMonomial (fun k => flowOverlap F a q (s + r) k ω) ζ) ξ

theorem hasSimpleSpectrum_of_gap {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) {δ : ℝ}
    (hδ : 0 < δ) (h : ∀ i j : Fin N, i ≠ j → δ ≤ |freshEigenvalue K i - freshEigenvalue K j|) :
    HasSimpleSpectrum N K := by
  rw [hasSimpleSpectrum_iff_strictMono hK]
  have hmono : Monotone (freshEigenvalue K) := by
    intro i j hij
    simp only [freshEigenvalue, rawIncreasingEigenvalue_eq _ K hK]
    exact BlockBand.Foundations.Spectral.increasingEigenvalue_monotone hK
      (Fin.cast_le_cast _ |>.2 hij)
  refine hmono.strictMono_of_injective fun i j hij => ?_
  by_contra hne
  have := h i j hne
  rw [hij, sub_self, abs_zero] at this
  linarith

/-- The Dyson Brownian motion generator increment, stopped at the gap stopping time of level
`n > 1/δ`, equals `momentIncrement` on `B_δ` at samples with `hermProj ω = ω`. -/
theorem stopped_eq_momentIncrement {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a s δ : ℝ} (has : a ≤ s) (hδ : 0 < δ) (q : Fin N → ℂ) (ξ : Occ N) (u : ℝ≥0)
    {ω : FlowSample N} (hω₁ : hermProj ω = ω) (hω : ω ∈ gapGood F a δ s u) {n : ℕ}
    (hn : 1 / (n : ℝ) < δ) :
    stoppedProcess (fun v ω =>
        momentMonomial ((fun i => dysonOverlap N q
          (flowInit F ω + flowBM N (dysonStart a s + v) ω) i) ∘ Fin.revPerm) ξ -
        momentMonomial ((fun i => dysonOverlap N q
          (flowInit F ω + flowBM N (dysonStart a s) ω) i) ∘ Fin.revPerm) ξ -
        ∫ r in Ioc (0 : ℝ) v, angularGenerator N
          (dysonEigenvalue N (flowInit F ω + flowBM N (dysonStart a s + r.toNNReal) ω))
          (fun Y => momentMonomial (Y ∘ Fin.revPerm) ξ)
          (fun i => dysonOverlap N q (flowInit F ω + flowBM N (dysonStart a s + r.toNNReal) ω) i))
      (gapStop N (fun t ω => flowInit F ω + flowBM N t ω) (dysonStart a s) n) u ω =
      momentIncrement F a q ξ s u ω := by
  have hω' : hermProj ω ∈ gapGood F a δ s u := by rwa [hω₁]
  rw [stoppedProcess_eq_of_le (gapStop_ge hF has hω' hn)]
  have hH : ω.1.IsHermitian := by
    rw [← hω₁]; exact hermPart_isHermitian _
  have hHσ := flowMatrix_isHermitian hF a hH
  -- simple spectrum on `[s, s+u]`
  have hsimple : ∀ v : ℝ, 0 ≤ v → v ≤ u → HasSimpleSpectrum N (flowMatrix F a ω (s + v)) :=
    fun v hv0 hvu => hasSimpleSpectrum_of_gap (hHσ _) hδ fun i j hij =>
      gap_ge_of_gapGood hF hω hv0 hvu hij
  -- overlaps at time `s + v`
  have hX : ∀ v : ℝ≥0, (v : ℝ) ≤ u →
      (fun i => dysonOverlap N q (flowInit F ω + flowBM N (dysonStart a s + v) ω) i) ∘ Fin.revPerm =
        fun k => flowOverlap F a q (s + v) k ω := by
    intro v hvu
    funext k
    simp only [Function.comp_apply, Fin.revPerm_apply]
    rw [flowInit_add_flowBM_start F has, hω₁, dysonOverlap_rev (hHσ _) (hsimple v v.2 hvu)]
    rfl
  have hX0 : (fun i => dysonOverlap N q (flowInit F ω + flowBM N (dysonStart a s) ω) i) ∘
      Fin.revPerm = fun k => flowOverlap F a q s k ω := by
    have := hX 0 (by simp)
    simpa using this
  simp only [momentIncrement]
  rw [hX u le_rfl, hX0]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hr0 : 0 ≤ r := hr.1.le
  have hrt : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr0
  have hK := flowInit_add_flowBM_start F has ω r.toNNReal
  rw [hω₁, hrt] at hK
  rw [hK, angularGenerator_rev (hHσ _) (hsimple r hr0 hr.2) q ξ]
  rfl

/-- **Integrated conditional moment identity.** For Hermitian `F`, `a < s`, `s + u ≤ c`, `δ > 0`,
every bounded `𝓛 = pathSigma F a s c`-measurable `Λ`:
`E[1_{B_δ} Λ (mono(X(s+u)) - mono(X(s)) - ∫_{(0,u]} 𝓑 mono)] = 0`, integrably. -/
theorem integrated_moment_identity (hDBM : DysonBrownianMotion N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s c : ℝ} (has : a < s)
    (q : Fin N → ℂ) (ξ : Occ N) {u : ℝ≥0} (huc : s + u ≤ c) {δ : ℝ} (hδ : 0 < δ)
    {Λ : FlowSample N → ℝ} (hΛ : Measurable[pathSigma F a s c] Λ) (hΛb : ∃ C, ∀ ω, |Λ ω| ≤ C) :
    Integrable (fun ω => (gapGood F a δ s u).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        momentIncrement F a q ξ s u ω) (flowLaw N a) ∧
      ∫ ω, (gapGood F a δ s u).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        momentIncrement F a q ξ s u ω ∂flowLaw N a = 0 := by
  obtain ⟨-, -, hb3, -⟩ := hDBM (FlowSample N) (flowLaw N a) (flowFiltration N) (flowBM N)
    (flowInit F) (isHermitianBrownian_flowBM a) (measurable_flowInit F) (flowInit_isHermitian hF)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  have hnδ : 1 / (n : ℝ) < δ := by
    rw [div_lt_iff₀ (by exact_mod_cast hn0)]
    rw [div_lt_iff₀ hδ] at hn
    linarith
  set Λ' : FlowSample N → ℝ := fun ω => (gapGood F a δ s u).indicator (fun _ => (1 : ℝ)) ω * Λ ω
  have hΛ'm : Measurable[pathSigma F a s c] Λ' :=
    (measurable_const.indicator (measurableSet_gapGood F a δ huc)).mul hΛ
  have hΛ'b : ∃ C, ∀ ω, |Λ' (hermProj ω)| ≤ C := by
    obtain ⟨C, hC⟩ := hΛb
    refine ⟨max C 0, fun ω => ?_⟩
    simp only [Λ']
    by_cases h : hermProj ω ∈ gapGood F a δ s u
    · rw [Set.indicator_of_mem h, one_mul]; exact (hC _).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem h, zero_mul, abs_zero]; exact le_max_right _ _
  have hstart : 0 < dysonStart a s := by
    simp only [dysonStart, Real.toNNReal_pos]; linarith
  have key := hb3 (dysonStart a s) hstart q n hn0 (fun Y => momentMonomial (Y ∘ Fin.revPerm) ξ)
    (contDiff_momentMonomial 2 ξ |>.comp (by fun_prop)) u (fun ω => Λ' (hermProj ω))
    (measurable_comp_hermProj hF has.le hΛ'm) hΛ'b
  simp only at key
  have hae : (fun ω => Λ' (hermProj ω) * stoppedProcess (fun v ω =>
        momentMonomial ((fun i => dysonOverlap N q
          (flowInit F ω + flowBM N (dysonStart a s + v) ω) i) ∘ Fin.revPerm) ξ -
        momentMonomial ((fun i => dysonOverlap N q
          (flowInit F ω + flowBM N (dysonStart a s) ω) i) ∘ Fin.revPerm) ξ -
        ∫ r in Ioc (0 : ℝ) v, angularGenerator N
          (dysonEigenvalue N (flowInit F ω + flowBM N (dysonStart a s + r.toNNReal) ω))
          (fun Y => momentMonomial (Y ∘ Fin.revPerm) ξ)
          (fun i => dysonOverlap N q (flowInit F ω + flowBM N (dysonStart a s + r.toNNReal) ω) i))
      (gapStop N (fun t ω => flowInit F ω + flowBM N t ω) (dysonStart a s) n) u ω) =ᵐ[flowLaw N a]
      fun ω => (gapGood F a δ s u).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        momentIncrement F a q ξ s u ω := by
    filter_upwards [hermProj_ae_eq (N := N) a] with ω hω₁
    rw [hω₁]
    by_cases hω : ω ∈ gapGood F a δ s u
    · simp only [Λ']
      rw [stopped_eq_momentIncrement hF has.le hδ q ξ u hω₁ hω hnδ]
    · simp [Λ', hω]
  exact ⟨key.1.congr hae, (integral_congr_ae hae).symm.trans key.2⟩

end BlockBand.Palm.MomentFlow
