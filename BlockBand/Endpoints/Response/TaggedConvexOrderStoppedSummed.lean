module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWickDefs
public import BlockBand.Endpoints.Response.TaggedConvexOrderStoppedRemoval
public import BlockBand.Endpoints.Response.TaggedConvexOrder

/-!
# The stopped remainder input from the summed contracting-words bound

Fixed `0 < b < 1/2`, bulk `E`, `s > 0`, tagged sequences at the constant energy `E`; path law
`growthPathLaw W b`, probe `circularVectorLaw`; the trace stop of the one-tag family from `εW`,
`ε = s/2`, at every level `K > 0`; uniform in `m ≤ M` and in the partial ranges `k+1 ≤ l' ≤ n`.

* `tcx_stopped_step`: one stopped step is bounded by the summand of
  `ContractingWordsContract.summed` (tower property `∫ E_l[·] = ∫ ·`, pull-out
  `E_l[1_A f] = 1_A E_l[f]` on `A ∈ growthSigma W l`).
* `tcwStoppedRemainderCoreFixed_of_summed`: the stopped remainder input from the summed contract.
* `tcoTagComparisonCoreFixed_of_wick`, `taggedConvexOrder_fixed_of_wick`: the fixed-energy tag
  comparison core and the fixed-energy tagged convex order theorem, with the Wick moment input
  `TcxWickMoment`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionUniform
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal NNReal

/-- **One stopped step from the summed contract** (tower property and pull-out on
`A = {l < σ_K}`): with `F_j = polyValue_j Φ_m` and `𝒜 = wordGenerator` at any time `t`,
`|E[1_A r_l(m)]| ≤ E|1_A(E_l[1_A(F_{l+1} - F_l)] - W⁻¹𝒜Φ_m)|`, the summand of
`ContractingWordsContract.summed`. Uses `TcxWickMoment` (`F_j = E_h Z_j^m`), `TcxWickGenerator`
(`Re 𝒜Φ_m = H_l` a.s.) and `A ∈ growthSigma W l`.
-/
theorem tcx_stopped_step (hCount : ConditionalBlockGUECount) (hWick : TcxWickMoment)
    (hGen : TcxWickGenerator) {b e : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2) (he1 : -2 < e)
    (he2 : e < 2) {W : ℕ} (hW : 0 < W) {k l m : ℕ} {K ε t : ℝ}
    (h1 : Integrable (fun x => lmf_tagResponseClock b e W (l + 1) k x ^ m) (probedClockLaw W b))
    (h0 : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ m) (probedClockLaw W b))
    (h2 : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ (m - 2 + 2))
      (probedClockLaw W b)) :
    ENNReal.ofReal |∫ ω, (tcw_alive b e W k K ε l).indicator (tcw_rem b e W l k m) ω
        ∂growthPathLaw W b| ≤
      ∫⁻ ω, ‖(tcw_alive b e W k K ε l).indicator (fun ω =>
          (growthPathLaw W b)[(tcw_alive b e W k K ε l).indicator (fun ω =>
              polyValue b e (tcw_tagFamily k) tcw_noInterval W (l + 1) ω (tcx_wickPoly m) -
                polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω (tcx_wickPoly m)) |
              growthSigma W l] ω -
            (W : ℂ)⁻¹ * polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω
              (wordGenerator b e tcw_noInterval t (tcx_wickPoly m))) ω‖ₑ ∂growthPathLaw W b := by
  have hP := tco_isProbabilityMeasure_growthPathLaw W b
  set μ := growthPathLaw W b
  set A := tcw_alive b e W k K ε l
  have hAm : MeasurableSet A := tcx_measurableSet_alive b e W k K ε l
  have hAl : MeasurableSet[growthSigma W l] A := tcx_measurableSet_alive_growthSigma b e W k K ε l
  have hle := tcx_growthSigma_le W l
  set G : GrowthPath W → ℂ := fun ω => polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω
    (wordGenerator b e tcw_noInterval t (tcx_wickPoly m))
  set Fr : ℕ → GrowthPath W → ℝ := fun j => tcw_F b e W j k m
  set g : GrowthPath W → ℂ := fun ω => ((Fr (l + 1) ω - Fr l ω : ℝ) : ℂ)
  have hg : (fun ω => polyValue b e (tcw_tagFamily k) tcw_noInterval W (l + 1) ω (tcx_wickPoly m) -
      polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω (tcx_wickPoly m)) = g := by
    funext ω
    simp only [g, Fr, Complex.ofReal_sub, tcx_F_eq_polyValue hWick]
  rw [hg]
  have iF1 : Integrable (Fr (l + 1)) μ := tcw_integrable_F h1
  have iF0 : Integrable (Fr l) μ := tcw_integrable_F h0
  have iH : Integrable (tcw_H b e W l k m) μ := tcw_integrable_H hCount hb1 he1 he2 hW l k m h2
  have ig : Integrable g μ := (iF1.sub iF0).ofReal
  set cond := μ[A.indicator g | growthSigma W l]
  -- the tower property and the pull-out on `A`
  have hcond : ∫ ω, A.indicator cond ω ∂μ = ∫ ω, A.indicator g ω ∂μ := by
    have e1 : A.indicator cond =ᵐ[μ] μ[A.indicator (A.indicator g) | growthSigma W l] :=
      (condExp_indicator (ig.indicator hAm) hAl).symm
    rw [integral_congr_ae e1, integral_condExp hle, Set.indicator_indicator, Set.inter_self]
  -- the real remainder as the real part of the summed integrand
  have hrem : ∫ ω, A.indicator (tcw_rem b e W l k m) ω ∂μ =
      ∫ ω, (A.indicator (fun ω => cond ω - (W : ℂ)⁻¹ * G ω) ω).re ∂μ := by
    have hGH : ∀ᵐ ω ∂μ, (G ω).re = tcw_H b e W l k m ω :=
      hGen m b hb hb1 e he1 he2 W hW l k t
    have icond : Integrable (A.indicator cond) μ := integrable_condExp.indicator hAm
    have i1 : Integrable (fun ω => (A.indicator cond ω).re) μ := icond.re
    have i2 : Integrable (fun ω => (W : ℝ)⁻¹ * A.indicator (tcw_H b e W l k m) ω) μ :=
      (iH.indicator hAm).const_mul _
    have e2 : (fun ω => (A.indicator (fun ω => cond ω - (W : ℂ)⁻¹ * G ω) ω).re) =ᵐ[μ]
        fun ω => (A.indicator cond ω).re - (W : ℝ)⁻¹ * A.indicator (tcw_H b e W l k m) ω := by
      filter_upwards [hGH] with ω hω
      by_cases hω' : ω ∈ A
      · simp only [Set.indicator_of_mem hω', Complex.sub_re, ← hω]
        rw [show ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
      · simp [Set.indicator_of_notMem hω']
    rw [integral_congr_ae e2, integral_sub i1 i2, integral_const_mul]
    have e3 : ∫ ω, (A.indicator cond ω).re ∂μ = ∫ ω, A.indicator (fun ω => Fr (l + 1) ω - Fr l ω) ω ∂μ := by
      have : ∫ ω, (A.indicator cond ω).re ∂μ = (∫ ω, A.indicator cond ω ∂μ).re :=
        integral_re icond
      rw [this, hcond]
      have : (∫ ω, A.indicator g ω ∂μ) = ((∫ ω, A.indicator (fun ω => Fr (l + 1) ω - Fr l ω) ω ∂μ : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        congr 1; funext ω
        by_cases hω' : ω ∈ A
        · simp [Set.indicator_of_mem hω', g]
        · simp [Set.indicator_of_notMem hω']
      rw [this, Complex.ofReal_re]
    have hI1 : Integrable (A.indicator (fun ω => Fr (l + 1) ω - Fr l ω)) μ :=
      (iF1.sub iF0).indicator hAm
    rw [e3, ← integral_const_mul, ← integral_sub hI1 i2]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω' : ω ∈ A
    · simp only [Set.indicator_of_mem hω', tcw_rem, Fr]
    · simp [Set.indicator_of_notMem hω']
  rw [hrem, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun ω => ?_)
  rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)

/-- **`TcwStoppedRemainderCoreFixed` from `ContractingWordsContract.summed`.** Instantiated at
`nT = 1`, `nI = 0`, the tag family `k`, `ε = s/2`, `T = τ + 1`, the level `K` and `Φ = Φ_m` (`tcx_wickPoly`); every
`l ∈ [k+1, n)` is a step of `summed`.
Inputs: `ContractingWordsContract`, `FullSourceMomentsContract` (integrability),
`ConditionalBlockGUECount`, and the two deterministic identities `TcxWickMoment` and
`TcxWickGenerator` (proved as `tcx_wickMoment` and `tcx_wickGenerator`). Adaptedness of the stop
event is `tcx_measurableSet_alive_growthSigma`.
-/
theorem tcwStoppedRemainderCoreFixed_of_summed (hCW : ContractingWordsContract)
    (hMom : FullSourceMomentsContract) (hCount : ConditionalBlockGUECount)
    (hWick : TcxWickMoment) (hGen : TcxWickGenerator) : TcwStoppedRemainderCoreFixed := by
  intro b hb hb' E hE1 hE2 s τ hs σ hσ M δ K hδ hK
  have hsτ := tco_tagSequence_s_le σ
  have hε : 0 < s / 2 := by linarith
  have hεT : s / 2 < τ + 1 := by linarith
  have hq : IsIntervalTests tcw_noInterval := fun a => a.elim0
  suffices H : ∀ m ∈ range (M + 1), ∀ᶠ j in atTop, ∀ l', σ.k j + 1 ≤ l' → l' ≤ σ.n j →
      |∑ l ∈ Ico (σ.k j + 1) l', ∫ ω, (tcw_alive b (σ.energy j) (σ.W j) (σ.k j) K (s / 2) l).indicator
        (tcw_rem b (σ.energy j) (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b| ≤ δ by
    filter_upwards [(eventually_all_finset _).2 H] with j hj m hm l' h1 h2
    exact hj m (by simp; omega) l' h1 h2
  intro m _
  obtain ⟨C, W₀, hC⟩ := hCW.summed b hb hb' E hE1 hE2 1 0 tcw_noInterval hq (tcx_wickPoly m)
    (tcx_isOrdinaryPoly_wickPoly m) (s / 2) (τ + 1) K hε hεT
  choose Cf hCf using tcc_momentsAlong_fixed hMom hb hb' hE1 hE2 σ hσ
  have hmomE : ∀ᶠ j in atTop, ∀ p ∈ range (m + 3), ∀ l, σ.k j < l → l ≤ σ.n j →
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * p)) ∂tcc_law b (σ.energy j) (σ.W j) l (σ.k j) ≤
        ENNReal.ofReal (Cf p) :=
    (eventually_all_finset _).2 fun p _ => hCf p
  have htag : ∀ᶠ j in atTop, s / 2 * (σ.W j : ℝ) ≤ σ.k j := by
    filter_upwards [σ.tag_tendsto.eventually (lt_mem_nhds (show s / 2 < s by linarith))] with j hj
    have hW : (0 : ℝ) < σ.W j := by exact_mod_cast σ.W_pos j
    rw [lt_div_iff₀ hW] at hj
    exact hj.le
  have hsmall : ∀ᶠ j in atTop, C * (1 / Real.sqrt (σ.W j) + 1 / (σ.W j : ℝ)) ≤ δ := by
    have t1 : Tendsto (fun W : ℕ => 1 / Real.sqrt W) atTop (𝓝 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have t2 : Tendsto (fun W : ℕ => 1 / (W : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have t3 := (t1.add t2).const_mul C
    rw [add_zero, mul_zero] at t3
    exact σ.width_tendsto.eventually (t3.eventually (ge_mem_nhds hδ))
  filter_upwards [hmomE, tcc_eventually_len σ W₀, htag, hsmall] with j hmj hlen hkj hsm
  intro l' h1 h2
  rw [hσ j] at hmj ⊢
  have hWpos := σ.W_pos j
  have hint : ∀ l, σ.k j + 1 ≤ l → l ≤ σ.n j → ∀ p ≤ m + 2, Integrable
      (fun x => lmf_tagResponseClock b E (σ.W j) l (σ.k j) x ^ p) (probedClockLaw (σ.W j) b) :=
    fun l hl1 hl2 p hp => tcw_integrable_tagClock_pow (hmj p (by simp; omega) l (by omega) hl2)
  obtain ⟨hC1, -⟩ := hC (σ.W j) hlen.1 (tcw_tagFamily (σ.k j)) (fun _ => hkj)
  dsimp only at hC1
  have hstep := fun l (hl : l ∈ Ico (σ.k j + 1) l') =>
    tcx_stopped_step (K := K) (ε := s / 2) (t := ((l + 1 : ℕ) : ℝ) / σ.W j) hCount hWick hGen hb
      hb' hE1 hE2 hWpos (hint (l + 1) (by simp at hl; omega) (by simp at hl; omega) m (by omega))
      (hint l (by simp at hl; omega) (by simp at hl; omega) m (by omega))
      (hint l (by simp at hl; omega) (by simp at hl; omega) (m - 2 + 2) (by omega))
  have hsub : Ico (σ.k j + 1) l' ⊆ (range ⌊(τ + 1) * (σ.W j : ℝ)⌋₊).filter
      fun i : ℕ => s / 2 * (σ.W j : ℝ) ≤ (i : ℝ) ∧ ∀ a, i ≠ tcw_tagFamily (σ.k j) a := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
    refine mem_filter.2 ⟨mem_range.2 (Nat.lt_of_succ_le (Nat.le_floor ?_)), ?_, fun a => ?_⟩
    · have : ((l + 1 : ℕ) : ℝ) ≤ σ.n j := by exact_mod_cast (show l + 1 ≤ σ.n j by omega)
      exact this.trans hlen.2
    · exact hkj.trans (by exact_mod_cast (show σ.k j ≤ l by omega))
    · simp only [tcw_tagFamily]; omega
  rw [← ENNReal.ofReal_le_ofReal_iff hδ.le]
  calc ENNReal.ofReal |∑ l ∈ Ico (σ.k j + 1) l', ∫ ω, (tcw_alive b E (σ.W j) (σ.k j) K (s / 2)
          l).indicator (tcw_rem b E (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b|
      ≤ ENNReal.ofReal (∑ l ∈ Ico (σ.k j + 1) l', |∫ ω, (tcw_alive b E (σ.W j) (σ.k j) K (s / 2)
          l).indicator (tcw_rem b E (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b|) :=
        ENNReal.ofReal_le_ofReal (abs_sum_le_sum_abs _ _)
    _ = ∑ l ∈ Ico (σ.k j + 1) l', ENNReal.ofReal |∫ ω, (tcw_alive b E (σ.W j) (σ.k j) K (s / 2)
          l).indicator (tcw_rem b E (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b| :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _
    _ ≤ _ := Finset.sum_le_sum hstep
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub
    _ ≤ _ := hC1
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hsm

/-- **`TcoTagComparisonCoreFixed` from the contracts and the two algebraic identities**
`TcxWickMoment` and `TcxWickGenerator`. Neither `TcwNuclearNormMeasurable` nor
`TcwStoppedRemainderCoreFixed` (derived from `summed`) is assumed.
-/
theorem tcoTagComparisonCoreFixed_of_wick (hMom : FullSourceMomentsContract)
    (hBirth : TagBirthValueContract) (hStops : FullSourceStopsContract)
    (hCount : ConditionalBlockGUECount) (hCW : ContractingWordsContract)
    (hWick : TcxWickMoment) (hGen : TcxWickGenerator) : TcoTagComparisonCoreFixed :=
  tcoTagComparisonCoreFixed_of_stopped' hMom hBirth hStops hCount
    (tcwStoppedRemainderCoreFixed_of_summed hCW hMom hCount hWick hGen)

/-- **The tagged convex order theorem at fixed energy** (`taggedConvexOrder_fixed`) from the
contracts and the two algebraic identities `TcxWickMoment`, `TcxWickGenerator`.
-/
theorem taggedConvexOrder_fixed_of_wick (hMomU : FullSourceMomentsEnergyUniformContract)
    (hMom : FullSourceMomentsContract) (hBirth : TagBirthValueContract)
    (hStops : FullSourceStopsContract) (hCount : ConditionalBlockGUECount)
    (hCW : ContractingWordsContract) (hWick : TcxWickMoment) (hGen : TcxWickGenerator) :
    TaggedConvexOrderFixedStatement :=
  taggedConvexOrder_fixed hMomU
    (tcoTagComparisonCoreFixed_of_wick hMom hBirth hStops hCount hCW hWick hGen)

end BlockBand.Endpoints
