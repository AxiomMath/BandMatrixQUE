module

public import BlockBand.Endpoints.Response.TaggedConvexOrderUniformBase
public import BlockBand.Endpoints.Response.TaggedConvexOrderWickGen

/-!
# Energy-uniform tagged convex order: the stopped remainder along moving energies

`tcu_stoppedRemainderAlong` proves `TcwStoppedRemainderAlong` along a tagged sequence with moving
energies, from `ContractingWordsEnergyUniformContract`, `FullSourceMomentsEnergyUniformContract`
and `ConditionalBlockGUECount`: the energies eventually lie in a compact bulk interval, on which
the summed contracting-words bound is uniform. Path law `growthPathLaw W b`, probe
`circularVectorLaw`; the path, the trace stop and the remainder `tcw_rem` are evaluated at `e_j`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.TransmissionUniform2
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal NNReal

/-- **The stopped remainder along moving energies**, from
`ContractingWordsEnergyUniformContract.summed` instantiated at `nT = 1`, `nI = 0`, the tag family
`k`, `ε = s/2`, `T = τ + 1`, the level `K`, `Φ = Φ_m` (`tcx_wickPoly`) and the bulk margin `κ`;
every `l ∈ [k+1, n)` is a step of `summed`.
-/
theorem tcu_stoppedRemainderAlong (hCW : ContractingWordsEnergyUniformContract)
    (hMom : FullSourceMomentsEnergyUniformContract) (hCount : ConditionalBlockGUECount)
    {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ}
    (hs : 0 < s) (σ : TcoTagSequence s τ E) : TcwStoppedRemainderAlong b σ := by
  intro M δ K hδ hK
  obtain ⟨κ, hκ, hbulk⟩ := tcu_eventually_bulk σ hE1 hE2
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
  obtain ⟨C, W₀, hC⟩ := hCW.summed b hb hb' κ hκ 1 0 tcw_noInterval hq (tcx_wickPoly m)
    (tcx_isOrdinaryPoly_wickPoly m) (s / 2) (τ + 1) K hε hεT
  choose Cf hCf using tcu_momentsAlong hMom hb hb' hE1 hE2 σ
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
  filter_upwards [hmomE, tcc_eventually_len σ W₀, htag, hsmall, hbulk]
    with j hmj hlen hkj hsm he
  intro l' h1 h2
  obtain ⟨he1, he2⟩ := tcu_bulk_bounds hκ he
  have hWpos := σ.W_pos j
  have hint : ∀ l, σ.k j + 1 ≤ l → l ≤ σ.n j → ∀ p ≤ m + 2, Integrable
      (fun x => lmf_tagResponseClock b (σ.energy j) (σ.W j) l (σ.k j) x ^ p)
        (probedClockLaw (σ.W j) b) :=
    fun l hl1 hl2 p hp => tcw_integrable_tagClock_pow (hmj p (by simp; omega) l (by omega) hl2)
  obtain ⟨hC1, -⟩ := hC (σ.W j) hlen.1 (σ.energy j) he (tcw_tagFamily (σ.k j)) (fun _ => hkj)
  dsimp only at hC1
  have hstep := fun l (hl : l ∈ Ico (σ.k j + 1) l') =>
    tcx_stopped_step (K := K) (ε := s / 2) (t := ((l + 1 : ℕ) : ℝ) / σ.W j) hCount tcx_wickMoment
      tcx_wickGenerator hb hb' he1 he2 hWpos
      (hint (l + 1) (by simp at hl; omega) (by simp at hl; omega) m (by omega))
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
  calc ENNReal.ofReal |∑ l ∈ Ico (σ.k j + 1) l', ∫ ω, (tcw_alive b (σ.energy j) (σ.W j) (σ.k j) K
          (s / 2) l).indicator (tcw_rem b (σ.energy j) (σ.W j) l (σ.k j) m) ω
          ∂growthPathLaw (σ.W j) b|
      ≤ ENNReal.ofReal (∑ l ∈ Ico (σ.k j + 1) l', |∫ ω, (tcw_alive b (σ.energy j) (σ.W j) (σ.k j)
          K (s / 2) l).indicator (tcw_rem b (σ.energy j) (σ.W j) l (σ.k j) m) ω
          ∂growthPathLaw (σ.W j) b|) :=
        ENNReal.ofReal_le_ofReal (abs_sum_le_sum_abs _ _)
    _ = ∑ l ∈ Ico (σ.k j + 1) l', ENNReal.ofReal |∫ ω, (tcw_alive b (σ.energy j) (σ.W j) (σ.k j)
          K (s / 2) l).indicator (tcw_rem b (σ.energy j) (σ.W j) l (σ.k j) m) ω
          ∂growthPathLaw (σ.W j) b| :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _
    _ ≤ _ := Finset.sum_le_sum hstep
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub
    _ ≤ _ := hC1
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hsm

end BlockBand.Endpoints
