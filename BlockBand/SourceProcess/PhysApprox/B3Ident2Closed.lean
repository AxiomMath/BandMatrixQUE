module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2Defs

/-!
# Closed properties pass to the uncapped fdd limit

Measure: the conditioned closed law `closedLaw b W np [|physCapEventC]` at width `W`, and the
candidate's `Q`. Domain: `FrameDomain` (only `b < 1`, `|E| < 2`, `s < τ_j`, the admissible
frame and `0 < h < 1` are used).

* `integral_capIndicator`: `∫ 1_{cap}(y.1.1) d closedLaw = P_W(cap)` (through the Borel version
  `physCapEventM`).
* `eventually_capProb_ne_zero`: for non-atomic `h` and a cap of positive entrance mass,
  `P_W(cap) ≠ 0` eventually (`tendsto_capProb`).
* `condObsTestAll_eq_one`: a test equal to `1` a.s. on the cap event has conditioned value `1`.
* **`ae_mem_of_fddAll`** (portmanteau for closed sets, with the outer approximations
  `apprSeq`): if eventually, almost surely on the cap event, finitely many finite-`W` observables
  lie in a closed set `F`, then `Q`-almost surely the limit observables lie in `F`. No
  measurability of the finite-`W` observables is needed.
* **`ae_kc_zero`**: `Kc 0 = 0` almost surely (`b3ClosedKAt` vanishes at `n_s`, `B3Bridge`).
* `ae_feasible_fdd` and **`ae_feasible_all`**: `G t` is `GramFeasible` for every `t`, almost
  surely (`complexClosedFeasible_holds`, `isClosed_setOf_gramFeasible`; non-birth rational times,
  then right limits through the every-`ω` continuity of `G − J` and the right-continuity of `J`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

variable {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ}

/-- **`∫ 1_{cap} d closedLaw = P_W(cap)`.** -/
theorem integral_capIndicator (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (W : ℕ) :
    ∫ y, (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 ∂closedLaw b W np =
      (growthPathLaw W b (physCapEventC b E s h K W)).toReal := by
  have hae : physCapEventC b E s h K W =ᵐ[growthPathLaw W b]
      ClosedIdent.physCapEventM b E s h K W := ClosedIdent.physCapEvent_ae_eq hb hE1 hE2 s h K
  have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      (closedLaw b W np) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)
      (ν := Measure.pi fun _ : Fin np =>
        BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin W))).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b) (ν := phaseLaw))
  have h1 : (fun y : ProbedPath W np × ℝ =>
      (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1) =ᵐ[closedLaw b W np]
      fun y => (ClosedIdent.physCapEventM b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 :=
    hq.ae_eq_comp (indicator_ae_eq_of_ae_eq_set hae)
  have hm : MeasurableSet ((fun y : ProbedPath W np × ℝ => y.1.1) ⁻¹'
      ClosedIdent.physCapEventM b E s h K W) :=
    (measurable_fst.comp measurable_fst) (ClosedIdent.measurableSet_physCapEventM b E s h K W)
  have e2 : (fun y : ProbedPath W np × ℝ =>
      (ClosedIdent.physCapEventM b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1) =
      ((fun y : ProbedPath W np × ℝ => y.1.1) ⁻¹'
        ClosedIdent.physCapEventM b E s h K W).indicator 1 := rfl
  rw [integral_congr_ae h1, e2, integral_indicator_one hm, measureReal_def,
    probedPhase_preimage_path, measure_congr hae]

/-- **The cap mass is eventually positive** (non-atomic `h`, positive entrance mass). -/
theorem eventually_capProb_ne_zero (hTL : TransmissionLawContract) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) (hs : 0 < s) (hh : 0 < h)
    (hA : CapCond.NoAtom (entranceLaw P μ s) h) (hne : entranceLaw P μ s (capSet K h) ≠ 0) :
    ∀ᶠ W in atTop, growthPathLaw W b (physCapEventC b E s h K W) ≠ 0 := by
  have := hlim.prob
  have := CapCond.isFiniteMeasure_entranceLaw P μ s
  have hpos : 0 < (entranceLaw P μ s (capSet K h)).toReal :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  filter_upwards [(CapCond.tendsto_capProb hTL hb0 hb hE1 hE2 hlim hs hh K (hA K)).eventually
    (lt_mem_nhds hpos)] with W hW
  exact (ENNReal.toReal_pos_iff.1 hW).1.ne'

/-- **A test equal to `1` almost surely on the cap event has conditioned value `1`.** -/
theorem condObsTestAll_eq_one (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ}
    {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hW : growthPathLaw W b (physCapEventC b E s h K W) ≠ 0) {ι : Type} [Fintype ι]
    (i : ι → LIdx K np) (u : ι → ℝ≥0) (ψ : BoundedContinuousFunction (ι → ℂ) ℝ)
    (h1 : ∀ᵐ y ∂closedLaw b W np, y.1.1 ∈ physCapEventC b E s h K W →
      ψ (fun l => b3ObsAll b E s h τ m W V (i l) (u l) y) = 1) :
    condObsTestAll b E s h τ m W V i u ψ = 1 := by
  have e : ∫ y, (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
      ψ (fun l => b3ObsAll b E s h τ m W V (i l) (u l) y) ∂closedLaw b W np =
      ∫ y, (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 ∂closedLaw b W np := by
    refine integral_congr_ae (h1.mono fun y hy => ?_)
    dsimp only
    by_cases hc : y.1.1 ∈ physCapEventC b E s h K W
    · rw [Set.indicator_of_mem hc, one_mul, hy hc]
    · rw [Set.indicator_of_notMem hc, zero_mul]
  unfold condObsTestAll
  rw [e, integral_capIndicator hb hE1 hE2 W]
  exact div_self (ENNReal.toReal_ne_zero.2 ⟨hW, measure_ne_top _ _⟩)

variable {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {φ : ℕ → ℕ}
  {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'} {tseq : Ω' → ℕ → ℝ}
  {G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))} {Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ}

/-- **Closed properties pass to the uncapped fdd limit** (portmanteau for closed sets). -/
theorem ae_mem_of_fddAll [IsProbabilityMeasure Q] (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hF : IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc)
    (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hcap : ∀ᶠ n in atTop, growthPathLaw (φ n) b (physCapEventC b E s h K (φ n)) ≠ 0)
    {ι : Type} [Fintype ι] (i : ι → LIdx K np) (u : ι → ℝ≥0) (hu : ∀ l j, s + (u l : ℝ) ≠ τ j)
    {F : Set (ι → ℂ)} (hFc : IsClosed F)
    (hW : ∀ᶠ n in atTop, ∀ᵐ y ∂closedLaw b (φ n) np, y.1.1 ∈ physCapEventC b E s h K (φ n) →
      (fun l => b3ObsAll b E s h τ m (φ n) (Vs (φ n)) (i l) (u l) y) ∈ F) :
    ∀ᵐ ω ∂Q, (fun l => complexObs tseq G Kc (i l) (u l) ω) ∈ F := by
  set X : Ω' → ι → ℂ := fun ω l => complexObs tseq G Kc (i l) (u l) ω
  have hX : Measurable X := Measurable.of_eval fun l => hobs (i l) (u l)
  set ψ : ℕ → BoundedContinuousFunction (ι → ℂ) ℝ := fun k =>
    realBCF (hFc.apprSeq k) (HasOuterApproxClosed.apprSeq_apply_le_one hFc k)
  have hψv : ∀ k x, ψ k x = ((hFc.apprSeq k x : ℝ≥0) : ℝ) := fun _ _ => rfl
  have hψ1 : ∀ k x, x ∈ F → ψ k x = 1 := fun k x hx => by
    rw [hψv, HasOuterApproxClosed.apprSeq_apply_eq_one hFc k hx, NNReal.coe_one]
  have hψle : ∀ k x, ψ k x ≤ 1 := fun k x => by
    rw [hψv]; exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hFc k x
  have hint : ∀ k, ∫ ω, ψ k (X ω) ∂Q = 1 := fun k => by
    refine tendsto_nhds_unique (hF ι i u hu (ψ k)) (tendsto_const_nhds.congr' ?_)
    filter_upwards [hcap, hW] with n hn hn'
    exact (condObsTestAll_eq_one hb hE1 hE2 hn i u (ψ k)
      (hn'.mono fun y hy hc => hψ1 k _ (hy hc))).symm
  have hae : ∀ k, ∀ᵐ ω ∂Q, ψ k (X ω) = 1 := fun k => by
    have hI : Integrable (fun ω => ψ k (X ω)) Q :=
      (integrable_const ‖ψ k‖).mono' ((ψ k).continuous.measurable.comp hX).aestronglyMeasurable
        (ae_of_all _ fun ω => (ψ k).norm_coe_le_norm _)
    have h0 : ∫ ω, (1 - ψ k (X ω)) ∂Q = 0 := by
      rw [integral_sub (integrable_const _) hI, hint k]; simp
    have h0' := (integral_eq_zero_iff_of_nonneg (fun ω => sub_nonneg.2 (hψle k _))
      ((integrable_const _).sub hI)).1 h0
    filter_upwards [h0'] with ω hω
    have h2 : 1 - ψ k (X ω) = 0 := hω
    linarith
  filter_upwards [ae_all_iff.2 hae] with ω hω
  by_contra hnot
  have hlim := (tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hFc)) (X ω)
  rw [Set.indicator_of_notMem hnot] at hlim
  have h1 : ∀ k, hFc.apprSeq k (X ω) = 1 := fun k => by
    have := hω k
    rw [hψv] at this
    exact_mod_cast this
  simp only [h1, tendsto_const_nhds_iff] at hlim
  exact one_ne_zero hlim

/-- **`𝒦(0) = 0` almost surely.** -/
theorem ae_kc_zero [IsProbabilityMeasure Q] (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hτ : ∀ j, s < τ j) (hF : IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc)
    (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hcap : ∀ᶠ n in atTop, growthPathLaw (φ n) b (physCapEventC b E s h K (φ n)) ≠ 0) :
    ∀ᵐ ω ∂Q, Kc 0 ω = 0 := by
  have hu : ∀ (_ : Fin np × Fin np) j, s + ((0 : ℝ≥0) : ℝ) ≠ τ j := fun _ j => by
    rw [NNReal.coe_zero, add_zero]; exact (hτ j).ne
  have hmem := ae_mem_of_fddAll hb hE1 hE2 hF hobs hcap
    (fun ij : Fin np × Fin np => (Sum.inr (Sum.inr ij) : LIdx K np)) (fun _ => 0) hu
    (isClosed_singleton (x := (0 : Fin np × Fin np → ℂ)))
    (Eventually.of_forall fun n => ae_of_all _ fun y _ => by
      funext ij
      have e : limLenAll s (φ n) 0 = closeLen s (φ n) := by
        simp [limLenAll, closeLen]
      show b3ClosedKAt b E s h τ m (φ n) (limLenAll s (φ n) 0) y ij.1 ij.2 = 0
      rw [e, b3ClosedKAt_start hτ y, Matrix.zero_apply])
  filter_upwards [hmem] with ω hω
  ext i j
  exact congrFun hω (i, j)

/-- **Feasibility at a non-birth time**, almost surely. -/
theorem ae_feasible_fdd [IsProbabilityMeasure Q] {T : ℝ} (hD : FrameDomain b E τ m T s h K Vs)
    (hφ : Tendsto φ atTop atTop) (hF : IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc)
    (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hcap : ∀ᶠ n in atTop, growthPathLaw (φ n) b (physCapEventC b E s h K (φ n)) ≠ 0)
    {u : ℝ≥0} (hu : ∀ j, s + (u : ℝ) ≠ τ j) :
    ∀ᵐ ω ∂Q, GramFeasible (srcSignature K (Fin np)) (G u ω) := by
  obtain ⟨⟨-, hb, hE1, hE2, -⟩, -⟩ := id hD
  have hb1 : b < 1 := by linarith
  have hDH := (BornUnique.isSignature_srcSignature K (Fin np)).1
  have hFc : IsClosed (gramOfEntries ⁻¹'
      {G : GramState (SrcCol K (Fin np)) | GramFeasible (srcSignature K (Fin np)) G}) :=
    (B3Feas.isClosed_setOf_gramFeasible hDH).preimage continuous_gramOfEntries
  have hmem := ae_mem_of_fddAll hb1 hE1 hE2 hF hobs hcap
    (fun e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np) => (Sum.inl e : LIdx K np))
    (fun _ => u) (fun _ => hu) hFc
    ((hφ.eventually (complexClosedFeasible_holds b E np τ m T s h K Vs hD)).mono
      fun n hn => hn.mono fun y hy hc => by
        change GramFeasible (srcSignature K (Fin np)) (gramOfEntries fun e => gramEntry e
          (b3ClosedGramAt b E s h τ m (φ n) (limLenAll s (φ n) u) (Vs (φ n)) y))
        rw [gramOfEntries_gramEntry]
        exact hy hc _ (Nat.floor_le_floor (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right u.2) (Nat.cast_nonneg _))))
  filter_upwards [hmem] with ω hω
  have e : gramOfEntries (fun e => complexObs tseq G Kc (Sum.inl e) u ω) = G u ω :=
    gramOfEntries_gramEntry (G u ω)
  rw [← e]
  exact hω

/-- **Feasibility at every time**, almost surely. -/
theorem ae_feasible_all [IsProbabilityMeasure Q] {T : ℝ} (hD : FrameDomain b E τ m T s h K Vs)
    (hφ : Tendsto φ atTop atTop) (hF : IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc)
    (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hcap : ∀ᶠ n in atTop, growthPathLaw (φ n) b (physCapEventC b E s h K (φ n)) ≠ 0)
    (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u) :
    ∀ᵐ ω ∂Q, ∀ t, GramFeasible (srcSignature K (Fin np)) (G t ω) := by
  have hDH := (BornUnique.isSignature_srcSignature K (Fin np)).1
  have hq : ∀ᵐ ω ∂Q, ∀ q : ℚ, (∀ j, s + ((q : ℝ).toNNReal : ℝ) ≠ τ j) →
      GramFeasible (srcSignature K (Fin np)) (G (q : ℝ).toNNReal ω) := by
    rw [ae_all_iff]
    intro q
    by_cases hqb : ∀ j, s + ((q : ℝ).toNNReal : ℝ) ≠ τ j
    · exact (ae_feasible_fdd hD hφ hF hobs hcap hqb).mono fun ω hω _ => hω
    · exact ae_of_all _ fun ω hb' => absurd hb' hqb
  filter_upwards [hq] with ω hω t
  have hseq : ∀ n : ℕ, ∃ q : ℚ, (t : ℝ) < q ∧ (q : ℝ) < t + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                        linarith)
  choose q hq1 hq2 using hseq
  set v : ℕ → ℝ≥0 := fun n => (q n : ℝ).toNNReal
  have hv : ∀ n, (v n : ℝ) = q n := fun n => Real.coe_toNNReal _ (t.2.trans (hq1 n).le)
  have hvt : ∀ n, (t : ℝ) < v n := fun n => by rw [hv n]; exact hq1 n
  have hlimR : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (t : ℝ)) := by
    have hup : Tendsto (fun n : ℕ => (t : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (t : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (t : ℝ))).add
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (hvt n).le) (fun n => by rw [hv n]; exact (hq2 n).le)
  have hlim : Tendsto v atTop (𝓝 t) := NNReal.tendsto_coe.1 hlimR
  have hnb : ∀ᶠ n in atTop, ∀ j, s + (v n : ℝ) ≠ τ j := by
    rw [eventually_all]
    intro j
    by_cases hj : τ j ≤ s + t
    · exact Eventually.of_forall fun n => by have := hvt n; exact ne_of_gt (by linarith)
    · rw [not_le] at hj
      exact (hlimR.eventually (gt_mem_nhds (show (t : ℝ) < τ j - s by linarith))).mono
        fun n hn => ne_of_lt (by linarith)
  have hJ : ∀ᶠ n in atTop, gramJ (K := K) b s τ m (v n) = gramJ b s τ m t := by
    have hiff : ∀ᶠ n in atTop, ∀ j, (τ j - s ≤ (v n : ℝ) ↔ τ j - s ≤ (t : ℝ)) := by
      rw [eventually_all]
      intro j
      by_cases hj : τ j - s ≤ t
      · exact Eventually.of_forall fun n => ⟨fun _ => hj, fun _ => hj.trans (hvt n).le⟩
      · rw [not_le] at hj
        exact (hlimR.eventually (gt_mem_nhds hj)).mono fun n hn =>
          ⟨fun h' => absurd h' (not_le.2 hn), fun h' => absurd h' (not_le.2 hj)⟩
    exact hiff.mono fun n hn => by simp only [gramJ, birthJump, hn]
  have hGt : Tendsto (fun n => G (v n) ω) atTop (𝓝 (G t ω)) := by
    have h1 := ((hc ω).tendsto t).comp hlim
    have h2 : Tendsto (fun n => gramJ (K := K) b s τ m (v n)) atTop (𝓝 (gramJ b s τ m t)) :=
      tendsto_const_nhds.congr' (hJ.mono fun n hn => hn.symm)
    simpa using h1.add h2
  exact (B3Feas.isClosed_setOf_gramFeasible hDH).mem_of_tendsto hGt
    (hnb.mono fun n hn => hω (q n) hn)

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
