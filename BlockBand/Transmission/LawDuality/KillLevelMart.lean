module

public import BlockBand.Transmission.LawDuality.KillGenPath
public import BlockBand.Transmission.LawDuality.KillLevelGap
public import BlockBand.Transmission.LawDuality.KillTestVal
public import BlockBand.Transmission.LawDuality.KillMartLim
public import BlockBand.Transmission.LawDuality.RatioTest
public import BlockBand.Transmission.Dual.LevelStep

/-!
# The killed duality, one level: the level-`q` ratio martingale across the deletion

Fix a normalized dual realization, a finite measure `ν`, and a stopping time `τ` up to which the
path stays in `{x_i ≤ M, y_j ≤ 1 − ε}` (`StaysIn`). With `ρ = r ∧ τ` (`stopAt`) and
`G(t) = F_{Z_t}(ν)` (`pathRatio`), the **level-`q` limit process** is

`L^q_r = G(ρ ∧ σ_{q−1}) − G(ρ ∧ σ_q) − ∫_{(0,ρ]} 𝒟_qF_·(ν)(Z_u) 1{N_u = q} du` (`levelMart`).

* **`exists_levelMart_approx`**: `L^q_r` is, for every `r`, the a.s. limit of `𝓖`-martingales
  `M_k` with `|M_k(r)| ≤ 2 + C r` (`C = genMass D₀ q M ε ν`): `M_k` is (a version of) the dual
  martingale of the cutoff test `u_{k+1}·F_·(ν)` stopped at `τ ∧ θ_k` (`θ_k` the exit of
  `{u_k > 1/2}`); its value is `dualMartingale_eq_of_le_hit_test`; the `F`-part converges by
  `tendsto_level_gap_of_continuous` with `G` (`continuous_ratioPath`, across the deletion),
  the drift part by `tendsto_integral_liftGen` (mass-linear bound).
* **`integral_mul_levelMart_sub_eq_zero`**: `E[A (L^q_t − L^q_s)] = 0` for bounded
  `𝓖_s`-measurable `A`, `s ≤ t`.
* `abs_levelMart_le`, `aestronglyMeasurable_levelMart`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

section Defs

variable {Ω : Type*}

/-- `ρ = r ∧ τ` as a real time. -/
def stopAt (τ : Ω → WithTop ℝ≥0) (r : ℝ≥0) (ω : Ω) : ℝ≥0 := (min (r : WithTop ℝ≥0) (τ ω)).untopA

theorem coe_stopAt (τ : Ω → WithTop ℝ≥0) (r : ℝ≥0) (ω : Ω) :
    (stopAt τ r ω : WithTop ℝ≥0) = min (r : WithTop ℝ≥0) (τ ω) :=
  coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))

theorem stopAt_le (τ : Ω → WithTop ℝ≥0) (r : ℝ≥0) (ω : Ω) : stopAt τ r ω ≤ r := by
  have := coe_stopAt τ r ω ▸ min_le_left (r : WithTop ℝ≥0) (τ ω)
  exact WithTop.coe_le_coe.1 this

theorem stopAt_le_tau (τ : Ω → WithTop ℝ≥0) (r : ℝ≥0) (ω : Ω) :
    (stopAt τ r ω : WithTop ℝ≥0) ≤ τ ω :=
  (coe_stopAt τ r ω).le.trans (min_le_right _ _)

/-- **The level-`q` limit process** `G(ρ∧σ_{q−1}) − G(ρ∧σ_q) − ∫_{(0,ρ]} 𝒟_qF(Z)1{N=q}`. -/
def levelMart (D0 : ℝ) (ν : FiniteMeasure unitInterval) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (τ : Ω → WithTop ℝ≥0) (q : ℕ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  pathRatio ν N X Y (min (stopAt τ r ω : WithTop ℝ≥0) (entryTime (fun t => N t ω) (q - 1))).untopA ω -
    pathRatio ν N X Y (min (stopAt τ r ω : WithTop ℝ≥0) (entryTime (fun t => N t ω) q)).untopA ω -
    ∫ u in Ioc (0 : ℝ) (stopAt τ r ω), dualLift (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ))
      (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω)

/-- Up to `τ` every path stays in `{x_i ≤ M, y_j ≤ 1 − ε}`. -/
def StaysIn (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (τ : Ω → WithTop ℝ≥0) (M ε : ℝ) :
    Prop :=
  ∀ ω (u : ℝ≥0), (u : WithTop ℝ≥0) ≤ τ ω → ∀ i, i < N u ω → X u ω i ≤ M ∧ Y u ω i ≤ 1 - ε

variable {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

theorem abs_levelMart_le {ω : Ω}
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) (D0 : ℝ)
    (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hU : StaysIn N X Y τ M ε) (q : ℕ) (r : ℝ≥0) :
    |levelMart D0 ν N X Y τ q r ω| ≤ 2 + genMass D0 q M ε ν * r := by
  have hI := abs_integral_liftGen_le (q := q) hP D0 ν hM hε hε1 (a := stopAt τ r ω)
    fun u hu => hU ω u ((WithTop.coe_le_coe.2 hu).trans (stopAt_le_tau τ r ω))
  have hr := NNReal.coe_le_coe.2 (stopAt_le τ r ω)
  have hC := genMass_nonneg D0 q M ε ν
  have h1 := abs_pathRatio_le hP ν
    (min (stopAt τ r ω : WithTop ℝ≥0) (entryTime (fun t => N t ω) (q - 1))).untopA
  have h2 := abs_pathRatio_le hP ν
    (min (stopAt τ r ω : WithTop ℝ≥0) (entryTime (fun t => N t ω) q)).untopA
  unfold levelMart
  refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (by linarith)) ?_)
  exact hI.trans (mul_le_mul_of_nonneg_left hr hC)

end Defs

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ} {p : ℕ} {x y : Fin p → ℝ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- **The level-`q` limit process is an a.s. limit of bounded martingales.** -/
theorem exists_levelMart_approx (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p) (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hU : StaysIn N X Y τ M ε) {q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ L : ℕ → ℝ≥0 → Ω → ℝ, (∀ k, Martingale (L k) 𝓖 P) ∧
      (∀ r, ∀ᵐ ω ∂P, Tendsto (fun k => L k r ω) atTop (𝓝 (levelMart D0 ν N X Y τ q r ω))) ∧
      ∀ r k, ∀ᵐ ω ∂P, |L k r ω| ≤ 2 + genMass D0 q M ε ν * r := by
  obtain ⟨u, hsm, hcs, hts, hu01, hO, hex⟩ := exists_chamber_exhaustion q
  have hNm : ∀ t, Measurable[𝓖 t] (N t) := fun t => (h.adapted t).1
  have hXm : ∀ t, Measurable[𝓖 t] (X t) := fun t => (h.adapted t).2.1
  have hYm : ∀ t, Measurable[𝓖 t] (Y t) := fun t => (h.adapted t).2.2
  have hq0 : ∀ ω, q ≤ N 0 ω := fun ω => (hstart ω).symm ▸ hqp
  have hh0 : ∀ k, ∀ z ∉ dualChamber q, u k z = 0 := fun k z hz =>
    image_eq_zero_of_notMem_tsupport fun h' => hz (hts k h')
  set θ : ℕ → Ω → WithTop ℝ≥0 :=
    fun k => hitLe (fun t ω => testVal q (u k) (N t ω) (X t ω) (Y t ω)) (1 / 2) with hθdef
  have hθ : ∀ k, IsStoppingTime 𝓖 (θ k) := fun k =>
    isStoppingTime_hitLe (fun t => measurable_testVal_comp (mΩ := 𝓖 t)
      (hsm k).continuous.measurable (hNm t) (hXm t) (hYm t))
      (fun ω t => tendsto_testVal_right (hpath ω) (hsm k).continuous t)
      (fun ω => lowerSemicontinuous_testVal (hpath ω) (hsm k).continuous (hh0 k)
        (fun z => (hu01 k z).2) hq) (1 / 2)
  -- the stopped values
  set g : ℕ → ℝ≥0 → Ω → ℝ := fun k r ω =>
    (if entryTime (fun t => N t ω) q ≤
        ((min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω)).untopA : WithTop ℝ≥0) ∧
        entryTime (fun t => N t ω) q < θ k ω then
      pathRatio ν N X Y (min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω)).untopA ω -
        pathRatio ν N X Y (entryTime (fun t => N t ω) q).untopA ω
    else 0) -
      ∫ v in Ioc (0 : ℝ) (min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω)).untopA,
        dualLift (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ))
          (N v.toNNReal ω) (X v.toNNReal ω) (Y v.toNNReal ω) with hgdef
  have hA : ∀ k, ∃ L : ℝ≥0 → Ω → ℝ, Martingale L 𝓖 P ∧ ∀ r, L r =ᵐ[P] g k r := by
    intro k
    obtain ⟨O, hOo, hOs, hO1⟩ := hO k
    set f : DualCoord q → ℝ := localRatio (u (k + 1)) ν with hfdef
    have hMf := martingale_localRatio ν h hq hqp (hsm (k + 1)) (hcs (k + 1)) (hts (k + 1))
    have hcont : ∀ ω, Continuous fun t => dualMartingale D0 q f N X Y t ω := fun ω =>
      continuous_dualMartingale (hpath ω) D0 hq
        ((contDiff_localRatio ν (hsm (k + 1)) (hts (k + 1))).of_le (by norm_cast))
        (hasCompactSupport_localRatio ν (hcs (k + 1)))
        ((tsupport_localRatio_subset ν).trans (hts (k + 1)))
    have hρk : IsStoppingTime 𝓖 fun ω => min (τ ω) (θ k ω) := hτ.min (hθ k)
    obtain ⟨M', hM', hM'e⟩ := exists_martingale_stoppedProcess hMf
      (fun t => EventuallyEq.rfl) (ae_of_all _ hcont) hρk
    refine ⟨M', hM', fun r => ?_⟩
    filter_upwards [hM'e r] with ω hω
    rw [hω]
    show dualMartingale D0 q f N X Y (min (r : WithTop ℝ≥0) (min (τ ω) (θ k ω))).untopA ω =
      g k r ω
    rw [← min_assoc, ← coe_stopAt]
    have hfin : min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have hr : (((min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω)).untopA : ℝ≥0) : WithTop ℝ≥0) ≤
        θ k ω := by
      rw [coe_untopA_of_ne_top hfin]; exact min_le_right _ _
    have hhO : ∀ z, 1 / 2 ≤ u k z → z ∈ O := fun z hz =>
      hOs (show u k z ≠ 0 by intro e; rw [e] at hz; norm_num at hz)
    have hfO : EqOn f (ratioOn ν) O := fun z hz => by
      simp only [hfdef, localRatio, hO1 z hz, one_mul]
    have hθv : ∀ v : ℝ≥0, (v : WithTop ℝ≥0) < θ k ω →
        1 / 2 < testVal q (u k) (N v ω) (X v ω) (Y v ω) := fun v hv => lt_hitLe hv
    rw [dualMartingale_eq_of_le_hit_test (hpath ω) D0 hq (hq0 ω) (hsm k).continuous (hh0 k)
      hOo hhO hfO hθv hr]
    simp only [hgdef]
    congr 1
    split_ifs with hc
    · have h1 := level_eq_of_le_hit (hpath ω) hq (hsm k).continuous (hh0 k) hθv hr hc.1 hc.2
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hc.1)
      have h2 : N (entryTime (fun t => N t ω) q).untopA ω = q := by
        rw [← hs]; exact level_at_entry (hpath ω) (hq0 ω) hs.symm
      rw [dualLift_eq_of_eq h1 (fun m => (ratioOn ν : DualCoord m → ℝ)),
        dualLift_eq_of_eq h2 (fun m => (ratioOn ν : DualCoord m → ℝ))]
      rfl
    · rfl
  choose L hL hLe using hA
  refine ⟨L, hL, fun r => ?_, fun r k => ?_⟩
  · filter_upwards [ae_all_iff.2 fun k => hLe k r] with ω hω
    simp_rw [hω]
    have hUω : ∀ v : ℝ≥0, v ≤ stopAt τ r ω → ∀ i, i < N v ω → X v ω i ≤ M ∧ Y v ω i ≤ 1 - ε :=
      fun v hv => hU ω v ((WithTop.coe_le_coe.2 hv).trans (stopAt_le_tau τ r ω))
    have hc : ∀ t : ℝ≥0, entryTime (fun t => N t ω) q ≤ t →
        (t : WithTop ℝ≥0) < entryTime (fun t => N t ω) (q - 1) →
        ∀ᶠ k in atTop, (t : WithTop ℝ≥0) < θ k ω := fun t ht1 ht2 =>
      eventually_lt_hit (hpath ω) (fun k => (hsm k).continuous) hex ht1 ht2
    have hG := tendsto_level_gap_of_continuous (hpath ω) (continuous_ratioPath (hpath ω) ν) hq
      (hq0 ω) (stopAt τ r ω) (fun k => θ k ω)
      (fun e he k => hit_le_entry_pred (hpath ω) hq he) hc
    have hI := tendsto_integral_liftGen (hpath ω) D0 ν hM hε hε1 hq (stopAt τ r ω) hUω
      (fun k => θ k ω) hc
    exact hG.sub hI
  · filter_upwards [hLe k r] with ω hω
    rw [hω]
    have hfin : min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have hle : (min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω)).untopA ≤ stopAt τ r ω := by
      have := min_le_left (stopAt τ r ω : WithTop ℝ≥0) (θ k ω)
      rw [← coe_untopA_of_ne_top hfin] at this
      exact WithTop.coe_le_coe.1 this
    have hI := abs_integral_liftGen_le (q := q) (hpath ω) D0 ν hM hε hε1
      (a := (min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω)).untopA) fun v hv =>
        hU ω v ((WithTop.coe_le_coe.2 (hv.trans hle)).trans (stopAt_le_tau τ r ω))
    have hr := NNReal.coe_le_coe.2 (hle.trans (stopAt_le τ r ω))
    have hC := genMass_nonneg D0 q M ε ν
    have hF : |(if entryTime (fun t => N t ω) q ≤
        ((min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω)).untopA : WithTop ℝ≥0) ∧
        entryTime (fun t => N t ω) q < θ k ω then
      pathRatio ν N X Y (min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω)).untopA ω -
        pathRatio ν N X Y (entryTime (fun t => N t ω) q).untopA ω
      else 0)| ≤ 2 := by
      split_ifs
      · have h1 := abs_pathRatio_le (hpath ω) ν
          (min (stopAt τ r ω : WithTop ℝ≥0) (θ k ω)).untopA
        have h2 := abs_pathRatio_le (hpath ω) ν (entryTime (fun t => N t ω) q).untopA
        exact (abs_sub _ _).trans (by linarith)
      · simp
    simp only [hgdef]
    refine (abs_sub _ _).trans (add_le_add hF ?_)
    exact hI.trans (mul_le_mul_of_nonneg_left hr hC)

/-- **Orthogonality of the level-`q` increments.** -/
theorem integral_mul_levelMart_sub_eq_zero (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p) (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hU : StaysIn N X Y τ M ε) {q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Ω → ℝ} (hA : StronglyMeasurable[𝓖 s] A) {CA : ℝ} (hAb : ∀ ω, |A ω| ≤ CA) :
    ∫ ω, A ω * (levelMart D0 ν N X Y τ q t ω - levelMart D0 ν N X Y τ q s ω) ∂P = 0 := by
  obtain ⟨L, hL, hlim, hb⟩ := exists_levelMart_approx h hpath hstart ν hτ hM hε hε1 hU hq hqp
  exact integral_mul_increment_eq_zero_of_tendsto hL hlim (fun r => ⟨_, hb r⟩) hst hA hAb

theorem aestronglyMeasurable_levelMart (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p) (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hU : StaysIn N X Y τ M ε) {q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) (r : ℝ≥0) :
    AEStronglyMeasurable (levelMart D0 ν N X Y τ q r) P := by
  obtain ⟨L, hL, hlim, -⟩ := exists_levelMart_approx h hpath hstart ν hτ hM hε hε1 hU hq hqp
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (fun k => (((hL k).1 r).mono (𝓖.le r)).aestronglyMeasurable) (hlim r)

end BlockBand.Transmission.LawDuality
