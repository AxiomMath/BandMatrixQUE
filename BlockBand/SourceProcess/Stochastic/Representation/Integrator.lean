module
public import BlockBand.SourceProcess.Stochastic.Representation.Driver
public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblemConverse
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The stopped compensated process of a martingale-problem solution as a vector integrator

Setting: a probability space `(Ω, 𝓖, Q)` with a raw filtration; `Y` solves the
`(b, σσᵀ)` martingale problem in the domain `V` (`IsMPSolutionOn`), `W` is a relatively
compact subdomain of `V` (`IsInteriorDomain W V`), and `b'`, `σ'` are **everywhere continuous**
coefficients agreeing with `b`, `σ` on `closure W` (e.g. cutoffs of coefficients continuous on an
open `U ⊇ closure W`, `exists_cutoff`). `τ_W = exitTimeFrom W Y`.

* `covEntry σ' i j y = (σ' σ'ᵀ)_{ij}(y)`: continuous, PSD everywhere, symmetric.
* `integral_stoppedComposite`: `∫_{(0,t]} φ(Y_r) 1{r ≤ τ} dr = ∫_{(0, t ∧ τ]} φ(Y_r) dr` pathwise.
* **`exists_mp_integrator`**: there is a raw `𝓖`-stopping time `τ`, equal to `τ_W` on every
  continuous path, such that the stopped compensated coordinates
  `M^i_t = Y^i_{t∧τ_W} - Y^i_0 - ∫_0^{t∧τ_W} b_i(Y_s) ds` form a vector integrator
  `IsL2IntegratorVec Q 𝓖 M (psdVersion τ (covEntry σ') Y)` (density `σ'σ'ᵀ(Y_s) 1{s ≤ τ}`
  pathwise a.s. for `s > 0`).
-/

namespace BlockBand.SourceProcess.Stochastic.Representation
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

variable {d m : ℕ}

/-- The covariance entries `(σ σᵀ)_{ij}(y)`. -/
def covEntry (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ) (i j : Fin d) (y : Fin d → ℝ) : ℝ :=
  ∑ k, σ y i k * σ y j k

theorem covEntry_eq (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ) (i j : Fin d)
    (y : Fin d → ℝ) : covEntry σ i j y = (σ y * (σ y).transpose) i j := by
  simp [covEntry, Matrix.mul_apply]

theorem covEntry_symm (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ) (i j : Fin d)
    (y : Fin d → ℝ) : covEntry σ i j y = covEntry σ j i y := by
  simp only [covEntry, mul_comm]

theorem covEntry_psd (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ) (y : Fin d → ℝ)
    (v : Fin d → ℝ) : 0 ≤ ∑ i, ∑ j, v i * v j * covEntry σ i j y := by
  calc (0 : ℝ) ≤ ∑ k, (∑ i, v i * σ y i k) * (∑ j, v j * σ y j k) :=
        Finset.sum_nonneg fun k _ => mul_self_nonneg _
    _ = ∑ k, ∑ i, ∑ j, (v i * σ y i k) * (v j * σ y j k) := by simp only [Finset.sum_mul_sum]
    _ = ∑ i, ∑ k, ∑ j, (v i * σ y i k) * (v j * σ y j k) := Finset.sum_comm
    _ = ∑ i, ∑ j, v i * v j * covEntry σ i j y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [covEntry, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem continuous_covEntry {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ} (hσ : Continuous σ)
    (i j : Fin d) : Continuous (covEntry σ i j) := by
  have hc (i : Fin d) (k : Fin m) : Continuous fun y => σ y i k :=
    (continuous_apply k).comp ((continuous_apply i).comp hσ)
  exact continuous_finsetSum _ fun k _ => (hc i k).mul (hc j k)

variable {Ω : Type*}

/-- `∫_{(0,t]} φ(Y_r) 1{r ≤ τ} dr = ∫_{(0, t ∧ τ]} φ(Y_r) dr`, pathwise. -/
theorem integral_stoppedComposite {E : Type*} (τ : Ω → WithTop ℝ≥0) (φ : E → ℝ)
    (Y : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) :
    ∫ r in Ioc (0 : ℝ) t, stoppedComposite τ φ Y (r, ω) =
      ∫ r in Ioc (0 : ℝ) (stopTime (τ ω) t), φ (Y r.toNNReal ω) := by
  set u := stopTime (τ ω) t
  have hu : u ≤ t := stopTime_le _ _
  have hucoe : ((u : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (τ ω) :=
    coe_untopA_min t (τ ω)
  calc ∫ r in Ioc (0 : ℝ) t, stoppedComposite τ φ Y (r, ω)
      = ∫ r in Ioc (0 : ℝ) t, (Ioc (0 : ℝ) u).indicator (fun r => φ (Y r.toNNReal ω)) r := by
        refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        have hiff : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω ↔ r ∈ Ioc (0 : ℝ) u := by
          have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hr.2
          constructor
          · intro h
            refine ⟨hr.1, ?_⟩
            rw [← Real.toNNReal_le_iff_le_coe]
            have h' : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (τ ω) :=
              le_min (WithTop.coe_le_coe.2 hrt) h
            rw [← hucoe] at h'
            exact WithTop.coe_le_coe.1 h'
          · rintro ⟨-, h⟩
            have h' : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0) :=
              WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 h)
            rw [hucoe] at h'
            exact h'.trans (min_le_right _ _)
        by_cases h : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω
        · rw [indicator_of_mem (hiff.1 h)]
          unfold stoppedComposite
          split_ifs with h'
          · rfl
          · exact absurd h h'
        · rw [indicator_of_notMem (fun hm => h (hiff.2 hm))]
          unfold stoppedComposite
          split_ifs with h'
          · exact absurd h' h
          · rfl
    _ = ∫ r in Ioc (0 : ℝ) t ∩ Ioc (0 : ℝ) u, φ (Y r.toNNReal ω) :=
        setIntegral_indicator measurableSet_Ioc
    _ = _ := by rw [inter_eq_right.2 (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 hu))]

variable {b b' : (Fin d → ℝ) → Fin d → ℝ} {σ σ' : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ}
  {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ}

/-- On a continuous path, the stopped compensated process only sees `b` on `closure W`. -/
theorem stopped_mpCompensated_congr (hW : IsOpen W) (hbb : EqOn b b' (closure W)) {ω : Ω}
    (hω : Continuous fun t => Y t ω) (i : Fin d) (t : ℝ≥0) :
    stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y) t ω =
      stoppedProcess (mpCompensated b' Y i) (exitTimeFrom W Y) t ω := by
  simp only [stoppedProcess_eq_stopTime, mpCompensated]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  rw [hbb ((stopped_path_mem_closure hW hω t).1 s hs)]

theorem continuous_mpCompensated (hb' : Continuous b') {ω : Ω} (hω : Continuous fun t => Y t ω)
    (i : Fin d) : Continuous fun t => mpCompensated b' Y i t ω := by
  have hg : Continuous fun s : ℝ => b' (Y s.toNNReal ω) i :=
    (continuous_apply i).comp (hb'.comp (hω.comp continuous_real_toNNReal))
  have hprim := intervalIntegral.continuous_primitive
    (fun a c => hg.intervalIntegrable (μ := volume) a c) (0 : ℝ)
  have he : (fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, b' (Y s.toNNReal ω) i) =
      fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, b' (Y s.toNNReal ω) i := by
    funext t; rw [intervalIntegral.integral_of_le t.coe_nonneg]
  have hc : Continuous fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, b' (Y s.toNNReal ω) i := by
    rw [he]; exact hprim.comp NNReal.continuous_coe
  exact (((continuous_apply i).comp hω).sub continuous_const).sub hc

/-- Pathwise bound of the stopped compensated process. -/
theorem abs_stopped_mpCompensated_le (hW : IsOpen W) {R B : ℝ} (hR0 : 0 ≤ R) (hB0 : 0 ≤ B)
    (hR : ∀ y ∈ closure W, ∀ i, |y i| ≤ R) (hB : ∀ y ∈ closure W, ∀ i, |b y i| ≤ B)
    {ω : Ω} (hω : Continuous fun t => Y t ω) (i : Fin d) (t : ℝ≥0) :
    |stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y) t ω| ≤ 2 * R + B * t := by
  obtain ⟨hcl, hY0⟩ := stopped_path_mem_closure hW hω t
  set u := stopTime (exitTimeFrom W Y ω) t
  have hu : u ≤ t := stopTime_le _ _
  have h1 : |Y u ω i - Y 0 ω i| ≤ 2 * R := by
    rcases hY0 with h | ⟨h1, h0⟩
    · rw [h, sub_self, abs_zero]; positivity
    · refine (abs_sub _ _).trans ?_
      linarith [hR _ h1 i, hR _ h0 i]
  have h2 : |∫ s in Ioc (0 : ℝ) u, b (Y s.toNNReal ω) i| ≤ B * t := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) u)
      (f := fun s => b (Y s.toNNReal ω) i) (C := B) measure_Ioc_lt_top
      (fun s hs => by rw [Real.norm_eq_abs]; exact hB _ (hcl s hs) i)
    rw [Real.norm_eq_abs] at h
    have hv : volume.real (Ioc (0 : ℝ) u) = u := by simp [Measure.real, Real.volume_Ioc]
    rw [hv] at h
    exact h.trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hu) hB0)
  rw [stoppedProcess_eq_stopTime, mpCompensated]
  exact (abs_sub _ _).trans (by linarith)

variable [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {V : Set (Fin d → ℝ)}

/-- **The stopped compensated process of a martingale-problem solution is a vector
integrator** with the PSD predictable density `psdVersion τ (σ'σ'ᵀ) Y`. -/
theorem exists_mp_integrator (hWV : IsInteriorDomain W V) (hb' : Continuous b')
    (hσ' : Continuous σ') (hbb : EqOn b b' (closure W)) (hσσ : EqOn σ σ' (closure W))
    (hY : IsMPSolutionOn Q 𝓖 b (fun y => σ y * (σ y).transpose) V Y) :
    ∃ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ ∧
      (∀ ω, (Continuous fun t => Y t ω) → τ ω = exitTimeFrom W Y ω) ∧
      IsL2IntegratorVec Q 𝓖 (fun i => stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y))
        (psdVersion τ (covEntry σ') Y) := by
  obtain ⟨τ, hτ, hτc, -⟩ := exists_stoppingTime_ae_eq_hitTime (Q := Q) (F := Wᶜ)
    (fun t => (hY.adapted t).measurable) hY.continuous hWV.1.isClosed_compl
  have hτe : ∀ ω, (Continuous fun t => Y t ω) → τ ω = exitTimeFrom W Y ω := fun ω h => hτc ω h
  obtain ⟨R, hR⟩ : ∃ R, ∀ y ∈ closure W, ∀ i, |y i| ≤ R := by
    obtain ⟨R, hR⟩ := hWV.2.1.exists_bound_of_continuousOn continuousOn_id
    exact ⟨R, fun y hy i => by
      rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm y i).trans (hR y hy)⟩
  obtain ⟨B, hB⟩ : ∃ B, ∀ y ∈ closure W, ∀ i, |b y i| ≤ B := by
    obtain ⟨B, hB⟩ := hWV.2.1.exists_bound_of_continuousOn hb'.continuousOn
    exact ⟨B, fun y hy i => by
      rw [hbb hy, ← Real.norm_eq_abs]; exact (norm_le_pi_norm (b' y) i).trans (hB y hy)⟩
  refine ⟨τ, hτ, hτe, IsL2IntegratorVec.of_psdVersion hτ (continuous_covEntry hσ')
    (covEntry_psd σ') hY.adapted hY.continuous (fun i => ?_) (fun i t => ?_)
    (fun i => hY.drift W hWV i) (fun i j => ?_)⟩
  · filter_upwards [hY.continuous] with ω hω
    have he : (fun t => stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y) t ω) =
        fun t => stoppedProcess (mpCompensated b' Y i) (exitTimeFrom W Y) t ω :=
      funext fun t => stopped_mpCompensated_congr hWV.1 hbb hω i t
    rw [he]
    exact continuous_stoppedProcess (continuous_mpCompensated hb' hω i) _
  · obtain ⟨N, hN, hNe⟩ := hY.drift W hWV i
    refine MemLp.of_bound (((hN.1 t).mono (𝓖.le t)).aestronglyMeasurable.congr (hNe t))
      (2 * max R 0 + max B 0 * t) ?_
    filter_upwards [hY.continuous] with ω hω
    rw [Real.norm_eq_abs]
    exact abs_stopped_mpCompensated_le hWV.1 (le_max_right _ _) (le_max_right _ _)
      (fun y hy i => (hR y hy i).trans (le_max_left _ _))
      (fun y hy i => (hB y hy i).trans (le_max_left _ _)) hω i t
  · obtain ⟨K, hK, hKe⟩ := hY.bracket W hWV i j
    refine ⟨K, hK, fun t => (hKe t).trans ?_⟩
    filter_upwards [hY.continuous] with ω hω
    simp only [stoppedProcess_eq_stopTime]
    rw [integral_stoppedComposite, hτe ω hω]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [covEntry_eq, hσσ ((stopped_path_mem_closure hWV.1 hω t).1 s hs)]

end BlockBand.SourceProcess.Stochastic.Representation
