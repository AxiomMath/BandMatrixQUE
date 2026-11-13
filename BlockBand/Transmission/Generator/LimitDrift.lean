module

public import BlockBand.Transmission.Generator.LimitTerms

/-!
# The drift martingale of every power-sum limit (first half of `martingale`)

Part of the transmission generator theorem.

`limit_drift_martingale hLU hD`: along a moving energy, every `IsPowerTraceLimitAlong` limit has
`M_k(s,t) = P_k(t) - P_k(s) - ∫_s^t A_k(P(u)) du` as martingale increments (natural filtration,
positive times), for every `k ≥ 1`. Hypotheses: `TransmissionLengthUniformContract`
(moments, UI) and `PowerDriftSummable` (finite-`W` drift errors).

Proof (no Skorokhod space, no modulus): for a past test `Φ`, the finite-`W` tested identity
(`abs_integral_drift_le`) gives `E_n[Φ ΔP] - Σ_r E_n[Φ A_k(P_r)]/W → 0`; the Riemann sum is
`∫_s^t E_n[Φ A_k(P_{⌊Wu⌋})] du` up to two boundary cells (`boundary_le`); each time converges
by fdd + `L²` bounds (`drift_point_tendsto`), and dominated convergence in `u` and Fubini on the
limit (`limit_fubini`) identify `E[Φ ∫_s^t A_k]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

theorem drift_cutVec {Ω : Type*} (D : ℝ) (k : ℕ) (Pk : ℕ → ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    transmissionDrift D k (cutVec Pk u ω) = transmissionDrift D k (fun i => Pk i u ω) :=
  (drift_extend_lim D k Pk u ω).2

theorem integral_mul_sub_sum {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {ψ X : α → ℝ} {Y : ℕ → α → ℝ} (S : Finset ℕ) (c : ℝ) (hψ : AEStronglyMeasurable ψ μ)
    {B : ℝ} (hB : ∀ x, |ψ x| ≤ B) (hX : Integrable X μ) (hY : ∀ r, Integrable (Y r) μ) :
    ∫ x, ψ x * (X x - ∑ r ∈ S, Y r x / c) ∂μ =
      ∫ x, ψ x * X x ∂μ - ∑ r ∈ S, (∫ x, ψ x * Y r x ∂μ) / c := by
  have hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ B := Eventually.of_forall fun x => by simpa using hB x
  have hYc : ∀ r, Integrable (fun x => ψ x * (Y r x / c)) μ := fun r =>
    ((hY r).div_const c).bdd_mul hψ hb
  simp only [mul_sub, Finset.mul_sum]
  rw [integral_sub (hX.bdd_mul hψ hb) (integrable_finsetSum _ fun r _ => hYc r),
    integral_finsetSum _ fun r _ => hYc r]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [← mul_div_assoc]
  exact integral_div c _

/-- **Every limit solves the drift part of the martingale problem.** -/
theorem limit_drift_martingale (hLU : TransmissionLengthUniformContract) (hD : PowerDriftSummable)
    {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ}
    {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Pk : ℕ → ℝ → Ω → ℝ} (h : IsPowerTraceLimitAlong b e P Pk) {k : ℕ} (hk : 1 ≤ k) :
    IsMartingaleIncrements P (fun k : {k : ℕ // 1 ≤ k} => Pk k.1) (Set.Ioi 0)
      (fun s t ω => Pk k t ω - Pk k s ω -
        ∫ u in s..t, transmissionDrift (transportD0 b E) k (fun i => Pk i u ω)) := by
  have := h.prob
  obtain ⟨σ, hσm, hσ⟩ := h.fdd
  have hS : LimitSetup b e P Pk σ := ⟨h.prob, h.measurable, hσm.tendsto_atTop, hσ⟩
  have hD0 : 0 ≤ (transportD0 b E) := (transportD0_pos hb0 hE1 hE2).le
  have hH : Continuous (transmissionDrift (transportD0 b E) k) :=
    continuous_transmissionDrift (transportD0 b E) k (v := fun x => x) fun j => continuous_apply j
  intro s t hs ht hst
  have hs0 : 0 < s := hs
  have ht0 : 0 < t := ht
  -- the drift has bounded second moments on `[s, t]` (test `Φ = 1`)
  obtain ⟨K₁, -, -, hK₁⟩ := drift_point_tendsto hLU hb0 hb hE1 hE2 he hS k hs0 (t := t)
    (m := 0) Fin.elim0 (fun l => l.elim0) (BoundedContinuousFunction.const _ 1)
  have hHC : ∀ u ∈ Set.Icc s t, ∫⁻ ω, ‖transmissionDrift (transportD0 b E) k (cutVec Pk u ω)‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal K₁ := fun u hu => by
    simpa [drift_cutVec] using (hK₁ u hu).1
  obtain ⟨Ct, -, hCt⟩ := limit_sq_bound hLU hb0 hb hE1 hE2 he hS hk ht0
  obtain ⟨Cs, -, hCs⟩ := limit_sq_bound hLU hb0 hb hE1 hE2 he hS hk hs0
  have hPt := (sq_integrable_of (h.measurable k hk t ht0).aestronglyMeasurable hCt).2.1
  have hPs := (sq_integrable_of (h.measurable k hk s hs0).aestronglyMeasurable hCs).2.1
  have hAint : Integrable (fun ω => ∫ u in s..t, transmissionDrift (transportD0 b E) k (fun i => Pk i u ω)) P := by
    have := (limit_fubini h.measurable h.continuous hH hs0 hst (ψ := fun _ => (1 : ℝ))
      measurable_const (B := 1) (by simp) hHC).1
    simpa [drift_cutVec] using this
  refine ⟨(hPt.sub hPs).sub hAint, fun m i u hu Φ => ?_⟩
  set pts : Fin m → ℕ × ℝ := fun l => ((i l).1, u l)
  have hpts : ∀ l, 1 ≤ (pts l).1 ∧ 0 < (pts l).2 := fun l => ⟨(i l).2, (hu l).1⟩
  show ∫ ω, Φ (limVec Pk pts ω) * (Pk k t ω - Pk k s ω -
    ∫ u in s..t, transmissionDrift (transportD0 b E) k (fun i => Pk i u ω)) ∂P = 0
  have hψm : Measurable fun ω => Φ (limVec Pk pts ω) :=
    Φ.continuous.measurable.comp (measurable_limVec h.measurable pts hpts)
  obtain ⟨K, hK0, hKfin, hKlim⟩ := drift_point_tendsto hLU hb0 hb hE1 hE2 he hS k hs0 (t := t)
    pts hpts Φ
  have hA := increment_tendsto hLU hb0 hb hE1 hE2 he hS hk hs0 hst pts hpts Φ
  set cn : ℕ → ℕ → ℝ := fun n r => ∫ ω, Φ (finVec b e (σ n) pts ω) *
    transmissionDrift (transportD0 b E) k (pathPowers b (e (σ n)) (σ n) r ω) ∂growthPathLaw (σ n) b
  set g : ℝ → ℝ := fun u => ∫ ω, Φ (limVec Pk pts ω) * transmissionDrift (transportD0 b E) k (fun i => Pk i u ω) ∂P
  -- dominated convergence in `u`
  have hcn_bd : ∀ᶠ n in atTop, ∀ u ∈ Set.Icc s t, |cn n ⌊((σ n : ℕ) : ℝ) * u⌋₊| ≤ 1 + K := by
    filter_upwards [hKfin] with n hn u hu
    exact abs_integral_le_of_sq hK0 (hn u hu)
  have hDCT : Tendsto (fun n => ∫ u in s..t, cn n ⌊((σ n : ℕ) : ℝ) * u⌋₊) atTop
      (𝓝 (∫ u in s..t, g u)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1 + K)
      (Eventually.of_forall fun n => ((measurable_from_nat (f := cn n)).comp
        (Nat.measurable_floor.comp (measurable_const.mul measurable_id))).aestronglyMeasurable)
      ?_ intervalIntegrable_const ?_
    · filter_upwards [hcn_bd] with n hn
      refine Eventually.of_forall fun u hu => ?_
      rw [Set.uIoc_of_le hst] at hu
      rw [Real.norm_eq_abs]; exact hn u ⟨hu.1.le, hu.2⟩
    · refine Eventually.of_forall fun u hu => ?_
      rw [Set.uIoc_of_le hst] at hu
      exact (hKlim u ⟨hu.1.le, hu.2⟩).2
  -- the finite-`W` comparison
  have herr := errSum_tendsto hD hb0 hb hE1 hE2 he hk hs0 (by linarith : s < t + 1) hσm.tendsto_atTop
  set Wb := EnergyUniform.windowWidth (min (2 + E) (2 - E)) Ce
  have hcmp : ∀ᶠ n in atTop, |∫ ω, Φ (finVec b e (σ n) pts ω) *
        (pathPower b (e (σ n)) (σ n) k ⌊((σ n : ℕ) : ℝ) * t⌋₊ ω -
          pathPower b (e (σ n)) (σ n) k ⌊((σ n : ℕ) : ℝ) * s⌋₊ ω) ∂growthPathLaw (σ n) b -
        ∫ u in s..t, cn n ⌊((σ n : ℕ) : ℝ) * u⌋₊| ≤
      ‖Φ‖ * (∑ r ∈ lengthWindow s (t + 1) (σ n),
        ∫ ω, |driftError b E (e (σ n)) (σ n) k r ω| ∂growthPathLaw (σ n) b) +
      2 * (1 + K) / (σ n : ℝ) := by
    filter_upwards [hcn_bd, hσm.tendsto_atTop.eventually_ge_atTop (max Wb 1)] with n hn hn'
    set W := σ n
    have hW : 0 < W := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn')
    have hWr : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    have hmem := along_mem_bulk hE1 hE2 he (le_trans (le_max_left _ _) hn')
    obtain ⟨he1, he2⟩ := bulk_bounds' (by linarith [(mem_bulk_min hE1 hE2).1]) hmem
    set rs := ⌊(W : ℝ) * s⌋₊
    set rt := ⌊(W : ℝ) * t⌋₊
    have hrst : rs ≤ rt := Nat.floor_mono (mul_le_mul_of_nonneg_left hst hWr)
    have hψn : Measurable[growthSigma W rs] fun ω => Φ (finVec b e W pts ω) := by
      refine Φ.continuous.measurable.comp ?_
      refine @Measurable.of_eval _ _ _ (growthSigma W rs) _ _ fun l => ?_
      exact (measurable_pathPower_adapted b (e W) (pts l).1 _).mono
        (growthSigma_mono (Nat.floor_mono (mul_le_mul_of_nonneg_left (hu l).2 hWr))) le_rfl
    have hdi := abs_integral_drift_le (E := E) (by linarith : b < 1) he1 he2 hD0 hk hψn
      (fun ω => abs_bcf_le Φ _) rt hrst
    have hYi : ∀ r, Integrable (fun ω =>
        transmissionDrift (transportD0 b E) k (pathPowers b (e W) W r ω)) (growthPathLaw W b) := fun r => by
      have h1 := integrable_of_ae_bound ((measurable_drift_pathPowers b E (e W) k r).mono
        (growthSigma_le W r) le_rfl) (drift_pathPowers_bound (by linarith) he1 he2 (transportD0 b E) hD0 k r)
      have hWne : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
      refine (h1.const_mul (W : ℝ)).congr (Eventually.of_forall fun ω => ?_)
      simp only
      field_simp
    rw [integral_mul_sub_sum (X := fun ω => pathPower b (e W) W k rt ω - pathPower b (e W) W k rs ω)
      (Y := fun r ω => transmissionDrift (transportD0 b E) k (pathPowers b (e W) W r ω))
      (Finset.Ico rs rt) (W : ℝ)
      (hψn.mono (growthSigma_le W rs) le_rfl).aestronglyMeasurable (fun ω => abs_bcf_le Φ _)
      ((integrable_of_ae_bound (measurable_pathPower _ _ _ _) (pathPower_bound (by linarith) he1 he2
        hk rt)).sub (integrable_of_ae_bound (measurable_pathPower _ _ _ _)
          (pathPower_bound (by linarith) he1 he2 hk rs))) hYi] at hdi
    have hsum := sum_div_eq_integral hW (cn n) hrst
    have hbd := boundary_le hW (cn n) hs0.le hst
    have hb1 : |cn n rs| ≤ 1 + K := hn s ⟨le_rfl, hst⟩
    have hb2 : |cn n rt| ≤ 1 + K := hn t ⟨hst, le_rfl⟩
    have hsub : ∑ r ∈ Finset.Ico rs rt, ∫ ω, |driftError b E (e W) W k r ω| ∂growthPathLaw W b ≤
        ∑ r ∈ lengthWindow s (t + 1) W, ∫ ω, |driftError b E (e W) W k r ω| ∂growthPathLaw W b :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl
        (Nat.floor_mono (mul_le_mul_of_nonneg_left (by linarith) hWr)))
        fun r _ _ => integral_nonneg fun _ => abs_nonneg _
    have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
    have h2 : (|cn n rs| + |cn n rt|) / W ≤ 2 * (1 + K) / W := by
      gcongr; linarith
    have hΦ0 : 0 ≤ ‖Φ‖ := norm_nonneg _
    have h3 := mul_le_mul_of_nonneg_left hsub hΦ0
    rw [hsum] at hdi
    calc _ ≤ |∫ ω, Φ (finVec b e W pts ω) * (pathPower b (e W) W k rt ω -
            pathPower b (e W) W k rs ω) ∂growthPathLaw W b -
          ∫ u in (rs : ℝ) / W..(rt : ℝ) / W, cn n ⌊(W : ℝ) * u⌋₊| +
          |(∫ u in s..t, cn n ⌊(W : ℝ) * u⌋₊) -
            ∫ u in (rs : ℝ) / W..(rt : ℝ) / W, cn n ⌊(W : ℝ) * u⌋₊| := by
          have := abs_sub_le (∫ ω, Φ (finVec b e W pts ω) * (pathPower b (e W) W k rt ω -
            pathPower b (e W) W k rs ω) ∂growthPathLaw W b)
            (∫ u in (rs : ℝ) / W..(rt : ℝ) / W, cn n ⌊(W : ℝ) * u⌋₊)
            (∫ u in s..t, cn n ⌊(W : ℝ) * u⌋₊)
          rwa [abs_sub_comm (∫ u in (rs : ℝ) / W..(rt : ℝ) / W, cn n ⌊(W : ℝ) * u⌋₊)] at this
      _ ≤ _ := add_le_add (hdi.trans h3) (hbd.trans h2)
  -- conclude
  have hW0 : Tendsto (fun n => 2 * (1 + K) / ((σ n : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * (1 + K))).comp hσm.tendsto_atTop
  have hzero : Tendsto (fun n => ∫ ω, Φ (finVec b e (σ n) pts ω) *
        (pathPower b (e (σ n)) (σ n) k ⌊((σ n : ℕ) : ℝ) * t⌋₊ ω -
          pathPower b (e (σ n)) (σ n) k ⌊((σ n : ℕ) : ℝ) * s⌋₊ ω) ∂growthPathLaw (σ n) b -
        ∫ u in s..t, cn n ⌊((σ n : ℕ) : ℝ) * u⌋₊) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ‖Φ‖ * (∑ r ∈ lengthWindow s (t + 1) (σ n),
        ∫ ω, |driftError b E (e (σ n)) (σ n) k r ω| ∂growthPathLaw (σ n) b) +
        2 * (1 + K) / ((σ n : ℕ) : ℝ)) atTop (𝓝 0) := by
      simpa using (herr.const_mul ‖Φ‖).add hW0
    exact squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hcmp) hlim
  have heq := tendsto_nhds_unique (hA.sub hDCT) hzero
  have hfub := (limit_fubini h.measurable h.continuous hH hs0 hst hψm (B := ‖Φ‖)
    (fun ω => abs_bcf_le Φ _) hHC).2
  replace hfub := hfub.1
  simp only [drift_cutVec] at hfub
  have hb' : ∀ᵐ ω ∂P, ‖Φ (limVec Pk pts ω)‖ ≤ ‖Φ‖ :=
    Eventually.of_forall fun ω => Φ.norm_coe_le_norm _
  simp only [mul_sub]
  rw [integral_sub (((hPt.sub hPs).bdd_mul hψm.aestronglyMeasurable hb').congr
      (Eventually.of_forall fun ω => by simp [mul_sub]))
    (hAint.bdd_mul hψm.aestronglyMeasurable hb'), hfub]
  have : ∫ ω, (Φ (limVec Pk pts ω) * Pk k t ω - Φ (limVec Pk pts ω) * Pk k s ω) ∂P =
      ∫ ω, Φ (limVec Pk pts ω) * (Pk k t ω - Pk k s ω) ∂P := by
    simp only [mul_sub]
  rw [this]
  linarith

end BlockBand.Transmission.Generator
