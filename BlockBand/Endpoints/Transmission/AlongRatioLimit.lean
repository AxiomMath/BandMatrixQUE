module

public import BlockBand.Endpoints.Transmission.AlongRatioDrift

/-!
# Tested drift sums along moving energies converge to the base-energy drift integral

Along a sub-limit `(P, μ)` of the processes at energies `e W` (`IsTransmissionSubLimitAlong`,
`W_n = φ n`, `E_n = e W_n`), for a past test `Φ` at times `u_l > 0`, `0 < s ≤ t` and a chamber
point `z`:

* `eventually_energy_along`: eventually `-2 < E_n < 2` and `W_n > 0`;
* `tendsto_test_mul_along`: the past test times a bounded continuous function of a later state
  converges, as in `tendsto_test_mul`, with the width-`W` process at `E_n`;
* `exists_bound_ratioDrift_near`: the drift is bounded uniformly in `ν`, `u`, `E'` and in `D₀'`
  with `|D₀' - D₀| ≤ 1`;
* `tendsto_c_floor_along`: the pointwise limit of the floor-sampled tested drift, as in
  `tendsto_c_floor`, with the extra coefficient error
  `|D₀(E_n) - D₀(E)|·C_z + R·|h_{E_n}(⌊W_nv⌋/W_n) - h_E(v)| → 0` (`abs_ratioDrift_sub_le`,
  `Generator.tendsto_transportD0`, `continuous_absorptionRate_pair`);
* `tendsto_drift_sum_along`: `E_n[testAt · Σ_{⌊W_ns⌋ ≤ r < ⌊W_nt⌋} ratioDriftAt_r(E_n)/W_n]`
  tends to `∫_s^t E[Φ(μ(u_l)) ratioDrift(D₀(E), E, κ, v, z, μ_v)] dv`, the drift at the base
  energy.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Transmission

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.LawDuality BlockBand.Transmission.LawForced
open scoped NNReal ENNReal BoundedContinuousFunction

/-- Eventually along `φ`, the moving energy is in `(-2, 2)` and the width is positive. -/
theorem eventually_energy_along {E Ce : ℝ} {e : ℕ → ℝ} (hE1 : -2 < E) (hE2 : E < 2)
    (he : IsMovingEnergy E Ce e) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    ∀ᶠ n in atTop, -2 < e (φ n) ∧ e (φ n) < 2 ∧ 0 < φ n := by
  obtain ⟨hκI, -⟩ := mem_bulkInterval_half hE1 hE2
  filter_upwards [hφ.eventually (BlockBand.Transmission.LawFinite.eventually_mem_bulkInterval
    hE1 hE2 he), hφ.eventually_ge_atTop 1] with n hn h1
  exact ⟨by linarith [hn.1], by linarith [hn.2], h1⟩

/-- **Past test times a bounded continuous function of a later state, along `e`.** -/
theorem tendsto_test_mul_along {b : ℝ} {e : ℕ → ℝ} {κ : ℝ → ℝ} {φ : ℕ → ℕ}
    (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1) (hEn : ∀ᶠ n in atTop, -2 < e (φ n) ∧ e (φ n) < 2)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (h : IsTransmissionSubLimitAlong b e κ φ P μ) {m : ℕ} {u : Fin m → ℝ} (hu : ∀ l, 0 < u l)
    (Φ : BoundedContinuousFunction (Fin m → FiniteMeasure unitInterval) ℝ) {v : ℝ} (hv : 0 < v)
    (H : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ) :
    Tendsto (fun n => ∫ ω, testAt b (e (φ n)) κ (φ n) u Φ ω *
        H (transmissionProcess b (e (φ n)) κ (φ n) v ω) ∂growthPathLaw (φ n) b) atTop
      (𝓝 (∫ ω, Φ (fun l => μ (u l) ω) * H (μ v ω) ∂P)) := by
  set τ : Fin (m + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) u v
  have hτ : ∀ i, 0 < τ i := fun i => by
    refine Fin.lastCases ?_ (fun l => ?_) i
    · simp only [τ, Fin.snoc_last]; exact hv
    · simp only [τ, Fin.snoc_castSucc]; exact hu l
  set Ψ : BoundedContinuousFunction (Fin (m + 1) → FiniteMeasure unitInterval) ℝ :=
    Φ.compContinuous (initMap m) * H.compContinuous (lastMap m)
  have hΨ : ∀ ν : ℝ → FiniteMeasure unitInterval,
      Ψ (fun i => ν (τ i)) = Φ (fun l => ν (u l)) * H (ν v) := by
    intro ν
    simp only [Ψ, BoundedContinuousFunction.coe_mul, Pi.mul_apply,
      BoundedContinuousFunction.compContinuous_apply, initMap, lastMap, ContinuousMap.coe_mk, τ,
      Fin.snoc_castSucc, Fin.snoc_last]
  have hf := h.fdd (m + 1) τ hτ Ψ
  rw [integral_congr_ae (Eventually.of_forall fun ω => hΨ (fun t => μ t ω))] at hf
  refine hf.congr' ?_
  filter_upwards [hEn] with n hn
  rw [integral_congr_ae (Eventually.of_forall fun ω =>
    hΨ (fun t => transmissionProcess b (e (φ n)) κ (φ n) t ω))]
  refine integral_congr_ae ?_
  filter_upwards [testAt_ae_eq (W := φ n) hκ hb hn.1 hn.2 u Φ] with ω hω
  rw [hω]

/-- `|h_{E'}(u) - h_E(u)| ≤ 4K` when `0 ≤ κ u ≤ K`. -/
theorem abs_absorptionRate_sub_energy_le (E E' : ℝ) (κ : ℝ → ℝ) (u : ℝ) {K : ℝ}
    (h0 : 0 ≤ κ u) (hK : κ u ≤ K) :
    |absorptionRate E' κ u - absorptionRate E κ u| ≤ 4 * K := by
  obtain ⟨a0, a4⟩ := fourPi_semicircle_mem E
  obtain ⟨a0', a4'⟩ := fourPi_semicircle_mem E'
  unfold absorptionRate
  set a := 4 * Real.pi * BlockBand.Parameters.semicircleDensity E
  set a' := 4 * Real.pi * BlockBand.Parameters.semicircleDensity E'
  rw [show a' * κ u - a * κ u = (a' - a) * κ u by ring, abs_mul, abs_of_nonneg h0]
  have hd : |a' - a| ≤ 4 := abs_le.2 ⟨by linarith, by linarith⟩
  calc |a' - a| * κ u ≤ 4 * κ u := mul_le_mul_of_nonneg_right hd h0
    _ ≤ 4 * K := by linarith

/-- The drift at a chamber point is bounded uniformly in `ν`, `u`, `E'` and `|D₀' - D₀| ≤ 1`. -/
theorem exists_bound_ratioDrift_near (D0 E : ℝ) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ)
    {p : ℕ} {z : DualCoord p} (hz : z ∈ dualChamber p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D0' E' u : ℝ) (ν : FiniteMeasure unitInterval), |D0' - D0| ≤ 1 →
      |ratioDrift D0' E' κ u z ν| ≤ K := by
  obtain ⟨C0, hC00, hC0⟩ := exists_bound_drift D0 E hκ hz
  obtain ⟨Cz, hCz0, hCz⟩ := abs_ratioDrift_sub_le hz
  obtain ⟨-, hκ0, Kκ, hKκ⟩ := hκ
  have hzr := IsRatioParameter.isRatioRange hz
  have hR : 0 ≤ ∑ i, (z.1 i + z.2 i) := Finset.sum_nonneg fun i _ => by
    have := hzr.1 i; have := (hzr.2 i).1; linarith
  refine ⟨C0 + Cz + (∑ i, (z.1 i + z.2 i)) * (4 * max Kκ 0), by positivity,
    fun D0' E' u ν hD => ?_⟩
  have h1 := hCz D0 D0' E E' κ u u ν
  have h2 := abs_absorptionRate_sub_energy_le E E' κ u (hκ0 u) ((hKκ u).trans (le_max_left _ 0))
  have h3 : |D0' - D0| * Cz ≤ Cz := by nlinarith [abs_nonneg (D0' - D0)]
  have h4 := mul_le_mul_of_nonneg_left h2 hR
  have h5 := abs_sub_abs_le_abs_sub (ratioDrift D0' E' κ u z ν) (ratioDrift D0 E κ u z ν)
  linarith [hC0 u ν]

section

variable {b E Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {κ : ℝ → ℝ}
  (hκ : IsAbsorptionProfile κ) (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {p : ℕ}
  {z : DualCoord p} (hz : z ∈ dualChamber p) {m : ℕ} {u : Fin m → ℝ}
  (Φ : BoundedContinuousFunction (Fin m → FiniteMeasure unitInterval) ℝ)
  {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
  (h : IsTransmissionSubLimitAlong b e κ φ P μ) (hu : ∀ l, 0 < u l)

include he hκ hb hE1 hE2 hz hφ h hu in
/-- **Pointwise limit of the floor-sampled tested drift, along `e`**, with the base-energy drift. -/
theorem tendsto_c_floor_along {v : ℝ} (hv : 0 < v) :
    Tendsto (fun n => testDrift b (e (φ n)) κ (φ n) u Φ z ⌊((φ n : ℕ) : ℝ) * v⌋₊) atTop
      (𝓝 (∫ ω, Φ (fun l => μ (u l) ω) * ratioDrift (transportD0 b E) E κ v z (μ v ω) ∂P)) := by
  have hEn := eventually_energy_along hE1 hE2 he hφ
  have hlim := tendsto_test_mul_along hκ.2.1 hb (hEn.mono fun n hn => ⟨hn.1, hn.2.1⟩) h hu Φ hv
    (driftBCF (transportD0 b E) E hκ hz v)
  simp only [driftBCF_apply] at hlim
  obtain ⟨Cz, hCz0, hCz⟩ := abs_ratioDrift_sub_le hz
  set R := ∑ i, (z.1 i + z.2 i)
  set δ : ℕ → ℝ := fun n => |transportD0 b (e (φ n)) - transportD0 b E| * Cz +
    R * |absorptionRate (e (φ n)) κ ((⌊((φ n : ℕ) : ℝ) * v⌋₊ : ℝ) / (φ n : ℝ)) -
      absorptionRate E κ v|
  have hgap : Tendsto (fun n => ‖Φ‖ * δ n) atTop (𝓝 0) := by
    have hD : Tendsto (fun n => |transportD0 b (e (φ n)) - transportD0 b E|) atTop (𝓝 0) := by
      refine ((BlockBand.Transmission.Generator.tendsto_transportD0 (b := b) hE1 hE2 he).comp
        hφ).congr fun n => ?_
      simp only [Function.comp, abs_sub_comm]
    have hpair : Tendsto (fun n => ((e (φ n), (⌊((φ n : ℕ) : ℝ) * v⌋₊ : ℝ) / (φ n : ℝ)) :
        ℝ × ℝ)) atTop (𝓝 (E, v)) :=
      ((BlockBand.Transmission.Generator.tendsto_movingEnergy he).comp hφ).prodMk_nhds
        (tendsto_floor_div hφ hv.le)
    have hh := ((continuous_absorptionRate_pair hκ.1).tendsto (E, v)).comp hpair
    have hh0 : Tendsto (fun n => |absorptionRate (e (φ n)) κ
        ((⌊((φ n : ℕ) : ℝ) * v⌋₊ : ℝ) / (φ n : ℝ)) - absorptionRate E κ v|) atTop (𝓝 0) := by
      have := (hh.sub (tendsto_const_nhds (x := absorptionRate E κ v))).abs
      simpa [Function.comp] using this
    have := ((hD.mul_const Cz).add (hh0.const_mul R)).const_mul ‖Φ‖
    simpa [δ] using this
  obtain ⟨C, -, hC⟩ := exists_bound_drift (transportD0 b E) E hκ hz
  have hdiff : ∀ᶠ n in atTop, ‖testDrift b (e (φ n)) κ (φ n) u Φ z ⌊((φ n : ℕ) : ℝ) * v⌋₊ -
      ∫ ω, testAt b (e (φ n)) κ (φ n) u Φ ω *
        ratioDrift (transportD0 b E) E κ v z (transmissionProcess b (e (φ n)) κ (φ n) v ω)
          ∂growthPathLaw (φ n) b‖ ≤ ‖Φ‖ * δ n := by
    filter_upwards [hEn] with n hn
    obtain ⟨hn1, hn2, -⟩ := hn
    set W := φ n
    set En := e (φ n)
    obtain ⟨Cn, -, hCn⟩ := exists_bound_drift (transportD0 b En) En hκ hz
    have htest : Measurable (testAt b En κ W u Φ) :=
      Φ.continuous.measurable.comp (measurable_pi_iff.mpr fun l => measurable_stateAt' b En κ _)
    have hTP := aemeasurable_transmissionProcess (W := W) hκ.2.1 hb hn1 hn2 v
    have hA : Integrable (fun ω => testAt b En κ W u Φ ω *
        ratioDriftAt b En κ W ⌊(W : ℝ) * v⌋₊ z ω) (growthPathLaw W b) := by
      refine Integrable.of_bound (C := ‖Φ‖ * Cn) (htest.aestronglyMeasurable.mul ?_)
        (Eventually.of_forall fun ω => ?_)
      · exact ((continuous_ratioDrift_nu _ En hκ.1 hz _).measurable.comp_aemeasurable
          hTP).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_testAt_le b En κ u Φ ω) (hCn _ _) (abs_nonneg _) (norm_nonneg _)
    have hB : Integrable (fun ω => testAt b En κ W u Φ ω *
        ratioDrift (transportD0 b E) E κ v z (transmissionProcess b En κ W v ω))
        (growthPathLaw W b) := by
      refine Integrable.of_bound (C := ‖Φ‖ * C) (htest.aestronglyMeasurable.mul ?_)
        (Eventually.of_forall fun ω => ?_)
      · exact ((continuous_ratioDrift_nu _ E hκ.1 hz _).measurable.comp_aemeasurable
          hTP).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_testAt_le b En κ u Φ ω) (hC _ _) (abs_nonneg _) (norm_nonneg _)
    rw [testDrift, ← integral_sub hA hB]
    have hδ0 : 0 ≤ δ n := by
      have : 0 ≤ R := Finset.sum_nonneg fun i _ => by
        have hzr := IsRatioParameter.isRatioRange hz
        have := hzr.1 i; have := (hzr.2 i).1; linarith
      positivity
    have hint := norm_integral_le_of_norm_le_const (μ := growthPathLaw W b)
      (f := fun ω => testAt b En κ W u Φ ω * ratioDriftAt b En κ W ⌊(W : ℝ) * v⌋₊ z ω -
        testAt b En κ W u Φ ω *
          ratioDrift (transportD0 b E) E κ v z (transmissionProcess b En κ W v ω))
      (C := ‖Φ‖ * δ n)
      (Eventually.of_forall fun ω => by
        rw [← mul_sub, Real.norm_eq_abs, abs_mul]
        have hd := hCz (transportD0 b E) (transportD0 b En) E En κ v
          ((⌊(W : ℝ) * v⌋₊ : ℝ) / W) (transmissionProcess b En κ W v ω)
        change |testAt b En κ W u Φ ω| * |ratioDrift (transportD0 b En) En κ
          ((⌊(W : ℝ) * v⌋₊ : ℝ) / W) z (transmissionProcess b En κ W v ω) -
          ratioDrift (transportD0 b E) E κ v z (transmissionProcess b En κ W v ω)| ≤ _
        exact mul_le_mul (abs_testAt_le b En κ u Φ ω) hd (abs_nonneg _) (norm_nonneg _))
    rwa [probReal_univ, mul_one] at hint
  have h0 : Tendsto (fun n => testDrift b (e (φ n)) κ (φ n) u Φ z ⌊((φ n : ℕ) : ℝ) * v⌋₊ -
      ∫ ω, testAt b (e (φ n)) κ (φ n) u Φ ω *
        ratioDrift (transportD0 b E) E κ v z (transmissionProcess b (e (φ n)) κ (φ n) v ω)
          ∂growthPathLaw (φ n) b) atTop (𝓝 0) := squeeze_zero_norm' hdiff hgap
  simpa using h0.add hlim

include he hκ hb hE1 hE2 hz hφ h hu in
/-- **The tested drift sums along `e` converge to the base-energy limit drift integral.** -/
theorem tendsto_drift_sum_along {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    Tendsto (fun n => ∫ ω, testAt b (e (φ n)) κ (φ n) u Φ ω *
        ∑ r ∈ Finset.Ico ⌊((φ n : ℕ) : ℝ) * s⌋₊ ⌊((φ n : ℕ) : ℝ) * t⌋₊,
          ratioDriftAt b (e (φ n)) κ (φ n) r z ω / (φ n : ℝ) ∂growthPathLaw (φ n) b) atTop
      (𝓝 (∫ v in s..t, ∫ ω, Φ (fun l => μ (u l) ω) *
        ratioDrift (transportD0 b E) E κ v z (μ v ω) ∂P)) := by
  have hEn := eventually_energy_along hE1 hE2 he hφ
  obtain ⟨K0, hK00, hK0⟩ := exists_bound_ratioDrift_near (transportD0 b E) E hκ hz
  have hDn : ∀ᶠ n in atTop, |transportD0 b (e (φ n)) - transportD0 b E| ≤ 1 := by
    have hD := (BlockBand.Transmission.Generator.tendsto_transportD0 (b := b) hE1 hE2 he).comp hφ
    filter_upwards [hD.eventually (ge_mem_nhds one_pos)] with n hn
    simpa [Function.comp, abs_sub_comm] using hn
  set K := ‖Φ‖ * K0
  set g : ℕ → ℝ → ℝ := fun n v => testDrift b (e (φ n)) κ (φ n) u Φ z ⌊((φ n : ℕ) : ℝ) * v⌋₊
  have hgK : ∀ᶠ n in atTop, ∀ v, ‖g n v‖ ≤ K := by
    filter_upwards [hDn] with n hn v
    have hint := norm_integral_le_of_norm_le_const (μ := growthPathLaw (φ n) b)
      (f := fun ω => testAt b (e (φ n)) κ (φ n) u Φ ω *
        ratioDriftAt b (e (φ n)) κ (φ n) ⌊((φ n : ℕ) : ℝ) * v⌋₊ z ω) (C := K)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_testAt_le b _ κ u Φ ω) (hK0 _ _ _ _ hn) (abs_nonneg _)
          (norm_nonneg _))
    rwa [probReal_univ, mul_one] at hint
  have hgi : ∀ n x y, IntervalIntegrable (g n) volume x y := fun n x y =>
    BlockBand.Transmission.Generator.intervalIntegrable_floor_comp (W := φ n)
      (testDrift b (e (φ n)) κ (φ n) u Φ z) x y
  -- the middle integral
  have hmid : Tendsto (fun n => ∫ v in s..t, g n v) atTop
      (𝓝 (∫ v in s..t, ∫ ω, Φ (fun l => μ (u l) ω) *
        ratioDrift (transportD0 b E) E κ v z (μ v ω) ∂P)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => K)
      (Eventually.of_forall fun n => (hgi n s t).def'.aestronglyMeasurable)
      (hgK.mono fun n hn => Eventually.of_forall fun v _ => hn v)
      intervalIntegrable_const (Eventually.of_forall fun v hv => ?_)
    have hv0 : 0 < v := by
      rw [Set.uIoc_of_le hst] at hv; exact hs.trans hv.1
    exact tendsto_c_floor_along he hκ hb hE1 hE2 hz Φ hφ h hu hv0
  -- the boundary cells
  have hcell : ∀ {x : ℝ}, 0 < x → Tendsto (fun n =>
      ∫ v in (⌊((φ n : ℕ) : ℝ) * x⌋₊ : ℝ) / (φ n : ℝ)..x, g n v) atTop (𝓝 0) := by
    intro x hx
    have hcon := tendsto_floor_div hφ hx.le
    have hb0 : Tendsto (fun n => K * |x - (⌊((φ n : ℕ) : ℝ) * x⌋₊ : ℝ) / (φ n : ℝ)|) atTop
        (𝓝 0) := by
      have := ((tendsto_const_nhds (x := x)).sub hcon).abs.const_mul K
      simpa using this
    refine squeeze_zero_norm' ?_ hb0
    filter_upwards [hgK] with n hn
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun v _ => hn v
  have hlim := ((hcell hs).add hmid).sub (hcell (hs.trans_le hst))
  simp only [zero_add, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hEn] with n hn
  obtain ⟨hn1, hn2, hW⟩ := hn
  have hr : ⌊((φ n : ℕ) : ℝ) * s⌋₊ ≤ ⌊((φ n : ℕ) : ℝ) * t⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg _))
  rw [sum_eq_integral_floor hκ hb hn1 hn2 hz Φ hW hr]
  change _ = ∫ v in (⌊((φ n : ℕ) : ℝ) * s⌋₊ : ℝ) / (φ n : ℝ)..(⌊((φ n : ℕ) : ℝ) * t⌋₊ : ℝ) /
    (φ n : ℝ), g n v
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (hgi n ((⌊((φ n : ℕ) : ℝ) * s⌋₊ : ℝ) / (φ n : ℝ)) s)
    (hgi n s ((⌊((φ n : ℕ) : ℝ) * t⌋₊ : ℝ) / (φ n : ℝ)))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hgi n s t)
    (hgi n t ((⌊((φ n : ℕ) : ℝ) * t⌋₊ : ℝ) / (φ n : ℝ)))
  have e3 := intervalIntegral.integral_symm (f := g n) (μ := volume) t
    ((⌊((φ n : ℕ) : ℝ) * t⌋₊ : ℝ) / (φ n : ℝ))
  linarith

end

end BlockBand.Endpoints.Transmission
