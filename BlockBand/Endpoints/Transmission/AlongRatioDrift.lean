module

public import BlockBand.Endpoints.Transmission.AlongDefs
public import BlockBand.Transmission.LawForced.AbsSum
public import BlockBand.Transmission.LawForced.LimitDrift
public import BlockBand.Transmission.Absorbed.MixBulk
public import BlockBand.Transmission.Absorbed.JetUniform
public import BlockBand.Transmission.LawFinite.Along
public import BlockBand.Transmission.Generator.DriftOneSum
public import BlockBand.Transmission.LawDuality.Entrance

/-!
# The ratio drift along moving energies: coefficient continuity and summed errors

Two inputs for the passage to sub-limits along a moving energy `e W` (`|e W - E| ≤ Ce/W²`):

* the drift coefficient is continuous in `(D₀, E, u)`, uniformly in `ν`, at a fixed chamber point
  (`dualGenerator_eq_mul`: the generator is linear in `D₀`; `abs_ratioDrift_sub_le`:
  `|ratioDrift D₀' E' κ u' z ν - ratioDrift D₀ E κ u z ν| ≤ |D₀' - D₀|·C_z + R(z)·|h' - h|`,
  with `h = absorptionRate`; `continuous_absorptionRate_pair`; `abs_absorptionRate_sub_le`:
  `|h_E(u) - h_E(u')| ≤ 4|κ u - κ u'|` for every `E`, since `4πρ ≤ 4`);
* `tendsto_ratioDriftError_along`: the width-`W` summed `L¹` drift error at energy `e W` tends
  to `0`. The bound `ratioDriftError_abs_L1` is bulk-uniform (its constants are chosen before
  `E ∈ bulkInterval κI`), so it applies at `E := e W` once `e W` is in the bulk
  (`LawFinite.eventually_mem_bulkInterval`); the moment inputs are
  `Absorbed.absorbedJetMoments_holds` and `Absorbed.absorbedSourceMixingBulk_holds`, and the
  time-shift term is bounded uniformly in the energy.

The hypotheses are `MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient`
and `GaussianPoincare`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Transmission

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.LawDuality BlockBand.Transmission.LawForced
open scoped NNReal ENNReal BoundedContinuousFunction

/-!
## Continuity of the drift coefficient
-/

/-- The dual generator is linear in `D₀`. -/
theorem dualGenerator_eq_mul (D0 : ℝ) {q : ℕ} (f : DualCoord q → ℝ) (z : DualCoord q) :
    dualGenerator D0 f z = D0 * dualGenerator 1 f z := by
  unfold dualGenerator; ring

/-- `4πρ(E) ∈ [0, 4]` for every real `E`. -/
theorem fourPi_semicircle_mem (E : ℝ) :
    0 ≤ 4 * Real.pi * BlockBand.Parameters.semicircleDensity E ∧
      4 * Real.pi * BlockBand.Parameters.semicircleDensity E ≤ 4 := by
  unfold BlockBand.Parameters.semicircleDensity
  have hs0 : 0 ≤ Real.sqrt (4 - E ^ 2) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h4]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hpi : 0 < Real.pi := Real.pi_pos
  have e : 4 * Real.pi * (Real.sqrt (4 - E ^ 2) / (2 * Real.pi)) = 2 * Real.sqrt (4 - E ^ 2) := by
    field_simp; ring
  rw [e]; constructor <;> linarith

/-- `|h_E(u) - h_E(u')| ≤ 4|κ u - κ u'|`, uniformly in the energy. -/
theorem abs_absorptionRate_sub_le (E : ℝ) (κ : ℝ → ℝ) (u u' : ℝ) :
    |absorptionRate E κ u - absorptionRate E κ u'| ≤ 4 * |κ u - κ u'| := by
  obtain ⟨h0, h4⟩ := fourPi_semicircle_mem E
  unfold absorptionRate
  rw [show 4 * Real.pi * BlockBand.Parameters.semicircleDensity E * κ u -
      4 * Real.pi * BlockBand.Parameters.semicircleDensity E * κ u' =
      4 * Real.pi * BlockBand.Parameters.semicircleDensity E * (κ u - κ u') by ring, abs_mul,
    abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)

/-- `(E, u) ↦ h_E(u) = 4πρ(E)κ(u)` is jointly continuous. -/
theorem continuous_absorptionRate_pair {κ : ℝ → ℝ} (hκ : Continuous κ) :
    Continuous fun q : ℝ × ℝ => absorptionRate q.1 κ q.2 := by
  unfold absorptionRate BlockBand.Parameters.semicircleDensity
  have hρ : Continuous fun q : ℝ × ℝ => Real.sqrt (4 - q.1 ^ 2) / (2 * Real.pi) :=
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_fst.pow 2))).div_const _
  exact (continuous_const.mul hρ).mul (hκ.comp continuous_snd)

/-- **Continuity of the drift coefficient, uniformly in `ν`**, at a fixed chamber point. -/
theorem abs_ratioDrift_sub_le {p : ℕ} {z : DualCoord p} (hz : z ∈ dualChamber p) :
    ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ (D0 D0' E E' : ℝ) (κ : ℝ → ℝ) (u u' : ℝ)
      (ν : FiniteMeasure unitInterval),
      |ratioDrift D0' E' κ u' z ν - ratioDrift D0 E κ u z ν| ≤
        |D0' - D0| * Cz + (∑ i, (z.1 i + z.2 i)) *
          |absorptionRate E' κ u' - absorptionRate E κ u| := by
  obtain ⟨C, hC⟩ := exists_bound_dualGenerator_ratioOn 1 isCompact_singleton
    (Set.singleton_subset_iff.mpr hz)
  refine ⟨max C 0, le_max_right _ _, fun D0 D0' E E' κ u u' ν => ?_⟩
  have hzr := IsRatioParameter.isRatioRange hz
  have hR : 0 ≤ ∑ i, (z.1 i + z.2 i) := Finset.sum_nonneg fun i _ => by
    have := hzr.1 i; have := (hzr.2 i).1; linarith
  have hF := transmissionRatio_mem_vec hzr ν
  have hG : |dualGenerator 1 (ratioOn ν) z| ≤ max C 0 :=
    (hC z (Set.mem_singleton z) ν).trans (le_max_left _ _)
  have e : ratioDrift D0' E' κ u' z ν - ratioDrift D0 E κ u z ν =
      (D0' - D0) * dualGenerator 1 (ratioOn ν) z -
        (absorptionRate E' κ u' - absorptionRate E κ u) * (∑ i, (z.1 i + z.2 i)) *
          transmissionRatio z.1 z.2 ν := by
    unfold ratioDrift
    rw [dualGenerator_eq_mul D0', dualGenerator_eq_mul D0]; ring
  rw [e]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hG (abs_nonneg _)
  · rw [abs_mul, abs_mul, abs_of_nonneg hR, abs_of_pos hF.1]
    calc |absorptionRate E' κ u' - absorptionRate E κ u| * (∑ i, (z.1 i + z.2 i)) *
          transmissionRatio z.1 z.2 ν
        ≤ |absorptionRate E' κ u' - absorptionRate E κ u| * (∑ i, (z.1 i + z.2 i)) * 1 :=
          mul_le_mul_of_nonneg_left hF.2 (mul_nonneg (abs_nonneg _) hR)
      _ = _ := by ring

/-!
## The summed width-`W` error at energy `e W`
-/

/-- **The summed ratio drift error along a moving energy tends to `0`** (as in
`ratioDriftSummable_of_pins` at `E := e W`; the constants of `ratioDriftError_abs_L1` are
bulk-uniform). -/
theorem tendsto_ratioDriftError_along (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    {b E Ce : ℝ} {e : ℕ → ℝ} {κ : ℝ → ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (he : IsMovingEnergy E Ce e) (hκ : IsAbsorptionProfile κ) {p : ℕ}
    {z : DualCoord p} (hz : z ∈ dualChamber p) {ε T : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) :
    Tendsto (fun W : ℕ => ∑ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
      ∫ ω, |ratioDriftError b (e W) κ W z r ω| ∂growthPathLaw W b) atTop (𝓝 0) := by
  obtain ⟨hκI, -⟩ := mem_bulkInterval_half hE1 hE2
  obtain ⟨C, W₀, hC0, hL⟩ := ratioDriftError_abs_L1 hMT hGA hLp hP
    (BlockBand.Transmission.Absorbed.absorbedJetMoments_holds hMT hGA hLp)
    (BlockBand.Transmission.Absorbed.absorbedSourceMixingBulk_holds hMT hGA hLp)
    (κI := (2 - |E|) / 2) (ε := ε / 2) (T := T + 1) hb0 hb hκI (by positivity)
    (by linarith) hκ hz
  have hT0 : 0 < T := by linarith
  have hb1 : b < 1 := by linarith
  have hzr := IsRatioParameter.isRatioRange hz
  have hR : 0 ≤ ∑ i, (z.1 i + z.2 i) := Finset.sum_nonneg fun i _ => by
    have := hzr.1 i; have := (hzr.2 i).1; linarith
  have hts := tendsto_time_shift hκ.1 (ε := ε) hT0.le
  have hU : Tendsto (fun W : ℕ => T * C * (Real.sqrt W)⁻¹ + (∑ i, (z.1 i + z.2 i)) *
      (4 * ∑ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
        |κ ((r : ℝ) / W) - κ (((r : ℝ) + 1) / W)| / W)) atTop (𝓝 0) := by
    have hs : Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    simpa using (hs.const_mul (T * C)).add ((hts.const_mul 4).const_mul (∑ i, (z.1 i + z.2 i)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ =>
      abs_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (max W₀ ⌈2 / ε⌉₊),
    BlockBand.Transmission.LawFinite.eventually_mem_bulkInterval hE1 hE2 he] with W hW hEW
  simp only [max_le_iff] at hW
  obtain ⟨hW0, hW2⟩ := hW
  have hE4 : e W ^ 2 ≤ 4 := by
    have h1 := hEW.1; have h2 := hEW.2
    have : |E| < 2 := abs_lt.2 ⟨hE1, hE2⟩
    nlinarith [abs_nonneg E]
  have hWε : 2 / ε ≤ (W : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hW2)
  have hεW : 2 ≤ ε * W := by rw [div_le_iff₀ hε] at hWε; linarith
  have hWpos : (0 : ℝ) < W := by nlinarith
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  have hb' : ∀ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
      ∫ ω, |ratioDriftError b (e W) κ W z r ω| ∂growthPathLaw W b ≤
        C * (Real.sqrt W)⁻¹ ^ 3 + (∑ i, (z.1 i + z.2 i)) *
          (4 * (|κ ((r : ℝ) / W) - κ (((r : ℝ) + 1) / W)| / W)) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have h1 := Nat.lt_floor_add_one ((W : ℝ) * ε)
    have h2 : (⌊(W : ℝ) * ε⌋₊ : ℝ) ≤ r := by exact_mod_cast hr.1
    have hr2 : ε / 2 * W ≤ r := by nlinarith
    have hr1 : 1 ≤ r := by
      have : (1 : ℝ) ≤ r := by nlinarith
      exact_mod_cast this
    have hr3 : (r : ℝ) ≤ (T + 1) * W := by
      have h3 : (r : ℝ) < ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast hr.2
      have h4 := Nat.floor_le (mul_nonneg hWpos.le hT0.le)
      nlinarith
    have := hL W hW0 (e W) hEW r hr1 hr2 hr3
    rw [drift_D_eq hb1 hE4 κ hWpos r] at this
    refine this.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hR))
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (abs_absorptionRate_sub_le (e W) κ _ _) hWpos.le
  refine (Finset.sum_le_sum hb').trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hcard := card_Ico_floor_le (W := W) (ε := ε) hT0.le
  have hK0 : 0 ≤ C * (Real.sqrt W)⁻¹ ^ 3 := by positivity
  have hsW : (W : ℝ) * (Real.sqrt W)⁻¹ ^ 3 = (Real.sqrt W)⁻¹ := by
    set q := Real.sqrt W
    have h2 : (W : ℝ) = q ^ 2 := (Real.sq_sqrt hWpos.le).symm
    rw [h2]
    have hq : q ≠ 0 := hs0.ne'
    field_simp
  have := mul_le_mul_of_nonneg_right hcard hK0
  have e' : T * W * (C * (Real.sqrt W)⁻¹ ^ 3) = T * C * ((W : ℝ) * (Real.sqrt W)⁻¹ ^ 3) := by
    ring
  rw [hsW] at e'
  linarith

end BlockBand.Endpoints.Transmission
