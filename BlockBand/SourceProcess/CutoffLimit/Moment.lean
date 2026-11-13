module

public import BlockBand.SourceProcess.CutoffLimit.Approx
public import BlockBand.SourceProcess.CutoffLimit.InitFrame
public import BlockBand.SourceProcess.SourcePins.AtomLimit

/-!
# `E Σ √t_i < ∞` for the entrance, and the small modes carry vanishing mass

* `lintegral_psiInt_le`: for a homogeneous limit `(P, μ)` and `s > 0`,
  `E ∫ψ_{1/2} dμ(s) ≤ C(1 + s⁻¹)`. Each `ν ↦ ∫ g_n dν` is continuous and nonnegative, so the
  portmanteau inequality (Mathlib, from the open-set inequality and `tendsto_law`) bounds
  its mean by `liminf_W E ∫ g_n dμ_W(s) ≤ limsup_W E Tr T^{1/2} ≤ C(1+s⁻¹)`; then Fatou in `n`.
* `lintegral_entrance_psi_lt_top`: the same for `entranceLaw P μ s`, finite.
* `tendsto_tail`: `E ∫ψ_{1/2} 1_{y ≤ (n+1)^{-2}} dν → 0` (dominated convergence twice).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.SourceProcess.SourcePins
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal

/-- `ν ↦ ∫ g_n dν`. -/
def gInt (n : ℕ) (ν : FiniteMeasure unitInterval) : ℝ :=
  ∫ y, gApprox n y ∂(ν : Measure unitInterval)

theorem continuous_gInt (n : ℕ) : Continuous (gInt n) :=
  FiniteMeasure.continuous_integral_continuousMap
    (⟨gApprox n, continuous_gApprox n⟩ : C(unitInterval, ℝ))

theorem gInt_nonneg (n : ℕ) (ν : FiniteMeasure unitInterval) : 0 ≤ gInt n ν :=
  integral_nonneg (gApprox_nonneg n)

theorem ofReal_gInt (n : ℕ) (ν : FiniteMeasure unitInterval) :
    ENNReal.ofReal (gInt n ν) = ∫⁻ y, ENNReal.ofReal (gApprox n y) ∂(ν : Measure unitInterval) :=
  ofReal_integral_eq_lintegral_ofReal
    ((BoundedContinuousFunction.mkOfCompact ⟨gApprox n, continuous_gApprox n⟩).integrable _)
    (ae_of_all _ (gApprox_nonneg n))

theorem ofReal_gInt_le (n : ℕ) (ν : FiniteMeasure unitInterval) :
    ENNReal.ofReal (gInt n ν) ≤ psiInt (1 / 2) ν := by
  rw [ofReal_gInt]
  exact lintegral_mono (gApprox_le_psiP n)

theorem psiInt_le_liminf (ν : FiniteMeasure unitInterval) :
    psiInt (1 / 2) ν ≤ liminf (fun n => ENNReal.ofReal (gInt n ν)) atTop := by
  simp only [ofReal_gInt]
  exact lintegral_psiP_le_liminf _

/-- At fixed `n`: `E ∫ g_n dμ(s) ≤ limsup_W E Tr T^{1/2}`. -/
theorem lintegral_gInt_le {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (gInt n (μ s ω)) ∂P ≤
      limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal (fracTrace (1 / 2)
        (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω)) ∂growthPathLaw W b) atTop := by
  have hP := hlim.prob
  have hconv := tendsto_law hb hE1 hE2 hlim hs
  have hmeas : Measurable fun ν => ENNReal.ofReal (gInt n ν) :=
    (continuous_gInt n).measurable.ennreal_ofReal
  have hport := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := P.map (μ s))
    (μs := fun W : ℕ => (growthPathLaw W b).map (transmissionProcess b E (fun _ => 0) W s))
    (continuous_gInt n) (fun ν => gInt_nonneg n ν) (fun G hG => by
      have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hG
      simpa only [toPM, ProbabilityMeasure.coe_mk] using this)
  rw [lintegral_map hmeas (hlim.measurable s hs)] at hport
  refine hport.trans ((liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)).trans
    (limsup_le_limsup (Eventually.of_forall fun W => ?_) (by isBoundedDefault)
      (by isBoundedDefault)))
  have hae := Transmission.LawDuality.aemeasurable_transmissionProcess (W := W)
    (κ := fun _ => 0) (fun _ => le_rfl) hb hE1 hE2 s
  have hpas := Transmission.Bridge.ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb hE1 hE2
  rw [lintegral_map' hmeas.aemeasurable hae]
  refine lintegral_mono_ae ?_
  filter_upwards [hpas] with ω hω
  refine (ofReal_gInt_le n _).trans (le_of_eq ?_)
  exact lintegral_psiP_traceMeasure (by norm_num) (Transmission.Bridge.pathTransmission_posSemidef hω _)
    (Transmission.Bridge.one_sub_pathTransmission_posSemidef b E _ W _ ω)

/-- **`E ∫ψ_{1/2} dμ(s) ≤ C(1 + s⁻¹)`** from TL `fractional` at `p = 1/2`. -/
theorem lintegral_psiInt_le (hTL : TransmissionLawContract) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, ∫⁻ ω, psiInt (1 / 2) (μ s ω) ∂P ≤ ENNReal.ofReal (C * (1 + s⁻¹)) := by
  obtain ⟨C, hC⟩ := hTL.fractional b hb0 hb E hE1 hE2 (1 / 2) (by norm_num) (by norm_num)
  refine ⟨C, ?_⟩
  have hb1 : b < 1 := by linarith
  calc ∫⁻ ω, psiInt (1 / 2) (μ s ω) ∂P
      ≤ ∫⁻ ω, liminf (fun n => ENNReal.ofReal (gInt n (μ s ω))) atTop ∂P :=
        lintegral_mono fun ω => psiInt_le_liminf _
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (gInt n (μ s ω)) ∂P) atTop :=
        lintegral_liminf_le fun n =>
          ((continuous_gInt n).measurable.comp (hlim.measurable s hs)).ennreal_ofReal
    _ ≤ ENNReal.ofReal (C * (1 + s⁻¹)) :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun n =>
          (lintegral_gInt_le hb1 hE1 hE2 hlim hs n).trans (hC s hs))

/-- **The entrance has `E Σ √t_i < ∞`** (as `E ∫ψ_{1/2} dν` under `entranceLaw P μ s`). -/
theorem lintegral_entrance_psi_lt_top (hTL : TransmissionLawContract) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ ν, ∫⁻ y, psiP (1 / 2) y ∂ν ∂entranceLaw P μ s < ⊤ := by
  obtain ⟨C, hC⟩ := lintegral_psiInt_le hTL hb0 hb hE1 hE2 hlim hs
  have hmc : Measurable fun ω => (μ s ω : Measure unitInterval) :=
    measurable_subtype_coe.comp (hlim.measurable s hs)
  rw [entranceLaw, lintegral_map (Measure.measurable_lintegral (measurable_psiP _)) hmc]
  exact hC.trans_lt ENNReal.ofReal_lt_top

theorem tailPsi_mono {h h' : ℝ} (h0 : 0 ≤ h) (hh : h ≤ h') : tailPsi h ≤ tailPsi h' := by
  intro y
  refine Set.indicator_le_indicator_of_subset (fun y hy => ?_) (fun _ => zero_le) y
  exact le_trans hy (pow_le_pow_left₀ h0 hh 2)

theorem tailPsi_le_psiP (h : ℝ) : tailPsi h ≤ psiP (1 / 2) :=
  fun y => Set.indicator_le_self _ _ y

theorem tendsto_tailPsi (y : unitInterval) :
    Tendsto (fun n : ℕ => tailPsi (1 / ((n : ℝ) + 1)) y) atTop (𝓝 0) := by
  rcases y.2.1.eq_or_lt with hy | hy
  · have hp : psiP (1 / 2) y = 0 := by rw [psiP, ite_eq_right (by rw [← hy]; exact lt_irrefl 0)]
    refine tendsto_const_nhds.congr fun n => ?_
    exact (le_antisymm ((tailPsi_le_psiP _ y).trans hp.le) zero_le).symm
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (y : ℝ))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    refine (Set.indicator_of_notMem (fun hmem => ?_) _).symm
    simp only [Set.mem_ofPred_eq] at hmem
    have hn' : (1 / (y : ℝ)) < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 : 1 / ((n : ℝ) + 1) < y := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hy] at hn'
      linarith
    have h2 : (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
      have h0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      have h1' : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      nlinarith
    linarith

/-- **The small modes carry vanishing mass**: `E ∫ψ_{1/2} 1_{y ≤ (n+1)^{-2}} dν → 0`. -/
theorem tendsto_tail {ent : Measure (Measure unitInterval)}
    (hfin : ∫⁻ ν, ∫⁻ y, psiP (1 / 2) y ∂ν ∂ent < ⊤) :
    Tendsto (fun n : ℕ => ∫⁻ ν, ∫⁻ y, tailPsi (1 / ((n : ℝ) + 1)) y ∂ν ∂ent) atTop (𝓝 0) := by
  have hm : Measurable fun ν : Measure unitInterval => ∫⁻ y, psiP (1 / 2) y ∂ν :=
    Measure.measurable_lintegral (measurable_psiP _)
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := ent) (f := fun _ => 0)
    (F := fun n ν => ∫⁻ y, tailPsi (1 / ((n : ℝ) + 1)) y ∂ν)
    (fun ν => ∫⁻ y, psiP (1 / 2) y ∂ν)
    (fun n => Measure.measurable_lintegral (measurable_tailPsi _))
    (fun n => ae_of_all _ fun ν => lintegral_mono (tailPsi_le_psiP _)) hfin.ne ?_
  · simpa using hlim
  filter_upwards [ae_lt_top hm hfin.ne] with ν hν
  have := tendsto_lintegral_of_dominated_convergence (μ := ν) (f := fun _ => 0)
    (F := fun n => tailPsi (1 / ((n : ℝ) + 1))) (psiP (1 / 2))
    (fun n => measurable_tailPsi _) (fun n => ae_of_all _ (tailPsi_le_psiP _)) hν.ne
    (ae_of_all _ tendsto_tailPsi)
  simpa using this

end BlockBand.SourceProcess.CutoffLimit
