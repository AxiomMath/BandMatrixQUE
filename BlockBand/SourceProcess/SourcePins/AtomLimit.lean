module

public import BlockBand.SourceProcess.SourcePins.AtomClosed
public import BlockBand.SourceProcess.SourcePins.AtomIdent
public import BlockBand.SourceProcess.SourcePins.AtomFinite
public import BlockBand.SourceProcess.SourceProcessLaw.Interface
public import BlockBand.Transmission.LawDuality.BorelGiry
public import BlockBand.Transmission.LawDuality.TightAbsorbed
public import BlockBand.Transmission.LawForced.LawHolds

/-!
# `EntranceAtomic`

The entrance measure of a homogeneous limit is a.s. atomic.

* `measure_notMem_atomSet_le`: for a homogeneous limit `(P, μ)`, `s > 0` and `R > 0`,
  `P(μ(s) ∉ S_R) ≤ B/R`, with `S_R = atomSet (1/2) R` and `B` from the fractional clause of
  `TransmissionLawContract` at `p = 1/2`.
  Proof: `S_R` is closed (`isClosed_atomSet`) and Borel = Giry (`instBorelSpaceFiniteMeasureUnit`).
  The portmanteau inequality for the open set `S_Rᶜ` uses the fdd at `k = 1`. At finite `W`,
  `μ_W(s) ∉ S_R` forces `Tr T^{1/2} > R` (`traceMeasure_mem_atomSet`, since `0 ⪯ T ⪯ I` a.s.).
  Markov's inequality applies to `Tr T^{1/2} = ∫⁻ ψ_{1/2} dμ_W(s)`, a measurable function of
  `μ_W(s)`.
* `entranceAtomic_of hTL : EntranceAtomic`: a.s. `μ(s) ∈ ⋃_R S_R`; `noMassAtZero` and
  `exists_seq_of_mem_atomSet` conclude.
* `entranceAtomic_holds hMT hGA hLp hP : EntranceAtomic` (from the contract hypotheses, via
  `LawForced.transmissionLawContract_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourcePins

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs BlockBand.SourceProcess.SourceProcessLaw
open scoped ENNReal NNReal BoundedContinuousFunction

/-- `Ψ_p(ν) = ∫⁻ ψ_p dν`. -/
def psiInt (p : ℝ) (ν : FiniteMeasure unitInterval) : ℝ≥0∞ :=
  ∫⁻ y, psiP p y ∂(ν : Measure unitInterval)

theorem measurable_psiInt (p : ℝ) : Measurable (psiInt p) :=
  (Measure.measurable_lintegral (measurable_psiP p)).comp measurable_subtype_coe

/-- At finite `W`: `P_W(μ_W(s) ∉ S_R) ≤ E_W Tr T^p / R`. -/
theorem finite_notMem_le {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ} {p R : ℝ}
    (hp : 0 < p) (hR : 0 < R) (s : ℝ) :
    growthPathLaw W b (transmissionProcess b E (fun _ => 0) W s ⁻¹' (atomSet p R)ᶜ) ≤
      (∫⁻ ω, ENNReal.ofReal (fracTrace p (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω))
        ∂growthPathLaw W b) / ENNReal.ofReal R := by
  have hae := Transmission.LawDuality.aemeasurable_transmissionProcess (W := W)
    (κ := fun _ => 0) (fun _ => le_rfl) hb hE1 hE2 s
  have hpas := Transmission.Bridge.ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb hE1 hE2
  have hT : ∀ᵐ ω ∂growthPathLaw W b,
      psiInt p (transmissionProcess b E (fun _ => 0) W s ω) =
        ENNReal.ofReal (fracTrace p (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω)) := by
    filter_upwards [hpas] with ω hω
    exact lintegral_psiP_traceMeasure hp (Transmission.Bridge.pathTransmission_posSemidef hω _)
      (Transmission.Bridge.one_sub_pathTransmission_posSemidef b E _ W _ ω)
  refine (measure_mono_ae ?_).trans ((meas_ge_le_lintegral_div
    ((measurable_psiInt p).comp_aemeasurable hae) (by simpa using hR) ENNReal.ofReal_ne_top).trans
    (le_of_eq (by rw [lintegral_congr_ae (hT.mono fun ω h => by simpa using h)])))
  filter_upwards [hpas, hT] with ω hω hψ hG
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hG
  simp only [Function.comp_apply, hψ]
  refine ENNReal.ofReal_le_ofReal (le_of_lt (not_le.1 fun hle => hG ?_))
  exact traceMeasure_mem_atomSet hp (Transmission.Bridge.pathTransmission_posSemidef hω _)
    (Transmission.Bridge.one_sub_pathTransmission_posSemidef b E _ W _ ω) hle

/-- A probability measure as a point of `ProbabilityMeasure`. -/
def toPM {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] :
    ProbabilityMeasure X :=
  ⟨ν, inferInstance⟩

/-- The fdd clause at `k = 1` as weak convergence of the laws of `μ_W(s)`. -/
theorem tendsto_law {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s : ℝ} (hs : 0 < s) :
    have := hlim.prob
    Tendsto (fun W : ℕ => toPM ((growthPathLaw W b).map (transmissionProcess b E (fun _ => 0) W s)))
      atTop (𝓝 (toPM (P.map (μ s)))) := by
  intro _
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp only [toPM, ProbabilityMeasure.coe_mk]
  rw [integral_map (hlim.measurable s hs).aemeasurable f.continuous.aestronglyMeasurable]
  have h := hlim.fdd 1 (fun _ => s) (fun _ => hs)
    (f.compContinuous ⟨fun v : Fin 1 → FiniteMeasure unitInterval => v 0, continuous_apply 0⟩)
  refine h.congr fun W => ?_
  rw [integral_map (Transmission.LawDuality.aemeasurable_transmissionProcess (fun _ => le_rfl)
    hb hE1 hE2 s) f.continuous.aestronglyMeasurable]
  rfl

/-- **`P(μ(s) ∉ S_R) ≤ B/R`.** -/
theorem measure_notMem_atomSet_le (hTL : TransmissionLawContract) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s : ℝ} (hs : 0 < s) :
    ∃ B : ℝ, ∀ R : ℝ, 0 < R → P (μ s ⁻¹' (atomSet (1 / 2) R)ᶜ) ≤ ENNReal.ofReal (B / R) := by
  obtain ⟨C, hC⟩ := hTL.fractional b hb0 hb E hE1 hE2 (1 / 2) (by norm_num) (by norm_num)
  refine ⟨max (C * (1 + s⁻¹)) 0 + 1, fun R hR => ?_⟩
  have hb1 : b < 1 := by linarith
  have hF := isClosed_atomSet (p := 1 / 2) (R := R) (by norm_num)
  have hconv := tendsto_law hb1 hE1 hE2 hlim hs
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hF.isOpen_compl
  simp only [toPM, ProbabilityMeasure.coe_mk] at hle
  rw [Measure.map_apply (hlim.measurable s hs) hF.isOpen_compl.measurableSet] at hle
  refine hle.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
  have hlt : limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
      (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω))
      ∂growthPathLaw W b) atTop < ENNReal.ofReal (max (C * (1 + s⁻¹)) 0 + 1) :=
    (hC s hs).trans_lt ((ENNReal.ofReal_le_ofReal (le_max_left _ _)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (lt_add_one _)))
  filter_upwards [eventually_lt_of_limsup_lt hlt] with W hW
  rw [Measure.map_apply_of_aemeasurable (Transmission.LawDuality.aemeasurable_transmissionProcess
    (fun _ => le_rfl) hb1 hE1 hE2 s) hF.isOpen_compl.measurableSet,
    ENNReal.ofReal_div_of_pos hR]
  exact (finite_notMem_le hb1 hE1 hE2 (by norm_num) hR s).trans
    (ENNReal.div_le_div_right hW.le _)

/-- **`EntranceAtomic`** from `TransmissionLawContract`. -/
theorem entranceAtomic_of (hTL : TransmissionLawContract) : EntranceAtomic := by
  intro b hb0 hb E hE1 hE2 Ω m P μ hlim s hs
  obtain ⟨B, hB⟩ := measure_notMem_atomSet_le hTL hb0 hb hE1 hE2 hlim hs
  have hall : ∀ᵐ ω ∂P, ∃ R : ℕ, μ s ω ∈ atomSet (1 / 2) R := by
    rw [ae_iff]
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
    obtain ⟨R, hR⟩ := exists_nat_gt (max B 0 / ε)
    have hR0 : (0 : ℝ) < R := lt_of_le_of_lt (div_nonneg (le_max_right _ _) ε.2) hR
    refine (measure_mono fun ω hω => ?_).trans ((hB R hR0).trans ?_)
    · simp only [Set.mem_ofPred_eq, not_exists] at hω
      exact hω R
    · rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ hR0]
      rw [div_lt_iff₀ (by exact_mod_cast hε)] at hR
      nlinarith [le_max_left B 0]
  filter_upwards [hall, hTL.noMassAtZero b hb0 hb E hE1 hE2 Ω m P μ hlim s hs] with ω ⟨R, hR⟩ h0
  exact exists_seq_of_mem_atomSet (by norm_num) (by norm_num) hR h0

/-- **`EntranceAtomic` from the contract hypotheses.** -/
theorem entranceAtomic_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) : EntranceAtomic :=
  entranceAtomic_of (Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP)

end BlockBand.SourceProcess.SourcePins
