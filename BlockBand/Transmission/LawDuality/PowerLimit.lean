module

public import BlockBand.Transmission.LawDuality.PowerBridge
public import BlockBand.Transmission.DualBoundary.LawConv

/-!
# Homogeneous subsequential limits are power-trace limits; the generator mass bound

This is where the transmission generator theorem enters the transmission law for `κ ≡ 0`.

* `powerProcess μ k t = ∫ s^{k-1} dμ_t` (`= P_k(t)` of the limit).
* `measurable_integral_continuous`: `ν ↦ ∫ g dν` is Giry-measurable for continuous `g`.
* `IsTransmissionSubLimit.comp`: a subsequential limit along `φ` is one along `φ ∘ σ`, `σ → ∞`.
* **`isPowerTraceLimit_of_subLimit`**: every homogeneous subsequential limit `(P, μ)` gives a
  limit `(P, powerProcess μ)` of the power sums in the sense of
  `TransmissionStatements.IsPowerTraceLimit`; hence `hTG.martingale` and `hTG.meanConductance`
  apply to it.
* **`hasLocalMassBound_zero`**: under `hTG : TransmissionGeneratorContract`, every homogeneous
  subsequential limit has `E μ_t[0,1] ≤ 2/(D₀ε)` on `[ε, T]` (`HasLocalMassBound`), the
  `κ ≡ 0` case of the third clause of `SubLimitRatioMP`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal BoundedContinuousFunction

/-- `Π_k(t) = ∫ s^{k-1} dμ_t`. -/
def powerProcess {Ω : Type*} (μ : ℝ → Ω → FiniteMeasure unitInterval) : ℕ → ℝ → Ω → ℝ :=
  fun k t ω => ∫ s, (s : ℝ) ^ (k - 1) ∂(μ t ω : Measure unitInterval)

/-- `s ↦ s^j` on `[0,1]`. -/
def powBCF (j : ℕ) : unitInterval →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun s => (s : ℝ) ^ j, continuous_subtype_val.pow j⟩

theorem measurable_integral_continuous (g : C(unitInterval, ℝ)) :
    Measurable fun ν : FiniteMeasure unitInterval => ∫ t, g t ∂(ν : Measure unitInterval) :=
  measurable_integral_continuous_of (ν := id) (fun k => measurable_logTransform (evalPoint_pos k).le) g

variable {b E : ℝ} {κ : ℝ → ℝ} {φ : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {μ : ℝ → Ω → FiniteMeasure unitInterval}

theorem IsTransmissionSubLimit.comp (h : IsTransmissionSubLimit b E κ φ P μ) {σ : ℕ → ℕ}
    (hσ : Tendsto σ atTop atTop) : IsTransmissionSubLimit b E κ (φ ∘ σ) P μ :=
  { h with fdd := fun k τ hτ Φ => (h.fdd k τ hτ Φ).comp hσ }

/-- **Homogeneous subsequential limits are power-trace limits** (strictly increasing `φ`). -/
theorem isPowerTraceLimit_of_subLimit (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hφ : StrictMono φ) (h : IsTransmissionSubLimit b E (fun _ => 0) φ P μ) :
    IsPowerTraceLimit b E P (powerProcess μ) where
  prob := h.prob
  measurable k _ t ht := (measurable_integral_continuous (powBCF (k - 1)).toContinuousMap).comp
    (h.measurable t ht)
  continuous k _ := h.continuous.mono fun ω hω =>
    (FiniteMeasure.continuous_integral_boundedContinuousFunction (powBCF (k - 1))).comp_continuousOn hω
  fdd := by
    refine ⟨φ, hφ, fun m ks ts hkt Φ => ?_⟩
    let F : C(Fin m → FiniteMeasure unitInterval, Fin m → ℝ) :=
      ⟨fun ν l => ∫ s, (s : ℝ) ^ (ks l - 1) ∂(ν l : Measure unitInterval),
        continuous_pi fun l => (FiniteMeasure.continuous_integral_boundedContinuousFunction
          (powBCF (ks l - 1))).comp (continuous_apply l)⟩
    have hlim := h.fdd m ts (fun l => (hkt l).2) (Φ.compContinuous F)
    refine hlim.congr fun n => integral_congr_ae ?_
    filter_upwards [ae_integral_pow_transmissionProcess (W := φ n) (b := b) (E := E)
      (κ := fun _ => 0) (fun _ => le_rfl) (by linarith) hE1 hE2] with ω hω
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, F]
    congr 1
    funext l
    rw [hω, Nat.sub_add_cancel (hkt l).1]
    rfl

theorem isPowerTraceLimit_of_subLimit' (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hφ : Tendsto φ atTop atTop) (h : IsTransmissionSubLimit b E (fun _ => 0) φ P μ) :
    IsPowerTraceLimit b E P (powerProcess μ) := by
  obtain ⟨σ, hσ, hφσ⟩ := strictMono_subseq_of_tendsto_atTop hφ
  exact isPowerTraceLimit_of_subLimit hb2 hE1 hE2 hφσ (h.comp hσ.tendsto_atTop)

/-- **The TG mean-conductance bound gives the local mass bound** (`κ ≡ 0`). -/
theorem hasLocalMassBound_zero (hTG : TransmissionGeneratorContract) (hb : 0 < b)
    (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hφ : Tendsto φ atTop atTop)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (h : IsTransmissionSubLimit b E (fun _ => 0) φ P μ) : HasLocalMassBound P μ := by
  have hPT := isPowerTraceLimit_of_subLimit' hb2 hE1 hE2 hφ h
  have hD := DualBoundary.transportD0_pos hb hE1 hE2
  intro ε T hε
  refine ⟨2 / (transportD0 b E * ε), fun t ht => ?_⟩
  have ht0 : 0 < t := hε.trans_le ht.1
  have hm := hTG.meanConductance b hb hb2 E hE1 hE2 Ω inferInstance P (powerProcess μ) hPT t ht0
  have e : ∀ ω, (μ t ω : Measure unitInterval) Set.univ = ‖powerProcess μ 1 t ω‖ₑ := by
    intro ω
    have h1 : powerProcess μ 1 t ω = (μ t ω : Measure unitInterval).real Set.univ := by
      simp [powerProcess]
    rw [h1, Real.enorm_eq_ofReal measureReal_nonneg, Measure.real,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [e]
  refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (mul_le_mul_of_nonneg_left ht.1 hD.le)

end BlockBand.Transmission.LawDuality
