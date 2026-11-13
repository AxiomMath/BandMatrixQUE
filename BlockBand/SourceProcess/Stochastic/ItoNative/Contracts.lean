module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Itô and stopping contracts in every universe, and the zero-bracket lemma

The contracts (a1) `SemimartingaleItoFormula d` and (a2) `StoppedSemimartingale d` quantify over
sample spaces `Ω : Type`. The driver space `DriverSample S κ` lives in the universe of
`S` and `κ`, so we restate both conclusions for `Ω : Type*`; the proofs are the proofs of
`semimartingaleItoFormula_holds` and `stoppedSemimartingale_holds`, whose ingredients are
universe polymorphic.

* `isContinuousSemimartingale_ito`: the Itô formula, any universe, with `U = univ`.
* `isContinuousSemimartingale_stopped`: stopped semimartingales, any universe.
* `smCompensated_ae_eq_zero_of_bracket`: a one-dimensional continuous semimartingale whose
  covariance density vanishes identically has `Y_t − Y_0 − ∫_0^t β = 0` a.s. for every `t`
  (localize; `E[M²_{t∧τ_n}] = E[M²_0] = 0` by the bracket martingale clause; `τ_n → ⊤`).
-/

namespace BlockBand.SourceProcess.Stochastic.ItoNative
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {d : ℕ}

/-- **Contract (a1) in every universe** (open set `U = univ`): for a continuous
semimartingale `Y` with characteristics `(β, α)` and a measurable `C²` function
`φ : ℝ × ℝ^d → ℝ`, the process `φ(t, Y_t)` is a continuous semimartingale with drift
`itoDrift` and bracket density `itoBracket`. -/
theorem isContinuousSemimartingale_ito {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    {φ : ℝ × (Fin d → ℝ) → ℝ} (hφm : Measurable φ) (hφ' : ContDiff ℝ 2 φ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖 (fun t ω (_ : Fin 1) => φ ((t : ℝ), Y t ω))
      (fun t ω (_ : Fin 1) => itoDrift φ (Y t ω) t (β t ω) (α t ω))
      (fun t ω => Matrix.of fun (_ _ : Fin 1) => itoBracket φ (Y t ω) t (α t ω)) := by
  have hU : IsOpen (univ : Set (Fin d → ℝ)) := isOpen_univ
  have hYU : ∀ᵐ ω ∂Q, ∀ t, Y t ω ∈ (univ : Set (Fin d → ℝ)) :=
    ae_of_all _ fun _ _ => mem_univ _
  have hφ : ContDiffOn ℝ 2 φ (univ ×ˢ (univ : Set (Fin d → ℝ))) := hφ'.contDiffOn
  obtain ⟨σ, hσ, hσlim, hloc⟩ := exists_localizer H hU hYU hφm hφ
  have hconst : Continuous fun x : ℝ => (fun _ : Fin 1 => x) :=
    continuous_pi fun _ => continuous_id
  refine ⟨fun t => ?_, fun i => ?_, ?_, fun i => ?_, fun i => ?_, ?_, ⟨σ, hσ, hσlim, fun m => ?_⟩⟩
  · exact hconst.comp_stronglyMeasurable
      ((isStronglyProgressive_phi hφm H.progressive).stronglyAdapted t)
  · exact hconst.comp_stronglyMeasurable (isStronglyProgressive_phi hφm H.progressive i)
  · filter_upwards [H.continuous, hYU] with ω hω hU'
    exact hconst.comp (hφ.continuousOn.comp_continuous (NNReal.continuous_coe.prodMk hω)
      fun t => ⟨mem_univ _, hU' t⟩)
  · exact hconst.comp_stronglyMeasurable (isStronglyProgressive_driftPath φ H.progressive
      H.drift_progressive H.cov_progressive i)
  · exact (continuous_matrix fun _ _ => continuous_id).comp_stronglyMeasurable
      (isStronglyProgressive_bracketPath φ H.progressive H.cov_progressive i)
  · filter_upwards [H.continuous, hYU, H.integrable] with ω hω hU' hi t
    exact ⟨fun _ => integrableOn_itoDrift_path hU hφ hω hU' t (hi t).1 (hi t).2,
      fun _ _ => integrableOn_itoBracket_path hU hφ hω hU' t (hi t).2⟩
  · obtain ⟨⟨W, T, c, ys, D⟩, hN, hB⟩ := hloc m
    obtain ⟨h1, h2⟩ := D.ito_local hN hB
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      exact h1
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact h2

/-- **Contract (a2) in every universe**: a continuous semimartingale stopped at a stopping time
`ρ` is a continuous semimartingale with characteristics switched off after `ρ`. -/
theorem isContinuousSemimartingale_stopped {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓖 ρ) :
    IsContinuousSemimartingale Q 𝓖 (stoppedProcess Y ρ) (switchAfter ρ β) (switchAfter ρ α) := by
  obtain ⟨τ, hτ, hτlim, hmart⟩ := H.localizing
  refine ⟨fun t => H.progressive.stronglyAdapted_stoppedProcess hρ t,
    H.progressive.stoppedProcess hρ, ?_,
    isStronglyProgressive_switchAfter H.drift_progressive hρ,
    isStronglyProgressive_switchAfter H.cov_progressive hρ, ?_,
    ⟨τ, hτ, hτlim, fun n => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [H.continuous] with ω hω
    exact hω.comp (continuous_stopTime _)
  · filter_upwards [H.integrable] with ω hω t
    refine ⟨fun i => integrableOn_switchAfter_path ρ β (fun b : Fin d → ℝ => b i) rfl ω t
      ((hω t).1 i), fun i j => integrableOn_switchAfter_path ρ α
        (fun a : Matrix (Fin d) (Fin d) ℝ => a i j) rfl ω t ((hω t).2 i j)⟩
  · obtain ⟨M, hM, hMX⟩ := (hmart n).1 i
    have hc : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess (smCompensated Y β i) (τ n) t ω := by
      filter_upwards [H.continuous, H.integrable] with ω hω hi
      exact (continuous_smCompensated hω fun t => (hi t).1 i).comp (continuous_stopTime _)
    obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM hMX hc hρ
    refine ⟨M', hM', fun t => (hM'X t).trans (ae_of_all _ fun ω => ?_)⟩
    simp only [stoppedProcess_eq_stopTime, smCompensated_stopped]
    rw [stopTime_comm]
  · obtain ⟨M, hM, hMX⟩ := (hmart n).2 i j
    have hc : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess (fun t ω =>
        smCompensated Y β i t ω * smCompensated Y β j t ω -
          ∫ s in Set.Ioc (0 : ℝ) t, α s.toNNReal ω i j) (τ n) t ω := by
      filter_upwards [H.continuous, H.integrable] with ω hω hi
      exact (((continuous_smCompensated hω fun t => (hi t).1 i).mul
        (continuous_smCompensated hω fun t => (hi t).1 j)).sub
        (continuous_setIntegral_Ioc (g := fun u => α u ω i j) fun t => (hi t).2 i j)).comp
        (continuous_stopTime _)
    obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM hMX hc hρ
    refine ⟨M', hM', fun t => (hM'X t).trans (ae_of_all _ fun ω => ?_)⟩
    simp only [stoppedProcess_eq_stopTime, smCompensated_stopped, integral_switchAfter_α]
    rw [stopTime_comm]

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
/-- The compensated coordinate vanishes at time `0`. -/
theorem smCompensated_zero (Y β : ℝ≥0 → Ω → Fin d → ℝ) (i : Fin d) (ω : Ω) :
    smCompensated Y β i 0 ω = 0 := by
  simp [smCompensated]

/-- **Zero bracket ⇒ zero martingale part.** If a one-dimensional continuous semimartingale has
identically vanishing covariance density, then its compensated coordinate
`Y_t − Y_0 − ∫_0^t β` vanishes almost surely at every time `t`. -/
theorem smCompensated_ae_eq_zero_of_bracket {Y β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    (hα : ∀ t ω, α t ω 0 0 = 0) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, smCompensated Y β 0 t ω = 0 := by
  obtain ⟨τ, -, hτlim, hm⟩ := H.localizing
  set c := smCompensated Y β 0 with hc
  have key : ∀ n, ∀ᵐ ω ∂Q, stoppedProcess c (τ n) t ω = 0 := by
    intro n
    obtain ⟨M, hM, hMX⟩ := (hm n).2 0 0
    have hsq : ∀ s ω, stoppedProcess (fun t ω => smCompensated Y β 0 t ω *
        smCompensated Y β 0 t ω - ∫ s in Set.Ioc (0 : ℝ) t, α s.toNNReal ω 0 0) (τ n) s ω =
        (stoppedProcess c (τ n) s ω) ^ 2 := by
      intro s ω
      simp only [stoppedProcess, hα, integral_zero, sub_zero, hc]
      ring
    have h0 : M 0 =ᵐ[Q] 0 := by
      filter_upwards [hMX 0] with ω hω
      rw [hω, hsq]
      simp [stoppedProcess, hc, smCompensated_zero]
    have hint : ∫ ω, M t ω ∂Q = 0 := by
      have := hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
      rw [setIntegral_univ, setIntegral_univ] at this
      rw [← this, integral_congr_ae h0]
      simp
    have hMt : M t =ᵐ[Q] fun ω => (stoppedProcess c (τ n) t ω) ^ 2 := by
      filter_upwards [hMX t] with ω hω
      rw [hω, hsq]
    have hI : Integrable (fun ω => (stoppedProcess c (τ n) t ω) ^ 2) Q :=
      (hM.integrable t).congr hMt
    rw [integral_congr_ae hMt] at hint
    have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hI).1 hint
    filter_upwards [hz] with ω hω
    simpa using hω
  filter_upwards [ae_all_iff.2 key, hτlim] with ω hω hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds (WithTop.coe_lt_top t))).exists
  have := hω n
  rwa [stoppedProcess_eq_of_le hn.le] at this

end BlockBand.SourceProcess.Stochastic.ItoNative
