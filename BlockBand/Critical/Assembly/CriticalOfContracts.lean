module

public import BlockBand.Internal.Contracts.CriticalEntire
public import BlockBand.Counting.SimpleSpectralLimitsTopology
public import BlockBand.Model.Construction.MarkedStateTopologyConsequences
public import BlockBand.Model.Construction.SpectralFiniteRealization

/-!
# The critical theorem from joint recovery and stationarity

The critical theorem (existence and uniqueness of the critical family of marked limit laws)
follows from `JointRecoveryContract` (the joint recovery theorem) and `CriticalStationarity`
(the stationarity proposition), together with the measurability of the spectral projection,
the existence of finite realizations and the uniqueness of weak limits.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Critical.Assembly

open Filter Topology MeasureTheory
open BlockBand.Internal.Contracts.CriticalEntire

/-- For every `τ > 0` there is an admissible critical sequence: `W_j = j + 1`,
`n_j = max 4 ⌈τ (j+1)⌉₊`. -/
theorem exists_criticalSequence (τ : ℝ) (hτ : 0 < τ) : Nonempty (CriticalSequence τ) := by
  refine ⟨{ n := fun j => max 4 ⌈τ * ((j : ℝ) + 1)⌉₊
            W := fun j => j + 1
            n_ge_four := fun j => le_max_left _ _
            W_pos := fun j => Nat.succ_pos j
            width_tendsto := tendsto_add_atTop_nat 1
            ratio_tendsto := ?_ }⟩
  -- Eventually `τ(j+1) ≥ 4`, so `n_j = ⌈τ(j+1)⌉₊ ∈ [τ(j+1), τ(j+1)+1)`.
  have hW : Tendsto (fun j : ℕ => ((j : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hlow : ∀ᶠ j : ℕ in atTop, τ ≤ ((max 4 ⌈τ * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ)) := by
    refine Eventually.of_forall fun j => ?_
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    rw [le_div_iff₀ hpos]
    calc τ * ((j + 1 : ℕ) : ℝ) = τ * ((j : ℝ) + 1) := by push_cast; ring
      _ ≤ (⌈τ * ((j : ℝ) + 1)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ ((max 4 ⌈τ * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have hup : ∀ᶠ j : ℕ in atTop, ((max 4 ⌈τ * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ)) ≤
      τ + 1 / ((j : ℝ) + 1) := by
    have h4 : ∀ᶠ j : ℕ in atTop, (4 : ℝ) ≤ τ * ((j : ℝ) + 1) :=
      (hW.const_mul_atTop hτ).eventually_ge_atTop 4
    filter_upwards [h4] with j hj
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hmax : ((max 4 ⌈τ * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) ≤ τ * ((j : ℝ) + 1) + 1 := by
      have hc : ((⌈τ * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) < τ * ((j : ℝ) + 1) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have h4c : (4 : ℝ) ≤ ((⌈τ * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) := hj.trans (Nat.le_ceil _)
      rcases le_total 4 ⌈τ * ((j : ℝ) + 1)⌉₊ with h | h
      · rw [max_eq_right h]; exact hc.le
      · rw [max_eq_left h]; push_cast; linarith
    rw [show (((j + 1 : ℕ) : ℝ)) = (j : ℝ) + 1 by push_cast; ring, div_le_iff₀ hpos]
    calc ((max 4 ⌈τ * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) ≤ τ * ((j : ℝ) + 1) + 1 := hmax
      _ = (τ + 1 / ((j : ℝ) + 1)) * ((j : ℝ) + 1) := by field_simp
  have hlim : Tendsto (fun j : ℕ => τ + 1 / ((j : ℝ) + 1)) atTop (𝓝 τ) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hlow hup

/-- The critical theorem, conditional on joint recovery and stationarity. -/
theorem critical_of_contracts (hJR : JointRecoveryContract)
    (hS : BlockBand.Internal.Contracts.Inputs.CriticalStationarity)
    (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) :
    ∃! family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family := by
  have := BlockBand.Model.Construction.markedPointMeasureLaw_t2Space
  have hE2 : E ^ 2 < 4 := by nlinarith [hE.1, hE.2]
  have hreal : ∀ (τ : PositiveRatio) (s : CriticalSequence τ.1),
      Nonempty (∀ j, FiniteRealization (s.parameters b hb hb' j)) := fun τ s =>
    ⟨fun j => (BlockBand.Model.Construction.nonempty_finiteRealization _).some⟩
  obtain ⟨family, hfam, -⟩ := hJR b E hb hb' hE
  have hstat : ∀ τ : PositiveRatio, IsSpectrallyStationary (family τ) ∧
      IsMarkRotationInvariant (family τ) ∧ HasUniformSpatialIntensity (family τ) := by
    intro τ
    obtain ⟨s⟩ := exists_criticalSequence τ.1 τ.2
    obtain ⟨R⟩ := hreal τ s
    exact hS τ.1 s τ.2 b E hb hb' hE2 R id strictMono_id (family τ) (hfam.convergence τ s R)
  refine ⟨family, ⟨BlockBand.Counting.continuous_markedSpectralProjection.measurable, hreal,
    hfam.convergence, hfam.simple, hfam.unitIntensity, fun τ => (hstat τ).2.2,
    fun τ => (hstat τ).1, fun τ => (hstat τ).2.1⟩, ?_⟩
  intro family' hfam'
  funext τ
  obtain ⟨s⟩ := exists_criticalSequence τ.1 τ.2
  obtain ⟨R⟩ := hreal τ s
  exact tendsto_nhds_unique (hfam'.2.2.1 τ s R) (hfam.convergence τ s R)

end BlockBand.Critical.Assembly
