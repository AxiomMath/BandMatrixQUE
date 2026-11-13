module

public import BlockBand.Transmission.LawFinite.EntranceDrift

/-!
# Entrance bookkeeping: `g = 4ηq`, telescoping, the first reciprocal

* `conductance_eq` (`g = 4ηq`), `entranceEvent_subset` (`{min g_r ≤ K} ⊆ {∃ r ≤ ⌊tW⌋, q_r < K'}`
  for `K < 4ηK'`);
* `telescope`: summing `cP_j + Φ_{j+1} ≤ Φ_j + e + D_j` in `ℝ≥0∞`;
* `lintegral_recipK_le`: `E r_K(q₁) ≤ K⁻¹P(q₁ < aW) + (aW)⁻¹`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- `g = 4ηq`. -/
theorem conductance_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    conductanceOf (passiveTransmission b E X) = 4 * etaZ b E * passiveMass b E X := by
  rw [conductanceOf, passiveTransmission, trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    passiveMass]

/-- The entrance event lies in `{∃ r ≤ ⌊tW⌋, q_r < K'}` once `K < 4ηK'`. -/
theorem entranceEvent_subset {b E : ℝ} {κ : ℝ → ℝ} {K t K' : ℝ} (hη : 0 < etaZ b E)
    (hK : K < 4 * etaZ b E * K') :
    entranceEvent b E κ K t W ⊆ {ω | ∃ r, 1 ≤ r ∧ r ≤ ⌊t * W⌋₊ ∧
      passiveMass b E (pathNearSchur b E κ W r ω) < K'} := by
  rintro ω ⟨r, hr1, hrt, hg⟩
  refine ⟨r, hr1, Nat.le_floor hrt, ?_⟩
  rw [pathTransmission, conductance_eq] at hg
  by_contra h; push Not at h
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4 * etaZ b E)
  linarith

/-- **Telescoping** (abstract, `ℝ≥0∞`): `cP_j + Φ_{j+1} ≤ Φ_j + e + D_j` for `j ≥ 1` gives
`c Σ_{1 ≤ j < N} P_j ≤ Φ₁ + Σ_{1 ≤ j < N} (e + D_j)`. -/
theorem telescope {Φ P D : ℕ → ℝ≥0∞} {c e : ℝ≥0∞}
    (h : ∀ j, 1 ≤ j → c * P j + Φ (j + 1) ≤ Φ j + e + D j) (N : ℕ) :
    c * ∑ j ∈ Finset.Ico 1 N, P j ≤ Φ 1 + ∑ j ∈ Finset.Ico 1 N, (e + D j) := by
  suffices H : ∀ n, c * ∑ j ∈ Finset.Ico 1 (n + 1), P j + Φ (n + 1) ≤
      Φ 1 + ∑ j ∈ Finset.Ico 1 (n + 1), (e + D j) by
    rcases N with _ | n
    · simp
    · exact le_trans le_self_add (H n)
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (a := 1) (b := n + 1) (by omega),
      Finset.sum_Ico_succ_top (a := 1) (b := n + 1) (by omega), mul_add]
    have hs := h (n + 1) (by omega)
    calc c * ∑ j ∈ Finset.Ico 1 (n + 1), P j + c * P (n + 1) + Φ (n + 1 + 1)
        = (c * ∑ j ∈ Finset.Ico 1 (n + 1), P j) + (c * P (n + 1) + Φ (n + 1 + 1)) := by
          rw [add_assoc]
      _ ≤ (c * ∑ j ∈ Finset.Ico 1 (n + 1), P j) + (Φ (n + 1) + e + D (n + 1)) := by gcongr
      _ = (c * ∑ j ∈ Finset.Ico 1 (n + 1), P j + Φ (n + 1)) + (e + D (n + 1)) := by
          simp only [add_assoc]
      _ ≤ Φ 1 + ∑ j ∈ Finset.Ico 1 (n + 1), (e + D j) + (e + D (n + 1)) := by gcongr
      _ = _ := by rw [add_assoc]

/-- `E r_K(q₁) ≤ K⁻¹P(q₁ < aW) + (aW)⁻¹`. -/
theorem lintegral_recipK_le {b E : ℝ} {κ : ℝ → ℝ} {K a : ℝ} (haW : 0 < a * W) :
    ∫⁻ ω, ENNReal.ofReal (recipK K (passiveMass b E (pathNearSchur b E κ W 1 ω)))
        ∂growthPathLaw W b ≤
      ENNReal.ofReal K⁻¹ * growthPathLaw W b
          {ω | passiveMass b E (pathNearSchur b E κ W 1 ω) < a * W} +
        ENNReal.ofReal (a * W)⁻¹ := by
  have hq : Measurable fun ω => passiveMass b E (pathNearSchur b E κ W 1 ω) :=
    (SourceMixing.measurable_passiveMass b E).comp ((pathNearSchur_adapted b E κ W 1).mono
      (Generator.growthSigma_le W 1) le_rfl)
  have hS : MeasurableSet {ω | passiveMass b E (pathNearSchur b E κ W 1 ω) < a * W} :=
    measurableSet_lt hq measurable_const
  calc ∫⁻ ω, ENNReal.ofReal (recipK K (passiveMass b E (pathNearSchur b E κ W 1 ω)))
        ∂growthPathLaw W b
      ≤ ∫⁻ ω, ({ω | passiveMass b E (pathNearSchur b E κ W 1 ω) < a * W}.indicator
          (fun _ => ENNReal.ofReal K⁻¹) ω + ENNReal.ofReal (a * W)⁻¹) ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        by_cases h : passiveMass b E (pathNearSchur b E κ W 1 ω) < a * W
        · rw [Set.indicator_of_mem (s := {ω | passiveMass b E (pathNearSchur b E κ W 1 ω) < a * W})
            h]
          exact le_add_right (ENNReal.ofReal_le_ofReal recipK_le)
        · rw [Set.indicator_of_notMem (s := {ω | passiveMass b E (pathNearSchur b E κ W 1 ω) <
            a * W}) h, zero_add]
          refine ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans ?_)
          exact inv_anti₀ haW (not_lt.mp h)
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_indicator_const hS, lintegral_const,
          measure_univ, mul_one]

end BlockBand.Transmission.LawFinite
