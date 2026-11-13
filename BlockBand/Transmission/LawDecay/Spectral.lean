module

public import BlockBand.Transmission.Generator.Basic

/-!
# Eigenvalue constraints on the power sums along the path

The generator inequality (`LawDecay.Gen.lyapGen_le`) uses two facts about `P_k = Σ tᵢ^k`,
`tᵢ ≥ 0` (: `0 ≤ r₂ ≤ 1`, `r₃ ≤ r₂^{3/2}`):
* `P₂ ≤ P₁²` (`ℓ² ≤ ℓ¹`);
* `P₃ ≤ √P₂·P₂` (`ℓ³ ≤ ℓ²`, from `tᵢ ≤ √P₂`).

`ae_spectral`: almost surely, at every length `r` of the unabsorbed path, with
`P_k = Re Tr T_r^k` (`pathPower`). The eigenvalues are nonnegative because `T_r ⪰ 0`
(`Bridge.pathTransmission_posSemidef`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Generator

/-- `Σtᵢ² ≤ (Σtᵢ)²` and `Σtᵢ³ ≤ √(Σtᵢ²)·Σtᵢ²` for `tᵢ ≥ 0`. -/
theorem sums_facts {n : Type*} [Fintype n] (t : n → ℝ) (h0 : ∀ i, 0 ≤ t i) :
    ∑ i, t i ^ 2 ≤ (∑ i, t i ^ 1) ^ 2 ∧
      ∑ i, t i ^ 3 ≤ Real.sqrt (∑ i, t i ^ 2) * ∑ i, t i ^ 2 := by
  constructor
  · have hle : ∀ i, t i ≤ ∑ j, t j ^ 1 := fun i => by
      simpa using Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
    calc ∑ i, t i ^ 2 ≤ ∑ i, t i * ∑ j, t j ^ 1 :=
          Finset.sum_le_sum fun i _ => by rw [sq]; exact mul_le_mul_of_nonneg_left (hle i) (h0 i)
      _ = (∑ i, t i ^ 1) ^ 2 := by rw [← Finset.sum_mul, sq]; simp
  · have hle : ∀ i, t i ≤ Real.sqrt (∑ j, t j ^ 2) := fun i => by
      rw [Real.le_sqrt (h0 i) (Finset.sum_nonneg fun j _ => sq_nonneg _)]
      exact Finset.single_le_sum (f := fun j => t j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    calc ∑ i, t i ^ 3 ≤ ∑ i, Real.sqrt (∑ j, t j ^ 2) * t i ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            rw [show t i ^ 3 = t i * t i ^ 2 by ring]
            exact mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]

variable {W : ℕ}

/-- **Almost surely** `P₂ ≤ P₁²` and `P₃ ≤ √P₂·P₂` at every length. -/
theorem ae_spectral {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ r : ℕ,
      pathPower b E W 2 r ω ≤ pathPower b E W 1 r ω ^ 2 ∧
        pathPower b E W 3 r ω ≤ Real.sqrt (pathPower b E W 2 r ω) * pathPower b E W 2 r ω := by
  filter_upwards [Bridge.ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb h1 h2]
    with ω hω
  intro r
  have h0 := Bridge.pathTransmission_posSemidef hω r
  simp only [pathPower]
  rw [trace_pow_re_eq h0.1 1, trace_pow_re_eq h0.1 2, trace_pow_re_eq h0.1 3]
  exact sums_facts _ h0.eigenvalues_nonneg

end BlockBand.Transmission.LawDecay
