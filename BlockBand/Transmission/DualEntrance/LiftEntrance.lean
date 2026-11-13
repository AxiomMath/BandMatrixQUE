module

public import BlockBand.Transmission.DualEntrance.LiftFaces
public import BlockBand.Transmission.DualLift.LAssembly

/-!
# Instantaneous entrance and no return for the lift; the contract field `exists_`

Measure and domain: the driver space `LΩ S = DriverSample S (Fin 5)` with the law
`LP μ` (any `S : Type`, any probability `μ` on `S`) and the augmented filtration `L𝓖 μ`;
`D₀ > 0`; any admissible random start `ξ` (`IsLiftStart`: augmented-`𝓕₀`-measurable, values in
`liftM`) and any `LiftFamily μ D₀ ξ`. No other hypothesis.

* **`liftEntrance_holds : 0 < D₀ → LiftEntrance D₀`**. Proof: for every `n`, `k`, `m` and face
  `i` (`x`, `y`, `1 − y`), `ae_pos` of `isEntranceFace` (with `ε = 1/(k+1)`) gives a.s.
  positivity of the face on `(0, stopT]`. On the good set the flat path `Yf n` equals `Zp n` and
  stays in `flatK R`, `R = max(max(n, ‖ξ‖), 1)`, so `x + y ≥ 1/R` and `x ≤ 2R²` for all times.
  With `1/(k+1) < 1/R` and `m > 2R²` this gives `stopT = e_n` up to every `t ≤ e_n`.
* **`dualBoundaryStart_exists`**: the field `DualBoundaryStartContract.exists_`, with no
  hypothesis (via `DualLift.exists_of_entrance`).
* **`liftBoundaryDual_holds`**, **`liftDualDeletionInterior_holds`**: the boundary and interior
  realization statements `LiftBoundaryDual`, `LiftDualDeletionInterior` for every `D₀ > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualEntrance

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionUniform BlockBand.SourceProcess.Stochastic
  BlockBand.Transmission.Dual BlockBand.Transmission.DualLift
open scoped NNReal

theorem mem_flatChamber_one {z : Fin 2 → ℝ} (h0 : 0 < z 0) (h1 : 0 < z 1) (h2 : z 1 < 1) :
    z ∈ flatChamber 1 := by
  have h := Exists.flat_mem_of_ratio (x := ![z 0]) (y := ![z 1])
    ⟨Subsingleton.strictMono _, Subsingleton.strictMono _, fun i => by
      rw [Fin.fin_one_eq_zero i]; exact h0, fun i => by
      rw [Fin.fin_one_eq_zero i]; exact ⟨h1, h2⟩⟩
  have e : z = ![z 0, z 1] := by
    funext j; fin_cases j <;> rfl
  rw [e]; exact h

/-- **Instantaneous entrance and no return for the lift**. -/
theorem liftEntrance_holds {D0 : ℝ} (hD0 : 0 < D0) : LiftEntrance D0 := by
  intro S _ μ _ ξ hξ F
  have hpos : ∀ᵐ ω ∂LP μ, ∀ n k m : ℕ, ∀ i : Fin 3, ∀ t : ℝ≥0, 0 < t →
      (t : WithTop ℝ≥0) ≤ stopT F n (1 / ((k : ℝ) + 1)) m ω →
        0 < faceZ F n (1 / ((k : ℝ) + 1)) m i t ω 0 := by
    simp only [ae_all_iff]
    intro n k m i
    exact (isEntranceFace F hD0 hξ n (by positivity) (Nat.cast_nonneg m) i).ae_pos
  have hG : ∀ᵐ ω ∂LP μ, ω ∈ F.good := by
    rw [ae_iff]; exact F.measure_good_compl hD0 hξ
  filter_upwards [hpos, hG] with ω hω hg n t ht hte
  set R : ℝ := max (max (n : ℝ) ‖ξ ω‖) 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hK : ∀ u, F.Yf n u ω ∈ flatK R := fun u => F.Yf_mem_flatK hξ n u ω
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 1 / R by positivity)
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * R * R)
  have hτ : (t : WithTop ℝ≥0) ≤ stopT F n (1 / ((k : ℝ) + 1)) m ω := by
    refine le_min hte (le_iInf₂ fun u hu => ?_)
    exfalso
    have h := hK u
    have h1 : 0 < F.Yf n u ω 0 + F.Yf n u ω 1 - 1 / ((k : ℝ) + 1) := by linarith [h.1]
    have h2 : 0 < (m : ℝ) - F.Yf n u ω 0 := by linarith [h.2.2.1]
    exact absurd hu (not_le.2 (lt_min h1 h2))
  have hz : ∀ i, 0 < faceR i 0 * F.Yf n t ω 0 + faceR i 1 * F.Yf n t ω 1 + faceC i := fun i =>
    (faceZ_eq F i hτ) ▸ hω n k m i t ht hτ
  have e := F.Yf_of_good hg n t
  rw [← e]
  have hx := hz 0
  have hy := hz 1
  have hw := hz 2
  simp [faceR, faceC] at hx hy hw
  exact mem_flatChamber_one hx hy (by linarith)

/-- **The field `DualBoundaryStartContract.exists_`**, unconditionally. -/
theorem dualBoundaryStart_exists :
    ∀ D0 : ℝ, 0 < D0 → ∀ x y : ℝ, IsDualStart ![x] ![y] → HasBoundaryDualProcess D0 ![x] ![y] :=
  exists_of_entrance fun _ hD0 => liftEntrance_holds hD0

/-- Boundary-start realizations on the driver space `LΩ S`, for every `D₀ > 0`. -/
theorem liftBoundaryDual_holds {D0 : ℝ} (hD0 : 0 < D0) : LiftBoundaryDual D0 :=
  liftBoundaryDual_of_entrance hD0 (liftEntrance_holds hD0)

/-- Interior-start realizations are `IsDualDeletionProcess`es, for every `D₀ > 0`. -/
theorem liftDualDeletionInterior_holds {D0 : ℝ} (hD0 : 0 < D0) : LiftDualDeletionInterior D0 :=
  liftDualDeletionInterior_of_entrance hD0 (liftEntrance_holds hD0)

end BlockBand.Transmission.DualEntrance
