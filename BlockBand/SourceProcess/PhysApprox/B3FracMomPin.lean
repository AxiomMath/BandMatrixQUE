module

public import BlockBand.SourceProcess.PhysApprox.B3JetOrder
public import BlockBand.Transmission.FractionalBulk.Main
public import BlockBand.SourceProcess.ClosedReduce.Entrance

/-!
# The one-layer `q`-th power step of the fractional trace, and far = near

This file belongs to the fractional bounds for homogeneous transmission.
`P = Tr T^α` (`fracTrace α`), `g = Tr T`, `δ₀, δ₁` the scalar jets of a passive input `X`,
`stepFrac α b E X` the fresh-layer value of `P`.

* **`FracPowStep α q`**, stated as a hypothesis: the one-layer bound for the `q`-th power, at
  every passive `X`,
  `E P₊^q ≤ P^q - (c/W)P^{q+1} + AW^qδ₀^{q+1} + A/W + (A/W)g^{q+1}
    + BW^q((δ₀/d)^{2q} + (δ₁/d)^{2q} + (g/(γW))^{2q})`;
* **`fracPowStep_one`**: at `q = 1` this is `stepBound_bulk` (from the contract hypotheses
  `GaussianAbsorptionContract`, `GaussianLpGradient`, `GaussianPoincare`);
* **`ae_farFracTrace_eq`**: a.s. `farFracTrace = Tr T_near^α` at every length (equal
  characteristic polynomials, `ClosedReduce.ae_charpoly_near_eq_far`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.FracMom

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.FractionalBulk
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- **`FracPowStep α q`: the fresh-layer bound for `(Tr T^α)^q` at every passive input**
(fixed `b, E`). At `q = 1` it is `stepBound_bulk` (`fracPowStep_one`). -/
def FracPowStep (α : ℝ) (q : ℕ) : Prop :=
  ∀ b E : ℝ, 0 < b → b < 1 / 2 → -2 < E → E < 2 →
    ∃ (c A B d γ : ℝ) (W₀ : ℕ), 0 < c ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 < d ∧ 0 < γ ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        ∫ y, stepFrac α b E X y ^ q ∂freshLaw W b ≤
          fracTrace α (passiveTransmission b E X) ^ q -
            c / W * fracTrace α (passiveTransmission b E X) ^ (q + 1) +
          A * (W : ℝ) ^ q * jetDistance0 b E X ^ (q + 1) + A / W +
          A / W * conductanceOf (passiveTransmission b E X) ^ (q + 1) +
          B * (W : ℝ) ^ q * ((jetDistance0 b E X / d) ^ (2 * q) +
            (jetDistance1 b E s X / d) ^ (2 * q) +
            (conductanceOf (passiveTransmission b E X) / (γ * W)) ^ (2 * q))

theorem bulk_of_lt' {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < min (2 + E) (2 - E) ∧ E ∈ bulkInterval (min (2 + E) (2 - E)) :=
  ⟨lt_min (by linarith) (by linarith),
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩⟩

/-- **`FracPowStep α 1` is `stepBound_bulk`.** -/
theorem fracPowStep_one (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : FracPowStep α 1 := by
  intro b E hb0 hb hE1 hE2
  obtain ⟨hκ, hEκ⟩ := bulk_of_lt' hE1 hE2
  obtain ⟨c, A, B, d, γ, W₀, hc, hA, hB, hd, hγ, hS⟩ :=
    stepBound_bulk hGA hLp hP hα0 hα1 hb0 hb hκ
  refine ⟨c, A, B, d, γ, W₀, hc, hA, hB, hd, hγ, fun W hW s hs X hX => ?_⟩
  have h := hS W hW E hEκ s hs X hX
  simp only [pow_one, Nat.reduceAdd, Nat.reduceMul]
  exact h

/-- **Far = near**: a.s., at every length, `farFracTrace = Tr T_near^α`. -/
theorem ae_farFracTrace_eq {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (α : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ n : ℕ, Jet.farFracTrace b E α W n ω =
      fracTrace α (pathTransmission b E (fun _ => 0) W n ω) := by
  filter_upwards [ClosedReduce.ae_charpoly_near_eq_far hb hE1 hE2 hW] with ω hc n
  rw [fracTrace_congr' (hc n), SourcePins.fracTrace_eq_sum
    (Closing.isHermitian_farTransmission b E W n ω) α]
  rfl

end BlockBand.SourceProcess.PhysApprox.B3.FracMom
