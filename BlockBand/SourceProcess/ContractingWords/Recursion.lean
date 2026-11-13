module

public import BlockBand.SourceProcess.ContractingWords.Interface
public import BlockBand.SourceProcess.ContractingWords.Alive
public import BlockBand.SourceProcess.ContractingWords.Moments

/-!
# The field `recursion` from the one-step mean and fluctuation

* `doob_split`: for an `m`-measurable event `A` and an integrable `Z₁`, the centered part
  `ξ = Z₁ - E[Z₁|m]` has `E[1_Aξ | m] = 0`.
* `geometric_iterate`: `a_{j+1} ≤ ρa_j + c` from `a_{j₀} ≤ A₀` gives
  `a_j ≤ A₀ρ^{j-j₀} + c/(1-ρ)` (invariant form, in `ℝ≥0∞`).
* `norm_meanFactor_le`: `‖meanFactor b E s Zs‖ ≤ thetaBound b κI` for `E` in the bulk, a stationary jet `s` and
  `1 ≤ unconjCount Zs + conjCount Zs`.
* `recursion_of` (proved in the sibling module, with the lemmas above): the field `recursion` of `ContractingWordsEnergyUniformContract` from the
  hypotheses `WordStepMean`, `WordStepFluct` and the Gaussian inputs (load moments). `ξ_{j+1}` is
  the Doob centered part; the decay uses `A_{j+1} ⊆ A_j`, Minkowski, `|λ| ≤ |θ_*| ≤ ρ₀ < 1`
  (`thetaStar_bulk_bound`) and the initial bound `‖Z_{j₀}‖_p ≤ C₀` (`productValue_eLpNorm_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform2
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge
open scoped ENNReal ComplexConjugate

theorem doob_split {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} (hm : m ≤ m₀)
    [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet[m] A) {Z₁ : Ω → ℂ}
    (hZ : Integrable Z₁ μ) :
    Integrable (A.indicator fun ω => Z₁ ω - μ[Z₁ | m] ω) μ ∧
      μ[A.indicator (fun ω => Z₁ ω - μ[Z₁ | m] ω) | m] =ᵐ[μ] 0 := by
  have hξ : Integrable (fun ω => Z₁ ω - μ[Z₁ | m] ω) μ := hZ.sub integrable_condExp
  refine ⟨hξ.indicator (hm _ hA), ?_⟩
  have h1 := condExp_indicator (m := m) hξ hA
  have h2 : μ[(fun ω => Z₁ ω - μ[Z₁ | m] ω) | m] =ᵐ[μ] 0 := by
    have h3 := condExp_sub (m := m) hZ (integrable_condExp (m := m) (f := Z₁) (μ := μ))
    rw [condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp integrable_condExp] at h3
    refine (Filter.EventuallyEq.trans ?_ h3).trans ?_
    · rfl
    · exact Filter.Eventually.of_forall fun ω => by simp
  refine h1.trans ?_
  filter_upwards [h2] with ω hω
  by_cases h : ω ∈ A
  · simp [Set.indicator_of_mem h, hω]
  · simp [Set.indicator_of_notMem h]

theorem geometric_iterate {a : ℕ → ℝ≥0∞} {ρ c A₀ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 ≤ c)
    (hA : 0 ≤ A₀) {j₀ N : ℕ} (h0 : a j₀ ≤ ENNReal.ofReal A₀)
    (hstep : ∀ i, j₀ ≤ i → i < N → a (i + 1) ≤ ENNReal.ofReal ρ * a i + ENNReal.ofReal c) :
    ∀ n, j₀ + n ≤ N → a (j₀ + n) ≤ ENNReal.ofReal (A₀ * ρ ^ n + c / (1 - ρ)) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have hcρ : 0 ≤ c / (1 - ρ) := div_nonneg hc h1ρ.le
  intro n
  induction n with
  | zero =>
    intro _
    exact h0.trans (ENNReal.ofReal_le_ofReal (by simp; positivity))
  | succ n ih =>
    intro hn
    have ih' := ih (by omega)
    refine (hstep (j₀ + n) (by omega) (by omega)).trans ?_
    calc ENNReal.ofReal ρ * a (j₀ + n) + ENNReal.ofReal c
        ≤ ENNReal.ofReal ρ * ENNReal.ofReal (A₀ * ρ ^ n + c / (1 - ρ)) + ENNReal.ofReal c := by
          gcongr
      _ = ENNReal.ofReal (A₀ * ρ ^ (n + 1) + c / (1 - ρ)) := by
          rw [← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_add (by positivity) hc]
          congr 1
          field_simp
          ring

theorem norm_meanFactor_le {b κI E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κI)
    (hE : E ∈ bulkInterval κI) {s : ℂ} (hs : IsStationaryJet b E s) {nT nI : ℕ}
    (Zs : List (TraceWord nT nI)) (hr : 1 ≤ unconjCount Zs + conjCount Zs) :
    ‖meanFactor b E s Zs‖ ≤ thetaBound b κI := by
  obtain ⟨-, hρ1, hθ⟩ := thetaStar_bulk_bound hb0 hb hκ
  have ht := hθ E hE s hs
  have ht1 : ‖thetaStar b E s‖ ≤ 1 := ht.trans hρ1.le
  rw [meanFactor, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add]
  obtain ⟨r, hr'⟩ : ∃ r, unconjCount Zs + conjCount Zs = r + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (by omega)).symm⟩
  rw [hr', pow_succ]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ht1)).trans ht

end BlockBand.SourceProcess.ContractingWords
