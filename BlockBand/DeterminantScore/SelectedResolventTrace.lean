module

public import BlockBand.DeterminantScore.SelectedResolventCertificate

/-!
# The trace estimates at the selected energies

`SelectedTraceStatement` splits into two named statements, each in the event format of
`SelectedResolventStatement`.

* **`SelectedLocalLawStatement`** (the averaged local law
  `‖Tr R_η - d m_E(iη)‖_{L^p} ≤ C W^ε/η`, transferred to the selected energies on the energy
  and rank-one grids of the physical local window):
  `|Tr R_η - d m_E(iη)| ≤ C W^ε/η`.
* **`SelectedIBPStatement`** (Gaussian integration by parts
  `E_G Tr G_dR_η = -t E_G (Tr R_η)²`, Gaussian `L^p` Poincaré, the grids and the infinite-parameter
  compression): `|Tr G_dR_η + s d m_E(iη)²| ≤ C W^{9/10+ε}`.

* `selectedTrace_of_parts`: the two give `SelectedTraceStatement` (union of the events).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedResolvent

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.LocalWindow
open scoped ENNReal

/-- **The averaged local law at the selected energies**: `b, T, ϑ`
first, then for `ε, D > 0` a constant `C`; uniformly in `4 ≤ n ≤ TW`, models, pairs and splitting
laws an event `Ω` of every pair-law probability `≤ C W^{-D}` outside which, at every `ϑ`-bulk
selected energy `E = λ_α`, `|Tr R_η - d m_E(iη)| ≤ C W^ε/η` (`d = 2W`, `η = W^{-3/5}`,
`R_η = (A(E) - iη)⁻¹`, `m_E = pairDyson K₀(E) s`). -/
def SelectedLocalLawStatement : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
      ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D →
        ∃ C : ℝ, ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
          ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
            IsPairSplitting p i model (splitS p) Pω →
              ∃ Ω : Set (SplitState p i × PairMatrix p i),
                (∀ α : Fin p.N, splitPairLaw p i α Pω Ω ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
                ∀ x ∉ Ω, ∀ α : Fin p.N, IsBulkRank p ϑ α →
                  let E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α
                  let K := schurK0 p i x.1 E
                  let s := splitS p
                  let η := (p.W : ℝ) ^ (-(3 / 5 : ℝ))
                  let Rη := (schurA p i x.1 x.2 E - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i))⁻¹
                  ‖Rη.trace - ((2 * p.W : ℝ) : ℂ) * pairDyson p i K s ((η : ℂ) * Complex.I)‖ ≤
                    C * (p.W : ℝ) ^ ε / η

/-- **The Gaussian integration-by-parts estimate at the selected energies**, in the same format: `|Tr G_dR_η + s d m_E(iη)²| ≤ C W^{9/10+ε}`. -/
def SelectedIBPStatement : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
      ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D →
        ∃ C : ℝ, ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
          ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
            IsPairSplitting p i model (splitS p) Pω →
              ∃ Ω : Set (SplitState p i × PairMatrix p i),
                (∀ α : Fin p.N, splitPairLaw p i α Pω Ω ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
                ∀ x ∉ Ω, ∀ α : Fin p.N, IsBulkRank p ϑ α →
                  let E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α
                  let K := schurK0 p i x.1 E
                  let s := splitS p
                  let η := (p.W : ℝ) ^ (-(3 / 5 : ℝ))
                  let Rη := (schurA p i x.1 x.2 E - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i))⁻¹
                  ‖(x.2 * Rη).trace + (s : ℂ) * ((2 * p.W : ℝ) : ℂ) *
                      pairDyson p i K s ((η : ℂ) * Complex.I) ^ 2‖ ≤
                    C * (p.W : ℝ) ^ (9 / 10 + ε)

/-- **`SelectedTraceStatement` from the local law and the integration-by-parts estimate** (union
of the exceptional events). -/
theorem selectedTrace_of_parts (h3 : SelectedLocalLawStatement) (h4 : SelectedIBPStatement) :
    SelectedTraceStatement := by
  intro b T ϑ hϑ ε hε D hD
  obtain ⟨C3, hC3⟩ := h3 b T ϑ hϑ ε hε D hD
  obtain ⟨C4, hC4⟩ := h4 b T ϑ hϑ ε hε D hD
  refine ⟨|C3| + |C4|, fun p hpb hn model i Pω hsplit => ?_⟩
  obtain ⟨Ω3, hΩ3, hg3⟩ := hC3 p hpb hn model i Pω hsplit
  obtain ⟨Ω4, hΩ4, hg4⟩ := hC4 p hpb hn model i Pω hsplit
  have hW0 : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hneg : 0 ≤ (p.W : ℝ) ^ (-D) := (Real.rpow_pos_of_pos hW0 _).le
  refine ⟨Ω3 ∪ Ω4, fun α => ?_, fun x hx α hα => ?_⟩
  · refine (measure_union_le _ _).trans ?_
    calc splitPairLaw p i α Pω Ω3 + splitPairLaw p i α Pω Ω4
        ≤ ENNReal.ofReal (|C3| * (p.W : ℝ) ^ (-D)) + ENNReal.ofReal (|C4| * (p.W : ℝ) ^ (-D)) :=
          add_le_add ((hΩ3 α).trans (ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_abs_self _) hneg)))
            ((hΩ4 α).trans (ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_abs_self _) hneg)))
      _ = ENNReal.ofReal ((|C3| + |C4|) * (p.W : ℝ) ^ (-D)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  have h3' := hg3 x (fun h => hx (Or.inl h)) α hα
  have h4' := hg4 x (fun h => hx (Or.inr h)) α hα
  dsimp only at h3' h4' ⊢
  have hη : 0 ≤ (p.W : ℝ) ^ ε / (p.W : ℝ) ^ (-(3 / 5 : ℝ)) := by positivity
  have hp : 0 ≤ (p.W : ℝ) ^ (9 / 10 + ε) := (Real.rpow_pos_of_pos hW0 _).le
  refine ⟨h3'.trans ?_, h4'.trans ?_⟩
  · rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right ((le_abs_self C3).trans (by linarith [abs_nonneg C4])) hη
  · exact mul_le_mul_of_nonneg_right ((le_abs_self C4).trans (by linarith [abs_nonneg C3])) hp

/-- **`SelectedResolventStatement`** from `MatchedTracesContract`, `PhysicalBlockConditionalCount`,
`CoareaContract`, `RankLocationContract`, the local law `SelectedLocalLawStatement` and the
integration-by-parts estimate `SelectedIBPStatement`. -/
theorem selectedResolvent_of_localLaw_ibp (hMT : MatchedTracesContract)
    (hPBC : PhysicalBlockConditionalCount) (hCo : CoareaContract)
    (hRank : RankLocationContract) (h3 : SelectedLocalLawStatement) (h4 : SelectedIBPStatement) :
    WeightedTrace.SelectedResolventStatement :=
  selectedResolvent_of_trace hMT hPBC hCo hRank (selectedTrace_of_parts h3 h4)

end BlockBand.DeterminantScore.SelectedResolvent
