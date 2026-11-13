module

public import BlockBand.Transmission.Dual.GGlueMart

/-!
# The gluing step `DelFrom D₀ k → DelFrom D₀ (k+1)` and the dual boundary lemma

* **`delFrom_succ`**: for `D₀ > 0`, `DelFrom D₀ k → DelFrom D₀ (k+1)`. The first stage is a
  random-start family `F : B1R` on `ΩR S (k+1)` (`nonempty_b1R`); `DelFrom k` is applied to
  `(ΩR S (k+1), PR μ (k+1), F.surv)`; the glued process on the restart space with the glued
  filtration is an `IsDualFrom` realization at level `k+1`, with `π = fst ∘ π'`.
* **`dualBoundaryLaw_holds : DualBoundaryLawStatement`** (`dualBoundaryLaw_of_delStep`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- **The gluing step**: a random-start deletion process at level `k` gives one at level
`k + 1`. -/
theorem delFrom_succ {D0 : ℝ} (hD0 : 0 < D0) (k : ℕ) (hk : DelFrom D0 k) :
    DelFrom D0 (k + 1) := by
  intro S _ μ hμ ξ hξ hξc
  obtain ⟨F⟩ := nonempty_b1R (μ := μ) (q := k + 1) hD0 hξ
  obtain ⟨Ω, m, 𝓖, P, π', N', X', Y', hD', hmap, hcomap, h0⟩ :=
    hk (ΩR S (k + 1)) inferInstance (PR μ (k + 1)) inferInstance F.surv F.measurable_surv
      F.surv_mem
  have := hD'.prob
  have hπ := B1R.measurable_of_comap hcomap
  have hlev : ∀ t ω, N' t ω ≤ k := hD'.level_le
  refine ⟨Ω, m, F.gFilt hcomap hD0 hξ hξc, P, fun ω => (π' ω).1, F.gN π' N',
    F.gC π' N' F.sX X', F.gC π' N' F.sY Y',
    { prob := hD'.prob
      adapted := F.adapted_g hcomap hD0 hξ hξc hD'
      start := Eventually.of_forall (F.gN_zero π' N')
      bound := fun ω => (F.gN_zero π' N' ω).le
      paths := fun ω => F.isDeletionPath_g hξc (hD'.paths ω) (h0 ω)
      martingale := fun q hq hqk f hf hfc hfs => ?_ }, ?_, ?_,
    fun ω => ⟨F.gN_zero π' N' ω, F.dualCoordOf_g_zero π' N' X' Y' hξc ω⟩⟩
  · rcases Nat.lt_or_ge q (k + 1) with h | h
    · exact F.martingale_g_low hcomap hD0 hξ hξc hD' h0 hq (by omega) hf hfc hfs
    · obtain rfl : q = k + 1 := le_antisymm hqk h
      exact F.martingale_g_top hcomap hD0 hξ hξc hmap hlev hf hfc hfs
  · rw [show (fun ω => (π' ω).1) = Prod.fst ∘ π' from rfl, ← Measure.map_map measurable_fst hπ,
      hmap]
    show (μ.prod _).map Prod.fst = μ
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  · have h1 : Measurable[comapFilt hπ (𝓖R μ (k + 1)) 0] fun ω => (π' ω).1 :=
      (measurable_fst_zero μ (q := k + 1) measurable_id).comp (comap_measurable π')
    exact (h1.mono (le_glueFilt _ _ _ 0) le_rfl).comap_le

/-- **The law clauses of the dual boundary lemma** (`DualBoundaryLawStatement`). -/
theorem dualBoundaryLaw_holds : DualBoundaryLawStatement :=
  dualBoundaryLaw_of_delStep fun _ hD0 k hk => delFrom_succ hD0 k hk

end BlockBand.Transmission.Dual.G
