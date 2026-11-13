module

public import BlockBand.SourceProcess.ClosedFeas.BaseSplit
public import BlockBand.SourceProcess.ClosedReduce.Entrance
public import BlockBand.SourceProcess.Closing.PhaseAvg
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AmbientFeasible

/-!
# The closed Gram process is exactly feasible at finite `W`

**Exact feasibility holds.** Almost surely, on the cap event, for every admissible
time-`s` frame `Vs` (`IsTimeSFrame`), every sample, every phase and every length `j ≥ n_s`:
* **`ae_twoProjection_closedFrameAt`**: `TwoProjection P 𝖣 (C_j(z)ᴴ X_j)`;
* **`ae_gramFeasible_closedGramAt`**: `GramFeasible 𝖣 (closedGramAt … j Vs y)`.

Proof: (1) `base_split` at `n_s`: `Vs𝖣Vsᴴ = splitCurrent` (the cap makes the frame carry the
whole retained transmission mass, `sum_retW_cap`); (2) `ae_openCur_split`: the unclosed transport
conserves `splitCurrent`; (3) `twoProjection_closed` at length `j`: closing with `|z| = 1` turns it
into `C_jᴴ𝕊_jᴴP𝕊_jC_j - P`, a projection of rank `W`. Probe columns have signature `0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedFeas

open MeasureTheory Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ClosedReduce BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.CapLimit BlockBand.Transmission.Bridge

variable {W : ℕ} {b E s h : ℝ} {K : ℕ}

theorem retW_eq_zero {t : ℝ} (ht : t ≤ h ^ 2) : retW h t = 0 := by
  simp [retW, not_lt.2 ht]

/-- **Under the cap the first `K` sorted eigenvalues carry the whole retained mass.** -/
theorem sum_retW_cap (ω : GrowthPath W) (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2) :
    ∑ i, retW h ((isHermitian_farTransmission b E W (closeLen s W) ω).eigenvalues i) =
      ∑ k : Fin K, retW h (physTseq b E s W ω k.val) := by
  set hT := isHermitian_farTransmission b E W (closeLen s W) ω
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin W)))
  have h1 : ∑ i, retW h (hT.eigenvalues i) = ∑ j, retW h (hT.eigenvalues₀ j) :=
    Equiv.sum_comp e.symm (fun j => retW h (hT.eigenvalues₀ j))
  have h2 : ∑ j, retW h (hT.eigenvalues₀ j) =
      ∑ k ∈ Finset.range (Fintype.card (Fin W)), retW h (physTseq b E s W ω k) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by simp only [physTseq, j.isLt, ↓reduceDIte]
  have h3 : ∑ k : Fin K, retW h (physTseq b E s W ω k.val) =
      ∑ k ∈ Finset.range K, retW h (physTseq b E s W ω k) :=
    Fin.sum_univ_eq_sum_range (fun k => retW h (physTseq b E s W ω k)) K
  have hz : retW h 0 = 0 := retW_eq_zero (sq_nonneg h)
  rw [h1, h2, h3,
    Finset.sum_subset (Finset.range_subset_range.2 (le_max_left _ K)) (fun k _ hk => by
      rw [Finset.mem_range, not_lt] at hk
      simp only [physTseq, not_lt.2 hk, ↓reduceDIte, hz]),
    Finset.sum_subset (Finset.range_subset_range.2 (le_max_right (Fintype.card (Fin W)) K))
      (fun k _ hk => by
        rw [Finset.mem_range, not_lt] at hk
        exact retW_eq_zero (hcap k hk))]

/-- On the cap event the sorted far transmission eigenvalues beyond `K` are omitted. -/
theorem physTseq_le_of_cap {ω : GrowthPath W}
    (hS : scatteringMatrix b E W (closeLen s W) ω * (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hcap : ω ∈ entEvent (physTseq b E s W) (capSet K h)) :
    ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2 := by
  have ht := isTransmissionSequence_physTseq (s := s) hS
  have hK : seqExtract (seqTraceMeasure (physTseq b E s W ω)) K ≤ h ^ 2 := hcap
  rw [seqExtract_seqTraceMeasure ht] at hK
  exact fun k hk => (ht.1 hk).trans hK

theorem star_phase_mul (θ : ℝ) : star (phase θ) * phase θ = 1 := by
  rw [Complex.star_def, Complex.conj_mul', norm_phase]; simp

/-- **Exact feasibility of the closed frame** (TwoProjection form). -/
theorem ae_twoProjection_closedFrameAt {T : ℝ} {p M : ℕ} (q : Fin p → ℝ → ℝ) (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) (hh : h ^ 2 < 1)
    (hs : 1 ≤ closeLen s W) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : IsTimeSFrame b E s h K W Vs) :
    ∀ᵐ ω ∂growthPathLaw W b, ω ∈ physCapEvent b E s h K W →
      ∀ (km : (Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ)) (θ : ℝ) (j : ℕ),
        closeLen s W ≤ j →
        TwoProjection (nearPortProj W) (srcSignature K (Fin p × Fin M))
          (closedFrameAt b E s T h q W j Vs ((ω, km), θ)) := by
  filter_upwards [hVs.2, FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
    ae_physCapEvent_iff hb hE1 hE2 hW s h K, ae_openCur_split (K := K) (h := h) hb0 hb hE1 hE2 hW hs,
    ae_isUnit_closingResolvent hb0 hb hE1 hE2 hW hh (closeLen s W)]
    with ω ⟨hG, hE⟩ hU hcapI hsplit hR hcap km θ j hj
  set S₀ := scatteringMatrix b E W (closeLen s W) ω
  have hS₀ : S₀ᴴ * S₀ = 1 := mul_eq_one_comm.mp (hU _).1
  have ht := isTransmissionSequence_physTseq (s := s) (hU (closeLen s W)).1
  have hbase : Vs ω * curSig K * (Vs ω)ᴴ = physSplit b E s h W (closeLen s W) ω :=
    base_split (S := S₀) hS₀ (hU _).1 hh (fun k => (ht.2.1 k)) (Vs ω) (congrArg Prod.fst hG) hE
      (omitted_mul_timeSFrame (Vs ω) (hU _).1 hG hE)
      (sum_retW_cap ω (physTseq_le_of_cap (hU _).1 (hcapI.1 hcap)))
  have hX := hsplit (Vs ω) hbase (j - closeLen s W)
  rw [show closeLen s W + (j - closeLen s W) = j by omega] at hX
  have hXs : openFrameAt b E s T q W j Vs (ω, km) * srcSignature K (Fin p × Fin M) *
      (openFrameAt b E s T q W j Vs (ω, km))ᴴ =
        splitCurrent (scatteringMatrix b E W j ω) (nearPortProj W) (fA h S₀) (fPi h S₀) := by
    rw [frame_sig, curBlock_openFrameAt]; exact hX
  exact twoProjection_closed (mul_eq_one_comm.mp (hU j).1) nearPortProj_conjTranspose
    nearPortProj_mul_self (nearPortProj_mul_farEmbed _) (farEmbed_mul_nearPortProj _) fA_conj
    fA_mul_self fA_mul_fPi (fPi_mul_conj hh)
    (hR j (le_trans hs hj) (phase θ) (norm_phase θ).le) (star_phase_mul θ) hXs

/-- **Exact feasibility of the closed Gram process at finite `W`**. -/
theorem ae_gramFeasible_closedGramAt {T : ℝ} {p M : ℕ} (q : Fin p → ℝ → ℝ) (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) (hh : h ^ 2 < 1)
    (hs : 1 ≤ closeLen s W) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : IsTimeSFrame b E s h K W Vs) :
    ∀ᵐ ω ∂growthPathLaw W b, ω ∈ physCapEvent b E s h K W →
      ∀ (km : (Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ)) (θ : ℝ) (j : ℕ),
        closeLen s W ≤ j →
        GramFeasible (srcSignature K (Fin p × Fin M)) (closedGramAt b E s T h q W j Vs ((ω, km), θ)) := by
  filter_upwards [ae_twoProjection_closedFrameAt (T := T) (M := M) q hb0 hb hE1 hE2 hW hh hs hVs]
    with ω hω hcap km θ j hj
  exact GramUniqueness.gramFeasible_of_twoProjection nearPortProj_conjTranspose
    nearPortProj_mul_self (hω hcap km θ j hj)

end BlockBand.SourceProcess.ClosedFeas
