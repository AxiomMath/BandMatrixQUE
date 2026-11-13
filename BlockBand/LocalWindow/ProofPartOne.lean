module

public import BlockBand.LocalWindow.ProofETH
public import BlockBand.LocalWindow.ProofPartOneAssemblyEvents
public import BlockBand.LocalWindow.ProofPartOneAssemblyArith
public import BlockBand.LocalWindow.ProofPartOneGrid
public import BlockBand.LocalWindow.ProofCertificateRegular
public import BlockBand.LocalWindow.ProofNormEvent
public import BlockBand.LocalWindow.ProofPairLaw
public import BlockBand.Window.Count.RefinedCountLocationTools

/-!
# Assembly of part (i) of the physical local window

Proof of `PhysicalLocalWindowPartOneClauses`, the local count of part (i) of the physical
local-window lemma.

## Main results

* `measure_union_ofReal_le`: `μ(A ∪ B) ≤ ofReal (a + b)` from `μ A ≤ ofReal a`, `μ B ≤ ofReal b`.
* **`physicalLocalWindow_partOne`**: `PhysicalLocalWindowPartOneClauses`.

Constants. `ϑ' = min(ϑ, 1/4)`, `κ = πϑ'/4` (classical locations of
`ϑ`-bulk ranks lie in `bulkInterval(2κ)`, so off the rank-exit event the selected energies lie in
`bulkInterval κ`); `(ε_c, r, s₀, v₀)` from `ProofCertificate.poleCertificate_regular b κ`;
`L = 4/v₀² + 1`, `c = v₀/2`, `C₁ = L + 2/v₀ + 1` (fixed before `γ, D`). For `γ, D`: `D' = D + 1`,
`ε₀ = W^{-(D'+4)}`, grid spacing `h = W^{-2}/((nW)²/ε₀² + 1)` on `bulkInterval κ`
(`|Es| ≤ W^M`, `M = 2(D'+4) + 7`), local-law exponents `ε = δ = γ/2`, norm exponent
`A = D' + 8`, and the threshold `W^{γ/2} ≥ K` (`K` explicit); below it `Ω` is the whole space.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.LocalWindow.ProofPartOne BlockBand.LocalWindow.ProofCount
open BlockBand.LocalWindow.ProofCrowding BlockBand.LocalWindow.ProofNormEvent
open BlockBand.LocalWindow.ProofCertificate BlockBand.LocalWindow.LawBridge
open scoped ENNReal Matrix.Norms.L2Operator

/-- `μ(A ∪ B) ≤ ofReal (a + b)` from `μ A ≤ ofReal a`, `μ B ≤ ofReal b`, `a, b ≥ 0`. -/
theorem measure_union_ofReal_le {X : Type*} [MeasurableSpace X] (μ : Measure X) {A B : Set X}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : μ A ≤ ENNReal.ofReal a)
    (hB : μ B ≤ ENNReal.ofReal b) : μ (A ∪ B) ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_add ha hb]
  exact (measure_union_le A B).trans (add_le_add hA hB)

set_option maxHeartbeats 400000 in

/-- `PhysicalLocalWindowPartOneClauses`.
For `b, T, ϑ` there are `c, C₁ > 0` such
that for `0 < γ < 1/2`, `D > 0` there is `C` with: for every admissible `p` (`p.b = b`,
`n ≤ TW`), model, adjacent pair and splitting law, an event `Ω` of original and of every
pair-law probability `≤ C W^{-D}` outside which, at every `ϑ`-bulk selected energy `E = λ_α`,
with `η = W^{-1+γ}`, `c W η ≤ N_{A(E)}([-C₁η, C₁η])` and `Σ η²/(λ² + η²) ≤ C₁ W η`.
Inputs:
`ExternalLocalGUE`, `MDEBranchIdentification`, `PhysicalBlockConditionalCount`,
`MatchedTracesContract`, `RankLocationContract`, `CoareaContract`, and the law bridge
`PairGUELawBridgeStatement`.
-/
theorem physicalLocalWindow_partOne (hBridge : PairGUELawBridgeStatement)
    (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract)
    (hRL : RankLocationContract) (hCo : CoareaContract) :
    PhysicalLocalWindowPartOneClauses := by
  intro b T ϑ hϑ
  by_cases hb : 0 < b ∧ b < 1 / 2
  swap
  · refine ⟨1, 1, one_pos, one_pos, fun γ _ _ D _ => ⟨0, fun p hpb => ?_⟩⟩
    exact absurd ⟨hpb ▸ p.b_pos, hpb ▸ p.b_lt_half⟩ hb
  obtain ⟨hb0, hb1⟩ := hb
  -- the bulk margin and the certificate constants (fixed before `γ, D`)
  set ϑ' := min ϑ (1 / 4) with hϑ'
  have hϑ'0 : 0 < ϑ' := lt_min hϑ (by norm_num)
  have hϑ'1 : ϑ' < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hϑ'4 : ϑ' ≤ 1 / 4 := min_le_right _ _
  set κ := Real.pi * ϑ' / 4 with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ2 : κ ≤ 2 := by
    have := mul_le_mul Real.pi_lt_four.le hϑ'4 hϑ'0.le (by norm_num)
    rw [hκ]; linarith
  obtain ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, hreg⟩ := poleCertificate_regular b κ hb0 hb1 hκ0
  set L := 4 / v₀ ^ 2 + 1 with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ 4 / v₀ ^ 2 := by positivity
    rw [hL]; linarith
  have hLv : 4 ≤ L * v₀ ^ 2 := by
    rw [hL, add_mul, div_mul_cancel₀ _ (by positivity)]
    have := sq_nonneg v₀
    linarith
  refine ⟨v₀ / 2, L + 2 / v₀ + 1, by positivity, by positivity, fun γ hγ hγ1 D hD => ?_⟩
  -- constants depending on `γ, D`
  set D' := D + 1 with hD'
  have hD'0 : 0 ≤ D' := by linarith
  obtain ⟨CG, cG, hCG, hcG, hnormEv⟩ := normEvent_le
  set s := min (1 - 2 * b) b with hs_def
  have hs : 0 < s := lt_min (by linarith) hb0
  set Cn := (Real.sqrt s)⁻¹ * (|T| + CG + T ^ 2) with hCn
  obtain ⟨N₀, -, hloc⟩ := splitLaw_localBad_le hBridge hELG hMDE (D' + 8) Cn (γ / 2) (γ / 2)
    (2 * (D' + 4) + 7 + D') (by positivity) (by positivity) (by positivity)
  obtain ⟨Ccr, hCcr, hcr⟩ := splitLaw_crowding_rpow_le hPBC b T D' hb1 hD'0
  obtain ⟨Cnb, hCnb, hnb⟩ := normBound_le_rpow T D' cG hcG
  obtain ⟨Cgr, hCgr, hgr⟩ := gridCertificateHat_le hMT hPBC b κ T hb0 hb1 hκ0 (1 / 2) D'
    (2 * (D' + 4) + 7) (by norm_num) hD'0
  obtain ⟨Crk, hCrk, hrk⟩ := splitLaw_partOneRank_le hRL b T ϑ' κ D' hb0 hb1 hϑ'0 hϑ'1 hκ0 hD'0
  set K : ℝ := 16 / v₀ + 6 + 4 / v₀ + L + 3 / Real.sqrt s +
    (1 + 4 / (s * Real.sqrt κ)) / εc + 4 * T ^ 2 + 5 + N₀ + 1 with hK
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsk0 : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ0
  have hKt : 16 / v₀ ≤ K ∧ 6 ≤ K ∧ 4 / v₀ ≤ K ∧ L ≤ K ∧ 3 / Real.sqrt s ≤ K ∧
      (1 + 4 / (s * Real.sqrt κ)) / εc ≤ K ∧ 4 * T ^ 2 + 5 ≤ K ∧ (N₀ : ℝ) ≤ K := by
    have a1 : 0 ≤ 16 / v₀ := by positivity
    have a2 : 0 ≤ 4 / v₀ := by positivity
    have a3 : 0 ≤ 3 / Real.sqrt s := by positivity
    have a4 : 0 ≤ (1 + 4 / (s * Real.sqrt κ)) / εc := by positivity
    have a5 : 0 ≤ 4 * T ^ 2 := by positivity
    have a6 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hK] <;> linarith
  set Csm := K ^ (2 * D' / γ) with hCsm
  have hCsm0 : 0 ≤ Csm := by
    have : 0 < K := by linarith [hKt.2.1]
    positivity
  set Ct := Ccr + Cnb + Cgr + Crk + 2 + Csm with hCt
  have hCt0 : 0 ≤ Ct := by positivity
  refine ⟨max Ct (T * Ct / 2), fun p hpb hn model i Pω hPω => ?_⟩
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hWD : (p.W : ℝ) ^ (-(D + 1)) ≤ (p.W : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hWD0 : 0 ≤ (p.W : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hW0.le _
  suffices H : ∃ Ω : Set (SplitState p i × PairMatrix p i),
      splitLaw p i Pω Ω ≤ ENNReal.ofReal (Ct * (p.W : ℝ) ^ (-(D + 1))) ∧
      ∀ x ∉ Ω, ∀ α : Fin p.N, IsBulkRank p ϑ α →
        let E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α
        let A := schurA p i x.1 x.2 E
        let η := (p.W : ℝ) ^ (-1 + γ)
        v₀ / 2 * (p.W : ℝ) * η ≤
            spectralSum A (fun l => if |l| ≤ (L + 2 / v₀ + 1) * η then 1 else 0) ∧
          spectralSum A (fun l => η ^ 2 / (l ^ 2 + η ^ 2)) ≤ (L + 2 / v₀ + 1) * (p.W : ℝ) * η by
    obtain ⟨Ω, hΩ, hgood⟩ := H
    refine ⟨Ω, hΩ.trans (ENNReal.ofReal_le_ofReal ?_), fun α => ?_, hgood⟩
    · exact (mul_le_mul_of_nonneg_left hWD hCt0).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hW0.le _))
    · refine (splitPairLaw_le_of hPω α hCt0 hn hΩ).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hW0.le _)
  -- small `W`: the whole space
  by_cases hsmall : (p.W : ℝ) ^ (γ / 2) < K
  · refine ⟨Set.univ, ?_, fun x hx => absurd (Set.mem_univ x) hx⟩
    have h1 : splitLaw p i Pω Set.univ = 1 := by
      have hprob : IsProbabilityMeasure (gueMeasure (PairSite p i) (pairTime p (splitS p))) := by
        unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
        infer_instance
      unfold splitLaw
      rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ_of_isPairSplitting p i hPω,
        measure_univ, one_mul]
    rw [h1, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ((small_W_absorb hW0 hγ hD'0 hsmall).trans ?_)
    exact mul_le_mul_of_nonneg_right (by rw [hCt]; linarith) hWD0
  push Not at hsmall
  -- large `W`: scale facts
  obtain ⟨hu1, huW, hWη, hηu, h2W, hhalf, hη0, hW2η⟩ := partOne_scale_facts hW1 hγ hγ1
  set W : ℝ := (p.W : ℝ) with hWdef
  set u := W ^ (γ / 2) with hu
  set η := W ^ (-1 + γ) with hη
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hKt
  have hLη : L * η ≤ 1 := by
    have hLu : L ≤ u := k4.trans hsmall
    have huu : u ≤ u ^ 2 := by nlinarith only [hu1]
    calc L * η ≤ u ^ 2 * η := mul_le_mul_of_nonneg_right (hLu.trans huu) hη0.le
      _ = η * u ^ 2 := mul_comm _ _
      _ ≤ 1 := hηu
  have hη1 : η ≤ 1 := (le_mul_of_one_le_left hη0.le hL1).trans hLη
  have hspl : splitS p = s := splitS_eq hpb
  have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hT0 : 0 ≤ T := by
    have : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
    by_contra h; push Not at h
    have := mul_neg_of_neg_of_pos h hW0
    linarith
  have hd2 : ((2 * p.W : ℕ) : ℝ) = 2 * W := by push_cast; ring
  -- the truncation radius, the norm scale and the grid
  set ε₀ := W ^ (-(D' + 4)) with hε₀
  have hε₀0 : 0 < ε₀ := Real.rpow_pos_of_pos hW0 _
  set cn := (p.n : ℝ) * W with hcn
  have hcn0 : 0 ≤ cn := by positivity
  have hcnT : cn ≤ |T| * W ^ 2 := by
    rw [abs_of_nonneg hT0, hcn]
    calc (p.n : ℝ) * W ≤ T * W * W := mul_le_mul_of_nonneg_right hn hW0.le
      _ = T * W ^ 2 := by ring
  set h := W ^ (-2 : ℝ) / (cn ^ 2 / ε₀ ^ 2 + 1) with hh
  have hW2pos : 0 < W ^ (-2 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have hh0 : 0 < h := div_pos hW2pos (by positivity)
  have hrh : (cn ^ 2 / ε₀ ^ 2 + 1) * h = W ^ (-2 : ℝ) := by
    rw [hh]; field_simp
  obtain ⟨Es, hEs, hEsc, hEsg⟩ := exists_bulk_grid hκ0.le hκ2 hh0
  have hWT : 4 * T ^ 2 + 5 ≤ W := by linarith
  have hcard : (Es.card : ℝ) ≤ W ^ (2 * (D' + 4) + 7) :=
    hEsc.trans (grid_card_bound hW1 hn0 hn (by linarith) hWT)
  -- the large-`W` inequalities
  have hN₀ : N₀ ≤ 2 * p.W := by
    have h' : (N₀ : ℝ) ≤ 2 * W := by linarith
    have h'' : ((N₀ : ℕ) : ℝ) ≤ ((2 * p.W : ℕ) : ℝ) := by rw [hd2]; exact h'
    exact_mod_cast h''
  have hdom : ((2 * p.W : ℕ) : ℝ) ^ (γ / 2) ≤ ((2 * p.W : ℕ) : ℝ) * η * (v₀ / Real.pi) := by
    rw [hd2]
    have hpi := Real.pi_lt_four
    have hpi0 := Real.pi_pos
    have huv : 4 ≤ u * v₀ :=
      ((div_le_iff₀ hv₀).mp k3).trans (mul_le_mul_of_nonneg_right hsmall hv₀.le)
    rw [mul_div_assoc', le_div_iff₀ hpi0]
    have : 2 * W * η * v₀ = 2 * u ^ 2 * v₀ := by rw [mul_assoc 2 W η, hWη]
    rw [this]
    have hu0 : 0 ≤ u := by linarith
    calc (2 * W) ^ (γ / 2) * Real.pi ≤ 2 * u * Real.pi := mul_le_mul_of_nonneg_right h2W hpi0.le
      _ ≤ 2 * u * 4 := mul_le_mul_of_nonneg_left hpi.le (by positivity)
      _ ≤ 2 * u * (u * v₀) := mul_le_mul_of_nonneg_left huv (by positivity)
      _ = 2 * u ^ 2 * v₀ := by ring
  have hzbound : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ e ∈ Es, ‖(e : ℂ) + Complex.I * (t : ℂ)‖ ≤
      Real.sqrt (splitS p) * ((2 * p.W : ℕ) : ℝ) ^ (D' + 8 + 1 / (γ / 2)) := by
    intro t ht0 ht1 e he
    have he2 : |e| ≤ 2 := by
      obtain ⟨a1, a2⟩ := hEs e he; rw [abs_le]; constructor <;> linarith
    refine (norm_ofReal_add_I_le e t).trans ?_
    rw [abs_of_nonneg ht0, hspl, hd2]
    have hexp : 1 ≤ D' + 8 + 1 / (γ / 2) := by
      have : 0 ≤ 1 / (γ / 2) := by positivity
      linarith
    have h2W1 : 2 * W ≤ (2 * W) ^ (D' + 8 + 1 / (γ / 2)) := by
      calc 2 * W = (2 * W) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    have hsu : 3 ≤ Real.sqrt s * u := by
      have := ((div_le_iff₀ hsq0).mp k5).trans (mul_le_mul_of_nonneg_right hsmall hsq0.le)
      linarith
    have a1 := mul_le_mul_of_nonneg_left h2W1 hsq0.le
    have a2 : Real.sqrt s * u ≤ Real.sqrt s * (2 * W) :=
      mul_le_mul_of_nonneg_left (by linarith) hsq0.le
    linarith
  have hz : ∀ e ∈ Es, ‖(e : ℂ) + Complex.I * η‖ ≤
        Real.sqrt (splitS p) * ((2 * p.W : ℕ) : ℝ) ^ (D' + 8 + 1 / (γ / 2)) ∧
      ‖(e : ℂ) + Complex.I * ((L * η : ℝ) : ℂ)‖ ≤
        Real.sqrt (splitS p) * ((2 * p.W : ℕ) : ℝ) ^ (D' + 8 + 1 / (γ / 2)) := fun e he =>
    ⟨hzbound η hη0.le hη1 e he, hzbound (L * η) (by positivity) hLη e he⟩
  have hthr : W ^ (-1 + 1 / 2 : ℝ) + 4 / (W * (splitS p * Real.sqrt κ)) ≤ εc := by
    rw [hspl]
    set q := 1 + 4 / (s * Real.sqrt κ) with hq
    have hqu : q ≤ u * εc :=
      ((div_le_iff₀ hεc).mp k6).trans (mul_le_mul_of_nonneg_right hsmall hεc.le)
    have hu0 : 0 < u := by linarith
    have a1 : 4 / (W * (s * Real.sqrt κ)) * u ≤ 4 / (s * Real.sqrt κ) := by
      have e : 4 / (W * (s * Real.sqrt κ)) * u = 4 / (s * Real.sqrt κ) * (u / W) := by
        field_simp
      rw [e]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one hW0).mpr huW)
    have hsum : (W ^ (-1 + 1 / 2 : ℝ) + 4 / (W * (s * Real.sqrt κ))) * u ≤ u * εc := by
      rw [add_mul]; rw [hq] at hqu; linarith
    have := le_of_mul_le_mul_right (by linarith : (W ^ (-1 + 1 / 2 : ℝ) +
      4 / (W * (s * Real.sqrt κ))) * u ≤ εc * u) hu0
    exact this
  -- the exceptional event
  set Ω₁ := crowdingEvent p i ε₀ 2 with hΩ₁
  set Ω₂ := entryEvent p i ∪ gueEvent p i CG with hΩ₂
  set Ω₃ : Set (SplitState p i × PairMatrix p i) := {x | x ∉ crowdingEvent p i ε₀ 2 ∧
    ∃ E ∈ Es, (p.W : ℝ) ^ (-1 + 1 / 2 : ℝ) + 4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) <
      certErrHat ε₀ p i x.1 E} with hΩ₃
  set Ω₄ := partOneRankEvent p i ϑ' κ with hΩ₄
  set Ω₅ := partOneNullEvent p i with hΩ₅
  set Ω₆ := LocalBadEvent p i ε₀ (D' + 8) Cn v₀ η L (γ / 2) Es with hΩ₆
  refine ⟨Ω₁ ∪ Ω₂ ∪ Ω₃ ∪ Ω₄ ∪ Ω₅ ∪ Ω₆, ?_, ?_⟩
  · set w := W ^ (-D') with hw
    have hw0 : 0 ≤ w := Real.rpow_nonneg hW0.le _
    have b1 : splitLaw p i Pω Ω₁ ≤ ENNReal.ofReal (Ccr * w) := hcr p hpb hn model i Pω hPω
    have b2 : splitLaw p i Pω Ω₂ ≤ ENNReal.ofReal (Cnb * w) :=
      (hnormEv p model i Pω hPω).trans (ENNReal.ofReal_le_ofReal (hnb p hn))
    have b3 : splitLaw p i Pω Ω₃ ≤ ENNReal.ofReal (Cgr * w) :=
      hgr p hpb hn model i Pω hPω Es hEs hcard ε₀
    have b4 : splitLaw p i Pω Ω₄ ≤ ENNReal.ofReal (Crk * w) := hrk p hpb hn model i Pω hPω
    have b5 : splitLaw p i Pω Ω₅ ≤ ENNReal.ofReal 0 := by
      rw [splitLaw_partOneNull_eq_zero hCo hPω]; exact bot_le
    have b6 : splitLaw p i Pω Ω₆ ≤ ENNReal.ofReal (2 * w) := by
      refine (hloc p model i Pω hPω hN₀ ε₀ hε₀0 Es η L v₀ hη0 hL1 hv₀ hdom hz).trans ?_
      set M := 2 * (D' + 4) + 7 with hM
      have hM0 : 0 ≤ M := by positivity
      have e1 : ((2 * p.W : ℕ) : ℝ) ^ (-(M + D')) ≤ W ^ (-(M + D')) := by
        rw [hd2]; exact Real.rpow_le_rpow_of_nonpos hW0 (by linarith) (by linarith)
      have e2 : W ^ M * W ^ (-(M + D')) = w := by
        rw [← Real.rpow_add hW0, hw]; ring_nf
      have e3 : (Es.card : ℝ) * (2 * ((2 * p.W : ℕ) : ℝ) ^ (-(M + D'))) ≤ 2 * w := by
        have hp : 0 ≤ ((2 * p.W : ℕ) : ℝ) ^ (-(M + D')) := Real.rpow_nonneg (by positivity) _
        calc (Es.card : ℝ) * (2 * ((2 * p.W : ℕ) : ℝ) ^ (-(M + D')))
            ≤ W ^ M * (2 * W ^ (-(M + D'))) :=
              mul_le_mul hcard (by linarith) (by positivity) (Real.rpow_nonneg hW0.le _)
          _ = 2 * (W ^ M * W ^ (-(M + D'))) := by ring
          _ = 2 * w := by rw [e2]
      have hp : 0 ≤ ((2 * p.W : ℕ) : ℝ) ^ (-(M + D')) := Real.rpow_nonneg (by positivity) _
      calc (Es.card : ℝ≥0∞) * (2 * ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-(M + D'))))
          = ENNReal.ofReal ((Es.card : ℝ) * (2 * ((2 * p.W : ℕ) : ℝ) ^ (-(M + D')))) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
        _ ≤ ENNReal.ofReal (2 * w) := ENNReal.ofReal_le_ofReal e3
    have n1 : 0 ≤ Ccr * w := mul_nonneg hCcr hw0
    have n2 : 0 ≤ Cnb * w := mul_nonneg hCnb hw0
    have n3 : 0 ≤ Cgr * w := mul_nonneg hCgr hw0
    have n4 : 0 ≤ Crk * w := mul_nonneg hCrk hw0
    have n6 : 0 ≤ 2 * w := by positivity
    have s2 := measure_union_ofReal_le (splitLaw p i Pω) n1 n2 b1 b2
    have s3 := measure_union_ofReal_le (splitLaw p i Pω) (add_nonneg n1 n2) n3 s2 b3
    have s4 := measure_union_ofReal_le (splitLaw p i Pω) (add_nonneg (add_nonneg n1 n2) n3) n4
      s3 b4
    have s5 := measure_union_ofReal_le (splitLaw p i Pω)
      (add_nonneg (add_nonneg (add_nonneg n1 n2) n3) n4) le_rfl s4 b5
    have hsum := measure_union_ofReal_le (splitLaw p i Pω)
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg n1 n2) n3) n4) le_rfl) n6 s5 b6
    refine hsum.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hCt]
    have := mul_nonneg hCsm0 hw0
    nlinarith only [this]
  · intro x hx α hα E A η'
    simp only [Set.mem_union, not_or] at hx
    obtain ⟨⟨⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩, hx5⟩, hx6⟩ := hx
    -- the null event: Hermitian blocks, `E` not a pole
    have hherm : x.1.1.IsHermitian ∧ x.1.2.2.IsHermitian ∧ x.2.IsHermitian := by
      by_contra hc; exact hx5 (Or.inl hc)
    obtain ⟨hH, hV, hG⟩ := hherm
    have hdet : (x.1.1 - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0 :=
      fun h0 => hx5 (Or.inr ⟨α, h0⟩)
    -- rank location: `E ∈ bulkInterval κ`
    have hαϑ' : IsBulkRank p ϑ' α := isBulkRank_antitone (min_le_left _ _) hα
    have hcl := BlockBand.Window.Count.classicalLocation_mem_bulk p hϑ'0 hαϑ'
    have hEl : |E - classicalLocation p α| < κ := by
      by_contra hc; push Not at hc; exact hx4 ⟨α, hαϑ', hc⟩
    have hEκ : E ∈ bulkInterval κ := by
      obtain ⟨c1, c2⟩ := hcl
      rw [abs_lt] at hEl
      have : Real.pi * ϑ' / 2 = 2 * κ := by rw [hκ]; ring
      refine ⟨?_, ?_⟩ <;> linarith
    -- the nearest grid point, crowding, norms, certificate
    obtain ⟨e, he, hEe⟩ := hEsg E hEκ
    have heκ := hEs e he
    have hE2 : |E| ≤ 2 := by
      obtain ⟨c1, c2⟩ := hEκ; rw [abs_le]; constructor <;> linarith
    have hnear := nearSet_card_le_one_of_not_mem hx1 hH hE2
    obtain ⟨hC, hC', hVn⟩ := norm_bounds_of_not_mem (fun h' => hx2 (Or.inl h'))
      (fun h' => hx2 (Or.inr h'))
    have hcert : certErrHat ε₀ p i x.1 e ≤ εc := by
      have : ¬ ((p.W : ℝ) ^ (-1 + 1 / 2 : ℝ) + 4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) <
          certErrHat ε₀ p i x.1 e) := fun hlt => hx3 ⟨hx1, e, he, hlt⟩
      push Not at this
      exact this.trans hthr
    have hroot : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        HasRegularRoot (truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e) (splitS p) v₀ e t := by
      intro t ht0 ht1
      obtain ⟨h1, h2, h3⟩ := hreg p hpb i x.1 hV ε₀ e heκ hcert (splitS p) (by linarith) le_rfl e
        (by rw [sub_self, abs_zero]; exact hr.le) t ht0 ht1
      exact ⟨_, h1, h2, h3⟩
    have hFn : (Real.sqrt (splitS p))⁻¹ * ‖truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e‖ ≤
        Cn * ((2 * p.W : ℕ) : ℝ) ^ (D' + 8) := by
      have hop : ‖truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e‖ ≤ (cn + CG) + cn ^ 2 / ε₀ :=
        l2_opNorm_le_of_toE (by positivity)
          (norm_truncF_le hH x.1.2.1 x.1.2.2 hε₀0 hcn0 hC hC' hVn e)
      have hsc := truncF_scale hW1 hcn0 hcnT hCG.le (by linarith : 0 ≤ D' + 4)
      have e8 : D' + 8 = D' + 4 + 4 := by ring
      rw [hspl, hd2, hCn, mul_assoc, e8]
      exact mul_le_mul_of_nonneg_left (hop.trans hsc) (inv_nonneg.mpr hsq0.le)
    have hLG : x.1 ∈ LocalGood p i ε₀ (D' + 8) Cn v₀ η L e :=
      ⟨hV, hFn, hroot η hη0.le hη1, hroot (L * η) (by positivity) hLη⟩
    have hPB : ¬ PoissonBad ((2 * p.W : ℕ) : ℝ) (γ / 2) v₀ η L
        (truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e + x.2 - (e : ℂ) • 1) := fun hb => hx6 ⟨e, he, hLG, hb⟩
    rw [hd2] at hPB
    -- the scale inequalities of `partOne_point`
    have hcardβ : (Fintype.card (PairSite p i) : ℝ) = 2 * W := by
      rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
    have hrr : (cn ^ 2 / ε₀ ^ 2 + 1) * h ≤ η := by
      rw [hrh]; exact (le_mul_of_one_le_right hW2pos.le hW1).trans hW2η
    have huv16 : 16 ≤ u * v₀ :=
      ((div_le_iff₀ hv₀).mp k1).trans (mul_le_mul_of_nonneg_right hsmall hv₀.le)
    have hu0 : 0 ≤ u := by linarith
    have hWa : 3 * (2 * W) ^ (γ / 2) + 2 ≤ v₀ / 2 * W * η := by
      have e1 : v₀ / 2 * W * η = v₀ / 2 * u ^ 2 := by rw [mul_assoc, hWη]
      rw [e1]
      have a1 : 16 * u ≤ u * v₀ * u := mul_le_mul_of_nonneg_right huv16 hu0
      nlinarith only [a1, h2W, hu1]
    have hmid : 2 * W * ((cn ^ 2 / ε₀ ^ 2 + 1) * h) / η ≤ 2 := by
      rw [hrh, div_le_iff₀ hη0]
      linarith only [hW2η]
    have hWb : (2 * W) ^ (γ / 2) + 2 * W * ((cn ^ 2 / ε₀ ^ 2 + 1) * h) / η + 2 ≤ W * η := by
      rw [hWη]
      have hu6 : 6 ≤ u := k2.trans hsmall
      have a1 : 6 * u ≤ u * u := mul_le_mul_of_nonneg_right hu6 hu0
      nlinarith only [a1, hmid, h2W, hu1]
    have hv2 : 0 ≤ 2 / v₀ := by positivity
    have hL0 : 0 ≤ L := by linarith
    exact partOne_point hH x.1.2.1 hV hG hε₀0 hcn0 hC hC' hdet hnear hEe hη0 hL1 hv₀ hLv hcardβ
      hPB hrr (by linarith) (by linarith) hWa hWb

end BlockBand.LocalWindow
