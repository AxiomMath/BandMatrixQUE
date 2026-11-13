module

public import BlockBand.DeterminantScore.SelectedLocalLawArith
public import BlockBand.LocalWindow.ProofPartOneAssemblyEvents
public import BlockBand.LocalWindow.ProofPartOneAssemblyArith

/-!
# `SelectedLocalLawStatement`: the averaged local law at the selected energies

Item (3) of `WeightedTrace.SelectedResolventStatement`. In the proof of the physical real-loop
proposition the averaged local law gives `‖Tr R_η - d m_E(iη)‖_{L^p} ≤ C W^ε/η`; this is
transferred to the selected energies on the energy grid of the proof of the physical
local-window lemma.

* `grid_r_le`: `((nW)²/ε₀² + 1) h ≤ (T² + 1) W⁻²` (`ε₀ = W^{-(D+5)}`, `h = W^{-(2(D+5)+6)}`).
* **`selectedLocalLaw_holds`**: `SelectedResolvent.SelectedLocalLawStatement`.
* `selectedResolvent_of_ibp`: `WeightedTrace.SelectedResolventStatement` from the same inputs and
  the remaining named item (4), `SelectedResolvent.SelectedIBPStatement`.

Proof. Bulk margin `κ` and the certificate event `Ω_c` from `SelectedCertificateStatement`
(`SelectedResolvent.selectedCertificate_holds`) at `ε = 1/2` (off `Ω_c`: `H_R, V` Hermitian,
every `ϑ`-bulk selected energy in `bulkInterval κ` with `certErr(E) ≤ C_c W^{-1/2}`); regularity
constants `(ε₁, δ_P, L)` of `pair_regular` at `c = min(1 - 2b, b)`, `V = √κ/2`. For large `W`,
with `ε₀ = W^{-(D+5)}`, `h = W^{-(2(D+5)+6)}`, `Es = bulkGrid κ h`, `η = W^{-3/5}`,
`χ₀ = C_χ W^{-1/2}`: the remaining event is crowding at radius `ε₀`
(`PhysicalBlockConditionalCount`) ∪ the norm event ∪ the null event (`CoareaContract`) ∪ the
grid trace-failure event (`splitLaw_traceBad_le`: `ExternalLocalGUE`, `MDEBranchIdentification`,
the law bridge; local-law loss `d^ε`, domain exponent `1/5`, failure power `M + D + 1`), of
split-law probability `≤ C W^{-(D+1)}`, so pair-law `≤ (TC/2) W^{-D}` (`splitPairLaw_le_of`).
Off the events, at `E = λ_α` with grid neighbour `e`: `certErrHat(e) ≤ χ₀` puts the exterior in
`TraceGood e`, and `selected_point` with `scale_le` gives
`‖Tr R_η - d m_E(iη)‖ ≤ C_b W^ε/η`. Small `W`: `Ω` = everything (`splitPairLaw_le_small`).

Hypotheses: exactly `ExternalLocalGUE`, `MDEBranchIdentification`,
`PhysicalBlockConditionalCount`, `MatchedTracesContract`, `RankLocationContract`,
`CoareaContract`, and the statement `LawBridge.PairGUELawBridgeStatement`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedLocalLaw

open MeasureTheory ProbabilityTheory Matrix Set BlockBand.Palm
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.LocalWindow BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofCertificate
open BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofPartOne
open BlockBand.DeterminantScore.SelectedResolvent
open scoped ENNReal ComplexConjugate Matrix.Norms.L2Operator

/-- **The grid operator move**: with `ε₀ = W^{-(D+5)}`, `h = W^{-(2(D+5)+6)}`,
`0 ≤ n ≤ TW`, `W ≥ 1`, `D ≥ 0`: `((nW)²/ε₀² + 1) h ≤ (T² + 1) W⁻²`. -/
theorem grid_r_le {T W n D : ℝ} (hW1 : 1 ≤ W) (hn0 : 0 ≤ n) (hn : n ≤ T * W) (hD : 0 ≤ D) :
    ((n * W) ^ 2 / (W ^ (-(D + 1 + 4))) ^ 2 + 1) * W ^ (-(2 * (D + 5) + 6)) ≤
      (T ^ 2 + 1) * W ^ (-2 : ℝ) := by
  have hW0 : 0 < W := by linarith
  set ε₀ := W ^ (-(D + 1 + 4)) with hε₀
  set P := W ^ (2 * (D + 5) + 4) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hW1 (by linarith)
  have hε₀sq : ε₀ ^ 2 = W ^ (-(2 * (D + 5))) := by
    rw [hε₀, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  have hnW : (n * W) ^ 2 ≤ T ^ 2 * W ^ (4 : ℝ) := by
    have hT : 0 ≤ T * W := hn0.trans hn
    have : n * W ≤ T * W * W := mul_le_mul_of_nonneg_right hn hW0.le
    have h2 := pow_le_pow_left₀ (by positivity) this 2
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hq : (n * W) ^ 2 / ε₀ ^ 2 ≤ T ^ 2 * P := by
    rw [hε₀sq, div_eq_mul_inv, ← Real.rpow_neg hW0.le, neg_neg]
    calc (n * W) ^ 2 * W ^ (2 * (D + 5)) ≤ T ^ 2 * W ^ (4 : ℝ) * W ^ (2 * (D + 5)) := by
          gcongr
      _ = T ^ 2 * P := by rw [mul_assoc, ← Real.rpow_add hW0, hP]; ring_nf
  have hPh : P * W ^ (-(2 * (D + 5) + 6)) = W ^ (-2 : ℝ) := by
    rw [hP, ← Real.rpow_add hW0]; ring_nf
  have hh0 : 0 ≤ W ^ (-(2 * (D + 5) + 6)) := (Real.rpow_pos_of_pos hW0 _).le
  calc ((n * W) ^ 2 / ε₀ ^ 2 + 1) * W ^ (-(2 * (D + 5) + 6))
      ≤ (T ^ 2 * P + P) * W ^ (-(2 * (D + 5) + 6)) := by gcongr
    _ = (T ^ 2 + 1) * (P * W ^ (-(2 * (D + 5) + 6))) := by ring
    _ = _ := by rw [hPh]

/-- `μ(A ∪ B) ≤ ofReal (a + b)` from `μ A ≤ ofReal a`, `μ B ≤ ofReal b`, `a, b ≥ 0`. -/
theorem union_ofReal_le {X : Type*} [MeasurableSpace X] (μ : Measure X) {A B : Set X}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : μ A ≤ ENNReal.ofReal a)
    (hB : μ B ≤ ENNReal.ofReal b) : μ (A ∪ B) ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_add ha hb]
  exact (measure_union_le A B).trans (add_le_add hA hB)

set_option maxHeartbeats 1600000 in

/-- **Item (3) of `SelectedResolventStatement`: the averaged local law at the selected energies**:
`SelectedLocalLawStatement`, i.e. for `b, T, ϑ > 0`, `ε, D > 0` a constant `C` such that
uniformly in `n ≤ TW`, models, pairs and splitting laws, an event `Ω` of every pair-law
probability `≤ C W^{-D}` has, outside it, at every `ϑ`-bulk selected energy `E = λ_α`,
`|Tr R_η - d m_E(iη)| ≤ C W^ε/η` (`η = W^{-3/5}`, `d = 2W`). Inputs: `ExternalLocalGUE`,
`MDEBranchIdentification`, `PhysicalBlockConditionalCount`, `MatchedTracesContract`,
`CoareaContract`, `RankLocationContract`, and the law bridge `PairGUELawBridgeStatement`. -/
theorem selectedLocalLaw_holds (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hCo : CoareaContract) (hRank : RankLocationContract) :
    SelectedLocalLawStatement := by
  intro b T ϑ hϑ ε hε D hD
  by_cases hb : 0 < b ∧ b < 1 / 2
  swap
  · exact ⟨0, fun p hpb => absurd ⟨hpb ▸ p.b_pos, hpb ▸ p.b_lt_half⟩ hb⟩
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨κ, hκ, hCk⟩ := selectedCertificate_holds hMT hPBC hCo hRank b T ϑ hϑ
  obtain ⟨Cc, hCc⟩ := hCk (1 / 2) (by norm_num) D hD
  -- `κ > 2`: no bulk energies
  by_cases hκ2 : κ ≤ 2
  swap
  · refine ⟨|Cc|, fun p hpb hn model i Pω hsplit => ?_⟩
    obtain ⟨Ω, hΩ, hg⟩ := hCc p hpb hn model i Pω hsplit
    refine ⟨Ω, fun α => (hΩ α).trans (ENNReal.ofReal_le_ofReal ?_), fun x hx α hα => ?_⟩
    · exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exfalso
      obtain ⟨-, -, hsel⟩ := hg x hx
      obtain ⟨⟨h1, h2⟩, -⟩ := hsel α hα
      exact hκ2 (by linarith)
  -- the fixed constants
  set c₀ := min (1 - 2 * b) b with hc₀def
  have hc₀ : 0 < c₀ := lt_min (by linarith) hb0
  have hc₀1 : c₀ < 1 := (min_le_right _ _).trans_lt (by linarith)
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  set V := Real.sqrt κ / 2 with hVdef
  have hV : 0 < V := by positivity
  obtain ⟨ε₁, δP, L, hε₁, hδP, hL, hreg⟩ := pairRegularBody_exists hc₀ hc₀1 hV
  obtain ⟨Ccr, hCcr0, hcr⟩ := splitLaw_crowding_le hPBC b T (D + 1) hb0 hb1 (by linarith)
  obtain ⟨CG, cG, hCG, hcG, hnorm⟩ := ProofNormEvent.normEvent_le
  obtain ⟨Cnb, hCnb0, hCnb⟩ := ProofNormEvent.normBound_le_rpow T (D + 1) cG hcG
  set Aℓ : ℝ := D + 1 + 4 + 4 with hAℓ
  set Cn : ℝ := (Real.sqrt c₀)⁻¹ * (|T| + CG + T ^ 2 + 2) with hCn
  set M : ℝ := 2 * (D + 5) + 6 + 3 with hM
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨N₀, -, hloc⟩ := splitLaw_traceBad_le hBridge hELG hMDE hreg hV hL.le hκ le_rfl Aℓ Cn
    (1 / 5) ε (M + (D + 1)) (by norm_num) hε (by positivity)
  set La : ℝ := 1 / 2 + 2 / Real.sqrt κ with hLa
  have hLa0 : 0 ≤ La := by positivity
  set K₁ : ℝ := 2 * (c₀ * (Real.sqrt κ / 2))⁻¹ * (c₀ * (Real.sqrt κ / 2))⁻¹ *
      (T ^ 2 + 1 + c₀ * (1 / 2 + 2 / Real.sqrt κ)) + (1 / 2 + 2 / Real.sqrt κ) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set Cχ : ℝ := |Cc| + 4 / (c₀ * Real.sqrt κ) + K₁ + 1 with hCχ
  have hCχ0 : 0 < Cχ := by positivity
  set Cb : ℝ := 2 + 2 * (T ^ 2 + 1) + 2 ^ ε + 4 * L * (1 + Cχ) + 2 * La with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set Cr : ℝ := Ccr + Cnb + 1 with hCr
  have hCr0 : 0 ≤ Cr := by positivity
  set kd : ℝ := 3 * V / 4 / Real.pi with hkd
  have hkd0 : 0 < kd := by positivity
  set W₀ : ℝ := max (max (max (δP ^ (-1 / (3 / 5 : ℝ))) ((ε₁ / Cχ) ^ (-1 / (1 / 2 : ℝ))))
      (max (kd ^ (-1 / (1 / 5 : ℝ))) (Real.sqrt c₀)⁻¹)) (max (N₀ : ℝ) 2) with hW₀
  have hW₀2 : 2 ≤ W₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hW₀0 : 0 ≤ W₀ := by linarith
  refine ⟨|Cc| + |T| * Cr / 2 + |T| * W₀ ^ (D + 1) / 2 + Cb,
    fun p hpb hn model i Pω hsplit => ?_⟩
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hT : 0 ≤ T := by
    have : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
    by_contra h
    push Not at h
    nlinarith
  have hsp : splitS p = c₀ := splitS_eq hpb
  have hs : 0 < splitS p := hsp ▸ hc₀
  have hneg : 0 ≤ (p.W : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hCsum : 0 ≤ |T| * Cr / 2 := by positivity
  have hCsmall : 0 ≤ |T| * W₀ ^ (D + 1) / 2 := by positivity
  obtain ⟨Ωc, hΩc, hgc⟩ := hCc p hpb hn model i Pω hsplit
  -- small `W`: the whole space
  by_cases hWbig : W₀ < (p.W : ℝ)
  swap
  · push Not at hWbig
    refine ⟨Set.univ, fun α => ?_, fun x hx => absurd (Set.mem_univ x) hx⟩
    refine (splitPairLaw_le_small hsplit α Set.univ (by linarith : (0 : ℝ) ≤ D) hn hWbig).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [abs_of_nonneg hT] at hCsum hCsmall ⊢
    refine mul_le_mul_of_nonneg_right ?_ hneg
    have := abs_nonneg Cc
    linarith
  -- large `W`
  set W : ℝ := (p.W : ℝ) with hWdef
  have hW₀W : ∀ t : ℝ, t ≤ W₀ → t ≤ W := fun t ht => ht.trans hWbig.le
  have hW2 : 2 ≤ W := hW₀W 2 hW₀2
  have hNW : N₀ ≤ 2 * p.W := by
    have h' : (N₀ : ℝ) ≤ W := hW₀W _ ((le_max_left _ _).trans (le_max_right _ _))
    have h'' : (N₀ : ℝ) ≤ ((2 * p.W : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h''
  have hd2 : ((2 * p.W : ℕ) : ℝ) = 2 * W := by push_cast; ring
  set dR : ℝ := ((2 * p.W : ℕ) : ℝ) with hdR
  have hdR1 : 1 ≤ dR := by rw [hd2]; linarith
  set ε₀ := W ^ (-(D + 1 + 4)) with hε₀
  have hε₀0 : 0 < ε₀ := Real.rpow_pos_of_pos hW0 _
  set h := W ^ (-(2 * (D + 5) + 6)) with hh
  have hh0 : 0 < h := Real.rpow_pos_of_pos hW0 _
  have hhW : h ≤ W ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  set Es := bulkGrid κ h with hEs
  have hEsb : ∀ e ∈ Es, e ∈ bulkInterval κ := fun e he => bulkGrid_mem hκ2 hh0.le he
  have hcard : (Es.card : ℝ) ≤ W ^ M := by
    refine (bulkGrid_card_le hκ.le hκ2 hh0).trans ?_
    have h4 : 4 / h = 4 * W ^ (2 * (D + 5) + 6) := by
      rw [hh, Real.rpow_neg hW0.le, div_inv_eq_mul]
    have hM1 : 1 ≤ W ^ (2 * (D + 5) + 6) := Real.one_le_rpow hW1 (by linarith)
    have h3 : (8 : ℝ) ≤ W ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ W ^ 3 := pow_le_pow_left₀ (by norm_num) hW2 3
    have hsp3 : W ^ M = W ^ (2 * (D + 5) + 6) * W ^ (3 : ℝ) := by
      rw [hM]; exact Real.rpow_add hW0 _ _
    rw [h4, hsp3]
    have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ W ^ (2 * (D + 5) + 6))
    linarith
  set η := W ^ (-(3 / 5 : ℝ)) with hη
  have hη0 : 0 < η := Real.rpow_pos_of_pos hW0 _
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
  set χ₀ := Cχ * W ^ (-(1 / 2 : ℝ)) with hχ₀
  have hχ₀0 : 0 ≤ χ₀ := by positivity
  -- the large-`W` thresholds
  have hηδ : η ≤ δP := rpow_neg_le_of_le (by norm_num) hδP
    (hW₀W _ (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)))
  have hχε : χ₀ ≤ ε₁ := by
    have h' := rpow_neg_le_of_le (a := 1 / 2) (by norm_num) (div_pos hε₁ hCχ0)
      (hW₀W _ (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)))
    rw [le_div_iff₀ hCχ0] at h'
    rw [hχ₀]; linarith
  have hmul : ∀ a : ℝ, W * W ^ a = W ^ (1 + a) := fun a => by
    rw [Real.rpow_add hW0, Real.rpow_one]
  have hdom : dR ^ (1 / 5 : ℝ) ≤ dR * η * (3 * V / 4 / Real.pi) := by
    have hk := rpow_neg_le_of_le (a := 1 / 5) (by norm_num) hkd0
      (hW₀W _ (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)))
    rw [hd2, Real.mul_rpow (by norm_num) hW0.le, ← hkd]
    have h2r : (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hsplitW : W ^ (1 / 5 : ℝ) = W ^ (-(1 / 5 : ℝ)) * W ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_add hW0]; norm_num
    have hWη : 2 * W * η = 2 * W ^ (2 / 5 : ℝ) := by
      rw [mul_assoc, hη, hmul]; norm_num
    have hp : 0 ≤ W ^ (2 / 5 : ℝ) := Real.rpow_nonneg hW0.le _
    have hp' : 0 ≤ W ^ (1 / 5 : ℝ) := Real.rpow_nonneg hW0.le _
    rw [hWη]
    calc (2 : ℝ) ^ (1 / 5 : ℝ) * W ^ (1 / 5 : ℝ) ≤ 2 * W ^ (1 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_right h2r hp'
      _ = 2 * (W ^ (-(1 / 5 : ℝ)) * W ^ (2 / 5 : ℝ)) := by rw [hsplitW]
      _ ≤ 2 * (kd * W ^ (2 / 5 : ℝ)) := by gcongr
      _ = 2 * W ^ (2 / 5 : ℝ) * kd := by ring
  have hzb : η ≤ Real.sqrt (splitS p) * dR ^ (Aℓ + 1 / (1 / 5)) := by
    have hsW : 1 ≤ Real.sqrt c₀ * W := by
      have h' : (Real.sqrt c₀)⁻¹ ≤ W :=
        hW₀W _ (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
      have hsc : 0 < Real.sqrt c₀ := Real.sqrt_pos.mpr hc₀
      have := mul_le_mul_of_nonneg_left h' hsc.le
      rwa [mul_inv_cancel₀ hsc.ne'] at this
    have hexp : 1 ≤ Aℓ + 1 / (1 / 5 : ℝ) := by rw [hAℓ]; norm_num; linarith
    have hdd : dR ≤ dR ^ (Aℓ + 1 / (1 / 5)) := by
      calc dR = dR ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hdR1 hexp
    have hsc0 : 0 ≤ Real.sqrt c₀ := Real.sqrt_nonneg _
    rw [hsp]
    have : W ≤ dR := by rw [hd2]; linarith
    calc η ≤ 1 := hη1
      _ ≤ Real.sqrt c₀ * W := hsW
      _ ≤ Real.sqrt c₀ * dR ^ (Aℓ + 1 / (1 / 5)) :=
          mul_le_mul_of_nonneg_left (this.trans hdd) hsc0
  -- the remaining exceptional event
  set Ωr : Set (SplitState p i × PairMatrix p i) :=
    ProofCrowding.crowdingEvent p i ε₀ 2 ∪
      (ProofNormEvent.entryEvent p i ∪ ProofNormEvent.gueEvent p i CG) ∪ partOneNullEvent p i ∪
      TraceBadEvent p i ε₀ Aℓ Cn χ₀ ε η (L * (η + χ₀)) Es with hΩrdef
  have hΩr : splitLaw p i Pω Ωr ≤ ENNReal.ofReal (Cr * W ^ (-(D + 1))) := by
    have hw : 0 ≤ W ^ (-(D + 1)) := Real.rpow_nonneg hW0.le _
    have b1 := hcr p hpb hn model i Pω hsplit
    have b2 : splitLaw p i Pω (ProofNormEvent.entryEvent p i ∪ ProofNormEvent.gueEvent p i CG) ≤
        ENNReal.ofReal (Cnb * W ^ (-(D + 1))) :=
      (hnorm p model i Pω hsplit).trans (ENNReal.ofReal_le_ofReal (hCnb p hn))
    have b3 := splitLaw_partOneNull_eq_zero hCo hsplit
    have b4 : splitLaw p i Pω (TraceBadEvent p i ε₀ Aℓ Cn χ₀ ε η (L * (η + χ₀)) Es) ≤
        ENNReal.ofReal (1 * W ^ (-(D + 1))) := by
      refine (hloc p hpb model i Pω hsplit hNW ε₀ hε₀0 Es hEsb η χ₀ hη0 hηδ hχ₀0 hχε hdom
        hzb).trans ?_
      have e1 : dR ^ (-(M + (D + 1))) ≤ W ^ (-(M + (D + 1))) := by
        rw [hd2]; exact Real.rpow_le_rpow_of_nonpos hW0 (by linarith) (by linarith)
      have e2 : W ^ M * W ^ (-(M + (D + 1))) = W ^ (-(D + 1)) := by
        rw [← Real.rpow_add hW0]; ring_nf
      have hp : 0 ≤ dR ^ (-(M + (D + 1))) := Real.rpow_nonneg (by linarith) _
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (Es.card : ℝ) * dR ^ (-(M + (D + 1))) ≤ W ^ M * W ^ (-(M + (D + 1))) :=
            mul_le_mul hcard e1 hp (Real.rpow_nonneg hW0.le _)
        _ = 1 * W ^ (-(D + 1)) := by rw [e2, one_mul]
    have n1 : 0 ≤ Ccr * W ^ (-(D + 1)) := mul_nonneg hCcr0 hw
    have n2 : 0 ≤ Cnb * W ^ (-(D + 1)) := mul_nonneg hCnb0 hw
    have s2 := union_ofReal_le (splitLaw p i Pω) n1 n2 b1 b2
    have s3 := union_ofReal_le (splitLaw p i Pω) (add_nonneg n1 n2) le_rfl s2
      (by rw [b3]; exact bot_le)
    have s4 := union_ofReal_le (splitLaw p i Pω)
      (add_nonneg (add_nonneg n1 n2) le_rfl) (by positivity) s3 b4
    refine s4.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hCr]; ring
  refine ⟨Ωc ∪ Ωr, fun α => ?_, fun x hx α hα => ?_⟩
  · refine (measure_union_le _ _).trans ?_
    have hr := splitPairLaw_le_of hsplit α hCr0 hn hΩr
    calc splitPairLaw p i α Pω Ωc + splitPairLaw p i α Pω Ωr
        ≤ ENNReal.ofReal (Cc * W ^ (-D)) + ENNReal.ofReal (T * Cr / 2 * W ^ (-D)) :=
          add_le_add (hΩc α) hr
      _ ≤ ENNReal.ofReal (|Cc| * W ^ (-D)) + ENNReal.ofReal (T * Cr / 2 * W ^ (-D)) := by
          gcongr; exact le_abs_self _
      _ = ENNReal.ofReal ((|Cc| + T * Cr / 2) * W ^ (-D)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hneg)
          rw [abs_of_nonneg hT] at hCsum hCsmall ⊢
          linarith
  -- the pointwise estimate
  have hxc : x ∉ Ωc := fun h' => hx (Or.inl h')
  have hxr : x ∉ Ωr := fun h' => hx (Or.inr h')
  simp only [hΩrdef, Set.mem_union, not_or] at hxr
  obtain ⟨⟨⟨hxcr, hxent, hxgue⟩, hxnull⟩, hxbad⟩ := hxr
  obtain ⟨hH, hV, hsel⟩ := hgc x hxc
  have hG : x.2.IsHermitian := by
    by_contra hc; exact hxnull (Or.inl fun h' => hc h'.2.2)
  have hdet : ∀ β : Fin p.N, (x.1.1 -
      ((physicalOrderedEigenvalue p (assemble p i x.1 x.2) β : ℝ) : ℂ) •
        (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0 :=
    fun β h0 => hxnull (Or.inr ⟨β, h0⟩)
  obtain ⟨hC, hC', hVn⟩ := ProofNormEvent.norm_bounds_of_not_mem hxent hxgue
  dsimp only
  set E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α with hEdef
  obtain ⟨hEκ, hcertE⟩ := hsel α hα
  have hE2 : |E| ≤ 2 := by
    obtain ⟨h1, h2⟩ := hEκ; rw [abs_le]; constructor <;> linarith
  have hnear := ProofCrowding.nearSet_card_le_one_of_not_mem hxcr hH hE2
  obtain ⟨e, heEs, hEe⟩ := exists_bulkGrid_near hh0 hEκ
  have he := hEsb e heEs
  have he2 : |e| ≤ 2 := by
    obtain ⟨h1, h2⟩ := he; rw [abs_le]; constructor <;> linarith
  set cn : ℝ := (p.n : ℝ) * W with hcn
  have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hcn0 : 0 ≤ cn := by positivity
  -- the certificate at `E` and at `e`
  have hWh : W ^ (-1 + 1 / 2 : ℝ) = W ^ (-(1 / 2 : ℝ)) := by norm_num
  have hpw1 : W ^ (-1 : ℝ) ≤ W ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  have hpw2 : W ^ (-2 : ℝ) ≤ W ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  have hph : 0 ≤ W ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hW0.le _
  have hcertE' : certErr p i x.1 E ≤ |Cc| * W ^ (-(1 / 2 : ℝ)) := by
    rw [← hWh]; exact hcertE.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (Real.rpow_nonneg hW0.le _))
  have hcertχ : certErr p i x.1 E ≤ χ₀ := by
    refine hcertE'.trans ?_
    rw [hχ₀]
    refine mul_le_mul_of_nonneg_right ?_ hph
    have : 0 ≤ 4 / (c₀ * Real.sqrt κ) := by positivity
    linarith
  have hhat : certErrHat ε₀ p i x.1 e ≤ certErr p i x.1 E + 4 / (W * (c₀ * Real.sqrt κ)) +
      gridLip c₀ κ cn ε₀ * h := by
    have := SelectedLocalLaw.certErrHat_grid_le x.1 hH hV hε₀0 hcn0 hκ hC hC' hs hEκ he hEe
      (hdet α) hnear
    rw [hsp] at this
    exact this
  have hgl : gridLip c₀ κ cn ε₀ * h ≤ K₁ * W ^ (-2 : ℝ) := by
    have := gridLip_mul_le (s := splitS p) (κ := κ) (T := T) hs hκ hW1 hn0 hn hD.le
    rw [hsp] at this
    exact this
  have hchiK : ‖certificateChi (hatK ε₀ x.1 e) (splitS p) 0 (conj (matchedA e))‖ ≤ χ₀ := by
    refine (norm_chi_hatK_le ε₀ x.1 hV e).trans (hhat.trans ?_)
    have hB : 4 / (W * (c₀ * Real.sqrt κ)) = 4 / (c₀ * Real.sqrt κ) * W ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]; field_simp
    rw [hB]
    have hB0 : 0 ≤ 4 / (c₀ * Real.sqrt κ) := by positivity
    have e1 : 4 / (c₀ * Real.sqrt κ) * W ^ (-1 : ℝ) ≤
        4 / (c₀ * Real.sqrt κ) * W ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hpw1 hB0
    have e2 : K₁ * W ^ (-2 : ℝ) ≤ K₁ * W ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hpw2 hK₁0
    have e3 : χ₀ = (|Cc| + 4 / (c₀ * Real.sqrt κ) + K₁) * W ^ (-(1 / 2 : ℝ)) +
        W ^ (-(1 / 2 : ℝ)) := by rw [hχ₀, hCχ]; ring
    rw [e3]
    linarith [hcertE', e1, e2, hgl, hph]
  -- the norm bound of `K̂_e`
  have hTn : (Real.sqrt (splitS p))⁻¹ * ‖hatK ε₀ x.1 e‖ ≤ Cn * dR ^ Aℓ := by
    have hop : ‖hatK ε₀ x.1 e‖ ≤ (cn + CG) + cn ^ 2 / ε₀ + 2 := by
      refine l2_opNorm_le_of_toE (by positivity) fun v => ?_
      unfold hatK
      rw [map_sub, LinearMap.sub_apply]
      have k1 := norm_truncF_le hH x.1.2.1 x.1.2.2 hε₀0 hcn0 hC hC' hVn e v
      have k2 := norm_toE_smul_one (ι := PairSite p i) (e : ℂ) v
      rw [Complex.norm_real, Real.norm_eq_abs] at k2
      calc _ ≤ ‖Matrix.toEuclideanLin (𝕜 := ℂ) (truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e) v‖ +
              ‖Matrix.toEuclideanLin (𝕜 := ℂ) ((e : ℂ) • (1 : PairMatrix p i)) v‖ :=
            norm_sub_le _ _
        _ ≤ ((cn + CG) + cn ^ 2 / ε₀) * ‖v‖ + 2 * ‖v‖ := by
            rw [k2]; gcongr
        _ = _ := by ring
    have hcnT : cn ≤ |T| * W ^ 2 := by
      rw [abs_of_nonneg hT, hcn]
      calc (p.n : ℝ) * W ≤ T * W * W := mul_le_mul_of_nonneg_right hn hW0.le
        _ = T * W ^ 2 := by ring
    have hsc := truncF_scale hW1 hcn0 hcnT hCG.le (by linarith : (0 : ℝ) ≤ D + 1 + 4)
    have hA1 : 1 ≤ (2 * W) ^ Aℓ := Real.one_le_rpow (by linarith) (by positivity)
    rw [hsp, hd2, hCn, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    have e8 : D + 1 + 4 + 4 = Aℓ := by rw [hAℓ]
    rw [e8] at hsc
    linarith [hop, hsc, hA1]
  have hgood : x.1 ∈ TraceGood p i ε₀ Aℓ Cn χ₀ e := ⟨hV, hTn, hchiK⟩
  have hbad : ‖((hatK ε₀ x.1 e + x.2 - (((0 : ℝ) : ℂ) + Complex.I * η) •
        (1 : PairMatrix p i))⁻¹).trace - ((2 * p.W : ℕ) : ℂ) * conj (matchedA e)‖ ≤
      dR ^ ε / η + dR * (L * (η + χ₀)) :=
    not_lt.mp fun hlt => hxbad ⟨e, heEs, hgood, hlt⟩
  have hpt := selected_point x hH hV hG hε₀0 hcn0 hκ hC hC' hsp hreg hL.le hη0 hηδ hχε hEκ he
    hEe (hdet α) hnear hcertχ hbad
  refine hpt.trans ?_
  -- the scale arithmetic
  obtain ⟨s1, s2, s3, s4, s5⟩ := scale_le hW1 hε
  rw [← hη] at s1 s2 s3 s4 s5
  set u := W ^ ε / η with hu
  have hr := grid_r_le hW1 hn0 hn hD.le
  rw [← hε₀, ← hh, ← hcn] at hr
  have hT2 : 0 ≤ T ^ 2 + 1 := by positivity
  have k1 : 2 / η ≤ 2 * u := by rw [div_eq_mul_one_div]; linarith
  have k2 : 2 * W * ((cn ^ 2 / ε₀ ^ 2 + 1) * h) / η ^ 2 ≤ 2 * (T ^ 2 + 1) * u := by
    calc 2 * W * ((cn ^ 2 / ε₀ ^ 2 + 1) * h) / η ^ 2
        ≤ 2 * W * ((T ^ 2 + 1) * W ^ (-2 : ℝ)) / η ^ 2 := by gcongr
      _ = 2 * (T ^ 2 + 1) * (W * W ^ (-2 : ℝ) / η ^ 2) := by ring
      _ ≤ 2 * (T ^ 2 + 1) * u := by gcongr
  have k3 : dR ^ ε / η = 2 ^ ε * u := by
    rw [hd2, Real.mul_rpow (by norm_num) hW0.le, hu]; ring
  have k4 : 2 * dR * (L * (η + χ₀)) ≤ 4 * L * (1 + Cχ) * u := by
    rw [hd2, hχ₀]
    have hLp : 0 ≤ L := hL.le
    have e1 : 2 * (2 * W) * (L * (η + Cχ * W ^ (-(1 / 2 : ℝ)))) =
        4 * L * (W * η) + 4 * L * Cχ * (W * W ^ (-(1 / 2 : ℝ))) := by ring
    rw [e1]
    have a1 : 4 * L * (W * η) ≤ 4 * L * u := mul_le_mul_of_nonneg_left s3 (by positivity)
    have a2 : 4 * L * Cχ * (W * W ^ (-(1 / 2 : ℝ))) ≤ 4 * L * Cχ * u :=
      mul_le_mul_of_nonneg_left s4 (by positivity)
    linarith [a1, a2]
  have k5 : dR * (La * h) ≤ 2 * La * u := by
    rw [hd2]
    have : 2 * W * (La * h) ≤ 2 * La * (W * W ^ (-2 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hhW (by positivity : (0 : ℝ) ≤ 2 * W * La)
      linarith
    exact this.trans (mul_le_mul_of_nonneg_left s5 (by positivity))
  have hu0 : 0 ≤ u := by positivity
  have hfin : Cb * u ≤ (|Cc| + |T| * Cr / 2 + |T| * W₀ ^ (D + 1) / 2 + Cb) * u := by
    refine mul_le_mul_of_nonneg_right ?_ hu0
    have := abs_nonneg Cc
    linarith
  have hsum : 2 / η + 2 * W * ((cn ^ 2 / ε₀ ^ 2 + 1) * h) / η ^ 2 + dR ^ ε / η +
      2 * dR * (L * (η + χ₀)) + dR * ((1 / 2 + 2 / Real.sqrt κ) * h) ≤ Cb * u := by
    rw [k3, hCb]
    rw [← hLa]
    linarith [k1, k2, k4, k5]
  calc _ ≤ Cb * u := hsum
    _ ≤ _ := hfin
    _ = _ := by rw [hu]; ring

/-- **`SelectedResolventStatement` up to item (4)**: items (1)–(2) from
`selectedCertificate_holds`, item (3) from `selectedLocalLaw_holds`; item (4)
(`SelectedIBPStatement`, Gaussian integration by parts) remains a hypothesis. -/
theorem selectedResolvent_of_ibp (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hCo : CoareaContract) (hRank : RankLocationContract)
    (h4 : SelectedIBPStatement) : WeightedTrace.SelectedResolventStatement :=
  selectedResolvent_of_localLaw_ibp hMT hPBC hCo hRank
    (selectedLocalLaw_holds hBridge hELG hMDE hPBC hMT hCo hRank) h4

end BlockBand.DeterminantScore.SelectedLocalLaw
