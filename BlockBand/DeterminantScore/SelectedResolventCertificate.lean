module

public import BlockBand.DeterminantScore.SelectedResolventEvents

/-!
# `SelectedCertificateStatement`: the pole certificate at the selected energies

The uniform pole certificate holds simultaneously for `E ∈ I`, with arbitrary fixed polynomial
failure power; a grid of spacing `W^{-M}`, `M > 2A₀ + 6`, suffices. It is applied at the
selected energies `E = λ_α` (the rank-location theorem pays the bulk exit and permits the
simultaneous assertion at the selected energies; the roots avoid exterior poles almost
surely) and used in the proof of the physical real-loop proposition (the certificate gives
`m_E(0) = m_sc(E) + O(W^{-1+ε})`).

* `certErr_le_of_good` (deterministic): off the crowding and norm events, at a nonpole bulk
  energy `E` within `h` of a grid energy `e` whose truncated certificate is `≤ u`:
  `certErr(E) ≤ u + gridLip · h + 4/(W s √κ)`.
* `gridLip_mul_le`: the arithmetic `gridLip(s, κ, nW, W^{-(D+5)}) · W^{-(2(D+5)+6)} ≤ K₁ W^{-2}`.
* **`selectedCertificate_holds`**: `SelectedCertificateStatement` from `MatchedTracesContract`
  (through `gridCertificateHat_le`), `PhysicalBlockConditionalCount` (crowding and pole null set
  at grid energies), `CoareaContract` (`regular_ae`: the selected energies are not exterior
  poles) and `RankLocationContract` (bulk exit). Bulk margin `κ = π min(ϑ, 1/4)/4`; truncation
  radius `ε₀ = W^{-(D+5)}`, grid `bulkGrid κ W^{-(2(D+5)+6)}`; small `W < 2` exceptional.
* **`selectedResolvent_of_trace`**: `SelectedResolventStatement` from the same contracts and the
  named `SelectedTraceStatement` (items (3)–(4)).
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
open BlockBand.LocalWindow BlockBand.LocalWindow.ProofCertificate
open scoped ENNReal

/-!
## Pointwise transfer
-/

/-- **The certificate at a selected energy, pointwise**: off the crowding event
at radius `ε₀` on `[-2, 2]` and the norm event, for Hermitian `H_R`, `V`, a nonpole energy
`E ∈ bulkInterval κ` and a grid energy `e ∈ bulkInterval κ` with `|E - e| ≤ h` and
`certErrHat(e) ≤ u`: `certErr(E) ≤ u + gridLip(s, κ, nW, ε₀) h + 4/(W s √κ)`. -/
theorem certErr_le_of_good {p : Parameters} {i : ZMod p.n} {x : SplitState p i × PairMatrix p i}
    {κ ε₀ h u CG : ℝ} (hκ : 0 < κ) (hε₀ : 0 < ε₀) (hs : 0 < splitS p)
    (hH : x.1.1.IsHermitian) (hV : x.1.2.2.IsHermitian)
    (hcrowd : x ∉ ProofCrowding.crowdingEvent p i ε₀ 2)
    (hent : x ∉ ProofNormEvent.entryEvent p i) (hgue : x ∉ ProofNormEvent.gueEvent p i CG)
    {E e : ℝ} (hE : E ∈ bulkInterval κ) (he : e ∈ bulkInterval κ) (hEe : |E - e| ≤ h)
    (hdet : (x.1.1 - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0)
    (hcert : certErrHat ε₀ p i x.1 e ≤ u) :
    certErr p i x.1 E ≤ u + gridLip (splitS p) κ ((p.n : ℝ) * p.W) ε₀ * h +
      4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) := by
  obtain ⟨hC, hC', -⟩ := ProofNormEvent.norm_bounds_of_not_mem hent hgue
  have hgrid := certErrHat_le_grid x.1 hH hV hε₀ (by positivity) hκ hC hC' hs hE he
  have hE2 : |E| ≤ 2 := by obtain ⟨h1, h2⟩ := hE; rw [abs_le]; constructor <;> linarith
  have hnear := ProofCrowding.nearSet_card_le_one_of_not_mem hcrowd hH hE2
  have him := sqrt_le_abs_matchedA_im hκ hE
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have himne : (matchedA E).im ≠ 0 := by
    intro h0; rw [h0, abs_zero] at him; linarith
  have hrev := certErr_le_certErrHat (ε := ε₀) x.1 hH hV hdet hnear himne hs
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hk : 2 / ((p.W : ℝ) * (splitS p * |(matchedA E).im|)) ≤
      4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h' : Real.sqrt κ ≤ 2 * |(matchedA E).im| := by linarith
    have := mul_le_mul_of_nonneg_left h' (mul_pos hW hs).le
    nlinarith
  have hgl : 0 ≤ gridLip (splitS p) κ ((p.n : ℝ) * p.W) ε₀ := by unfold gridLip; positivity
  have hgh : gridLip (splitS p) κ ((p.n : ℝ) * p.W) ε₀ * |E - e| ≤
      gridLip (splitS p) κ ((p.n : ℝ) * p.W) ε₀ * h := mul_le_mul_of_nonneg_left hEe hgl
  linarith

/-- **Grid arithmetic**: with `ε₀ = W^{-(D+5)}` and `h = W^{-(2(D+5)+6)}`, `n ≤ TW`:
`gridLip(s, κ, nW, ε₀) h ≤ K₁ W^{-2}`, `K₁ = 2 h_s⁻² (T² + 1 + s L_a) + L_a`. -/
theorem gridLip_mul_le {s κ T W n D : ℝ} (hs : 0 < s) (hκ : 0 < κ) (hW1 : 1 ≤ W) (hn0 : 0 ≤ n)
    (hn : n ≤ T * W) (hD : 0 ≤ D) :
    gridLip s κ (n * W) (W ^ (-(D + 1 + 4))) * W ^ (-(2 * (D + 5) + 6)) ≤
      (2 * (s * (Real.sqrt κ / 2))⁻¹ * (s * (Real.sqrt κ / 2))⁻¹ *
          (T ^ 2 + 1 + s * (1 / 2 + 2 / Real.sqrt κ)) + (1 / 2 + 2 / Real.sqrt κ)) *
        W ^ (-2 : ℝ) := by
  have hW0 : 0 < W := by linarith
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
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
  set Q := (s * (Real.sqrt κ / 2))⁻¹ with hQ
  set La := 1 / 2 + 2 / Real.sqrt κ with hLa
  have hQ0 : 0 ≤ Q := by positivity
  have hLa0 : 0 ≤ La := by positivity
  have hgl : gridLip s κ (n * W) ε₀ ≤
      (2 * Q * Q * (T ^ 2 + 1 + s * La) + La) * P := by
    unfold gridLip
    rw [← hQ, ← hLa]
    have h1 : (n * W) ^ 2 / ε₀ ^ 2 + 1 + s * La ≤ (T ^ 2 + 1 + s * La) * P := by
      have : 0 ≤ s * La := by positivity
      nlinarith
    have h2 : 2 * Q * Q * ((n * W) ^ 2 / ε₀ ^ 2 + 1 + s * La) ≤
        2 * Q * Q * ((T ^ 2 + 1 + s * La) * P) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : La ≤ La * P := le_mul_of_one_le_right hLa0 hP1
    nlinarith
  have hPh : P * W ^ (-(2 * (D + 5) + 6)) = W ^ (-2 : ℝ) := by
    rw [hP, ← Real.rpow_add hW0]; ring_nf
  have hh0 : 0 ≤ W ^ (-(2 * (D + 5) + 6)) := (Real.rpow_pos_of_pos hW0 _).le
  calc gridLip s κ (n * W) ε₀ * W ^ (-(2 * (D + 5) + 6))
      ≤ (2 * Q * Q * (T ^ 2 + 1 + s * La) + La) * P * W ^ (-(2 * (D + 5) + 6)) :=
        mul_le_mul_of_nonneg_right hgl hh0
    _ = _ := by rw [mul_assoc, hPh]

/-!
## The certificate statement
-/

/-- **`SelectedCertificateStatement`** from `MatchedTracesContract`,
`PhysicalBlockConditionalCount`, `CoareaContract`, `RankLocationContract`. -/
theorem selectedCertificate_holds (hMT : MatchedTracesContract)
    (hPBC : PhysicalBlockConditionalCount) (hCo : CoareaContract)
    (hRank : RankLocationContract) : SelectedCertificateStatement := by
  intro b T ϑ hϑ
  by_cases hb : 0 < b ∧ b < 1 / 2
  swap
  · refine ⟨1, one_pos, fun ε _ D _ => ⟨0, fun p hpb => ?_⟩⟩
    exact absurd ⟨hpb ▸ p.b_pos, hpb ▸ p.b_lt_half⟩ hb
  obtain ⟨hb0, hb1⟩ := hb
  set ϑ' := min ϑ (1 / 4) with hϑ'def
  have hϑ'0 : 0 < ϑ' := lt_min hϑ (by norm_num)
  have hϑ'4 : ϑ' ≤ 1 / 4 := min_le_right _ _
  have hϑ'1 : ϑ' < 1 / 2 := by linarith
  have hϑ'ϑ : ϑ' ≤ ϑ := min_le_left _ _
  set κ := Real.pi * ϑ' / 4 with hκdef
  have hκ : 0 < κ := by positivity
  have hκ2 : κ ≤ 2 := by
    have := Real.pi_le_four
    rw [hκdef]; nlinarith
  refine ⟨κ, hκ, fun ε hε D hD => ?_⟩
  set c₀ := min (1 - 2 * b) b with hc₀def
  have hc₀ : 0 < c₀ := lt_min (by linarith) hb0
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  obtain ⟨Ccr, hCcr0, hcr⟩ := splitLaw_crowding_le hPBC b T (D + 1) hb0 hb1 (by linarith)
  obtain ⟨CG, cG, hCG, hcG, hnorm⟩ := ProofNormEvent.normEvent_le
  obtain ⟨Cn, hCn0, hCn⟩ := ProofNormEvent.normBound_le_rpow T (D + 1) cG hcG
  obtain ⟨Cg, hCg0, hgrid⟩ := gridCertificateHat_le hMT hPBC b κ T hb0 hb1 hκ (ε / 2) (D + 1)
    (2 * (D + 5) + 6 + 3) (by positivity) (by linarith)
  obtain ⟨Crk, hCrk0, hrk⟩ :=
    splitLaw_rank_le hRank b T ϑ' κ (D + 1) hb0 hb1 hϑ'0 hϑ'1 hκ (by linarith)
  set Ctot := Ccr + Cn + Cg + Crk with hCtot
  have hCtot0 : 0 ≤ Ctot := by positivity
  set K₁ := 2 * (c₀ * (Real.sqrt κ / 2))⁻¹ * (c₀ * (Real.sqrt κ / 2))⁻¹ *
      (T ^ 2 + 1 + c₀ * (1 / 2 + 2 / Real.sqrt κ)) + (1 / 2 + 2 / Real.sqrt κ) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set Ccert := 1 + 8 / (c₀ * Real.sqrt κ) + K₁ with hCcert
  have hCcert0 : 0 ≤ Ccert := by positivity
  refine ⟨|T| * Ctot / 2 + |T| * 2 ^ (D + 1) / 2 + Ccert,
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
  have hneg : 0 ≤ (p.W : ℝ) ^ (-D) := (Real.rpow_pos_of_pos hW0 _).le
  have hA0 : 0 ≤ |T| * Ctot / 2 := by positivity
  have hB0 : 0 ≤ |T| * 2 ^ (D + 1) / 2 := by positivity
  by_cases hW2 : (p.W : ℝ) < 2
  · refine ⟨Set.univ, fun α => ?_, fun x hx => absurd (Set.mem_univ x) hx⟩
    refine (splitPairLaw_le_small hsplit α Set.univ hD.le hn hW2.le).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [abs_of_nonneg hT] at hA0 hB0 ⊢
    exact mul_le_mul_of_nonneg_right (by linarith) hneg
  push Not at hW2
  set ε₀ := (p.W : ℝ) ^ (-(D + 1 + 4)) with hε₀
  have hε₀0 : 0 < ε₀ := Real.rpow_pos_of_pos hW0 _
  set h := (p.W : ℝ) ^ (-(2 * (D + 5) + 6)) with hh
  have hh0 : 0 < h := Real.rpow_pos_of_pos hW0 _
  set Es := bulkGrid κ h with hEs
  have hEsb : ∀ e ∈ Es, e ∈ bulkInterval κ := fun e he => bulkGrid_mem hκ2 hh0.le he
  have hcard : (Es.card : ℝ) ≤ (p.W : ℝ) ^ (2 * (D + 5) + 6 + 3) := by
    refine (bulkGrid_card_le hκ.le hκ2 hh0).trans ?_
    have h4 : 4 / h = 4 * (p.W : ℝ) ^ (2 * (D + 5) + 6) := by
      rw [hh, Real.rpow_neg hW0.le, div_inv_eq_mul]
    have hM1 : 1 ≤ (p.W : ℝ) ^ (2 * (D + 5) + 6) := Real.one_le_rpow hW1 (by linarith)
    have h3 : (8 : ℝ) ≤ (p.W : ℝ) ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ (p.W : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hW2 3
    have hsp3 : (p.W : ℝ) ^ (2 * (D + 5) + 6 + 3) =
        (p.W : ℝ) ^ (2 * (D + 5) + 6) * (p.W : ℝ) ^ (3 : ℝ) := Real.rpow_add hW0 _ _
    rw [h4, hsp3]
    have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ (p.W : ℝ) ^ (2 * (D + 5) + 6))
    linarith
  set Ωg : Set (SplitState p i × PairMatrix p i) :=
    {x | x ∉ ProofCrowding.crowdingEvent p i ε₀ 2 ∧ ∃ e ∈ Es,
      (p.W : ℝ) ^ (-1 + ε / 2) + 4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) <
        certErrHat ε₀ p i x.1 e} with hΩg
  set Ω := ProofCrowding.crowdingEvent p i ε₀ 2 ∪
    (ProofNormEvent.entryEvent p i ∪ ProofNormEvent.gueEvent p i CG) ∪ Ωg ∪
    rankEvent p i ϑ' κ ∪ nullEvent p i with hΩ
  have hΩle : splitLaw p i Pω Ω ≤ ENNReal.ofReal (Ctot * (p.W : ℝ) ^ (-(D + 1))) := by
    have h1 := hcr p hpb hn model i Pω hsplit
    have h2 : splitLaw p i Pω (ProofNormEvent.entryEvent p i ∪ ProofNormEvent.gueEvent p i CG) ≤
        ENNReal.ofReal (Cn * (p.W : ℝ) ^ (-(D + 1))) :=
      (hnorm p model i Pω hsplit).trans (ENNReal.ofReal_le_ofReal (hCn p hn))
    have h3 := hgrid p hpb hn model i Pω hsplit Es hEsb hcard ε₀
    have h4 := hrk p hpb hn model i Pω hsplit
    have h5 := splitLaw_null_le hCo hsplit
    have hp : 0 ≤ (p.W : ℝ) ^ (-(D + 1)) := (Real.rpow_pos_of_pos hW0 _).le
    calc splitLaw p i Pω Ω
        ≤ splitLaw p i Pω (ProofCrowding.crowdingEvent p i ε₀ 2) +
            splitLaw p i Pω (ProofNormEvent.entryEvent p i ∪ ProofNormEvent.gueEvent p i CG) +
            splitLaw p i Pω Ωg + splitLaw p i Pω (rankEvent p i ϑ' κ) +
            splitLaw p i Pω (nullEvent p i) := by
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (Ccr * (p.W : ℝ) ^ (-(D + 1))) +
            ENNReal.ofReal (Cn * (p.W : ℝ) ^ (-(D + 1))) +
            ENNReal.ofReal (Cg * (p.W : ℝ) ^ (-(D + 1))) +
            ENNReal.ofReal (Crk * (p.W : ℝ) ^ (-(D + 1))) + 0 := by
          rw [h5]
          gcongr
      _ = ENNReal.ofReal (Ctot * (p.W : ℝ) ^ (-(D + 1))) := by
          rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; rw [hCtot]; ring
  refine ⟨Ω, fun α => ?_, fun x hx => ?_⟩
  · refine (splitPairLaw_le_of hsplit α hCtot0 hn hΩle).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_right ?_ hneg
    rw [abs_of_nonneg hT] at hA0 hB0 ⊢
    linarith
  have hcrowd : x ∉ ProofCrowding.crowdingEvent p i ε₀ 2 :=
    fun h => hx (Or.inl (Or.inl (Or.inl (Or.inl h))))
  have hent : x ∉ ProofNormEvent.entryEvent p i :=
    fun h => hx (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl h)))))
  have hgue : x ∉ ProofNormEvent.gueEvent p i CG :=
    fun h => hx (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr h)))))
  have hg : x ∉ Ωg := fun h => hx (Or.inl (Or.inl (Or.inr h)))
  have hrank : x ∉ rankEvent p i ϑ' κ := fun h => hx (Or.inl (Or.inr h))
  have hnull : x ∉ nullEvent p i := fun h => hx (Or.inr h)
  have hHV : x.1.1.IsHermitian ∧ x.1.2.2.IsHermitian := by
    by_contra h; exact hnull (Or.inl h)
  have hdet : ∀ α : Fin p.N, (x.1.1 -
      ((physicalOrderedEigenvalue p (assemble p i x.1 x.2) α : ℝ) : ℂ) •
        (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0 :=
    fun α h0 => hnull (Or.inr ⟨α, h0⟩)
  refine ⟨hHV.1, hHV.2, fun α hα => ?_⟩
  set E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α with hE
  have hα' := isBulkRank_mono hϑ'ϑ hα
  have hloc : |E - classicalLocation p α| ≤ κ := not_lt.mp fun h => hrank ⟨α, hα', h⟩
  have hcl := BlockBand.Window.Count.classicalLocation_mem_bulk p hϑ'0 hα'
  have hEκ : E ∈ bulkInterval κ := by
    obtain ⟨h1, h2⟩ := hcl
    rw [abs_le] at hloc
    have : Real.pi * ϑ' / 2 = 2 * κ := by rw [hκdef]; ring
    rw [this] at h1 h2
    exact ⟨by linarith, by linarith⟩
  refine ⟨hEκ, ?_⟩
  obtain ⟨e, heEs, hEe⟩ := exists_bulkGrid_near hh0 hEκ
  have he := hEsb e heEs
  have hcert_e : certErrHat ε₀ p i x.1 e ≤
      (p.W : ℝ) ^ (-1 + ε / 2) + 4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) :=
    not_lt.mp fun hlt => hg ⟨hcrowd, e, heEs, hlt⟩
  have hgood := certErr_le_of_good hκ hε₀0 hs hHV.1 hHV.2 hcrowd hent hgue hEκ he hEe
    (hdet α) hcert_e
  refine hgood.trans ?_
  -- arithmetic
  have hn0 : (0 : ℝ) ≤ p.n := by positivity
  have hgl := gridLip_mul_le (s := splitS p) (κ := κ) (T := T) hs hκ hW1 hn0 hn hD.le
  rw [hsp] at hgl ⊢
  rw [← hK₁] at hgl
  have hpe : 0 ≤ (p.W : ℝ) ^ (-1 + ε) := (Real.rpow_pos_of_pos hW0 _).le
  have hA : (p.W : ℝ) ^ (-1 + ε / 2) ≤ (p.W : ℝ) ^ (-1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hm1 : (p.W : ℝ) ^ (-1 : ℝ) ≤ (p.W : ℝ) ^ (-1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hm2 : (p.W : ℝ) ^ (-2 : ℝ) ≤ (p.W : ℝ) ^ (-1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hB : 4 / ((p.W : ℝ) * (c₀ * Real.sqrt κ)) = 4 / (c₀ * Real.sqrt κ) * (p.W : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]; field_simp
  have hB0 : 0 ≤ 4 / (c₀ * Real.sqrt κ) := by positivity
  rw [hB]
  have e1 : 4 / (c₀ * Real.sqrt κ) * (p.W : ℝ) ^ (-1 : ℝ) ≤
      4 / (c₀ * Real.sqrt κ) * (p.W : ℝ) ^ (-1 + ε) := mul_le_mul_of_nonneg_left hm1 hB0
  have e2 : K₁ * (p.W : ℝ) ^ (-2 : ℝ) ≤ K₁ * (p.W : ℝ) ^ (-1 + ε) :=
    mul_le_mul_of_nonneg_left hm2 hK₁0
  have e3 : Ccert * (p.W : ℝ) ^ (-1 + ε) ≤
      (|T| * Ctot / 2 + |T| * 2 ^ (D + 1) / 2 + Ccert) * (p.W : ℝ) ^ (-1 + ε) :=
    mul_le_mul_of_nonneg_right (by linarith) hpe
  have e4 : Ccert * (p.W : ℝ) ^ (-1 + ε) = (p.W : ℝ) ^ (-1 + ε) +
      4 / (c₀ * Real.sqrt κ) * (p.W : ℝ) ^ (-1 + ε) +
      4 / (c₀ * Real.sqrt κ) * (p.W : ℝ) ^ (-1 + ε) + K₁ * (p.W : ℝ) ^ (-1 + ε) := by
    rw [hCcert]; ring
  linarith

/-- **`SelectedResolventStatement` from the certificate inputs and the trace estimates**:
items (1)–(2) are proved here (`selectedCertificate_holds`, `selected_regular`); items (3)–(4)
are the named hypothesis `SelectedTraceStatement`. -/
theorem selectedResolvent_of_trace (hMT : MatchedTracesContract)
    (hPBC : PhysicalBlockConditionalCount) (hCo : CoareaContract)
    (hRank : RankLocationContract) (hTr : SelectedTraceStatement) :
    WeightedTrace.SelectedResolventStatement :=
  selectedResolvent_of_parts (selectedCertificate_holds hMT hPBC hCo hRank) hTr

end BlockBand.DeterminantScore.SelectedResolvent
