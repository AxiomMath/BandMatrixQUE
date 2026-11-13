module

public import BlockBand.DeterminantScore.SelectedIBPHoldsGrid
public import BlockBand.DeterminantScore.SelectedLocalLawHolds

/-!
# `SelectedIBPStatement`: the Gaussian integration-by-parts estimate at the selected energies

Item (4) of `WeightedTrace.SelectedResolventStatement`, following the proof of the physical
real-loop proposition (Gaussian integration by parts gives `E_G Tr G_dR_η = -t E_G (Tr R_η)²`;
the averaged local law; Gaussian `L^p` Poincaré with `√t (d/η)^{1/2} η^{-1} = W^{9/10}`; the
grids and the infinite-parameter compression), with the energy grid and rank-one transfer of
the physical local-window lemma.

* `ibp_point`: the deterministic conclusion at a selected energy `E` with grid neighbour `e`:
  `|Tr G R_η + s d m_E(iη)²| ≤ B + c_G(2/η) + 2W c_G (c²/ε₀² + 1)h/η² + 3d(L(η + χ₀) + L_a h)`
  from the grid bound `|Tr G R_η(K̂_e) + s d ā(e)²| ≤ B`.
* **`selectedIBP_holds`**: `SelectedResolvent.SelectedIBPStatement`.
* **`selectedResolvent_holds`**: `WeightedTrace.SelectedResolventStatement` (items (1)–(3) from
  `SelectedLocalLaw.selectedResolvent_of_ibp`, item (4) from `selectedIBP_holds`).

Proof of `selectedIBP_holds`. As `SelectedLocalLaw.selectedLocalLaw_holds` (certificate event
`Ω_c` at `ε = 1/2`, crowding at `ε₀ = W^{-(D+5)}`, norm and null events, grid
`Es = bulkGrid κ h`, `h = W^{-(2(D+5)+6)}`, `|Es| ≤ W^{M_g}`), with the grid trace-failure event
replaced by `IBPBadEvent` at `η = W^{-3/5}`, `a = √3 W^{9/10}` (`a² η³ = 3`), `u = W^{9/10+ε}`,
`n = ⌈(M_g + D + 1)/ε⌉ + 1`: `splitLaw(IBPBadEvent) ≤ |Es| (C₀ √(3n) Q^{1/n})ⁿ W^{-εn} ≤
K W^{-(D+1)}` (`splitLaw_ibpBad_le`). Off the events the grid exterior is in `TraceGood e` and
`ibp_point` with the norm event `‖G‖ ≤ C_G` gives `≤ C W^{9/10+ε}`. Small `W`: `Ω` = everything.

Hypotheses: exactly `ExternalLocalGUE`, `MDEBranchIdentification`, `GaussianLpGradient`,
`PhysicalBlockConditionalCount`, `MatchedTracesContract`, `RankLocationContract`,
`CoareaContract`, and `LawBridge.PairGUELawBridgeStatement`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedIBPHolds

open MeasureTheory ProbabilityTheory Matrix Set BlockBand.Palm
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.LocalWindow BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofCertificate
open BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofPartOne
open BlockBand.DeterminantScore.SelectedResolvent BlockBand.DeterminantScore.SelectedLocalLaw
open BlockBand.DeterminantScore.SelectedIBP
open scoped ENNReal ComplexConjugate Matrix.Norms.L2Operator

local notation "TE" => Matrix.toEuclideanLin (𝕜 := ℂ)

section Point

variable {p : Parameters} {i : ZMod p.n}

/-- **The deterministic conclusion at one selected energy.** Let `H_R, V, G` be
Hermitian, `‖C‖, ‖C*‖ ≤ c`, `‖G‖ ≤ c_G`, `ε₀ > 0`, `s = splitS p = c₀ ≤ 1`,
`PairRegularBody c₀ (√κ/2) ε₁ δ_P L`, `0 < η ≤ δ_P`, `χ₀ ≤ ε₁`; `E, e ∈ bulkInterval κ` with
`|E - e| ≤ h`, `E` a nonpole energy with at most one eigenvalue of `H_R` within `ε₀`,
`certErr(E) ≤ χ₀`, and the grid bound `|Tr G R_η(K̂_e) + s d ā(e)²| ≤ B` (`d = 2W`). Then
`|Tr G R_η + s d m_E(iη)²| ≤ B + c_G(2/η) + 2W c_G (c²/ε₀² + 1)h/η² + 3d(L(η + χ₀) + L_a h)`,
`L_a = 1/2 + 2/√κ`. -/
theorem ibp_point (x : SplitState p i × PairMatrix p i) (hH : x.1.1.IsHermitian)
    (hV : x.1.2.2.IsHermitian) (hG : x.2.IsHermitian) {ε₀ c cG κ h η χ₀ ε₁ δP L c₀ B : ℝ}
    (hε₀ : 0 < ε₀) (hc : 0 ≤ c) (hcG : 0 ≤ cG) (hκ : 0 < κ)
    (hC : ∀ v, ‖TE x.1.2.1 v‖ ≤ c * ‖v‖) (hC' : ∀ w, ‖TE x.1.2.1ᴴ w‖ ≤ c * ‖w‖)
    (hGn : ∀ v, ‖TE x.2 v‖ ≤ cG * ‖v‖)
    (hsp : splitS p = c₀) (hs1 : splitS p ≤ 1)
    (hreg : PairRegularBody c₀ (Real.sqrt κ / 2) ε₁ δP L) (hL : 0 ≤ L)
    (hη : 0 < η) (hηδ : η ≤ δP) (hχ₁ : χ₀ ≤ ε₁) {E e : ℝ} (hE : E ∈ bulkInterval κ)
    (he : e ∈ bulkInterval κ) (hEe : |E - e| ≤ h)
    (hdet : (x.1.1 - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0)
    (hnear : (nearSet ε₀ hH E).card ≤ 1) (hcert : certErr p i x.1 E ≤ χ₀)
    (hbad : ‖(x.2 * res (hatK ε₀ x.1 e) η x.2).trace +
        (splitS p : ℂ) * ((2 * p.W : ℕ) : ℂ) * conj (matchedA e) ^ 2‖ ≤ B) :
    ‖(x.2 * (schurA p i x.1 x.2 E - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i))⁻¹).trace +
        (splitS p : ℂ) * ((2 * p.W : ℝ) : ℂ) *
          pairDyson p i (schurK0 p i x.1 E) (splitS p) ((η : ℂ) * Complex.I) ^ 2‖ ≤
      B + (cG * (2 / η) + 2 * p.W * (cG * ((c ^ 2 / ε₀ ^ 2 + 1) * h)) / η ^ 2) +
        3 * ((2 * p.W : ℕ) : ℝ) * (L * (η + χ₀) + (1 / 2 + 2 / Real.sqrt κ) * h) := by
  set dR : ℝ := ((2 * p.W : ℕ) : ℝ) with hdR
  have hd0 : 0 ≤ dR := Nat.cast_nonneg _
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hdC : ((2 * p.W : ℝ) : ℂ) = ((2 * p.W : ℕ) : ℂ) := by push_cast; ring
  -- the transfer of `Tr G R`
  have h1 := traceG_transfer x.1 x.2 hH hV hG hε₀ hc hcG hC hC' hGn (e := e) hdet hnear hη
  have hr : 2 * p.W * (cG * ((c ^ 2 / ε₀ ^ 2 + 1) * |E - e|)) / η ^ 2 ≤
      2 * p.W * (cG * ((c ^ 2 / ε₀ ^ 2 + 1) * h)) / η ^ 2 := by gcongr
  -- the reference energies
  have hμ : ‖conj (matchedA e) - conj (matchedA E)‖ ≤ (1 / 2 + 2 / Real.sqrt κ) * h := by
    rw [← map_sub, Complex.norm_conj]
    refine (norm_matchedA_sub_le hκ he hE).trans ?_
    rw [abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hEe (by positivity)
  -- the regularity package at `K₀(E)`
  have hK := WeightedTrace.schurK0_isHermitian hH hV E
  obtain ⟨hVμ, hμ1⟩ := conj_matchedA_bounds hκ hE
  obtain ⟨-, hμe⟩ := conj_matchedA_bounds hκ he
  have hchi : ‖certificateChi (schurK0 p i x.1 E) c₀ 0 (conj (matchedA E))‖ ≤ χ₀ := by
    rw [← hsp]; exact (norm_chi_le_certErr x.1 hH hV E).trans hcert
  have hδ0 : 0 ≤ δP := hη.le.trans hηδ
  have hzim : 0 ≤ ((η : ℂ) * Complex.I).im := by simp [hη.le]
  have hznorm : ‖(η : ℂ) * Complex.I‖ = η := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have hzδ : ‖(η : ℂ) * Complex.I‖ ≤ δP := by rw [hznorm]; exact hηδ
  obtain ⟨-, -, hnearE⟩ := pairDyson_near hreg hL hδ0 hK hVμ hμ1 hchi hχ₁ hzim hzδ
  have hm2 := ((hreg p i _ hK _ hVμ hμ1 (hchi.trans hχ₁)).1 _ hzim hzδ).2.1
  rw [hznorm] at hnearE
  rw [hsp] at hbad ⊢
  rw [hdC]
  set m := pairDyson p i (schurK0 p i x.1 E) c₀ ((η : ℂ) * Complex.I)
  set ae := conj (matchedA e)
  have hRE : (schurA p i x.1 x.2 E - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i))⁻¹ =
      res (schurK0 p i x.1 E) η x.2 := rfl
  rw [hRE]
  set X := (x.2 * res (schurK0 p i x.1 E) η x.2).trace
  set Y := (x.2 * res (hatK ε₀ x.1 e) η x.2).trace
  have heq : X + (c₀ : ℂ) * ((2 * p.W : ℕ) : ℂ) * m ^ 2 =
      (Y + (c₀ : ℂ) * ((2 * p.W : ℕ) : ℂ) * ae ^ 2) + (X - Y) +
        (c₀ : ℂ) * ((2 * p.W : ℕ) : ℂ) * ((m - ae) * (m + ae)) := by ring
  rw [heq]
  have hmae : ‖m - ae‖ ≤ L * (η + χ₀) + (1 / 2 + 2 / Real.sqrt κ) * h := by
    have e1 : m - ae = (m - conj (matchedA E)) + (conj (matchedA E) - ae) := by ring
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add hnearE ?_)
    rw [norm_sub_rev]; exact hμ
  have hmpa : ‖m + ae‖ ≤ 3 := (norm_add_le _ _).trans (by linarith)
  have hc0 : 0 < c₀ := hsp ▸ hs
  have hc1 : c₀ ≤ 1 := hsp ▸ hs1
  have n3 : ‖(c₀ : ℂ) * ((2 * p.W : ℕ) : ℂ) * ((m - ae) * (m + ae))‖ ≤
      3 * dR * (L * (η + χ₀) + (1 / 2 + 2 / Real.sqrt κ) * h) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0,
      Complex.norm_natCast]
    have hpos : 0 ≤ L * (η + χ₀) + (1 / 2 + 2 / Real.sqrt κ) * h :=
      (norm_nonneg _).trans hmae
    calc c₀ * dR * (‖m - ae‖ * ‖m + ae‖)
        ≤ 1 * dR * ((L * (η + χ₀) + (1 / 2 + 2 / Real.sqrt κ) * h) * 3) := by gcongr
      _ = 3 * dR * (L * (η + χ₀) + (1 / 2 + 2 / Real.sqrt κ) * h) := by ring
  have t1 := norm_add_le ((Y + (c₀ : ℂ) * ((2 * p.W : ℕ) : ℂ) * ae ^ 2) + (X - Y))
    ((c₀ : ℂ) * ((2 * p.W : ℕ) : ℂ) * ((m - ae) * (m + ae)))
  have t2 := norm_add_le (Y + (c₀ : ℂ) * ((2 * p.W : ℕ) : ℂ) * ae ^ 2) (X - Y)
  linarith

end Point

set_option maxHeartbeats 1600000 in

/-- **Item (4) of `SelectedResolventStatement`: the Gaussian integration-by-parts estimate at the
selected energies**: `SelectedIBPStatement`, i.e. for `b, T, ϑ > 0`, `ε, D > 0` a constant `C`
such that uniformly in `n ≤ TW`, models, pairs and splitting laws, an event `Ω` of every
pair-law probability `≤ C W^{-D}` has, outside it, at every `ϑ`-bulk selected energy `E = λ_α`,
`|Tr G_d R_η + s d m_E(iη)²| ≤ C W^{9/10+ε}` (`η = W^{-3/5}`, `d = 2W`). Inputs:
`ExternalLocalGUE`, `MDEBranchIdentification`, `GaussianLpGradient`,
`PhysicalBlockConditionalCount`, `MatchedTracesContract`, `CoareaContract`,
`RankLocationContract`, and the law bridge `PairGUELawBridgeStatement`. -/
theorem selectedIBP_holds (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (hLp : GaussianLpGradient)
    (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract) (hCo : CoareaContract)
    (hRank : RankLocationContract) : SelectedIBPStatement := by
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
  set n : ℕ := ⌈(M + D + 1) / ε⌉₊ + 1 with hndef
  have hn1 : 1 ≤ n := by omega
  have hεn : M + D + 1 ≤ ε * n := by
    have h1 : (M + D + 1) / ε ≤ ⌈(M + D + 1) / ε⌉₊ := Nat.le_ceil _
    have h2 : ((⌈(M + D + 1) / ε⌉₊ : ℕ) : ℝ) ≤ n := by rw [hndef]; push_cast; linarith
    have := (div_le_iff₀' hε).mp (h1.trans h2)
    linarith
  obtain ⟨N₀, C₀, hC₀, hibp⟩ := splitLaw_ibpBad_le hBridge hELG hMDE hLp hreg hV hL.le hκ le_rfl
    Aℓ Cn n hn1
  set Q : ℝ := yConst n + yConst (2 * n) + 1 with hQ
  have hQ0 : 0 ≤ Q := by
    have := yConst_nonneg hn1
    have := yConst_nonneg (show 1 ≤ 2 * n by omega)
    linarith
  set kc : ℝ := C₀ * Real.sqrt n * Real.sqrt 3 * Q ^ ((n : ℝ)⁻¹) with hkc
  have hkc0 : 0 ≤ kc := by positivity
  set Kc : ℝ := kc ^ (n : ℝ) with hKc
  have hKc0 : 0 ≤ Kc := Real.rpow_nonneg hkc0 _
  set La : ℝ := 1 / 2 + 2 / Real.sqrt κ with hLa
  have hLa0 : 0 ≤ La := by positivity
  set K₁ : ℝ := 2 * (c₀ * (Real.sqrt κ / 2))⁻¹ * (c₀ * (Real.sqrt κ / 2))⁻¹ *
      (T ^ 2 + 1 + c₀ * (1 / 2 + 2 / Real.sqrt κ)) + (1 / 2 + 2 / Real.sqrt κ) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set Cχ : ℝ := |Cc| + 4 / (c₀ * Real.sqrt κ) + K₁ + 1 with hCχ
  have hCχ0 : 0 < Cχ := by positivity
  set Cb : ℝ := 16 + 12 * L * (1 + Cχ) + 2 * CG + 2 * CG * (T ^ 2 + 1) + 6 * La with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set Cr : ℝ := Ccr + Cnb + Kc with hCr
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
  have hη1' : η ≤ 1 := hη1
  have hdR0 : 0 < dR := by linarith
  have hWd : W ≤ dR := by rw [hd2]; linarith
  have hℓ : dR ^ (1 / 10 : ℝ) / η ≤ dR := by
    have e1 : dR ^ (1 / 10 : ℝ) / η = dR ^ (1 / 10 : ℝ) * W ^ (3 / 5 : ℝ) := by
      rw [hη, div_eq_mul_inv, ← Real.rpow_neg hW0.le, neg_neg]
    rw [e1]
    calc dR ^ (1 / 10 : ℝ) * W ^ (3 / 5 : ℝ) ≤ dR ^ (1 / 10 : ℝ) * dR ^ (3 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hW0.le hWd (by norm_num))
            (Real.rpow_nonneg hdR0.le _)
      _ = dR ^ (1 / 10 + 3 / 5 : ℝ) := (Real.rpow_add hdR0 _ _).symm
      _ ≤ dR ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hdR1 (by norm_num)
      _ = dR := Real.rpow_one _
  have hdη : 1 ≤ dR * η := by
    have hWη : 2 * W * η = 2 * W ^ (2 / 5 : ℝ) := by
      rw [mul_assoc, hη, hmul]; norm_num
    have : 1 ≤ W ^ (2 / 5 : ℝ) := Real.one_le_rpow hW1 (by norm_num)
    rw [hd2, hWη]; linarith
  set a : ℝ := Real.sqrt 3 * W ^ (9 / 10 : ℝ) with ha
  have ha0 : 0 < a := by positivity
  have ha3 : 3 ≤ a ^ 2 * η ^ 3 := by
    have e1 : (W ^ (9 / 10 : ℝ)) ^ 2 = W ^ (9 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
    have e2 : η ^ 3 = W ^ (-(9 / 5) : ℝ) := by
      rw [hη, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
    have e3 : a ^ 2 * η ^ 3 = 3 := by
      rw [ha, mul_pow, Real.sq_sqrt (by norm_num), e1, e2, mul_assoc, ← Real.rpow_add hW0]
      norm_num
    rw [e3]
  set u : ℝ := W ^ (9 / 10 + ε) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hW0 _
  set B : ℝ := u + (5 * dR ^ (1 / 10 : ℝ) / η + 5) + 3 * dR * (L * (η + χ₀)) with hB
  -- the remaining exceptional event
  set Ωr : Set (SplitState p i × PairMatrix p i) :=
    ProofCrowding.crowdingEvent p i ε₀ 2 ∪
      (ProofNormEvent.entryEvent p i ∪ ProofNormEvent.gueEvent p i CG) ∪ partOneNullEvent p i ∪
      IBPBadEvent p i ε₀ Aℓ Cn χ₀ η B Es with hΩrdef
  have hΩr : splitLaw p i Pω Ωr ≤ ENNReal.ofReal (Cr * W ^ (-(D + 1))) := by
    have hw : 0 ≤ W ^ (-(D + 1)) := Real.rpow_nonneg hW0.le _
    have b1 := hcr p hpb hn model i Pω hsplit
    have b2 : splitLaw p i Pω (ProofNormEvent.entryEvent p i ∪ ProofNormEvent.gueEvent p i CG) ≤
        ENNReal.ofReal (Cnb * W ^ (-(D + 1))) :=
      (hnorm p model i Pω hsplit).trans (ENNReal.ofReal_le_ofReal (hCnb p hn))
    have b3 := splitLaw_partOneNull_eq_zero hCo hsplit
    have b4 : splitLaw p i Pω (IBPBadEvent p i ε₀ Aℓ Cn χ₀ η B Es) ≤
        ENNReal.ofReal (Kc * W ^ (-(D + 1))) := by
      refine (hibp p hpb model i Pω hsplit hNW ε₀ hε₀0 Es hEsb η χ₀ hη0 hηδ hη1 hχ₀0 hχε hdom
        hzb hℓ hdη a u B ha0 ha3 hu0 le_rfl).trans ?_
      have hWr : W ^ (9 / 10 : ℝ) / W ^ (9 / 10 + ε) = W ^ (-ε) := by
        rw [← Real.rpow_sub hW0]; ring_nf
      have hX : C₀ * Real.sqrt n * (a * Q ^ ((n : ℝ)⁻¹)) / u = kc * W ^ (-ε) := by
        rw [← hWr, hkc, ha, hudef]
        field_simp
      have hXn : (C₀ * Real.sqrt n * (a * Q ^ ((n : ℝ)⁻¹)) / u) ^ (n : ℝ) =
          Kc * W ^ (-(ε * n)) := by
        rw [hX, Real.mul_rpow hkc0 (Real.rpow_nonneg hW0.le _), ← Real.rpow_mul hW0.le, hKc]
        ring_nf
      rw [hXn, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have e1 : W ^ (-(ε * n)) ≤ W ^ (-(M + D + 1)) :=
        Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      have e2 : W ^ M * W ^ (-(M + D + 1)) = W ^ (-(D + 1)) := by
        rw [← Real.rpow_add hW0]; ring_nf
      have hp : 0 ≤ W ^ (-(ε * n)) := Real.rpow_nonneg hW0.le _
      calc (Es.card : ℝ) * (Kc * W ^ (-(ε * n))) = Kc * ((Es.card : ℝ) * W ^ (-(ε * n))) := by
            ring
        _ ≤ Kc * (W ^ M * W ^ (-(M + D + 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hcard e1 hp (Real.rpow_nonneg hW0.le _)) hKc0
        _ = Kc * W ^ (-(D + 1)) := by rw [e2]
    have n1 : 0 ≤ Ccr * W ^ (-(D + 1)) := mul_nonneg hCcr0 hw
    have n2 : 0 ≤ Cnb * W ^ (-(D + 1)) := mul_nonneg hCnb0 hw
    have s2 := union_ofReal_le (splitLaw p i Pω) n1 n2 b1 b2
    have s3 := union_ofReal_le (splitLaw p i Pω) (add_nonneg n1 n2) le_rfl s2
      (by rw [b3]; exact bot_le)
    have s4 := union_ofReal_le (splitLaw p i Pω)
      (add_nonneg (add_nonneg n1 n2) le_rfl) (mul_nonneg hKc0 hw) s3 b4
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
  have hbad : ‖(x.2 * res (hatK ε₀ x.1 e) η x.2).trace +
      (splitS p : ℂ) * ((2 * p.W : ℕ) : ℂ) * conj (matchedA e) ^ 2‖ ≤ B :=
    not_lt.mp fun hlt => hxbad ⟨e, heEs, hgood, hlt⟩
  have hGn : ∀ v, ‖TE x.2 v‖ ≤ CG * ‖v‖ := by
    have hGn' : ‖x.2‖ ≤ CG := by by_contra h'; exact hxgue (lt_of_not_ge h')
    intro v
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hGn' (norm_nonneg v))
    rw [Matrix.l2_opNorm_def]
    exact ContinuousLinearMap.le_opNorm (LinearMap.toContinuousLinearMap (TE x.2)) v
  have hs1 : splitS p ≤ 1 := by rw [hsp]; exact hc₀1.le
  have hpt := ibp_point x hH hV hG hε₀0 hcn0 hCG.le hκ hC hC' hGn hsp hs1 hreg hL.le hη0 hηδ hχε
    hEκ he hEe (hdet α) hnear hcertχ hbad
  refine hpt.trans ?_
  -- the scale arithmetic
  obtain ⟨s1, s2, s3, s4, s5⟩ := scale_le hW1 hε
  rw [← hη] at s1 s2 s3 s4 s5
  set uG := W ^ ε / η with huG
  set v := W ^ (9 / 10 + ε) with hv
  have huv : uG ≤ v := by
    have : uG = W ^ (ε + 3 / 5) := by
      rw [huG, hη, div_eq_mul_inv, ← Real.rpow_neg hW0.le, neg_neg, ← Real.rpow_add hW0]
    rw [this]; exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hv1 : 1 ≤ v := Real.one_le_rpow hW1 (by positivity)
  have hℓv : dR ^ (1 / 10 : ℝ) / η ≤ 2 * v := by
    have e1 : dR ^ (1 / 10 : ℝ) / η = 2 ^ (1 / 10 : ℝ) * W ^ (1 / 10 + 3 / 5 : ℝ) := by
      rw [hd2, Real.mul_rpow (by norm_num) hW0.le, hη, div_eq_mul_inv, ← Real.rpow_neg hW0.le,
        neg_neg, mul_assoc, ← Real.rpow_add hW0]
    have h2r : (2 : ℝ) ^ (1 / 10 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 10 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h3 : W ^ (1 / 10 + 3 / 5 : ℝ) ≤ v := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    rw [e1]
    exact mul_le_mul h2r h3 (Real.rpow_nonneg hW0.le _) (by norm_num)
  have hr := grid_r_le hW1 hn0 hn hD.le
  rw [← hε₀, ← hh, ← hcn] at hr
  have hT2 : 0 ≤ T ^ 2 + 1 := by positivity
  have hCGp : 0 ≤ CG := hCG.le
  have hLp' : 0 ≤ L := hL.le
  have k1 : 5 * dR ^ (1 / 10 : ℝ) / η ≤ 10 * v := by
    rw [mul_div_assoc]; linarith
  have k3 : 3 * dR * (L * (η + χ₀)) ≤ 6 * L * (1 + Cχ) * uG := by
    rw [hd2, hχ₀]
    have e1 : 3 * (2 * W) * (L * (η + Cχ * W ^ (-(1 / 2 : ℝ)))) =
        6 * L * (W * η) + 6 * L * Cχ * (W * W ^ (-(1 / 2 : ℝ))) := by ring
    rw [e1]
    have a1 : 6 * L * (W * η) ≤ 6 * L * uG := mul_le_mul_of_nonneg_left s3 (by positivity)
    have a2 : 6 * L * Cχ * (W * W ^ (-(1 / 2 : ℝ))) ≤ 6 * L * Cχ * uG :=
      mul_le_mul_of_nonneg_left s4 (by positivity)
    linarith [a1, a2]
  have k4 : CG * (2 / η) ≤ 2 * CG * uG := by
    have : 2 / η ≤ 2 * uG := by rw [div_eq_mul_one_div]; linarith
    calc CG * (2 / η) ≤ CG * (2 * uG) := mul_le_mul_of_nonneg_left this hCGp
      _ = 2 * CG * uG := by ring
  have k5 : 2 * W * (CG * ((cn ^ 2 / ε₀ ^ 2 + 1) * h)) / η ^ 2 ≤ 2 * CG * (T ^ 2 + 1) * uG := by
    calc 2 * W * (CG * ((cn ^ 2 / ε₀ ^ 2 + 1) * h)) / η ^ 2
        ≤ 2 * W * (CG * ((T ^ 2 + 1) * W ^ (-2 : ℝ))) / η ^ 2 := by gcongr
      _ = 2 * CG * (T ^ 2 + 1) * (W * W ^ (-2 : ℝ) / η ^ 2) := by ring
      _ ≤ 2 * CG * (T ^ 2 + 1) * uG := by gcongr
  have k6 : 3 * dR * (L * (η + χ₀) + La * h) ≤ 6 * L * (1 + Cχ) * uG + 6 * La * uG := by
    have e1 : 3 * dR * (L * (η + χ₀) + La * h) = 3 * dR * (L * (η + χ₀)) + 3 * dR * (La * h) := by
      ring
    rw [e1]
    have : 3 * dR * (La * h) ≤ 6 * La * uG := by
      rw [hd2]
      have : 3 * (2 * W) * (La * h) ≤ 6 * La * (W * W ^ (-2 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hhW (by positivity : (0 : ℝ) ≤ 6 * W * La)
        linarith
      exact this.trans (mul_le_mul_of_nonneg_left s5 (by positivity))
    linarith
  have huG0 : 0 ≤ uG := by positivity
  have hsum : B + (CG * (2 / η) + 2 * W * (CG * ((cn ^ 2 / ε₀ ^ 2 + 1) * h)) / η ^ 2) +
      3 * dR * (L * (η + χ₀) + La * h) ≤ Cb * v := by
    have hc1 : 0 ≤ 12 * L * (1 + Cχ) + 2 * CG + 2 * CG * (T ^ 2 + 1) + 6 * La := by positivity
    have hcu := mul_le_mul_of_nonneg_left huv hc1
    have eCb : Cb * v = 16 * v + (12 * L * (1 + Cχ) + 2 * CG + 2 * CG * (T ^ 2 + 1) + 6 * La) * v := by
      rw [hCb]; ring
    have eB : B = v + (5 * dR ^ (1 / 10 : ℝ) / η + 5) + 3 * dR * (L * (η + χ₀)) := hB
    rw [eCb, eB]
    linarith [k1, k3, k4, k5, k6, hcu, hv1]
  have hfin : Cb * v ≤ (|Cc| + |T| * Cr / 2 + |T| * W₀ ^ (D + 1) / 2 + Cb) * v := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    have := abs_nonneg Cc
    linarith
  rw [← hLa]
  exact hsum.trans hfin

/-- **`SelectedResolventStatement`**: items (1)–(3) from
`SelectedLocalLaw.selectedResolvent_of_ibp`, item (4) from `selectedIBP_holds`. Inputs: exactly
`ExternalLocalGUE`, `MDEBranchIdentification`, `GaussianLpGradient`,
`PhysicalBlockConditionalCount`, `MatchedTracesContract`, `RankLocationContract`,
`CoareaContract` and the law bridge `PairGUELawBridgeStatement`. -/
theorem selectedResolvent_holds (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (hLp : GaussianLpGradient)
    (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract) (hCo : CoareaContract)
    (hRank : RankLocationContract) : WeightedTrace.SelectedResolventStatement :=
  selectedResolvent_of_ibp hBridge hELG hMDE hPBC hMT hCo hRank
    (selectedIBP_holds hBridge hELG hMDE hLp hPBC hMT hCo hRank)

end BlockBand.DeterminantScore.SelectedIBPHolds
