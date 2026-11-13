module

public import BlockBand.Endpoints.Normalization.RegularEventNorm

/-!
# Regular prior event: constructors of the two contracts

The regular prior event is internal to the proof of the normalizer theorem (pair form, and its
one-block form). We prove
* `pairRegularEvent_of_inputs : MatchedTracesContract → PhysicalBlockConditionalCount →
  PairRegularEventContract`;
* `blockRegularEvent_of_inputs : MatchedTracesContract → PhysicalBlockConditionalCount →
  BlockRegularEventContract`.

Constants and quantifiers are as in the contracts: `b ∈ (0,1/2)`, `κ > 0`, `T` first; the
regularity constants `r₀, s₀, v₀` come from the deterministic certificate (`regularEvent_certificate`
at the fresh variance `c = min(b,1-2b)` resp. `1-2b` and the bulk `κ`) and are fixed before `D`; for
every `D > 0` the norm exponent is `A = 3(D+5)+5`; for every `η > 0` the width `W₀` is the maximum
of the trace-tail width at threshold `t = min(ε, η/C)` and order `q = D+2` and the norm-tail width.
The bad event is covered by (i) the `Pω`-null non-Hermitian event, (ii) the trace event
`t ≤ max_k |W⁻¹Tr P_k(K - s a)⁻¹ - a|` (pair; `MatchedTracesContract.residualPair`) resp.
`t ≤ |W⁻¹ Tr(z₀ - Σ)⁻¹ - a|` (block; `MatchedTracesContract.commonPort`), of probability
`≤ W^{-D}/2`, and (iii) the norm event, of probability `≤ W^{-D}/2` (pole bound from
`PhysicalBlockConditionalCount`, Gaussian first-moment tails). Off these, `χ ≤ t ≤ ε`, so the
certificate gives fresh regularity and `|m - conj a| ≤ C|χ| ≤ η`.

Other results used include `Palm.certificate_semicircle_full`, `Density.integral_norm_entry_le_two`
and `Coarea.PoleExclusion.ae_blocks_isHermitian`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Palm BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.Inputs (PhysicalBlockConditionalCount)
open scoped ENNReal NNReal ComplexConjugate

theorem regularEvent_half_add_half (x : ℝ) (hx : 0 ≤ x) :
    (0 : ℝ≥0∞) + ENNReal.ofReal (x / 2) + ENNReal.ofReal (x / 2) = ENNReal.ofReal x := by
  rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem regularEvent_abs_le_two {κ e : ℝ} (hκ : 0 < κ) (he : e ∈ bulkInterval κ) : |e| ≤ 2 :=
  abs_le.2 ⟨by linarith [he.1], by linarith [he.2]⟩

/-- **Constructor of `PairRegularEventContract`** (the regular event of the proof of the
normalizer theorem), from `MatchedTracesContract` and `PhysicalBlockConditionalCount`.
-/
theorem pairRegularEvent_of_inputs (hMT : MatchedTracesContract)
    (hPC : PhysicalBlockConditionalCount) : PairRegularEventContract := by
  intro b hb0 hb1 κ T hκ
  set c : ℝ := min b (1 - 2 * b)
  have hc : 0 < c := lt_min hb0 (by linarith)
  have hc1 : c < 1 := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨ε, r₀, s₀, v₀, C, hε, hC, hconst, hcert⟩ := regularEvent_certificate hc hc1 hκ
  refine ⟨r₀, s₀, v₀, hconst, fun D hD => ⟨3 * (D + 5) + 5, fun η hη => ?_⟩⟩
  set t : ℝ := min ε (η / C)
  have ht : 0 < t := lt_min hε (div_pos hη hC)
  obtain ⟨W₁, hW₁⟩ := regularEvent_pair_trace_tail hMT hb0 hb1 (T := T) hκ t ht D hD
  obtain ⟨W₂, hW₂⟩ := regularEvent_pair_norm_tail hPC hb0 hb1 T D hD
  refine ⟨max W₁ W₂, fun p hpb hW hn model i Pω hsplit σ e he => ?_⟩
  have hps : pairS p = c := regularEvent_pairS_eq p hpb
  set Btr : Set (SplitState p i) := {ω | t ≤ max
      ‖pairBlockTrace p i ((pairResidual p i ω e - ((pairS p : ℂ) * matchedA e) • 1)⁻¹) i -
        matchedA e‖
      ‖pairBlockTrace p i ((pairResidual p i ω e - ((pairS p : ℂ) * matchedA e) • 1)⁻¹)
        (i + 1) - matchedA e‖}
  set Bnb : Set (SplitState p i) :=
    {ω | ¬ NormBound (pairDeformation p i σ ω e) (3 * (D + 5) + 5)}
  set Bh : Set (SplitState p i) := {ω | ¬ (ω.1.IsHermitian ∧ ω.2.2.IsHermitian)}
  have hcover : {ω | ¬ IsPairRegular p i σ (3 * (D + 5) + 5) r₀ s₀ v₀ η e ω} ⊆
      Bh ∪ Btr ∪ Bnb := by
    intro ω hω
    by_contra hcon
    have hH : ω.1.IsHermitian ∧ ω.2.2.IsHermitian := by
      by_contra h; exact hcon (Or.inl (Or.inl h))
    have htr : max
        ‖pairBlockTrace p i ((pairResidual p i ω e - ((pairS p : ℂ) * matchedA e) • 1)⁻¹) i -
          matchedA e‖
        ‖pairBlockTrace p i ((pairResidual p i ω e - ((pairS p : ℂ) * matchedA e) • 1)⁻¹)
          (i + 1) - matchedA e‖ < t := by
      by_contra h; exact hcon (Or.inl (Or.inr (not_lt.mp h)))
    have hnb : NormBound (pairDeformation p i σ ω e) (3 * (D + 5) + 5) := by
      by_contra h; exact hcon (Or.inr h)
    apply hω
    have hchi := (regularEvent_pair_chi_le p i σ ω hH.1 hH.2 (pairS p) e).trans htr.le
    have hF := regularEvent_physicalCoareaF_isHermitian hH.1 ω.2.1 hH.2 e
    have hFσ : (pairDeformation p i σ ω e).IsHermitian := by
      unfold pairDeformation
      rw [Matrix.reindex_apply]
      exact hF.submatrix _
    have hNpos : 0 < Fintype.card (PairSite p i) := by
      rw [ContractClauses.card_pairSite]; exact Nat.mul_pos (by norm_num) p.W_pos
    rw [hps] at hchi
    obtain ⟨hreg, hdist⟩ := hcert _ hNpos _ hFσ e he (hchi.trans (min_le_left _ _))
    unfold IsPairRegular
    rw [hps]
    refine ⟨⟨hFσ, hnb, hreg⟩, hdist.trans ?_⟩
    calc C * ‖certificateChi (pairDeformation p i σ ω e) c e (conj (matchedA e))‖
        ≤ C * (η / C) := mul_le_mul_of_nonneg_left (hchi.trans (min_le_right _ _)) hC.le
      _ = η := by field_simp
  have hBh : Pω Bh = 0 := by
    have := PoleExclusion.ae_blocks_isHermitian hsplit
    rwa [ae_iff] at this
  have hBtr := hW₁ p hpb ((le_max_left _ _).trans hW) hn model i Pω hsplit e he
  have hBnb := hW₂ p hpb ((le_max_right _ _).trans hW) hn model i Pω hsplit σ e
  calc Pω {ω | ¬ IsPairRegular p i σ (3 * (D + 5) + 5) r₀ s₀ v₀ η e ω}
      ≤ Pω (Bh ∪ Btr ∪ Bnb) := measure_mono hcover
    _ ≤ Pω Bh + Pω Btr + Pω Bnb :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ 0 + ENNReal.ofReal ((p.W : ℝ) ^ (-D) / 2) + ENNReal.ofReal ((p.W : ℝ) ^ (-D) / 2) := by
        rw [hBh]; gcongr
    _ = ENNReal.ofReal ((p.W : ℝ) ^ (-D)) :=
        regularEvent_half_add_half _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **Constructor of `BlockRegularEventContract`** (the one-block regular event), from
`MatchedTracesContract` (field `commonPort`) and `PhysicalBlockConditionalCount`.
-/
theorem blockRegularEvent_of_inputs (hMT : MatchedTracesContract)
    (hPC : PhysicalBlockConditionalCount) : BlockRegularEventContract := by
  intro b hb0 hb1 κ T hκ
  set c : ℝ := 1 - 2 * b
  have hc : 0 < c := by simp only [c]; linarith
  have hc1 : c < 1 := by simp only [c]; linarith
  obtain ⟨ε, r₀, s₀, v₀, C, hε, hC, hconst, hcert⟩ := regularEvent_certificate hc hc1 hκ
  refine ⟨r₀, s₀, v₀, hconst, fun D hD => ⟨3 * (D + 5) + 5, fun η hη => ?_⟩⟩
  set t : ℝ := min ε (η / C)
  have ht : 0 < t := lt_min hε (div_pos hη hC)
  obtain ⟨W₁, hW₁⟩ := regularEvent_block_trace_tail hMT hb0 hb1 (T := T) hκ t ht D hD
  obtain ⟨W₂, hW₂⟩ := regularEvent_block_norm_tail hPC hb0 hb1 T D hD
  refine ⟨max W₁ W₂, fun p hpb hW hn model k Pω hsplit σ e he => ?_⟩
  have hpc : p.c = c := regularEvent_c_eq p hpb
  set Btr : Set (BlockState p k) := {ω | t ≤ ‖oneBlockTrace p k
      ((commonZ b e • 1 - ω.2ᴴ * (ω.1 - (e : ℂ) • 1)⁻¹ * ω.2)⁻¹) - matchedA e‖}
  set Bnb : Set (BlockState p k) :=
    {ω | ¬ NormBound (blockDeformation p k σ ω e) (3 * (D + 5) + 5)}
  set Bh : Set (BlockState p k) := {ω | ¬ ω.1.IsHermitian}
  have hcover : {ω | ¬ IsBlockRegular p k σ (3 * (D + 5) + 5) r₀ s₀ v₀ η e ω} ⊆
      Bh ∪ Btr ∪ Bnb := by
    intro ω hω
    by_contra hcon
    have hH : ω.1.IsHermitian := by
      by_contra h; exact hcon (Or.inl (Or.inl h))
    have htr : ‖oneBlockTrace p k
        ((commonZ b e • 1 - ω.2ᴴ * (ω.1 - (e : ℂ) • 1)⁻¹ * ω.2)⁻¹) - matchedA e‖ < t := by
      by_contra h; exact hcon (Or.inl (Or.inr (not_lt.mp h)))
    have hnb : NormBound (blockDeformation p k σ ω e) (3 * (D + 5) + 5) := by
      by_contra h; exact hcon (Or.inr h)
    apply hω
    have hchi : ‖certificateChi (blockDeformation p k σ ω e) p.c e (conj (matchedA e))‖ ≤ t := by
      rw [regularEvent_block_chi_eq p k σ ω hH hpb (regularEvent_abs_le_two hκ he)]
      exact htr.le
    have hF : (blockF p k ω e).IsHermitian := by
      unfold blockF
      exact regularEvent_physicalCoareaF_isHermitian hH ω.2 isHermitian_zero e
    have hFσ : (blockDeformation p k σ ω e).IsHermitian := by
      unfold blockDeformation
      rw [Matrix.reindex_apply]
      exact hF.submatrix _
    have hNpos : 0 < Fintype.card (BlockSite p k) := by
      rw [regularEvent_card_blockSite]; exact p.W_pos
    rw [hpc] at hchi
    obtain ⟨hreg, hdist⟩ := hcert _ hNpos _ hFσ e he (hchi.trans (min_le_left _ _))
    unfold IsBlockRegular
    rw [hpc]
    refine ⟨⟨hFσ, hnb, hreg⟩, hdist.trans ?_⟩
    calc C * ‖certificateChi (blockDeformation p k σ ω e) c e (conj (matchedA e))‖
        ≤ C * (η / C) := mul_le_mul_of_nonneg_left (hchi.trans (min_le_right _ _)) hC.le
      _ = η := by field_simp
  have hBh : Pω Bh = 0 := by
    have := regularEvent_ae_blockState_isHermitian hsplit
    rwa [ae_iff] at this
  have hBtr := hW₁ p hpb ((le_max_left _ _).trans hW) hn model k Pω hsplit e he
  have hBnb := hW₂ p hpb ((le_max_right _ _).trans hW) hn model k Pω hsplit σ e
  calc Pω {ω | ¬ IsBlockRegular p k σ (3 * (D + 5) + 5) r₀ s₀ v₀ η e ω}
      ≤ Pω (Bh ∪ Btr ∪ Bnb) := measure_mono hcover
    _ ≤ Pω Bh + Pω Btr + Pω Bnb :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ 0 + ENNReal.ofReal ((p.W : ℝ) ^ (-D) / 2) + ENNReal.ofReal ((p.W : ℝ) ^ (-D) / 2) := by
        rw [hBh]; gcongr
    _ = ENNReal.ofReal ((p.W : ℝ) ^ (-D)) :=
        regularEvent_half_add_half _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end BlockBand.Endpoints.Normalization
