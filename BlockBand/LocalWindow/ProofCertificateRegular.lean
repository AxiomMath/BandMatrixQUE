module

public import BlockBand.LocalWindow.ProofCertificateTransfer
public import BlockBand.Palm.RegularityCertificate
public import BlockBand.Angular.FiberAngular

/-!
# The uniform pole certificate for `F̂` and its regularity

The pole certificate for the truncated residual `F̂` on an energy grid, and the uniform
regularity of the Dyson root that it implies, for the physical local-window lemma.

## Main results

* `gridCertificateHat_le`: the uniform pole certificate on a grid for `F̂`, off the crowding
  event, under the original split law. The hypotheses are `MatchedTracesContract` (its residual-pair
  field, through `gridCertificate_le`) and `PhysicalBlockConditionalCount`; hermiticity of `H_R` and
  `V` holds almost surely by `IsPairSplitting`.
* `norm_certificateChi_le` (deterministic): the one-trace certificate `χ` of the regularity
  certificate lemma for `F = F̂(e)`, `c = s`, `μ = ā` is bounded by `certErrHat`.
* `poleCertificate_regular` (deterministic): constants `ε_c, r, s₀, v₀ > 0` depending only on
  `b, κ` such that `certErrHat(e) ≤ ε_c` at `e ∈ bulkInterval κ` gives, for the canonical Dyson
  root `m` of `F̂(e)` at `s' ∈ [s - s₀, s]`, `|x - e| ≤ r`, `0 ≤ η ≤ 1`:
  `m = ⟨(F̂(e) - x - iη - s'm)⁻¹⟩` and `v₀ ≤ Im m ≤ v₀⁻¹` (from
  `BlockBand.Palm.certificate_full_uniform`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCertificate

open MeasureTheory ProbabilityTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.LocalWindow.ProofCount BlockBand.Coarea
open scoped ENNReal ComplexConjugate

/-!
## The certificate on the split space
-/

section Grid

variable {p : Parameters} {i : ZMod p.n}

/-- **The uniform pole certificate on a grid, for `F̂`.** Fixed `b, κ, T`,
`ε > 0`, `D ≥ 0`, `M` first; then `C`; uniformly in admissible `p`, models, adjacent pairs,
splitting laws, grids `Es ⊆ bulkInterval κ` with `|Es| ≤ W^M` and truncation radii `ε₀`: under
the original split law, off the crowding event at radius `ε₀` on `[-2, 2]`, some grid energy
has `certErrHat > W^{-1+ε} + 4/(W s √κ)` with probability at most `C W^{-D}`. -/
theorem gridCertificateHat_le (hMT : MatchedTracesContract)
    (hPBC : PhysicalBlockConditionalCount) (b κ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hκ : 0 < κ) (ε D M : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
        IsPairSplitting p i model (splitS p) Pω →
        ∀ Es : Finset ℝ, (∀ E ∈ Es, E ∈ bulkInterval κ) → (Es.card : ℝ) ≤ (p.W : ℝ) ^ M →
        ∀ ε₀ : ℝ,
          splitLaw p i Pω {x | x ∉ ProofCrowding.crowdingEvent p i ε₀ 2 ∧ ∃ E ∈ Es,
            (p.W : ℝ) ^ (-1 + ε) + 4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) <
              certErrHat ε₀ p i x.1 E} ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) := by
  obtain ⟨C, hC, hgrid⟩ := gridCertificate_le hMT b κ T hb hb' hκ ε D M hε hD
  refine ⟨C, hC, fun p hpb hn model i Pω hsplit Es hEs hcard ε₀ => ?_⟩
  have hs : 0 < splitS p := by
    rw [splitS_eq hpb]; exact lt_min (by linarith) hb
  have hprob : IsProbabilityMeasure (gueMeasure (PairSite p i) (pairTime p (splitS p))) := by
    unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
    infer_instance
  set A : Set (SplitState p i) :=
    {om | ∃ E ∈ Es, (p.W : ℝ) ^ (-1 + ε) < certErr p i om E}
  set N1 : Set (SplitState p i) := {om | ¬ (om.1.IsHermitian ∧ om.2.2.IsHermitian)}
  set P : Set (SplitState p i × PairMatrix p i) := ⋃ E ∈ Es,
    {x | (x.1.1 - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det = 0}
  have hN1 : Pω N1 = 0 := by
    have := BlockBand.Angular.FiberAngular.ae_hermitian_of_isPairSplitting p i hsplit
    rw [ae_iff] at this
    exact this
  have hP : splitLaw p i Pω P = 0 :=
    (measure_biUnion_null_iff (Es.countable_toSet)).mpr fun E _ =>
      splitLaw_pole_null hPBC hsplit E
  have hsub : {x : SplitState p i × PairMatrix p i |
      x ∉ ProofCrowding.crowdingEvent p i ε₀ 2 ∧ ∃ E ∈ Es,
        (p.W : ℝ) ^ (-1 + ε) + 4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) <
          certErrHat ε₀ p i x.1 E} ⊆ (A ×ˢ Set.univ ∪ N1 ×ˢ Set.univ) ∪ P := by
    rintro x ⟨hcrowd, E, hE, hlt⟩
    by_cases hP' : x ∈ P
    · exact Or.inr hP'
    by_cases hN : x.1 ∈ N1
    · exact Or.inl (Or.inr ⟨hN, trivial⟩)
    refine Or.inl (Or.inl ⟨⟨E, hE, ?_⟩, trivial⟩)
    simp only [N1, Set.mem_ofPred_eq, not_not] at hN
    have hdet : (x.1.1 - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0 :=
      fun h => hP' (Set.mem_biUnion hE h)
    have hEb := hEs E hE
    have hE2 : |E| ≤ 2 := by
      obtain ⟨h1, h2⟩ := hEb; rw [abs_le]; constructor <;> linarith
    have hnear := ProofCrowding.nearSet_card_le_one_of_not_mem hcrowd hN.1 hE2
    have him := sqrt_le_abs_matchedA_im hκ hEb
    have himne : (matchedA E).im ≠ 0 := by
      intro h0; rw [h0, abs_zero] at him
      have := Real.sqrt_pos.mpr hκ; linarith
    have hle := certErrHat_le (ε := ε₀) x.1 hN.1 hN.2 hdet hnear himne hs
    have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
    have hk : 2 / ((p.W : ℝ) * (splitS p * |(matchedA E).im|)) ≤
        4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) := by
      have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 2 * ((p.W : ℝ) * (splitS p * Real.sqrt κ)) ≤
          4 * ((p.W : ℝ) * (splitS p * |(matchedA E).im|)) := by
        have h' : Real.sqrt κ ≤ 2 * |(matchedA E).im| := by linarith
        have := mul_le_mul_of_nonneg_left h' (mul_pos hW hs).le
        nlinarith
      linarith
    linarith
  have hA := hgrid p hpb hn model i Pω hsplit Es hEs hcard
  calc splitLaw p i Pω _ ≤ splitLaw p i Pω ((A ×ˢ Set.univ ∪ N1 ×ˢ Set.univ) ∪ P) :=
        measure_mono hsub
    _ ≤ splitLaw p i Pω (A ×ˢ Set.univ) + splitLaw p i Pω (N1 ×ˢ Set.univ) +
          splitLaw p i Pω P :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ = Pω A := by
        -- `Measure.prod_prod` holds for arbitrary sets
        rw [hP, add_zero]
        unfold splitLaw
        rw [Measure.prod_prod, Measure.prod_prod, hN1, zero_mul, add_zero,
          measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) := hA

end Grid

/-!
## From the block certificate to the one-trace certificate `χ`
-/

section Chi

variable {p : Parameters} {i : ZMod p.n}

/-- The trace over the pair is the sum of the two block traces. -/
theorem trace_eq_pairBlockTrace (M : PairMatrix p i) :
    M.trace = (p.W : ℂ) * (pairBlockTrace p i M i + pairBlockTrace p i M (i + 1)) := by
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  unfold pairBlockTrace
  rw [← mul_add, ← mul_assoc, mul_inv_cancel₀ hW, one_mul, ← Finset.sum_add_distrib]
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun x _ => ?_
  have hne := BlockBand.Angular.FiberAngular.self_ne_add_one p i
  have h1 : (1 : ZMod p.n) ≠ 0 := fun h1 => hne (by rw [h1, add_zero])
  rcases x.2 with h | h
  · simp [h, Matrix.diag, h1]
  · simp [h, Matrix.diag, h1]

/-- `‖a(E)‖ = 1` for `|E| ≤ 2`. -/
theorem norm_matchedA {E : ℝ} (hE : E ^ 2 ≤ 4) : ‖matchedA E‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  have h4 : Real.sqrt (4 - E ^ 2) * Real.sqrt (4 - E ^ 2) = 4 - E ^ 2 :=
    Real.mul_self_sqrt (by linarith)
  have : (matchedA E).re * (matchedA E).re + (matchedA E).im * (matchedA E).im = 1 := by
    simp only [matchedA]
    nlinarith
  rw [this, Real.sqrt_one]

/-- **`χ ≤ certErrHat`**: for Hermitian `V`, the one-trace certificate
`χ = ⟨(F̂(e) - e - s ā)⁻¹⟩ - ā` of the regularity certificate lemma (`c = s`, `μ = ā`) is
bounded by the block certificate error of `F̂`. -/
theorem norm_certificateChi_le (ε : ℝ) (om : SplitState p i) (hV : om.2.2.IsHermitian) (e : ℝ) :
    ‖BlockBand.Palm.certificateChi (truncF ε om.1 om.2.1 om.2.2 e) (splitS p) e
        (conj (matchedA e))‖ ≤ certErrHat ε p i om e := by
  set F := truncF ε om.1 om.2.1 om.2.2 e
  have hF : F.IsHermitian := isHermitian_truncF ε om.1 om.2.1 hV e
  set a := matchedA e
  set R := (F - (e : ℂ) • 1 - ((splitS p : ℂ) * a) • (1 : PairMatrix p i))⁻¹
  have hR : (F - (((e : ℂ) + (splitS p : ℂ) * conj a)) • (1 : PairMatrix p i))⁻¹ = Rᴴ := by
    rw [conjTranspose_nonsing_inv]
    congr 1
    rw [conjTranspose_sub, conjTranspose_sub, hF.eq, conjTranspose_smul, conjTranspose_smul,
      conjTranspose_one, sub_sub, ← add_smul]
    congr 2
    simp [Complex.conj_ofReal]
  have hcard : (Fintype.card (PairSite p i) : ℂ) = 2 * p.W := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have hchi : BlockBand.Palm.certificateChi F (splitS p) e (conj a) =
      conj (((pairBlockTrace p i R i - a) + (pairBlockTrace p i R (i + 1) - a)) / 2) := by
    unfold BlockBand.Palm.certificateChi BlockBand.Palm.certificateMatrixTrace
      BlockBand.Palm.certificateMatrixResolvent
    rw [hR, trace_conjTranspose, trace_eq_pairBlockTrace, hcard]
    rw [map_div₀, map_add, map_sub, map_sub]
    simp only [star_mul', Complex.star_def, map_natCast]
    field_simp
    simp [map_ofNat]
    ring
  rw [hchi, Complex.norm_conj, norm_div, Complex.norm_two]
  unfold certErrHat
  have h1 := norm_add_le (pairBlockTrace p i R i - a) (pairBlockTrace p i R (i + 1) - a)
  have h2 := le_max_left ‖pairBlockTrace p i R i - a‖ ‖pairBlockTrace p i R (i + 1) - a‖
  have h3 := le_max_right ‖pairBlockTrace p i R i - a‖ ‖pairBlockTrace p i R (i + 1) - a‖
  linarith

end Chi

/-!
## Uniform regularity from the certificate
-/

section Regular

/-- **Uniform regularity**, from `BlockBand.Palm.certificate_full_uniform`. Fixed `b, κ`
first; then constants `ε_c, r, s₀, v₀ > 0`; for every admissible `p` with `p.b = b`, split state
with Hermitian `V`, truncation radius `ε` and `e ∈ bulkInterval κ` with
`certErrHat ε p i ω e ≤ ε_c`: for every `s' ∈ [s - s₀, s]` (`s = splitS p`), `|x - e| ≤ r` and
`0 ≤ η ≤ 1`, the canonical Dyson root `m` of the spectrum of `F̂(e)` at `z = x + iη` and variance
`s'` solves `m = ⟨(F̂(e) - z - s'm)⁻¹⟩` and `v₀ ≤ Im m ≤ v₀⁻¹`. -/
theorem poleCertificate_regular (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hκ : 0 < κ) :
    ∃ εc r s₀ v₀ : ℝ, 0 < εc ∧ 0 < r ∧ 0 < s₀ ∧ 0 < v₀ ∧
      ∀ p : Parameters, p.b = b → ∀ (i : ZMod p.n) (om : SplitState p i)
        (hV : om.2.2.IsHermitian) (ε e : ℝ), e ∈ bulkInterval κ → certErrHat ε p i om e ≤ εc →
        ∀ s' : ℝ, splitS p - s₀ ≤ s' → s' ≤ splitS p → ∀ x : ℝ, |x - e| ≤ r →
        ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
          BlockBand.Palm.certificateCanonicalDyson
              (isHermitian_truncF ε om.1 om.2.1 hV e).eigenvalues s' ((x : ℂ) + Complex.I * η) =
            BlockBand.Palm.certificateMatrixTrace (truncF ε om.1 om.2.1 om.2.2 e)
              (((x : ℂ) + Complex.I * η) + s' * BlockBand.Palm.certificateCanonicalDyson
                (isHermitian_truncF ε om.1 om.2.1 hV e).eigenvalues s'
                  ((x : ℂ) + Complex.I * η)) ∧
          v₀ ≤ (BlockBand.Palm.certificateCanonicalDyson
              (isHermitian_truncF ε om.1 om.2.1 hV e).eigenvalues s'
                ((x : ℂ) + Complex.I * η)).im ∧
          (BlockBand.Palm.certificateCanonicalDyson
              (isHermitian_truncF ε om.1 om.2.1 hV e).eigenvalues s'
                ((x : ℂ) + Complex.I * η)).im ≤ v₀⁻¹ := by
  set c := min (1 - 2 * b) b
  have hc : 0 < c := lt_min (by linarith) hb
  have hc1 : c < 1 := (min_le_right _ _).trans_lt (by linarith)
  have hV0 : 0 < Real.sqrt κ / 2 := by have := Real.sqrt_pos.mpr hκ; linarith
  obtain ⟨εc, r, s₀, v₀, C, hεc, hr, hs₀, -, hv₀, -, h⟩ :=
    BlockBand.Palm.certificate_full_uniform.{0} hc hc1 hV0
  refine ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, fun p hpb i om hV ε e he hcert s' hs1 hs2 x hx η hη
    hη1 => ?_⟩
  have hsp : splitS p = c := splitS_eq hpb
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  have him := sqrt_le_abs_matchedA_im hκ he
  have himle : (matchedA e).im ≤ 0 := by
    rw [matchedA_im]; have := Real.sqrt_nonneg (4 - e ^ 2); linarith
  have hVμ : Real.sqrt κ / 2 ≤ (conj (matchedA e)).im := by
    rw [Complex.conj_im]; rw [abs_of_nonpos himle] at him; exact him
  have he2 : e ^ 2 ≤ 4 := by obtain ⟨h1, h2⟩ := he; nlinarith
  have hμ : ‖conj (matchedA e)‖ ≤ 1 := by rw [Complex.norm_conj, norm_matchedA he2]
  have hchi := (norm_certificateChi_le ε om hV e).trans hcert
  rw [hsp] at hchi hs1 hs2
  exact (h (PairSite p i) (truncF ε om.1 om.2.1 om.2.2 e) (isHermitian_truncF ε om.1 om.2.1 hV e)
    e (conj (matchedA e)) hVμ hμ hchi).1 s' hs1 hs2 x hx η hη hη1

end Regular

end BlockBand.LocalWindow.ProofCertificate
