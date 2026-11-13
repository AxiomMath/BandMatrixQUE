module

public import BlockBand.DeterminantScore.WeightedTrace
public import BlockBand.DeterminantScore.SelectedResolventRegular
public import BlockBand.LocalWindow.ProofPairLaw

/-!
# `SelectedResolventStatement` from the selected-energy certificate and the trace estimates

The statement splits into two named sub-statements, each in the event format of
`SelectedResolventStatement` (one exceptional event of every pair-law probability `≤ C W^{-D}`
outside which the estimates hold at every selected bulk energy `E = λ_α`):

* **`SelectedCertificateStatement`** (the uniform pole certificate at the selected energies;
  rank location pays the bulk exit): for
  fixed `b, T, ϑ` a bulk interval `bulkInterval κ` such that, off the event, `H_R` and `V` are
  Hermitian and every selected energy lies in `bulkInterval κ` with block certificate
  `certErr(E) = max_{k=i,i+1} |W⁻¹ Tr P_k (K₀(E) - s a)⁻¹ - a| ≤ C W^{-1+ε}`.
* **`SelectedTraceStatement`**: the averaged local law
  `|Tr R_η - d m_E(iη)| ≤ C W^ε/η` and `|Tr G_d R_η + s d m_E(iη)²| ≤ C W^{9/10+ε}`
  (Gaussian integration by parts and `L^p` Poincaré on the energy and rank-one grids).

**`selectedResolvent_of_parts`**: the two sub-statements imply `SelectedResolventStatement`.
The regularity, centre and certificate items are deduced deterministically from the
certificate by `selected_regular` (the regularity certificate lemma), with `δ, C₀` depending only on
`b` and `κ = κ(b, T, ϑ)`; small `W` (where `η > δ` or the certificate is not below the
regularity threshold) are exceptional (`Ω = everything`, `splitPairLaw_le_small`).

Also: `norm_chi_le_certErr` (the one-trace certificate `χ` of `K₀(E)` at `μ = ā` is bounded by
the block certificate), `splitPairLaw_le_small`, `rpow_neg_le_of_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedResolvent

open MeasureTheory ProbabilityTheory Matrix Set BlockBand.Palm
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.LocalWindow BlockBand.LocalWindow.ProofCertificate
open scoped NNReal ENNReal ComplexConjugate

/-!
## The two sub-statements
-/

/-- **The certificate at the selected energies** (the uniform pole certificate, with rank location). `b, T, ϑ` first; then a bulk margin `κ > 0`; then for
`ε, D > 0` a constant `C`; uniformly in `4 ≤ n ≤ TW`, models, pairs and splitting laws there is
an event `Ω` of every pair-law probability `≤ C W^{-D}` outside which `H_R`, `V` are Hermitian
and every `ϑ`-bulk selected energy `E = λ_α` lies in `bulkInterval κ` with
`certErr p i ω E ≤ C W^{-1+ε}`. -/
def SelectedCertificateStatement : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
    ∃ κ : ℝ, 0 < κ ∧
      ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D →
        ∃ C : ℝ, ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
          ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
            IsPairSplitting p i model (splitS p) Pω →
              ∃ Ω : Set (SplitState p i × PairMatrix p i),
                (∀ α : Fin p.N, splitPairLaw p i α Pω Ω ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
                ∀ x ∉ Ω, x.1.1.IsHermitian ∧ x.1.2.2.IsHermitian ∧
                  ∀ α : Fin p.N, IsBulkRank p ϑ α →
                    physicalOrderedEigenvalue p (assemble p i x.1 x.2) α ∈ bulkInterval κ ∧
                    certErr p i x.1 (physicalOrderedEigenvalue p (assemble p i x.1 x.2) α) ≤
                      C * (p.W : ℝ) ^ (-1 + ε)

/-- **The trace estimates at the selected energies**: the averaged local law
`|Tr R_η - d m_E(iη)| ≤ C W^ε/η` and the Gaussian integration-by-parts estimate
`|Tr G_dR_η + s d m_E(iη)²| ≤ C W^{9/10+ε}`, in the format and with the notation
of `WeightedTrace.SelectedResolventStatement` (its last two items). -/
def SelectedTraceStatement : Prop :=
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
                    C * (p.W : ℝ) ^ ε / η ∧
                  ‖(x.2 * Rη).trace + (s : ℂ) * ((2 * p.W : ℝ) : ℂ) *
                      pairDyson p i K s ((η : ℂ) * Complex.I) ^ 2‖ ≤
                    C * (p.W : ℝ) ^ (9 / 10 + ε)

/-!
## Deterministic tools
-/

section Tools

variable {p : Parameters} {i : ZMod p.n}

/-- **`χ ≤ certErr`**: for Hermitian `H_R`, `V`, the one-trace certificate
`χ = ⟨(K₀(E) - s ā)⁻¹⟩ - ā` of the regularity certificate lemma (`c = s`, `μ = ā`, at `z = 0`) is
bounded by the block certificate of the residual `K₀(E) = F(E) - E`. -/
theorem norm_chi_le_certErr (om : SplitState p i) (hH : om.1.IsHermitian)
    (hV : om.2.2.IsHermitian) (E : ℝ) :
    ‖certificateChi (schurK0 p i om E) (splitS p) 0 (conj (matchedA E))‖ ≤ certErr p i om E := by
  set K := schurK0 p i om E with hKdef
  have hK : K.IsHermitian := WeightedTrace.schurK0_isHermitian hH hV E
  set a := matchedA E
  set R := (K - ((splitS p : ℂ) * a) • (1 : PairMatrix p i))⁻¹ with hRdef
  have hR : (K - (((0 : ℝ) : ℂ) + (splitS p : ℂ) * conj a) • (1 : PairMatrix p i))⁻¹ = Rᴴ := by
    rw [hRdef, conjTranspose_nonsing_inv]
    congr 1
    rw [conjTranspose_sub, hK.eq, conjTranspose_smul, conjTranspose_one]
    congr 2
    simp [Complex.conj_ofReal]
  have hcard : (Fintype.card (PairSite p i) : ℂ) = 2 * p.W := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have hchi : certificateChi K (splitS p) 0 (conj a) =
      conj (((pairBlockTrace p i R i - a) + (pairBlockTrace p i R (i + 1) - a)) / 2) := by
    unfold certificateChi certificateMatrixTrace certificateMatrixResolvent
    rw [hR, trace_conjTranspose, trace_eq_pairBlockTrace, hcard]
    rw [map_div₀, map_add, map_sub, map_sub]
    simp only [star_mul', Complex.star_def, map_natCast]
    field_simp
    simp [map_ofNat]
    ring
  rw [hchi, Complex.norm_conj, norm_div, Complex.norm_two]
  have hres : pairResidual p i om E = K := rfl
  unfold certErr
  rw [hres]
  have h1 := norm_add_le (pairBlockTrace p i R i - a) (pairBlockTrace p i R (i + 1) - a)
  have h2 := le_max_left ‖pairBlockTrace p i R i - a‖ ‖pairBlockTrace p i R (i + 1) - a‖
  have h3 := le_max_right ‖pairBlockTrace p i R i - a‖ ‖pairBlockTrace p i R (i + 1) - a‖
  linarith

/-- `W ≥ t^{-1/a}` gives `W^{-a} ≤ t`. -/
theorem rpow_neg_le_of_le {a t W : ℝ} (ha : 0 < a) (ht : 0 < t) (hW : t ^ (-1 / a) ≤ W) :
    W ^ (-a) ≤ t := by
  have h0 : 0 < t ^ (-1 / a) := Real.rpow_pos_of_pos ht _
  calc W ^ (-a) ≤ (t ^ (-1 / a)) ^ (-a) := Real.rpow_le_rpow_of_nonpos h0 hW (by linarith)
    _ = t := by
        rw [← Real.rpow_mul ht.le, show -1 / a * -a = 1 by field_simp, Real.rpow_one]

/-- **Small `W` are exceptional**: if `n ≤ TW` and `W ≤ W₀`, every set has pair-law probability
at most `(T W₀^{D+1}/2) W^{-D}`. -/
theorem splitPairLaw_le_small {model : p.GaussianRingModel} {Pω : Measure (SplitState p i)}
    (hPω : IsPairSplitting p i model (splitS p) Pω) (α : Fin p.N)
    (Ω : Set (SplitState p i × PairMatrix p i)) {T D W₀ : ℝ} (hD : 0 ≤ D)
    (hn : (p.n : ℝ) ≤ T * (p.W : ℝ)) (hW : (p.W : ℝ) ≤ W₀) :
    splitPairLaw p i α Pω Ω ≤ ENNReal.ofReal (T * W₀ ^ (D + 1) / 2 * (p.W : ℝ) ^ (-D)) := by
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hT : 0 ≤ T := by
    have : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
    by_contra h
    push Not at h
    nlinarith
  have hprob := PhysicalColumn.isProbabilityMeasure_gue (PairSite p i) (pairTime p (splitS p))
  have huniv : splitLaw p i Pω Set.univ = 1 := by
    unfold splitLaw
    rw [← Set.univ_prod_univ, Measure.prod_prod, ScoreMoments.PairRow.splitLaw_univ hPω,
      measure_univ, one_mul]
  refine (splitPairLaw_le hPω α Ω).trans ?_
  calc ENNReal.ofReal ((p.n : ℝ) / 2) * splitLaw p i Pω Ω
      ≤ ENNReal.ofReal ((p.n : ℝ) / 2) * 1 := by
        gcongr; rw [← huniv]; exact measure_mono (Set.subset_univ _)
    _ = ENNReal.ofReal ((p.n : ℝ) / 2) := mul_one _
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hWD : (p.W : ℝ) = (p.W : ℝ) ^ (D + 1) * (p.W : ℝ) ^ (-D) := by
          rw [← Real.rpow_add hW0, show D + 1 + -D = 1 by ring, Real.rpow_one]
        have hpow : (p.W : ℝ) ^ (D + 1) ≤ W₀ ^ (D + 1) :=
          Real.rpow_le_rpow hW0.le hW (by linarith)
        have hneg : 0 ≤ (p.W : ℝ) ^ (-D) := (Real.rpow_pos_of_pos hW0 _).le
        calc (p.n : ℝ) / 2 ≤ T * (p.W : ℝ) / 2 := by linarith
          _ = T * ((p.W : ℝ) ^ (D + 1) * (p.W : ℝ) ^ (-D)) / 2 := by rw [← hWD]
          _ ≤ T * (W₀ ^ (D + 1) * (p.W : ℝ) ^ (-D)) / 2 := by gcongr
          _ = _ := by ring

end Tools

/-!
## The reduction
-/

/-- **`SelectedResolventStatement` from its two named parts**: the
certificate at the selected energies gives the regularity, centre and certificate items through
`selected_regular`; the trace statement gives the two trace items; the exceptional event
is the union, or everything for small `W`. -/
theorem selectedResolvent_of_parts (hCert : SelectedCertificateStatement)
    (hTr : SelectedTraceStatement) : WeightedTrace.SelectedResolventStatement := by
  intro b T ϑ hϑ
  obtain ⟨κ, hκ, hCk⟩ := hCert b T ϑ hϑ
  by_cases hb : 0 < b ∧ b < 1 / 2
  swap
  · refine ⟨1, 1, one_pos, one_pos, fun ε _ D _ => ⟨0, fun p hpb => ?_⟩⟩
    exact absurd ⟨hpb ▸ p.b_pos, hpb ▸ p.b_lt_half⟩ hb
  obtain ⟨ε₁, δ, L, hε₁, hδ, hL, hreg⟩ := selected_regular b κ hb.1 hb.2 hκ
  refine ⟨δ, L, hδ, hL, fun ε hε D hD => ?_⟩
  set ε' := min ε (1 / 2) with hε'def
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨C1, hC1⟩ := hCk ε' hε'0 D hD
  obtain ⟨C2, hC2⟩ := hTr b T ϑ hϑ ε hε D hD
  set C1' := max C1 1 with hC1'def
  have hC1'0 : 0 < C1' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set W₀ := max (max ((ε₁ / C1') ^ (-1 / (1 - ε'))) (δ ^ (-1 / (3 / 5 : ℝ)))) 1 with hW₀def
  refine ⟨|T| * W₀ ^ (D + 1) / 2 + |C1| + |C2| + L * C1', fun p hpb hn model i Pω hsplit => ?_⟩
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hT : 0 ≤ T := by
    have : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
    by_contra h
    push Not at h
    nlinarith
  have hW₀1 : 1 ≤ W₀ := le_max_right _ _
  have hCsmall : 0 ≤ |T| * W₀ ^ (D + 1) / 2 := by positivity
  have hLC : 0 ≤ L * C1' := by positivity
  obtain ⟨Ω1, hΩ1, hgood1⟩ := hC1 p hpb hn model i Pω hsplit
  obtain ⟨Ω2, hΩ2, hgood2⟩ := hC2 p hpb hn model i Pω hsplit
  by_cases hWbig : W₀ < (p.W : ℝ)
  swap
  · push Not at hWbig
    refine ⟨Set.univ, fun α => ?_, fun x hx => absurd (Set.mem_univ x) hx⟩
    refine (splitPairLaw_le_small hsplit α Set.univ hD.le hn hWbig).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hneg : 0 ≤ (p.W : ℝ) ^ (-D) := (Real.rpow_pos_of_pos hW0 _).le
    rw [abs_of_nonneg hT]
    gcongr
    have := abs_nonneg C1; have := abs_nonneg C2
    linarith
  have hneg : 0 ≤ (p.W : ℝ) ^ (-D) := (Real.rpow_pos_of_pos hW0 _).le
  -- large `W`: thresholds
  have hcertsmall : C1' * (p.W : ℝ) ^ (-1 + ε') ≤ ε₁ := by
    have h := rpow_neg_le_of_le (a := 1 - ε') (t := ε₁ / C1') (W := p.W) (by linarith)
      (by positivity) (((le_max_left _ _).trans (le_max_left _ _)).trans hWbig.le)
    rw [show -(1 - ε') = -1 + ε' by ring, le_div_iff₀ hC1'0] at h
    linarith
  have hηδ : (p.W : ℝ) ^ (-(3 / 5 : ℝ)) ≤ δ :=
    rpow_neg_le_of_le (by norm_num) hδ (((le_max_right _ _).trans (le_max_left _ _)).trans
      hWbig.le)
  have hεpow : (p.W : ℝ) ^ (-1 + ε') ≤ (p.W : ℝ) ^ (-1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  refine ⟨Ω1 ∪ Ω2, fun α => ?_, fun x hx α hα => ?_⟩
  · refine (measure_union_le _ _).trans ?_
    calc splitPairLaw p i α Pω Ω1 + splitPairLaw p i α Pω Ω2
        ≤ ENNReal.ofReal (|C1| * (p.W : ℝ) ^ (-D)) + ENNReal.ofReal (|C2| * (p.W : ℝ) ^ (-D)) :=
          add_le_add ((hΩ1 α).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_abs_self _)))
            ((hΩ2 α).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_abs_self _)))
      _ = ENNReal.ofReal ((|C1| + |C2|) * (p.W : ℝ) ^ (-D)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C2]) hneg)
  have hx1 : x ∉ Ω1 := fun h => hx (Or.inl h)
  have hx2 : x ∉ Ω2 := fun h => hx (Or.inr h)
  obtain ⟨hH, hV, hsel⟩ := hgood1 x hx1
  obtain ⟨hEκ, hcert⟩ := hsel α hα
  obtain ⟨h3, h4⟩ := hgood2 x hx2 α hα
  intro E K s η Rη
  have hK : K.IsHermitian := WeightedTrace.schurK0_isHermitian hH hV E
  have hχ := norm_chi_le_certErr x.1 hH hV E
  have hcert1 : certErr p i x.1 E ≤ C1' * (p.W : ℝ) ^ (-1 + ε') :=
    hcert.trans (by gcongr; exact le_max_left _ _)
  have hcert2 : certErr p i x.1 E ≤ C1' * (p.W : ℝ) ^ (-1 + ε) :=
    hcert1.trans (by gcongr)
  obtain ⟨r1, r2, r3, r4, r5⟩ := hreg p hpb i K hK E hEκ (hχ.trans (hcert1.trans hcertsmall))
  have hfin : L * ‖certificateChi K (splitS p) 0 (conj (matchedA E))‖ ≤
      (|T| * W₀ ^ (D + 1) / 2 + |C1| + |C2| + L * C1') * (p.W : ℝ) ^ (-1 + ε) := by
    have hp : 0 ≤ (p.W : ℝ) ^ (-1 + ε) := (Real.rpow_pos_of_pos hW0 _).le
    calc L * ‖certificateChi K (splitS p) 0 (conj (matchedA E))‖
        ≤ L * (C1' * (p.W : ℝ) ^ (-1 + ε)) := by gcongr; exact hχ.trans hcert2
      _ = (L * C1') * (p.W : ℝ) ^ (-1 + ε) := by ring
      _ ≤ _ := by
          gcongr
          have := abs_nonneg C1; have := abs_nonneg C2
          linarith
  refine ⟨r1, r2, r3 η (Real.rpow_pos_of_pos hW0 _).le hηδ, r4.trans hfin, r5.trans hfin,
    h3.trans ?_, h4.trans ?_⟩
  · have hp : 0 ≤ (p.W : ℝ) ^ ε / η := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    gcongr
    have := abs_nonneg C1
    linarith [le_abs_self C2]
  · have hp : 0 ≤ (p.W : ℝ) ^ (9 / 10 + ε) := (Real.rpow_pos_of_pos hW0 _).le
    gcongr
    have := abs_nonneg C1
    linarith [le_abs_self C2]

end BlockBand.DeterminantScore.SelectedResolvent
