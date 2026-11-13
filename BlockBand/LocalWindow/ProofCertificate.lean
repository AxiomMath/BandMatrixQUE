module

public import BlockBand.LocalWindow.Statements
public import BlockBand.DeterminantScore.PairRowMoment

/-!
# The pole certificate on an energy grid

A union bound over a polynomially large energy grid for the pole certificate of the exact
residual, used in the physical local-window lemma.

## Main results

* `measure_lt_le_of_eLpNorm_le`: Markov at a real moment `q > 0` (no measurability needed).
* `gridCertificate_le`: for fixed `b, κ, T`, `ε > 0`, `D ≥ 0` and `M` there is `C` such that,
  for every admissible `p` (`p.b = b`, `n ≤ TW`), model, adjacent pair, splitting law `Pω` and
  finite set `Es ⊆ bulkInterval κ` with `|Es| ≤ W^M`,
  `Pω{∃ E ∈ Es, max_{k=i,i+1} |W⁻¹ Tr P_k (K(E) - s a(E))⁻¹ - a(E)| > W^{-1+ε}} ≤ C W^{-D}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCertificate

open MeasureTheory ProbabilityTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open scoped ENNReal

/-- The certificate error `max_{k = i, i+1} |W⁻¹ Tr P_k (K(E) - s a)⁻¹ - a|` of the exact
residual `K(E) = F(E) - E` at `s = splitS p`, `a = matchedA E`. -/
def certErr (p : Parameters) (i : ZMod p.n) (om : SplitState p i) (E : ℝ) : ℝ :=
  max ‖pairBlockTrace p i ((pairResidual p i om E - ((splitS p : ℂ) * matchedA E) • 1)⁻¹) i -
      matchedA E‖
    ‖pairBlockTrace p i ((pairResidual p i om E - ((splitS p : ℂ) * matchedA E) • 1)⁻¹) (i + 1) -
      matchedA E‖

theorem certErr_nonneg (p : Parameters) (i : ZMod p.n) (om : SplitState p i) (E : ℝ) :
    0 ≤ certErr p i om E :=
  le_max_of_le_left (norm_nonneg _)

/-- **Markov at a real moment**: `‖f‖_q ≤ K` gives `μ{f > u} ≤ (K/u)^q` for `f ≥ 0`, `q, u > 0`
(outer measure; no measurability). -/
theorem measure_lt_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) {q u K : ℝ} (hq : 0 < q) (hu : 0 < u) (hK : 0 ≤ K)
    (h : eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal K) :
    μ {x | u < f x} ≤ ENNReal.ofReal ((K / u) ^ q) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by simp [hq]
  have hM := mul_meas_ge_le_pow_eLpNorm' μ hq0 ENNReal.ofReal_ne_top (f := f)
    (ENNReal.ofReal u)
  rw [ENNReal.toReal_ofReal hq.le] at hM
  have hsub : {x | u < f x} ⊆ {x | ENNReal.ofReal u ≤ ‖f x‖ₑ} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Real.enorm_of_nonneg (hf x)]
    exact ENNReal.ofReal_le_ofReal hx.le
  have h2 : ENNReal.ofReal u ^ q * μ {x | u < f x} ≤ ENNReal.ofReal K ^ q :=
    (mul_le_mul_right (measure_mono hsub) _).trans
      (hM.trans (ENNReal.rpow_le_rpow h hq.le))
  rw [ENNReal.ofReal_rpow_of_nonneg hu.le hq.le, ENNReal.ofReal_rpow_of_nonneg hK hq.le] at h2
  have hup : 0 < u ^ q := Real.rpow_pos_of_pos hu q
  rw [Real.div_rpow hK hu.le, ENNReal.ofReal_div_of_pos hup]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hup])) (Or.inl ENNReal.ofReal_ne_top),
    mul_comm]
  exact h2

/-- `splitS p = min(1 - 2b, b)` depends only on `b`. -/
theorem splitS_eq {p : Parameters} {b : ℝ} (hpb : p.b = b) : splitS p = min (1 - 2 * b) b := by
  unfold splitS Parameters.c; rw [hpb]

/-- **The uniform pole certificate on a grid**, for the exact residual, from
`MatchedTracesContract.residualPair`. Fixed `b, κ, T`, `ε > 0`, `D ≥ 0`, `M` first; then
`C`; uniformly in admissible `p` with `p.b = b`, `n ≤ TW`, models, adjacent pairs, splitting
laws at `s = splitS p` and finite energy sets `Es ⊆ bulkInterval κ` with `|Es| ≤ W^M`. -/
theorem gridCertificate_le (hMT : MatchedTracesContract) (b κ T : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (hκ : 0 < κ) (ε D M : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
        IsPairSplitting p i model (splitS p) Pω →
        ∀ Es : Finset ℝ, (∀ E ∈ Es, E ∈ bulkInterval κ) → (Es.card : ℝ) ≤ (p.W : ℝ) ^ M →
          Pω {om | ∃ E ∈ Es, (p.W : ℝ) ^ (-1 + ε) < certErr p i om E} ≤
            ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) := by
  set s := min (1 - 2 * b) b with hsdef
  have hs : 0 < s := lt_min (by linarith) hb
  have hs' : s < 2 * min (1 - 2 * b) b := by rw [← hsdef]; linarith
  obtain ⟨ε₀, C₀, hε₀, h⟩ := hMT.residualPair b hb hb' κ T s hκ hs hs'
  set q : ℝ := max 2 ((max D 0 + M) / ε) with hqdef
  have hq2 : 2 ≤ q := le_max_left _ _
  have hq0 : 0 < q := by linarith
  have hqε : max D 0 + M ≤ ε * q := by
    have := le_max_right 2 ((max D 0 + M) / ε)
    rw [div_le_iff₀ hε] at this; linarith
  set K₀ : ℝ := |C₀| * Real.sqrt q
  have hK₀ : 0 ≤ K₀ := by positivity
  refine ⟨K₀ ^ q + (q / ε₀) ^ D, by positivity, fun p hpb hn model i Pω hsplit Es hEs hcard => ?_⟩
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hsp : splitS p = s := splitS_eq hpb
  have hWD : 0 < (p.W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW0 _
  by_cases hqW : q ≤ ε₀ * p.W
  · -- the moment bound applies at every grid energy
    have hE : ∀ E ∈ Es, Pω {om | (p.W : ℝ) ^ (-1 + ε) < certErr p i om E} ≤
        ENNReal.ofReal (K₀ ^ q / (p.W : ℝ) ^ (ε * q)) := by
      intro E hEmem
      have hsplit' : IsPairSplitting p i model s Pω := hsp ▸ hsplit
      have hm := h p hpb hn model i Pω hsplit' E (hEs E hEmem) q hq2 hqW
      have hm' : eLpNorm (fun om => certErr p i om E) (ENNReal.ofReal q) Pω ≤
          ENNReal.ofReal (K₀ / p.W) := by
        refine le_trans (le_of_eq ?_) (hm.trans (ENNReal.ofReal_le_ofReal ?_))
        · unfold certErr; rw [hsp]
        · apply div_le_div_of_nonneg_right _ hW0.le
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
      refine (measure_lt_le_of_eLpNorm_le Pω _ (fun om => certErr_nonneg p i om E) hq0
        (Real.rpow_pos_of_pos hW0 _) (by positivity) hm').trans (le_of_eq ?_)
      congr 1
      have e1 : K₀ / p.W / (p.W : ℝ) ^ (-1 + ε) = K₀ / (p.W : ℝ) ^ ε := by
        rw [Real.rpow_add hW0, Real.rpow_neg_one]
        field_simp
      rw [e1, Real.div_rpow hK₀ (Real.rpow_nonneg hW0.le _), ← Real.rpow_mul hW0.le]
    have hsub : {om | ∃ E ∈ Es, (p.W : ℝ) ^ (-1 + ε) < certErr p i om E} =
        ⋃ E ∈ Es, {om | (p.W : ℝ) ^ (-1 + ε) < certErr p i om E} := by
      ext om; simp
    rw [hsub]
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum hE).trans ?_
    rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hWq : 0 < (p.W : ℝ) ^ (ε * q) := Real.rpow_pos_of_pos hW0 _
    have hexp : (p.W : ℝ) ^ M / (p.W : ℝ) ^ (ε * q) ≤ (p.W : ℝ) ^ (-D) := by
      rw [← Real.rpow_sub hW0]
      apply Real.rpow_le_rpow_of_exponent_le hW1
      have := le_max_left D 0
      linarith
    calc (Es.card : ℝ) * (K₀ ^ q / (p.W : ℝ) ^ (ε * q))
        ≤ (p.W : ℝ) ^ M * (K₀ ^ q / (p.W : ℝ) ^ (ε * q)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = K₀ ^ q * ((p.W : ℝ) ^ M / (p.W : ℝ) ^ (ε * q)) := by ring
      _ ≤ K₀ ^ q * (p.W : ℝ) ^ (-D) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ (K₀ ^ q + (q / ε₀) ^ D) * (p.W : ℝ) ^ (-D) := by
          apply mul_le_mul_of_nonneg_right _ hWD.le
          have : 0 ≤ (q / ε₀) ^ D := by positivity
          linarith
  · -- small `W`: the bound exceeds one
    push Not at hqW
    have hprob := BlockBand.DeterminantScore.ScoreMoments.PairRow.splitLaw_univ hsplit
    refine (measure_mono (Set.subset_univ _)).trans ?_
    rw [hprob, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hWq : (p.W : ℝ) < q / ε₀ := by rw [lt_div_iff₀ hε₀]; linarith
    have h1 : 1 ≤ (q / ε₀) ^ D * (p.W : ℝ) ^ (-D) := by
      rw [Real.rpow_neg hW0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hW0 _),
        one_mul]
      exact Real.rpow_le_rpow hW0.le hWq.le hD
    have : 0 ≤ K₀ ^ q * (p.W : ℝ) ^ (-D) := by positivity
    nlinarith

end BlockBand.LocalWindow.ProofCertificate
