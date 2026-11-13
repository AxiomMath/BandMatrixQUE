module

public import BlockBand.SourceProcess.FullSourceGenerator.TightModulus
public import BlockBand.SourceProcess.FullSourceGenerator.ConjWord
public import BlockBand.SourceProcess.FullSourceGenerator.Assembly

/-!
# The field `tight` of `FullSourceGeneratorContract`

`tightClause_of`: from the summed generator errors with early tags `EarlySummed` and the
full-source stops statement, the `tight` field holds; with the generator clause,
`fullSourceGenerator_of_early` gives `FullSourceGeneratorContract`.

The argument is the modulus estimate of the full-source stops lemma together with its stop tail.
Complex words are reduced to the real polynomials `rePoly w`, `imPoly w` (`ConjWord`;
`‖z‖ ≤ |Re z| + |Im z|`), whose modulus is `modulus_real`. Tightness at `t₁` needs no moment:
before the stop the word is bounded by `aliveBound` (`ae_polyValue_le_of_alive`), and the stop
is removed by `tail`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory MvPolynomial Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {nT nI : ℕ}

theorem isRealPoly_rePoly {b E : ℝ} {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q)
    {w : TraceWord nT nI} (hw : IsOrdinaryWord w) : IsRealPoly b E q (rePoly w) :=
  fun W k j ω => by rw [polyValue_rePoly b E k q hq j ω hw, Complex.ofReal_re]

theorem isRealPoly_imPoly {b E : ℝ} {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q)
    {w : TraceWord nT nI} (hw : IsOrdinaryWord w) : IsRealPoly b E q (imPoly w) :=
  fun W k j ω => by rw [polyValue_imPoly b E k q hq j ω hw, Complex.ofReal_re]

theorem realVal_rePoly {b E : ℝ} {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q) {W : ℕ}
    (k : Fin nT → ℕ) {w : TraceWord nT nI} (hw : IsOrdinaryWord w) (j : ℕ) (ω : GrowthPath W) :
    realVal b E k q W j (rePoly w) ω = (wordValue b E k q W j ω w).re := by
  simp only [realVal, polyValue_rePoly b E k q hq j ω hw, Complex.ofReal_re]

theorem realVal_imPoly {b E : ℝ} {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q) {W : ℕ}
    (k : Fin nT → ℕ) {w : TraceWord nT nI} (hw : IsOrdinaryWord w) (j : ℕ) (ω : GrowthPath W) :
    realVal b E k q W j (imPoly w) ω = (wordValue b E k q W j ω w).im := by
  simp only [realVal, polyValue_imPoly b E k q hq j ω hw, Complex.ofReal_re]

/-- **The field `tight`.** -/
theorem tightClause_of (hES : EarlySummed) (hFS : FullSourceStopsContract)
    (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : TightClause := by
  intro b hb0 hb E hE1 hE2 t₀ ht₀ nT nI q hq k hk w hw t₁ T ht₁ hT
  have hqI : IsIntervalTests q := fun a => let ⟨s, hs⟩ := hq a; ⟨s, t₀, hs⟩
  refine ⟨fun θ hθ => ?_, fun η θ hη hθ => ?_⟩
  · -- tight at `t₁`
    set ε := t₀ / 2
    have hε : 0 < ε := by positivity
    have hεT : ε < T + 1 := by show t₀ / 2 < T + 1; linarith
    obtain ⟨Cs, hCs⟩ := hFS.tail b hb0 hb E hE1 hE2 nT nI q hqI ε (T + 1) hε hεT
    set K := |Cs| / θ + 1
    have hK : 0 < K := by positivity
    have hCK : Cs / K < θ := by
      rw [div_lt_iff₀ hK]
      have : θ * K = |Cs| + θ := by simp only [K]; field_simp
      linarith [le_abs_self Cs]
    have hstop : ∀ᶠ W : ℕ in atTop, (⨆ k' : Fin nT → ℕ, growthPathLaw W b {ω | ∃ j : ℕ,
        ε * W ≤ j ∧ (j : ℝ) ≤ (T + 1) * W ∧ K < traceLoad b E k' q W j ω}) <
          ENNReal.ofReal θ :=
      eventually_lt_of_limsup_lt ((hCs K hK).trans_lt
        (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hCK, hθ⟩))
    obtain ⟨W₁, hW₁⟩ := eventually_atTop.mp hstop
    refine ⟨aliveBound K (wv w), max W₁ (max 1 ⌈2 / t₀⌉₊), fun W hW => ?_⟩
    have hW1 : 1 ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
    have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
    have hWc : ⌈2 / t₀⌉₊ ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW)
    have hWc' : (⌈2 / t₀⌉₊ : ℝ) ≤ W := by exact_mod_cast hWc
    have hWt : 2 ≤ (W : ℝ) * t₀ := by
      have h := (Nat.le_ceil (2 / t₀)).trans hWc'
      rw [div_le_iff₀ ht₀] at h; linarith
    set j₁ := ⌊(W : ℝ) * t₁⌋₊
    have hj₁ : (W : ℝ) * t₁ < j₁ + 1 := Nat.lt_floor_add_one _
    have hεj : ε * W ≤ j₁ := by
      show t₀ / 2 * W ≤ j₁; nlinarith [mul_le_mul_of_nonneg_left ht₁ hW0.le]
    have hj₁T : (j₁ : ℝ) ≤ (T + 1) * W := (Nat.floor_le (by nlinarith)).trans (by nlinarith)
    set Stop := {ω : GrowthPath W | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ (T + 1) * W ∧
      K < traceLoad b E (k W) q W j ω}
    have hae := ae_polyValue_le_of_alive (nT := nT) hb hE1 hE2 hW1 q hqI K ε
    have hincl : {ω | aliveBound K (wv w) < ‖wordValue b E (k W) q W j₁ ω w‖} ⊆
        Stop ∪ {ω | ¬ ∀ (j : ℕ) (k' : Fin nT → ℕ) (Ψ : TracePoly nT nI), Ψ ∈ ordPoly nT nI →
          ε * W ≤ j → ω ∈ alive b E k' q K ε W j →
            ‖polyValue b E k' q W j ω Ψ‖ ≤ polyConst Ψ * (1 + K + K ^ 2) ^ polyExp Ψ} := by
      intro ω hω
      by_cases hS : ω ∈ Stop
      · exact Or.inl hS
      refine Or.inr fun h => ?_
      have := h j₁ (k W) (wv w) (wv_mem_ordPoly hw) hεj (mem_alive_of_notMem_stop hS hj₁T)
      simp only [polyValue, wv, eval_X] at this
      exact absurd this (not_le.mpr hω)
    refine (measure_mono hincl).trans ((measure_union_le _ _).trans ?_)
    rw [ae_iff.mp hae, add_zero]
    exact ((le_iSup (fun k' : Fin nT → ℕ => growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧
      (j : ℝ) ≤ (T + 1) * W ∧ K < traceLoad b E k' q W j ω}) (k W)).trans
        (hW₁ W (le_trans (le_max_left _ _) hW)).le)
  · -- the modulus
    obtain ⟨δ₁, hδ₁, W₁, h₁⟩ := modulus_real hES hFS hMT hGA hLp hSR hb0 hb hE1 hE2 ht₀ hq hk
      (rePoly_ordinary hw) (isRealPoly_rePoly hqI hw) ht₁ hT (half_pos hη) (half_pos hθ)
    obtain ⟨δ₂, hδ₂, W₂, h₂⟩ := modulus_real hES hFS hMT hGA hLp hSR hb0 hb hE1 hE2 ht₀ hq hk
      (imPoly_ordinary hw) (isRealPoly_imPoly hqI hw) ht₁ hT (half_pos hη) (half_pos hθ)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max W₁ W₂, fun W hW => ?_⟩
    have hincl : {ω | ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ min δ₁ δ₂ ∧
        η < ‖wordValue b E (k W) q W ⌊(W : ℝ) * t⌋₊ ω w -
          wordValue b E (k W) q W ⌊(W : ℝ) * t'⌋₊ ω w‖} ⊆
        {ω | ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ₁ ∧
          η / 2 < |realVal b E (k W) q W ⌊(W : ℝ) * t⌋₊ (rePoly w) ω -
            realVal b E (k W) q W ⌊(W : ℝ) * t'⌋₊ (rePoly w) ω|} ∪
        {ω | ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ₂ ∧
          η / 2 < |realVal b E (k W) q W ⌊(W : ℝ) * t⌋₊ (imPoly w) ω -
            realVal b E (k W) q W ⌊(W : ℝ) * t'⌋₊ (imPoly w) ω|} := by
      intro ω ⟨t, ht, t', ht', htt, hgt⟩
      simp only [realVal_rePoly hqI (k W) hw, realVal_imPoly hqI (k W) hw]
      have hn := Complex.norm_le_abs_re_add_abs_im (wordValue b E (k W) q W ⌊(W : ℝ) * t⌋₊ ω w -
        wordValue b E (k W) q W ⌊(W : ℝ) * t'⌋₊ ω w)
      rw [Complex.sub_re, Complex.sub_im] at hn
      by_cases hre : η / 2 < |(wordValue b E (k W) q W ⌊(W : ℝ) * t⌋₊ ω w).re -
          (wordValue b E (k W) q W ⌊(W : ℝ) * t'⌋₊ ω w).re|
      · exact Or.inl ⟨t, ht, t', ht', htt.trans (min_le_left _ _), hre⟩
      · refine Or.inr ⟨t, ht, t', ht', htt.trans (min_le_right _ _), ?_⟩
        linarith
    refine (measure_mono hincl).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add (h₁ W (le_trans (le_max_left _ _) hW))
      (h₂ W (le_trans (le_max_right _ _) hW))).trans_eq ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- `FullSourceGeneratorContract` from `GeneratorClause`, with `tight` from `tightClause_of`. -/
theorem fullSourceGenerator_of_early (hES : EarlySummed) (hFS : FullSourceStopsContract)
    (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hG : GeneratorClause) : FullSourceGeneratorContract :=
  fullSourceGenerator_of hGA hLp hSR hG (tightClause_of hES hFS hMT hGA hLp hSR)

end BlockBand.SourceProcess.FullSourceGenerator
