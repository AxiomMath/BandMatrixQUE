module

public import BlockBand.SourceProcess.ContractingWords.SepAlgebra

/-!
# Every nonempty word is bounded by the load

The lemma `ae_norm_wordValue_le` bounds ordinary words. Here the same bound holds for **every
nonempty word**, contracting separators included: almost surely, for every length `j` and tag births
`k`, `|Tr w| ≤ L_j^{|w|}` (`ae_norm_wordValue_le_all`), `L_j = 1 + 2g_j + Σ_a Tr Q_{a,j}`, and an
admitted product satisfies `|Z_j| ≤ L_j^{deg Z}` (`ae_norm_productValue_le`). The one-letter current
words use `norm_trace_current_sepMat_le`; longer words use Hilbert–Schmidt norms and
`hsNorm_mul_sepMat_le` (`𝕊` is a.s. unitary). `Tr|J|` is never used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.FullSource
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge

variable {W : ℕ}

/-- One-letter words with any separator: `|Tr(AB)| ≤ L_j`. -/
theorem norm_trace_letter_sep_le (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W)
    (hS : scatteringMatrix b E W j ω * (scatteringMatrix b E W j ω)ᴴ = 1)
    (hg : pathConductance b E W j ω = ((pathCurrent b E W j ω) ^ 2).trace.re / 2)
    (ℓ : TraceLetter nT nI) (σ : Separator) :
    ‖(letterMatrix b E k q W j ω ℓ * separatorMatrix b E W j ω σ).trace‖ ≤
      wordLoad b E k q W j ω := by
  have hsum : 0 ≤ ∑ a, sourceTrace b E k q W j ω a :=
    Finset.sum_nonneg fun a _ => sourceTrace_nonneg b E k q hq j ω a
  have hJdef : pathCurrent b E W j ω = (scatteringMatrix b E W j ω)ᴴ * nearProjection W *
      scatteringMatrix b E W j ω - nearProjection W := rfl
  have hJ2 : hsNorm (pathCurrent b E W j ω) ^ 2 = 2 * pathConductance b E W j ω := by
    have h := current_hsNorm_sq (scatteringMatrix b E W j ω) (nearProjection W)
      nearProjection_conjTranspose
    rw [hg, hJdef, ← h, Complex.ofReal_re]; ring
  have hg0 : 0 ≤ pathConductance b E W j ω := by nlinarith [hsNorm_nonneg (pathCurrent b E W j ω)]
  rw [separatorMatrix_eq_sepMat]
  have hB := fun T => hsNorm_mul_sepMat_le (m := Fin j × Fin W) (scatteringMatrix b E W j ω) hS σ T
  cases ℓ with
  | current =>
    have h := norm_trace_current_sepMat_le (scatteringMatrix b E W j ω) hS σ
    rw [← hJdef, hJ2] at h
    simp only [letterMatrix, wordLoad]; linarith
  | tag a =>
    obtain ⟨t, c, hc, he⟩ := sourceLetter_gram b E k q hq j ω (Sum.inl a)
    have hle := sourceTrace_le_sum b E k q hq j ω (Sum.inl a)
    have hst : sourceTrace b E k q W j ω (Sum.inl a) =
        (letterMatrix b E k q W j ω (.tag a)).trace.re := rfl
    simp only [sourceLetter, Sum.elim_inl] at he
    rw [hst, he] at hle
    rw [he]
    have := gram_trace_mul_le t c hc (fun i => pastS b E W j i (pastCoords W j ω)) _ hB
    simp only [wordLoad]; linarith
  | interval a =>
    obtain ⟨t, c, hc, he⟩ := sourceLetter_gram b E k q hq j ω (Sum.inr a)
    have hle := sourceTrace_le_sum b E k q hq j ω (Sum.inr a)
    have hst : sourceTrace b E k q W j ω (Sum.inr a) =
        (letterMatrix b E k q W j ω (.interval a)).trace.re := rfl
    simp only [sourceLetter, Sum.elim_inr] at he
    rw [hst, he] at hle
    rw [he]
    have := gram_trace_mul_le t c hc (fun i => pastS b E W j i (pastCoords W j ω)) _ hB
    simp only [wordLoad]; linarith

/-- **Every nonempty word is bounded by the load**, almost surely, at every length. -/
theorem ae_norm_wordValue_le_all {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {nT nI : ℕ} (q : Fin nI → ℝ → ℝ) (hq : IsIntervalTests q) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (k : Fin nT → ℕ) (w : TraceWord nT nI),
      w ≠ [] → ‖wordValue b E k q W j ω w‖ ≤ wordLoad b E k q W j ω ^ w.length := by
  filter_upwards [ae_scattering_unitary hb hE1 hE2 hW] with ω hω j k w hw
  obtain ⟨hS, hg⟩ := hω j
  rcases w with _ | ⟨x, w⟩
  · exact absurd rfl hw
  rcases w with _ | ⟨y, w⟩
  · simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Matrix.mul_one, List.length_singleton, pow_one]
    exact norm_trace_letter_sep_le b E k q hq j ω hS hg x.1 x.2
  · rw [wordValue]
    refine (norm_trace_list_prod_le _ (by simp)).trans ?_
    rw [List.map_map]
    have hlen : (x :: y :: w).length =
        ((x :: y :: w).map (hsNorm ∘ fun x => letterMatrix b E k q W j ω x.1 *
          separatorMatrix b E W j ω x.2)).length := by simp
    rw [hlen]
    refine list_prod_le_pow (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hz; exact hsNorm_nonneg _
    · obtain ⟨u, -, rfl⟩ := List.mem_map.mp hz
      simp only [Function.comp_apply]
      rw [separatorMatrix_eq_sepMat]
      exact (hsNorm_mul_sepMat_le _ hS u.2 _).trans
        (letter_bounds b E k q hq j ω hS hg u.1 .id (Or.inl rfl)).1

theorem productDegree_cons {nT nI : ℕ} (w : TraceWord nT nI) (Zs : List (TraceWord nT nI)) :
    productDegree (w :: Zs) = w.length + productDegree Zs := by
  simp [productDegree]

/-- **Admitted products are bounded by the load**, almost surely, at every length. -/
theorem ae_norm_productValue_le {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {nT nI : ℕ} (q : Fin nI → ℝ → ℝ) (hq : IsIntervalTests q) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (k : Fin nT → ℕ) (Zs : List (TraceWord nT nI)),
      IsAdmittedProduct Zs →
        ‖productValue b E k q W j ω Zs‖ ≤ wordLoad b E k q W j ω ^ productDegree Zs := by
  filter_upwards [ae_norm_wordValue_le_all hb hE1 hE2 hW (nT := nT) q hq,
    ae_scattering_unitary hb hE1 hE2 hW] with ω hω hU j k Zs hZ
  have hL1 := one_le_wordLoad b E k q hq j ω (hU j).2
  induction Zs with
  | nil => simp [productValue, productDegree]
  | cons w Zs ih =>
    have hw := hω j k w (hZ w List.mem_cons_self)
    have ih' := ih fun v hv => hZ v (List.mem_cons_of_mem _ hv)
    rw [productValue, List.map_cons, List.prod_cons, productDegree_cons, pow_add]
    rw [productValue] at ih'
    exact (norm_mul_le _ _).trans (mul_le_mul hw ih' (norm_nonneg _) (by positivity))

theorem measurable_productValue (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (j : ℕ) (Zs : List (TraceWord nT nI)) :
    Measurable fun ω : GrowthPath W => productValue b E k q W j ω Zs := by
  induction Zs with
  | nil => simp only [productValue, List.map_nil, List.prod_nil]; exact measurable_const
  | cons w Zs ih =>
    simp only [productValue, List.map_cons, List.prod_cons] at ih ⊢
    exact (measurable_wordValue b E k q j w).mul ih

end BlockBand.SourceProcess.ContractingWords
