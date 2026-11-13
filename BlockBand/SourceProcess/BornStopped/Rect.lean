module

public import BlockBand.SourceProcess.BornStopped.Piece
public import BlockBand.SourceProcess.BornStopped.Dyadic

/-!
# Rectangles at the dyadic horizons

Under `GramHorizonLaw`, two born solutions whose data `(z, (G - J)(0))` have the same law give
equal masses to the rectangles `{z ∈ A} ∩ {tildeG(dyTime n (dyIdx n (α' z))) ∈ B}`, where the
dyadic times approximate from below a time `α'` such that no birth lies in `(0, α')`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornStopped

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

variable {c F Z : Type} [Fintype c] [DecidableEq c] [Fintype F] [MeasurableSpace Z] {D0 : ℝ}
  {D : Matrix c c ℂ} {j : F → GramState c} {b : Z → F → ℝ} {α' : Z → ℝ≥0}
  {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m} {Q : Measure Ω}
  {z : Ω → Z} {G : ℝ≥0 → Ω → GramState c}
  {Ω' : Type} {m' : MeasurableSpace Ω'} {𝓖' : Filtration ℝ≥0 m'} {Q' : Measure Ω'}
  {z' : Ω' → Z} {G' : ℝ≥0 → Ω' → GramState c}

/-- The piece `{x ∈ A, dyIdx n (α' x) = k}`. -/
def dyPiece (α' : Z → ℝ≥0) (A : Set Z) (n k : ℕ) : Set Z :=
  A ∩ (fun x => dyIdx n (α' x)) ⁻¹' {k}

/-- `tildeG` at the dyadic horizon `dyTime n (dyIdx n (α' z))`. -/
def dyX {Ω₁ : Type} (j : F → GramState c) (b : Z → F → ℝ) (α' : Z → ℝ≥0) (z₁ : Ω₁ → Z)
    (G₁ : ℝ≥0 → Ω₁ → GramState c) (n : ℕ) (ω : Ω₁) : GramState c :=
  tildeG j (fun ω => b (z₁ ω)) G₁ (dyTime n (dyIdx n (α' (z₁ ω)))) ω

omit [Fintype F] [MeasurableSpace Z] in
theorem dyPiece_noBirth (hb' : ∀ x f, b x f ≤ 0 ∨ (α' x : ℝ) ≤ b x f) {A : Set Z} {n k : ℕ} :
    ∀ x ∈ dyPiece α' A n k, ∀ f, b x f ≤ 0 ∨ (dyTime n k : ℝ) < b x f := by
  rintro x ⟨-, hx⟩ f
  have hx' : dyIdx n (α' x) = k := hx
  rcases eq_or_lt_of_le (zero_le (a := α' x)) with h0 | hpos
  · rw [← hx', ← h0, dyIdx_zero, dyTime_zero, NNReal.coe_zero]
    exact le_or_gt _ _
  · rcases hb' x f with h | h
    · exact Or.inl h
    · right; rw [← hx']; exact lt_of_lt_of_le (NNReal.coe_lt_coe.2 (dyTime_lt hpos)) h

theorem measurableSet_dyPiece (hα : Measurable α') {A : Set Z} (hA : MeasurableSet A) (n k : ℕ) :
    MeasurableSet (dyPiece α' A n k) :=
  hA.inter ((measurable_dyIdx n).comp hα (measurableSet_singleton k))

omit [MeasurableSpace Z] in
theorem measurable_tildeG {β : Ω → F → ℝ}
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G) (t : ℝ≥0) :
    Measurable (tildeG j β G t) := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  exact ((measurable_G hG t).sub (measurable_of_stronglyMeasurable_gram (𝓖.le 0) (hG.jump t))).add
    (measurable_of_stronglyMeasurable_gram (𝓖.le 0) (hG.jump 0))

theorem measurable_dyX (hα : Measurable α') (hz : Measurable z)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (b (z ω)) (t : ℝ)) G) (n : ℕ) :
    Measurable (dyX j b α' z G n) := by
  have h : Measurable fun p : Ω × ℕ => tildeG j (fun ω => b (z ω)) G (dyTime n p.2) p.1 := by
    refine measurable_from_prod_countable_left fun k => ?_
    have := measurable_tildeG hG (dyTime n k)
    exact this
  have e : dyX j b α' z G n = (fun p : Ω × ℕ => tildeG j (fun ω => b (z ω)) G (dyTime n p.2) p.1) ∘
      fun ω => (ω, dyIdx n (α' (z ω))) := rfl
  rw [e]
  exact h.comp (measurable_id.prodMk ((measurable_dyIdx n).comp (hα.comp hz)))

omit [Fintype c] [DecidableEq c] [MeasurableSpace Z] in
theorem preimage_dyX (z₁ : Ω → Z) (G₁ : ℝ≥0 → Ω → GramState c) (A : Set Z)
    (B : Set (GramState c)) (n : ℕ) :
    z₁ ⁻¹' A ∩ dyX j b α' z₁ G₁ n ⁻¹' B =
      ⋃ k, z₁ ⁻¹' dyPiece α' A n k ∩ tildeG j (fun ω => b (z₁ ω)) G₁ (dyTime n k) ⁻¹' B := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, dyPiece, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨_, ⟨hA, rfl⟩, hB⟩
  · rintro ⟨k, ⟨hA, rfl⟩, hB⟩
    exact ⟨hA, hB⟩

theorem measure_dyX (hα : Measurable α') (hz : Measurable z)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (b (z ω)) (t : ℝ)) G)
    {A : Set Z} (hA : MeasurableSet A) {B : Set (GramState c)} (hB : MeasurableSet B) (n : ℕ) :
    Q (z ⁻¹' A ∩ dyX j b α' z G n ⁻¹' B) =
      ∑' k, Q (z ⁻¹' dyPiece α' A n k ∩ tildeG j (fun ω => b (z ω)) G (dyTime n k) ⁻¹' B) := by
  rw [preimage_dyX]
  refine measure_iUnion (fun k l hkl => Set.disjoint_left.2 fun ω h1 h2 => hkl ?_)
    fun k => (hz (measurableSet_dyPiece hα hA n k)).inter (measurable_tildeG hG _ hB)
  have e1 : dyIdx n (α' (z ω)) = k := h1.1.2
  have e2 : dyIdx n (α' (z ω)) = l := h2.1.2
  exact e1.symm.trans e2

/-- **Equal masses of the dyadic rectangles** for two born solutions. -/
theorem rect_dy (hH : GramHorizonLaw) (hD0 : 0 < D0) (hD : IsSignature D) (hb : Measurable b)
    (hα : Measurable α') (hb' : ∀ x f, b x f ≤ 0 ∨ (α' x : ℝ) ≤ b x f)
    [IsProbabilityMeasure Q] (hz : Measurable[𝓖 0] z)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (b (z ω)) (t : ℝ)) G)
    [IsProbabilityMeasure Q'] (hz' : Measurable[𝓖' 0] z')
    (hG' : IsBornGramSolution Q' 𝓖' D0 D (fun t ω => birthSum j (b (z' ω)) (t : ℝ)) G')
    (h0 : Q.map (fun ω => (z ω, bornCont j (fun ω => b (z ω)) G 0 ω)) =
      Q'.map (fun ω => (z' ω, bornCont j (fun ω => b (z' ω)) G' 0 ω)))
    {A : Set Z} (hA : MeasurableSet A) {B : Set (GramState c)} (hB : MeasurableSet B) (n : ℕ) :
    Q (z ⁻¹' A ∩ dyX j b α' z G n ⁻¹' B) = Q' (z' ⁻¹' A ∩ dyX j b α' z' G' n ⁻¹' B) := by
  have hzm : Measurable z := hz.mono (𝓖.le 0) le_rfl
  have hzm' : Measurable z' := hz'.mono (𝓖'.le 0) le_rfl
  rw [measure_dyX hα hzm hG hA hB, measure_dyX hα hzm' hG' hA hB]
  refine tsum_congr fun k => ?_
  have hS := measurableSet_dyPiece hα hA n k
  by_cases hS0 : Q (z ⁻¹' dyPiece α' A n k) = 0
  · have hS0' : Q' (z' ⁻¹' dyPiece α' A n k) = 0 := by rwa [← mass_eq hz hG hz' hG' h0 hS]
    rw [measure_mono_null Set.inter_subset_left hS0, measure_mono_null Set.inter_subset_left hS0']
  · rw [← cond_mul_eq_inter (hzm hS) _ Q, ← cond_mul_eq_inter (hzm' hS) _ Q',
      mass_eq hz hG hz' hG' h0 hS, ← Measure.map_apply (measurable_tildeG hG _) hB,
      ← Measure.map_apply (measurable_tildeG hG' _) hB,
      piece_law hH hD0 hD hb hz hG hz' hG' h0 hS hS0 (dyPiece_noBirth hb')]

end BlockBand.SourceProcess.BornStopped
