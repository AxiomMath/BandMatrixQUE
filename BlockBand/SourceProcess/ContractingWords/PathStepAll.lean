module

public import BlockBand.SourceProcess.ContractingWords.StepState

/-!
# The exact one-step update with unborn tags

When no tag is born at the step `j → j+1`, the letters at `j+1`, the values of products of words and
their conditional mean are given exactly by the fresh layer added at that step.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.Bridge

variable {W nT nI : ℕ}

theorem tagResponse_eq_zero_of_le (b E : ℝ) {n k : ℕ} (h : n ≤ k) (ω : GrowthPath W) :
    tagResponse b E W n k ω = 0 := by
  have hP : tagProjection W n k = 0 := by
    ext x y
    simp only [tagProjection, Matrix.diagonal_apply, Matrix.zero_apply]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  simp [tagResponse, hP]

/-- **The letters at `j+1`** when no tag is born at the step. -/
theorem ae_letter_succ' {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → (∀ a, j ≠ k a) → ∀ ℓ : TraceLetter nT nI,
      letterMatrix b E k q W (j + 1) ω ℓ =
        (transportN b E W j ω)ᴴ * letterMatrix b E k q W j ω ℓ * transportN b E W j ω +
          (injCoef q W j ℓ : ℂ) • ((freshD b E (pathXX E W j ω) (freshSample W j ω))ᴴ *
            freshD b E (pathXX E W j ω) (freshSample W j ω)) := by
  filter_upwards [ae_pathCurrent_succ_full hb0 hb hE1 hE2 hW,
    ae_tagResponse_succ_full hb0 hb hE1 hE2 hW, ae_tagResponse_succ_new_full hb0 hb hE1 hE2 hW]
    with ω hJ hT hN j hj hk ℓ
  cases ℓ with
  | current => simp [letterMatrix, injCoef, hJ j hj]
  | tag a =>
    simp only [letterMatrix, injCoef, Complex.ofReal_zero, zero_smul, add_zero]
    by_cases hka : k a < j
    · rw [hT j hj (k a) hka, Matrix.mul_smul, Matrix.smul_mul]
    · have h1 : j + 1 ≤ k a := by have := hk a; omega
      rw [tagResponse_eq_zero_of_le b E h1, tagResponse_eq_zero_of_le b E (by omega : j ≤ k a)]
      simp
  | interval a =>
    simp only [letterMatrix, injCoef]
    exact intervalSource_succ b E j (q a) ω _ _ (fun k hk => hT j hj k hk) (hN j hj)

/-- **The exact update of a product of words** when no tag is born at the step. -/
theorem ae_productValue_step' {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → (∀ a, j ≠ k a) → ∀ Zs : List (TraceWord nT nI),
      productValue b E k q W (j + 1) ω Zs =
          newProd (letterMatrix b E k q W j ω) (injCoef q W j) (transportN b E W j ω)
            (freshD b E (pathXX E W j ω) (freshSample W j ω))
            (sepOf b E (freshTwoPortSchur E (pathXX E W j ω) (freshSample W j ω))) Zs ∧
        productValue b E k q W j ω Zs =
          coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) Zs := by
  filter_upwards [ae_letter_succ' hb0 hb hE1 hE2 hW k q, ae_isUnit_pathPencil_growth hb hW E,
    ae_pathSchur_succ_eq_freshTwoPortSchur hb hW E] with ω hL hF hX j hj hk Zs
  have hS1 : ∀ σ, separatorMatrix b E W (j + 1) ω σ =
      sepOf b E (freshTwoPortSchur E (pathXX E W j ω) (freshSample W j ω)) σ := fun σ => by
    rw [separatorMatrix_eq_sepOf b E (j + 1) ω (hF (j + 1)), hX j hj]
  have hS0 : ∀ σ, separatorMatrix b E W j ω σ = sepOf b E (pathXX E W j ω) σ := fun σ =>
    separatorMatrix_eq_sepOf b E j ω (hF j) σ
  constructor
  · simp only [productValue, newProd]
    congr 1
    refine List.map_congr_left fun w _ => ?_
    simp only [wordValue, newWord]
    congr 2
    refine List.map_congr_left fun x _ => ?_
    rw [hL j hj hk x.1, hS1 x.2]
  · simp only [productValue, coreProd]
    congr 1
    refine List.map_congr_left fun w _ => ?_
    simp only [wordValue, matWord, letWord, List.map_map]
    congr 2
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, hS0 x.2]

/-- **The path step in state form** when no tag is born at the step. -/
theorem ae_step_state' {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → (∀ a, j ≠ k a) → ∀ Zs : List (TraceWord nT nI),
      productValue b E k q W (j + 1) ω Zs =
          stateΨ b E k q W j Zs (pastCoords W j ω, freshSample W j ω) ∧
        productValue b E k q W j ω Zs =
          coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) Zs := by
  filter_upwards [ae_productValue_step' hb0 hb hE1 hE2 hW k q] with ω h j hj hk Zs
  refine ⟨?_, (h j hj hk Zs).2⟩
  rw [(h j hj hk Zs).1, stateΨ, stateZ_extPast]
  rfl

/-- **The conditional mean of the step** when no tag is born at the step. -/
theorem condExp_step' {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j)
    (hk : ∀ a, j ≠ k a) (Zs : List (TraceWord nT nI))
    (hint : Integrable (fun ω => productValue b E k q W (j + 1) ω Zs) (growthPathLaw W b)) :
    (growthPathLaw W b)[fun ω => productValue b E k q W (j + 1) ω Zs | growthSigma W j] =ᵐ[
      growthPathLaw W b] fun ω => ∫ y, stateZ b E k q W j Zs ω y ∂freshLaw W b := by
  have hae : (fun ω => productValue b E k q W (j + 1) ω Zs) =ᵐ[growthPathLaw W b]
      fun ω => stateΨ b E k q W j Zs (pastCoords W j ω, freshSample W j ω) := by
    filter_upwards [ae_step_state' hb0 hb hE1 hE2 hW k q] with ω h
    exact (h j hj hk Zs).1
  have hint' := hint.congr hae
  refine (condExp_congr_ae hae).trans ((condExp_past_fresh b j (measurable_stateΨ b E k q j Zs)
    hint').trans (Eventually.of_forall fun ω => ?_))
  simp only [stateΨ, stateZ_extPast]

end BlockBand.SourceProcess.ContractingWords
