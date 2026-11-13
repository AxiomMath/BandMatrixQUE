module

public import BlockBand.SourceProcess.ContractingWords.LayerWord
public import BlockBand.SourceProcess.CompleteSourceGap.Bridge
public import BlockBand.Transmission.Bridge.TransportFull

/-!
# The exact one-step update along the path (almost surely)

`ae_productValue_step`: almost surely, for every `j ≥ 1` with all tag births `k_a < j`,
* `Z_{j+1} = newProd A_j c_j N_j D_j S_j Zs`: letters `A_j = letterMatrix j`, injections
  `c_j = injCoef q W j` (`q_a((j+1)/W)/W²` for interval sources), `N_j = transportN`,
  `D_j = freshD` (`Y_{j+1;j} = D_j*D_j`), new separators `S_j = sepOf 𝕏_{j+1}` with
  `𝕏_{j+1} = freshTwoPortSchur E 𝕏_j (fresh_j)`;
* `Z_j = coreProd A_j (sepOf 𝕏_j) Zs`.
Inputs: `ae_pathCurrent_succ_full`, `ae_tagResponse_succ_full`, `ae_tagResponse_succ_new_full`
(Bridge), `ae_pathSchur_succ_eq_freshTwoPortSchur` and `separatorMatrix_eq_sepOf`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.Bridge

variable {W nT nI : ℕ}

/-- The injection weights of the step `j → j+1`: `q_a((j+1)/W)/W²` for interval source `a`. -/
def injCoef (q : Fin nI → ℝ → ℝ) (W j : ℕ) : TraceLetter nT nI → ℝ
  | .current => 0
  | .tag _ => 0
  | .interval a => q a (((j + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2

/-- The old two-port Schur matrix `𝕏_j`. -/
abbrev pathXX (E : ℝ) (W j : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  pathSchur E (pathAt W j ω)

theorem intervalSource_succ (b E : ℝ) (j : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W)
    (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (hold : ∀ k, k < j → tagResponse b E W (j + 1) k ω = Nᴴ * tagResponse b E W j k ω * N)
    (hnew : tagResponse b E W (j + 1) j ω = Dᴴ * D) :
    intervalSource b E W (j + 1) q ω =
      Nᴴ * intervalSource b E W j q ω * N +
        ((q (((j + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ) • (Dᴴ * D) := by
  rw [intervalSource, Finset.sum_range_succ, hnew, intervalSource, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hold k (Finset.mem_range.mp hk), Matrix.mul_smul, Matrix.smul_mul]

/-- **The letters at `j+1`**, almost surely. -/
theorem ae_letter_succ {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → (∀ a, k a < j) → ∀ ℓ : TraceLetter nT nI,
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
    rw [hT j hj (k a) (hk a), Matrix.mul_smul, Matrix.smul_mul]
  | interval a =>
    simp only [letterMatrix, injCoef]
    exact intervalSource_succ b E j (q a) ω _ _ (fun k hk => hT j hj k hk) (hN j hj)

/-- **The exact update of a product of words**, almost surely. -/
theorem ae_productValue_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → (∀ a, k a < j) → ∀ Zs : List (TraceWord nT nI),
      productValue b E k q W (j + 1) ω Zs =
          newProd (letterMatrix b E k q W j ω) (injCoef q W j) (transportN b E W j ω)
            (freshD b E (pathXX E W j ω) (freshSample W j ω))
            (sepOf b E (freshTwoPortSchur E (pathXX E W j ω) (freshSample W j ω))) Zs ∧
        productValue b E k q W j ω Zs =
          coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) Zs := by
  filter_upwards [ae_letter_succ hb0 hb hE1 hE2 hW k q, ae_isUnit_pathPencil_growth hb hW E,
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

end BlockBand.SourceProcess.ContractingWords
