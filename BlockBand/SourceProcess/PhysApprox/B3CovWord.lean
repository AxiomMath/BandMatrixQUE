module

public import BlockBand.SourceProcess.PhysApprox.B3CovLayer
public import BlockBand.SourceProcess.ContractingWords.WordsHolds

/-!
# The `LayerCov` shape from `LayerCov` and a word representation

* **`CovWordRep e Z`**, **`ConjWordRep e Z`** (hypotheses): the representation a.e. on the alive
  set, for the brackets of `CovLayerHyp` and `ConjLayerHyp`;
* `cov_list_sum_bound`, `isWordCovRep_bound`: the deterministic estimate, by `LayerCov` term
  by term;
* **`covLayerHyp_of_rep`**, **`conjLayerHyp_of_rep`**: `LayerCov → CovWordRep → CovLayerHyp`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.SourceProcess.ContractingWords (LayerCov layerNew layerErr layerRem contrCov
  currentOf coreProd injCoef layerCov_holds)
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## The deterministic estimate
-/

/-- A combination with coefficients of modulus `≤ 1` of terms within `B` of their predictions. -/
theorem cov_list_sum_bound {α : Type*} (L : List α) (a f g : α → ℂ) (c : ℂ) {B : ℝ}
    (h : ∀ p ∈ L, ‖a p‖ ≤ 1 ∧ ‖f p - c * g p‖ ≤ B) :
    ‖(L.map fun p => a p * f p).sum - c * (L.map fun p => a p * g p).sum‖ ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hp := h p List.mem_cons_self
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have key : a p * f p + (L.map fun p => a p * f p).sum -
        c * (a p * g p + (L.map fun p => a p * g p).sum) =
        a p * (f p - c * g p) +
          ((L.map fun p => a p * f p).sum - c * (L.map fun p => a p * g p).sum) := by ring
    rw [key]
    calc ‖a p * (f p - c * g p) +
          ((L.map fun p => a p * f p).sum - c * (L.map fun p => a p * g p).sum)‖
        ≤ ‖a p * (f p - c * g p)‖ +
          ‖(L.map fun p => a p * f p).sum - c * (L.map fun p => a p * g p).sum‖ :=
          norm_add_le _ _
      _ ≤ 1 * B + L.length * B := by
          refine add_le_add ?_ ih'
          rw [norm_mul]
          exact mul_le_mul hp.1 hp.2 (norm_nonneg _) zero_le_one
      _ = ((L.length + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- **The word representation at one point** (see the module docstring). -/
def IsWordCovRep (b E : ℝ) (d : ℕ) (K₀ c₀ : ℝ) (M : ℕ) (CR : ℝ) (W : ℕ) (x κ : ℂ)
    (ev zv : ℝ) : Prop :=
  ∃ (s : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (nT nI : ℕ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (q : Fin nI → ℝ → ℝ) (j : ℕ) (L : List (ℂ × TraceWord nT nI × TraceWord nT nI)),
    IsStationaryJet b E s ∧ XX.IsHermitian ∧ (∀ ℓ, (A ℓ).IsHermitian) ∧
    (∀ ℓ, nuclearNorm (A ℓ) ≤ K₀) ∧ A .current = currentOf b E XX ∧ (∀ a t, |q a t| ≤ c₀) ∧
    L.length ≤ M ∧
    (∀ p ∈ L, ‖p.1‖ ≤ 1 ∧ IsOrdinaryWord p.2.1 ∧ IsOrdinaryWord p.2.2 ∧ p.2.1.length ≤ d ∧
      p.2.2.length ≤ d ∧
      ((contrCov p.2.1 p.2.2).map fun Zs => ‖coreProd A (sepOf b E XX) Zs‖).sum ≤ CR * zv) ∧
    layerErr b E s XX = ev ∧ 0 ≤ ev ∧
    x = (L.map fun p => p.1 * ∫ y,
        (layerNew b E A (injCoef q W j) XX p.2.1 y - coreProd A (sepOf b E XX) [p.2.1]) *
          (layerNew b E A (injCoef q W j) XX p.2.2 y - coreProd A (sepOf b E XX) [p.2.2])
          ∂freshLaw W b).sum ∧
    κ = (L.map fun p => p.1 * MvPolynomial.eval (fun u => coreProd A (sepOf b E XX) [u])
        (wordCov (transportD0 b E) p.2.1 p.2.2)).sum

/-- **`LayerCov` term by term**: a represented bracket has the `LayerCov` shape, with constant
`M C (C_R + 1)` and exponent `2d + 4`. -/
theorem isWordCovRep_bound (hLC : LayerCov) {b E κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κI) (hE : E ∈ bulkInterval κI) (d : ℕ) {K₀ c₀ CR : ℝ} (hK₀ : 0 ≤ K₀)
    (hc₀ : 0 ≤ c₀) (hCR : 0 ≤ CR) (M : ℕ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ (x κv : ℂ) (ev zv : ℝ), 0 ≤ zv →
      IsWordCovRep b E d K₀ c₀ M CR W x κv ev zv →
      ‖x - (W : ℂ)⁻¹ * κv‖ ≤ (M * C * (CR + 1)) * (ev * zv) +
        (M * C * (CR + 1)) * ((W : ℝ)⁻¹ / Real.sqrt W + ev ^ 2 + ev ^ (2 * d + 4)) := by
  obtain ⟨C, W₀, hC, hLay⟩ := hLC b hb0 hb κI hκ d K₀ c₀ hK₀ hc₀
  refine ⟨C, W₀, hC, fun W hW x κv ev zv hzv hrep => ?_⟩
  obtain ⟨s, XX, nT, nI, A, q, j, L, hs, hXX, hAh, hAn, hAc, hq, hLlen, hLp, hev, hev0, hx,
    hκv⟩ := hrep
  subst hx hκv
  set R0 : ℝ := (W : ℝ)⁻¹ / Real.sqrt W + ev ^ 2 + ev ^ (2 * d + 4) with hR0
  have hR0n : 0 ≤ R0 := by rw [hR0]; positivity
  have hB0 : 0 ≤ C * ev * (CR * zv) + C * R0 := by positivity
  have hterm : ∀ p ∈ L, ‖p.1‖ ≤ 1 ∧
      ‖(∫ y, (layerNew b E A (injCoef q W j) XX p.2.1 y - coreProd A (sepOf b E XX) [p.2.1]) *
          (layerNew b E A (injCoef q W j) XX p.2.2 y - coreProd A (sepOf b E XX) [p.2.2])
          ∂freshLaw W b) - (W : ℂ)⁻¹ * MvPolynomial.eval (fun u => coreProd A (sepOf b E XX) [u])
            (wordCov (transportD0 b E) p.2.1 p.2.2)‖ ≤ C * ev * (CR * zv) + C * R0 := by
    intro p hp
    obtain ⟨h1, hw, hv, hwl, hvl, hcon⟩ := hLp p hp
    have hb := hLay W hW E hE s hs XX hXX nT nI A q j hAh hAn hAc hq p.2.1 p.2.2 hw hv hwl hvl
    rw [hev] at hb
    refine ⟨h1, hb.trans (add_le_add (mul_le_mul_of_nonneg_left hcon (mul_nonneg hC hev0))
      (le_of_eq ?_))⟩
    rw [hR0]; rfl
  have hsum := cov_list_sum_bound L (fun p => p.1)
    (fun p => ∫ y, (layerNew b E A (injCoef q W j) XX p.2.1 y -
        coreProd A (sepOf b E XX) [p.2.1]) *
      (layerNew b E A (injCoef q W j) XX p.2.2 y - coreProd A (sepOf b E XX) [p.2.2])
        ∂freshLaw W b)
    (fun p => MvPolynomial.eval (fun u => coreProd A (sepOf b E XX) [u])
      (wordCov (transportD0 b E) p.2.1 p.2.2)) ((W : ℂ)⁻¹) hterm
  refine hsum.trans ?_
  have hM : (L.length : ℝ) ≤ M := by exact_mod_cast hLlen
  have h1 : 0 ≤ (M : ℝ) * C * (ev * zv) := by positivity
  have h2 : 0 ≤ (M : ℝ) * C * R0 := by positivity
  calc (L.length : ℝ) * (C * ev * (CR * zv) + C * R0)
      ≤ M * (C * ev * (CR * zv) + C * R0) := mul_le_mul_of_nonneg_right hM hB0
    _ ≤ (M * C * (CR + 1)) * (ev * zv) + (M * C * (CR + 1)) * R0 := by
        nlinarith [mul_nonneg hCR h1, mul_nonneg hCR h2]

/-!
## The representation estimates
-/

/-- **The word representation of the raw closed brackets** (the full-source calculation with
finitely many far open channels). There are `d, M` and `K₀, c₀, C_R ≥ 0` such that, eventually
in `W`, at every no-birth step `j`, for all coordinates `c, c'`, a.e. on the alive set,
`E_j[1_{A_j} dX_c dX_c']` and `cCov_{c,c'}(G_j)` have an `IsWordCovRep` with scale `e_j` and
contracting size `|Z_j|`.
-/
def CovWordRep (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (d M : ℕ) (K₀ c₀ CR : ℝ),
    0 ≤ K₀ ∧ 0 ≤ c₀ ∧ 0 ≤ CR ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c c' : CIdx K np,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        IsWordCovRep b E d K₀ c₀ M CR W
          ((closedLaw b W np)[(b3Alive b E s h τ m R W j (Vs W)).indicator
            (fun y => b3dX b E s h τ m W j (Vs W) c y * b3dX b E s h τ m W j (Vs W) c' y) |
            b3Sigma W j np] y)
          (cCov b E c c' (b3ClosedGramAt b E s h τ m W j (Vs W) y))
          (e b E np τ m s h K W (Vs W) j y) ‖Z b E np τ m s h K W (Vs W) j y‖

/-- **The word representation of the raw closed conjugate brackets**, as `CovWordRep` for
`E_j[1_{A_j} d𝒦_ij conj d𝒦_kl]` and `kConjCov`. -/
def ConjWordRep (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (d M : ℕ) (K₀ c₀ CR : ℝ),
    0 ≤ K₀ ∧ 0 ≤ c₀ ∧ 0 ≤ CR ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij kl : Fin np × Fin np,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        IsWordCovRep b E d K₀ c₀ M CR W
          ((closedLaw b W np)[(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            b3dX b E s h τ m W j (Vs W) (Sum.inr ij : CIdx K np) y *
              conj (b3dX b E s h τ m W j (Vs W) (Sum.inr kl : CIdx K np) y)) |
            b3Sigma W j np] y)
          (kConjCov b E ij kl (b3ClosedGramAt b E s h τ m W j (Vs W) y))
          (e b E np τ m s h K W (Vs W) j y) ‖Z b E np τ m s h K W (Vs W) j y‖

/-- A bulk margin for an energy in `(-2, 2)`. -/
theorem cov_bulk {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    0 < min (E + 2) (2 - E) ∧ E ∈ bulkInterval (min (E + 2) (2 - E)) := by
  refine ⟨lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left (E + 2) (2 - E); linarith
  · have := min_le_right (E + 2) (2 - E); linarith

/-- **`LayerCov + CovWordRep ⇒ CovLayerHyp`.** -/
theorem covLayerHyp_of_rep {e Z : CovField} (hLC : LayerCov) (hR : CovWordRep e Z) :
    CovLayerHyp e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  obtain ⟨d, M, K₀, c₀, CR, hK₀, hc₀, hCR, hev⟩ := hR b E np τ m T s h K Vs hFD R
  obtain ⟨C, W₀, hC, hB⟩ := isWordCovRep_bound hLC hb0 hb hκ hE d hK₀ hc₀ hCR M
  refine ⟨M * C * (CR + 1), 2 * d + 4, by positivity, by omega, ?_⟩
  filter_upwards [hev, eventually_ge_atTop W₀] with W hW hW0 j hj c c'
  filter_upwards [hW j hj c c'] with y hy hyA
  exact hB W hW0 _ _ _ _ (norm_nonneg _) (hy hyA)

/-- **`LayerCov + ConjWordRep ⇒ ConjLayerHyp`.** -/
theorem conjLayerHyp_of_rep {e Z : CovField} (hLC : LayerCov) (hR : ConjWordRep e Z) :
    ConjLayerHyp e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  obtain ⟨d, M, K₀, c₀, CR, hK₀, hc₀, hCR, hev⟩ := hR b E np τ m T s h K Vs hFD R
  obtain ⟨C, W₀, hC, hB⟩ := isWordCovRep_bound hLC hb0 hb hκ hE d hK₀ hc₀ hCR M
  refine ⟨M * C * (CR + 1), 2 * d + 4, by positivity, by omega, ?_⟩
  filter_upwards [hev, eventually_ge_atTop W₀] with W hW hW0 j hj ij kl
  filter_upwards [hW j hj ij kl] with y hy hyA
  exact hB W hW0 _ _ _ _ (norm_nonneg _) (hy hyA)

/-!
## The three targets from the contract hypotheses
-/

/-- **Target `KStepCov`** from the input hypotheses (via `layerCov_holds`), the word representation,
the error moments, decay and the `L²` hypotheses `GenStepMemL2`, `GenStepMeanL2`.
-/
theorem kStepCov_of_word {e Z : CovField} (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hL2 : GenStepMemL2)
    (hM : GenStepMeanL2) (hR : CovWordRep e Z) (hE : CovErrMoments e) (hD : CovDecayHyp Z) :
    KStepCov :=
  kStepCov_of_layer hL2 hM (covLayerHyp_of_rep (layerCov_holds hGA hLp hP) hR) hE hD

/-- **Target `KStepConjCov`** from the input hypotheses, the conjugate representation, the error
moments, decay and the `L²` hypotheses `GenStepMemL2`, `GenStepMeanL2`.
-/
theorem kStepConjCov_of_word {e Z : CovField} (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hL2 : GenStepMemL2)
    (hM : GenStepMeanL2) (hR : ConjWordRep e Z) (hE : CovErrMoments e) (hD : CovDecayHyp Z) :
    KStepConjCov :=
  kStepConjCov_of_layer hL2 hM (conjLayerHyp_of_rep (layerCov_holds hGA hLp hP) hR) hE hD

/-- **Target `GramSumStepCov`** from the input hypotheses, the word representation, the error
moments, decay and the Gram `L²` hypotheses `GramSumStepMemL2`, `GramSumStepMeanL2`.
-/
theorem gramSumStepCov_of_word {e Z : CovField} (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hL2 : GramSumStepMemL2)
    (hM : GramSumStepMeanL2) (hR : CovWordRep e Z) (hE : CovErrMoments e)
    (hD : CovDecayHyp Z) : GramSumStepCov :=
  gramSumStepCov_of_layer hL2 hM (covLayerHyp_of_rep (layerCov_holds hGA hLp hP) hR) hE hD

end BlockBand.SourceProcess.PhysApprox.B3
