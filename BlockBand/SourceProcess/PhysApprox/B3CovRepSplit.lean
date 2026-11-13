module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepErr

/-!
# The bracket estimates split into Gram pairs and `𝒦` pairs, with concrete fields

* `CovLayerAt`: the `LayerCov`-shaped bound of `CovLayerHyp` at one pair
  (`covLayerHyp_iff`: `CovLayerHyp` is this bound at every pair, `Iff.rfl`);
* **`CovWordRepGram e Z`** (hypothesis): `CovWordRep` restricted to Gram–Gram pairs;
* **`CovLayerHypK e Z`**: `CovLayerHyp` restricted to pairs with a `𝒦` coordinate, proved directly
  rather than through words (for the concrete fields: `covLayerHypK_of_mixed`,
  `covLayerHypK_of_nearG`);
* **`covLayerHyp_of_parts : LayerCov → CovWordRepGram e Z → CovLayerHypK e Z → CovLayerHyp e Z`**.
  The sign `e ≥ 0` needed to merge the two constants comes from the Gram
  representation (`IsWordCovRep` contains `0 ≤ e`) at the diagonal Gram coordinate of a probe;
* `kStepCov_of_covRep`, `gramSumStepCov_of_covRep`, `kStepConjCov_of_covRep`,
  `complexClosedSummed_of_covRep`: the targets with `e = b3CovErr`, `Z = b3CovZ`.

The targets below do not use `CovDecayHyp` or `CovErrMoments` as hypotheses: for the concrete
fields these are proved (`covErrMoments_b3CovErr`, `covDecayHyp_b3CovZ`).
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
open BlockBand.SourceProcess.ContractingWords (LayerCov layerCov_holds)
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## The bound at one pair
-/

/-- The `LayerCov`-shaped bound of `CovLayerHyp` at one coordinate pair `c, c'`. -/
def CovLayerAt (e Z : CovField) (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (s h R : ℝ) {K W : ℕ}
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (j : ℕ) (C : ℝ) (N : ℕ)
    (c c' : CIdx K np) : Prop :=
  ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
    ‖(closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator
        (fun y => b3dX b E s h τ m W j Vs c y * b3dX b E s h τ m W j Vs c' y) |
        b3Sigma W j np] y -
      (W : ℂ)⁻¹ * cCov b E c c' (b3ClosedGramAt b E s h τ m W j Vs y)‖ ≤
    C * (e b E np τ m s h K W Vs j y * ‖Z b E np τ m s h K W Vs j y‖) +
      C * ((W : ℝ)⁻¹ / Real.sqrt W + e b E np τ m s h K W Vs j y ^ 2 +
        e b E np τ m s h K W Vs j y ^ N)

theorem covLayerHyp_iff (e Z : CovField) :
    CovLayerHyp e Z ↔ ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ 2 ≤ N ∧
      ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c c' : CIdx K np,
        CovLayerAt e Z b E τ m s h R (Vs W) j C N c c' := Iff.rfl

/-!
## The split hypotheses
-/

/-- **The word representation for Gram–Gram pairs** (`CovWordRep` restricted to the Gram
coordinates). -/
def CovWordRepGram (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (d M : ℕ) (K₀ c₀ CR : ℝ),
    0 ≤ K₀ ∧ 0 ≤ c₀ ∧ 0 ≤ CR ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ g g' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        IsWordCovRep b E d K₀ c₀ M CR W
          ((closedLaw b W np)[(b3Alive b E s h τ m R W j (Vs W)).indicator
            (fun y => b3dX b E s h τ m W j (Vs W) (Sum.inl g) y *
              b3dX b E s h τ m W j (Vs W) (Sum.inl g') y) | b3Sigma W j np] y)
          (cCov b E (Sum.inl g) (Sum.inl g') (b3ClosedGramAt b E s h τ m W j (Vs W) y))
          (e b E np τ m s h K W (Vs W) j y) ‖Z b E np τ m s h K W (Vs W) j y‖

/-- **The `LayerCov` shape for the pairs with a `𝒦` coordinate**
(`cCov = kGramCov` for mixed pairs, `0` for `𝒦𝒦` pairs). It is proved directly from the closed
exact update `d𝒦 = u*Δv` and the fresh second moments of `Δ` (`covLayerHypK_of_mixed`). -/
def CovLayerHypK (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ 2 ≤ N ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c c' : CIdx K np,
      ((∃ ij, c = Sum.inr ij) ∨ (∃ ij, c' = Sum.inr ij)) →
        CovLayerAt e Z b E τ m s h R (Vs W) j C N c c'

/-- `CovWordRep` contains its Gram part. -/
theorem covWordRepGram_of_rep {e Z : CovField} (h : CovWordRep e Z) : CovWordRepGram e Z := by
  intro b E np τ m T s h' K Vs hFD R
  obtain ⟨d, M, K₀, c₀, CR, hK₀, hc₀, hCR, hev⟩ := h b E np τ m T s h' K Vs hFD R
  exact ⟨d, M, K₀, c₀, CR, hK₀, hc₀, hCR, hev.mono fun W hW j hj g g' => hW j hj _ _⟩

/-!
## Merging the two constants
-/

theorem isWordCovRep_nonneg {b E : ℝ} {d : ℕ} {K₀ c₀ : ℝ} {M : ℕ} {CR : ℝ} {W : ℕ} {x κ : ℂ}
    {ev zv : ℝ} (h : IsWordCovRep b E d K₀ c₀ M CR W x κ ev zv) : 0 ≤ ev := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hev0, -, -⟩ := h
  exact hev0

theorem pow_le_sq_add_pow {x : ℝ} (hx : 0 ≤ x) {a N : ℕ} (ha : 2 ≤ a) (haN : a ≤ N) :
    x ^ a ≤ x ^ 2 + x ^ N := by
  rcases le_total x 1 with h1 | h1
  · have := pow_le_pow_of_le_one hx h1 ha
    have := pow_nonneg hx N
    linarith
  · have := pow_le_pow_right₀ h1 haN
    have := sq_nonneg x
    linarith

/-- A `LayerCov`-shaped bound with `(Cᵢ, Nᵢ)` implies the one with `(2C', max)`, for `e ≥ 0`. -/
theorem cov_bound_weaken {Ci C' ev zv w : ℝ} {Ni N : ℕ} (hCi : 0 ≤ Ci) (hC' : Ci ≤ C')
    (hev : 0 ≤ ev) (hzv : 0 ≤ zv) (hw : 0 ≤ w) (hNi : 2 ≤ Ni) (hN : Ni ≤ N) {x : ℝ}
    (hx : x ≤ Ci * (ev * zv) + Ci * (w + ev ^ 2 + ev ^ Ni)) :
    x ≤ (2 * C') * (ev * zv) + (2 * C') * (w + ev ^ 2 + ev ^ N) := by
  have hp := pow_le_sq_add_pow hev hNi hN
  have hN0 := pow_nonneg hev N
  have h2 := sq_nonneg ev
  have hez : 0 ≤ ev * zv := mul_nonneg hev hzv
  have h1 : Ci * (ev * zv) ≤ (2 * C') * (ev * zv) :=
    mul_le_mul_of_nonneg_right (by linarith) hez
  have h3 : Ci * (w + ev ^ 2 + ev ^ Ni) ≤ (2 * C') * (w + ev ^ 2 + ev ^ N) := by
    calc Ci * (w + ev ^ 2 + ev ^ Ni) ≤ Ci * (w + ev ^ 2 + (ev ^ 2 + ev ^ N)) :=
          mul_le_mul_of_nonneg_left (by linarith) hCi
      _ ≤ C' * (w + ev ^ 2 + (ev ^ 2 + ev ^ N)) :=
          mul_le_mul_of_nonneg_right hC' (by positivity)
      _ ≤ (2 * C') * (w + ev ^ 2 + ev ^ N) := by nlinarith
  linarith

/-- **`LayerCov + CovWordRepGram + CovLayerHypK ⇒ CovLayerHyp`.** -/
theorem covLayerHyp_of_parts {e Z : CovField} (hLC : LayerCov) (hG : CovWordRepGram e Z)
    (hK : CovLayerHypK e Z) : CovLayerHyp e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  obtain ⟨d, M, K₀, c₀, CR, hK₀, hc₀, hCR, hevG⟩ := hG b E np τ m T s h K Vs hFD R
  obtain ⟨C₁, W₀, hC₁, hB⟩ := isWordCovRep_bound hLC hb0 hb hκ hE d hK₀ hc₀ hCR M
  obtain ⟨CK, NK, hCK, hNK, hevK⟩ := hK b E np τ m T s h K Vs hFD R
  set CG : ℝ := M * C₁ * (CR + 1) with hCGdef
  have hCG : 0 ≤ CG := by positivity
  refine ⟨2 * (CG + CK), max (2 * d + 4) NK, by positivity, le_max_of_le_right hNK, ?_⟩
  filter_upwards [hevG, hevK, eventually_ge_atTop W₀] with W hWG hWK hW0 j hj c c'
  have hw : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by positivity
  -- the bound from the `𝒦` estimate, given `e ≥ 0` from a diagonal Gram coordinate of a probe
  have hKcase : ∀ i : Fin np, ((∃ ij, c = Sum.inr ij) ∨ (∃ ij, c' = Sum.inr ij)) →
      CovLayerAt e Z b E τ m s h R (Vs W) j (2 * (CG + CK)) (max (2 * d + 4) NK) c c' := by
    intro i hc
    let g : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np) := (0, Sum.inr i, Sum.inr i)
    filter_upwards [hWK j hj c c' hc, hWG j hj g g] with y hy hyG hyA
    exact cov_bound_weaken hCK (by linarith) (isWordCovRep_nonneg (hyG hyA)) (norm_nonneg _) hw
      hNK (le_max_right _ _) (hy hyA)
  rcases c with g | ij
  · rcases c' with g' | kl
    · filter_upwards [hWG j hj g g'] with y hy hyA
      have hrep := hy hyA
      exact cov_bound_weaken hCG (by linarith) (isWordCovRep_nonneg hrep) (norm_nonneg _) hw
        (by omega) (le_max_left _ _) (hB W hW0 _ _ _ _ (norm_nonneg _) hrep)
    · exact hKcase kl.1 (Or.inr ⟨kl, rfl⟩)
  · exact hKcase ij.1 (Or.inl ⟨ij, rfl⟩)

/-!
## The targets with the concrete fields
-/

/-- **`KStepCov`** with `e = b3CovErr`, `Z = b3CovZ`. -/
theorem kStepCov_of_covRep (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hL2 : GenStepMemL2) (hM : GenStepMeanL2)
    (hG : CovWordRepGram b3CovErr b3CovZ) (hK : CovLayerHypK b3CovErr b3CovZ)
    (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp) (hg : ClosedCondLp) (hD : B3ClosedContrDecay) :
    KStepCov :=
  kStepCov_of_layer hL2 hM (covLayerHyp_of_parts (layerCov_holds hGA hLp hP) hG hK)
    (covErrMoments_b3CovErr h0 h1 hg) (covDecayHyp_b3CovZ hD)

/-- **`GramSumStepCov`** with `e = b3CovErr`, `Z = b3CovZ`. -/
theorem gramSumStepCov_of_covRep (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hL2 : GramSumStepMemL2) (hM : GramSumStepMeanL2)
    (hG : CovWordRepGram b3CovErr b3CovZ) (hK : CovLayerHypK b3CovErr b3CovZ)
    (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp) (hg : ClosedCondLp) (hD : B3ClosedContrDecay) :
    GramSumStepCov :=
  gramSumStepCov_of_layer hL2 hM (covLayerHyp_of_parts (layerCov_holds hGA hLp hP) hG hK)
    (covErrMoments_b3CovErr h0 h1 hg) (covDecayHyp_b3CovZ hD)

/-- **`KStepConjCov`** with `e = b3CovErr`, `Z = b3CovZ`. -/
theorem kStepConjCov_of_covRep (hL2 : GenStepMemL2) (hM : GenStepMeanL2)
    (hC : ConjLayerHyp b3CovErr b3CovZ) (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp)
    (hg : ClosedCondLp) (hD : B3ClosedContrDecay) : KStepConjCov :=
  kStepConjCov_of_layer hL2 hM hC (covErrMoments_b3CovErr h0 h1 hg) (covDecayHyp_b3CovZ hD)

/-- **`ComplexClosedSummed` from the layer hypotheses** with the concrete fields: the two drift
estimates, the birth half, the Gram representation, the `𝒦` bracket estimates, the closed jets and
the closed decay. -/
theorem complexClosedSummed_of_covRep (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hGD : GramSumStepDrift)
    (hB : GenReqBirth) (hKD : KStepDrift) (hG : CovWordRepGram b3CovErr b3CovZ)
    (hK : CovLayerHypK b3CovErr b3CovZ) (hC : ConjLayerHyp b3CovErr b3CovZ)
    (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp) (hg : ClosedCondLp) (hD : B3ClosedContrDecay) :
    ComplexClosedSummed :=
  complexClosedSummed_of_layer hGD hB hKD
    (covLayerHyp_of_parts (layerCov_holds hGA hLp hP) hG hK) hC
    (covErrMoments_b3CovErr h0 h1 hg) (covDecayHyp_b3CovZ hD)

end BlockBand.SourceProcess.PhysApprox.B3
