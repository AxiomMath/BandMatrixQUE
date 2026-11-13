module

public import BlockBand.SourceProcess.PhysApprox.B3Pins

/-!
# The split of `ComplexClosedSummed` into six halves

`b3SummedErr` is, by definition, the sum of three summed errors:

* `genDriftSum c` (conditional drift error, steps without a birth), depending on `c` only;
* `genBrSum c c'` (conditional bilinear-bracket error, steps without a birth);
* `genBirthSum c` (birth error at birth steps), depending on `c` only.

`b3SummedErr_eq_gen` records this (`rfl`), and `genBrSum_comm_inl_inr` swaps a mixed pair. Hence
`ComplexClosedSummed` follows from six halves (`complexClosedSummed_of_parts`):

* the `𝒦` halves: `KDriftSummed` (`𝒦` drift), `KBracketSummed` (every pair with a `𝒦`
  coordinate first: `d𝒦 d𝒦` and `d𝒦 dG`), `KConjSummed` (`d𝒦 d𝒦̄`, i.e. `b3ConjErr`);
* the Gram halves `GenReqGramDrift`, `GenReqGramBracket`, and the birth half `GenReqBirth`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## The per-step errors and the step sets
-/

/-- The steps `n_s ≤ j < ⌊WT⌋` without a birth. -/
def genNoBirthSteps (s T : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W : ℕ) : Finset ℕ :=
  (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => ¬ IsBirthStep τ W j)

/-- The steps `n_s ≤ j < ⌊WT⌋` with a birth. -/
def genBirthSteps (s T : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W : ℕ) : Finset ℕ :=
  (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => IsBirthStep τ W j)

/-- The conditional drift error of coordinate `c` at step `j` (summand of `b3SummedErr`). -/
def genDriftStep (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) : ℝ≥0∞ :=
  ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
      (closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs c) |
        b3Sigma W j np] y - (W : ℂ)⁻¹ * cDrift b E c (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ
    ∂closedLaw b W np

/-- The conditional bilinear-bracket error of `c, c'` at step `j` (summand of `b3SummedErr`). -/
def genBrStep (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c c' : CIdx K np) : ℝ≥0∞ :=
  ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
      (closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator
          (fun y => b3dX b E s h τ m W j Vs c y * b3dX b E s h τ m W j Vs c' y) |
        b3Sigma W j np] y -
      (W : ℂ)⁻¹ * cCov b E c c' (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ ∂closedLaw b W np

/-- The birth error of coordinate `c` at step `j` (summand of `b3SummedErr`). -/
def genBirthStep (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) : ℝ≥0∞ :=
  ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
      b3dX b E s h τ m W j Vs c y - cEntry c (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j)) y‖ₑ
    ∂closedLaw b W np

/-- The conditional conjugate-bracket error of `𝒦_ij, 𝒦_kl` at step `j` (summand of
`b3ConjErr`). -/
def genConjStep (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij kl : Fin np × Fin np) :
    ℝ≥0∞ :=
  ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
      (closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
          b3dX b E s h τ m W j Vs (Sum.inr ij) y * conj (b3dX b E s h τ m W j Vs (Sum.inr kl) y)) |
        b3Sigma W j np] y -
      (W : ℂ)⁻¹ * kConjCov b E ij kl (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ
    ∂closedLaw b W np

/-!
## The three summed errors
-/

/-- The summed drift error of `c`. -/
def genDriftSum (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) : ℝ≥0∞ :=
  ∑ j ∈ genNoBirthSteps s T τ W, genDriftStep b E s h τ m R W j Vs c

/-- The summed bilinear-bracket error of `c, c'`. -/
def genBrSum (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c c' : CIdx K np) : ℝ≥0∞ :=
  ∑ j ∈ genNoBirthSteps s T τ W, genBrStep b E s h τ m R W j Vs c c'

/-- The summed birth error of `c`. -/
def genBirthSum (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) : ℝ≥0∞ :=
  ∑ j ∈ genBirthSteps s T τ W, genBirthStep b E s h τ m R W j Vs c

/-- **`b3SummedErr` is the sum of the three summed errors** (by definition). -/
theorem b3SummedErr_eq_gen (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c c' : CIdx K np) :
    b3SummedErr b E s T h τ m R W Vs c c' =
      genDriftSum b E s T h τ m R W Vs c + genBrSum b E s T h τ m R W Vs c c' +
        genBirthSum b E s T h τ m R W Vs c := rfl

/-- **`b3ConjErr` is the sum of the per-step conjugate errors** (by definition). -/
theorem b3ConjErr_eq_gen (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij kl : Fin np × Fin np) :
    b3ConjErr b E s T h τ m R W Vs ij kl =
      ∑ j ∈ genNoBirthSteps s T τ W, genConjStep (K := K) b E s h τ m R W j Vs ij kl := rfl

/-- The bracket error is symmetric in a pair whose coefficient is symmetric. -/
theorem genBrStep_comm (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c c' : CIdx K np)
    (hcov : ∀ G, cCov b E c c' G = cCov b E c' c G) :
    genBrStep b E s h τ m R W j Vs c c' = genBrStep b E s h τ m R W j Vs c' c := by
  unfold genBrStep
  have h1 : (fun y => b3dX b E s h τ m W j Vs c y * b3dX b E s h τ m W j Vs c' y) =
      fun y => b3dX b E s h τ m W j Vs c' y * b3dX b E s h τ m W j Vs c y :=
    funext fun _ => mul_comm _ _
  rw [h1]
  simp only [hcov]

/-- **A mixed Gram–`𝒦` bracket error equals the `𝒦`–Gram one** (`cCov` is `kGramCov` both
ways). -/
theorem genBrSum_comm_inl_inr (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) (ij : Fin np × Fin np) :
    genBrSum b E s T h τ m R W Vs (Sum.inl e) (Sum.inr ij) =
      genBrSum b E s T h τ m R W Vs (Sum.inr ij) (Sum.inl e) := by
  unfold genBrSum
  exact Finset.sum_congr rfl fun j _ =>
    genBrStep_comm b E s h τ m R W j Vs (Sum.inl e) (Sum.inr ij) fun _ => rfl

/-!
## The six halves
-/

/-- **The summed `𝒦` drift error vanishes** (the closed drift of `𝒦` is `0`). -/
def KDriftSummed : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (ij : Fin np × Fin np),
    Tendsto (fun W => genDriftSum b E s T h τ m R W (Vs W) (Sum.inr ij : CIdx K np)) atTop
      (𝓝 0)

/-- **The summed bracket error of every pair with a `𝒦` coordinate first vanishes**:
`d𝒦 d𝒦 = 0` (`c' = inr`) and `d𝒦 dG = kGramCov` (`c' = inl`). -/
def KBracketSummed : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (ij : Fin np × Fin np) (c' : CIdx K np),
    Tendsto (fun W => genBrSum b E s T h τ m R W (Vs W) (Sum.inr ij) c') atTop (𝓝 0)

/-- **The summed conjugate-bracket error vanishes** (`d𝒦 d𝒦̄ = kConjCov`); this is the second
conjunct of `ComplexClosedSummed`. -/
def KConjSummed : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (ij kl : Fin np × Fin np),
    Tendsto (fun W => b3ConjErr b E s T h τ m R W (Vs W) ij kl) atTop (𝓝 0)

/-- **The summed Gram drift error vanishes** (Gram half). -/
def GenReqGramDrift : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs →
    ∀ (R : ℝ) (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    Tendsto (fun W => genDriftSum b E s T h τ m R W (Vs W) (Sum.inl e : CIdx K np)) atTop (𝓝 0)

/-- **The summed Gram–Gram bracket error vanishes** (Gram half). -/
def GenReqGramBracket : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs →
    ∀ (R : ℝ) (e e' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    Tendsto (fun W => genBrSum b E s T h τ m R W (Vs W) (Sum.inl e : CIdx K np) (Sum.inl e'))
      atTop (𝓝 0)

/-- **The summed birth error of every coordinate vanishes** (birth half). -/
def GenReqBirth : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (c : CIdx K np),
    Tendsto (fun W => genBirthSum b E s T h τ m R W (Vs W) c) atTop (𝓝 0)

/-- **Assembly of `ComplexClosedSummed`**: the six halves give `ComplexClosedSummed`. -/
theorem complexClosedSummed_of_parts (hGD : GenReqGramDrift) (hGB : GenReqGramBracket)
    (hB : GenReqBirth) (hKD : KDriftSummed) (hKB : KBracketSummed) (hKC : KConjSummed) :
    ComplexClosedSummed := by
  intro b E np τ m T s h K Vs hD R
  refine ⟨fun c c' => ?_, fun ij kl => hKC b E np τ m T s h K Vs hD R ij kl⟩
  have hd : Tendsto (fun W => genDriftSum b E s T h τ m R W (Vs W) c) atTop (𝓝 0) := by
    rcases c with e | ij
    · exact hGD b E np τ m T s h K Vs hD R e
    · exact hKD b E np τ m T s h K Vs hD R ij
  have hbr : Tendsto (fun W => genBrSum b E s T h τ m R W (Vs W) c c') atTop (𝓝 0) := by
    rcases c with e | ij
    · rcases c' with e' | kl
      · exact hGB b E np τ m T s h K Vs hD R e e'
      · simp only [genBrSum_comm_inl_inr]
        exact hKB b E np τ m T s h K Vs hD R kl (Sum.inl e)
    · exact hKB b E np τ m T s h K Vs hD R ij c'
  have hbi := hB b E np τ m T s h K Vs hD R c
  simp only [b3SummedErr_eq_gen]
  simpa using (hd.add hbr).add hbi

end BlockBand.SourceProcess.PhysApprox.B3
