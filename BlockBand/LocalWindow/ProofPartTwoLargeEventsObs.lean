module

public import BlockBand.LocalWindow.ProofPartTwoLargeCentreRect

/-!
# The compressed grid observables of the large-`ρ` branch

Compressions of the two classes of part (ii) observables to the orthogonal complement of the pole
direction, and their distance to the compressed exact observable.

## Main results

* class (a), `B = B₀(ω)`: `largeObsA sel B₀ j₀ e ω = U(ω)* B₀(ω) U(ω)` (`measurable_largeObsA`,
  a Hermitian contraction, and **exactly** `U*BU`: `δ_J = 0`);
* class (b), `B = f(K₀(E))`: `largeObsB sel ε f j₀ e ω = f(compRegM e ω)` (`measurable_largeObsB`,
  given the Borel measurability of `X ↦ f(X)` on `Fin (2W - 1)`, as in
  `measurable_spectralFn`), a Hermitian contraction, and
  **`largeObsB_close`**: on the label event of `(j₀, E)` and `(j₀, e)`,
  `‖f(compRegM e) - U* f(K₀(E)) U‖ ≤ √(2W - 1) K₀ (‖C‖²/ε² + 1)|E - e| +
  √(2W)(3K₀K'² + 4K')/|ρ(E)|` (`‖F_reg(E) - E‖ ≤ K'`, `6K' ≤ |ρ(E)|`; operator Lipschitz
  `opNorm_spectralFn_sub_le` on the compressed block and the limiting compression
  `opNorm_compress_spectralTest_largeRho_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open scoped Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

attribute [local instance] pairSite_nonempty

/-- Class (a) compressed observable `U(ω)* B₀(ω) U(ω)`. -/
def largeObsA (sel : CEH.EigenpairSelection (2 * p.W)) (B₀ : SplitState p i → PairMatrix p i) :
    ExteriorSite p i → ℝ → SplitState p i → Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ :=
  fun j₀ _ om => (poleIsometry sel j₀ om)ᴴ * B₀ om * poleIsometry sel j₀ om

/-- Class (b) compressed grid observable `f(compRegM e ω)`. -/
def largeObsB (sel : CEH.EigenpairSelection (2 * p.W)) (ε : ℝ) (f : ℝ → ℝ) :
    ExteriorSite p i → ℝ → SplitState p i → Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ :=
  fun j₀ e om => BlockBand.LocalWindow.spectralFn f (compRegM sel ε j₀ e om)

theorem measurable_largeObsA (sel : CEH.EigenpairSelection (2 * p.W))
    {B₀ : SplitState p i → PairMatrix p i} (hB₀ : Measurable B₀) (j₀ : ExteriorSite p i)
    (e : ℝ) : Measurable (largeObsA sel B₀ j₀ e) :=
  measurable_poleCompress sel j₀ hB₀

theorem measurable_largeObsB (sel : CEH.EigenpairSelection (2 * p.W)) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ}
    (hfm : Measurable (BlockBand.LocalWindow.spectralFn (ι := Fin (2 * p.W - 1)) f))
    (j₀ : ExteriorSite p i) (e : ℝ) : Measurable (largeObsB sel ε f j₀ e) :=
  hfm.comp (measurable_compRegM sel hε j₀ e)

/-- On the label event, the class (a) compressed observable is a Hermitian contraction. -/
theorem largeObsA_spec (sel : CEH.EigenpairSelection (2 * p.W))
    {B₀ : SplitState p i → PairMatrix p i} (hB₀ : ∀ om, (B₀ om).IsHermitian ∧ ‖B₀ om‖ ≤ 1)
    {ε : ℝ} {j₀ : ExteriorSite p i} {e : ℝ} {om : SplitState p i}
    (hl : om ∈ poleLabelSet ε j₀ e) :
    (largeObsA sel B₀ j₀ e om).IsHermitian ∧ ‖largeObsA sel B₀ j₀ e om‖ ≤ 1 := by
  obtain ⟨hH, hs, -⟩ := hl
  exact compress_hermitian_contraction (poleIsometry_spec sel hH hs).1 (hB₀ om).1 (hB₀ om).2

/-- The class (b) compressed observable is a Hermitian contraction (`|f| ≤ 1`). -/
theorem largeObsB_spec (sel : CEH.EigenpairSelection (2 * p.W)) (ε : ℝ) {f : ℝ → ℝ}
    (hf : ∀ x, |f x| ≤ 1) (j₀ : ExteriorSite p i) (e : ℝ) (om : SplitState p i) :
    (largeObsB sel ε f j₀ e om).IsHermitian ∧ ‖largeObsB sel ε f j₀ e om‖ ≤ 1 :=
  ⟨isHermitian_spectralFn f _, opNorm_spectralFn_le hf _⟩

/-- **The class (b) grid observable is close to the compressed exact observable**:
at a simple label `j₀` separated at `ε > 0` from the exact
energy `E` (not a pole) and from the grid energy `e` (`H_R, V` Hermitian), for a spectral test
`f` (`k ≥ 1`), `‖F_reg(E) - E‖ ≤ K'` (`K' > 0`) and `6K' ≤ |ρ(E)|`:
`‖f(compRegM e) - U* f(K₀(E)) U‖ ≤ √(2W - 1) K₀ (‖C‖²/ε² + 1)|E - e| +
√(2W)(3K₀K'² + 4K')/|ρ(E)|`. -/
theorem largeObsB_close (sel : CEH.EigenpairSelection (2 * p.W)) {ε : ℝ} (hε : 0 < ε)
    {om : SplitState p i} (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian)
    {j₀ : ExteriorSite p i} (hs : PoleSimple hH j₀) {E e : ℝ} (hsepE : PoleSeparated ε hH j₀ E)
    (hsepe : PoleSeparated ε hH j₀ e) (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0) {k : ℕ} {K₀ : ℝ}
    {f : ℝ → ℝ} (hf : BlockBand.LocalWindow.IsSpectralTest k K₀ f) (hk : 1 ≤ k) {K' : ℝ}
    (hK' : 0 < K') (hM' : ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖ ≤ K')
    (hρ' : 6 * K' ≤ |poleRho hH j₀ om.2.1 E|) :
    ‖largeObsB sel ε f j₀ e om - (poleIsometry sel j₀ om)ᴴ *
        BlockBand.LocalWindow.spectralFn f (schurK0 p i om E) * poleIsometry sel j₀ om‖ ≤
      Real.sqrt ((2 * p.W - 1 : ℕ) : ℝ) * K₀ * ((‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) +
        Real.sqrt (2 * (p.W : ℝ)) * ((3 * K₀ * K' ^ 2 + 4 * K') / |poleRho hH j₀ om.2.1 E|) := by
  set U := poleIsometry sel j₀ om with hUdef
  obtain ⟨hUU, hUw, hcompl⟩ := poleIsometry_spec sel hH hs
  have hw := sqNorm_poleDir hH j₀ om.2.1
  have hMEh := isHermitian_regK om hH hV j₀ E
  have hMeh := isHermitian_regK om hH hV j₀ e
  have hK0 : 0 ≤ K₀ := nonneg_of_isSpectralTest hf hk
  -- grid to exact on the compressed block
  have h1 : ‖largeObsB sel ε f j₀ e om - BlockBand.LocalWindow.spectralFn f
      (Uᴴ * (regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1) * U)‖ ≤
      Real.sqrt ((2 * p.W - 1 : ℕ) : ℝ) * K₀ * ((‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) := by
    unfold largeObsB
    rw [compRegM_eq sel ε hH hV hs hsepe]
    have h := opNorm_spectralFn_sub_le (isHermitian_compress hMeh U) (isHermitian_compress hMEh U)
      hK0 (lipschitz_of_isSpectralTest hf hk)
    rw [Fintype.card_fin] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, abs_sub_comm]
    exact (opNorm_compress_le hUU _).trans (opNorm_regK_sub_le hε om hH j₀ hsepe hsepE)
  -- the limiting compression at `E`
  have h2 := opNorm_compress_spectralTest_largeRho_le hf hk hMEh hK' hM' hUU hUw hcompl hw hρ'
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * (p.W : ℝ) := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
  rw [hcard, ← schurK0_pole_decomp om hH j₀ hdet] at h2
  have t := norm_sub_le_norm_sub_add_norm_sub (largeObsB sel ε f j₀ e om)
    (BlockBand.LocalWindow.spectralFn f (Uᴴ * (regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1) * U))
    (Uᴴ * BlockBand.LocalWindow.spectralFn f (schurK0 p i om E) * U)
  rw [norm_sub_rev (BlockBand.LocalWindow.spectralFn f _)] at t
  linarith

end BlockBand.LocalWindow.ProofPartTwo
