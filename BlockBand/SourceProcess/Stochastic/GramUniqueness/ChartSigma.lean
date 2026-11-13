module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartBracket
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartEk
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The chart factor and the chart diffusion

One global chart per spectral gap `δ > 0`; no principal-minor case split. In the ambient space
`ℂ^c ⊕ ℂ^c` with near projection `P0 = diag(1, 0)`:
* `chartFrame δ G = [h(B); h(M - B)]` with `h = cutSqrt δ` applied by `fcM` (Hermitian part,
  spectral calculus). It is defined and Lipschitz for every `G` (`ChartLip`).
* `ChartGood D δ G`: `G` is feasible and the eigenvalues of `B` and `M - B` lie in
  `{0} ∪ [δ, ∞)`. **`gramPair_chartFrame`**: then `chartFrame δ G` realizes `G`.
* `chartSigma D0 D δ y` (real coordinates, noise index `SourceNoise (c ⊕ c)` enumerated): the
  real coordinates of the Gram noise `gramNoise D0 P0 D a (chartFrame δ (fromGramReal y))`.
* **`chartSigma_cov`**: on `ChartGood` states, `σσᵀ = gramRealCov` (`bracket_transfer` to a
  constrained realization, then `gramNoise_cov_entry`). The chart frame itself need not satisfy
  the two-projection constraint.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra
open BlockBand.SourceProcess.Stochastic.GramUniqueness

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- The near projection `diag(1, 0)` of the chart ambient space `ℂ^c ⊕ ℂ^c`. -/
def P0 : Matrix (c ⊕ c) (c ⊕ c) ℂ := fromBlocks 1 0 0 0

omit [Fintype c] in
theorem P0_herm : (P0 (c := c))ᴴ = P0 := by simp [P0, fromBlocks_conjTranspose]

theorem P0_idem : P0 (c := c) * P0 = P0 := by simp [P0, fromBlocks_multiply]

/-- The chart frame `[h(B); h(M - B)]`. -/
def chartFrame (δ : ℝ) (G : Matrix c c ℂ × Matrix c c ℂ) : Matrix (c ⊕ c) c ℂ :=
  fromRows (fcM (cutSqrt δ) G.2) (fcM (cutSqrt δ) (G.1 - G.2))

omit [DecidableEq c] in
theorem sourceGram_fromRows (X Y : Matrix c c ℂ) :
    sourceGram (fromRows X Y) = Xᴴ * X + Yᴴ * Y := by
  ext i j
  simp [sourceGram, mul_apply, Fintype.sum_sum_type]

theorem nearGram_fromRows (X Y : Matrix c c ℂ) : nearGram P0 (fromRows X Y) = Xᴴ * X := by
  ext i j
  simp [nearGram, P0, mul_apply, Fintype.sum_sum_type, fromBlocks, one_apply]

/-- The states where the chart frame realizes the Gram pair. -/
def ChartGood (D : Matrix c c ℂ) (δ : ℝ) (G : Matrix c c ℂ × Matrix c c ℂ) : Prop :=
  GramFeasible D G ∧ (∀ i, eL G.2 i = 0 ∨ δ ≤ eL G.2 i) ∧
    ∀ i, eL (G.1 - G.2) i = 0 ∨ δ ≤ eL (G.1 - G.2) i

theorem fcM_sq_of_gap {δ : ℝ} (hδ : 0 < δ) {A : Matrix c c ℂ} (hA : Aᴴ = A)
    (h : ∀ i, eL A i = 0 ∨ δ ≤ eL A i) : (fcM (cutSqrt δ) A)ᴴ * fcM (cutSqrt δ) A = A := by
  rw [fcM_conjTranspose, fcM_mul_self fun i => cutSqrt_mul_self hδ (h i), hermPart_of_herm hA]

/-- **The chart frame realizes every good state.** -/
theorem gramPair_chartFrame {D : Matrix c c ℂ} {δ : ℝ} (hδ : 0 < δ)
    {G : Matrix c c ℂ × Matrix c c ℂ} (hG : ChartGood D δ G) :
    gramPair P0 (chartFrame δ G) = G := by
  obtain ⟨h1, h2⟩ := herm_of_feasible hG.1
  have hC : (G.1 - G.2)ᴴ = G.1 - G.2 := by rw [conjTranspose_sub, h1, h2]
  simp only [gramPair, chartFrame, sourceGram_fromRows, nearGram_fromRows,
    fcM_sq_of_gap hδ h2 hG.2.1, fcM_sq_of_gap hδ hC hG.2.2, add_sub_cancel]

/-- The number of real noise coordinates of the chart. -/
abbrev chartNoiseDim (c : Type*) [Fintype c] : ℕ := Fintype.card (SourceNoise (c ⊕ c))

/-- Enumeration of the chart noise coordinates. -/
def chartNoiseEquiv (c : Type*) [Fintype c] : SourceNoise (c ⊕ c) ≃ Fin (chartNoiseDim c) :=
  Fintype.equivFin _

/-- **The chart diffusion matrix** in real Gram coordinates. -/
def chartSigma (D0 : ℝ) (D : Matrix c c ℂ) (δ : ℝ) (y : Fin (gramDim c) → ℝ) :
    Matrix (Fin (gramDim c)) (Fin (chartNoiseDim c)) ℝ := fun i k =>
  reIm ((gramRealEquiv c).symm i).2 (gramEntry ((gramRealEquiv c).symm i).1
    (gramNoise D0 P0 D ((chartNoiseEquiv c).symm k) (chartFrame δ (fromGramReal y))))

/-- **`σσᵀ` is the Gram covariance at good states.** -/
theorem chartSigma_cov {D0 : ℝ} (hD0 : 0 ≤ D0) {D : Matrix c c ℂ} (hD : IsSignature D) {δ : ℝ}
    (hδ : 0 < δ) {y : Fin (gramDim c) → ℝ} (hy : ChartGood D δ (fromGramReal y)) :
    chartSigma D0 D δ y * (chartSigma D0 D δ y).transpose = gramRealCov D0 D y := by
  ext i j
  rw [mul_apply]
  simp only [transpose_apply, chartSigma]
  rw [Equiv.sum_comp (chartNoiseEquiv c).symm (fun a =>
      reIm ((gramRealEquiv c).symm i).2 (gramEntry ((gramRealEquiv c).symm i).1
        (gramNoise D0 P0 D a (chartFrame δ (fromGramReal y)))) *
      reIm ((gramRealEquiv c).symm j).2 (gramEntry ((gramRealEquiv c).symm j).1
        (gramNoise D0 P0 D a (chartFrame δ (fromGramReal y))))),
    sum_reIm_mul _ (fun a => gramNoise_herm D0 P0_herm D a _)]
  obtain ⟨n, N, P, V, hP, hV, hGe⟩ := exists_realization_of_feasible hy.1
  have hT := bracket_transfer hD0 hD.1 P0_herm P0_idem hP.1 hP.2.1
    ((gramPair_chartFrame hδ hy).trans hGe.symm)
  rw [hT, hT, gramNoise_cov_entry hD0 hP hD hV, gramNoise_cov_entry hD0 hP hD hV, hGe]
  rfl

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
