module

public import BlockBand.Endpoints.Clock.OpenClockLaw

/-!
# The deterministic-clock lemma uniformly in a small Hermitian initial matrix `X₀ = D`

We consider the one-ended chain started at a deterministic Hermitian `X₀ = D` with `Y₀ = 0`, as in
the perturbation clause of the open-inputs lemma.
* `openClockLaplaceWD`, `detClockRemainderD`: `openClockLaplaceW` and `detClockRemainder` with
  `X₀ = D` in place of `X₀ = 0`; at `D = 0` they are the same terms (`openClockLaplaceWD_zero`,
  `detClockRemainderD_zero`).
* `DetClockEvolutionD`: the deterministic-clock lemma uniformly in `‖D‖ ≤ ε` (operator norm):
  fixed `0 < b < 1/2`, `-2 < E < 2`, `T`, admissible `q`; there is `ε > 0` such that for every
  `K ≥ 1` there are `δ_{W,j}` with `|r_{W,j}^D(a)| ≤ δ_{W,j}` for all Hermitian `‖D‖ ≤ ε`,
  `j₀ ≤ j ≤ TW`, `a ∈ [K⁻¹, K]`, and `Σ_{j=j₀}^{⌊TW⌋} δ_{W,j} → 0`. The constants (`ε`, `δ`) do
  not depend on `D`. This is the form used for the Robin entrance lemma (closed far port,
  `X₀ = B₀*λ_θ⁻¹B₀`).
* `detClockEvolution_of_D : DetClockEvolutionD → DetClockEvolution`: the statement with `D = 0`
  is a special case.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal Matrix Matrix.Norms.L2Operator

/-- `f^D_{W,j}(a) = E F_a(Q_j^q)` for the one-ended chain started at `X₀ = D`, `Y₀ = 0`. -/
def openClockLaplaceWD (W : ℕ) (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (a : ℝ) : ℝ :=
  ∫ ω, detLaplace (oneEndedQ b E q D j ω) a ∂oneEndedLaw W b j

/-- The remainder `r^D_{W,j}(a)` of the deterministic clock step for the chain
started at `X₀ = D`. -/
def detClockRemainderD (W : ℕ) (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (a : ℝ) : ℝ :=
  openClockLaplaceWD W b E q D (j + 1) a - openClockLaplaceWD W b E q D j a -
    (W : ℝ)⁻¹ * (transportD0 b E / 2 * a ^ 2 * deriv (deriv (openClockLaplaceWD W b E q D j)) a -
      dStar b * q (((j + 1 : ℕ) : ℝ) / W) * a * openClockLaplaceWD W b E q D j a)

theorem openClockLaplaceWD_zero (W : ℕ) (b E : ℝ) (q : ℝ → ℝ) (j : ℕ) :
    openClockLaplaceWD W b E q (0 : Matrix (Fin W) (Fin W) ℂ) j = openClockLaplaceW W b E q j :=
  rfl

theorem detClockRemainderD_zero (W : ℕ) (b E : ℝ) (q : ℝ → ℝ) (j : ℕ) (a : ℝ) :
    detClockRemainderD W b E q (0 : Matrix (Fin W) (Fin W) ℂ) j a =
      detClockRemainder W b E q j a :=
  rfl

/-- **The deterministic-clock lemma, uniformly in a small Hermitian initial matrix.** See the
module docstring. It is derived from its hypotheses in `detClockEvolutionD_of`. -/
def DetClockEvolutionD : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (q : ℝ → ℝ),
    IsClockWeight q → ∃ ε : ℝ, 0 < ε ∧ ∀ K : ℝ, 1 ≤ K → ∃ δ : ℕ → ℕ → ℝ,
      (∀ W j (D : Matrix (Fin W) (Fin W) ℂ), D.IsHermitian → ‖D‖ ≤ ε →
        openEntranceTime W ≤ j → (j : ℝ) ≤ T * W → ∀ a ∈ Icc K⁻¹ K,
          |detClockRemainderD W b E q D j a| ≤ δ W j) ∧
      Tendsto (fun W => ∑ j ∈ Finset.Icc (openEntranceTime W) ⌊T * W⌋₊, δ W j) atTop (𝓝 0)

/-- The statement `DetClockEvolution` (`X₀ = 0`) is the case `D = 0` of
`DetClockEvolutionD`. -/
theorem detClockEvolution_of_D (h : DetClockEvolutionD) : DetClockEvolution := by
  intro b hb0 hb1 E hE0 hE1 T q hq K hK
  obtain ⟨ε, hε, hK'⟩ := h b hb0 hb1 E hE0 hE1 T q hq
  obtain ⟨δ, hδ, hsum⟩ := hK' K hK
  refine ⟨δ, fun W j hj hjT a ha => ?_, hsum⟩
  have h0 := hδ W j (0 : Matrix (Fin W) (Fin W) ℂ) Matrix.isHermitian_zero
    (by rw [norm_zero]; exact hε.le) hj hjT a ha
  rwa [detClockRemainderD_zero] at h0

end BlockBand.Endpoints.Clock
