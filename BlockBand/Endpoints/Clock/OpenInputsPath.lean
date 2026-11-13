module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The one-ended path and the input moments of the open-inputs lemma

This file defines the one-ended path and states `OpenInputsMoments`, the input moments of the
open-inputs lemma.

## The one-ended path versus the near-end-grown path

`TransmissionPath.pathNearSchur` / `TransmissionStatements.pathX` is not the one-ended path. That path
has two absorbing ports with parameter `z` (near and far); its `X_r` is
`nearSchur z (C*(H_path - E)⁻¹C)`, the far port being eliminated through
`X₁₁ + X₁₂(z - X₂₂)⁻¹X₂₁`. Read as a cavity chain this is
`X_{r+1} = B_{r+1}*(A_r - E - X_r)⁻¹B_{r+1}` started from the random, non-Hermitian far-port
self-energy `B_0 z⁻¹ B_0*` (so `Y = -Im X ⪰ 0` is nonzero and `T = 4ηR*YR ≠ 0`). The one-ended
chain starts from the free end `X_0 = 0` (more generally a deterministic Hermitian `D`): every
`X_j` is then Hermitian (almost surely), the passive transmission vanishes, and `Q_j^q` below is
the injected clock, not the passive `Q = R*YR`. We define the one-ended chain here and reuse the
one-layer vocabulary: `freshLaw`, `freshLayer` (`𝒢`), `freshL` (`L = (z-X)𝒢₁₂`), `freshSchur`
(`X₊ = B*(A-E-X)⁻¹B`), `passiveF` (`f`), `freshTransportedF` (`Lf₊L*`), `hsSandwich`,
`jetDistance0/1`, `IsStationaryJet`.

## Objects

* `z = boundaryZ b E = a⁻¹ + ba`, `a = matchedA E`.
* Probability space at step `j`: the first `j` fresh layers,
  `oneEndedLaw W b j = Measure.pi (fun _ : Fin j => freshLaw W b)` (independent
  `A ~ GUE_W(c/W)`, `c = 1-2b`, `B ~ Gin(b/W)`). The quantities at step `j` depend only on these
  layers, so their laws (hence all `L^p` norms) are those of the infinite i.i.d. sequence.
* `oneEndedX E D j`: `X_0 = D`, `X_{j+1} = B_{j+1}*(A_{j+1} - E - X_j)⁻¹B_{j+1}`
  (`freshSchur`); the path of the paper is `D = 0`.
* `freshG12`: `(𝒢_j)₁₂` (physical row, port column); `freshC = (𝒢₁₂)*(𝒢₁₂)`;
  `L_j = freshL b E X_{j-1}` (`= (z - X_{j-1})(𝒢_j)₁₂`).
* `oneEndedY`: `Y_0 = 0`, `Y_j = q(j/W)C_j + L_j*Y_{j-1}L_j`; `oneEndedQ = W⁻²Y`,
  `oneEndedGamma = Re Tr Q` (`Q ⪰ 0`, so the trace is real).
* `f(X) = (z - X)⁻¹ - (z - z̄)⁻¹I` is `passiveF b E X` (`c₀ = (2iη)⁻¹ = (z - z̄)⁻¹`).
* `openEntranceTime W = j₀ = ⌈(log W)²⌉`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexConjugate Matrix Matrix.Norms.L2Operator

/-- One fresh one-port layer sample `(A, B)` of the one-ended path. -/
abbrev OneEndedLayer (W : ℕ) := LayerSample W .oneBlockOnePort

/-- Law of the first `j` fresh layers of the one-ended path (`A_j` GUE of
entry variance `(1-2b)/W`, `B_j` circular of variance `b/W`, all layers independent). -/
def oneEndedLaw (W : ℕ) (b : ℝ) (j : ℕ) : Measure (Fin j → OneEndedLayer W) :=
  Measure.pi fun _ : Fin j => freshLaw W b

/-- `(𝒢)₁₂`: physical-row, port-column block of the fresh layer resolvent
`𝒢 = [[A - E - X, B],[B*, zI]]⁻¹`. -/
def freshG12 {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => freshLayer b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))

/-- The injection `C = (𝒢)₁₂*(𝒢)₁₂`. -/
def freshC {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    Matrix (Fin W) (Fin W) ℂ :=
  (freshG12 b E X ω)ᴴ * freshG12 b E X ω

/-- The one-ended cavity chain `X_0 = D`, `X_{j+1} = B*(A - E - X_j)⁻¹B` with the
`(j+1)`-st fresh layer (a general deterministic Hermitian `D`, as in the
open-inputs lemma). -/
def oneEndedX (E : ℝ) {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ) :
    (j : ℕ) → (Fin j → OneEndedLayer W) → Matrix (Fin W) (Fin W) ℂ
  | 0, _ => D
  | j + 1, ω => freshSchur E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))

/-- The clock `Y_0 = 0`, `Y_{j+1} = q((j+1)/W) C_{j+1} + L_{j+1}* Y_j L_{j+1}`,
`L_{j+1} = (z - X_j)(𝒢_{j+1})₁₂`. -/
def oneEndedY (b E : ℝ) (q : ℝ → ℝ) {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ) :
    (j : ℕ) → (Fin j → OneEndedLayer W) → Matrix (Fin W) (Fin W) ℂ
  | 0, _ => 0
  | j + 1, ω =>
      ((q (((j + 1 : ℕ) : ℝ) / W) : ℝ) : ℂ) •
          freshC b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) +
        (freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)))ᴴ *
          oneEndedY b E q D j (Fin.init ω) *
          freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))

/-- `Q_j^q = W⁻² Y_j^q`. -/
def oneEndedQ (b E : ℝ) (q : ℝ → ℝ) {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (ω : Fin j → OneEndedLayer W) : Matrix (Fin W) (Fin W) ℂ :=
  (((W : ℝ) ^ 2)⁻¹ : ℂ) • oneEndedY b E q D j ω

/-- `γ_j^q = Tr Q_j^q` (real since `Q ⪰ 0`, we take the real part). -/
def oneEndedGamma (b E : ℝ) (q : ℝ → ℝ) {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (ω : Fin j → OneEndedLayer W) : ℝ :=
  (oneEndedQ b E q D j ω).trace.re

/-- `j₀ = ⌈(log W)²⌉`. -/
def openEntranceTime (W : ℕ) : ℕ := ⌈Real.log W ^ 2⌉₊

/-- Admissible clock weights: `q` continuous, nonnegative and bounded (only the values `q(j/W)`, `j ≤ TW`, enter). -/
def IsClockWeight (q : ℝ → ℝ) : Prop :=
  Continuous q ∧ (∀ x, 0 ≤ q x) ∧ ∃ K : ℝ, ∀ x, q x ≤ K

/-- **Input moments of the open-inputs lemma.** Fixed `0 < b < 1/2`, bulk `-2 < E < 2`, horizon `T`, admissible clock weight `q`,
and moment order `p ≥ 1` first; then a small `ε > 0`, a constant `C` and `W₀`; for every
`W ≥ W₀` and every deterministic Hermitian initial `X_0 = D` with `‖D‖ ≤ ε` (operator norm),
with `Y_0 = 0`:
* for every solution `s` of the stationary-jet equation (`k₋s² + (1+ca²)s + a² = 0`,
  `|s| ≤ (1-b)⁻¹`; unique by the lemma) and every
  `j₀ ≤ j ≤ TW`: `‖δ_{0,j}‖_p + ‖δ_{1,j}‖_p ≤ C/W`, where
  `δ_{0,j} = |h_j(z) - a|`, `δ_{1,j} = |h_j'(z) - s|`, `h_j(ζ) = W⁻¹Tr(ζ - X_j)⁻¹`
  (`jetDistance0/1` of `X_j`);
* for every `0 ≤ j ≤ TW`: `‖γ_j^q‖_p ≤ C(j+1)/W` (unstopped).

Here all of `ε, C, W₀` may depend on `(b, E, T, q, p)`; this is implied by the version with
`C_p` for the jet clause, `C_{p,T,q}` for the clock clause and `ε` depending on a finite moment
family (a finite moment family is dominated by its largest order on a probability space), and it
is all that the clock-mixing lemma uses. The further clauses of the lemma (the `C√p/W` range
`2 ≤ p ≤ a_*W`, the exit probability `e^{-c_*W log W}`, the existence of `s_*`) are not stated. -/
def OpenInputsMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (q : ℝ → ℝ),
    IsClockWeight q → ∀ p : ℝ, 1 ≤ p →
      ∃ (ε C : ℝ) (W₀ : ℕ), 0 < ε ∧ ∀ W : ℕ, W₀ ≤ W →
        ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
          (∀ s : ℂ, IsStationaryJet b E s → ∀ j : ℕ, openEntranceTime W ≤ j →
              (j : ℝ) ≤ T * W →
              eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal p)
                  (oneEndedLaw W b j) +
                eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal p)
                  (oneEndedLaw W b j) ≤ ENNReal.ofReal (C / W)) ∧
          ∀ j : ℕ, (j : ℝ) ≤ T * W →
            eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) ≤
              ENNReal.ofReal (C * ((j : ℝ) + 1) / W)

end BlockBand.Endpoints.Clock
