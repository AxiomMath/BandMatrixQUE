module

public import BlockBand.Layers.TaggedTraceEnergy

/-!
# The full-energy trace bound: derivative objects, layer inputs and the path recursion

The objects and the named one-layer statements of the energy paragraph in the proof of the
tagged-trace lemma, which lead to the full-energy trace bound.

## Objects

For a Hermitian two-port matrix `X` (the old Schur input) with source `S = X'(E) ⪰ 0` at
`z = z_∂(E)`: `R = (z - X)⁻¹` (`fetR`), the derivative of the old trace
`f'_i = W⁻¹ Tr[R(S - z_∂')R]_{ii}` (`fetFd`), its distance `max_i |f'_i - a'|` (`fetDist`) and the
clock `u = W⁻¹ Re Tr R* S R` (`fetClock`). Along a path, `X_r = pathSchur E ω`,
`X_r' = B_p*(H - E)⁻²B_p` (`fetXd`) and `fetPathDist = fetDist (X_r, X_r')`; `fetFd` is the exact
energy derivative of `E ↦ W⁻¹ Tr(R_r)_{ii}` (`fetC_hasDerivAt_pathTrace`). At one separate-port
layer the outgoing derivative is `ġ_j = -W⁻¹ Tr Q_j 𝒢 P 𝒢`, `P = ∂_E 𝒢⁻¹ = -Ŝ + D₀`
(`fetGd`). In the residual pair layer the derivative of `W⁻¹ Tr P_k(V - E - X - sa)⁻¹ - a` is
`ρ'_k = W⁻¹ Tr P_k R(1 + S + s a')R - a'` (`fetRho`).

## Named layer inputs (each a statement about one layer law with deterministic inputs)

* `FetStepMean` — one separate-port step, conditional mean (in the paper: "the same
  contraction gives outgoing error `q_*|f' - a'| + Cδ(1+s_r) + C(1+s_r)/W`").
* `FetCoreBound` — the cores `r ∈ {1, 2}` (in the paper: "the finite-core derivatives follow by
  differentiating their stable finite mean equations").
* `FetResidualBound` — the final residual pair layer (in the paper: "the final residual
  pair has a fixed stability gap ... The final energy derivative gives the full-energy trace bound").

## Where the named statements are proved

These results are proved in other modules, named in parentheses:

* `fetStepMean_holds` (`FullEnergyStep`), `fetCoreBound_holds` (`FullEnergyCore`),
  `fetResidualBound_holds` (`FullEnergyTrace`), `fetPathBound_holds` (`FullEnergyRecursion`:
  the path clause `‖f'_r - a'‖_{L^p(pathLaw W r b)} ≤ C(r+1)/√W`);
* the final `fullEnergyTraceBound_holds` (`FullEnergyTransfer`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. The derivative objects
-/

section Objects

variable {W : ℕ}

/-- `R = (z_∂ - X)⁻¹`, the old two-port resolvent. -/
def fetR (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹

/-- `f'_i = W⁻¹ Tr[R (S - z_∂') R]_{ii}`: the energy derivative of `W⁻¹ Tr(z_∂(E) - X(E))⁻¹_{ii}`
when `X'(E) = S`. -/
def fetFd (b E : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) : ℂ :=
  blockTrace (fetR b E X * (S - tgtZd b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) *
    fetR b E X) i

/-- The derivative distance `max_i |f'_i - a'|`. -/
def fetDist (b E : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  max ‖fetFd b E X S 0 - tgtAd E‖ ‖fetFd b E X S 1 - tgtAd E‖

/-- The clock `u = W⁻¹ Re Tr R* S R` (`= W⁻¹ Re Tr K⁻* S K⁻¹`, `K = z_∂ - X`). -/
def fetClock (b E : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  clkTrace ((fetR b E X)ᴴ * S * fetR b E X)

/-- `X_r' = B_p* (H - E)⁻² B_p`, the energy derivative of `X_r = pathSchur E ω`. -/
def fetXd {r : ℕ} (E : ℝ) (ω : PathSample W r) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (pathPortCoupling ω)ᴴ * (pathMatrix ω - (E : ℂ) • 1)⁻¹ * (pathMatrix ω - (E : ℂ) • 1)⁻¹ *
    pathPortCoupling ω

/-- The path derivative distance `max_i |f'_{r,i} - a'|`. -/
def fetPathDist {r : ℕ} (b E : ℝ) (ω : PathSample W r) : ℝ :=
  fetDist b E (pathSchur E ω) (fetXd E ω)

/-- The energy insertion `P = ∂_E 𝒢⁻¹ = -Ŝ + D₀ = diag(-(I + S), z_∂' I)` of a separate-port
layer. -/
def fetP (b E : ℝ) (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  -dcvHat S + tgtD0 (tgtZd b E)

/-- The outgoing port derivative `ġ_j = -W⁻¹ Tr Q_j 𝒢 P 𝒢` of a separate-port layer at
`z = z_∂(E)` with old input `X` and source `S` (`tgtEnergyClause`, `D = Q_j`). -/
def fetGd (b E : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .separate) (j : Fin 2) : ℂ :=
  -((W : ℂ)⁻¹ * (meqPortProj (W := W) (σ := .separate) j *
    (layerResolvent .separate E (boundaryZ b E) X ℓ * fetP b E S *
      layerResolvent .separate E (boundaryZ b E) X ℓ)).trace)

/-- `ρ'_k = W⁻¹ Tr P_k R (1 + S + s a') R - a'`, `R = (V - E - X - sa)⁻¹`: the energy derivative
of the residual-pair trace `W⁻¹ Tr P_k (V - E - X(E) - s a(E))⁻¹ - a(E)` when `X'(E) = S`. -/
def fetRho (E s : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : RpSample W)
    (k : Fin 2) : ℂ :=
  blockTrace (rpResolvent E s X ω * (1 + S + ((s : ℂ) * tgtAd E) • 1) * rpResolvent E s X ω) k -
    tgtAd E

/-- `max_k |ρ'_k|`. -/
def fetRhoMax (E s : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : RpSample W) : ℝ :=
  max ‖fetRho E s X S ω 0‖ ‖fetRho E s X S ω 1‖

end Objects

/-!
## 2. The named inputs and the path statement
-/

/-- **One separate-port step, conditional mean** (the energy analogue of
`v = d + (c + b²a²)Qv`, `w = ba²v`, with the cancellation `1 + (1-b)a' + z_∂' = 0`).

*Law.* The fresh layer `layerLaw W b .separate`, conditional on the old input: `X` Hermitian and
`S ⪰ 0` deterministic (the old Schur matrix and its energy derivative), `E ∈ bulkInterval κ`,
`z = z_∂(E)`. *Objects.* `ġ_j = fetGd` (the a.s. energy derivative of the outgoing port trace
`W⁻¹ Tr(𝒢_ports)_{jj}` along any Hermitian family with `X'(E) = S`, `tgtEnergyClause`),
`d = fetDist` (old derivative distance), `u = fetClock`, `δ = d(X) = matchedDistance`.
*Quantifiers.* `b ∈ (0,1/2)`, `κ > 0` first; then `d_* > 0`, `q ∈ [0,1)`, `C ≥ 0`, `W₀`; then
uniformly in `W ≥ W₀`, `X`, `S`, `E`, `j`, on `δ ≤ d_*`:
`|E ġ_j - a'| ≤ q d + C(1 + u)(δ + 1/W)`. -/
def FetStepMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar q C : ℝ) (W₀ : ℕ), 0 < dstar ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar → ∀ j : Fin 2,
        ‖(∫ ℓ, fetGd b E X S ℓ j ∂layerLaw W b .separate) - tgtAd E‖ ≤
          q * fetDist b E X S + C * (1 + fetClock b E X S) * (matchedDistance b E X + 1 / W)

/-- **The cores** `r ∈ {1, 2}`. *Law:* `pathLaw W r b`. *Quantifiers:* `b ∈ (0,1/2)`,
`κ > 0`, the moment order `p ≥ 1` first; then `C ≥ 0`, `W₀`; uniformly in `W ≥ W₀`, both cores and
`E ∈ bulkInterval κ`: `‖max_i |f'_{r,i} - a'|‖_{L^p} ≤ C/√W`. -/
def FetCoreBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ r : ℕ, (r = 1 ∨ r = 2) →
      ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => fetPathDist b E ω) (ENNReal.ofReal p) (pathLaw W r b) ≤
          ENNReal.ofReal (C / Real.sqrt W)

/-- **The final residual pair layer**. *Law:* `rpLaw W b s` (residual
pair blocks `GUE_W((c - s/2)/W)`, internal bond `Gin((b - s/2)/W)`), conditional on the exterior
path: `X` Hermitian, `S ⪰ 0` deterministic, `E ∈ bulkInterval κ`, fixed admissible
`0 < s < 2 min(c,b)`. *Objects:* `ρ' = fetRho` (`R = (V - E - X - sa)⁻¹`), `d = fetDist`,
`u = fetClock`, `δ = matchedDistance b E X`. *Quantifiers:* `b, κ, s` and `p ≥ 1` first; then
`d_* > 0`, `C ≥ 0`, `W₀`; uniformly in `W ≥ W₀`, `X`, `S`, `E`:
* crude (every `X`): `‖max_k |ρ'_k|‖_{L^p} ≤ C(1 + u)`;
* on `δ ≤ d_*`: `‖max_k |ρ'_k|‖_{L^p} ≤ C(d + (1 + u)(δ + 1/√W))` (mean by the stability gap
  `s/(1-b)`, noise `C_p(1+u)/√W`). -/
def FetResidualBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ s : ℝ, 0 < κ → 0 < s → s < 2 * min (1 - 2 * b) b →
    ∀ p : ℝ, 1 ≤ p → ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ 0 ≤ C ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      ∀ E ∈ bulkInterval κ,
        eLpNorm (fetRhoMax E s X S) (ENNReal.ofReal p) (rpLaw W b s) ≤
            ENNReal.ofReal (C * (1 + fetClock b E X S)) ∧
          (matchedDistance b E X ≤ dstar →
            eLpNorm (fetRhoMax E s X S) (ENNReal.ofReal p) (rpLaw W b s) ≤
              ENNReal.ofReal (C * (fetDist b E X S + (1 + fetClock b E X S) *
                (matchedDistance b E X + 1 / Real.sqrt W))))

/-- **The path clause of the energy paragraph** (in the paper: "the full clock bound proves
`‖f'_r - a'‖_{L^p} ≤ C_p(r+1)/√W`"). *Law:* `pathLaw W r b`. *Quantifiers:* `b ∈ (0,1/2)`, `κ > 0`,
`T` and `p ≥ 1` first; then `C ≥ 0`, `W₀`; uniformly in `W ≥ W₀`, `1 ≤ r ≤ TW` (both parities) and
`E ∈ bulkInterval κ`. -/
def FetPathBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => fetPathDist b E ω) (ENNReal.ofReal p) (pathLaw W r b) ≤
          ENNReal.ofReal (C * ((r : ℝ) + 1) / Real.sqrt W)

end BlockBand.Layers
