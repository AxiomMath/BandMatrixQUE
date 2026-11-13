module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Internal.Contracts.QUE

/-!
# Gaussian layers, matched traces, rank location and the physical center

This file states, as propositions, the estimates on one fresh Gaussian layer (absorption,
trace matrix, contraction and comparison), the matched traces on paths and on the ring, the
stopped scalar recursion, the fresh count, the compensated phases, rank location, the weighted
layer, and the regular domain and smoothing of the physical center.

## Conventions

* **Conditioning on the old deformation.** The paper states the layer estimates for a
  Hermitian `X` *independent* of the fresh layer, "uniformly in `X`", with expectations
  "conditional on the independent Hermitian deformation". The statements quantify over every
  *deterministic* Hermitian `X` and integrate against `layerLaw` only. This is exactly the
  conditional statement (Fubini over any independent law of `X`), and it is how it is used.
* **Layer shapes.** `LayerShape` lists the four configurations of the Gaussian absorption
  lemma: two blocks with separate ports (`B = diag(B₁,B₂)`), two blocks
  with a common port (`B = (B₁ᵀ,B₂ᵀ)ᵀ`), one block with one port, one block with two
  independent ports. Bond coordinates of non-incident (block, port) pairs are sampled but
  unused; the law of `𝒢` is unchanged. The two-block core with an internal bond is the
  separate-port shape with the internal bond inside `X`.
* **Inverses.** Lean's `⁻¹` is the totalized inverse (zero on singular matrices). Every
  inverse below is almost surely of an invertible matrix at deterministic energies, and
  `GaussianAbsorptionContract` states that invertibility.
* **Norms.** Matrix norms are the Euclidean operator norm (`Matrix.Norms.L2Operator`), as in
  `Internal.Contracts.Inputs`. Matrix expectations are taken entrywise (`matrixExpect`), so no completeness
  of the operator-normed space is used.
* **Bulk intervals.** "A fixed compact interval `I ⋐ (-2,2)`" is `bulkInterval κ =
  [-2+κ, 2-κ]` for a fixed `κ > 0`; every compact `I ⋐ (-2,2)` lies in one of these, so the
  quantification is equivalent.
* **Ranks.** `α : Fin p.N` is zero-based: the paper's rank `α` is Lean `α.val + 1`, as in
  `IsBulkRank`. `e_α = F_sc⁻¹(α/(nW))` is `classicalLocation`.
* **Phases.** `Θ_z(F) = π⁻¹ Σ_j arg(z - λ_j(F))` with `0 < arg < π` (`phaseCount`). For
  Hermitian `X` and `Im z > 0`, `π⁻¹ Im Tr log(z - X) = Θ_z(X)` with the principal logarithm,
  so `Ψ_r` and `Ξ` need no choice of continuous logarithm at a deterministic energy.
* **The center's interval.** The regular domain of `j_e` uses `I = bulkInterval κ_α`,
  `κ_α = (2 - |e_α|)/2`, a choice depending on the rank (the family cannot depend on `ϑ`); for
  `ϑ`-bulk ranks `κ_α ≥ ϑ/2`, and all constants are uniform over `ϑ`-bulk ranks. The center uses
  the full compressed inverse `ℛ_e(ζ)` of the proof of the smooth-center lemma, which equals
  `(K_e - ζ)⁻¹` off real Schur poles (an event of probability zero at `λ_α`).
* **Every block.** Ring clauses stated "for block zero" are stated for every block `k`; this
  follows from cyclic invariance of the law (the translation clause of stationarity).
* **Fixed moment orders.** "For every fixed `p`" is `∀ p, ∃ C_p`, with `p` chosen after the
  model constants (`b`, interval, `T`) and before `n, W` and all deterministic data.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Coarea BlockBand.Model.Construction BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.QUE
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 0. Scalar vocabulary: the matched parameters
-/

/-- The matched value `a = (-E - i√(4-E²))/2` (`|a| = 1`, `Im a < 0` in the bulk). -/
def matchedA (E : ℝ) : ℂ := ⟨-E / 2, -Real.sqrt (4 - E ^ 2) / 2⟩

/-- The separate-port parameter `z = z_∂ = a⁻¹ + b a` (`= -E - (1-b)a`). -/
def boundaryZ (b E : ℝ) : ℂ := (matchedA E)⁻¹ + (b : ℂ) * matchedA E

/-- The common-port parameter `z₀ = a⁻¹ + 2b a` (`= -E - c a`). -/
def commonZ (b E : ℝ) : ℂ := (matchedA E)⁻¹ + 2 * (b : ℂ) * matchedA E

/-- The fixed bulk interval `[-2+κ, 2-κ]`. -/
def bulkInterval (κ : ℝ) : Set ℝ := Set.Icc (-2 + κ) (2 - κ)

/-- Semicircle distribution function `F_sc(E) = ∫_{-2}^E ρ_sc` (the density vanishes
outside `[-2,2]`, so this is the distribution function for every real `E`). -/
def semicircleCDF (E : ℝ) : ℝ := ∫ x in (-2 : ℝ)..E, Parameters.semicircleDensity x

/-- Classical location `e_α = F_sc⁻¹(α/(nW))` of the zero-based rank `α` (the paper's rank
`α.val + 1`). -/
def classicalLocation (p : Parameters) (α : Fin p.N) : ℝ :=
  sInf {E : ℝ | ((α.val + 1 : ℕ) : ℝ) / p.N ≤ semicircleCDF E}

/-- `ℓ = π⁻¹ Im log a⁻¹` (principal logarithm). -/
def phaseEll (E : ℝ) : ℝ := (Complex.log (matchedA E)⁻¹).im / Real.pi

/-- `h = π⁻¹ Im a²`. -/
def phaseH (E : ℝ) : ℝ := (matchedA E ^ 2).im / Real.pi

/-- `Θ_z(F) = π⁻¹ Σ_j arg(z - λ_j(F))`, eigenvalues with multiplicity
(`Inputs.spectralSum`); for `Im z > 0` every `arg` lies in `(0, π)`. -/
def phaseCount {ι : Type} [Fintype ι] [DecidableEq ι] (z : ℂ) (F : Matrix ι ι ℂ) : ℝ :=
  Inputs.spectralSum F (fun x => Complex.arg (z - x)) / Real.pi

/-- Entrywise expectation of a random matrix. -/
def matrixExpect {Ω ι κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (U : Ω → Matrix ι κ ℂ) :
    Matrix ι κ ℂ :=
  Matrix.of fun x y => ∫ ω, U ω x y ∂μ

/-- Normalized block trace `W⁻¹ Tr M_{jj}` of a matrix on `Fin k × Fin W`. -/
def blockTrace {k W : ℕ} (M : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) (j : Fin k) : ℂ :=
  (W : ℂ)⁻¹ * ∑ a : Fin W, M (j, a) (j, a)

/-!
## 1. Gaussian laws and one Gaussian layer
-/

/-- Circular (Ginibre) Gaussian `ι × κ` matrices with i.i.d. entries, `E|B_ij|² = t`,
real and imaginary parts independent of variance `t/2`. -/
def ginibreMeasure (ι κ : Type*) [Fintype ι] [Fintype κ] (t : ℝ≥0) : Measure (Matrix ι κ ℂ) :=
  (Measure.pi fun _ : ι × κ × Fin 2 => gaussianReal 0 (t / 2)).map
    (fun r => Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I)

/-- The four layer configurations of the Gaussian absorption lemma. -/
inductive LayerShape
  /-- Two physical blocks, separate ports, `B = diag(B₁, B₂)`. -/
  | separate
  /-- Two physical blocks, one common port, `B = (B₁ᵀ, B₂ᵀ)ᵀ`. -/
  | common
  /-- One physical block and one port. -/
  | oneBlockOnePort
  /-- One physical block and two independent ports. -/
  | oneBlockTwoPorts
  deriving DecidableEq

/-- Number of fresh physical blocks. -/
@[reducible] def LayerShape.blocks : LayerShape → ℕ
  | .separate => 2
  | .common => 2
  | .oneBlockOnePort => 1
  | .oneBlockTwoPorts => 1

/-- Number of ports. -/
@[reducible] def LayerShape.ports : LayerShape → ℕ
  | .separate => 2
  | .common => 1
  | .oneBlockOnePort => 1
  | .oneBlockTwoPorts => 2

/-- Bond incidence: block `a` is coupled to port `j`. -/
def LayerShape.incident : (σ : LayerShape) → Fin σ.blocks → Fin σ.ports → Bool
  | .separate, a, j => decide (a.val = j.val)
  | .common, _, _ => true
  | .oneBlockOnePort, _, _ => true
  | .oneBlockTwoPorts, _, _ => true

/-- Physical sites of a layer. -/
abbrev PhysSite (W : ℕ) (σ : LayerShape) := Fin σ.blocks × Fin W

/-- Port sites of a layer. -/
abbrev PortSite (W : ℕ) (σ : LayerShape) := Fin σ.ports × Fin W

/-- All sites of the augmented layer matrix (physical first, then ports). -/
abbrev LayerSite (W : ℕ) (σ : LayerShape) := PhysSite W σ ⊕ PortSite W σ

/-- Fresh Gaussian coordinates of a layer: diagonal blocks and bond blocks. -/
abbrev LayerSample (W : ℕ) (σ : LayerShape) :=
  (Fin σ.blocks → Matrix (Fin W) (Fin W) ℂ) ×
    (Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ)

/-- Law of the fresh layer: independent `A_a ~ GUE_W(c/W)`, `c = 1-2b`, and independent
bonds `Gin(b/W)`. -/
def layerLaw (W : ℕ) (b : ℝ) (σ : LayerShape) : Measure (LayerSample W σ) :=
  (Measure.pi fun _ : Fin σ.blocks => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))).prod
    (Measure.pi fun _ : Fin σ.blocks => Measure.pi fun _ : Fin σ.ports =>
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))

/-- Block-diagonal matrix `diag(A_a)`. -/
def blockDiag {k W : ℕ} (A : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  fun x y => if x.1 = y.1 then A x.1 x.2 y.2 else 0

/-- The bond matrix `B` (physical × ports) of a layer. -/
def bondMatrix {W : ℕ} (σ : LayerShape)
    (B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (PhysSite W σ) (PortSite W σ) ℂ :=
  fun x y => if σ.incident x.1 y.1 then B x.1 y.1 x.2 y.2 else 0

/-- `𝒢⁻¹ = [[A - E - X, B], [B*, z I]]`. -/
def layerMatrix {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  Matrix.fromBlocks (blockDiag ω.1 - (E : ℂ) • 1 - X) (bondMatrix σ ω.2)
    (bondMatrix σ ω.2)ᴴ (z • 1)

/-- The layer resolvent `𝒢`. -/
def layerResolvent {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  (layerMatrix σ E z X ω)⁻¹

/-- The outgoing Schur self-energy `X₊ = B* (A - E - X)⁻¹ B` on the ports (the two-ended
recursion). -/
def layerSchur {W : ℕ} (σ : LayerShape) (E : ℝ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) :
    Matrix (PortSite W σ) (PortSite W σ) ℂ :=
  (bondMatrix σ ω.2)ᴴ * (blockDiag ω.1 - (E : ℂ) • 1 - X)⁻¹ * bondMatrix σ ω.2

/-- `W⁻¹ Tr 𝒢_{jj}` over physical block `j`. -/
def physBlockTrace {W : ℕ} {σ : LayerShape} (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (j : Fin σ.blocks) : ℂ :=
  (W : ℂ)⁻¹ * ∑ a : Fin W, M (Sum.inl (j, a)) (Sum.inl (j, a))

/-- `W⁻¹ Tr (𝒢_ports)_{jj}` over port `j`. -/
def portBlockTrace {W : ℕ} {σ : LayerShape} (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (j : Fin σ.ports) : ℂ :=
  (W : ℂ)⁻¹ * ∑ a : Fin W, M (Sum.inr (j, a)) (Sum.inr (j, a))

/-- The scalar distance `d(X) = max_i |W⁻¹ Tr[(z - X)⁻¹]_{ii} - a|`, `z = z_∂(E)`, of a
two-port Hermitian Schur matrix. -/
def matchedDistance (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  max ‖blockTrace ((boundaryZ b E • 1 - X)⁻¹) 0 - matchedA E‖
    ‖blockTrace ((boundaryZ b E • 1 - X)⁻¹) 1 - matchedA E‖

/-!
## 2. The Gaussian absorption lemma
-/

/-- **Gaussian absorption** (absorber moments). Law: `layerLaw W b σ` (fresh `A_a ~ GUE_W(c/W)`, bonds `Gin(b/W)`),
for each of the four shapes.
Quantifiers:
`b` and `η₀, M` first; then `ε₁, C > 0`
(depending only on `b, η₀, M`); then uniformly in `W ≥ 1`, the shape, every deterministic
Hermitian `X` (equivalently an independent Hermitian `X`, by Fubini), every real `E` and
every `z` with `Im z ≥ η₀`, `|z| ≤ M`: the augmented matrix is almost surely invertible and
`(E‖𝒢‖^p)^{1/p} ≤ C` for `1 ≤ p ≤ ε₁ W` (operator norm).
-/
def GaussianAbsorptionContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ η₀ M : ℝ, 0 < η₀ →
    ∃ ε₁ C : ℝ, 0 < ε₁ ∧ 0 < C ∧
      ∀ (W : ℕ), 0 < W → ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ),
        X.IsHermitian → ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
          (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
          ∀ p : ℝ, 1 ≤ p → p ≤ ε₁ * W →
            eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal p) (layerLaw W b σ) ≤
              ENNReal.ofReal C

/-!
## 3. The trace-matrix lemma
-/

/-- A matrix word `D₀ 𝒢^{ε₀} D₁ ⋯ 𝒢^{ε_{ℓ-1}} D_ℓ`, with `𝒢^{true} = 𝒢*`. Every word in
`𝒢, 𝒢*` and deterministic matrices with `ℓ` resolvent letters has this form. -/
def wordEval {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (ε : Fin ℓ → Bool)
    (D : Fin (ℓ + 1) → Matrix ι ι ℂ) (G : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  D 0 * (List.ofFn fun j : Fin ℓ => (if ε j then Gᴴ else G) * D j.succ).prod

/-- The trace-matrix lemma.
* `covariance`: for each fixed maximal word length `L` and bound `K`
  on the deterministic letters there are `C, W₀`; for `W ≥ W₀`, `f = W⁻¹ Tr w_f(𝒢)` and
  `U = w_U(𝒢)` with words of at most `L` resolvent letters: `f`, `U` and `fU` are
  integrable and `‖E(fU) - (Ef)(EU)‖ ≤ C W⁻²`. (The paper's `W₀(p, ℓ)` names a moment order
  that the displayed bound does not contain; the statement is the bound for every word.)
* `fluctuation`: there are `ε₃, C`; for every `W ≥ 1`,
  `f = W⁻¹ Tr(D 𝒢)` with deterministic `‖D‖ ≤ K` (every normalized block trace is the case
  `D = P_j`) and `2 ≤ p ≤ ε₃ W`: `‖f - Ef‖_p ≤ C √p / W`. Bounded insertions are a mild
  strengthening of "a single resolvent trace", proved by the same gradient bound
  `‖𝒢 D 𝒢‖_HS ≤ ‖D‖ √dim ‖𝒢‖²` as in the paper's proof. -/
structure TraceMatrixContract : Prop where
  covariance : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ η₀ M : ℝ, 0 < η₀ → ∀ (L : ℕ) (K : ℝ),
    ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
      ∀ (ℓf ℓU : ℕ), ℓf ≤ L → ℓU ≤ L →
      ∀ (εf : Fin ℓf → Bool) (Df : Fin (ℓf + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
        (εU : Fin ℓU → Bool) (DU : Fin (ℓU + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ),
        (∀ j, ‖Df j‖ ≤ K) → (∀ j, ‖DU j‖ ≤ K) →
        let μ := layerLaw W b σ
        let f : LayerSample W σ → ℂ := fun ω =>
          (W : ℂ)⁻¹ * (wordEval εf Df (layerResolvent σ E z X ω)).trace
        let U : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ := fun ω =>
          wordEval εU DU (layerResolvent σ E z X ω)
        Integrable f μ ∧ (∀ x y, Integrable (fun ω => U ω x y) μ) ∧
          (∀ x y, Integrable (fun ω => f ω * U ω x y) μ) ∧
          ‖matrixExpect μ (fun ω => f ω • U ω) - (∫ ω, f ω ∂μ) • matrixExpect μ U‖ ≤
            C / (W : ℝ) ^ 2
  fluctuation : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ η₀ M : ℝ, 0 < η₀ → ∀ K : ℝ,
    ∃ ε₃ C : ℝ, 0 < ε₃ ∧ ∀ (W : ℕ), 0 < W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
      ∀ D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖D‖ ≤ K →
      ∀ p : ℝ, 2 ≤ p → p ≤ ε₃ * W →
        let μ := layerLaw W b σ
        let f : LayerSample W σ → ℂ := fun ω =>
          (W : ℂ)⁻¹ * (D * layerResolvent σ E z X ω).trace
        eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂μ) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (C * Real.sqrt p / W)

/-!
## 4. The layer-contraction lemma and the clauses of its proof
-/

/-- The layer-contraction lemma.
* separate ports (`B = diag(B₁,B₂)`, port parameter `z_∂`): both outgoing mean port traces
  satisfy `|E W⁻¹ Tr(𝒢_ports)_{jj} - a| ≤ q_* d(X) + C W⁻²`;
* common port (`B = (B₁ᵀ,B₂ᵀ)ᵀ`, port parameter `z₀ = a⁻¹ + 2ba`):
  `|E W⁻¹ Tr 𝒢_port - a| ≤ C d(X) + C W⁻²`.
Expectations are over `layerLaw` (conditional on `X`). -/
def LayerContractionContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar C qstar : ℝ, 0 < dstar ∧ 0 ≤ qstar ∧ qstar < 1 ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
        (∀ j : Fin 2,
          ‖(∫ ω, portBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) j
              ∂layerLaw W b .separate) - matchedA E‖ ≤
            qstar * matchedDistance b E X + C / (W : ℝ) ^ 2) ∧
        ‖(∫ ω, portBlockTrace (layerResolvent .common E (commonZ b E) X ω) 0
            ∂layerLaw W b .common) - matchedA E‖ ≤
          C * matchedDistance b E X + C / (W : ℝ) ^ 2

/-- Top matrix `-E - X - c diag(m_i) - b diag(u_i)` of the two-port Dyson equation
(separate ports). -/
def twoPortTop (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (m u : Fin 2 → ℂ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  -((E : ℂ) • 1) - X - Matrix.diagonal (fun x => ((1 - 2 * b : ℝ) : ℂ) * m x.1 + (b : ℂ) * u x.1)

/-- Top matrix with the common-port shift `b u₀ I`. -/
def commonPortTop (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (m : Fin 2 → ℂ) (u₀ : ℂ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  -((E : ℂ) • 1) - X - Matrix.diagonal (fun x => ((1 - 2 * b : ℝ) : ℂ) * m x.1 + (b : ℂ) * u₀)

/-- The two-port Dyson equation (separate ports): `m_i = W⁻¹ Tr[top⁻¹]_{ii}`, `u_i = (z - b m_i)⁻¹`. -/
def IsTwoPortSolution (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (m u : Fin 2 → ℂ) : Prop :=
  ∀ i, m i = blockTrace (twoPortTop b E X m u)⁻¹ i ∧ u i = (boundaryZ b E - (b : ℂ) * m i)⁻¹

/-- Common-port version: `u₀ = (z₀ - b(m₁ + m₂))⁻¹`. -/
def IsCommonPortSolution (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (m : Fin 2 → ℂ) (u₀ : ℂ) : Prop :=
  (∀ i, m i = blockTrace (commonPortTop b E X m u₀)⁻¹ i) ∧
    u₀ = (commonZ b E - (b : ℂ) * (m 0 + m 1))⁻¹

/-- **The comparison clause of the layer contraction lemma**: the deterministic comparison
solution satisfies `max_i|m_i - a| + |u - a| ≤ C d(X)` in both port cases. Same quantifiers and
setting as `LayerContractionContract`, for `W ≥ W₀` (the physical-block means have no
deterministic bound; the inverse moments of the paper hold only for large `W`): on
`d(X) ≤ d_*` there is a solution of the two-port Dyson equation (resp. its common-port form)
with negative imaginary parts within `C d(X)` of `a`, and the physical and port means of the
layer are within `C W⁻²` of it (this identifies the branch selected by the means). -/
def LayerComparisonContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
        (∃ m u : Fin 2 → ℂ, IsTwoPortSolution b E X m u ∧
          (∀ i, (m i).im < 0 ∧ (u i).im < 0) ∧
          (∀ i, ‖m i - matchedA E‖ + ‖u i - matchedA E‖ ≤ C * matchedDistance b E X) ∧
          ∀ i : Fin 2,
            ‖(∫ ω, physBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) i
                ∂layerLaw W b .separate) - m i‖ ≤ C / (W : ℝ) ^ 2 ∧
            ‖(∫ ω, portBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) i
                ∂layerLaw W b .separate) - u i‖ ≤ C / (W : ℝ) ^ 2) ∧
        (∃ (m : Fin 2 → ℂ) (u₀ : ℂ), IsCommonPortSolution b E X m u₀ ∧
          (∀ i, (m i).im < 0) ∧ u₀.im < 0 ∧
          (∀ i, ‖m i - matchedA E‖ ≤ C * matchedDistance b E X) ∧
          ‖u₀ - matchedA E‖ ≤ C * matchedDistance b E X ∧
          (∀ i : Fin 2,
            ‖(∫ ω, physBlockTrace (layerResolvent .common E (commonZ b E) X ω) i
                ∂layerLaw W b .common) - m i‖ ≤ C / (W : ℝ) ^ 2) ∧
          ‖(∫ ω, portBlockTrace (layerResolvent .common E (commonZ b E) X ω) 0
              ∂layerLaw W b .common) - u₀‖ ≤ C / (W : ℝ) ^ 2)

/-- `Q_{ij} = W⁻¹ Tr R_{ij} R_{ji}` for a two-port matrix `R`. -/
def blockPairTrace {W : ℕ} (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) : ℂ :=
  (W : ℂ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W, R (i, x) (j, y) * R (j, y) (i, x)

/-- The outgoing coefficient `q₀(E) = b(1-b)/(1 - b - |c + b²a²|)` of the strict contraction. -/
def outgoingCoefficient (b E : ℝ) : ℝ :=
  b * (1 - b) / (1 - b - ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖)

/-- Strict contraction of the linearized layer recursion.
* `scalar`: `|c + b²a²| < (1-b)²` on `I` and `q₀(E) ≤ q < 1` uniformly on `I`.
* `rowSum`: `max_i Σ_j |Q_ij| ≤ (1-b)⁻¹ + C d(X)` for every deterministic Hermitian
  two-port `X`, `R = (z_∂ - X)⁻¹` (normality and the imaginary resolvent identity).
* `linearized`: the linearized separate-port equations `v = δ + (c + b²a²) Q v`,
  `w = b a² v` have outgoing coefficient below `q < 1` on `d(X) ≤ d_*`:
  `max_i |w_i| ≤ q max_i |δ_i|` for every solution. -/
structure StrictContractionContract : Prop where
  scalar : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ q : ℝ, q < 1 ∧
    ∀ E ∈ bulkInterval κ,
      ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ < (1 - b) ^ 2 ∧
        outgoingCoefficient b E ≤ q
  rowSum : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ C : ℝ,
    ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ, ∀ i : Fin 2,
      ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ ≤
        (1 - b)⁻¹ + C * matchedDistance b E X
  linearized : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar q : ℝ, 0 < dstar ∧ q < 1 ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
      ∀ δ v : Fin 2 → ℂ,
        (∀ i, v i = δ i + (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2) *
          ∑ j, blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j * v j) →
        ∀ i, ‖(b : ℂ) * matchedA E ^ 2 * v i‖ ≤ q * max ‖δ 0‖ ‖δ 1‖
  margin : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar t : ℝ, 0 < dstar ∧ t < 1 - b ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar → ∀ i : Fin 2,
        ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ *
          ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ ≤ t

/-!
## 5. Paths and the ring: the matched-traces theorem
-/

/-- Gaussian coordinates of a path of `r` physical blocks with two ports: diagonal blocks,
the `r - 1` internal bonds (bond `k` joins blocks `k` and `k+1`), and the two port bonds
(port 0 at block 0, port 1 at block `r-1`). -/
abbrev PathSample (W r : ℕ) :=
  (Fin r → Matrix (Fin W) (Fin W) ℂ) × (Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ) ×
    (Fin 2 → Matrix (Fin W) (Fin W) ℂ)

/-- Law of a path: independent `GUE_W(c/W)` blocks and `Gin(b/W)` bonds. -/
def pathLaw (W r : ℕ) (b : ℝ) : Measure (PathSample W r) :=
  (Measure.pi fun _ : Fin r => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))).prod
    ((Measure.pi fun _ : Fin (r - 1) => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))).prod
      (Measure.pi fun _ : Fin 2 => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))))

/-- The Hermitian path matrix (blocks on the diagonal, bonds on the first off-diagonals). -/
def pathMatrix {W r : ℕ} (ω : PathSample W r) : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ :=
  fun x y =>
    if x.1 = y.1 then ω.1 x.1 x.2 y.2
    else if h : x.1.val + 1 = y.1.val then ω.2.1 ⟨x.1.val, by have := y.1.isLt; omega⟩ x.2 y.2
    else if h' : y.1.val + 1 = x.1.val then
      star (ω.2.1 ⟨y.1.val, by have := x.1.isLt; omega⟩ y.2 x.2)
    else 0

/-- Port coupling: block 0 to port 0 and block `r-1` to port 1 (both for `r = 1`). -/
def pathPortCoupling {W r : ℕ} (ω : PathSample W r) : Matrix (Fin r × Fin W) (Fin 2 × Fin W) ℂ :=
  fun x y =>
    if (y.1 = 0 ∧ x.1.val = 0) ∨ (y.1 = 1 ∧ x.1.val + 1 = r) then ω.2.2 y.1 x.2 y.2 else 0

/-- The Schur self-energy `X_r = B_p* (H_path - E)⁻¹ B_p` of the path on its two ports. -/
def pathSchur {W r : ℕ} (E : ℝ) (ω : PathSample W r) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (pathPortCoupling ω)ᴴ * (pathMatrix ω - (E : ℂ) • 1)⁻¹ * pathPortCoupling ω

/-- `R_r = (z_∂ - X_r)⁻¹`. -/
def pathPortResolvent {W r : ℕ} (b E : ℝ) (ω : PathSample W r) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (boundaryZ b E • 1 - pathSchur E ω)⁻¹

/-- Sites of a single ring block `k`. -/
abbrev BlockSite (p : Parameters) (k : ZMod p.n) := {x : p.Site // x.1 = k}

/-- Sites off the ring block `k` (the path `R` of the one-block complement). -/
abbrev OffBlockSite (p : Parameters) (k : ZMod p.n) := {x : p.Site // x.1 ≠ k}

/-- The one-block complement `Σ = C* (H_R - E)⁻¹ C`, `R` = all blocks but `k`,
`C = H_{R,k}`. -/
def oneBlockComplement (p : Parameters) (k : ZMod p.n) (H : p.SiteMatrix) (E : ℝ) :
    Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  let HR : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ := fun x y => H x.1 y.1
  let C : Matrix (OffBlockSite p k) (BlockSite p k) ℂ := fun x y => H x.1 y.1
  Cᴴ * (HR - (E : ℂ) • 1)⁻¹ * C

/-- Normalized trace `W⁻¹ Tr` on one ring block. -/
def oneBlockTrace (p : Parameters) (k : ZMod p.n) (M : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    ℂ :=
  (p.W : ℂ)⁻¹ * M.trace

/-- Normalized trace `W⁻¹ Tr P_k M` of block `k` inside a pair matrix. -/
def pairBlockTrace (p : Parameters) (i : ZMod p.n) (M : PairMatrix p i) (k : ZMod p.n) : ℂ :=
  (p.W : ℂ)⁻¹ * ∑ x : PairSite p i, if x.1.1 = k then M x x else 0

/-- The pair residual `K(E) = F(E) - E = V - C*(H_R - E)⁻¹ C - E` of the split state
`ω = (H_R, C, V)` of the pair splitting. With `s = min(c,b)` this is `K_e(E)` of the Dyson
center. -/
def pairResidual (p : Parameters) (i : ZMod p.n) (ω : SplitState p i) (E : ℝ) : PairMatrix p i :=
  physicalCoareaF ω.1 ω.2.1 ω.2.2 E - (E : ℂ) • 1

/-- The matched-traces theorem.
* `path`: uniformly in `W`, `2 ≤ p ≤ ε₀ W`, `1 ≤ r ≤ TW`
  (both parities, one- and two-block cores) and deterministic `E ∈ I`, under `pathLaw`:
  `‖max_i |W⁻¹ Tr(R_r)_{ii} - a|‖_p ≤ C √p / W`.
* `commonPort`: the exact physical ring (raw `H`, row variance
  one), `4 ≤ n ≤ TW`, every block `k` (the paper: block zero; every block by cyclic invariance),
  `Σ` the one-block complement: `‖W⁻¹ Tr(z₀ - Σ)⁻¹ - a‖_p ≤ C √p / W`. -/
structure MatchedTracesContract : Prop where
  path : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W →
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
            ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖)
          (ENNReal.ofReal p) (pathLaw W r b) ≤ ENNReal.ofReal (C * Real.sqrt p / W)
  commonPort : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ), E ∈ bulkInterval κ →
      ∀ q : ℝ, 2 ≤ q → q ≤ ε₀ * p.W →
        eLpNorm (fun H => ‖oneBlockTrace p k ((commonZ b E • 1 - oneBlockComplement p k H E)⁻¹) -
            matchedA E‖) (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤
          ENNReal.ofReal (C * Real.sqrt q / p.W)
  residualPair : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T s : ℝ, 0 < κ → 0 < s →
    s < 2 * min (1 - 2 * b) b →
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
      IsPairSplitting p i model s Pω → ∀ E ∈ bulkInterval κ,
      ∀ q : ℝ, 2 ≤ q → q ≤ ε₀ * p.W →
        eLpNorm (fun ω =>
            max ‖pairBlockTrace p i ((pairResidual p i ω E - ((s : ℂ) * matchedA E) • 1)⁻¹) i -
                matchedA E‖
              ‖pairBlockTrace p i ((pairResidual p i ω E - ((s : ℂ) * matchedA E) • 1)⁻¹) (i + 1) -
                matchedA E‖)
          (ENNReal.ofReal q) Pω ≤ ENNReal.ofReal (C * Real.sqrt q / p.W)

/-!
## 6. The stopped scalar recursion: one step and exit
-/

/-- Growing two-ended path: a core of `r₀ ∈ {1, 2}` blocks with its port bonds, then `L`
fresh separate-port layers, each adding one block at each end (the two-ended recursion). -/
abbrev GrowthSample (W r₀ L : ℕ) := PathSample W r₀ × (Fin L → LayerSample W .separate)

/-- Law of the growing path: core and layers independent. -/
def growthLaw (W r₀ L : ℕ) (b : ℝ) : Measure (GrowthSample W r₀ L) :=
  (pathLaw W r₀ b).prod (Measure.pi fun _ : Fin L => layerLaw W b .separate)

/-- `X_{r₀ + 2k}` along the growing path: the core Schur matrix, then
`X_{r+2} = B*(A - E - X_r)⁻¹ B` for each of the first `k` layers (`k ≤ L`; constant after). -/
def grownSchur {W r₀ L : ℕ} (E : ℝ) (ω : GrowthSample W r₀ L) :
    ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | 0 => pathSchur E ω.1
  | k + 1 =>
    if h : k < L then layerSchur .separate E (grownSchur E ω k) (ω.2 ⟨k, h⟩)
    else grownSchur E ω k

/-- The stopped scalar recursion.
* `oneStep` (conditional on the old path = deterministic `X`): `b, I`
  first; then `d₀ > 0, q < 1, C, ε > 0`; for `W ≥ 1`, Hermitian two-port `X` with
  `d(X) ≤ d₀` and `E ∈ I`, almost surely `d(X₊) ≤ q d(X) + C W⁻² + ξ` with the explicit
  fresh error `ξ = max_j |W⁻¹Tr(𝒢_ports)_{jj} - E W⁻¹Tr(𝒢_ports)_{jj}|`, and
  `‖ξ‖_p ≤ C √p / W` for `2 ≤ p ≤ ε W`.
* `exit`: `b, I, T` first; then `d₀ > 0`; for every smaller radius
  `0 < d' ≤ d₀` (the proof of the clock-moment lemma reduces the radius; a mild
  strengthening of the fixed `d_*`, by the same argument) there are `c > 0` and
  `W₀`; for `W ≥ W₀`, both cores `r₀ ∈ {1,2}`, every `L` with `r₀ + 2L ≤ TW` and `E ∈ I`,
  `P(∃ k ≤ L, d(X_{r₀+2k}) > d') ≤ exp(-c W log W)`. -/
structure ScalarRecursionContract : Prop where
  oneStep : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ d₀ q C ε : ℝ, 0 < d₀ ∧ q < 1 ∧ 0 < ε ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ d₀ →
        let μ := layerLaw W b .separate
        let g : LayerSample W .separate → Fin 2 → ℂ := fun ω j =>
          portBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) j
        let ξ : LayerSample W .separate → ℝ := fun ω =>
          max ‖g ω 0 - ∫ ω', g ω' 0 ∂μ‖ ‖g ω 1 - ∫ ω', g ω' 1 ∂μ‖
        (∀ᵐ ω ∂μ, matchedDistance b E (layerSchur .separate E X ω) ≤
          q * matchedDistance b E X + C / (W : ℝ) ^ 2 + ξ ω) ∧
        ∀ p : ℝ, 2 ≤ p → p ≤ ε * W →
          eLpNorm ξ (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C * Real.sqrt p / W)
  exit : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d' : ℝ, 0 < d' → d' ≤ d₀ →
      ∃ (c : ℝ) (W₀ : ℕ), 0 < c ∧ ∀ (W : ℕ), W₀ ≤ W → 0 < W →
      ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) → ∀ L : ℕ, ((r₀ + 2 * L : ℕ) : ℝ) ≤ T * W →
      ∀ E ∈ bulkInterval κ,
        growthLaw W r₀ L b {ω | ∃ k ≤ L, d' < matchedDistance b E (grownSchur E ω k)} ≤
          ENNReal.ofReal (Real.exp (-(c * W * Real.log W)))

/-!
## 7. The fresh-count lemma
-/

/-- The fresh-count lemma.
* `mean`: `b, I` first, then `d_*, C`; for every `W ≥ 1`, Hermitian `F`
  (any norm) and `E ∈ I` with `d ≤ d_*`:
  `|E_A N_-(A - E - F) - Θ_{z₀}(F) - (cW/(2π)) Im a²| ≤ C(W d² + W^{2/5} log(2W))`.
* `fluctuation`: for every fixed `p ≥ 1` there is `C_p`; for every `W`, every Hermitian `F`
  and every real `E`, `‖N_- - E_A N_-‖_p ≤ C_p √W`. -/
structure FreshCountContract : Prop where
  mean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar C : ℝ, 0 < dstar ∧
      ∀ (W : ℕ), 0 < W → ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian →
      ∀ E ∈ bulkInterval κ,
        let a := matchedA E
        let z₀ : ℂ := -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * a
        let d := ‖(W : ℂ)⁻¹ * ((z₀ • 1 - F)⁻¹).trace - a‖
        d ≤ dstar →
          |(∫ A, (negativeCount (A - (E : ℂ) • 1 - F) : ℝ)
              ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) - phaseCount z₀ F -
            (1 - 2 * b) * W / (2 * Real.pi) * (a ^ 2).im| ≤
            C * (W * d ^ 2 + (W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * W))
  fluctuation : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ p : ℝ, 1 ≤ p → ∃ Cp : ℝ,
    ∀ (W : ℕ), 0 < W → ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian → ∀ E : ℝ,
      let μ := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
      eLpNorm (fun A => (negativeCount (A - (E : ℂ) • 1 - F) : ℝ) -
          ∫ A', (negativeCount (A' - (E : ℂ) • 1 - F) : ℝ) ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cp * Real.sqrt W)

/-!
## 8. The compensated-phase lemma and the displays of its proof
-/

/-- `N_r(E)`: eigenvalues of the path matrix below `E`. -/
def pathCount {W r : ℕ} (E : ℝ) (ω : PathSample W r) : ℕ :=
  negativeCount (pathMatrix ω - (E : ℂ) • 1)

/-- `Ψ_r = N_r(E) + π⁻¹ Im Tr log(z_∂ - X_r) = N_r(E) + Θ_{z_∂}(X_r)`. -/
def compensatedPhase {W r : ℕ} (b E : ℝ) (ω : PathSample W r) : ℝ :=
  (pathCount E ω : ℝ) + phaseCount (boundaryZ b E) (pathSchur E ω)

/-- The compensated phase on a path.
* `fluctuation`: `b, I, T` and each fixed `p ≥ 1` first; `‖Ψ_r - EΨ_r‖_p ≤ C_p √(r+1)`.
* `mean`: `b, I, T` first; `|EΨ_r - r W F_sc(E) - W(2ℓ + bh)| ≤ C (r+1)/W`. -/
structure CompensatedPhaseContract : Prop where
  fluctuation : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ Cp : ℝ, ∀ (W : ℕ), 0 < W → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
      eLpNorm (fun ω => compensatedPhase b E ω - ∫ ω', compensatedPhase b E ω' ∂pathLaw W r b)
          (ENNReal.ofReal p) (pathLaw W r b) ≤
        ENNReal.ofReal (Cp * Real.sqrt (r + 1))
  mean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ C : ℝ, ∀ (W : ℕ), 0 < W → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
      |(∫ ω, compensatedPhase b E ω ∂pathLaw W r b) - r * W * semicircleCDF E -
          W * (2 * phaseEll E + b * phaseH E)| ≤ C * (r + 1) / W

/-- The compensated one-layer increment.
* separate ports: `|E[N_-(A-E-X) + Θ_{z_∂}(X₊)] - Θ_{z_∂}(X) - 2W F_sc(E)| ≤ C(W d(X)² + W⁻¹)`;
* common port (`Ξ`): `|E[N_-(A-E-X) + Θ_{z₀}(X₊)] - Θ_{z_∂}(X) - W(ℓ + h)| ≤ C(W d(X)² + W⁻¹)`.
`b, I` first, then `C`; uniformly in `W ≥ 1`, every Hermitian `X` and `E ∈ I` (off the scalar
domain the bound is trivial since both sides are `O(W)`). -/
structure CompensatedIncrementContract : Prop where
  separate : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ C : ℝ, ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ,
      |(∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
            phaseCount (boundaryZ b E) (layerSchur .separate E X ω)) ∂layerLaw W b .separate) -
          phaseCount (boundaryZ b E) X - 2 * W * semicircleCDF E| ≤
        C * (W * matchedDistance b E X ^ 2 + (W : ℝ)⁻¹)
  common : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ C : ℝ, ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ,
      |(∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
            phaseCount (commonZ b E) (layerSchur .common E X ω)) ∂layerLaw W b .common) -
          phaseCount (boundaryZ b E) X - W * (phaseEll E + phaseH E)| ≤
        C * (W * matchedDistance b E X ^ 2 + (W : ℝ)⁻¹)

/-- `Ξ_{n-1} = N_{H_R}(E) + Θ_{z₀}(Σ)` for the ring with block `k` deleted. -/
def ringCompensatedPhase (p : Parameters) (k : ZMod p.n) (H : p.SiteMatrix) (E : ℝ) : ℝ :=
  let HR : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ := fun x y => H x.1 y.1
  (negativeCount (HR - (E : ℂ) • 1) : ℝ) + phaseCount (commonZ p.b E) (oneBlockComplement p k H E)

/-- The compensated phase on the ring with one block deleted.
* `fluctuation`: each fixed `p ≥ 1`: `‖Ξ_{n-1} - EΞ_{n-1}‖_p ≤ C_p √n`;
* `mean`: `|EΞ_{n-1} - (n-1) W F_sc(E) - W(ℓ + bh)| ≤ C n / W`. -/
structure RingCompensatedPhaseContract : Prop where
  fluctuation : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
    ∃ Cq : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ), E ∈ bulkInterval κ →
      eLpNorm (fun H => ringCompensatedPhase p k H E -
          ∫ H', ringCompensatedPhase p k H' E ∂(model.law : Measure p.SiteMatrix))
          (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤
        ENNReal.ofReal (Cq * Real.sqrt p.n)
  mean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ C : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ), E ∈ bulkInterval κ →
      |(∫ H, ringCompensatedPhase p k H E ∂(model.law : Measure p.SiteMatrix)) -
          ((p.n : ℝ) - 1) * p.W * semicircleCDF E - p.W * (phaseEll E + b * phaseH E)| ≤
        C * p.n / p.W

/-!
## 9. The rank-location theorem
-/

/-- The normalized block-mass law `n p_{αk} dP` (`physicalOrderedBlockMass`). -/
def physicalBlockMeasure (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (k : ZMod p.n) : Measure p.SiteMatrix :=
  (model.law : Measure p.SiteMatrix).withDensity
    (fun H => ENNReal.ofReal ((p.n : ℝ) * physicalOrderedBlockMass p H α k))

/-- The laws under which the eigenvalue-only statements of the rank-location theorem hold: the
physical law, each normalized block-mass law and each pair-mass law. -/
inductive MassLaw (p : Parameters)
  | physical
  | block (α : Fin p.N) (k : ZMod p.n)
  | pair (α : Fin p.N) (i : ZMod p.n)

/-- The measure of a `MassLaw`. -/
def MassLaw.measure {p : Parameters} (model : p.GaussianRingModel) : MassLaw p → Measure p.SiteMatrix
  | .physical => (model.law : Measure p.SiteMatrix)
  | .block α k => physicalBlockMeasure p model α k
  | .pair α i => physicalPairMeasure p model α i

/-- `N_H(E) = #{λ_j < E}`. -/
def physicalCount (p : Parameters) (H : p.SiteMatrix) (E : ℝ) : ℕ :=
  negativeCount (H - (E : ℂ) • 1)

/-- The rank-location theorem.
* `count_moment`: `b, I, T`, fixed `p ≥ 1` first;
  `‖N_H(E) - N F_sc(E)‖_p ≤ C_p √W` for deterministic `E ∈ I`;
* `count_mean`: `|E N_H(E) - N F_sc(E)| ≤ C(n/W + W^{2/5} log 2W)`;
* `location`: `b, T`, `ϑ ∈ (0,1/2)`, fixed `p ≥ 1` first;
  `sup_{ϑ ≤ α/N ≤ 1-ϑ} ‖λ_α - e_α‖_p ≤ C/(n √W)` (one-based `IsBulkRank`, increasing
  eigenvalues `physicalOrderedEigenvalue`). -/
structure RankLocationContract : Prop where
  count_moment : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
    ∃ Cq : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (L : MassLaw p) (E : ℝ), E ∈ bulkInterval κ →
      eLpNorm (fun H => (physicalCount p H E : ℝ) - p.N * semicircleCDF E) (ENNReal.ofReal q)
          (L.measure model) ≤ ENNReal.ofReal (Cq * Real.sqrt p.W)
  count_mean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ C : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (L : MassLaw p) (E : ℝ), E ∈ bulkInterval κ →
      |(∫ H, (physicalCount p H E : ℝ) ∂L.measure model) - p.N * semicircleCDF E| ≤
        C * ((p.n : ℝ) / p.W + (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W))
  location : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ T ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 → ∀ q : ℝ, 1 ≤ q →
    ∃ C : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (L : MassLaw p) (α : Fin p.N), IsBulkRank p ϑ α →
      eLpNorm (fun H => physicalOrderedEigenvalue p H α - classicalLocation p α)
          (ENNReal.ofReal q) (L.measure model) ≤
        ENNReal.ofReal (C / (p.n * Real.sqrt p.W))

/-!
## 10. The weighted-layer lemma
-/

/-- The weighted-layer lemma.
* `moments`: for each fixed `p ≥ 1` there are `C_p, W₀`; for `W ≥ W₀`:
  `‖K𝒢₁₁‖, ‖𝒢₁₁K*‖, ‖L‖` have `L^p` norms at most `C_p` (uniform in `X`, `E ∈ I`).
* `ward` (weighted Ward identity): on `d(X) ≤ d_*`, `‖E LL* - I‖ ≤ C(d(X) + W⁻²)`, `W ≥ W₀`.
* `clockMean`: on `d(X) ≤ d_*`,
  `E W⁻¹ Tr L*YL ≤ (1 + C d(X) + C W⁻²) u`, `W ≥ W₀`.
* `clockNoise`: each fixed `p`, `W ≥ W₀(p)`, every Hermitian `X`:
  `‖W⁻¹Tr L*YL - E‖_p ≤ (C_p/W) √(W⁻¹ Tr Y²) ≤ C_p u/√W` (both inequalities; the proof
  does not use the scalar domain).
* `unrestricted`: every Hermitian `X`: `‖W⁻¹ Tr L*YL‖_p ≤ C_p u`. -/
structure WeightedLayerContract : Prop where
  moments : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let G := fun ω => layerResolvent .separate E (boundaryZ b E) X ω
      eLpNorm (fun ω => ‖K * (G ω).toBlocks₁₁‖) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cp ∧
      eLpNorm (fun ω => ‖(G ω).toBlocks₁₁ * Kᴴ‖) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cp ∧
      eLpNorm (fun ω => ‖K * (G ω).toBlocks₁₂‖) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cp
  ward : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      matchedDistance b E X ≤ dstar →
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Lm := fun ω => K * (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂
      (∀ x y, Integrable (fun ω => (Lm ω * (Lm ω)ᴴ) x y) μ) ∧
      ‖matrixExpect μ (fun ω => Lm ω * (Lm ω)ᴴ) - 1‖ ≤
        C * (matchedDistance b E X + 1 / (W : ℝ) ^ 2)
  clockMean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      matchedDistance b E X ≤ dstar → ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      Y.PosSemidef →
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Lm := fun ω => K * (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂
      let u := (W : ℝ)⁻¹ * Y.trace.re
      Integrable (fun ω => (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re) μ ∧
      (∫ ω, (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re ∂μ) ≤
        (1 + C * matchedDistance b E X + C / (W : ℝ) ^ 2) * u
  clockNoise : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
    ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Lm := fun ω => K * (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂
      let t := fun ω => (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re
      let u := (W : ℝ)⁻¹ * Y.trace.re
      eLpNorm (fun ω => t ω - ∫ ω', t ω' ∂μ) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (Cp / W * Real.sqrt ((W : ℝ)⁻¹ * (Y * Y).trace.re)) ∧
        Cp / W * Real.sqrt ((W : ℝ)⁻¹ * (Y * Y).trace.re) ≤ Cp * u / Real.sqrt W
  unrestricted : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
    ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Lm := fun ω => K * (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂
      eLpNorm (fun ω => (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cp * ((W : ℝ)⁻¹ * Y.trace.re))

/-!
## 11. The physical center: simultaneous splitting, Dyson center and its regular domain
-/

section Center

variable (p : Parameters) (i : ZMod p.n)

/-- The splitting parameter `s = min(c, b)` of the simultaneous splitting. -/
def splitS : ℝ := min p.c p.b

/-- Embedding of a pair matrix on `S_e = {i, i+1}` into the site matrices. -/
def embedPair (G : PairMatrix p i) : p.SiteMatrix :=
  fun x y =>
    if hx : x.1 = i ∨ x.1 = i + 1 then
      if hy : y.1 = i ∨ y.1 = i + 1 then G ⟨x, hx⟩ ⟨y, hy⟩ else 0
    else 0

/-- `K_e(E)`: the Schur complement of `H^{(e)} - E` on `S_e`, from the residual matrix
`H^{(e)} = H - G_e`. -/
def edgeSchur (Hres : p.SiteMatrix) (E : ℝ) : PairMatrix p i :=
  physicalCoareaF (exteriorBlock p i Hres) (couplingBlock p i Hres) (pairBlock p i Hres) E -
    (E : ℂ) • 1

/-- Block projection `P_{S_g}` onto the pair `S_g = {g, g+1}` (also the direction of the
auxiliary scalar `ξ_g`, since `G_g = G_g⁰ + ξ_g I_{S_g}`). -/
def pairProjector (g : ZMod p.n) : p.SiteMatrix :=
  Matrix.diagonal (fun x => if x.1 = g ∨ x.1 = g + 1 then 1 else 0)

/-- The full compressed inverse `ℛ_e(ζ) = P_S (H^{(e)} - E - ζ P_S)⁻¹ P_S |_S` of the proof of
the smooth-center lemma. It equals `(K_e(E) - ζ)⁻¹` whenever `H^{(e)}_R - E` is
invertible (Schur complement), and, unlike `(K_e - ζ)⁻¹`, it does not jump at real Schur
poles; at a deterministic or pair-law-selected energy the two agree almost surely (pair pole
exclusion). -/
def compressedResolvent (Hres : p.SiteMatrix) (E : ℝ) (ζ : ℂ) : PairMatrix p i :=
  fun x y => (Hres - (E : ℂ) • 1 - ζ • pairProjector p i)⁻¹ x.1 y.1

/-- The residual `ε_e = (Σ_{k ∈ {i,i+1}} |W⁻¹ Tr P_k ℛ_e(sμ) - μ|²)^{1/2}`, `μ = ā`
(with `R_e⁰ = (K_e - sμ)⁻¹`). -/
def centerResidual (Hres : p.SiteMatrix) (E : ℝ) : ℝ :=
  let μ := conj (matchedA E)
  let R := compressedResolvent p i Hres E ((splitS p : ℂ) * μ)
  Real.sqrt (‖pairBlockTrace p i R i - μ‖ ^ 2 + ‖pairBlockTrace p i R (i + 1) - μ‖ ^ 2)

/-- `ζ` is an upper-half-plane root of `ζ = s N_aux⁻¹ Tr ℛ_e(ζ)`, `N_aux = 2W` (off Schur
poles: `ζ = s N_aux⁻¹ Tr (K_e - ζ)⁻¹`, the Dyson center equation). -/
def IsDysonRoot (Hres : p.SiteMatrix) (E : ℝ) (ζ : ℂ) : Prop :=
  0 < ζ.im ∧ ζ = (splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ * (compressedResolvent p i Hres E ζ).trace

/-- The root `ζ_e` selected in the disk `|ζ - sμ| < ρ₀` (zero if there is none; the regular
domain requires one, and the domain clause proves it is unique there). -/
def dysonRoot (ρ₀ : ℝ) (Hres : p.SiteMatrix) (E : ℝ) : ℂ := by
  classical
  exact if h : ∃ ζ, IsDysonRoot p i Hres E ζ ∧
      ‖ζ - (splitS p : ℂ) * conj (matchedA E)‖ < ρ₀
    then Classical.choose h else 0

/-- `J_e = P_i - P_{i+1}` on the pair. -/
def pairContrast : PairMatrix p i :=
  Matrix.diagonal (fun x => if x.1.1 = i then 1 else -1)

/-- `(s/N_aux) Tr J_e |ℛ_e(ζ)|²`, `|M|² = M*M` (real since `J_e` is Hermitian), clipped to
`[-1, 1]`. At a Dyson root `|j_e| ≤ (s/N_aux) Tr|ℛ_e(ζ)|² = 1` (Ward identity), so the clip
is inactive there (the paper's "bounded by one"); it only makes the witness bounded at
every parameter. -/
def centerFormula (Hres : p.SiteMatrix) (E : ℝ) (ζ : ℂ) : ℝ :=
  max (-1) (min 1 ((splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ *
    (pairContrast p i * (compressedResolvent p i Hres E ζ)ᴴ *
      compressedResolvent p i Hres E ζ).trace).re)

/-- Constants of the regular domain, as positive functions of `b` and of the interval margin
`κ` (model data only; no estimate). -/
structure CenterDomainConstants where
  ε₁ : ℝ → ℝ → ℝ
  ρ₀ : ℝ → ℝ → ℝ
  ε₁_pos : ∀ b κ, 0 < ε₁ b κ
  ρ₀_pos : ∀ b κ, 0 < ρ₀ b κ

/-- The interval margin used for rank `α`: `κ_α = (2 - |e_α|)/2`, so that `e_α` lies well
inside `bulkInterval κ_α`; for `ϑ`-bulk ranks `κ_α ≥ ϑ/2` (`e_α ∈ bulkInterval ϑ`). -/
def rankMargin (α : Fin p.N) : ℝ := (2 - |classicalLocation p α|) / 2

/-- The regular domain `D_e(E) = {E ∈ I, ε_e(E) ≤ ε₁}`, `I = bulkInterval κ_α`, together with
the existence of a Dyson root in the disk `|ζ - sμ| < ρ₀` (which the domain clause derives from
`ε_e ≤ ε₁` for bulk ranks). -/
def InCenterDomain (cst : CenterDomainConstants) (α : Fin p.N) (Hres : p.SiteMatrix) (E : ℝ) :
    Prop :=
  E ∈ bulkInterval (rankMargin p α) ∧ centerResidual p i Hres E ≤ cst.ε₁ p.b (rankMargin p α) ∧
    ∃ ζ, IsDysonRoot p i Hres E ζ ∧
      ‖ζ - (splitS p : ℂ) * conj (matchedA E)‖ < cst.ρ₀ p.b (rankMargin p α)

/-- The regular Dyson center `j_e(E)`, extended by zero off its regular domain. -/
def dysonCenter (cst : CenterDomainConstants) (α : Fin p.N) (Hres : p.SiteMatrix) (E : ℝ) : ℝ := by
  classical
  exact if InCenterDomain p i cst α Hres E then
    centerFormula p i Hres E (dysonRoot p i (cst.ρ₀ p.b (rankMargin p α)) Hres E)
  else 0

end Center

/-- An extension carries the edge-`i` part of the simultaneous splitting: a pair
Gaussian `G_e ~ GUE_{2W}(s/(2W))`, `s = min(c,b)`, independent of `H - G_e`, where
`H = X.Hm` has the exact physical law. -/
def IsCenterSplitting {p : Parameters} {model : p.GaussianRingModel} {i : ZMod p.n}
    (X : PairExtension p model) (G : X.Ω → PairMatrix p i) : Prop :=
  Measurable G ∧ HasLaw G (gueMeasure (PairSite p i) (pairTime p (splitS p))) X.P ∧
    IndepFun (fun ω => X.Hm ω - embedPair p i (G ω)) G X.P

/-- **The center family is the Dyson center.**
For every parameter set,
model, rank `α` and pair `i`, the witness's extension carries the edge splitting and its
center is `ω ↦ j_e(λ_α(H))` built from `H - G_e` (the Dyson center, extended by zero off the
regular domain with constants `cst`).
Uses of a center family rely only on this characterization, never on the internals of `Ω`.
-/
def IsDysonCenterFamily (cst : CenterDomainConstants) (w : PairCenterFamily) : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n),
    ∃ G : (w p model α i).X.Ω → PairMatrix p i, IsCenterSplitting (w p model α i).X G ∧
      ∀ ω, (w p model α i).center ω =
        dysonCenter p i cst α ((w p model α i).X.Hm ω - embedPair p i (G ω))
          (physicalOrderedEigenvalue p ((w p model α i).X.Hm ω) α)

/-- Reindexing of a pair matrix to `Fin (2W)` (any fixed enumeration; every use below is
invariant under it). -/
def pairToFin {p : Parameters} {i : ZMod p.n} (M : PairMatrix p i) :
    Matrix (Fin (Fintype.card (PairSite p i))) (Fin (Fintype.card (PairSite p i))) ℂ :=
  Matrix.reindex (Fintype.equivFin (PairSite p i)) (Fintype.equivFin (PairSite p i)) M

/-- The regular domain of the physical center.
* `small`: `b, ϑ, T` and every fixed `q` first; then `C_q, W₀`; for `W > W₀`,
  `4 ≤ n ≤ TW`, every model, `ϑ`-bulk rank, pair, and every extension carrying the edge
  splitting, the pair-law probability that `λ_α` leaves the regular domain is at most
  `C_q W^{1-q}`. -/
structure CenterDomainContract (cst : CenterDomainConstants) : Prop where
  regular : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 →
    ∃ r₀ s₀ v₀ y₀ C : ℝ, FreshConstants (min (1 - 2 * b) b) r₀ s₀ v₀ ∧ 0 < y₀ ∧
      ∀ (p : Parameters), p.b = b → ∀ (α : Fin p.N), IsBulkRank p ϑ α → ∀ (i : ZMod p.n)
        (Hres : p.SiteMatrix), Hres.IsHermitian → ∀ E : ℝ,
        (exteriorBlock p i Hres - (E : ℂ) • 1).det ≠ 0 → InCenterDomain p i cst α Hres E →
        let K := edgeSchur p i Hres E
        let ζ := dysonRoot p i (cst.ρ₀ p.b (rankMargin p α)) Hres E
        FreshRegular (pairToFin (K + (E : ℂ) • 1)) (splitS p) E r₀ s₀ v₀ ∧
          IsDysonRoot p i Hres E ζ ∧
          compressedResolvent p i Hres E ζ = (K - ζ • 1)⁻¹ ∧
          (∀ ζ', IsDysonRoot p i Hres E ζ' →
            ‖ζ' - (splitS p : ℂ) * conj (matchedA E)‖ < cst.ρ₀ p.b (rankMargin p α) → ζ' = ζ) ∧
          ζ = (splitS p : ℂ) * freshDyson (pairToFin (K + (E : ℂ) • 1)) (splitS p) E ∧
          y₀ ≤ ζ.im ∧ ‖ζ‖ ≤ C ∧
          dysonCenter p i cst α Hres E = ((splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ *
            (pairContrast p i * ((K - ζ • 1)⁻¹)ᴴ * (K - ζ • 1)⁻¹).trace).re
  small : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ ϑ T : ℝ, 0 < ϑ → ϑ < 1 / 2 → ∀ q : ℝ,
    ∃ Cq W₀ : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W → W₀ < (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α → ∀ (i : ZMod p.n)
        (X : PairExtension p model) (G : X.Ω → PairMatrix p i), IsCenterSplitting X G →
        extendedPairMeasure p α i X.P X.Hm
            {ω | ¬ InCenterDomain p i cst α (X.Hm ω - embedPair p i (G ω))
              (physicalOrderedEigenvalue p (X.Hm ω) α)} ≤
          ENNReal.ofReal (Cq * (p.W : ℝ) ^ (1 - q))
  measurable : ∀ (p : Parameters) (α : Fin p.N) (i : ZMod p.n),
    Measurable ({x : p.SiteMatrix × ℝ | x.1.IsHermitian}.indicator
        (fun x => dysonCenter p i cst α x.1 x.2)) ∧
      MeasurableSet {x : p.SiteMatrix × ℝ | x.1.IsHermitian ∧ InCenterDomain p i cst α x.1 x.2}

/-- **The center supply**: a center family is the
Dyson center for *some* positive domain constants for which the domain clause holds.
This is
what a `PairCenterFamily` comes with, together with `QUE.PhysicalCenterContract`;
the domain clause's `small` part forces the constants to be non-degenerate, so the center
cannot be trivial. Uses of the center (the angular part) assume exactly this.
-/
def IsCenterSupply (w : PairCenterFamily) : Prop :=
  ∃ cst : CenterDomainConstants, IsDysonCenterFamily cst w ∧ CenterDomainContract cst

/-!
## 12. The smooth-center lemma
-/

/-- `H` is supported on the cyclic block band: `H_xy = 0` unless the blocks of `x, y` are
equal or adjacent (an almost-sure property of the physical law; it holds for `H - G_e` and is
preserved along every shift line `H + Σ_g t_g P_{S_g}`). -/
def IsRingBanded (p : Parameters) (H : p.SiteMatrix) : Prop :=
  ∀ x y : p.Site, ¬ (y.1 = x.1 ∨ y.1 = x.1 + 1 ∨ y.1 = x.1 - 1) → H x y = 0

/-- Every physical bond `H_{k,k+1}` of the ring other than the internal bond of the pair
`S_e = {e, e+1}` is invertible (an almost-sure property of the physical law). -/
def ExteriorBondsInvertible (p : Parameters) (e : ZMod p.n) (H : p.SiteMatrix) : Prop :=
  ∀ k : ZMod p.n, k ≠ e →
    (Matrix.of fun a b : Fin p.W => H (k, a) (k + 1, b)).det ≠ 0

/-- Cyclic distance between the edges `e` and `g` of the ring. -/
def edgeDistance (p : Parameters) (e g : ZMod p.n) : ℕ :=
  min (g - e).val (e - g).val

/-- An extension carries the full simultaneous splitting:
`H = V + Σ_g (G_g⁰ + ξ_g I_{S_g})` with `H ~` physical law, all `G_g⁰` (traceless parts of
`GUE_{2W}(s/(2W))`), all scalars `ξ_g ~ N(0, s/(2W)²)` and `V` independent. Only the edge-`e`
residual `H - G_e` and the scalars are named, which is all the smooth-center lemma uses. -/
structure SimultaneousSplitting (p : Parameters) (model : p.GaussianRingModel) where
  X : PairExtension p model
  G : ∀ g : ZMod p.n, X.Ω → PairMatrix p g
  ξ : ZMod p.n → X.Ω → ℝ
  measurable_G : ∀ g, Measurable (G g)
  measurable_ξ : ∀ g, Measurable (ξ g)

/-- The law clauses of `SimultaneousSplitting`. -/
def SimultaneousSplitting.IsExact {p : Parameters} {model : p.GaussianRingModel}
    (S : SimultaneousSplitting p model) : Prop :=
  (∀ g, HasLaw (S.G g) (gueMeasure (PairSite p g) (pairTime p (splitS p))) S.X.P) ∧
    (∀ g ω, tracelessPart (S.G g ω) + ((S.ξ g ω : ℝ) : ℂ) • 1 = S.G g ω) ∧
    iIndepFun (fun g ω => (tracelessPart (S.G g ω), S.ξ g ω)) S.X.P ∧
    IndepFun (fun ω => S.X.Hm ω - ∑ g, embedPair p g (S.G g ω)) (fun ω g => S.G g ω) S.X.P

/-- The smooth-center lemma.
* `support`: `Φ(·, E) = 0` unless `E ∈ bulkInterval κ'`;
* `agree`: on the regular domain (same almost-sure restrictions) `Φ = j_e` (`dysonCenter`);
* `moment`, `derivative`: at deterministic `E`, under every exact simultaneous splitting,
  `‖j^{sm}_e(E)‖_p ≤ C_p/W` and, for `g ≠ e`, `‖∂_{ξ_g} j^{sm}_e(E)‖_p ≤ C_p(ρ^{d(e,g)} + W^{-1/2})`
  (`∂_{ξ_g} j^{sm}_e` is the derivative of `Φ` along `P_{S_g}`); `∂_{ξ_e} j^{sm}_e = 0` holds
  by construction, since `H - G_e` does not contain `ξ_e`;
* `replacement`: at `λ_α` the pair-law probability that `j^{sm}_e ≠ j_e` is `≤ C_D W^{-D}`
  (so bounded pair-law observables change by `O_D(W^{-D})`). -/
def SmoothCenterContract (cst : CenterDomainConstants) : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ ϑ T : ℝ, 0 < ϑ → ϑ < 1 / 2 →
    ∃ (ρ κ' : ℝ), 0 ≤ ρ ∧ ρ < 1 ∧ 0 < κ' ∧
    ∃ Φ : ∀ (p : Parameters), Fin p.N → ZMod p.n → p.SiteMatrix → ℝ → ℝ,
      (∀ (p : Parameters) α e (H : p.SiteMatrix) (E : ℝ), |Φ p α e H E| ≤ 1) ∧
      (∀ (p : Parameters) α e, Measurable (fun x : p.SiteMatrix × ℝ => Φ p α e x.1 x.2)) ∧
      (∀ (p : Parameters) α e (H₀ : p.SiteMatrix), H₀.IsHermitian →
        IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : (ZMod p.n → ℝ) × ℝ =>
            Φ p α e (H₀ + ∑ g, (x.1 g : ℂ) • pairProjector p g) x.2)) ∧
      (∀ (p : Parameters) α e (H₀ : p.SiteMatrix) (E : ℝ), E ∉ bulkInterval κ' → Φ p α e H₀ E = 0) ∧
      (∀ (p : Parameters), p.b = b → ∀ α, IsBulkRank p ϑ α → ∀ e (H₀ : p.SiteMatrix) (E : ℝ),
        H₀.IsHermitian → IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
        InCenterDomain p e cst α H₀ E → Φ p α e H₀ E = dysonCenter p e cst α H₀ E) ∧
      (∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
        ∀ (model : p.GaussianRingModel) (S : SimultaneousSplitting p model), S.IsExact →
        ∀ α, IsBulkRank p ϑ α → ∀ (e g : ZMod p.n) (E : ℝ),
          eLpNorm (fun ω => Φ p α e (S.X.Hm ω - embedPair p e (S.G e ω)) E) (ENNReal.ofReal q)
              S.X.P ≤ ENNReal.ofReal (Cq / p.W) ∧
          (g ≠ e → eLpNorm (fun ω => deriv (fun t : ℝ =>
                Φ p α e (S.X.Hm ω - embedPair p e (S.G e ω) + (t : ℂ) • pairProjector p g) E) 0)
              (ENNReal.ofReal q) S.X.P ≤
            ENNReal.ofReal (Cq * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ)))))) ∧
      (∀ D : ℝ, ∃ CD : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
        ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α → ∀ (i : ZMod p.n)
          (X : PairExtension p model) (G : X.Ω → PairMatrix p i), IsCenterSplitting X G →
          extendedPairMeasure p α i X.P X.Hm
              {ω | Φ p α i (X.Hm ω - embedPair p i (G ω)) (physicalOrderedEigenvalue p (X.Hm ω) α) ≠
                dysonCenter p i cst α (X.Hm ω - embedPair p i (G ω))
                  (physicalOrderedEigenvalue p (X.Hm ω) α)} ≤
            ENNReal.ofReal (CD * (p.W : ℝ) ^ (-D)))

end BlockBand.Internal.Contracts.Layers
