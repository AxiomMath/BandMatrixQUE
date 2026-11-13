module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Asymptotics.CriticalSequence

/-!
# Definitions for strong local mass flatness

The statement (`LocalMassFlatStatement`). Law: the exact physical law `model.law` of the
original periodic matrix (`GaussianRingModel`), ranks with multiplicity, raw eigenvalues
`λ_α = physicalOrderedEigenvalue`, `u_α = Nρ(E)(λ_α - E)` (`Clocks.microCoord`), block masses
`p_{αk} = ‖P_kψ_α‖² = physicalOrderedBlockMass`, pair masses `‖P_Sψ_α‖² = CoareaPalm.pairMass`
for the adjacent pair `S = {i, i+1}`. Quantifier order: `0 < b < 1/2`, a bulk energy
`-2 < E < 2` and `T₀ > 0` first; then one constant `C = C_{b,E,T₀}`; then every window
`w` (smooth, `IsWindow`: continuous, compactly supported, `w ≥ 0`, `∫ w = 1`), every
`τ ∈ (0, T₀]`, every critical sequence `n/W → τ` (`CriticalSequence`, `W → ∞`), every sequence
of exact models and every sequence of pairs/blocks `i_j` (so in particular every fixed pair).
`limsup_j a_j ≤ C√τ` is written `∀ ε > 0, ∀ᶠ j, a_j ≤ C√τ + ε`.

* `LmfMicroscopicTagComparison`: the microscopic tag comparison, in the same form as
  `MicroscopicTagComparisonStatement` (the defining bodies of `lmf_tagClock`, `lmf_meanClock`,
  `lmf_pathTagExpect`, `lmf_physicalTagSide`, `lmf_pathTagSide` are identical to those of
  `tagClock`, `meanClock`, `pathTagExpect`, `physicalTagSide`, `pathTagSide`, so the two
  propositions are definitionally equal).
* `LmfTaggedFlat`: the averaged tagged flat clause and the `M_W` clause of the tagged convex order
  theorem, in the energy-uniform reading required by the proof of local mass flatness (the
  positive and negative limiting moment bounds are uniform for the energies `e(u)` in the compact
  window); see its docstring.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped BoundedContinuousFunction ENNReal

/-!
## The matched-lead clocks of the microscopic tag comparison
-/

/-- `h*Y^{int}h = Σ_{j<r} ‖P_jUh‖²`, the interior clock of the matched-lead path. -/
def lmf_interiorLeadMass (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  ∑ i : Fin r, leadPositionMass b e W r x.1 x.2 (Sum.inl i)

/-- `Z_{r;K} = W⁻¹ h*Y_{r;K}h` (matched-lead path, interior position `K`). -/
def lmf_tagClock (b e : ℝ) (W r : ℕ) (K : Fin r) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    ℝ :=
  (W : ℝ)⁻¹ * leadPositionMass b e W r x.1 x.2 (Sum.inl K)

/-- `M_r = (rW)⁻¹ h*Y^{int}h`. -/
def lmf_meanClock (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  ((r : ℝ) * W)⁻¹ * lmf_interiorLeadMass b e W r x

/-- `E_{path,h,K} Φ(Z_{r;K}/M_r)` at real energy `e`: path prior `growthPathLaw W b`,
independent `h ~ CN(0, I_{2W})`, `K` uniform on the `r` interior positions. -/
def lmf_pathTagExpect (b e : ℝ) (W r : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) : ℝ :=
  ∫ x, (r : ℝ)⁻¹ * ∑ K : Fin r,
      Φ (Set.projIci 0 (lmf_tagClock b e W r K x / lmf_meanClock b e W r x))
    ∂probedClockLaw W b

/-- The physical side `E Σ_α w(u_α) Φ(n p_{αk})`, exact physical law. -/
def lmf_physicalTagSide (p : Parameters) (model : p.GaussianRingModel) (E : ℝ) (w : ℝ → ℝ)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (k : ZMod p.n) : ℝ :=
  ∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      Φ (Set.projIci 0 ((p.n : ℝ) * physicalOrderedBlockMass p H α k))
    ∂(model.law : Measure p.SiteMatrix)

/-- The path side `∫ w(u) E_{path,h,K} Φ(Z_{r;K}/M_r)(e(u)) du`, `r = n - 3`. -/
def lmf_pathTagSide (p : Parameters) (E : ℝ) (w : ℝ → ℝ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) : ℝ :=
  ∫ u, w u * lmf_pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) Φ

/-- **Hypothesis:
Law: the exact physical law on the left; on the right the independent
matched-lead path prior `growthPathLaw W b` (path of `r = n - 3` blocks, two matched auxiliary
leads), independent `h ~ CN(0, I_{2W})`, independent uniform `K`.
Fixed first:
`0 < b < 1/2`,
the bulk energy `-2 < E < 2`, a smooth compactly supported (possibly signed) `w`,
`Φ ∈ C_b([0,∞))`, then `τ > 0`, a critical sequence `n_j/W_j → τ` and models.
Conclusion:
for every `ε > 0`, eventually in `j`, **for every** block `k` (uniformity in the physical tag),
`|E Σ_α w(u_α)Φ(n p_{αk}) - ∫ w(u) E Φ(Z_{r;K}/M_r)(e(u)) du| ≤ ε`, `e(u) = E + u/(Nρ(E))`.
Definitionally equal to `MicroscopicTagComparisonStatement` (Sine/MicroscopicTagDefs).
-/
def LmfMicroscopicTagComparison : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ w : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w → HasCompactSupport w →
    ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ, ∀ τ : ℝ, 0 < τ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel),
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ k : ZMod (s.parameters b hb hb' j).n,
        |lmf_physicalTagSide (s.parameters b hb hb' j) (R j) E w Φ k -
            lmf_pathTagSide (s.parameters b hb hb' j) E w Φ| ≤ ε

/-!
## The tagged clocks of the tagged convex order theorem
-/

/-- `Z_{n;k} = h*Q_{n;k}h = W⁻¹ h*Y_{n;k}h`, `Y_{n;k} = 𝒰_n*P_k𝒰_n` the
`tagResponse` at real energy `e` (birth index `k`), on the
probed path `(ω, h)`, `h ~ CN(0, I_{2W})`.
-/
def lmf_tagResponseClock (b e : ℝ) (W n k : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  (W : ℝ)⁻¹ * BlockBand.Internal.Contracts.CoareaPalm.quadForm (tagResponse b e W n k x.1) x.2

/-- **The averaged clause of the tagged convex order theorem** (the tagged flat bound, and the
same bound for `M_W = n⁻¹Σ_k Z_{n;k} = T_W/τ_W`), taken here as a hypothesis.
Law: the near-end-grown path `growthPathLaw W b` of length `n` (the Gaussian path) with an
independent `h ~ CN(0, I_{2W})` (`probedClockLaw`); `Z_{n;k}` is `lmf_tagResponseClock`, `M_W`
is `rescaledClock` (`h*Yh/(nW)`, `Y = Σ_k Y_{n;k}`), `d = d_* = 1/(1-b)` (`dStar`).
Quantifiers:
`b`, bulk `E`, `T₀` and the positive integer `p` first; then
`C = C_{p,T₀}` (also depending on `b, E`); for every `τ ∈ (0,T₀]` and every `ClockSequence`
(`W_j → ∞`, `n_j/W_j → τ`, energies `E_j → E`):
`limsup_j n⁻¹ Σ_{k<n} E|Z_{n;k} - d|^{2p} ≤ Cτ^p` and `limsup_j E|M_W - d|^{2p} ≤ Cτ^p`
(lower integrals in `ℝ≥0∞`, so no integrability is presupposed).

*Energy uniformity.* The paper states it at the fixed energy `E`. The proof of the local mass
flatness theorem applies it at the moving energies `e(u) = E + u/(Nρ(E)) → E` and asserts that
"the positive and negative limiting moment bounds are uniform for the energies `e(u)` in the
compact window"; this hypothesis is that energy-uniform reading (as `ClockSequence` is for the
negative clock theorem and the clock small-ball lemma). It is proved from the energy-uniform
contracts as `lmfTaggedFlat_of_uniformContracts`.
The convex-order and moment-convergence clauses of the label are
not used and not stated.
-/
def LmfTaggedFlat : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ T₀ : ℝ, 0 < T₀ →
    ∀ p : ℕ, 0 < p → ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ s : ClockSequence τ E,
      limsup (fun j => ((s.n j : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range (s.n j),
          ∫⁻ x, ENNReal.ofReal
              (|lmf_tagResponseClock b (s.energy j) (s.W j) (s.n j) k x - dStar b| ^ (2 * p))
            ∂probedClockLaw (s.W j) b) atTop ≤ ENNReal.ofReal (C * τ ^ p) ∧
      limsup (fun j => ∫⁻ x, ENNReal.ofReal (|rescaledClock b s j x - dStar b| ^ (2 * p))
          ∂probedClockLaw (s.W j) b) atTop ≤ ENNReal.ofReal (C * τ ^ p)

/-!
## The statement of local mass flatness
-/

/-- `E Σ_α w(u_α) |n‖P_kψ_α‖² - 1|` (one block `k`), exact physical law. -/
def lmf_blockFlatness (p : Parameters) (model : p.GaussianRingModel) (E : ℝ) (w : ℝ → ℝ)
    (k : ZMod p.n) : ℝ :=
  ∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      |(p.n : ℝ) * physicalOrderedBlockMass p H α k - 1|
    ∂(model.law : Measure p.SiteMatrix)

/-- `E Σ_α w(u_α) |(n/2)‖P_Sψ_α‖² - 1|` for the adjacent pair `S = {i, i+1}`. -/
def lmf_pairFlatness (p : Parameters) (model : p.GaussianRingModel) (E : ℝ) (w : ℝ → ℝ)
    (i : ZMod p.n) : ℝ :=
  ∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      |(p.n : ℝ) / 2 * BlockBand.Internal.Contracts.CoareaPalm.pairMass p i α H - 1|
    ∂(model.law : Measure p.SiteMatrix)

/-- Strong local mass flatness. For the original periodic matrix (exact law `model.law`), fixed
first `0 < b < 1/2`, a bulk energy `-2 < E < 2` and `T₀ > 0`; then one constant `C = C_{b,E,T₀}`;
for every smooth window `w` (`IsWindow`: `w ≥ 0` continuous, compactly supported, `∫ w = 1`),
every `τ ∈ (0,T₀]`, every critical sequence `n/W → τ`, models, and adjacent pairs
`S = {i_j, i_j+1}`: `limsup E Σ_α w(u_α)|(n/2)‖P_Sψ_α‖² - 1| ≤ C√τ`, and the same for one block
`limsup E Σ_α w(u_α)|n‖P_kψ_α‖² - 1| ≤ C√τ` (`k = i_j`), written with `∀ ε > 0, ∀ᶠ j`. -/
def LocalMassFlatStatement : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 → ∀ T₀ : ℝ, 0 < T₀ →
    ∃ C : ℝ, ∀ w : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w → IsWindow w →
    ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
      (i : ∀ j, ZMod (s.parameters b hb hb' j).n),
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        lmf_pairFlatness (s.parameters b hb hb' j) (R j) E w (i j) ≤ C * Real.sqrt τ + ε ∧
        lmf_blockFlatness (s.parameters b hb hb' j) (R j) E w (i j) ≤ C * Real.sqrt τ + ε

end BlockBand.Endpoints
