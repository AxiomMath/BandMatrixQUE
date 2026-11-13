module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Internal.Contracts.Critical

/-!
# Common-port clock comparisons and the regular prior event

Statements comparing ratios and pairs of clocks of the transported common-port probe `Lg` with
those of a standard complex Gaussian vector, when the old self-energy is close to the matched
value; and the regular prior events for the pair and one-block deformations, on which the
deformation lies in `FreshClass` and its Stieltjes transform is close to the matched value.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.ClocksCommonPort

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix BoundedContinuousFunction

/-!
## 0. Vocabulary
-/

/-- The old self-energy of the matched-lead path of length `r` at real energy `e`:
`X = C*(H_path - e)⁻¹C` (`Layers.pathSchur` of `pathAt W r ω`). -/
def leadSchur (e : ℝ) (W r : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  pathSchur e (pathAt W r ω)

/-- Loewner sandwich `-D ⪯ B ⪯ D` on a finite index type. -/
def IsSandwichedOn {ι : Type*} [Fintype ι] (B D : Matrix ι ι ℂ) : Prop :=
  B.IsHermitian ∧ (D - B).PosSemidef ∧ (D + B).PosSemidef

/-- The joint law of the fresh common-port layer and an independent `g ~ CN(0, I_W)`. -/
def commonPortProbeLaw (W : ℕ) (b : ℝ) : Measure (LayerSample W .common × (Fin 1 × Fin W → ℂ)) :=
  (layerLaw W b .common).prod (circularVectorLaw (Fin 1 × Fin W))

/-- The transported probe `Lg ∈ ℂ^{2W}`. -/
def commonPortProbe (b e : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (x : LayerSample W .common × (Fin 1 × Fin W → ℂ)) : Fin 2 × Fin W → ℂ :=
  commonPortL b e X x.1 *ᵥ x.2

/-!
## 1. Common-port ratios
-/

/-- **The common-port ratios theorem** (also used in the physical lead profile theorem).
Fixed first:
`b ∈ (0,1/2)`, the bulk range `bulkInterval κ`, `k` and a continuous
`Φ: [-1,1]^k → ℝ`.
For every `ε > 0` there are `δ₀ > 0` and `W₀`; for `W ≥ W₀`, every Hermitian
old `X` and `e ∈ bulkInterval κ` with `δ = matchedDistance b e X ≤ δ₀`, every old `Y ⪰ 0` with
`Tr Y > 0` and old Hermitian `Y_j` with `-Y ⪯ Y_j ⪯ Y` (no condition-number, norm or rank
assumption), and every measurable default `d`:
`|E_{A,B,g} Φ(g*L*Y_jLg / g*L*YLg) - E_h Φ(h*Y_jh / h*Yh)| ≤ ε`.
-/
def CommonPortRatiosContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (k : ℕ)
    (Φ : C(Fin k → Set.Icc (-1 : ℝ) 1, ℝ)), ∀ ε : ℝ, 0 < ε → ∃ (δ₀ : ℝ) (W₀ : ℕ), 0 < δ₀ ∧
    ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ δ₀ →
    ∀ (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      (Yt : Fin k → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      Y.PosSemidef → 0 < Y.trace.re → (∀ j, IsSandwichedOn (Yt j) Y) →
    ∀ d : (Fin 2 × Fin W → ℂ) → Fin k → ℝ, Measurable d →
      |(∫ x, Φ (ratioCube Yt Y d (commonPortProbe b e X x)) ∂commonPortProbeLaw W b) -
          ∫ h, Φ (ratioCube Yt Y d h) ∂circularVectorLaw (Fin 2 × Fin W)| ≤ ε

/-!
## 2. Common-port parts of the two-positive-clocks lemma and the uniform clock tags
-/

/-- Two positive clocks at the common port.
* `joint`: `|E ψ(g*L*DLg/(γT), g*L*CLg/(γT)) - E_h ψ(h*Dh/T, h*Ch/T)| ≤ ε`;
* `ratio`: `|E Φ(g*L*CLg / g*L*DLg) - E_h Φ(h*Ch / h*Dh)| ≤ ε`.
The old matrices may be any (measurable functions of the) old path: the statement is
conditional on it. -/
structure TwoPositiveClocksCommonPortContract : Prop where
  joint : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ K : ℝ,
    ∀ ψ : (Set.Ici (0 : ℝ) × Set.Ici (0 : ℝ)) →ᵇ ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ (δ₀ : ℝ) (W₀ : ℕ), 0 < δ₀ ∧
    ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ δ₀ →
    ∀ D C : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, D.PosSemidef → C.PosSemidef →
      0 < D.trace.re → C.trace.re ≤ K * D.trace.re →
      let T := D.trace.re
      let γ := commonPortGamma b
      |(∫ x, ψ (clockPair (quadForm D (commonPortProbe b e X x) / (γ * T))
              (quadForm C (commonPortProbe b e X x) / (γ * T))) ∂commonPortProbeLaw W b) -
          ∫ h, ψ (clockPair (quadForm D h / T) (quadForm C h / T))
            ∂circularVectorLaw (Fin 2 × Fin W)| ≤ ε
  ratio : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ K : ℝ,
    ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ, ∀ ε : ℝ, 0 < ε → ∃ (δ₀ : ℝ) (W₀ : ℕ), 0 < δ₀ ∧
    ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ δ₀ →
    ∀ D C : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, D.PosSemidef → C.PosSemidef →
      0 < D.trace.re → C.trace.re ≤ K * D.trace.re →
    ∀ d : (Fin 2 × Fin W → ℂ) → ℝ, Measurable d →
      |(∫ x, Φ (ratioHalfLine C D d (commonPortProbe b e X x)) ∂commonPortProbeLaw W b) -
          ∫ h, Φ (ratioHalfLine C D d h) ∂circularVectorLaw (Fin 2 × Fin W)| ≤ ε

/-- **Uniform clock tags, common-port part** (`a_j = q Tr D_j / Tr D`).
Fixed first: `b`, the bulk range
and `Φ ∈ C_b([0,∞))`.
For every `ε > 0` there are `δ₀ > 0` and `W₀`; for `W ≥ W₀`, Hermitian `X`,
`e ∈ bulkInterval κ` with `δ ≤ δ₀`, every number of tags `q ≥ 1` (which may grow with `W`), every
family of old `D_j ⪰ 0`, `j < q`, with `D = Σ_j D_j` and `Tr D > 0`, and measurable default `d`:
with `J` uniform on the tags and `C = qD_J`,
`|q⁻¹ Σ_j E Φ(q g*L*D_jLg / g*L*DLg) - q⁻¹ Σ_j E_h Φ(q h*D_jh / h*Dh)| ≤ ε`.
-/
def UniformClockTagsCommonPortContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ,
    ∀ ε : ℝ, 0 < ε → ∃ (δ₀ : ℝ) (W₀ : ℕ), 0 < δ₀ ∧
    ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ δ₀ →
    ∀ (q : ℕ), 0 < q → ∀ Dt : Fin q → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      (∀ j, (Dt j).PosSemidef) → 0 < (∑ j, Dt j).trace.re →
    ∀ d : (Fin 2 × Fin W → ℂ) → ℝ, Measurable d →
      |(q : ℝ)⁻¹ * ∑ j, (∫ x, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) d
              (commonPortProbe b e X x)) ∂commonPortProbeLaw W b) -
          (q : ℝ)⁻¹ * ∑ j, ∫ h, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) d h)
            ∂circularVectorLaw (Fin 2 × Fin W)| ≤ ε

/-!
## 3. The regular prior event of the normalizer theorem
-/

/-- The pair deformation `F(e)` reindexed to `Fin (card S)` by a bijection `σ`. -/
def pairDeformation (p : Parameters) (i : ZMod p.n) (σ : PairSite p i ≃ Fin (Fintype.card (PairSite p i)))
    (ω : SplitState p i) (e : ℝ) :
    Matrix (Fin (Fintype.card (PairSite p i))) (Fin (Fintype.card (PairSite p i))) ℂ :=
  Matrix.reindex σ σ (physicalCoareaF ω.1 ω.2.1 ω.2.2 e)

/-- The pair regular event at energy `e`: `F(e)` in `FreshClass` (norm exponent `A`, variance
`s = pairS p`, constants `r₀, s₀, v₀`) and `|m_{F(e),s}(e) - conj(a(e))| ≤ η`. -/
def IsPairRegular (p : Parameters) (i : ZMod p.n)
    (σ : PairSite p i ≃ Fin (Fintype.card (PairSite p i))) (A r₀ s₀ v₀ η e : ℝ)
    (ω : SplitState p i) : Prop :=
  FreshClass (pairDeformation p i σ ω e) A (pairS p) e r₀ s₀ v₀ ∧
    ‖freshDyson (pairDeformation p i σ ω e) (pairS p) e - conj (matchedA e)‖ ≤ η

/-- **Regular prior event, pair form**: the regular event of the proof of the normalizer theorem,
as used in the crossing-sine lemma ("on the same prior regular event used in the normalizer
theorem, `K(E)` has polynomial norm, its fresh free convolution is regular on a fixed
energy/variance rectangle, and its density at zero tends to `ρ`") and to apply
`GaussianRatiosContract`, `TwoPositiveClocksPalmContract`, `UniformClockTagsPalmContract` to
physical exteriors. Fixed first: `b ∈ (0,1/2)`, the bulk
range `bulkInterval κ` and `T`.
Then there are regularity constants `r₀, s₀, v₀` with
`FreshConstants (pairS) r₀ s₀ v₀` for every admissible `p` with this `b` (`s = min(b,c)` depends
on `b` only); for every `D > 0` a norm exponent `A`; for every `η > 0` a width `W₀`: for
`W ≥ W₀`, `4 ≤ n ≤ TW`, every model, adjacent pair, splitting law `Pω` (at `s = pairS p`),
reindexing `σ` and deterministic `e ∈ bulkInterval κ`, the exterior prior probability that the
pair regular event fails is at most `W^{-D}`.
-/
def PairRegularEventContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ r₀ s₀ v₀ : ℝ, FreshConstants (min b (1 - 2 * b)) r₀ s₀ v₀ ∧
    ∀ D : ℝ, 0 < D → ∃ A : ℝ, ∀ η : ℝ, 0 < η → ∃ W₀ : ℕ,
    ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
      IsPairSplitting p i model (pairS p) Pω →
    ∀ (σ : PairSite p i ≃ Fin (Fintype.card (PairSite p i))), ∀ e ∈ bulkInterval κ,
      Pω {ω | ¬ IsPairRegular p i σ A r₀ s₀ v₀ η e ω} ≤ ENNReal.ofReal ((p.W : ℝ) ^ (-D))

/-- The one-block deformation `F(e) = -C*(H_R - e)⁻¹C` reindexed by a bijection `σ`. -/
def blockDeformation (p : Parameters) (k : ZMod p.n)
    (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (ω : BlockState p k) (e : ℝ) :
    Matrix (Fin (Fintype.card (BlockSite p k))) (Fin (Fintype.card (BlockSite p k))) ℂ :=
  Matrix.reindex σ σ (blockF p k ω e)

/-- The one-block regular event: `F(e)` in `FreshClass` at variance `c = 1 - 2b` and
`|m_{F(e),c}(e) - conj(a(e))| ≤ η`. -/
def IsBlockRegular (p : Parameters) (k : ZMod p.n)
    (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (A r₀ s₀ v₀ η e : ℝ)
    (ω : BlockState p k) : Prop :=
  FreshClass (blockDeformation p k σ ω e) A p.c e r₀ s₀ v₀ ∧
    ‖freshDyson (blockDeformation p k σ ω e) p.c e - conj (matchedA e)‖ ≤ η

/-- **Regular prior event, one-block form** (from the one-block normalizer proof, with the
matched-traces theorem and the regularity certificate supplying the regular deformation and
polynomial tails), as used in the microscopic tag comparison ("the good event of the
deformation is exactly the one in the proof of the one-block coarea formula; its complement has
vanishing physical mass"). Quantifiers as in `PairRegularEventContract`, with the fresh
block variance `c = 1 - 2b`, `N = W`, the one-block splitting law and any block `k`.
-/
def BlockRegularEventContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ r₀ s₀ v₀ : ℝ, FreshConstants (1 - 2 * b) r₀ s₀ v₀ ∧
    ∀ D : ℝ, 0 < D → ∃ A : ℝ, ∀ η : ℝ, 0 < η → ∃ W₀ : ℕ,
    ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (Pω : Measure (BlockState p k)),
      IsBlockSplitting p k model Pω →
    ∀ (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))), ∀ e ∈ bulkInterval κ,
      Pω {ω | ¬ IsBlockRegular p k σ A r₀ s₀ v₀ η e ω} ≤ ENNReal.ofReal ((p.W : ℝ) ^ (-D))

end BlockBand.Internal.Contracts.ClocksCommonPort
