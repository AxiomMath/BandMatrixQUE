module

public import BlockBand.Internal.Contracts.ClocksCommonPort

/-!
# Facts behind the physical lead-profile theorem

The decomposition of the ring around a block `k` into a matched-lead path and a common-port
layer, the identification of the Gaussian field at block `k`, and the relative Loewner closeness
of its covariance to the matched covariance.

## Conventions

* **The decomposition around block `k`** (in the paper, for block `0`).
  - The path's near port `0`, coupled to position `0`, is neighbour `k+1`; its far port `1`,
    coupled to position `r-1`, is neighbour `k-1`. This is the convention of `Clocks.leadRingBlock`
    rotated by `k`.
  - `leadPos` maps every off-block site to its lead coordinate in `FullSite W r`. `leadExterior`
    assembles the exterior `ω = (H_R, C)` of block `k` (`Clocks.BlockState`) from a path sample
    and a layer sample, in that position map.
* **Field and covariance**.
  - With `Σ = C*(H_R - e)⁻¹C` we have `Clocks.blockF = -Σ`, so `z₀ - Σ = commonZ b e • 1 + blockF`,
    where `z₀ = commonZ b e = -e - ca`.
  - The matched covariance is `c|z₀ - Σ|^{-2} = c((z₀-Σ)*(z₀-Σ))⁻¹` (`blockMatchedGamma`). The
    field factor is `M = √c (z₀ - Σ)⁻¹` (`blockFieldFactor`). For `g ~ CN(0, I_W)`, `Mg` has
    covariance `MM* = c|z₀ - Σ|^{-2}`.
  - The Schur lift `blockLift ω e (Mg)/√c` is the block-`k` column of `G_abs`. Split into block
    `k` and the old positions, it is `(Hg, U L g)`, with:
    - `H = Critical.commonPortH` and `L = Critical.commonPortL` at the old self-energy
      `X = ClocksCommonPort.leadSchur e W r ω_path`;
    - `U = Clocks.leadResponse = JR`, the port columns of the matched-lead inverse.
* **Inverses.** The identity is stated for samples where the five relevant matrices are
  invertible. Lean's totalized inverse is `0` on singular matrices.
  - The `regular_ae` clause asserts that this holds almost surely under the product law, for every
    bulk energy `e ∈ (-2,2)`.
  - The five matrices are `H_path - e`, `A - e - X`, `H_R - e`, `z₀ - Σ` and `z_b - X`.
* **In probability**. "Relative Loewner error `o(1)`" is read as: for every `ε > 0`, the
  exterior prior probability that `(1-ε)Γ₀ ⪯ Γ ⪯ (1+ε)Γ₀` fails is at most `ε` once `W ≥ W₀`.
  - `W₀` is uniform in `4 ≤ n ≤ TW`, the models, the block `k`, the splitting laws, the reindexing
    `σ` and the deterministic `e ∈ bulkInterval κ`.
  - The measure of a possibly non-measurable event is its outer measure.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.ClocksLeadProfile

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix

/-!
## 1. The decomposition around block `k`
-/

section Decomposition

variable (p : Parameters) (k : ZMod p.n)

/-- The lead coordinate of an off-block site: relative block `1` is the near port `0`, relative
block `n-1` is the far port `1`, and relative block `2 + i` is path position `i`. -/
def leadPos (x : OffBlockSite p k) : FullSite p.W (p.n - 3) :=
  let rel := (x.1.1 - k).val
  if rel = 1 then Sum.inr ((0 : Fin 2), x.1.2)
  else if rel = p.n - 1 then Sum.inr ((1 : Fin 2), x.1.2)
  else Sum.inl (⟨min (rel - 2) (p.n - 3 - 1), by have := p.n_ge_four; omega⟩, x.1.2)

/-- The exterior matrix in lead coordinates: the path of `r = n - 3` blocks, its couplings to
the two neighbours, and the neighbour diagonals `A₁, A₂` (no energy shift). -/
def leadExteriorMatrix (ωp : GrowthPath p.W) (ωl : LayerSample p.W .common) :
    Matrix (FullSite p.W (p.n - 3)) (FullSite p.W (p.n - 3)) ℂ :=
  Matrix.fromBlocks (pathMatrix (pathAt p.W (p.n - 3) ωp))
    (pathPortCoupling (pathAt p.W (p.n - 3) ωp))
    (pathPortCoupling (pathAt p.W (p.n - 3) ωp))ᴴ (blockDiag ωl.1)

/-- The coupling of the exterior to block `k`, in lead coordinates: only the two neighbours are
coupled, through `B`. -/
def leadExteriorCoupling (ωl : LayerSample p.W .common) :
    Matrix (FullSite p.W (p.n - 3)) (Fin 1 × Fin p.W) ℂ :=
  fun u v => match u with
    | Sum.inl _ => 0
    | Sum.inr y => bondMatrix .common ωl.2 y v

/-- The exterior `ω = (H_R, C)` of block `k` assembled from a path sample and a common-port
layer sample. -/
def leadExterior (x : GrowthPath p.W × LayerSample p.W .common) : BlockState p k :=
  (fun a c => leadExteriorMatrix p x.1 x.2 (leadPos p k a) (leadPos p k c),
   fun a y => leadExteriorCoupling p x.2 (leadPos p k a) ((0 : Fin 1), y.1.2))

/-- A block-`k` vector read on the common port `Fin 1 × Fin W`. -/
def blockPortVector (g : BlockSite p k → ℂ) : Fin 1 × Fin p.W → ℂ :=
  fun i => g ⟨(k, i.2), rfl⟩

end Decomposition

/-!
## 2. The matched covariance and the field factor
-/

/-- `z₀ - Σ = commonZ b e • 1 + blockF` (since `blockF = -Σ`). -/
def blockShifted (p : Parameters) (k : ZMod p.n) (ω : BlockState p k) (e : ℝ) :
    Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  commonZ p.b e • (1 : Matrix (BlockSite p k) (BlockSite p k) ℂ) + blockF p k ω e

/-- The matched covariance `c|z₀ - Σ|^{-2} = c((z₀-Σ)*(z₀-Σ))⁻¹`. -/
def blockMatchedGamma (p : Parameters) (k : ZMod p.n) (ω : BlockState p k) (e : ℝ) :
    Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  (p.c : ℂ) • ((blockShifted p k ω e)ᴴ * blockShifted p k ω e)⁻¹

/-- The field factor `M = √c (z₀ - Σ)⁻¹`. -/
def blockFieldFactor (p : Parameters) (k : ZMod p.n) (ω : BlockState p k) (e : ℝ) :
    Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  ((Real.sqrt p.c : ℝ) : ℂ) • (blockShifted p k ω e)⁻¹

/-- The five matrices that must be invertible (determinant nonzero): `H_path - e`, `A - e - X`, `H_R - e`,
`z₀ - Σ` and `z_b - X`. -/
def IsLeadRegular (p : Parameters) (k : ZMod p.n) (e : ℝ)
    (x : GrowthPath p.W × LayerSample p.W .common) : Prop :=
  let X := leadSchur e p.W (p.n - 3) x.1
  (pathMatrix (pathAt p.W (p.n - 3) x.1) - (e : ℂ) • 1).det ≠ 0 ∧
    (blockDiag x.2.1 - (e : ℂ) • 1 - X).det ≠ 0 ∧
    ((leadExterior p k x).1 - (e : ℂ) • 1).det ≠ 0 ∧
    (blockShifted p k (leadExterior p k x) e).det ≠ 0 ∧
    (matchedLeadK p.b e X).det ≠ 0

/-!
## 3. The identification of the Gaussian field
-/

/-- The identification of the Gaussian field at block `k`.
* `law`: for every admissible `p`, model and block `k`, every one-block splitting law `Pω` of
  block `k` is the image of `growthPathLaw W b ⊗ layerLaw W b .common` under `leadExterior p k`.
  The path and the fresh neighbour layer are independent with their original Gaussian laws, and
  this is the exterior prior.
* `regular_ae`: for every bulk energy `-2 < e < 2`, the five relevant matrices are invertible for
  almost every sample.
* `identity`: on such a sample, for every block-`k` vector `g` and every ring site `y`,
  `blockLift ω e ((z₀ - Σ)⁻¹ g)` equals:
  - `(H g)` at block `k`;
  - `(U L g)` at the lead coordinate of `y` otherwise.

  Here `ω = leadExterior p k x`, `H = commonPortH`, `L = commonPortL` at `X = leadSchur e W r x.1`,
  and `U = leadResponse`.
* `covariance`: if `z₀ - Σ` is invertible, `MM* = c|z₀ - Σ|^{-2}` for `M = blockFieldFactor`.

It is proved as `leadFieldIdentification_holds`. -/
structure LeadFieldIdentificationContract : Prop where
  law : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n)
    (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
      Pω = ((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)).map (leadExterior p k)
  regular_ae : ∀ (p : Parameters) (k : ZMod p.n) (e : ℝ), -2 < e → e < 2 →
    ∀ᵐ x ∂((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)), IsLeadRegular p k e x
  identity : ∀ (p : Parameters) (k : ZMod p.n) (e : ℝ)
    (x : GrowthPath p.W × LayerSample p.W .common), IsLeadRegular p k e x →
    ∀ (g : BlockSite p k → ℂ) (y : p.Site),
      let X := leadSchur e p.W (p.n - 3) x.1
      blockLift p k (leadExterior p k x) e ((blockShifted p k (leadExterior p k x) e)⁻¹ *ᵥ g) y =
        if hy : y.1 = k then (commonPortH p.b e X x.2 *ᵥ blockPortVector p k g) ((0 : Fin 1), y.2)
        else ((leadResponse p.b e p.W (p.n - 3) x.1 * commonPortL p.b e X x.2) *ᵥ
          blockPortVector p k g) (leadPos p k ⟨y, hy⟩)
  covariance : ∀ (p : Parameters) (k : ZMod p.n) (ω : BlockState p k) (e : ℝ),
    (blockShifted p k ω e).det ≠ 0 →
      blockFieldFactor p k ω e * (blockFieldFactor p k ω e)ᴴ = blockMatchedGamma p k ω e

/-!
## 4. Relative Loewner closeness in probability
-/

/-- Relative Loewner closeness of the block covariance to the matched covariance.
* Fixed first: `b ∈ (0,1/2)`, the bulk range `bulkInterval κ` and `T`.
* Then for every `ε > 0` there is `W₀` such that the following holds for `W ≥ W₀`, `4 ≤ n ≤ TW`,
  every model, block `k`, one-block splitting law `Pω`, reindexing `σ` and deterministic
  `e ∈ bulkInterval κ`.
* The `Pω`-probability that `(1-ε)Γ₀ ⪯ Γ ⪯ (1+ε)Γ₀` fails is at most `ε`, where
  `Γ = freshGamma (blockDeformation σ ω e) c e` and `Γ₀ = reindex σ σ (c|z₀ - Σ|^{-2})`. -/
def BlockGammaClosenessContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ,
    ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (Pω : Measure (BlockState p k)),
      IsBlockSplitting p k model Pω →
    ∀ (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))), ∀ e ∈ bulkInterval κ,
      Pω {ω | ¬ ((((1 + ε : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p k ω e) -
              freshGamma (blockDeformation p k σ ω e) p.c e).PosSemidef ∧
            (freshGamma (blockDeformation p k σ ω e) p.c e -
              ((1 - ε : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p k ω e)).PosSemidef)} ≤
        ENNReal.ofReal ε

end BlockBand.Internal.Contracts.ClocksLeadProfile
