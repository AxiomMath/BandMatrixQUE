module

public import BlockBand.Internal.Contracts.Inputs

/-!
# The physical ring and direct sums of rings as block models

The physical ring matrix in row-major block coordinates, split into its diagonal blocks and its
bond part, and the direct sum of ring matrices of common width, each presented as a
`BlockModel` for the projected Wegner lemma.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.InputsRing

open MeasureTheory
open BlockBand.Internal.Contracts.Inputs

/-- Row-major block coordinates of the physical sites. -/
def siteBlockEquiv (p : Parameters) : p.Site ≃ Fin p.n × Fin p.W :=
  (ZMod.finEquiv p.n).symm.toEquiv.prodCongr (Equiv.refl _)

/-- A physical site matrix in block coordinates. -/
def toBlockCoords (p : Parameters) (H : p.SiteMatrix) :
    Matrix (Fin p.n × Fin p.W) (Fin p.n × Fin p.W) ℂ :=
  H.submatrix (siteBlockEquiv p).symm (siteBlockEquiv p).symm

/-- The diagonal blocks `H_jj` of a block-coordinate matrix. -/
def diagonalBlocks {k W : ℕ} (X : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) :
    Fin k → Matrix (Fin W) (Fin W) ℂ :=
  fun j a b => X (j, a) (j, b)

/-- The off-diagonal-block (bond) part of a block-coordinate matrix. -/
def offDiagonalBlocks {k W : ℕ} (X : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  fun x y => if x.1 = y.1 then 0 else X x y

/-- A `BlockModel` presents a law on block-coordinate matrices: `Y = 0`, `A` are the diagonal
blocks and `D` the off-diagonal part of one random matrix whose joint law of
(diagonal blocks, off-diagonal part) is the push-forward of `μ`. Since `H = D + ⊕ A_j`, the law
of `M.H` is then the law of that matrix. -/
def Presents {k W : ℕ} (M : BlockModel k W)
    (μ : Measure (Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)) : Prop :=
  (∀ w, M.Y w = 0) ∧
    M.P.map (fun w => (M.A w, M.D w)) = μ.map (fun X => (diagonalBlocks X, offDiagonalBlocks X)) ∧
    M.P.map M.H = μ

/-- The ring as a `BlockModel`: for every admissible parameter set and
realization of the physical law there is a `BlockModel p.n p.W` with independent
`GUE_W(c/W)` diagonal blocks, bonds independent of them, `Y = 0`, presenting the physical law
in block coordinates.
-/
def RingAsBlockModel : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel), ∃ M : BlockModel p.n p.W,
    M.IsIndependent p.c ∧
      Presents M ((model.law : Measure p.SiteMatrix).map (toBlockCoords p))

/-- Parameters of a ring with `n ≥ 4` blocks, width `W ≥ 1` and bond `b ∈ (0,1/2)`. -/
def ringParameters (n W : ℕ) (b : ℝ) (hn : 4 ≤ n) (hW : 0 < W) (hb : 0 < b) (hb' : b < 1 / 2) :
    Parameters :=
  ⟨n, W, b, hn, hW, hb, hb'⟩

/-- The direct sum `⊕ᵢ Hᵢ` of ring matrices with common width, in block coordinates on
`Fin (Σᵢ nᵢ) × Fin W` (blocks ordered by `finSigmaFinEquiv`). -/
def directSumBlockCoords {r W : ℕ} (n : Fin r → ℕ)
    (H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ) :
    Matrix (Fin (∑ i, n i) × Fin W) (Fin (∑ i, n i) × Fin W) ℂ :=
  fun x y =>
    let u := finSigmaFinEquiv.symm x.1
    let v := finSigmaFinEquiv.symm y.1
    if h : u.1 = v.1 then H u.1 (u.2, x.2) (Fin.cast (by rw [h]) v.2, y.2) else 0

/-- A finite direct sum of independent physical rings as a `BlockModel`:
for `r` rings with block numbers `nᵢ ≥ 4`, common width `W ≥ 1` and common bond `b`, and any
realizations of their physical laws, there is a `BlockModel (Σᵢ nᵢ) W` with independent
`GUE_W(c/W)` blocks (`c = 1 - 2b`), bonds independent of them, `Y = 0`, presenting the law of
`⊕ᵢ Hᵢ` with the `Hᵢ` independent (product of the ring laws).
-/
def RingSumAsBlockModel : Prop :=
  ∀ (r W : ℕ) (n : Fin r → ℕ) (b : ℝ) (hn : ∀ i, 4 ≤ n i) (hW : 0 < W) (hb : 0 < b)
    (hb' : b < 1 / 2)
    (models : ∀ i, (ringParameters (n i) W b (hn i) hW hb hb').GaussianRingModel),
    ∃ M : BlockModel (∑ i, n i) W,
      M.IsIndependent (1 - 2 * b) ∧
        Presents M ((Measure.pi (fun i => ((models i).law :
            Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))).map
          (fun H => directSumBlockCoords n
            (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i))))

/-- Both presentations. -/
def RingBlockModels : Prop := RingAsBlockModel ∧ RingSumAsBlockModel

end BlockBand.Internal.Contracts.InputsRing
