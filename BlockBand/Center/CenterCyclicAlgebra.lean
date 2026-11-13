module

public import BlockBand.Center.PhysicalCenter

/-!
# Equivariance of the Dyson center under the cyclic block shift

For edges `g, g'` let `τ = siteReindexMatrix (cyclicSiteEquiv (g - g'))`, `(τH)_{xy} =
H_{x + (g-g'), y + (g-g')}` (block coordinates shifted), and `e : S_{g'} ≃ S_g`, `x ↦ x + (g-g')`
(`ccyPairEquiv`). Then `τ` carries the pair `S_g` to `S_{g'}`:

* `ccy_shift_embed`: `τ(embed_g G) = embed_{g'}(G ∘ (e × e))`; `ccy_shift_projector`:
  `τ P_{S_g} = P_{S_{g'}}`;
* `ccy_compressed`: `ℛ_{g'}(τH^{(g)}) = ℛ_g(H^{(g)}) ∘ (e × e)` (inverse of a reindexed matrix);
* `ccy_centerResidual`, `ccy_isDysonRoot`, `ccy_dysonRoot`, `ccy_centerFormula`,
  `ccy_inCenterDomain`, and **`ccy_dysonCenter`**: `j_{g'}(τH^{(g)}, E) = j_g(H^{(g)}, E)` for every
  residual matrix, energy, rank and domain constants (no Hermitian hypothesis needed).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate

variable {p : Parameters}

/-!
## 1. The shift of the pair sites
-/

theorem ccy_eq_iff {g g' k : ZMod p.n} : k + (g - g') = g ↔ k = g' := by
  constructor
  · intro h; linear_combination h
  · intro h; rw [h]; abel

theorem ccy_eq_succ_iff {g g' k : ZMod p.n} : k + (g - g') = g + 1 ↔ k = g' + 1 := by
  constructor
  · intro h; linear_combination h
  · intro h; rw [h]; abel

theorem ccy_mem_iff {g g' k : ZMod p.n} :
    (k + (g - g') = g ∨ k + (g - g') = g + 1) ↔ (k = g' ∨ k = g' + 1) := by
  rw [ccy_eq_iff, ccy_eq_succ_iff]

theorem ccy_mem_bwd {g g' k : ZMod p.n} (h : k = g ∨ k = g + 1) :
    k - (g - g') = g' ∨ k - (g - g') = g' + 1 := by
  have : k - (g - g') + (g - g') = k := sub_add_cancel _ _
  rw [← ccy_mem_iff (g := g), this]
  exact h

/-- The pair-site bijection `S_{g'} ≃ S_g`, `x ↦ x + (g - g')` on the block coordinate. -/
def ccyPairEquiv (g g' : ZMod p.n) : PairSite p g' ≃ PairSite p g where
  toFun x := ⟨p.cyclicSiteEquiv (g - g') x.1, ccy_mem_iff.mpr x.2⟩
  invFun x := ⟨(p.cyclicSiteEquiv (g - g')).symm x.1, ccy_mem_bwd x.2⟩
  left_inv x := Subtype.ext ((p.cyclicSiteEquiv (g - g')).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((p.cyclicSiteEquiv (g - g')).apply_symm_apply x.1)

theorem ccy_pairEquiv_val (g g' : ZMod p.n) (x : PairSite p g') :
    ((ccyPairEquiv g g' x : PairSite p g) : p.Site) = p.cyclicSiteEquiv (g - g') x.1 := rfl

/-- Transport of a pair matrix from `S_g` to `S_{g'}`. -/
def ccyPairShift (g g' : ZMod p.n) (G : PairMatrix p g) : PairMatrix p g' :=
  G.submatrix (ccyPairEquiv g g') (ccyPairEquiv g g')

/-- The block shift of site matrices carrying edge `g` to edge `g'`. -/
abbrev ccyShift (g g' : ZMod p.n) (H : p.SiteMatrix) : p.SiteMatrix :=
  p.siteReindexMatrix (p.cyclicSiteEquiv (g - g')) H

theorem ccy_shift_eq_submatrix (g g' : ZMod p.n) (H : p.SiteMatrix) :
    ccyShift g g' H = H.submatrix (p.cyclicSiteEquiv (g - g')) (p.cyclicSiteEquiv (g - g')) := rfl

/-!
## 2. Shift of the pair objects
-/

theorem ccy_shift_sub (g g' : ZMod p.n) (A B : p.SiteMatrix) :
    ccyShift g g' (A - B) = ccyShift g g' A - ccyShift g g' B := rfl

theorem ccy_shift_isHermitian_iff (g g' : ZMod p.n) (H : p.SiteMatrix) :
    (ccyShift g g' H).IsHermitian ↔ H.IsHermitian := by
  rw [ccy_shift_eq_submatrix]
  constructor
  · intro h
    have h2 := h.submatrix (p.cyclicSiteEquiv (g - g')).symm
    rw [Matrix.submatrix_submatrix] at h2
    simpa using h2
  · intro h
    exact h.submatrix _

theorem ccy_shift_embed (g g' : ZMod p.n) (G : PairMatrix p g) :
    ccyShift g g' (embedPair p g G) = embedPair p g' (ccyPairShift g g' G) := by
  ext x y
  simp only [ccyShift, Parameters.siteReindexMatrix]
  unfold embedPair ccyPairShift
  by_cases hx : x.1 = g' ∨ x.1 = g' + 1
  · have hx' : (p.cyclicSiteEquiv (g - g') x).1 = g ∨ (p.cyclicSiteEquiv (g - g') x).1 = g + 1 :=
      ccy_mem_iff.mpr hx
    rw [dite_eq_left hx, dite_eq_left hx']
    by_cases hy : y.1 = g' ∨ y.1 = g' + 1
    · have hy' : (p.cyclicSiteEquiv (g - g') y).1 = g ∨ (p.cyclicSiteEquiv (g - g') y).1 = g + 1 :=
        ccy_mem_iff.mpr hy
      rw [dite_eq_left hy, dite_eq_left hy']
      rfl
    · have hy' : ¬ ((p.cyclicSiteEquiv (g - g') y).1 = g ∨
          (p.cyclicSiteEquiv (g - g') y).1 = g + 1) := fun h => hy (ccy_mem_iff.mp h)
      rw [dite_eq_right hy, dite_eq_right hy']
  · have hx' : ¬ ((p.cyclicSiteEquiv (g - g') x).1 = g ∨
        (p.cyclicSiteEquiv (g - g') x).1 = g + 1) := fun h => hx (ccy_mem_iff.mp h)
    rw [dite_eq_right hx, dite_eq_right hx']

theorem ccy_shift_projector (g g' : ZMod p.n) :
    ccyShift g g' (pairProjector p g) = pairProjector p g' := by
  rw [ccy_shift_eq_submatrix]
  unfold pairProjector
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  simp only [Function.comp_apply]
  exact if_congr (ccy_mem_iff (g := g) (g' := g') (k := x.1)) rfl rfl

theorem ccy_shift_full (g g' : ZMod p.n) (R : p.SiteMatrix) (E : ℝ) (ζ : ℂ) :
    ccyShift g g' R - (E : ℂ) • 1 - ζ • pairProjector p g' =
      ccyShift g g' (R - (E : ℂ) • 1 - ζ • pairProjector p g) := by
  rw [← ccy_shift_projector g g']
  ext x y
  simp [ccy_shift_eq_submatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

theorem ccy_compressed (g g' : ZMod p.n) (R : p.SiteMatrix) (E : ℝ) (ζ : ℂ) :
    compressedResolvent p g' (ccyShift g g' R) E ζ =
      ccyPairShift g g' (compressedResolvent p g R E ζ) := by
  ext x y
  unfold compressedResolvent ccyPairShift
  rw [ccy_shift_full, ccy_shift_eq_submatrix, Matrix.inv_submatrix_equiv]
  rfl

theorem ccy_trace_shift (g g' : ZMod p.n) (M : PairMatrix p g) :
    (ccyPairShift g g' M).trace = M.trace := by
  unfold Matrix.trace ccyPairShift
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp (ccyPairEquiv g g') (fun x => M x x)

theorem ccy_pairBlockTrace (g g' : ZMod p.n) (M : PairMatrix p g) (k : ZMod p.n) :
    pairBlockTrace p g' (ccyPairShift g g' M) k = pairBlockTrace p g M (k + (g - g')) := by
  unfold pairBlockTrace
  congr 1
  rw [← Equiv.sum_comp (ccyPairEquiv g g')]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ccy_pairEquiv_val]
  unfold ccyPairShift
  simp only [Matrix.submatrix_apply]
  exact if_congr (show (p.cyclicSiteEquiv (g - g') x.1).1 = k + (g - g') ↔ x.1.1 = k from
    add_left_inj _).symm rfl rfl

theorem ccy_pairContrast (g g' : ZMod p.n) :
    ccyPairShift g g' (pairContrast p g) = pairContrast p g' := by
  unfold ccyPairShift pairContrast
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  simp only [Function.comp_apply]
  exact if_congr (ccy_eq_iff (g := g) (g' := g') (k := x.1.1)) rfl rfl

/-!
## 3. Equivariance of the Dyson center
-/

theorem ccy_centerResidual (g g' : ZMod p.n) (R : p.SiteMatrix) (E : ℝ) :
    centerResidual p g' (ccyShift g g' R) E = centerResidual p g R E := by
  unfold centerResidual
  have h1 : g' + (g - g') = g := by abel
  have h2 : g' + 1 + (g - g') = g + 1 := by abel
  simp only [ccy_compressed, ccy_pairBlockTrace, h1, h2]

theorem ccy_isDysonRoot (g g' : ZMod p.n) (R : p.SiteMatrix) (E : ℝ) (ζ : ℂ) :
    IsDysonRoot p g' (ccyShift g g' R) E ζ ↔ IsDysonRoot p g R E ζ := by
  unfold IsDysonRoot
  rw [ccy_compressed, ccy_trace_shift]

theorem ccy_dysonRoot (g g' : ZMod p.n) (ρ₀ : ℝ) (R : p.SiteMatrix) (E : ℝ) :
    dysonRoot p g' ρ₀ (ccyShift g g' R) E = dysonRoot p g ρ₀ R E := by
  unfold dysonRoot
  have hP : (fun ζ => IsDysonRoot p g' (ccyShift g g' R) E ζ ∧
      ‖ζ - (splitS p : ℂ) * conj (matchedA E)‖ < ρ₀) =
      fun ζ => IsDysonRoot p g R E ζ ∧ ‖ζ - (splitS p : ℂ) * conj (matchedA E)‖ < ρ₀ :=
    funext fun ζ => propext (and_congr_left' (ccy_isDysonRoot g g' R E ζ))
  rw [hP]

theorem ccy_centerFormula (g g' : ZMod p.n) (R : p.SiteMatrix) (E : ℝ) (ζ : ℂ) :
    centerFormula p g' (ccyShift g g' R) E ζ = centerFormula p g R E ζ := by
  unfold centerFormula
  rw [ccy_compressed, ← ccy_pairContrast g g']
  have h : (ccyPairShift g g' (pairContrast p g) *
      (ccyPairShift g g' (compressedResolvent p g R E ζ))ᴴ *
        ccyPairShift g g' (compressedResolvent p g R E ζ)) =
      ccyPairShift g g' (pairContrast p g * (compressedResolvent p g R E ζ)ᴴ *
        compressedResolvent p g R E ζ) := by
    unfold ccyPairShift
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rw [h, ccy_trace_shift]

theorem ccy_inCenterDomain (g g' : ZMod p.n) (cst : CenterDomainConstants) (α : Fin p.N)
    (R : p.SiteMatrix) (E : ℝ) :
    InCenterDomain p g' cst α (ccyShift g g' R) E ↔ InCenterDomain p g cst α R E := by
  unfold InCenterDomain
  simp only [ccy_centerResidual, ccy_isDysonRoot]

/-- **Equivariance of the Dyson center**: `j_{g'}(τH^{(g)}, E) = j_g(H^{(g)}, E)`. -/
theorem ccy_dysonCenter (g g' : ZMod p.n) (cst : CenterDomainConstants) (α : Fin p.N)
    (R : p.SiteMatrix) (E : ℝ) :
    dysonCenter p g' cst α (ccyShift g g' R) E = dysonCenter p g cst α R E := by
  unfold dysonCenter
  rw [ccy_dysonRoot, ccy_centerFormula]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((ccy_inCenterDomain g g' cst α R E).mp h1) h2
  · exact absurd ((ccy_inCenterDomain g g' cst α R E).mpr h2) h1
  · rfl

end BlockBand.Center
