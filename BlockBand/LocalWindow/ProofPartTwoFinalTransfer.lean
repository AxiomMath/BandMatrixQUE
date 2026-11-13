module

public import BlockBand.LocalWindow.ProofPartTwoTransfer
public import BlockBand.LocalWindow.ProofPartTwoStability
public import BlockBand.LocalWindow.ProofPartTwoObservable
public import BlockBand.LocalWindow.ProofPartTwoPoleCompl

/-!
# The small-`ρ` transfer from a grid point to the exact centre

`pairWindow_transfer_grid` centres the transferred overlap at the
centre `windowCenter J_g K_g s λ` of the **grid** deformation and grid observable. Part (ii) asks
for the centre `windowCenter J K s λ` of the **exact** deformation (at the energy `E`) `K = K₀(E)` and observable
`J = B(E)`. This file bounds the two moves.

## Main results

* `pairRootRectangle_shift`: a root rectangle around `E₁` of radius `r₁` contains every rectangle
  around `E₀` of radius `r₀` with `|E₀ - E₁| + r₀ ≤ r₁` (the certificate rectangles are centred at
  `0`; the window centres `μ` are grid points of `[-δ, δ]`).
* `norm_pairCentre_le`: `‖pairCentre J K s x‖ ≤ ‖J‖` at a Dyson root.
* **`smallRho_window_transfer`**: `K, K_g, G` Hermitian, `PairWindowGood K_g sel s μ β ε J_g G`,
  at most `N_c` eigenvalues of `K_g + G` in the window `[μ - h, μ + h]` (`h = (2W)^{-1+β}`),
  root rectangles of `K_g` and `K` around `μ` of radius `r₀ ≥ h`, `‖J_g‖ ≤ 1`; then for every
  unit `u` with `(K + G)u = λu`, `|λ - μ| ≤ h/2`, `‖K - K_g‖ ≤ r`:
  `|Re(u*Ju) - windowCenter J K s λ| ≤ 2‖J - J_g‖ + N_c · 2(2W)^ε(2W)^{-1/2}
  + (2 resLip/v₀)(3h/2) + 2τ + 2τ² + (2 resLip/v₀) r`, `τ = r/(h/2)`.

* `opNorm_vecMulVec_unit_le`, `opNorm_smul_vecMulVec_unit`: `‖ww*‖ ≤ 1`, `‖c ww*‖ = |c|` for a
  unit `w`.
* **`opNorm_schurK0_sub_grid_le`**: on the pole interval of both `E` and the grid energy `e`
  (`PoleSeparated ε j₀`, `E` not a pole), the exact deformation and the grid deformation
  `K_g = F_reg(e) + ρ_g ww* - e` of `pairRootRectangle_regF_family` satisfy
  `‖K₀(E) - K_g‖ ≤ (‖C‖²/ε² + 1)|E - e| + |ρ(E) - ρ_g|` (the operator error `r_W`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

/-- Root rectangles shrink: a rectangle around `E₁` of radius `r₁` contains the rectangle around
`E₀` of radius `r₀` when `|E₀ - E₁| + r₀ ≤ r₁`. -/
theorem pairRootRectangle_shift {K : PairMatrix p i} {s E₀ E₁ r₀ r₁ v₀ : ℝ}
    (h : PairRootRectangle K s E₁ r₁ v₀) (hr : |E₀ - E₁| + r₀ ≤ r₁) :
    PairRootRectangle K s E₀ r₀ v₀ := by
  intro x hx η hη hη1
  refine h x ?_ η hη hη1
  calc |x - E₁| = |(x - E₀) + (E₀ - E₁)| := by ring_nf
    _ ≤ |x - E₀| + |E₀ - E₁| := abs_add_le _ _
    _ ≤ r₁ := by linarith

/-- The real-axis centre of a contraction is a contraction: `‖pairCentre J K s x‖ ≤ ‖J‖` at a
Dyson root of the Hermitian `K` (`pairCentre_sub_le_obs` against `J = 0`). -/
theorem norm_pairCentre_le {K J : PairMatrix p i} (hK : K.IsHermitian) {s x : ℝ} (hs : 0 < s)
    {m : ℂ} (hm : IsDysonRoot K s (x : ℂ) m) : ‖pairCentre J K s x‖ ≤ ‖J‖ := by
  have h := pairCentre_sub_le_obs (B := J) (B' := 0) hK hs hm
  have h0 : pairCentre (0 : PairMatrix p i) K s x = 0 := by
    unfold pairCentre; simp
  rwa [h0, sub_zero, sub_zero] at h

/-- **The small-`ρ` window transfer to the exact centre**. Let `K_g` be a
Hermitian grid deformation with grid observable `J_g` (`‖J_g‖ ≤ 1`), `G` Hermitian with
`PairWindowGood K_g sel s μ β ε J_g G` and at most `N_c` eigenvalues of `K_g + G` in
`[μ - h, μ + h]`, `h = (2W)^{-1+β}`; let `K_g` and the exact Hermitian deformation `K` have root
rectangles around the window centre `μ` of radius `r₀ ≥ h`. For every unit `u` with
`(K + G) u = λ u`, `|λ - μ| ≤ h/2`, `‖K - K_g‖ ≤ r` and every observable `J`:
`|Re(u*Ju) - windowCenter J K s λ| ≤ 2‖J - J_g‖ + N_c · 2(2W)^ε(2W)^{-1/2} + (2 resLip/v₀)(3h/2)
+ 2τ + 2τ² + (2 resLip/v₀) r`, `τ = r/(h/2)` (no eigenvalue gap). -/
theorem smallRho_window_transfer {K Kg G J Jg : PairMatrix p i} (hK : K.IsHermitian)
    (hKg : Kg.IsHermitian) (hG : G.IsHermitian) (sel : CEH.EigenpairSelection (2 * p.W))
    {s μ β ε r₀ v₀ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀) (hRg : PairRootRectangle Kg s μ r₀ v₀)
    (hRK : PairRootRectangle K s μ r₀ v₀) (hhr : ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) ≤ r₀)
    (hJgn : ‖Jg‖ ≤ 1) (hgood : PairWindowGood Kg hKg sel s μ β ε Jg G) {Nc : ℕ}
    (hcount : (Finset.univ.filter fun k => pairEigval sel (Kg + G) (hKg.add hG) k ∈
        Icc (μ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (μ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))).card ≤ Nc)
    {u : PairSite p i → ℂ} (hu : l2Norm u = 1) {lam : ℝ} (hAu : (K + G) *ᵥ u = (lam : ℂ) • u)
    (hlam : |lam - μ| ≤ ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2) {r : ℝ} (hr : 0 ≤ r)
    (hKr : ‖K - Kg‖ ≤ r) :
    |(star u ⬝ᵥ (J *ᵥ u)).re - BlockBand.LocalWindow.windowCenter p i J K s lam| ≤
      2 * ‖J - Jg‖ +
        (Nc * (2 * (((2 * p.W : ℕ) : ℝ) ^ ε * ((2 * p.W : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))) +
          2 * resLip s v₀ / v₀ * (3 / 2 * ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) +
          2 * (r / (((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2)) +
          2 * (r / (((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2)) ^ 2) +
        2 * resLip s v₀ / v₀ * r := by
  set h := ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) with hh
  have hh0 : 0 < h := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.mul_pos two_pos p.W_pos)) _
  have hlam0 : |lam - μ| ≤ r₀ := hlam.trans (by linarith)
  -- the Dyson roots at `λ`
  obtain ⟨mg, hmg, _⟩ := hRg lam hlam0 0 le_rfl zero_le_one
  obtain ⟨mK, hmK, _⟩ := hRK lam hlam0 0 le_rfl zero_le_one
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hmg hmK
  -- (1) observable move in the overlap
  have t1 : |(star u ⬝ᵥ (J *ᵥ u)).re - (star u ⬝ᵥ (Jg *ᵥ u)).re| ≤ ‖J - Jg‖ :=
    abs_quadForm_sub_le J Jg hu
  -- (2) the grid transfer
  have t2 := pairWindow_transfer_grid hKg hG sel hs hv₀ hRg hhr hJgn hgood hcount hu hAu hlam hr
    hKr
  have hcen : ‖pairCentre Jg Kg s lam‖ ≤ 1 := (norm_pairCentre_le hKg hs hmg).trans hJgn
  have hτ : 0 ≤ (r / (h / 2)) ^ 2 := sq_nonneg _
  have t2' : |(star u ⬝ᵥ (Jg *ᵥ u)).re - BlockBand.LocalWindow.windowCenter p i Jg Kg s lam| ≤
      Nc * (2 * (((2 * p.W : ℕ) : ℝ) ^ ε * ((2 * p.W : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))) +
        2 * resLip s v₀ / v₀ * (3 / 2 * h) + 2 * (r / (h / 2)) + 2 * (r / (h / 2)) ^ 2 := by
    refine t2.trans ?_
    have : (1 + ‖pairCentre Jg Kg s lam‖) * (r / (h / 2)) ^ 2 ≤ 2 * (r / (h / 2)) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hτ
    linarith
  -- (3) deformation move in the centre
  have t3 : |BlockBand.LocalWindow.windowCenter p i Jg Kg s lam -
      BlockBand.LocalWindow.windowCenter p i Jg K s lam| ≤ 2 * resLip s v₀ / v₀ * r := by
    refine (windowCenter_sub_le_of_rootRectangle hKg hK hJgn hs hv₀ hRg hRK hlam0 hlam0).trans ?_
    have hL0 : 0 ≤ 2 * resLip s v₀ / v₀ := by
      have : 0 ≤ resLip s v₀ := by
        unfold resLip
        have := rootLip_nonneg s v₀
        have : 0 ≤ 1 + s * rootLip s v₀ := by nlinarith
        positivity
      positivity
    refine mul_le_mul_of_nonneg_left ?_ hL0
    rw [sub_self, abs_zero, zero_add, norm_sub_rev]
    exact hKr
  -- (4) observable move in the centre
  have t4 : |BlockBand.LocalWindow.windowCenter p i Jg K s lam -
      BlockBand.LocalWindow.windowCenter p i J K s lam| ≤ ‖J - Jg‖ := by
    rw [← norm_neg (J - Jg), neg_sub]
    exact windowCenter_sub_le_obs hK hs hmK
  -- assemble
  have e : (star u ⬝ᵥ (J *ᵥ u)).re - BlockBand.LocalWindow.windowCenter p i J K s lam =
      ((star u ⬝ᵥ (J *ᵥ u)).re - (star u ⬝ᵥ (Jg *ᵥ u)).re) +
        ((star u ⬝ᵥ (Jg *ᵥ u)).re - BlockBand.LocalWindow.windowCenter p i Jg Kg s lam) +
        (BlockBand.LocalWindow.windowCenter p i Jg Kg s lam -
          BlockBand.LocalWindow.windowCenter p i Jg K s lam) +
        (BlockBand.LocalWindow.windowCenter p i Jg K s lam -
          BlockBand.LocalWindow.windowCenter p i J K s lam) := by ring
  rw [e]
  have s1 := abs_add_le (((star u ⬝ᵥ (J *ᵥ u)).re - (star u ⬝ᵥ (Jg *ᵥ u)).re) +
        ((star u ⬝ᵥ (Jg *ᵥ u)).re - BlockBand.LocalWindow.windowCenter p i Jg Kg s lam) +
        (BlockBand.LocalWindow.windowCenter p i Jg Kg s lam -
          BlockBand.LocalWindow.windowCenter p i Jg K s lam))
    (BlockBand.LocalWindow.windowCenter p i Jg K s lam -
          BlockBand.LocalWindow.windowCenter p i J K s lam)
  have s2 := abs_add_le (((star u ⬝ᵥ (J *ᵥ u)).re - (star u ⬝ᵥ (Jg *ᵥ u)).re) +
        ((star u ⬝ᵥ (Jg *ᵥ u)).re - BlockBand.LocalWindow.windowCenter p i Jg Kg s lam))
    (BlockBand.LocalWindow.windowCenter p i Jg Kg s lam -
          BlockBand.LocalWindow.windowCenter p i Jg K s lam)
  have s3 := abs_add_le ((star u ⬝ᵥ (J *ᵥ u)).re - (star u ⬝ᵥ (Jg *ᵥ u)).re)
    ((star u ⬝ᵥ (Jg *ᵥ u)).re - BlockBand.LocalWindow.windowCenter p i Jg Kg s lam)
  linarith

/-- `‖ww*‖ ≤ 1` for a unit vector `w`. -/
theorem opNorm_vecMulVec_unit_le {ι : Type} [Fintype ι] [DecidableEq ι] {w : ι → ℂ}
    (hw : sqNorm w = 1) : ‖vecMulVec w (star w)‖ ≤ 1 := by
  refine opNorm_le_of_sqNorm zero_le_one fun v => ?_
  rw [vecMulVec_star_mulVec, ← vnorm_sq, ← vnorm_sq, vnorm_smul, vnorm_of_sqNorm_one hw, mul_one,
    one_pow, one_mul]
  have h : ‖star w ⬝ᵥ v‖ ≤ vnorm w * vnorm v := by
    have e : star w ⬝ᵥ v =
        inner ℂ (WithLp.toLp 2 w : EuclideanSpace ℂ ι) (WithLp.toLp 2 v) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rw [e, vnorm_eq, vnorm_eq]
    exact norm_inner_le_norm _ _
  rw [vnorm_of_sqNorm_one hw, one_mul] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `‖c ww*‖ = |c|` for a unit vector `w` and real `c`. -/
theorem opNorm_smul_vecMulVec_unit {ι : Type} [Fintype ι] [DecidableEq ι] {w : ι → ℂ}
    (hw : sqNorm w = 1) (c : ℝ) : ‖(c : ℂ) • vecMulVec w (star w)‖ = |c| := by
  refine le_antisymm ?_ ?_
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |c| * ‖vecMulVec w (star w)‖ ≤ |c| * 1 :=
          mul_le_mul_of_nonneg_left (opNorm_vecMulVec_unit_le hw) (abs_nonneg _)
      _ = |c| := mul_one _
  · have hww : star w ⬝ᵥ w = 1 := by rw [star_dotProduct_self, hw]; simp
    have h := norm_quadForm_le ((c : ℂ) • vecMulVec w (star w)) w
    rw [hw, mul_one, Matrix.smul_mulVec, vecMulVec_star_mulVec, hww, one_smul,
      dotProduct_smul, hww, smul_eq_mul, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
    exact h

/-- **The operator error from the grid point**: with `E` not a pole and
both `E` and the grid energy `e` in the pole interval of `j₀` (`PoleSeparated ε`, `ε > 0`), the
exact deformation `K₀(E) = F_reg(E) - E + ρ(E) ww*` and the grid deformation
`K_g = F_reg(e) + ρ_g ww* - e` satisfy `‖K₀(E) - K_g‖ ≤ (‖C‖²/ε² + 1)|E - e| + |ρ(E) - ρ_g|`. -/
theorem opNorm_schurK0_sub_grid_le {ε : ℝ} (hε : 0 < ε) (om : SplitState p i)
    (hH : om.1.IsHermitian) (j₀ : ExteriorSite p i) {E e ρg : ℝ}
    (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0) (hsepE : PoleSeparated ε hH j₀ E)
    (hsepe : PoleSeparated ε hH j₀ e) :
    ‖BlockBand.LocalWindow.schurK0 p i om E -
        (regF hH j₀ om.2.1 om.2.2 e +
          (ρg : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) -
            (e : ℂ) • (1 : PairMatrix p i))‖ ≤
      (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e| + |poleRho hH j₀ om.2.1 E - ρg| := by
  have : Nonempty (PairSite p i) := pairSite_nonempty p i
  set P := vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) with hP
  have hdiff : BlockBand.LocalWindow.schurK0 p i om E -
      (regF hH j₀ om.2.1 om.2.2 e + (ρg : ℂ) • P - (e : ℂ) • (1 : PairMatrix p i)) =
      ((regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • (1 : PairMatrix p i)) -
        (regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i))) +
        ((poleRho hH j₀ om.2.1 E - ρg : ℝ) : ℂ) • P := by
    rw [schurK0_pole_decomp om hH j₀ hdet, Complex.ofReal_sub, sub_smul]
    abel
  rw [hdiff]
  refine (norm_add_le _ _).trans (add_le_add (opNorm_regK_sub_le hε om hH j₀ hsepE hsepe) ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc |poleRho hH j₀ om.2.1 E - ρg| * ‖P‖ ≤ |poleRho hH j₀ om.2.1 E - ρg| * 1 :=
        mul_le_mul_of_nonneg_left (opNorm_vecMulVec_unit_le (sqNorm_poleDir hH j₀ om.2.1))
          (abs_nonneg _)
    _ = _ := mul_one _

end BlockBand.LocalWindow.ProofPartTwo
