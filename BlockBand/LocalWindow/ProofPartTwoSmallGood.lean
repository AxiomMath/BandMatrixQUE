module

public import BlockBand.LocalWindow.ProofPartTwoSmallTransfer

/-!
# The small-`ρ` conclusion off the grid bad set

Off the grid bad set, the conclusion of part (ii) holds at every energy of the small-`ρ`
branch.

## Main results

* **`smallRho_good_of_not_mem`**: at an exterior point `ω` (Hermitian `H_R, V`, `‖C‖, ‖C*‖ ≤ c`)
  and a Hermitian pair block `G` with `(ω, G)` outside the grid bad set `smallBadSet` of the index
  set `I = labels × E-grid × ρ-grid × λ-grid`, at a nonpole energy `E` without crowding at
  `ε₀ = W^{-A₀}` and with `SmallPoleAt A₀ H`, given the root rectangles of all grid deformations on
  their label events and of `K₀(E)` (from the certificates), the grid errors
  `(c²/ε₁² + 1) h_E ≤ W^{-2}`, `d_ρ = W^{-2}`, and the observable comparison
  `‖B(ω, E) - J_g‖ ≤ √(2W) K ‖K₀(E) - K_g‖`: every unit `u` with `A(E)u = λu`, `|λ| ≤ δ`, has
  `|u*B(E)u - j_B(E, λ)| ≤ (2C_c + 4L + 144 + 8K) W^{-1/2+ε}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

variable {p : Parameters} {i : ZMod p.n}

/-- The index set of the small-`ρ` grids: pole labels, energies, `ρ`-values, window centres. -/
def smallIndex (Es : Finset ℝ) (Lρ dρ δ h : ℝ) : Finset (Option (ExteriorSite p i) × ℝ × ℝ × ℝ) :=
  (Finset.univ : Finset (Option (ExteriorSite p i))) ×ˢ (Es ×ˢ (intervalGrid Lρ dρ ×ˢ
    intervalGrid δ (h / 2)))

/-- **The small-`ρ` conclusion off the grid bad set**. -/
theorem smallRho_good_of_not_mem {om : SplitState p i} {G : PairMatrix p i}
    (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian) (hG : G.IsHermitian) {c : ℝ}
    (hc : 0 ≤ c) (hC : ∀ v, ‖T om.2.1 v‖ ≤ c * ‖v‖) (hC' : ∀ w, ‖T om.2.1ᴴ w‖ ≤ c * ‖w‖)
    {B : PairMatrix p i} (sel : CEH.EigenpairSelection (2 * p.W))
    {Jg : Option (ExteriorSite p i) → ℝ → ℝ → SplitState p i → PairMatrix p i}
    {A₀ H E ε₁ hE Lρ δ β εw ε Cc Kq r v₀ : ℝ} {Es : Finset ℝ}
    (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    (hcr : spectralSum om.1 (ProofCrowding.iccInd (E - (p.W : ℝ) ^ (-A₀))
      (E + (p.W : ℝ) ^ (-A₀))) < 2)
    (hsmall : SmallPoleAt p i A₀ H om E) (hε₁ : 0 < ε₁)
    (hη : ε₁ + hE ≤ (p.W : ℝ) ^ (-A₀)) (hEe : ∃ e ∈ Es, |E - e| ≤ hE)
    (hrE : (c ^ 2 / ε₁ ^ 2 + 1) * hE ≤ (p.W : ℝ) ^ (-2 : ℝ))
    (hL : (p.W : ℝ) ^ H + c ^ 2 / (p.W : ℝ) ^ (-A₀) ≤ Lρ)
    (hRg : ∀ e ∈ Es, ∀ (l : Option (ExteriorSite p i)) (ρg : ℝ), om ∈ smallLabel ε₁ l e →
      PairRootRectangle (smallGridK ε₁ l e ρg om) (splitS p) 0 r v₀)
    (hRK : ∀ j₀ : ExteriorSite p i, PoleSeparated ε₁ hH j₀ E →
      PairRootRectangle (schurK0 p i om E) (splitS p) 0 r v₀)
    (hδr : δ ≤ r / 2) (hhr : ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) ≤ r / 2)
    (hnot : (om, G) ∉ smallBadSet sel ε₁ (splitS p) β εw Cc Jg
      (smallIndex Es Lρ ((p.W : ℝ) ^ (-2 : ℝ)) δ (((2 * p.W : ℕ) : ℝ) ^ (-1 + β))))
    (hJ : ∀ l e ρg, ‖B - Jg l e ρg om‖ ≤
      Real.sqrt (2 * (p.W : ℝ)) * Kq * ‖schurK0 p i om E - smallGridK ε₁ l e ρg om‖)
    (hJgn : ∀ l e ρg, ‖Jg l e ρg om‖ ≤ 1) (hv₀ : 0 < v₀) (hKq : 0 ≤ Kq) (hβ : 0 < β)
    (hεw : 0 < εw) (hβε : β + εw ≤ ε) (hβh : β + εw ≤ 1 / 2) (hCc : 0 ≤ Cc) :
    ∀ lam : ℝ, |lam| ≤ δ → ∀ u : PairSite p i → ℂ, l2Norm u = 1 →
      schurA p i om G E *ᵥ u = (lam : ℂ) • u →
      |(star u ⬝ᵥ (B *ᵥ u)).re - windowCenter p i B (schurK0 p i om E) (splitS p) lam| ≤
        (2 * Cc + 4 * (2 * resLip (splitS p) v₀ / v₀) + 144 + 8 * Kq) *
          (p.W : ℝ) ^ (-(1 / 2 : ℝ) + ε) := by
  intro lam hlam u hu hAu
  have hW0 : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hs : 0 < splitS p := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  set h := ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) with hh
  have hh0 : 0 < h := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.mul_pos two_pos p.W_pos)) _
  have hdρ : (0 : ℝ) < (p.W : ℝ) ^ (-2 : ℝ) := Real.rpow_pos_of_pos hW0 _
  obtain ⟨e, he, hEe'⟩ := hEe
  obtain ⟨j₀, l, ρg, hρg, hsepE, hlab, hKerr⟩ :=
    smallRho_grid_choice hH hV hc hC hC' hdet hcr hsmall hε₁ hη hEe' hL hdρ
  obtain ⟨μ, hμ, hlμ⟩ := exists_intervalGrid_near (half_pos hh0) hlam
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hlam
  have hμδ : |μ| ≤ δ := intervalGrid_mem hδ0 (half_pos hh0).le hμ
  have hidx : (l, e, ρg, μ) ∈ smallIndex (p := p) (i := i) Es Lρ ((p.W : ℝ) ^ (-2 : ℝ)) δ h := by
    unfold smallIndex
    simp only [Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨he, hρg, hμ⟩
  have hnb : (om, G) ∉ smallPointBad sel ε₁ (splitS p) β εw Cc Jg l e ρg μ := fun hb =>
    hnot (Set.mem_biUnion hidx hb)
  have hgood : PairWindowGood (smallGridK ε₁ l e ρg om) (isHermitian_smallGridK ε₁ l e ρg om) sel
      (splitS p) μ β εw (Jg l e ρg om) G := by
    by_contra hng
    exact hnb ⟨hlab, Or.inl hng⟩
  have hcount : ∃ hG' : G.IsHermitian,
      ((Finset.univ.filter fun k => pairEigval sel (smallGridK ε₁ l e ρg om + G)
          ((isHermitian_smallGridK ε₁ l e ρg om).add hG') k ∈
        Icc (μ - h) (μ + h)).card : ℝ) ≤ Cc * ((2 * p.W : ℕ) : ℝ) ^ β := by
    by_contra hng
    exact hnb ⟨hlab, Or.inr hng⟩
  -- root rectangles around the window centre `μ`, radius `r/2`
  have hμr : |μ - 0| + r / 2 ≤ r := by rw [sub_zero]; linarith
  have hRg' := (hRg e he l ρg hlab).mono hμr
  have hRK' := (hRK j₀ hsepE).mono hμr
  have hK : (schurK0 p i om E).IsHermitian := by
    rw [← schurK0H_eq hH hV]; exact isHermitian_schurK0H om E
  -- operator error
  set rr := (c ^ 2 / ε₁ ^ 2 + 1) * |E - e| + (p.W : ℝ) ^ (-2 : ℝ) with hrr
  have hrr0 : 0 ≤ rr := by positivity
  have hrrW : rr ≤ 2 * (p.W : ℝ) ^ (-2 : ℝ) := by
    have : (c ^ 2 / ε₁ ^ 2 + 1) * |E - e| ≤ (c ^ 2 / ε₁ ^ 2 + 1) * hE :=
      mul_le_mul_of_nonneg_left hEe' (by positivity)
    linarith
  have hJ' : ‖B - Jg l e ρg om‖ ≤ Real.sqrt (2 * (p.W : ℝ)) * Kq * rr :=
    (hJ l e ρg).trans (mul_le_mul_of_nonneg_left hKerr (by positivity))
  have hAu' : (schurK0 p i om E + G) *ᵥ u = (lam : ℂ) • u := hAu
  have hlam' : |lam - μ| ≤ h / 2 := hlμ
  exact smallRho_point_le hK (isHermitian_smallGridK ε₁ l e ρg om) hG sel hs hv₀ hRg' hRK' hhr
    (hJgn l e ρg) hgood hcount hu hAu' hlam' hrr0 hKerr hrrW hJ' hKq hβ hεw hβε hβh hCc

end BlockBand.LocalWindow.ProofPartTwo
