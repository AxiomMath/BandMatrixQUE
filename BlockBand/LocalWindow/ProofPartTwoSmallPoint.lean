module

public import BlockBand.LocalWindow.ProofPartTwoSmallGrid

/-!
# The grid point of an energy, small `ρ`

Choice of a grid point near an energy `E` of the small-`ρ` branch, with the root rectangles and
norm bounds of the corresponding grid deformation.

Fixed exterior data `ω` (Hermitian `H_R, V`, `‖C‖, ‖C*‖ ≤ c`), a nonpole energy `E` with no
crowding at radius `ε₀ = W^{-A₀}` and `SmallPoleAt A₀ H`, and a grid energy `e` with
`|E - e| ≤ η`, `ε₁ + η ≤ ε₀`.

## Main results

* `sqNorm_poleCoupling_le`: `‖C*φ‖² ≤ c²`.
* **`smallRho_rectangles`**: with the constants of `pairRootRectangle_rankOne_family`, the grid
  deformation on its label event and `K₀(E)` itself (at a separated label, from the
  certificate at `E`) have root rectangles `PairRootRectangle · s' 0 r v₀`.
* **`opNorm_smallGridK_le`**: on the label event, `‖smallGridK ε l e ρ_g ω‖ ≤ ‖V‖ + c²/ε + |e| +
  |ρ_g|` (the norm hypothesis of the window ETH).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open BlockBand.LocalWindow.ProofCertificate BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

variable {p : Parameters} {i : ZMod p.n}

section Generic

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `‖C*φ‖² ≤ c²` when `‖C*‖ ≤ c` as a Euclidean map (`φ` a unit eigenvector). -/
theorem sqNorm_poleCoupling_le {H : Matrix α α ℂ} (hH : H.IsHermitian) (j₀ : α) {C : Matrix α β ℂ}
    {c : ℝ} (hC' : ∀ w, ‖T Cᴴ w‖ ≤ c * ‖w‖) :
    sqNorm (poleCoupling hH j₀ C) ≤ c ^ 2 := by
  have hφ : poleVec hH j₀ = ⇑(hH.eigenvectorBasis j₀) := by
    funext a; unfold poleVec; rw [IsHermitian.eigenvectorUnitary_apply]
  have h1 : vnorm (poleCoupling hH j₀ C) ≤ c := by
    rw [vnorm_eq]
    unfold poleCoupling
    have e : (WithLp.toLp 2 (Cᴴ *ᵥ poleVec hH j₀) : EuclideanSpace ℂ β) =
        T Cᴴ (WithLp.toLp 2 (poleVec hH j₀)) := rfl
    rw [e]
    refine (hC' _).trans ?_
    have hn : ‖(WithLp.toLp 2 (poleVec hH j₀) : EuclideanSpace ℂ α)‖ = 1 := by
      rw [hφ, WithLp.toLp_ofLp]; exact hH.eigenvectorBasis.orthonormal.1 j₀
    rw [hn, mul_one]
  rw [← vnorm_sq]
  exact pow_le_pow_left₀ (vnorm_nonneg _) h1 2

end Generic

/-- `‖C‖ ≤ c` from the Euclidean bound. -/
theorem opNorm_C_le {om : SplitState p i} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ v, ‖T om.2.1 v‖ ≤ c * ‖v‖) : ‖om.2.1‖ ≤ c :=
  opNorm_le_of_toE _ hc hC

/-- **The grid point of an energy**. Hermitian `H_R, V`, `‖C‖, ‖C*‖ ≤ c`,
`E` not an exterior eigenvalue, no crowding at radius `ε₀ = W^{-A₀}` around `E`,
`SmallPoleAt A₀ H ω E`, `0 < ε₁`, `ε₁ + η ≤ ε₀`, `|E - e| ≤ η`, `L_ρ ≥ W^H + c²/ε₀`, `h_ρ > 0`:
a separated label `j₀`, a grid label `l` and `ρ_g ∈ intervalGrid L_ρ h_ρ` with
`ω ∈ smallLabel ε₁ l e` and `‖K₀(E) - smallGridK ε₁ l e ρ_g ω‖ ≤ (c²/ε₁² + 1)|E - e| + h_ρ`. -/
theorem smallRho_grid_choice {om : SplitState p i} (hH : om.1.IsHermitian)
    (hV : om.2.2.IsHermitian) {c : ℝ} (hc : 0 ≤ c) (hC : ∀ v, ‖T om.2.1 v‖ ≤ c * ‖v‖)
    (hC' : ∀ w, ‖T om.2.1ᴴ w‖ ≤ c * ‖w‖) {A₀ H E e ε₁ η Lρ dρ : ℝ}
    (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    (hcr : spectralSum om.1 (ProofCrowding.iccInd (E - (p.W : ℝ) ^ (-A₀))
      (E + (p.W : ℝ) ^ (-A₀))) < 2)
    (hsmall : SmallPoleAt p i A₀ H om E) (hε₁ : 0 < ε₁) (hη : ε₁ + η ≤ (p.W : ℝ) ^ (-A₀))
    (hEe : |E - e| ≤ η) (hL : (p.W : ℝ) ^ H + c ^ 2 / (p.W : ℝ) ^ (-A₀) ≤ Lρ) (hdρ : 0 < dρ) :
    ∃ (j₀ : ExteriorSite p i) (l : Option (ExteriorSite p i)) (ρg : ℝ),
      ρg ∈ intervalGrid Lρ dρ ∧ PoleSeparated ε₁ hH j₀ E ∧ om ∈ smallLabel ε₁ l e ∧
      ‖schurK0 p i om E - smallGridK ε₁ l e ρg om‖ ≤ (c ^ 2 / ε₁ ^ 2 + 1) * |E - e| + dρ := by
  have : Nonempty (PairSite p i) := pairSite_nonempty p i
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  set ε₀ := (p.W : ℝ) ^ (-A₀) with hε₀
  have hε₀0 : 0 < ε₀ := Real.rpow_pos_of_pos hW _
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hEe
  obtain ⟨j₀, hsep⟩ := exists_poleSeparated_of_crowding hH hcr
  have hsepE : PoleSeparated ε₁ hH j₀ E := poleSeparated_mono hH (by linarith) hsep
  have hsepe : PoleSeparated ε₁ hH j₀ e :=
    poleSeparated_shift hH (poleSeparated_mono hH hη hsep) hEe
  have hCn : ‖om.2.1‖ ≤ c := opNorm_C_le hc hC
  have hLρ0 : 0 ≤ Lρ := le_trans (by positivity) hL
  by_cases hnear : |hH.eigenvalues j₀ - E| ≤ ε₀
  · -- a simple pole within `ε₀`: the rank-one grid
    have hsim : PoleSimple hH j₀ := poleSimple_of_poleSeparated hH hsep hnear
    have hρE : |poleRho hH j₀ om.2.1 E| ≤ Lρ := by
      refine (abs_poleRho_le_of_smallPoleAt om hH j₀ hdet hsep hsmall).trans (le_trans ?_ hL)
      have := sqNorm_poleCoupling_le hH j₀ hC'
      have := div_le_div_of_nonneg_right this hε₀0.le
      linarith
    obtain ⟨ρg, hρg, hρd⟩ := exists_intervalGrid_near hdρ hρE
    refine ⟨j₀, some j₀, ρg, hρg, hsepE, ⟨hH, hsim, hsepe⟩, ?_⟩
    have hK : smallGridK ε₁ (some j₀) e ρg om = regF hH j₀ om.2.1 om.2.2 e +
        (ρg : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) -
          (e : ℂ) • (1 : PairMatrix p i) := by
      show poleGridK ε₁ j₀ e ρg om = _
      rw [poleGridK_eq hH hV hsim hsepe ρg]
      abel
    rw [hK]
    refine (opNorm_schurK0_sub_grid_le hε₁ om hH j₀ hdet hsepE hsepe).trans ?_
    have h1 : ‖om.2.1‖ ^ 2 / ε₁ ^ 2 ≤ c ^ 2 / ε₁ ^ 2 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hCn 2) (by positivity)
    have h2 := mul_le_mul_of_nonneg_right (add_le_add_left h1 1) (abs_nonneg (E - e))
    have h2' : (‖om.2.1‖ ^ 2 / ε₁ ^ 2 + 1) * |E - e| ≤ (c ^ 2 / ε₁ ^ 2 + 1) * |E - e| := by
      simpa [add_comm] using h2
    linarith
  · -- no exterior eigenvalue within `ε₀`: `F(E) = F̂(E)`
    push Not at hnear
    obtain ⟨ρg, hρg, -⟩ := exists_intervalGrid_near hdρ (L := Lρ) (x := 0) (by rw [abs_zero]; exact hLρ0)
    refine ⟨j₀, none, ρg, hρg, hsepE, mem_univ _, ?_⟩
    have hhat : poleRhoHat ε₁ hH j₀ om.2.1 E = poleRho hH j₀ om.2.1 E := by
      have hn : ¬ |hH.eigenvalues j₀ - E| ≤ ε₁ := by linarith
      unfold poleRhoHat poleRho truncInv
      simp only [hn, ite_false]
    have hF : physicalCoareaF om.1 om.2.1 om.2.2 E = truncF ε₁ om.1 om.2.1 om.2.2 E := by
      rw [physicalCoareaF_eq_truncF_add ε₁ hH j₀ om.2.1 om.2.2 hdet hsepE, hhat, sub_self,
        Complex.ofReal_zero, zero_smul, add_zero]
    have hK : schurK0 p i om E - smallGridK ε₁ none e ρg om =
        (truncF ε₁ om.1 om.2.1 om.2.2 E - truncF ε₁ om.1 om.2.1 om.2.2 e) -
          ((E - e : ℝ) : ℂ) • (1 : PairMatrix p i) := by
      show schurK0 p i om E - truncGridK ε₁ e om = _
      rw [truncGridK_eq hV]
      unfold schurK0
      rw [hF, Complex.ofReal_sub, sub_smul]
      abel
    rw [hK]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖truncF ε₁ om.1 om.2.1 om.2.2 E - truncF ε₁ om.1 om.2.1 om.2.2 e‖ ≤
        c ^ 2 * (|E - e| / ε₁ ^ 2) :=
      opNorm_le_of_toE _ (by positivity) (norm_truncF_sub_le hH om.2.1 om.2.2 hε₁ hc hC hC' E e)
    have h2 : ‖((E - e : ℝ) : ℂ) • (1 : PairMatrix p i)‖ ≤ |E - e| := by
      refine (opNorm_smul_one_le _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
    have e3 : c ^ 2 * (|E - e| / ε₁ ^ 2) + |E - e| = (c ^ 2 / ε₁ ^ 2 + 1) * |E - e| := by ring
    linarith

/-- **The root rectangles of the small-`ρ` branch** (`pairRootRectangle_rankOne_family`).
Constants `ε_c, r, s₀, v₀ > 0` depending on `b, κ`; for every admissible `p` with `p.b = b`,
Hermitian `V`, truncation radius `ε`, `2/(W s √κ) ≤ ε_c`, `s' ∈ [s - s₀, s]`:
(1) at a grid energy `e ∈ bulkInterval κ` with `certErrHat ε ω e ≤ ε_c`, every grid deformation
`smallGridK ε l e ρ_g ω` with `ω ∈ smallLabel ε l e` has `PairRootRectangle · s' 0 r v₀`;
(2) at an energy `E ∈ bulkInterval κ` with `certErrHat ε ω E ≤ ε_c`, not an exterior eigenvalue,
with a label `j₀` separated at `ε`, `K₀(E)` has `PairRootRectangle · s' 0 r v₀`. -/
theorem smallRho_rectangles (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hκ : 0 < κ) :
    ∃ εc r s₀ v₀ : ℝ, 0 < εc ∧ 0 < r ∧ 0 < s₀ ∧ 0 < v₀ ∧
      ∀ p : Parameters, p.b = b → ∀ (i : ZMod p.n) (om : SplitState p i)
        (_hV : om.2.2.IsHermitian) (ε : ℝ), 2 / ((p.W : ℝ) * splitS p * Real.sqrt κ) ≤ εc →
        ∀ s' : ℝ, splitS p - s₀ ≤ s' → s' ≤ splitS p →
        (∀ e : ℝ, e ∈ bulkInterval κ → certErrHat ε p i om e ≤ εc →
          ∀ (l : Option (ExteriorSite p i)) (ρg : ℝ), om ∈ smallLabel ε l e →
            PairRootRectangle (smallGridK ε l e ρg om) s' 0 r v₀) ∧
        (∀ E : ℝ, E ∈ bulkInterval κ → certErrHat ε p i om E ≤ εc →
          (om.1 - (E : ℂ) • 1).det ≠ 0 → ∀ (hH : om.1.IsHermitian) (j₀ : ExteriorSite p i),
            PoleSeparated ε hH j₀ E → PairRootRectangle (schurK0 p i om E) s' 0 r v₀) := by
  obtain ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, h⟩ := pairRootRectangle_rankOne_family b κ hb hb' hκ
  refine ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, fun p hpb i om hV ε hW s' hs1 hs2 => ⟨?_, ?_⟩⟩
  · intro e he hcert l ρg hl
    have : Nonempty (PairSite p i) := pairSite_nonempty p i
    cases l with
    | none =>
      have hK : smallGridK ε none e ρg om = truncF ε om.1 om.2.1 om.2.2 e +
          ((0 : ℝ) : ℂ) • vecMulVec (Pi.single (Classical.arbitrary (PairSite p i)) 1)
            (star (Pi.single (Classical.arbitrary (PairSite p i)) 1)) -
          (e : ℂ) • (1 : PairMatrix p i) := by
        show truncGridK ε e om = _
        rw [truncGridK_eq hV, Complex.ofReal_zero, zero_smul, add_zero]
      rw [hK]
      exact h p hpb i om hV ε e he hcert hW _ _ s' hs1 hs2
    | some j₀ =>
      obtain ⟨hH, hsim, hsep⟩ := hl
      have hK : smallGridK ε (some j₀) e ρg om = truncF ε om.1 om.2.1 om.2.2 e +
          ((ρg - poleRhoHat ε hH j₀ om.2.1 e : ℝ) : ℂ) •
            vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) -
          (e : ℂ) • (1 : PairMatrix p i) := by
        show poleGridK ε j₀ e ρg om = _
        rw [poleGridK_eq hH hV hsim hsep ρg, truncF_pole_decomp ε hH j₀ om.2.1 om.2.2 hsep,
          Complex.ofReal_sub, sub_smul]
        abel
      rw [hK]
      exact h p hpb i om hV ε e he hcert hW _ _ s' hs1 hs2
  · intro E hE hcert hdet hH j₀ hsep
    have : Nonempty (PairSite p i) := pairSite_nonempty p i
    have hK : schurK0 p i om E = truncF ε om.1 om.2.1 om.2.2 E +
        ((poleRho hH j₀ om.2.1 E - poleRhoHat ε hH j₀ om.2.1 E : ℝ) : ℂ) •
          vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) -
        (E : ℂ) • (1 : PairMatrix p i) := by
      unfold schurK0
      rw [physicalCoareaF_eq_truncF_add ε hH j₀ om.2.1 om.2.2 hdet hsep]
    rw [hK]
    exact h p hpb i om hV ε E hE hcert hW _ _ s' hs1 hs2

/-- **The norm of the grid deformation** on its label event: `‖smallGridK ε l e ρ_g ω‖ ≤
‖V‖ + c²/ε + |e| + |ρ_g|` (Hermitian `V`, `‖C‖, ‖C*‖ ≤ c`, `ε > 0`). -/
theorem opNorm_smallGridK_le {om : SplitState p i} (hV : om.2.2.IsHermitian) {c v : ℝ}
    (hc : 0 ≤ c) (hC : ∀ x, ‖T om.2.1 x‖ ≤ c * ‖x‖) (hC' : ∀ w, ‖T om.2.1ᴴ w‖ ≤ c * ‖w‖)
    (hv0 : 0 ≤ v) (hVn : ∀ x, ‖T om.2.2 x‖ ≤ v * ‖x‖) {ε : ℝ} (hε : 0 < ε) (l : Option (ExteriorSite p i))
    (e ρg : ℝ) (hl : om ∈ smallLabel ε l e) :
    ‖smallGridK ε l e ρg om‖ ≤ v + c ^ 2 / ε + |e| + |ρg| := by
  have : Nonempty (PairSite p i) := pairSite_nonempty p i
  have hv : ‖om.2.2‖ ≤ v := opNorm_le_of_toE _ hv0 hVn
  have hsm : ‖(e : ℂ) • (1 : PairMatrix p i)‖ ≤ |e| := by
    refine (opNorm_smul_one_le _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hρ0 : 0 ≤ |ρg| := abs_nonneg _
  cases l with
  | none =>
    show ‖truncGridK ε e om‖ ≤ _
    rw [truncGridK_eq hV]
    have hH : om.1.IsHermitian ∨ ¬ om.1.IsHermitian := em _
    have h1 : ‖truncF ε om.1 om.2.1 om.2.2 e‖ ≤ v + c ^ 2 / ε := by
      rcases hH with hH | hH
      · exact opNorm_le_of_toE _ (by positivity) (norm_truncF_le hH om.2.1 om.2.2 hε hc
            hC hC' hVn e)
      · have h0 : truncF ε om.1 om.2.1 om.2.2 e = om.2.2 := by
          unfold truncF truncResolvent; simp [hH]
        rw [h0]
        have : 0 ≤ c ^ 2 / ε := by positivity
        linarith
    linarith [norm_sub_le (truncF ε om.1 om.2.1 om.2.2 e) ((e : ℂ) • (1 : PairMatrix p i))]
  | some j₀ =>
    obtain ⟨hH, hsim, hsep⟩ := hl
    show ‖poleGridK ε j₀ e ρg om‖ ≤ _
    rw [poleGridK_eq hH hV hsim hsep ρg]
    have h1 := opNorm_regK_le hε om hH j₀ hsep
    have hCn : ‖om.2.1‖ ≤ c := opNorm_C_le hc hC
    have h2 : ‖om.2.1‖ ^ 2 / ε ≤ c ^ 2 / ε :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hCn 2) hε.le
    have h3 : ‖((ρg : ℝ) : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1))‖ =
        |ρg| := opNorm_smul_vecMulVec_unit (sqNorm_poleDir hH j₀ om.2.1) ρg
    have h4 := norm_add_le (regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i))
      (((ρg : ℝ) : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)))
    linarith

end BlockBand.LocalWindow.ProofPartTwo
