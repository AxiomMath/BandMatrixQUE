module

public import BlockBand.LocalWindow.ProofPartTwoAssembly
public import BlockBand.LocalWindow.ProofPartTwoExterior
public import BlockBand.LocalWindow.ProofPartTwoFinalTransfer

/-!
# Part (ii) of the physical local window: the small-`ρ` and large-`ρ` branches

Part (ii) of the physical local-window lemma is reduced to two branch statements, according to
whether the singular part `σ(E)` of the Schur deformation is at most or above `W^H`.

## Main results

* `PartTwoGoodAt`: the conclusion of part (ii) at one rank `α` (so `PartTwoGood = ∀ bulk α,
  PartTwoGoodAt`), with monotonicity `partTwoGoodAt_mono` (smaller `δ`, larger `C`).
* `SmallPoleAt A₀ H ω E` / `LargePoleAt A₀ H ω E`: `σ(E) ≤ W^H` / `σ(E) > W^H`.
* **`PartTwoSmallRhoStatement`**: the conditional form of (ii) (as in
  `PartTwoConditionalLargeStatement`) at the ranks with `SmallPoleAt A₀ H`, for every
  `A₀ ≥ D + 4` and every `H` (constants depending on `A₀, H`).
* **`PartTwoLargeRhoStatement`**: the same at the ranks with `LargePoleAt A₀ H`, for every
  `A₀ ≥ D + 4` and some `H = H(A₀, ε, D, K₀)` (the compression branch).
* `isWindowObservable_mono`: the observable class shrinks as `k` grows.
* **`partTwoConditionalLarge_of_branches`**: the two branches give
  `PartTwoConditionalLargeStatement` (`A₀ = D + 4`; common `δ = min δ₁ δ₂`, `k = max k₁ k₂`,
  `W₀ = max W₁ W₂`; `CondSmall.union`; every rank is in one branch).
* **`physicalLocalWindow_partTwo_of_branches`**: with `physicalLocalWindow_partTwo_of_large`,
  `PhysicalLocalWindowPartTwoStatement`. The reduction itself uses no hypothesis; the
  hypotheses enter through the branches.

Tools for the branches:
* `opNorm_physicalCoareaF_sub_truncF_eq` (`σ = |ρ - ρ̂|`), `abs_poleRhoHat_le`,
  `abs_poleRho_le_of_smallPoleAt`, `abs_poleRho_gt_of_largePoleAt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs BlockBand.LocalWindow.ProofETH
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## The conclusion at one rank and the split predicates
-/

/-- The conclusion of part (ii) at one rank `α`: at `E = λ_α`, for `|λ| ≤ δ`
and every unit `u` with `A(E) u = λ u`, `|u*B u - j_B(E, λ)| ≤ C W^{-1/2+ε}`. -/
def PartTwoGoodAt (p : Parameters) (i : ZMod p.n) (δ C ε : ℝ)
    (B : SplitState p i → ℝ → PairMatrix p i) (x : SplitState p i × PairMatrix p i)
    (α : Fin p.N) : Prop :=
  let E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α
  let A := schurA p i x.1 x.2 E
  ∀ lam : ℝ, |lam| ≤ δ → ∀ u : PairSite p i → ℂ, l2Norm u = 1 →
    A *ᵥ u = (lam : ℂ) • u →
    |(star u ⬝ᵥ (B x.1 E *ᵥ u)).re -
        windowCenter p i (B x.1 E) (schurK0 p i x.1 E) (splitS p) lam| ≤
      C * (p.W : ℝ) ^ (-(1 / 2 : ℝ) + ε)

variable {p : Parameters} {i : ZMod p.n}

theorem partTwoGood_iff_forall_at {ϑ δ C ε : ℝ} {B : SplitState p i → ℝ → PairMatrix p i}
    {x : SplitState p i × PairMatrix p i} :
    PartTwoGood p i ϑ δ C ε B x ↔ ∀ α : Fin p.N, IsBulkRank p ϑ α → PartTwoGoodAt p i δ C ε B x α :=
  Iff.rfl

/-- `PartTwoGoodAt` is monotone: smaller `δ`, larger `C`. -/
theorem partTwoGoodAt_mono {δ δ' C C' ε : ℝ} {B : SplitState p i → ℝ → PairMatrix p i}
    {x : SplitState p i × PairMatrix p i} {α : Fin p.N} (hδ : δ' ≤ δ) (hC : C ≤ C')
    (h : PartTwoGoodAt p i δ C ε B x α) : PartTwoGoodAt p i δ' C' ε B x α := by
  intro lam hlam u hu hAu
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  exact (h lam (hlam.trans hδ) u hu hAu).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hW.le _))

/-- The singular part `σ(E) = ‖F(E) - F̂(E)‖` of the Schur deformation at truncation radius
`ε₀` (`rank(F - F̂) ≤ 1` off crowding, and then `σ = |ρ - ρ̂|`). -/
def singularPart (p : Parameters) (i : ZMod p.n) (ε₀ : ℝ) (om : SplitState p i) (E : ℝ) : ℝ :=
  ‖physicalCoareaF om.1 om.2.1 om.2.2 E - ProofCount.truncF ε₀ om.1 om.2.1 om.2.2 E‖

/-- **Small pole parameter** (`|ρ| ≤ W^H`), in the canonical form
`σ(E) ≤ W^H` at truncation radius `ε₀ = W^{-A₀}`. -/
def SmallPoleAt (p : Parameters) (i : ZMod p.n) (A₀ H : ℝ) (om : SplitState p i) (E : ℝ) :
    Prop :=
  singularPart p i ((p.W : ℝ) ^ (-A₀)) om E ≤ (p.W : ℝ) ^ H

/-- **Large pole parameter** (`|ρ| > W^H`), in the canonical form
`σ(E) > W^H`. -/
def LargePoleAt (p : Parameters) (i : ZMod p.n) (A₀ H : ℝ) (om : SplitState p i) (E : ℝ) :
    Prop :=
  (p.W : ℝ) ^ H < singularPart p i ((p.W : ℝ) ^ (-A₀)) om E

/-!
## The two branch statements
-/

/-- **The small-`ρ` branch of part (ii)**: the conditional form of
`PartTwoConditionalLargeStatement`, with the conclusion required at the ranks `α` whose energy
`E = λ_α` has `SmallPoleAt A₀ H`. `b, T, ϑ` first; then `0 < δ < 1` and `k`; then `ε, D > 0`,
`K₀`, `A₀ ≥ D + 4` and `H`; then `C, W₀`. -/
def PartTwoSmallRhoStatement : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
    ∃ (δ : ℝ) (k : ℕ), 0 < δ ∧ δ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D → ∀ K₀ A₀ H : ℝ, D + 4 ≤ A₀ →
        ∃ (C : ℝ) (W₀ : ℕ), ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
          W₀ ≤ p.W →
          ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
            IsPairSplitting p i model (splitS p) Pω →
            ∀ B : SplitState p i → ℝ → PairMatrix p i, IsWindowObservable p i k K₀ B →
              ∃ (Ωext : Set (SplitState p i)) (S : Set (SplitState p i × PairMatrix p i)),
                MeasurableSet S ∧ Pω Ωext ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) ∧
                (∀ om ∉ Ωext, gueMeasure (PairSite p i) (pairTime p (splitS p))
                    (Prod.mk om ⁻¹' S) ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
                ∀ x : SplitState p i × PairMatrix p i, x.1 ∉ Ωext → x ∉ S →
                  ∀ α : Fin p.N, IsBulkRank p ϑ α →
                    SmallPoleAt p i A₀ H x.1
                      (physicalOrderedEigenvalue p (assemble p i x.1 x.2) α) →
                    PartTwoGoodAt p i δ C ε B x α

/-- **The large-`ρ` branch of part (ii)** (compression to `w^⊥`): as
`PartTwoSmallRhoStatement`, at the ranks with `LargePoleAt A₀ H`, for every `A₀ ≥ D + 4` and
some `H` chosen after `A₀` (and `ε, D, K₀`). -/
def PartTwoLargeRhoStatement : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
    ∃ (δ : ℝ) (k : ℕ), 0 < δ ∧ δ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D → ∀ K₀ A₀ : ℝ, D + 4 ≤ A₀ →
        ∃ (H C : ℝ) (W₀ : ℕ), ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
          W₀ ≤ p.W →
          ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
            IsPairSplitting p i model (splitS p) Pω →
            ∀ B : SplitState p i → ℝ → PairMatrix p i, IsWindowObservable p i k K₀ B →
              ∃ (Ωext : Set (SplitState p i)) (S : Set (SplitState p i × PairMatrix p i)),
                MeasurableSet S ∧ Pω Ωext ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) ∧
                (∀ om ∉ Ωext, gueMeasure (PairSite p i) (pairTime p (splitS p))
                    (Prod.mk om ⁻¹' S) ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
                ∀ x : SplitState p i × PairMatrix p i, x.1 ∉ Ωext → x ∉ S →
                  ∀ α : Fin p.N, IsBulkRank p ϑ α →
                    LargePoleAt p i A₀ H x.1
                      (physicalOrderedEigenvalue p (assemble p i x.1 x.2) α) →
                    PartTwoGoodAt p i δ C ε B x α

/-!
## The reduction
-/

/-- The observable class of part (ii) shrinks as the derivative order grows. -/
theorem isWindowObservable_mono {k k' : ℕ} (hk : k ≤ k') {K₀ : ℝ}
    {B : SplitState p i → ℝ → PairMatrix p i} (h : IsWindowObservable p i k' K₀ B) :
    IsWindowObservable p i k K₀ B := by
  rcases h with h | ⟨f, ⟨h1, h2, h3, h4⟩, hB⟩
  · exact Or.inl h
  · exact Or.inr ⟨f, ⟨h1, h2, fun j hj => h3 j (hj.trans hk), h4⟩, hB⟩

/-- `ofReal (C₁ w) + ofReal (C₂ w) ≤ ofReal ((max C₁ 0 + max C₂ 0) w)` for `w ≥ 0`. -/
theorem ofReal_add_le_max {C₁ C₂ w : ℝ} (hw : 0 ≤ w) :
    ENNReal.ofReal (C₁ * w) + ENNReal.ofReal (C₂ * w) ≤
      ENNReal.ofReal ((max C₁ 0 + max C₂ 0) * w) := by
  rw [add_mul, ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) hw)
    (mul_nonneg (le_max_right _ _) hw)]
  exact add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hw))
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hw))

/-- **Part (ii) from its two branches**. At `A₀ = D + 4`, every selected
bulk energy has `σ(E) ≤ W^H` or `σ(E) > W^H` for the `H` of the large branch, so the union of
the two branch events (`CondSmall.union`) gives `PartTwoConditionalLargeStatement`, with common
constants `δ = min δ₁ δ₂`, `k = max k₁ k₂`, `W₀ = max W₁ W₂`, `C = max C₁ 0 + max C₂ 0`. -/
theorem partTwoConditionalLarge_of_branches (hS : PartTwoSmallRhoStatement)
    (hL : PartTwoLargeRhoStatement) : PartTwoConditionalLargeStatement := by
  intro b T ϑ hϑ
  obtain ⟨δ₁, k₁, hδ₁, hδ₁1, hS'⟩ := hS b T ϑ hϑ
  obtain ⟨δ₂, k₂, hδ₂, hδ₂1, hL'⟩ := hL b T ϑ hϑ
  refine ⟨min δ₁ δ₂, max k₁ k₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans_lt hδ₁1,
    fun ε hε D hD K₀ => ?_⟩
  obtain ⟨H, C₂, W₂, hL''⟩ := hL' ε hε D hD K₀ (D + 4) le_rfl
  obtain ⟨C₁, W₁, hS''⟩ := hS' ε hε D hD K₀ (D + 4) H le_rfl
  refine ⟨max C₁ 0 + max C₂ 0, max W₁ W₂, fun p hpb hn hW model i Pω hPω B hB => ?_⟩
  have hWr : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  set w : ℝ := (p.W : ℝ) ^ (-D) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hWr.le _
  set ν := gueMeasure (PairSite p i) (pairTime p (splitS p))
  obtain ⟨Ω₁, S₁, hS₁, hΩ₁, hsec₁, hgood₁⟩ := hS'' p hpb hn ((le_max_left _ _).trans hW) model i
    Pω hPω B (isWindowObservable_mono (le_max_left _ _) hB)
  obtain ⟨Ω₂, S₂, hS₂, hΩ₂, hsec₂, hgood₂⟩ := hL'' p hpb hn ((le_max_right _ _).trans hW) model i
    Pω hPω B (isWindowObservable_mono (le_max_right _ _) hB)
  have hc₁ : CondSmall Pω ν Ω₁ S₁ (ENNReal.ofReal (C₁ * w)) := ⟨hS₁, hΩ₁, hsec₁⟩
  have hc₂ : CondSmall Pω ν Ω₂ S₂ (ENNReal.ofReal (C₂ * w)) := ⟨hS₂, hΩ₂, hsec₂⟩
  have hall := (hc₁.union hc₂).mono (ofReal_add_le_max hw0)
  refine ⟨Ω₁ ∪ Ω₂, S₁ ∪ S₂, hall.1, hall.2.1, hall.2.2, fun x hx1 hx2 α hα => ?_⟩
  simp only [Set.mem_union, not_or] at hx1 hx2
  have hCle₁ : C₁ ≤ max C₁ 0 + max C₂ 0 := by
    have := le_max_left C₁ 0; have := le_max_right C₂ 0; linarith
  have hCle₂ : C₂ ≤ max C₁ 0 + max C₂ 0 := by
    have := le_max_left C₂ 0; have := le_max_right C₁ 0; linarith
  by_cases hsmall : SmallPoleAt p i (D + 4) H x.1
      (physicalOrderedEigenvalue p (assemble p i x.1 x.2) α)
  · exact partTwoGoodAt_mono (min_le_left _ _) hCle₁ (hgood₁ x hx1.1 hx2.1 α hα hsmall)
  · exact partTwoGoodAt_mono (min_le_right _ _) hCle₂
      (hgood₂ x hx1.2 hx2.2 α hα (not_le.mp hsmall))

/-- **Part (ii) of the physical local window from the two branches**:
`partTwoConditionalLarge_of_branches` and `physicalLocalWindow_partTwo_of_large`
(small `W` absorbed, Fubini, pair-law tilt). -/
theorem physicalLocalWindow_partTwo_of_branches (hS : PartTwoSmallRhoStatement)
    (hL : PartTwoLargeRhoStatement) : PhysicalLocalWindowPartTwoStatement :=
  physicalLocalWindow_partTwo_of_large (partTwoConditionalLarge_of_branches hS hL)

/-!
## Tools for the branches
-/

/-- The exterior is nonempty (`n ≥ 4`): the site `(i + 2, 0)`. -/
theorem exteriorSite_nonempty (p : Parameters) (i : ZMod p.n) : Nonempty (ExteriorSite p i) := by
  have h4 := p.n_ge_four
  have hne : ∀ m : ℕ, 0 < m → m < 4 → (m : ZMod p.n) ≠ 0 := by
    intro m hm0 hm4 h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact absurd (Nat.le_of_dvd hm0 h0) (by omega)
  refine ⟨⟨(i + 2, ⟨0, p.W_pos⟩), ?_⟩⟩
  rintro (h | h)
  · have : ((2 : ℕ) : ZMod p.n) = 0 := by
      have h' : i + 2 = i + 0 := by simpa using h
      exact_mod_cast add_left_cancel h'
    exact hne 2 (by norm_num) (by norm_num) this
  · have : ((1 : ℕ) : ZMod p.n) = 0 := by
      have h' : (i + 1) + 1 = (i + 1) + 0 := by
        rw [add_zero, add_assoc]; exact_mod_cast h
      exact_mod_cast add_left_cancel h'
    exact hne 1 (by norm_num) (by norm_num) this

/-- **A separated pole label off crowding**: if `H_R` is Hermitian
and has fewer than two eigenvalues in `[E - ε₀, E + ε₀]` (the crowding clause of
`ExteriorGood`), some `j₀` is alone within `ε₀` of `E`. -/
theorem exists_poleSeparated_of_crowding {om : SplitState p i} (hH : om.1.IsHermitian)
    {ε₀ E : ℝ}
    (hcr : spectralSum om.1 (ProofCrowding.iccInd (E - ε₀) (E + ε₀)) < 2) :
    ∃ j₀ : ExteriorSite p i, PoleSeparated ε₀ hH j₀ E := by
  have : Nonempty (ExteriorSite p i) := exteriorSite_nonempty p i
  refine exists_poleSeparated hH ?_
  have h := BlockBand.LocalWindow.ProofCount.nearSet_card_eq hH ε₀ E
  have h' : ((BlockBand.LocalWindow.ProofCount.nearSet ε₀ hH E).card : ℝ) < 2 := by
    rw [h]; exact hcr
  have : (BlockBand.LocalWindow.ProofCount.nearSet ε₀ hH E).card < 2 := by exact_mod_cast h'
  omega

/-- `PoleSeparated` is monotone in the radius. -/
theorem poleSeparated_mono {α : Type} [Fintype α] [DecidableEq α] {M : Matrix α α ℂ}
    {ε ε' : ℝ} (hH : M.IsHermitian) {j₀ : α} {E : ℝ} (hε : ε' ≤ ε)
    (h : PoleSeparated ε hH j₀ E) : PoleSeparated ε' hH j₀ E :=
  fun j hj => hε.trans_lt (h j hj)

/-- **Shift of the pole interval**: a label separated at radius `ε + η` from `E`
is separated at radius `ε` from every `E'` with `|E - E'| ≤ η`.
-/
theorem poleSeparated_shift {α : Type} [Fintype α] [DecidableEq α] {M : Matrix α α ℂ}
    {ε η : ℝ} (hH : M.IsHermitian) {j₀ : α} {E E' : ℝ} (h : PoleSeparated (ε + η) hH j₀ E)
    (hEE : |E - E'| ≤ η) : PoleSeparated ε hH j₀ E' := by
  intro j hj
  have h1 := h j hj
  have h2 : |hH.eigenvalues j - E| ≤ |hH.eigenvalues j - E'| + |E' - E| := by
    have := abs_add_le (hH.eigenvalues j - E') (E' - E)
    rwa [show hH.eigenvalues j - E' + (E' - E) = hH.eigenvalues j - E by ring] at this
  rw [abs_sub_comm E' E] at h2
  linarith

/-- **`σ = |ρ - ρ̂|`**: at a nonpole energy of the pole interval
of `j₀`, `‖F(E) - F̂(E)‖ = |ρ(E) - ρ̂(E)|` (`F - F̂ = (ρ - ρ̂)ww*`, `w` a unit vector). -/
theorem opNorm_physicalCoareaF_sub_truncF_eq (om : SplitState p i) (hH : om.1.IsHermitian)
    (j₀ : ExteriorSite p i) {ε E : ℝ} (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    (hsep : PoleSeparated ε hH j₀ E) :
    singularPart p i ε om E = |poleRho hH j₀ om.2.1 E - poleRhoHat ε hH j₀ om.2.1 E| := by
  have : Nonempty (PairSite p i) := pairSite_nonempty p i
  unfold singularPart
  rw [physicalCoareaF_eq_truncF_add ε hH j₀ om.2.1 om.2.2 hdet hsep, add_sub_cancel_left]
  exact opNorm_smul_vecMulVec_unit (sqNorm_poleDir hH j₀ om.2.1) _

/-- `|ρ̂(E)| ≤ ‖C*φ‖²/ε` (`|g_ε| ≤ ε⁻¹`). -/
theorem abs_poleRhoHat_le {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {M : Matrix α α ℂ} {ε : ℝ} (hε : 0 < ε) (hH : M.IsHermitian) (j₀ : α) (C : Matrix α β ℂ)
    (E : ℝ) : |poleRhoHat ε hH j₀ C E| ≤ sqNorm (poleCoupling hH j₀ C) / ε := by
  unfold poleRhoHat
  rw [abs_mul, abs_neg, abs_of_nonneg (sqNorm_nonneg _), div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (ProofCount.abs_truncInv_le hε _) (sqNorm_nonneg _)

/-- **Small branch, in terms of `ρ`**: with `SmallPoleAt A₀ H` at a nonpole energy
of the pole interval of `j₀` (radius `W^{-A₀}`), `|ρ(E)| ≤ W^H + ‖C*φ‖² W^{A₀}`. -/
theorem abs_poleRho_le_of_smallPoleAt (om : SplitState p i) (hH : om.1.IsHermitian)
    (j₀ : ExteriorSite p i) {A₀ H E : ℝ} (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    (hsep : PoleSeparated ((p.W : ℝ) ^ (-A₀)) hH j₀ E) (hs : SmallPoleAt p i A₀ H om E) :
    |poleRho hH j₀ om.2.1 E| ≤
      (p.W : ℝ) ^ H + sqNorm (poleCoupling hH j₀ om.2.1) / (p.W : ℝ) ^ (-A₀) := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hσ := opNorm_physicalCoareaF_sub_truncF_eq om hH j₀ hdet hsep
  have hhat := abs_poleRhoHat_le (Real.rpow_pos_of_pos hW (-A₀)) hH j₀ om.2.1 E
  unfold SmallPoleAt at hs
  rw [hσ] at hs
  have := abs_sub_abs_le_abs_sub (poleRho hH j₀ om.2.1 E)
    (poleRhoHat ((p.W : ℝ) ^ (-A₀)) hH j₀ om.2.1 E)
  linarith

/-- **Large branch, in terms of `ρ`**: with `LargePoleAt A₀ H` at a nonpole energy
of the pole interval of `j₀`, `|ρ(E)| > W^H - ‖C*φ‖² W^{A₀}`. -/
theorem abs_poleRho_gt_of_largePoleAt (om : SplitState p i) (hH : om.1.IsHermitian)
    (j₀ : ExteriorSite p i) {A₀ H E : ℝ} (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    (hsep : PoleSeparated ((p.W : ℝ) ^ (-A₀)) hH j₀ E) (hl : LargePoleAt p i A₀ H om E) :
    (p.W : ℝ) ^ H - sqNorm (poleCoupling hH j₀ om.2.1) / (p.W : ℝ) ^ (-A₀) <
      |poleRho hH j₀ om.2.1 E| := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hσ := opNorm_physicalCoareaF_sub_truncF_eq om hH j₀ hdet hsep
  have hhat := abs_poleRhoHat_le (Real.rpow_pos_of_pos hW (-A₀)) hH j₀ om.2.1 E
  unfold LargePoleAt at hl
  rw [hσ] at hl
  have := abs_sub (poleRho hH j₀ om.2.1 E) (poleRhoHat ((p.W : ℝ) ^ (-A₀)) hH j₀ om.2.1 E)
  linarith

end BlockBand.LocalWindow.ProofPartTwo
