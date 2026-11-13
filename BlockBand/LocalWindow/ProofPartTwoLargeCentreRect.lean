module

public import BlockBand.LocalWindow.ProofPartTwoLargeCentreCert

/-!
# The uniform root rectangles of the large-`ρ` branch

The three root rectangles consumed by `largeRho_hcen` / `largeRho_point_le` (the exact `K₀(E)`,
its compressed regular part `U*M_E U`, and the grid deformation `compRegM e`), and the root
rectangle at the window centre `μ` consumed by the compressed ETH
(`gue_largeRhoCompBad_section_le`), all from the truncated certificate (uniformly on the
label event, from the certificate at the grid energy and at the exact energy).

## Main results

* `pairRootRectangle_mono`, `rootRectangle_mono` (smaller radius and lower bound),
  `rootRectangle_shift` (centre `0`, radius `r` to centre `μ`, radius `r'`, `|μ| + r' ≤ r`).
* **`largeRho_rectangles`**: constants `ε_c, r, s₀, v₀` (from `pairRootRectangle_schurK0_pole`
  and `compressRootRectangle_family`, combined by `min`) such that at a simple label `j₀`
  separated at `ε` from a bulk energy `x` with `certErrHat ε ω x ≤ ε_c`, `8/(W s√κ) ≤ ε_c` and
  `s ≤ 2W s₀`: `RootRectangle (U*(F_reg(x) - x)U) s' 0 r v₀` and, on the label event,
  `RootRectangle (compRegM x) s' 0 r v₀` (`s' = compressVar p s`, `s = splitS p`); if moreover
  `x` is not a pole, `PairRootRectangle K₀(x) s 0 r v₀`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Layers
open BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open BlockBand.LocalWindow.ProofCertificate BlockBand.External
open scoped Matrix.Norms.L2Operator

/-!
## Monotonicity and shift
-/

theorem rootRectangle_mono {N : ℕ} {F : Matrix (Fin N) (Fin N) ℂ} {s E₀ r r' v₀ v₀' : ℝ}
    (h : RootRectangle F s E₀ r v₀) (hr : r' ≤ r) (hv : v₀' ≤ v₀) :
    RootRectangle F s E₀ r' v₀' := fun x hx η hη hη1 => by
  obtain ⟨m, hm, hmv⟩ := h x (hx.trans hr) η hη hη1
  exact ⟨m, hm, hv.trans hmv⟩

theorem pairRootRectangle_mono {p : Parameters} {i : ZMod p.n} {K : PairMatrix p i}
    {s E₀ r r' v₀ v₀' : ℝ} (h : PairRootRectangle K s E₀ r v₀) (hr : r' ≤ r) (hv : v₀' ≤ v₀) :
    PairRootRectangle K s E₀ r' v₀' := fun x hx η hη hη1 => by
  obtain ⟨m, hm, hmv⟩ := h x (hx.trans hr) η hη hη1
  exact ⟨m, hm, hv.trans hmv⟩

/-- A root rectangle around `0` of radius `r` contains the rectangle around `μ` of radius `r'`
when `|μ| + r' ≤ r`. -/
theorem rootRectangle_shift {N : ℕ} {F : Matrix (Fin N) (Fin N) ℂ} {s r r' v₀ μ : ℝ}
    (h : RootRectangle F s 0 r v₀) (hμ : |μ| + r' ≤ r) : RootRectangle F s μ r' v₀ :=
  fun x hx η hη hη1 => h x (by
    rw [sub_zero]
    calc |x| = |(x - μ) + μ| := by rw [sub_add_cancel]
      _ ≤ |x - μ| + |μ| := abs_add_le _ _
      _ ≤ r := by linarith) η hη hη1

/-!
## The uniform rectangles
-/

variable {p : Parameters} {i : ZMod p.n}

attribute [local instance] pairSite_nonempty

/-- **The uniform root rectangles of the large-`ρ` branch**. -/
theorem largeRho_rectangles (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hκ : 0 < κ) :
    ∃ εc r s₀ v₀ : ℝ, 0 < εc ∧ 0 < r ∧ 0 < s₀ ∧ 0 < v₀ ∧
      ∀ p : Parameters, p.b = b → ∀ (i : ZMod p.n) (om : SplitState p i)
        (_hV : om.2.2.IsHermitian) (ε x : ℝ), x ∈ bulkInterval κ →
        certErrHat ε p i om x ≤ εc → 8 / ((p.W : ℝ) * splitS p * Real.sqrt κ) ≤ εc →
        splitS p ≤ 2 * (p.W : ℝ) * s₀ →
        ∀ (sel : CEH.EigenpairSelection (2 * p.W)) (hH : om.1.IsHermitian)
          (j₀ : ExteriorSite p i), PoleSimple hH j₀ → PoleSeparated ε hH j₀ x →
          RootRectangle ((poleIsometry sel j₀ om)ᴴ *
              (regF hH j₀ om.2.1 om.2.2 x - (x : ℂ) • 1) * poleIsometry sel j₀ om)
            (compressVar p (splitS p)) 0 r v₀ ∧
          RootRectangle (compRegM sel ε j₀ x om) (compressVar p (splitS p)) 0 r v₀ ∧
          ((om.1 - (x : ℂ) • 1).det ≠ 0 →
            PairRootRectangle (schurK0 p i om x) (splitS p) 0 r v₀) := by
  obtain ⟨εc₁, r₁, s₁, v₁, hεc₁, hr₁, hs₁, hv₁, h₁⟩ := pairRootRectangle_schurK0_pole b κ hb hb' hκ
  obtain ⟨εc₂, r₂, s₂, v₂, hεc₂, hr₂, hs₂, hv₂, h₂⟩ := compressRootRectangle_family b κ hb hb' hκ
  refine ⟨min εc₁ εc₂, min r₁ r₂, min s₁ s₂, min v₁ v₂, lt_min hεc₁ hεc₂, lt_min hr₁ hr₂,
    lt_min hs₁ hs₂, lt_min hv₁ hv₂, fun p hpb i om hV ε x hx hcert hW hs sel hH j₀ hsim hsep => ?_⟩
  have hs0 : 0 < splitS p := lt_min p.c_pos p.b_pos
  have hW0 : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hc₂ : certErrHat ε p i om x ≤ εc₂ := hcert.trans (min_le_right _ _)
  have hW₂ : 8 / ((p.W : ℝ) * splitS p * Real.sqrt κ) ≤ εc₂ := hW.trans (min_le_right _ _)
  obtain ⟨hs1, hs2⟩ := compressVar_mem_of_le (p := p) hs0.le
    (hs.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)))
  obtain ⟨hUU, -, hcompl⟩ := poleIsometry_spec sel hH hsim
  have hww : 1 - poleIsometry sel j₀ om * (poleIsometry sel j₀ om)ᴴ =
      vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) :=
    (eq_sub_of_add_eq' hcompl).symm
  have hD := regF_add_rankOne_sub_truncF ε hH j₀ om.2.1 om.2.2 hsep 0
  rw [Complex.ofReal_zero, zero_smul, add_zero] at hD
  have hcomp := h₂ p hpb i om hV ε x hx hc₂ hW₂ (regF hH j₀ om.2.1 om.2.2 x)
    (isHermitian_regF hH j₀ om.2.1 hV x) _ _ hD (poleIsometry sel j₀ om) _ hUU hww _ hs1 hs2
  have hcomp' := rootRectangle_mono hcomp (min_le_right r₁ r₂) (min_le_right v₁ v₂)
  refine ⟨hcomp', ?_, fun hdet => ?_⟩
  · rw [compRegM_eq sel ε hH hV hsim hsep]; exact hcomp'
  · have h2W : 2 / ((p.W : ℝ) * splitS p * Real.sqrt κ) ≤ εc₁ := by
      refine le_trans ?_ (hW.trans (min_le_left _ _))
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    have hK := h₁ p hpb i om hV ε x hx (hcert.trans (min_le_left _ _)) h2W hH j₀ hsep hdet
      (splitS p) (by linarith) le_rfl
    exact pairRootRectangle_mono hK (min_le_left _ _) (min_le_left _ _)

end BlockBand.LocalWindow.ProofPartTwo
