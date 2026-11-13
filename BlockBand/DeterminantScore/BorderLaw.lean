module

public import BlockBand.DeterminantScore.BorderLawPolar
public import BlockBand.DeterminantScore.BorderLawInterlace
public import BlockBand.DeterminantScore.BorderLawJacobian
public import BlockBand.DeterminantScore.WeylIntegrationComplexUnitary

/-!
# The bordered-matrix law for a diagonal corner

`diagonalBorderLaw_holds` proves `WeylIntegration.DiagonalBorderLawStatement`: for strictly
increasing `μ` and measurable `g ≥ 0`,
`∫_{ℂ^n} ∫_ℝ g(λ([[diag μ, v],[v*, a]])) da dv = π^n ∫_{λ ≻ μ} (Δ(λ)/Δ(μ)) g(λ) dλ`
(Lebesgue measures; `λ ≻ μ` strict interlacing). Hence `weylIntegration_holds`, the Weyl
integration formula `EigenDensity.WeylIntegrationStatement` without hypotheses.

Proof:
1. the spectrum depends on `v` only through `r = (|v_i|²)` (`freshEigenvalue_borderHerm_diagonal`,
   arrowhead characteristic polynomial);
2. polar coordinates `∫_{ℂ^n} F(|v|²) dv = π^n ∫_{(0,∞)^n} F`;
3. Fubini and `Fin (n+1) ≅ Fin n ⊕ {last}` (`lintegral_posOrthant_prod`);
4. the change of variables `λ ↦ borderCoord μ λ = (r(λ), a(λ))`, injective on the interlacing set
   with image `(0,∞)^n × ℝ` (`image_borderCoord`) and `|det D borderCoord| = Δ(λ)/Δ(μ)`, through
   `lintegral_image_eq_lintegral_abs_det_fderiv_mul`; on the interlacing set the spectrum at
   `borderCoord μ λ` is `λ` (`borderEig_borderCoord`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal

variable {n : ℕ}

/-- The positive orthant `(0, ∞)^n`. -/
def posOrthant (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ => Ioi 0

/-- The half-space `{y : y_i > 0 for i < n}` of `Fin (n+1) → ℝ` (last coordinate free). -/
def posBorder (n : ℕ) : Set (Fin (n + 1) → ℝ) := {y | ∀ i : Fin n, 0 < y i.castSucc}

/-- `(0,∞)^n` is measurable. -/
theorem measurableSet_posOrthant : MeasurableSet (posOrthant n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

/-- `posBorder n` is measurable. -/
theorem measurableSet_posBorder : MeasurableSet (posBorder n) := by
  have : posBorder n = ⋂ i : Fin n, {y : Fin (n + 1) → ℝ | 0 < y i.castSucc} := by
    ext y; simp [posBorder]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply _)

/-- Fubini and `Fin (n+1) ≅ Fin n ⊕ {last}`:
`∫_{(0,∞)^n} ∫_ℝ G(r, a) da dr = ∫_{posBorder} G(init y, y_last) dy`. -/
theorem lintegral_posOrthant_prod {G : (Fin n → ℝ) → ℝ → ℝ≥0∞}
    (hG : Measurable fun p : (Fin n → ℝ) × ℝ => G p.1 p.2) :
    ∫⁻ r in posOrthant n, ∫⁻ a, G r a =
      ∫⁻ y in posBorder n, G (Fin.init y) (y (Fin.last n)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last n)
  set F : ℝ × (Fin n → ℝ) → ℝ≥0∞ :=
    (Prod.snd ⁻¹' posOrthant n).indicator fun p => G p.2 p.1 with hFdef
  have hF : Measurable F :=
    (hG.comp measurable_swap).indicator (measurable_snd measurableSet_posOrthant)
  have hFe : (posBorder n).indicator (fun y => G (Fin.init y) (y (Fin.last n))) = F ∘ e := by
    funext y
    have he1 : e y = (y (Fin.last n), Fin.init y) := by
      simp [e, MeasurableEquiv.piFinSuccAbove]
    have hmem : y ∈ posBorder n ↔ (y (Fin.last n), Fin.init y) ∈ Prod.snd ⁻¹' posOrthant n := by
      simp [posBorder, posOrthant, Fin.init]
    simp only [Function.comp_apply, he1, hFdef]
    by_cases hy : y ∈ posBorder n
    · rw [indicator_of_mem hy, indicator_of_mem (hmem.1 hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy (hmem.2 h))]
  rw [← lintegral_indicator measurableSet_posBorder, hFe]
  rw [show (∫⁻ y, (F ∘ e) y) = ∫⁻ y, F (e y) from rfl,
    he.lintegral_comp_emb e.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod _ hF.aemeasurable,
    lintegral_lintegral_swap (f := fun a r => F (a, r)) hF.aemeasurable,
    ← lintegral_indicator measurableSet_posOrthant]
  refine lintegral_congr fun r => ?_
  by_cases hr : r ∈ posOrthant n
  · simp [hFdef, Set.indicator, hr]
  · simp [hFdef, Set.indicator, hr]

/-- The strictly interlacing set is measurable. -/
theorem measurableSet_interlaceSet (μ : Fin n → ℝ) : MeasurableSet (interlaceSet μ) :=
  measurableSet_interlacePairs.preimage measurable_prodMk_left

/-- `(r, a) ↦ spectrum` inverts `borderCoord μ` on the interlacing set. -/
theorem borderEig_borderCoord {μ : Fin n → ℝ} (hμ : StrictMono μ) {lam : Fin (n + 1) → ℝ}
    (hlam : lam ∈ interlaceSet μ) :
    borderEig μ (Fin.init (borderCoord μ lam)) (borderCoord μ lam (Fin.last n)) = lam := by
  have h1 : Fin.init (borderCoord μ lam) = arrowWeight μ lam := by
    funext i; simp [borderCoord, Fin.init]
  have h2 : borderCoord μ lam (Fin.last n) = arrowCorner μ lam := by simp [borderCoord]
  rw [h1, h2]
  exact borderEig_arrowCoord hμ hlam

/-- `borderCoord μ` maps the interlacing set onto `(0,∞)^n × ℝ`. -/
theorem image_borderCoord {μ : Fin n → ℝ} (hμ : StrictMono μ) :
    borderCoord μ '' interlaceSet μ = posBorder n := by
  ext y
  constructor
  · rintro ⟨lam, hlam, rfl⟩ i
    simpa [borderCoord] using arrowWeight_pos hμ hlam i
  · intro hy
    obtain ⟨h1, h2, h3⟩ := borderEig_spec hμ (r := Fin.init y) hy (y (Fin.last n))
    refine ⟨_, h1, ?_⟩
    rw [borderCoord, h2, h3]
    exact Fin.snoc_init_self y

/-- Joint measurability of `(r, a) ↦ borderEig μ r a`. -/
theorem measurable_borderEig (μ : Fin n → ℝ) :
    Measurable fun p : (Fin n → ℝ) × ℝ => borderEig μ p.1 p.2 := by
  have hc : Continuous fun p : (Fin n → ℝ) × ℝ =>
      ((fun i => ((Real.sqrt (p.1 i) : ℝ) : ℂ)), p.2) :=
    (continuous_pi fun i => Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp ((continuous_apply i).comp continuous_fst))).prodMk continuous_snd
  exact EigenDensity.measurable_freshEigs.comp ((continuous_borderHerm _).comp hc).measurable

/-- **The bordered-matrix law for a diagonal corner** (`DiagonalBorderLawStatement`). -/
theorem diagonalBorderLaw_holds : DiagonalBorderLawStatement := by
  intro n g hg μ hμ
  simp_rw [freshEigenvalue_borderHerm_diagonal μ]
  have hGm : Measurable fun p : (Fin n → ℝ) × ℝ => g (borderEig μ p.1 p.2) :=
    hg.comp (measurable_borderEig μ)
  refine (lintegral_normSq_pi (fun r => ∫⁻ a, g (borderEig μ r a))
    hGm.lintegral_prod_right').trans ?_
  congr 1
  have hinj : InjOn (borderCoord μ) (interlaceSet μ) := fun l1 h1 l2 h2 heq => by
    rw [← borderEig_borderCoord hμ h1, ← borderEig_borderCoord hμ h2, heq]
  rw [show (univ.pi fun _ => Ioi 0 : Set (Fin n → ℝ)) = posOrthant n from rfl,
    lintegral_posOrthant_prod hGm, ← image_borderCoord hμ,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_interlaceSet μ)
      (fun lam _ => (hasFDerivAt_borderCoord μ lam).hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun (measurableSet_interlaceSet μ) fun lam hlam => ?_
  rw [det_borderJac_toCLM, abs_det_borderJac hμ (strictMono_of_mem_interlaceSet hlam),
    borderEig_borderCoord hμ hlam]

/-- **The Weyl integration formula** (`EigenDensity.WeylIntegrationStatement`), unconditional. -/
theorem weylIntegration_holds : EigenDensity.WeylIntegrationStatement :=
  weylIntegration_of_diagonalBorderLaw diagonalBorderLaw_holds

end BlockBand.DeterminantScore.WeylIntegration
