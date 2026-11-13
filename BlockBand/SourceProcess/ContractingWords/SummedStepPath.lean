module

public import BlockBand.SourceProcess.ContractingWords.SummedEval

/-!
# The two increment formulas at one step of the path

`first_path`, `second_path`: `first_abstract` and `second_abstract` applied at one step `j → j+1`
of the growth path, with the word values as variables, the survival event `{j < σ_K}` and the
dominating variable `domM`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory MvPolynomial
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

variable {W nT nI : ℕ}

/-- **The first increment formula at one step.** -/
theorem first_path (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (j : ℕ)
    (Φ : TracePoly nT nI) {Cf : TracePoly nT nI → ℝ} {Nf : TracePoly nT nI → ℕ}
    (hCf : ∀ Ψ, 0 ≤ Cf Ψ) (hTf : ∀ Ψ, TayBound Φ.vars Ψ (Cf Ψ) (Nf Ψ)) {Nb : ℕ}
    (hmom : ∀ n ≤ Nb, ∫⁻ ω, ENNReal.ofReal (domM b E k q j Φ.vars ω) ^ n
      ∂growthPathLaw W b ≠ ⊤)
    (hN1 : ∀ w ∈ Φ.vars, Nf (pderiv w Φ) + 1 ≤ Nb)
    (hN2 : ∀ w ∈ Φ.vars, ∀ v ∈ Φ.vars, Nf (pderiv v (pderiv w Φ)) + 2 ≤ Nb)
    (hN3 : Nf Φ + 3 ≤ Nb) {ε₁ ε₂ δ : ℝ≥0∞}
    (h1 : ∀ w ∈ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
      (growthPathLaw W b)[(alive b E k q K ε W j).indicator (wordInc b E k q W j w) |
        growthSigma W j] ω -
      (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordDrift (transportD0 b E) w +
        MvPolynomial.C (wordInjection b q (stepTime W j) w))) 2 (growthPathLaw W b) ≤ ε₁)
    (h2 : ∀ p ∈ Φ.vars ×ˢ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
      (growthPathLaw W b)[(alive b E k q K ε W j).indicator
        (fun ω => wordInc b E k q W j p.1 ω * wordInc b E k q W j p.2 ω) | growthSigma W j] ω -
      (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCov (transportD0 b E) p.1 p.2))
        2 (growthPathLaw W b) ≤ ε₂)
    (h3 : ∀ w ∈ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator (wordInc b E k q W j w)) 6
      (growthPathLaw W b) ≤ δ) :
    ∫⁻ ω, ‖(alive b E k q K ε W j).indicator (fun ω =>
        (growthPathLaw W b)[(alive b E k q K ε W j).indicator (fun ω =>
          polyValue b E k q W (j + 1) ω Φ - polyValue b E k q W j ω Φ) | growthSigma W j] ω -
        (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordGenerator b E q (stepTime W j) Φ)) ω‖ₑ
        ∂growthPathLaw W b ≤
      (∑ w ∈ Φ.vars, ENNReal.ofReal (Cf (pderiv w Φ)) *
          momT (growthPathLaw W b) (domM b E k q j Φ.vars) (Nf (pderiv w Φ))) * ε₁ +
        (∑ p ∈ Φ.vars ×ˢ Φ.vars, ENNReal.ofReal (Cf (pderiv p.2 (pderiv p.1 Φ))) *
          momT (growthPathLaw W b) (domM b E k q j Φ.vars) (Nf (pderiv p.2 (pderiv p.1 Φ)))) *
          ε₂ +
        ENNReal.ofReal (Cf Φ * (Φ.vars.card : ℝ) ^ 2) * (Φ.vars.card *
          (momT (growthPathLaw W b) (domM b E k q j Φ.vars) (Nf Φ) * δ ^ (3 : ℝ))) := by
  have := first_abstract (μ := growthPathLaw W b) (growthSigma_le j)
    (measurableSet_alive b E k q K ε j) (subset_refl Φ.vars)
    (x := fun ω => wordValue b E k q W j ω) (x' := fun ω => wordValue b E k q W (j + 1) ω)
    (fun w => measurable_wordValue_past b E k q j w)
    (fun w => FullSourceStops.measurable_wordValue b E k q (j + 1) w)
    (measurable_domM b E k q j Φ.vars) (one_le_domM b E k q j Φ.vars)
    (dominated_domM b E k q j Φ.vars) (Cg := fun w => Cf (pderiv w Φ))
    (Ng := fun w => Nf (pderiv w Φ)) (fun w => hCf _) (fun w _ => hTf _)
    (CG := fun w v => Cf (pderiv v (pderiv w Φ))) (NG := fun w v => Nf (pderiv v (pderiv w Φ)))
    (fun w v => hCf _) (fun w _ v _ => hTf _) (hCf Φ) (hTf Φ) hmom hN1 hN2 hN3
    (fun w ω => (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordDrift (transportD0 b E) w +
      MvPolynomial.C (wordInjection b q (stepTime W j) w)))
    (fun w _ =>
      (measurable_const.mul
        (FullSourceStops.measurable_polyValue b E k q j _)).aestronglyMeasurable)
    (fun p ω => (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCov (transportD0 b E) p.1 p.2))
    (fun p _ =>
      (measurable_const.mul
        (FullSourceStops.measurable_polyValue b E k q j _)).aestronglyMeasurable)
    h1 h2 h3
  rw [← eLpNorm_one_eq_lintegral_enorm]
  convert this using 4
  rename_i ω
  exact congrArg₂ (· - ·) rfl
    (eval_wordGenerator b E q (stepTime W j) Φ (wordValue b E k q W j ω) _)
  exact ((stronglyMeasurable_condExp.mono (growthSigma_le j)).aestronglyMeasurable.sub
    (measurable_const.mul
      (FullSourceStops.measurable_polyValue b E k q j _)).aestronglyMeasurable).indicator
    (growthSigma_le j _ (measurableSet_alive b E k q K ε j))

/-- **The second increment formula at one step.** -/
theorem second_path (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (j : ℕ)
    (Φ : TracePoly nT nI) {Cf : TracePoly nT nI → ℝ} {Nf : TracePoly nT nI → ℕ}
    (hCf : ∀ Ψ, 0 ≤ Cf Ψ) (hTf : ∀ Ψ, TayBound Φ.vars Ψ (Cf Ψ) (Nf Ψ)) {Nb : ℕ}
    (hmom : ∀ n ≤ Nb, ∫⁻ ω, ENNReal.ofReal (domM b E k q j Φ.vars ω) ^ n
      ∂growthPathLaw W b ≠ ⊤)
    (hN1 : ∀ w ∈ Φ.vars, ∀ v ∈ Φ.vars, Nf (pderiv w Φ) + Nf (pderiv v Φ) + 2 ≤ Nb)
    (hN3 : 2 * Nf Φ + 3 + 3 ≤ Nb) {ε₂ δ : ℝ≥0∞}
    (h2 : ∀ p ∈ Φ.vars ×ˢ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
      (growthPathLaw W b)[(alive b E k q K ε W j).indicator
        (fun ω => wordInc b E k q W j p.1 ω * wordInc b E k q W j p.2 ω) | growthSigma W j] ω -
      (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCov (transportD0 b E) p.1 p.2))
        2 (growthPathLaw W b) ≤ ε₂)
    (h3 : ∀ w ∈ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator (wordInc b E k q W j w)) 6
      (growthPathLaw W b) ≤ δ) :
    ∫⁻ ω, ‖(alive b E k q K ε W j).indicator (fun ω =>
        (growthPathLaw W b)[(alive b E k q K ε W j).indicator (fun ω =>
          (polyValue b E k q W (j + 1) ω Φ - polyValue b E k q W j ω Φ) ^ 2) |
            growthSigma W j] ω -
        (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Φ)) ω‖ₑ ∂growthPathLaw W b ≤
      (∑ p ∈ Φ.vars ×ˢ Φ.vars, ENNReal.ofReal (Cf (pderiv p.1 Φ) * Cf (pderiv p.2 Φ)) *
          momT (growthPathLaw W b) (domM b E k q j Φ.vars)
            (Nf (pderiv p.1 Φ) + Nf (pderiv p.2 Φ))) * ε₂ +
        ENNReal.ofReal (3 * Cf Φ ^ 2 * (1 + Φ.vars.card) ^ 3 * (Φ.vars.card : ℝ) ^ 2) *
          (Φ.vars.card * (momT (growthPathLaw W b) (domM b E k q j Φ.vars) (2 * Nf Φ + 3) *
            δ ^ (3 : ℝ))) := by
  have := second_abstract (μ := growthPathLaw W b) (growthSigma_le j)
    (measurableSet_alive b E k q K ε j) (subset_refl Φ.vars)
    (x := fun ω => wordValue b E k q W j ω) (x' := fun ω => wordValue b E k q W (j + 1) ω)
    (fun w => measurable_wordValue_past b E k q j w)
    (fun w => FullSourceStops.measurable_wordValue b E k q (j + 1) w)
    (measurable_domM b E k q j Φ.vars) (one_le_domM b E k q j Φ.vars)
    (dominated_domM b E k q j Φ.vars) (Cg := fun w => Cf (pderiv w Φ))
    (Ng := fun w => Nf (pderiv w Φ)) (fun w => hCf _) (fun w _ => hTf _) (hCf Φ) (hTf Φ)
    hmom hN1 hN3
    (fun p ω => (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCov (transportD0 b E) p.1 p.2))
    (fun p _ =>
      (measurable_const.mul
        (FullSourceStops.measurable_polyValue b E k q j _)).aestronglyMeasurable)
    h2 h3
  rw [← eLpNorm_one_eq_lintegral_enorm]
  convert this using 4
  rename_i ω
  exact congrArg₂ (· - ·) rfl (eval_wordCarre b E Φ (wordValue b E k q W j ω) _)
  exact ((stronglyMeasurable_condExp.mono (growthSigma_le j)).aestronglyMeasurable.sub
    (measurable_const.mul
      (FullSourceStops.measurable_polyValue b E k q j _)).aestronglyMeasurable).indicator
    (growthSigma_le j _ (measurableSet_alive b E k q K ε j))

end BlockBand.SourceProcess.ContractingWords
