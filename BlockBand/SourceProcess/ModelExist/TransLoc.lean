module

public import BlockBand.SourceProcess.ModelExist.TransDef

/-!
# The transformed compensated processes are complex `LocMart`s

`N` are the
compensated coordinates of a progressive Gram martingale-problem solution `𝒢`.

* `cLocMart_bornRep`: `Σ c_e (N − N^{θ_e})` has drift `0` (`CLocMart.shift`, unbounded weights);
* `cLocMart_bornRep_mul`: the product of two has drift `Σ 1{θ_e ∨ θ_e' < s} c_e c_e' Γ'(𝒢_s)`
  (`CLocMart.pair`, then the `𝓕_{θ_e ∨ θ_e'}`-measurable weight `c_e c_e'`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
theorem stopped_pair_zero (N N' : ℝ≥0 → Ω → ℂ) (σ σ' : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (fun t ω => (N t ω - stoppedProcess N σ t ω) *
      (N' t ω - stoppedProcess N' σ' t ω)) (fun ω => max (σ ω) (σ' ω)) t ω = 0 := by
  simp only [stoppedProcess_eq_stopTime]
  rcases le_max_iff.1 (stopTime_le_self' (max (σ ω) (σ' ω)) t) with h | h
  · rw [stopTime_eq_self h, sub_self, zero_mul]
  · rw [stopTime_eq_self h, sub_self, mul_zero]

variable {c c' : Type*} [Fintype c'] {D0 : ℝ}
  {D' : Matrix c' c' ℂ} {𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ}
  {θ : c → Ω → ℝ≥0} {lam : c → Ω → c' → ℂ}

section
variable (h𝒢 : IsGramMartingaleSolution Q 𝓖 D0 D' 𝒢) (hp : IsStronglyProgressive 𝓖 𝒢)
  (hθ : ∀ y, Measurable[𝓖 0] (θ y))
  (hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace] (lam y))
include h𝒢 hp hlam

/-- **The transformed compensated coordinates have drift `0`.** -/
theorem cLocMart_bornRep (e : Fin 2 × c × c) :
    CLocMart Q 𝓖 (bornRep θ lam (gramCompensated D0 D' 𝒢) e) (fun _ _ => 0) := by
  have h := fun x x' => (gramLoc_drift h𝒢 hp (e.1, x, x')).shift (isStoppingTime_bTime hθ e)
    (stronglyMeasurable_bCoef hθ hlam e x x')
  have h2 := CLocMart.sum univ fun x _ => CLocMart.sum univ fun x' _ => h x x'
  convert h2 using 1
  · rfl
  · funext s ω
    symm
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x' _ => ?_
    split_ifs <;> simp

/-- **Products of transformed compensated coordinates.** -/
theorem cLocMart_bornRep_mul (e e' : Fin 2 × c × c) :
    CLocMart Q 𝓖 (fun t ω => bornRep θ lam (gramCompensated D0 D' 𝒢) e t ω *
        bornRep θ lam (gramCompensated D0 D' 𝒢) e' t ω)
      (fun s ω => ∑ x, ∑ x', ∑ z, ∑ z', if max (bTime θ e ω) (bTime θ e' ω) < (s : WithTop ℝ≥0)
        then bCoef lam e ω x x' * bCoef lam e' ω z z' *
          gramCovEntry D0 D' (e.1, x, x') (e'.1, z, z') (𝒢 s ω) else 0) := by
  have hσ := isStoppingTime_bTime hθ e
  have hσ' := isStoppingTime_bTime hθ e'
  have hρ := hσ.max hσ'
  have h := fun x x' z z' => by
    have hw : StronglyMeasurable[hρ.measurableSpace]
        (fun ω => bCoef lam e ω x x' * bCoef lam e' ω z z') :=
      ((stronglyMeasurable_bCoef hθ hlam e x x').mono
        (hσ.measurableSpace_mono hρ fun ω => le_max_left _ _)).mul
      ((stronglyMeasurable_bCoef hθ hlam e' z z').mono
        (hσ'.measurableSpace_mono hρ fun ω => le_max_right _ _))
    exact ((gramLoc_drift h𝒢 hp (e.1, x, x')).pair (gramLoc_drift h𝒢 hp (e'.1, z, z'))
      (gramLoc_bracket h𝒢 hp (e.1, x, x') (e'.1, z, z')) hσ hσ').weight hρ
      (stopped_pair_zero _ _ _ _) hw
  have h2 := CLocMart.sum univ fun x _ => CLocMart.sum univ fun x' _ =>
    CLocMart.sum univ fun z _ => CLocMart.sum univ fun z' _ => h x x' z z'
  convert h2 using 1
  · funext t ω
    simp only [bornRep, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ =>
      Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
    ring
  · funext s ω
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ =>
      Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
    split_ifs <;> rfl

end

end BlockBand.SourceProcess.ModelExist
