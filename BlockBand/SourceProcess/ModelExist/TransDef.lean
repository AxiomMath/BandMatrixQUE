module

public import BlockBand.SourceProcess.ModelExist.TransAlg
public import BlockBand.SourceProcess.ModelExist.GramLocMP

/-!
# The born congruence of a Gram martingale-problem solution

Data: a Gram process `𝒢` on the columns `c'`, and for every target column `y ∈ c` a birth time
`θ_y` (`𝓖₀`-measurable) and a vector `λ_y ∈ ℂ^{c'}` (`𝓕_{θ_y}`-measurable). The born frame
matrix is `L_t = (1{θ_y ≤ t} λ_y)_y` and the born Gram process `G_t = congrGram L_t 𝒢_t`.
For `e = (r, i, j)` the coefficient is `conj(λ_i) ⊗ λ_j` and the birth time `θ_i ∨ θ_j`.

* `bornRep`: `Σ c_e (N − N^{θ_e})` for the compensated coordinates `N` of `𝒢`.

Proved in a sibling module:
* `cLocMart_bornRep`: it is a `CLocMart` with drift `0`;
* `cLocMart_bornRep_mul`: the product of two of them has drift
  `Σ 1{θ_e ∨ θ_e' < s} c_e c_e' Γ'(𝒢_s)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

variable {Ω : Type*} {c c' : Type*} [Fintype c']

/-- The born frame matrix `L_t`. -/
def bornL (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ) (t : ℝ≥0) (ω : Ω) : Matrix c' c ℂ :=
  fun x y => if θ y ω ≤ t then lam y ω x else 0

/-- The born Gram process. -/
def bornG [Fintype c] (𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ) (θ : c → Ω → ℝ≥0)
    (lam : c → Ω → c' → ℂ) (t : ℝ≥0) (ω : Ω) : Matrix c c ℂ × Matrix c c ℂ :=
  congrGram (bornL θ lam t ω) (𝒢 t ω)

/-- The birth time `θ_i ∨ θ_j` of the coordinate `(r, i, j)`. -/
def bTime (θ : c → Ω → ℝ≥0) (e : Fin 2 × c × c) (ω : Ω) : WithTop ℝ≥0 :=
  ((max (θ e.2.1 ω) (θ e.2.2 ω) : ℝ≥0) : WithTop ℝ≥0)

/-- The coefficient `conj(λ_i(x)) λ_j(x')`. -/
def bCoef (lam : c → Ω → c' → ℂ) (e : Fin 2 × c × c) (ω : Ω) (x x' : c') : ℂ :=
  star (lam e.2.1 ω x) * lam e.2.2 ω x'

/-- The transformed compensated process `Σ c_e (N − N^{θ_e})`. -/
def bornRep (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ) (N : Fin 2 × c' × c' → ℝ≥0 → Ω → ℂ)
    (e : Fin 2 × c × c) (t : ℝ≥0) (ω : Ω) : ℂ :=
  ∑ x, ∑ x', bCoef lam e ω x x' * (N (e.1, x, x') t ω - stoppedProcess (N (e.1, x, x'))
    (bTime θ e) t ω)

omit [Fintype c'] in
theorem cf_bornL (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ) (t : ℝ≥0) (ω : Ω) (r : Fin 2)
    (i j : c) (x x' : c') :
    cf (bornL θ lam t ω) i j x x' =
      if bTime θ (r, i, j) ω ≤ t then bCoef lam (r, i, j) ω x x' else 0 := by
  simp only [cf, bornL, bTime, bCoef, WithTop.coe_le_coe, max_le_iff]
  by_cases hi : θ i ω ≤ t <;> by_cases hj : θ j ω ≤ t <;> simp [hi, hj]

theorem gramEntry_bornG [Fintype c] (𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ)
    (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ) (e : Fin 2 × c × c) (t : ℝ≥0) (ω : Ω) :
    gramEntry e (bornG 𝒢 θ lam t ω) = ∑ x, ∑ x', (if bTime θ e ω ≤ t then
      bCoef lam e ω x x' else 0) * gramEntry (e.1, x, x') (𝒢 t ω) := by
  obtain ⟨r, i, j⟩ := e
  simp only [bornG, gramEntry_congr, cf_bornL θ lam t ω r]

theorem gramDriftEntry_bornG [Fintype c] [DecidableEq c] {D : Matrix c c ℂ}
    {D' : Matrix c' c' ℂ} (D0 : ℝ) (𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ)
    {θ : c → Ω → ℝ≥0} {lam : c → Ω → c' → ℂ} (hsig : ∀ t ω, bornL θ lam t ω * D *
      (bornL θ lam t ω)ᴴ = D') (e : Fin 2 × c × c) (t : ℝ≥0) (ω : Ω) :
    gramDriftEntry D0 D e (bornG 𝒢 θ lam t ω) = ∑ x, ∑ x', (if bTime θ e ω ≤ t then
      bCoef lam e ω x x' else 0) * gramDriftEntry D0 D' (e.1, x, x') (𝒢 t ω) := by
  obtain ⟨r, i, j⟩ := e
  simp only [bornG, gramDriftEntry_congr (hsig t ω), cf_bornL θ lam t ω r]

theorem gramCovEntry_bornG [Fintype c] [DecidableEq c] {D : Matrix c c ℂ}
    {D' : Matrix c' c' ℂ} (D0 : ℝ) (𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ)
    {θ : c → Ω → ℝ≥0} {lam : c → Ω → c' → ℂ} (hsig : ∀ t ω, bornL θ lam t ω * D *
      (bornL θ lam t ω)ᴴ = D') (e e' : Fin 2 × c × c) (t : ℝ≥0) (ω : Ω) :
    gramCovEntry D0 D e e' (bornG 𝒢 θ lam t ω) = ∑ x, ∑ x', ∑ z, ∑ z',
      (if max (bTime θ e ω) (bTime θ e' ω) ≤ t then
        bCoef lam e ω x x' * bCoef lam e' ω z z' else 0) *
        gramCovEntry D0 D' (e.1, x, x') (e'.1, z, z') (𝒢 t ω) := by
  obtain ⟨r, i, j⟩ := e
  obtain ⟨r', k, l⟩ := e'
  simp only [bornG, gramCovEntry_congr (hsig t ω), cf4, cf_bornL θ lam t ω r, max_le_iff,
    bTime, bCoef, WithTop.coe_le_coe]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  by_cases h1 : θ i ω ≤ t ∧ θ j ω ≤ t <;> by_cases h2 : θ k ω ≤ t ∧ θ l ω ≤ t <;>
    simp only [h1, h2, ↓reduceIte, and_self, and_false, false_and, zero_mul, mul_zero,
      mul_assoc]

/-!
### Measurability of the birth data
-/

variable [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [Fintype c'] in
theorem isStoppingTime_of_meas0 {θ : Ω → ℝ≥0} (hθ : Measurable[𝓖 0] θ) :
    IsStoppingTime 𝓖 (fun ω => ((θ ω : ℝ≥0) : WithTop ℝ≥0)) := fun _ =>
  𝓖.mono zero_le _ (measurableSet_le (WithTop.measurable_coe.comp hθ) measurable_const)

omit [Fintype c'] in
theorem isStoppingTime_bTime {θ : c → Ω → ℝ≥0} (hθ : ∀ y, Measurable[𝓖 0] (θ y))
    (e : Fin 2 × c × c) : IsStoppingTime 𝓖 (bTime θ e) :=
  isStoppingTime_of_meas0 ((hθ e.2.1).max (hθ e.2.2))

omit [Fintype c'] in
theorem stronglyMeasurable_bCoef {θ : c → Ω → ℝ≥0} (hθ : ∀ y, Measurable[𝓖 0] (θ y))
    {lam : c → Ω → c' → ℂ}
    (hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace] (lam y))
    (e : Fin 2 × c × c) (x x' : c') :
    StronglyMeasurable[(isStoppingTime_bTime hθ e).measurableSpace]
      (fun ω => bCoef lam e ω x x') := by
  have h1 := (isStoppingTime_of_meas0 (hθ e.2.1)).measurableSpace_mono
    (isStoppingTime_bTime hθ e) fun ω => WithTop.coe_le_coe.2 (le_max_left _ _)
  have h2 := (isStoppingTime_of_meas0 (hθ e.2.2)).measurableSpace_mono
    (isStoppingTime_bTime hθ e) fun ω => WithTop.coe_le_coe.2 (le_max_right _ _)
  have a1 : StronglyMeasurable[(isStoppingTime_bTime hθ e).measurableSpace]
      (fun ω => lam e.2.1 ω x) :=
    ((continuous_apply x).comp_stronglyMeasurable (hlam e.2.1)).mono h1
  have a2 : StronglyMeasurable[(isStoppingTime_bTime hθ e).measurableSpace]
      (fun ω => lam e.2.2 ω x') :=
    ((continuous_apply x').comp_stronglyMeasurable (hlam e.2.2)).mono h2
  exact (continuous_star.comp_stronglyMeasurable a1).mul a2

end BlockBand.SourceProcess.ModelExist
