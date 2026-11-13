module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.MultiBracket
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Symmetrization of the bracket matrix; entry bounds for PSD matrices

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, finite index type `ι`,
`h : IsL2IntegratorVec Q 𝓖 N a` (`MultiBracket`). `IsL2IntegratorVec` does not assume `a`
symmetric; PSD (`0 ≤ vᵀ a v`) only controls the symmetric part.

* `symmPart a = (a + aᵀ)/2`; `IsL2IntegratorVec.symmetrize`: `N` is also an
  `IsL2IntegratorVec` with density `symmPart a` (the cross-bracket martingale is the average of
  those of `(i, j)` and `(j, i)`, since `N^i N^j = N^j N^i`); `symmPart_symm`.
* Pure matrix facts for a real matrix `A` with `0 ≤ vᵀ A v` for all `v`:
  `quadForm_two` (the quadratic form at `e_i + s e_j`), `psd_diag_nonneg`, and for symmetric
  `A`: `abs_le_of_psd_symm`: `|A_{ij}| ≤ (A_{ii} + A_{jj})/2`, `abs_le_trace_of_psd_symm`:
  `|A_{ij}| ≤ ∑_k A_{kk}`, `half_diag_le_trace`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

/-!
### Matrix facts
-/

/-- The quadratic form at `e_i + s e_j`. -/
theorem quadForm_two [DecidableEq ι] (A : ι → ι → ℝ) (i j : ι) (s : ℝ) :
    ∑ k, ∑ l, ((if k = i then 1 else 0) + s * (if k = j then 1 else 0)) *
      ((if l = i then 1 else 0) + s * (if l = j then 1 else 0)) * A k l =
      A i i + s * A i j + s * A j i + s ^ 2 * A j j := by
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, one_mul, zero_mul,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem psd_diag_nonneg {A : ι → ι → ℝ} (hpsd : ∀ v : ι → ℝ, 0 ≤ ∑ i, ∑ j, v i * v j * A i j)
    (i : ι) : 0 ≤ A i i := by
  classical
  have h := hpsd fun k => (if k = i then 1 else 0) + 0 * (if k = i then 1 else 0)
  rw [quadForm_two] at h
  linarith

/-- **Entry bound** `|A_{ij}| ≤ (A_{ii} + A_{jj})/2` for a symmetric PSD matrix. -/
theorem abs_le_of_psd_symm {A : ι → ι → ℝ}
    (hpsd : ∀ v : ι → ℝ, 0 ≤ ∑ i, ∑ j, v i * v j * A i j) (hs : ∀ i j, A i j = A j i)
    (i j : ι) : |A i j| ≤ (A i i + A j j) / 2 := by
  classical
  have h1 := hpsd fun k => (if k = i then 1 else 0) + 1 * (if k = j then 1 else 0)
  have h2 := hpsd fun k => (if k = i then 1 else 0) + (-1) * (if k = j then 1 else 0)
  rw [quadForm_two] at h1 h2
  rw [hs j i] at h1 h2
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

theorem half_diag_le_trace {A : ι → ι → ℝ} (hd : ∀ k, 0 ≤ A k k) (i j : ι) :
    (A i i + A j j) / 2 ≤ ∑ k, A k k := by
  have hi : A i i ≤ ∑ k, A k k :=
    Finset.single_le_sum (f := fun k => A k k) (fun k _ => hd k) (Finset.mem_univ i)
  have hj : A j j ≤ ∑ k, A k k :=
    Finset.single_le_sum (f := fun k => A k k) (fun k _ => hd k) (Finset.mem_univ j)
  linarith

/-- `|A_{ij}| ≤ tr A` for a symmetric PSD matrix. -/
theorem abs_le_trace_of_psd_symm {A : ι → ι → ℝ}
    (hpsd : ∀ v : ι → ℝ, 0 ≤ ∑ i, ∑ j, v i * v j * A i j) (hs : ∀ i j, A i j = A j i)
    (i j : ι) : |A i j| ≤ ∑ k, A k k :=
  (abs_le_of_psd_symm hpsd hs i j).trans (half_diag_le_trace (psd_diag_nonneg hpsd) i j)

/-!
### Symmetrization of a vector integrator
-/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}

omit [Fintype ι] mΩ in
/-- The symmetric part `(a + aᵀ)/2`. -/
def symmPart (a : ι → ι → ℝ≥0 → Ω → ℝ) (i j : ι) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (a i j t ω + a j i t ω) / 2

omit [Fintype ι] mΩ in
theorem symmPart_symm (a : ι → ι → ℝ≥0 → Ω → ℝ) (i j : ι) (t : ℝ≥0) (ω : Ω) :
    symmPart a i j t ω = symmPart a j i t ω := by
  simp only [symmPart, add_comm]

omit [Fintype ι] mΩ in
theorem symmPart_diag (a : ι → ι → ℝ≥0 → Ω → ℝ) (i : ι) : symmPart a i i = a i i := by
  funext t ω; simp only [symmPart]; ring

omit mΩ in
theorem symmPart_psd {a : ι → ι → ℝ≥0 → Ω → ℝ}
    (hpsd : ∀ t ω (v : ι → ℝ), 0 ≤ ∑ i, ∑ j, v i * v j * a i j t ω) (t : ℝ≥0) (ω : Ω)
    (v : ι → ℝ) : 0 ≤ ∑ i, ∑ j, v i * v j * symmPart a i j t ω := by
  have h := hpsd t ω v
  have e1 : ∑ i, ∑ j, v i * v j * symmPart a i j t ω =
      ((∑ i, ∑ j, v i * v j * a i j t ω) + ∑ i, ∑ j, v i * v j * a j i t ω) / 2 := by
    simp only [symmPart, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ i, ∑ j, v i * v j * a j i t ω = ∑ i, ∑ j, v i * v j * a i j t ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  linarith

namespace IsL2IntegratorVec

variable {N : ι → ℝ≥0 → Ω → ℝ} {a : ι → ι → ℝ≥0 → Ω → ℝ}

/-- **Symmetrization**: a vector integrator for `a` is one for `(a + aᵀ)/2`. -/
theorem symmetrize [IsFiniteMeasure Q] (h : IsL2IntegratorVec Q 𝓖 N a) :
    IsL2IntegratorVec Q 𝓖 N (symmPart a) where
  coord i := by rw [symmPart_diag]; exact h.coord i
  psd := symmPart_psd h.psd
  measurable i j := ((h.measurable i j).add (h.measurable j i)).div_const 2
  integrable i j := by
    filter_upwards [h.integrable i j, h.integrable j i] with ω h1 h2 t
    exact ((h1 t).add (h2 t)).div_const 2
  cross i j := by
    obtain ⟨K₁, hK₁, hKe₁⟩ := h.cross i j
    obtain ⟨K₂, hK₂, hKe₂⟩ := h.cross j i
    refine ⟨(1 / 2 : ℝ) • (K₁ + K₂), (hK₁.add hK₂).smul _, fun t => ?_⟩
    filter_upwards [hKe₁ t, hKe₂ t, h.integrable i j, h.integrable j i] with ω e1 e2 i1 i2
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, e1, e2, symmPart]
    rw [integral_div, integral_add (i1 t) (i2 t)]
    ring

end IsL2IntegratorVec

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
