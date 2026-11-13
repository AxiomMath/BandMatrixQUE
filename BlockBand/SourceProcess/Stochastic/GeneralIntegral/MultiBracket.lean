module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.MultiCross
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Vector integrators with a PSD bracket matrix

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, a finite index type `ι`.
`IsL2IntegratorVec Q 𝓖 N a`: `N = (N^i)_{i ∈ ι}` with every coordinate an
`IsL2Integrator Q 𝓖 (N^i) (a^{ii})`, the matrix `a_s(ω) = (a^{ij}_s(ω))` positive semidefinite
everywhere (`0 ≤ vᵀ a v`), every `a^{ij}` jointly measurable and a.s. locally integrable, and
`N^i N^j - ∫_{(0,t]} a^{ij}` with a `𝓖`-martingale modification (`⟨N^i, N^j⟩ = ∫ a^{ij}`).

* `IsL2IntegratorVec.combo c`: for every `c ∈ ℝ^ι`, `c · N = ∑ c_i N^i` is an
  `IsL2Integrator` with density `cᵀ a c = ∑_{ij} c_i c_j a^{ij}` (nonnegative by PSD). In
  particular polarization: `N^i ± N^j` with density `a^{ii} ± (a^{ij} + a^{ji}) + a^{jj}`.
  Consequently (by the scalar theory) every `H ∈ PredL2 𝓖 ν^c_T` has a continuous integral
  `∫ H d(c · N)` with `E(∫_0^T H d(c·N))² = E ∫_0^T H² cᵀ a c ds` and a bracket martingale:
  this is the vector integral of rank-one integrands `H c`.
* `IsL2IntegratorVec.crossPair i j`: the martingale modifications of `N^i, N^j` with the
  pathwise cross bracket `∫_{(0,t]} a^{ij}` form a `CrossPair`;
  `setIntegral_coord_cross`: `∫_D ΔM^i_{(a₁,b₁]} ΔM^j_{(a₂,b₂]} = ∫_D ∫_{(c, c ∨ d]} a^{ij}`
  (`c = a₁ ∨ a₂`, `d = b₁ ∧ b₂`, `D ∈ 𝓖_c`), the rectangle input of the cross isometry.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {ι : Type*} [Fintype ι]

/-- A vector of continuous `L²` integrators with PSD bracket density matrix `a`. -/
structure IsL2IntegratorVec (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) (N : ι → ℝ≥0 → Ω → ℝ)
    (a : ι → ι → ℝ≥0 → Ω → ℝ) : Prop where
  coord : ∀ i, IsL2Integrator Q 𝓖 (N i) (a i i)
  psd : ∀ t ω (v : ι → ℝ), 0 ≤ ∑ i, ∑ j, v i * v j * a i j t ω
  measurable : ∀ i j, Measurable fun p : ℝ × Ω => a i j p.1.toNNReal p.2
  integrable : ∀ i j, ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
    IntegrableOn (fun r : ℝ => a i j r.toNNReal ω) (Ioc 0 t)
  cross : ∀ i j, ∃ K : ℝ≥0 → Ω → ℝ, Martingale K 𝓖 Q ∧ ∀ t, K t =ᵐ[Q] fun ω =>
    N i t ω * N j t ω - ∫ r in Ioc (0 : ℝ) t, a i j r.toNNReal ω

omit [Fintype ι] in
theorem martingale_finset_sum [IsFiniteMeasure Q] (s : Finset ι) {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) 𝓖 Q) : Martingale (fun t ω => ∑ i ∈ s, M i t ω) 𝓖 Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact martingale_zero (E := ℝ) 𝓖 Q
  | insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      exact (hM x).add ih

namespace IsL2IntegratorVec

variable {N : ι → ℝ≥0 → Ω → ℝ} {a : ι → ι → ℝ≥0 → Ω → ℝ}

/-- The combination `c · N`. -/
def comboN (N : ι → ℝ≥0 → Ω → ℝ) (c : ι → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := ∑ i, c i * N i t ω

/-- The density `cᵀ a c`. -/
def comboA (a : ι → ι → ℝ≥0 → Ω → ℝ) (c : ι → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, c i * c j * a i j t ω

/-- **Linear combinations of the coordinates are scalar `L²` integrators** with density
`cᵀ a c`. -/
theorem combo [IsFiniteMeasure Q] (h : IsL2IntegratorVec Q 𝓖 N a) (c : ι → ℝ) :
    IsL2Integrator Q 𝓖 (comboN N c) (comboA a c) := by
  classical
  choose K hK hKe using h.cross
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [ae_all_iff.2 fun i => (h.coord i).continuous] with ω hω
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hω i)
  · intro t
    exact memLp_finsetSum _ fun i _ => ((h.coord i).memLp t).const_mul (c i)
  · refine ⟨fun t ω => ∑ i, c i * (h.coord i).mart t ω,
      martingale_finset_sum _ fun i => (h.coord i).mart_martingale.smul (c i), fun t => ?_⟩
    filter_upwards [ae_all_iff.2 fun i => (h.coord i).mart_ae t] with ω hω
    simp only [comboN, hω]
  · intro t ω
    exact h.psd t ω c
  · simp only [comboA]
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (h.measurable i j).const_mul _
  · filter_upwards [ae_all_iff.2 fun p : ι × ι => h.integrable p.1 p.2] with ω hω t
    simp only [comboA]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hω (i, j) t).const_mul _
  · refine ⟨fun t ω => ∑ i, ∑ j, c i * c j * K i j t ω,
      martingale_finset_sum _ fun i => martingale_finset_sum _ fun j =>
        (hK i j).smul (c i * c j), fun t => ?_⟩
    filter_upwards [ae_all_iff.2 fun p : ι × ι => hKe p.1 p.2 t,
      ae_all_iff.2 fun p : ι × ι => h.integrable p.1 p.2] with ω hω0 hi0
    have hω (i j : ι) := hω0 (i, j)
    have hi (i j : ι) := hi0 (i, j)
    have hint : ∫ r in Ioc (0 : ℝ) t, comboA a c r.toNNReal ω =
        ∑ i, ∑ j, c i * c j * ∫ r in Ioc (0 : ℝ) t, a i j r.toNNReal ω := by
      simp only [comboA]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hi i j t).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hi i j t).const_mul _]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    simp only [hint, comboN, hω, sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Pathwise cross bracket `∫_{(0,t]} a^{ij}`. -/
def crossB (a : ι → ι → ℝ≥0 → Ω → ℝ) (i j : ι) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in Ioc (0 : ℝ) t, a i j r.toNNReal ω

/-- The coordinate martingale modifications form a cross pair with bracket `∫ a^{ij}`. -/
theorem crossPair [IsFiniteMeasure Q] (h : IsL2IntegratorVec Q 𝓖 N a) (i j : ι) :
    CrossPair Q 𝓖 (h.coord i).mart (h.coord j).mart (crossB a i j) := by
  obtain ⟨K, hK, hKe⟩ := h.cross i j
  have hae (t : ℝ≥0) : crossB a i j t =ᵐ[Q] fun ω => (h.coord i).mart t ω *
      (h.coord j).mart t ω - K t ω := by
    filter_upwards [hKe t, (h.coord i).mart_ae t, (h.coord j).mart_ae t] with ω h1 h2 h3
    rw [h1, h2, h3, crossB]; ring
  have hint (t : ℝ≥0) : Integrable (crossB a i j t) Q :=
    (((h.coord i).mart_memLp t).integrable_mul ((h.coord j).mart_memLp t)).sub
      (hK.integrable t) |>.congr (hae t).symm
  refine ⟨(h.coord i).mart_martingale, (h.coord j).mart_martingale, (h.coord i).mart_memLp,
    (h.coord j).mart_memLp, hint, K, hK, fun t => ?_⟩
  filter_upwards [hae t] with ω hω
  rw [hω]; ring

theorem crossB_sub (h : IsL2IntegratorVec Q 𝓖 N a) (i j : ι) {u v : ℝ≥0} (huv : u ≤ v) :
    ∀ᵐ ω ∂Q, crossB a i j v ω - crossB a i j u ω =
      ∫ r in Ioc (u : ℝ) v, a i j r.toNNReal ω := by
  filter_upwards [h.integrable i j] with ω hω
  have hu : Ioc (0 : ℝ) u ∪ Ioc (u : ℝ) v = Ioc (0 : ℝ) v :=
    Ioc_union_Ioc_eq_Ioc u.coe_nonneg (NNReal.coe_le_coe.2 huv)
  have hsum : ∫ r in Ioc (0 : ℝ) v, a i j r.toNNReal ω =
      (∫ r in Ioc (0 : ℝ) u, a i j r.toNNReal ω) + ∫ r in Ioc (u : ℝ) v, a i j r.toNNReal ω := by
    rw [← hu]
    refine setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc (hω u)
      ((hω v).mono_set ?_)
    rw [← hu]; exact subset_union_right
  simp only [crossB] at hsum ⊢
  linarith

/-- **Cross covariance of coordinate increments** (rectangle input of the cross isometry). -/
theorem setIntegral_coord_cross [IsFiniteMeasure Q] (h : IsL2IntegratorVec Q 𝓖 N a)
    (i j : ι) {a₁ b₁ a₂ b₂ : ℝ≥0} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) {D : Set Ω}
    (hD : MeasurableSet[𝓖 (max a₁ a₂)] D) :
    ∫ ω in D, (N i b₁ ω - N i a₁ ω) * (N j b₂ ω - N j a₂ ω) ∂Q =
      ∫ ω in D, (∫ r in Ioc ((max a₁ a₂ : ℝ≥0) : ℝ) (max (max a₁ a₂) (min b₁ b₂) : ℝ≥0),
        a i j r.toNNReal ω) ∂Q := by
  have hDm : MeasurableSet D := 𝓖.le _ D hD
  have hm : (fun ω => (N i b₁ ω - N i a₁ ω) * (N j b₂ ω - N j a₂ ω)) =ᵐ[Q]
      fun ω => ((h.coord i).mart b₁ ω - (h.coord i).mart a₁ ω) *
        ((h.coord j).mart b₂ ω - (h.coord j).mart a₂ ω) := by
    filter_upwards [(h.coord i).mart_ae b₁, (h.coord i).mart_ae a₁, (h.coord j).mart_ae b₂,
      (h.coord j).mart_ae a₂] with ω h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  rw [setIntegral_congr_ae hDm (hm.mono fun ω h _ => h),
    (h.crossPair i j).setIntegral_cross_incr h₁ h₂ hD]
  exact setIntegral_congr_ae hDm ((h.crossB_sub i j (le_max_left _ _)).mono fun ω h _ => h)

end IsL2IntegratorVec

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
