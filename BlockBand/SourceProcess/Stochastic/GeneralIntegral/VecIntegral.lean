module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.VecCross
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The vector stochastic integral `∑_i ∫ H_i dN^i`

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, finite `ι`,
`h : IsL2IntegratorVec Q 𝓖 N a` with symmetric `a` (`hs`; WLOG by `symmetrize`), horizon `T`,
vector integrands `H : ι → PredL2 𝓖 ν̄`, `ν̄ = barMeasure Q a T = (tr a) ds ⊗ Q`
(every bounded predictable `H` belongs to it), with canonical representatives `H̃_i`.

* `vecIntegral h T H = ∑_i coordInt h T i (H i) ∈ L²(Q)` (terminal value).
* **`integral_sq_vecIntegral`** (vector isometry):
  `E(∑_i ∫_0^T H_i dN^i)² = ∫ ∑_{ij} H̃_i H̃_j a^{ij} d(dt ⊗ Q) = E ∫_0^T Hᵀ a H ds`
  (`integral_sq_vecIntegral_fubini`), the integrand being `dt ⊗ Q`-integrable.
* `vecCont h T H t = ∑_i ∫_0^t H_i dN^i` (sum of the coordinate `contIntegral`s);
  **`vecCont_spec`**: a.s. continuous paths, `L²` at every time, a `𝓖`-martingale
  modification, terminal value `vecIntegral` a.s., constant after `T`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] {N : ι → ℝ≥0 → Ω → ℝ}
  {a : ι → ι → ℝ≥0 → Ω → ℝ}

namespace IsL2IntegratorVec

variable (h : IsL2IntegratorVec Q 𝓖 N a) (T : ℝ≥0)

/-- The vector integral `∑_i ∫_0^T H_i dN^i` in `L²(Q)`. -/
def vecIntegral (H : ι → PredL2 𝓖 (barMeasure Q a T)) : Lp ℝ 2 Q :=
  ∑ i, h.coordInt T i (H i)

/-- The quadratic form `Hᵀ a H` of a vector integrand (canonical representatives). -/
def quadDensity (a : ι → ι → ℝ≥0 → Ω → ℝ) (H : ι → PredL2 𝓖 (barMeasure Q a T))
    (p : ℝ × Ω) : ℝ :=
  ∑ i, ∑ j, (H i : Lp ℝ 2 (barMeasure Q a T)) p * (H j : Lp ℝ 2 (barMeasure Q a T)) p *
    a i j p.1.toNNReal p.2

variable (hs : ∀ i j t ω, a i j t ω = a j i t ω)
include h hs

theorem integrable_quadDensity (H : ι → PredL2 𝓖 (barMeasure Q a T)) :
    Integrable (quadDensity T a H) (timeProbMeasure T Q) :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (h.integral_coordInt_mul T hs i j (H i) (H j)).1

/-- **Vector isometry**: `E(∑_i ∫_0^T H_i dN^i)² = ∫ Hᵀ a H d(dt ⊗ Q)`. -/
theorem integral_sq_vecIntegral (H : ι → PredL2 𝓖 (barMeasure Q a T)) :
    ∫ ω, (h.vecIntegral T H ω) ^ 2 ∂Q = ∫ p, quadDensity T a H p ∂timeProbMeasure T Q := by
  have h1 : ∫ ω, (h.vecIntegral T H ω) ^ 2 ∂Q =
      ⟪h.vecIntegral T H, h.vecIntegral T H⟫_ℝ := by
    rw [real_inner_Lp_eq]; simp only [sq]
  rw [h1, vecIntegral, sum_inner]
  simp only [inner_sum, real_inner_Lp_eq]
  unfold quadDensity
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (h.integral_coordInt_mul T hs i j (H i) (H j)).1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (h.integral_coordInt_mul T hs i j (H i) (H j)).1]
  exact Finset.sum_congr rfl fun j _ => (h.integral_coordInt_mul T hs i j (H i) (H j)).2

/-- **Vector isometry, Fubini form**: `E(∑_i ∫_0^T H_i dN^i)² = E ∫_{(0,T]} Hᵀ a H ds`. -/
theorem integral_sq_vecIntegral_fubini (H : ι → PredL2 𝓖 (barMeasure Q a T)) :
    ∫ ω, (h.vecIntegral T H ω) ^ 2 ∂Q =
      ∫ ω, (∫ r in Ioc (0 : ℝ) T, quadDensity T a H (r, ω)) ∂Q := by
  rw [h.integral_sq_vecIntegral T hs H, timeProbMeasure,
    integral_prod_symm _ (h.integrable_quadDensity T hs H)]

omit hs

/-- The continuous vector integral `t ↦ ∑_i ∫_0^t H_i dN^i`. -/
def vecCont (H : ι → PredL2 𝓖 (barMeasure Q a T)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, (h.coord i).contIntegral T (h.restr T i (H i)) t ω

/-- **The continuous vector integral**: a.s. continuous, `L²`, a martingale modification,
terminal value `vecIntegral`, constant after `T`. -/
theorem vecCont_spec (H : ι → PredL2 𝓖 (barMeasure Q a T)) :
    (∀ᵐ ω ∂Q, Continuous fun t => h.vecCont T H t ω) ∧
    (∀ t, MemLp (h.vecCont T H t) 2 Q) ∧
    (∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧ ∀ t, Y t =ᵐ[Q] h.vecCont T H t) ∧
    h.vecCont T H T =ᵐ[Q] h.vecIntegral T H ∧
    (∀ t, T ≤ t → h.vecCont T H t = h.vecCont T H T) := by
  have hsp (i : ι) := (h.coord i).contIntegral_spec T (h.restr T i (H i))
  choose Y hY hYe using fun i => (hsp i).2.2.1
  refine ⟨?_, fun t => ?_, ⟨fun t ω => ∑ i, Y i t ω, martingale_finset_sum _ hY, fun t => ?_⟩,
    ?_, fun t ht => ?_⟩
  · filter_upwards [ae_all_iff.2 fun i => (hsp i).1] with ω hω
    exact continuous_finsetSum _ fun i _ => hω i
  · exact memLp_finsetSum _ fun i _ => (hsp i).2.1 t
  · filter_upwards [ae_all_iff.2 fun i => hYe i t] with ω hω
    simp only [vecCont, hω]
  · filter_upwards [ae_all_iff.2 fun i => (hsp i).2.2.2.1,
      Lp.coeFn_fun_finsetSum Finset.univ fun i => h.coordInt T i (H i)] with ω hω hsum
    rw [vecIntegral, hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hω i]
    rfl
  · funext ω
    simp only [vecCont, (hsp _).2.2.2.2 t ht]

end IsL2IntegratorVec

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
