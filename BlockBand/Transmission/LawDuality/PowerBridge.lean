module

public import BlockBand.Transmission.LawDuality.Interface
public import BlockBand.Transmission.Generator.Basic

/-!
# The trace measure integrates `t^j` to `Tr T^{j+1}`

A bridge between the trace-measure process `μ_W(t)` of `TransmissionLawContract` and the power
sums `P_k(t) = Tr T^k_{⌊Wt⌋}` of `TransmissionGeneratorContract`: `μ = Σ_i t_iδ_{t_i}`, so
`∫ t^{k-1}dμ = Tr T^k`.

* `traceMeasure_eq_sum`: for Hermitian `T`, `traceMeasure T = Σ_i (λ_i)₊ δ_{λ_i}`;
* `integral_traceMeasure`: `∫ g d(traceMeasure T) = Σ_i (λ_i)₊ g(λ_i)` for continuous `g`;
* `integral_pow_traceMeasure`: `∫ t^j d(traceMeasure T) = Re Tr T^{j+1}` for `0 ⪯ T ⪯ I`;
* **`ae_integral_pow_transmissionProcess`**: a.s., for all `j, t`,
  `∫ s^j dμ_W(t) = Re Tr T_{⌊Wt⌋}^{j+1}` (any nonnegative absorption profile).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal BoundedContinuousFunction ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℂ}

theorem traceMeasure_eq_sum (hT : T.IsHermitian) :
    traceMeasure T = ∑ i, Real.toNNReal (hT.eigenvalues i) • unitDirac (toUnit (hT.eigenvalues i)) := by
  rw [traceMeasure, hT.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

theorem integral_traceMeasure (hT : T.IsHermitian) {g : unitInterval → ℝ} (hg : Continuous g) :
    ∫ s, g s ∂(traceMeasure T : Measure unitInterval) =
      ∑ i, (Real.toNNReal (hT.eigenvalues i) : ℝ) * g (toUnit (hT.eigenvalues i)) := by
  rw [traceMeasure_eq_sum hT, FiniteMeasure.toMeasure_sum,
    integral_finsetSum_measure (f := g) fun i _ =>
      (BoundedContinuousFunction.mkOfCompact (⟨g, hg⟩ : C(unitInterval, ℝ))).integrable _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  simp [unitDirac, integral_dirac, NNReal.smul_def]

/-- Eigenvalues of `0 ⪯ T ⪯ I` lie in `[0,1]`. -/
theorem eigenvalues_mem (h0 : T.PosSemidef) (h1 : (1 - T).PosSemidef) (i : n) :
    0 ≤ h0.1.eigenvalues i ∧ h0.1.eigenvalues i ≤ 1 := by
  have hT := h0.1
  refine ⟨h0.eigenvalues_nonneg i, ?_⟩
  have he := hT.eigenvalues_eq i
  have hp := h1.re_dotProduct_nonneg (hT.eigenvectorBasis i)
  have hn : star (⇑(hT.eigenvectorBasis i)) ⬝ᵥ (⇑(hT.eigenvectorBasis i)) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      hT.eigenvectorBasis.orthonormal.1 i]
    simp
  rw [sub_mulVec, one_mulVec, dotProduct_sub, hn, map_sub] at hp
  simp only [RCLike.one_re] at hp
  have : hT.eigenvalues i = RCLike.re (star (⇑(hT.eigenvectorBasis i)) ⬝ᵥ
      (T *ᵥ ⇑(hT.eigenvectorBasis i))) := he
  linarith

theorem integral_pow_traceMeasure (h0 : T.PosSemidef) (h1 : (1 - T).PosSemidef) (j : ℕ) :
    ∫ s, (s : ℝ) ^ j ∂(traceMeasure T : Measure unitInterval) = (T ^ (j + 1)).trace.re := by
  rw [integral_traceMeasure h0.1 (g := fun s : unitInterval => (s : ℝ) ^ j)
      (continuous_subtype_val.pow j),
    Generator.trace_pow_re_eq h0.1]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨ha, hb⟩ := eigenvalues_mem h0 h1 i
  rw [Real.coe_toNNReal _ ha, toUnit, Set.coe_projIcc, min_eq_right hb, max_eq_right ha, pow_succ]
  ring

variable {W : ℕ}

/-- **`∫ s^j dμ_W(t) = Re Tr T_{⌊Wt⌋}^{j+1}`**, almost surely, for all `j, t`. -/
theorem ae_integral_pow_transmissionProcess {b E : ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s)
    (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (t : ℝ),
      ∫ s, (s : ℝ) ^ j ∂(transmissionProcess b E κ W t ω : Measure unitInterval) =
        ((pathTransmission b E κ W ⌊(W : ℝ) * t⌋₊ ω) ^ (j + 1)).trace.re := by
  filter_upwards [Bridge.ae_passiveSample W hκ hb hE1 hE2] with ω hω
  intro j t
  exact integral_pow_traceMeasure (Bridge.pathTransmission_posSemidef hω _)
    (Bridge.one_sub_pathTransmission_posSemidef b E κ W _ ω) j

end BlockBand.Transmission.LawDuality
