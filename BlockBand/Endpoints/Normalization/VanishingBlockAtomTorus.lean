module

public import BlockBand.Model.Construction.MarkedStateTopology
public import BlockBand.Model.Construction.SpectralProfiles
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Vanishing block atoms: the pair energy of one mark

The paper bounds `Σ_k p_k² ≤ max_k p_k` and uses that the largest atom of a nonatomic limit mark
vanishes. We use an equivalent continuous form of the same bound: for the kernel
`ψ_m(r,s) = max(0, 1 - (m+1) d(r,s))` on the unit torus (`ψ_m(r,r) = 1`, `0 ≤ ψ_m ≤ 1`), the
pair energy `Q_m(ν) = ∫∫ ψ_m dν dν` satisfies

* `Σ_k p_k² ≤ Q_m(ν)` for every physical profile `ν = Σ_k p_k δ_{k/n}` (all `m`);
* `ν ↦ Q_m(ν)` is continuous for the weak topology of `MassProfile` (Mathlib's continuity of
  products of probability measures);
* `Q_m(ν) → (ν⊗ν)(diagonal) = 0` as `m → ∞` for every nonatomic `ν`.

This replaces the upper semicontinuity of the largest atom by a continuous majorant. Every
statement here is deterministic.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory Filter Topology
open BlockBand.Model.Construction

/-- The diagonal kernel `ψ_m(r,s) = max(0, 1 - (m+1) d(r,s))` on the unit torus. -/
def diagKernel (m : ℕ) (x : Torus × Torus) : ℝ :=
  max 0 (1 - ((m : ℝ) + 1) * dist x.1 x.2)

theorem continuous_diagKernel (m : ℕ) : Continuous (diagKernel m) := by
  unfold diagKernel
  exact continuous_const.max (continuous_const.sub
    (continuous_const.mul (continuous_fst.dist continuous_snd)))

theorem diagKernel_nonneg (m : ℕ) (x : Torus × Torus) : 0 ≤ diagKernel m x :=
  le_max_left _ _

theorem diagKernel_le_one (m : ℕ) (x : Torus × Torus) : diagKernel m x ≤ 1 := by
  unfold diagKernel
  apply max_le zero_le_one
  have : 0 ≤ ((m : ℝ) + 1) * dist x.1 x.2 := mul_nonneg (by positivity) dist_nonneg
  linarith

theorem diagKernel_self (m : ℕ) (r : Torus) : diagKernel m (r, r) = 1 := by
  simp [diagKernel]

/-- `ψ_m` as a bounded continuous function on the compact space `𝕋 × 𝕋`. -/
def diagKernelBCF (m : ℕ) : BoundedContinuousFunction (Torus × Torus) ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨diagKernel m, continuous_diagKernel m⟩

/-- The pair energy `Q_m(ν) = ∫ ψ_m d(ν ⊗ ν)` of a mass profile. -/
def pairEnergy (m : ℕ) (ν : MassProfile) : ℝ :=
  ∫ x, diagKernel m x ∂((ν.prod ν : ProbabilityMeasure (Torus × Torus)) : Measure (Torus × Torus))

theorem pairEnergy_nonneg (m : ℕ) (ν : MassProfile) : 0 ≤ pairEnergy m ν :=
  integral_nonneg (diagKernel_nonneg m)

theorem pairEnergy_le_one (m : ℕ) (ν : MassProfile) : pairEnergy m ν ≤ 1 := by
  unfold pairEnergy
  calc (∫ x, diagKernel m x ∂((ν.prod ν : ProbabilityMeasure (Torus × Torus)) :
          Measure (Torus × Torus)))
      ≤ ∫ _x, (1 : ℝ) ∂((ν.prod ν : ProbabilityMeasure (Torus × Torus)) :
          Measure (Torus × Torus)) :=
        integral_mono ((diagKernelBCF m).integrable _) (integrable_const _)
          (diagKernel_le_one m)
    _ = 1 := by simp

/-- `Q_m` is continuous for the weak topology on `MassProfile`. -/
theorem continuous_pairEnergy (m : ℕ) : Continuous (pairEnergy m) := by
  have hprod : Continuous (fun ν : MassProfile => ν.prod ν) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  rw [continuous_iff_continuousAt]
  intro ν
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (hprod.tendsto ν)) (diagKernelBCF m)
  unfold ContinuousAt pairEnergy
  simpa [diagKernelBCF] using h

/-- `Q_m` is measurable for the (Giry) measurable structure on `MassProfile`, which is
Borel by `massProfile_borelSpace`. -/
theorem measurable_pairEnergy (m : ℕ) : Measurable (pairEnergy m) := by
  have : BorelSpace MassProfile := massProfile_borelSpace
  exact (continuous_pairEnergy m).measurable

/-- **`Σ_k p_k² ≤ Q_m(ν)`** for the exact physical profile on every Hermitian matrix with
separable characteristic polynomial, every rank and every `m`. -/
theorem sum_sq_blockMass_le_pairEnergy (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) (α : Fin p.N) (m : ℕ) :
    ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k ^ 2 ≤
      pairEnergy m (physicalOrderedProfile p H α) := by
  set ν := physicalOrderedProfile p H α with hν
  set q := fun k : ZMod p.n => physicalOrderedBlockMass p H α k with hq
  set g := fun k : ZMod p.n => physicalProfileGrid p k with hg
  have hinner (r : Torus) : (∫ s, diagKernel m (r, s) ∂(ν : Measure Torus)) =
      ∑ l : ZMod p.n, q l * diagKernel m (r, g l) := by
    have h := physicalOrderedProfile_integral p H hH hsep α
      ⟨fun s => diagKernel m (r, s),
        (continuous_diagKernel m).comp (continuous_const.prodMk continuous_id)⟩
    simpa [hν, hq, hg] using h
  have hcont : Continuous (fun r : Torus => ∑ l : ZMod p.n, q l * diagKernel m (r, g l)) := by
    apply continuous_finsetSum
    intro l _
    exact continuous_const.mul
      ((continuous_diagKernel m).comp (continuous_id.prodMk continuous_const))
  have houter : (∫ r, (∑ l : ZMod p.n, q l * diagKernel m (r, g l)) ∂(ν : Measure Torus)) =
      ∑ k : ZMod p.n, q k * ∑ l : ZMod p.n, q l * diagKernel m (g k, g l) := by
    have h := physicalOrderedProfile_integral p H hH hsep α ⟨_, hcont⟩
    simpa [hν, hq, hg] using h
  have hE : pairEnergy m ν =
      ∑ k : ZMod p.n, q k * ∑ l : ZMod p.n, q l * diagKernel m (g k, g l) := by
    unfold pairEnergy
    rw [ProbabilityMeasure.toMeasure_prod,
      integral_prod (f := diagKernel m) (by exact (diagKernelBCF m).integrable _)]
    simp_rw [hinner]
    exact houter
  rw [hE]
  apply Finset.sum_le_sum
  intro k _
  have hqk : 0 ≤ q k := physicalOrderedBlockMass_nonneg p H α k
  have hsingle : q k * diagKernel m (g k, g k) ≤
      ∑ l : ZMod p.n, q l * diagKernel m (g k, g l) :=
    Finset.single_le_sum (f := fun l => q l * diagKernel m (g k, g l))
      (fun l _ => mul_nonneg (physicalOrderedBlockMass_nonneg p H α l)
        (diagKernel_nonneg m _)) (Finset.mem_univ k)
  rw [diagKernel_self, mul_one] at hsingle
  calc physicalOrderedBlockMass p H α k ^ 2 = q k * q k := by simp [hq, sq]
    _ ≤ q k * ∑ l : ZMod p.n, q l * diagKernel m (g k, g l) :=
      mul_le_mul_of_nonneg_left hsingle hqk

/-- **Nonatomic marks have vanishing pair energy:** `Q_m(ν) → 0` as `m → ∞` whenever
`ν {r} = 0` for every `r`. -/
theorem tendsto_pairEnergy_of_noAtoms (ν : MassProfile)
    (hν : ∀ r : Torus, (ν : Measure Torus) {r} = 0) :
    Tendsto (fun m : ℕ => pairEnergy m ν) atTop (𝓝 0) := by
  set μ : Measure (Torus × Torus) :=
    ((ν.prod ν : ProbabilityMeasure (Torus × Torus)) : Measure (Torus × Torus)) with hμ
  have hD : MeasurableSet (Set.diagonal Torus) := isClosed_diagonal.measurableSet
  have hlim : Tendsto (fun m : ℕ => ∫ x, diagKernel m x ∂μ) atTop
      (𝓝 (∫ x, (Set.diagonal Torus).indicator (1 : Torus × Torus → ℝ) x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro m
      exact (continuous_diagKernel m).aestronglyMeasurable
    · exact integrable_const _
    · intro m
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (diagKernel_nonneg m x)]
      exact diagKernel_le_one m x
    · filter_upwards with x
      by_cases hx : x.1 = x.2
      · have hmem : x ∈ Set.diagonal Torus := hx
        rw [Set.indicator_of_mem hmem]
        have : ∀ m : ℕ, diagKernel m x = 1 := by
          intro m
          obtain ⟨a, b⟩ := x
          simp only at hx
          subst hx
          exact diagKernel_self m a
        simp only [this, Pi.one_apply]
        exact tendsto_const_nhds
      · have hmem : x ∉ Set.diagonal Torus := hx
        rw [Set.indicator_of_notMem hmem]
        have hd : 0 < dist x.1 x.2 := dist_pos.mpr hx
        obtain ⟨m₀, hm₀⟩ := exists_nat_gt (1 / dist x.1 x.2)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop m₀] with m hm
        symm
        unfold diagKernel
        apply max_eq_left
        have h1 : 1 < ((m : ℝ) + 1) * dist x.1 x.2 := by
          have hm' : (m₀ : ℝ) ≤ m := by exact_mod_cast hm
          have : 1 / dist x.1 x.2 < (m : ℝ) + 1 := by linarith
          rw [div_lt_iff₀ hd] at this
          linarith
        linarith
  have hzero : (∫ x, (Set.diagonal Torus).indicator (1 : Torus × Torus → ℝ) x ∂μ) = 0 := by
    rw [integral_indicator_one hD]
    have : μ (Set.diagonal Torus) = 0 := by
      rw [hμ, ProbabilityMeasure.toMeasure_prod, Measure.prod_apply hD]
      have hpre (r : Torus) : Prod.mk r ⁻¹' Set.diagonal Torus = {r} := by
        ext s
        simp [Set.mem_diagonal_iff, eq_comm]
      simp_rw [hpre, hν]
      simp
    simp [Measure.real, this]
  rw [hzero] at hlim
  exact hlim

end BlockBand.Endpoints.Normalization
