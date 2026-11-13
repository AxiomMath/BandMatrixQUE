module

public import BlockBand.Endpoints.Sine.MicroscopicTagDefs
public import BlockBand.Internal.Contracts.RingSymmetry

/-!
# Step 1 of the microscopic tag comparison: cyclic invariance and the block-`0` Palm form

By cyclic invariance, the left side does not depend on `k`. Its expectation in the Palm law of
the mass on block `0`, with density `n p_{α0}`, is exactly its unweighted spectral expectation,
because `Σ_j p_{αj} = 1`.

Law: the exact physical law `model.law`. Inputs: `RingRotationInvariance` and the a.s.
normalization `physicalOrderedBlockMass_sum_ae`.

* `mts_physicalTagSide_eq_zero`: `E Σ_α w(u_α)Φ(n p_{αk}) = E Σ_α w(u_α)Φ(n p_{α0})` for every
  block `k` (uniformity in the physical tag is free).
* `mts_lintegral_palm_block0`: for a measurable `f ≥ 0` invariant under the cyclic rotation of
  its block-mass argument, `E Σ_α f(λ_α, p_α) = n E Σ_α p_{α0} f(λ_α, p_α)` (the left side of
  `OneBlockPalmContract.mass` at `k = 0`, times `n`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.RingSymmetry
open scoped ENNReal NNReal BoundedContinuousFunction

/-- **Step 1, `k`-independence.** With `RingRotationInvariance`, the physical tag side does not
depend on the tag `k`. -/
theorem mts_physicalTagSide_eq_zero (hRot : RingRotationInvariance) (p : Parameters)
    (model : p.GaussianRingModel) (E : ℝ) (w : ℝ → ℝ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (k : ZMod p.n) : physicalTagSide p model E w Φ k = physicalTagSide p model E w Φ 0 := by
  have h := (hRot p model k).2.2.1 (fun l P => ∑ α : Fin p.N,
    w (microCoord p E (l α)) * Φ (Set.projIci 0 ((p.n : ℝ) * P α 0)))
  simp only [zero_add] at h
  exact h

theorem mts_measurable_blockMassVector (p : Parameters) (α : Fin p.N) :
    Measurable (fun H : p.SiteMatrix => blockMassVector p H α) :=
  Measurable.of_eval fun k => measurable_physicalOrderedBlockMass p α k

theorem mts_measurable_physicalOrderedEigenvalue (p : Parameters) (α : Fin p.N) :
    Measurable (fun H : p.SiteMatrix => physicalOrderedEigenvalue p H α) :=
  measurable_rawIncreasingEigenvalue _

/-- **Step 1, block-`0` Palm form.** With `RingRotationInvariance`: for every measurable `f ≥ 0`
invariant under the cyclic rotation of its block-mass argument (`f(λ, q(· + j)) = f(λ, q)`),
`E Σ_α f(λ_α, p_α) = n E Σ_α p_{α0} f(λ_α, p_α)`. -/
theorem mts_lintegral_palm_block0 (hRot : RingRotationInvariance) (p : Parameters)
    (model : p.GaussianRingModel) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f))
    (hinv : ∀ (l : ℝ) (q : ZMod p.n → ℝ) (j : ZMod p.n), f l (fun i => q (i + j)) = f l q) :
    (∫⁻ H, ∑ α : Fin p.N, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      (p.n : ℝ≥0∞) * ∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α 0) *
          f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix) := by
  have hfm : ∀ α : Fin p.N, Measurable (fun H : p.SiteMatrix =>
      f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) := fun α =>
    hf.comp ((mts_measurable_physicalOrderedEigenvalue p α).prodMk
      (mts_measurable_blockMassVector p α))
  -- insert `Σ_k p_{αk} = 1`
  have hsum : (fun H : p.SiteMatrix => ∑ α : Fin p.N,
      f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) =ᵐ[(model.law : Measure _)]
      fun H => ∑ k : ZMod p.n, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) := by
    filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
      (fun k _ => physicalOrderedBlockMass_nonneg p H α k), hH α, ENNReal.ofReal_one, one_mul]
  have hmk : ∀ k ∈ (Finset.univ : Finset (ZMod p.n)), Measurable (fun H : p.SiteMatrix =>
      ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) := fun k _ =>
    Finset.measurable_sum _ fun α _ =>
      (ENNReal.measurable_ofReal.comp (measurable_physicalOrderedBlockMass p α k)).mul (hfm α)
  rw [lintegral_congr_ae hsum, lintegral_finsetSum _ hmk]
  -- every block gives the block-`0` term
  have hk : ∀ k : ZMod p.n, (∫⁻ H, ∑ α : Fin p.N,
      ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α 0) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix) := by
    intro k
    have h := (hRot p model k).2.2.2 (fun l P => ∑ α : Fin p.N,
      ENNReal.ofReal (P α 0) * f (l α) (P α))
    simp only [zero_add] at h
    have hinv' : ∀ H : p.SiteMatrix, ∀ α : Fin p.N,
        f (eigenvalueVector p H α) (fun i => blockMassMatrix p H α (i + k)) =
          f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) := by
      intro H α
      exact hinv _ (blockMassVector p H α) k
    simp only [hinv'] at h
    exact h
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul]

end BlockBand.Endpoints
