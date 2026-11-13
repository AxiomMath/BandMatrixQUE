module

public import BlockBand.Critical.RelativeVectors.Angular.Main
public import BlockBand.Palm.MomentFlow.BridgeBrownian

/-!
# Path σ-algebras of the concrete flow

On the concrete flow sample space `FlowSample N` with `Q = flowLaw N a`, filtration
`flowFiltration N`, Hermitian Brownian motion `G = flowBM N` (`isHermitianBrownian_flowBM`) and
`𝓖_0`-measurable start `F' = flowInit F` (`measurable_flowInit`), one has
`F' + G_v = flowMatrix F a (hermProj ω) (a+v)` (`flowInit_add_flowBM`). Hence
(`comap_hermProj_pathSigma_le`), for `a ≤ s`, the matrix path σ-algebra pulls back into the
eigenvalue path σ-algebra:

`hermProj⁻¹(pathSigma F a s c) ⊆ eigenPathSigma F' G (s - a)`

(an inclusion, not an equality of σ-algebras). A `pathSigma F a s c`-measurable multiplier `Λ₀`
gives the multiplier `Λ₀ ∘ hermProj`, measurable for that σ-algebra and equal to `Λ₀` almost surely
(`multiplier_of_pathSigma`, from `hermProj_ae_eq`). No boundedness is assumed or concluded; a bound
on `Λ₀` passes to `Λ₀ ∘ hermProj` trivially.

`complexAngularMartingale_any_start` is used without the premise `0 < s ∨ F a.s. simple` of
`ComplexAngularMartingaleStatement` (its proof never uses it), so at start time `0` one need not
prove that `F + G_a` has almost surely simple spectrum.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.MomentFlow
open scoped NNReal

variable {N r : ℕ}

/-- `hermProj⁻¹(pathSigma F a s c)` is contained in the eigenvalue-path σ-algebra of the concrete
flow after time `s - a` (for `a ≤ s`). -/
theorem comap_hermProj_pathSigma_le (F : Matrix (Fin N) (Fin N) ℂ) {a s : ℝ} (has : a ≤ s)
    (c : ℝ) :
    MeasurableSpace.comap hermProj (pathSigma F a s c) ≤
      BlockBand.Critical.RelativeVectors.eigenPathSigma (flowInit F) (flowBM N)
        (Real.toNNReal (s - a)) := by
  unfold pathSigma
  simp_rw [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup₂_le fun σ hσ => iSup_le fun k => ?_
  set v : ℝ≥0 := Real.toNNReal (σ - s)
  have hv : Real.toNNReal (s - a) + v = Real.toNNReal (σ - a) := by
    rw [← Real.toNNReal_add (by linarith) (by linarith [hσ.1])]
    congr 1; ring
  have e : (fun ω => flowEigenvalue F a ω σ k) ∘ hermProj =
      (fun lam : Fin N → ℝ => lam k) ∘ (fun ω => fun i =>
        freshEigenvalue (flowInit F ω + flowBM N (Real.toNNReal (s - a) + v) ω) i) := by
    funext ω
    simp only [Function.comp_apply, flowEigenvalue]
    rw [hv, flowInit_add_flowBM F a ω, Real.coe_toNNReal _ (by linarith [hσ.1])]
    congr 2; ring
  rw [e, ← MeasurableSpace.comap_comp]
  refine (MeasurableSpace.comap_mono (measurable_pi_apply k).comap_le).trans ?_
  exact le_iSup (fun v => MeasurableSpace.comap
    (fun ω => fun i => freshEigenvalue (flowInit F ω + flowBM N (Real.toNNReal (s - a) + v) ω) i)
    inferInstance) v

/-- A `pathSigma`-measurable multiplier `Λ₀` gives a multiplier `Λ₀ ∘ hermProj` that is measurable
for the eigenvalue path σ-algebra of the concrete flow and almost surely equal to `Λ₀`. (No
boundedness hypothesis; a bound on `Λ₀` is inherited by `Λ₀ ∘ hermProj`.) -/
theorem multiplier_of_pathSigma (F : Matrix (Fin N) (Fin N) ℂ) {a s : ℝ} (has : a ≤ s) (c : ℝ)
    {Λ₀ : FlowSample N → ℝ} (hΛ₀ : Measurable[pathSigma F a s c] Λ₀) :
    Measurable[BlockBand.Critical.RelativeVectors.eigenPathSigma (flowInit F) (flowBM N)
        (Real.toNNReal (s - a))] (Λ₀ ∘ hermProj) ∧
      Λ₀ ∘ hermProj =ᵐ[flowLaw N a] Λ₀ := by
  refine ⟨?_, ?_⟩
  · exact (hΛ₀.comp (Measurable.of_comap_le le_rfl)).mono
      (comap_hermProj_pathSigma_le F has c) le_rfl
  · filter_upwards [hermProj_ae_eq (N := N) a] with ω hω
    simp [hω]

end BlockBand.Critical.RelativeVectors.Angular
