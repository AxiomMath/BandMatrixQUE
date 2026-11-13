module

public import BlockBand.Native.ErdosRiabov.VS.ResolventItoFlow
public import BlockBand.Native.ErdosRiabov.VS.ChainTime
public import BlockBand.Native.ErdosRiabov.VS.BandCovariance
public import BlockBand.Native.ErdosRiabov.Chains.ChainBounds
public import BlockBand.Native.ErdosRiabov.Kernel.ProfilePow

set_option autoImplicit false

/-!
# Itô's formula for resolvent chains along the VS flow

## Setting

`p : BlockBand.Parameters`, `N = p.n * p.W`, matrices on `Fin N` (`RingMat p`), the VS band process
in coordinates `Y_t - Y_0 = vsNoise p t` on `RingSample p` under `driverLaw μ` (any probability law
`μ` of the unused initial state) with the filtration `driverAugmented μ`; at matrix level
`H_t = ringMatrixFin p (Y_t - Y_0)` (`ringMatrix` read through the row-major site order), with
`E|H_t(a,b)|² = t S_ab`, `S = shortRingProfile p.b p.n p.W`. A Hermitian shift `A₀` is allowed
(`A₀ = 0` is the case of the zig step). Spectral parameters are `C²` functions `z_j : ℝ → ℂ` off
the real axis for all times (`vsSpec`/`vsSat` provide the saturated
`z_{j,c(t)} ∈ {z_{c(t)}, z̄_{c(t)}}`). The chain test function is
`f(t, y) = chainTestT A₀ L z B K (t, y) = Re tr(K R_0 B_0 ⋯ R_{k-1} B_{k-1})`,
`R_j = (A₀ + L y - z_j(t))⁻¹`, `L = ringMatrixFin p`: the paper's chain `G_1 A_1 ⋯ A_{k-1} G_k`
is `B_{k-1} = 1`; entries `Re/Im (G_{[1,k]})_{ab}` are `K = E_{ba}`, `K = -i E_{ba}`
(`reTr_single`, `reTr_neg_I_smul`); averaged traces `Tr[G_{[1,k]} S^x]` are `B_{k-1} = S^x`.

## Main results

* `itoDrift_chainTestT_ring` (the chain drift, every `t`, every `y`):
  `drift = Re tr(K ∑_j ⋯ (ż_j(t) R_j²) ⋯) + ∑_{i ≤ j} Re tr(K G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)})`,
  `𝒮 = bandSelfEnergy S` (`chainDrift`); `itoBracket_chainTestT_ring`: the bracket density is
  `∑_i v_i (Re tr(K firstVar(L e_i)))²` (`chainBracket`).
* **`resolventChain_ito`** (Itô's formula for the driftless VS noise): `f(t, Y_t - Y_0)` is a
  continuous semimartingale with drift `chainDrift` and bracket density `chainBracket`.

Cited from the sibling modules: the next four items are proved in `ResolventItoVS`; the `Fin`-level
generator/bracket identities, the complex bracket `chainBracket_add_im`, the matrix process
`vsBandFin` and adaptedness are proved in `ResolventItoGlue`.

* **`chainDrift_vs`** (VS form of the drift, `t ∈ [0, 1]`, `z_j(t) = z_j + (1 - c(t)) m_j`):
  `drift = ∑_j [∑_{i<j} Re tr(K G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)}) +
    Re tr(K G_{[0,j]} 𝒮[G_j - m_j] G_{[j,k)})]` (flow term `ż_j G_j² = -m_j G_j²` absorbed with
  `𝒮[m I] = m I`, rows of `S` sum to one).
* **`chainBracket_le`**: if `|Im z_j(t)| ≥ ε > 0`, then
  `chainBracket ≤ 2 N (N ‖K‖ k ε^{-(k+1)} ∏_j ‖B_j‖)²` (`ℓ²` operator norms), and
  `chainBracket_le_pow`: with `ε ≥ (2N)⁻¹`, `‖K‖ ≤ 1`, `‖B_j‖ ≤ 1`:
  `chainBracket ≤ 2 k² 4^{k+1} N^{2k+5}` (a bound `≤ N^{C(k)}`).
* `resolventChain_ito_vs`: the pattern form `z_j ∈ {z, z̄}`, `m_j ∈ {m, m̄}` with the saturation
  `δ = Im z / (2 Im m)`, where `|Im z_{j,c(t)}| ≥ Im z / 2` for all `t`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Function
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.CEH.Flow
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Adapters.ErdosRiabov
open scoped NNReal

/-- Complex matrices on `Fin (p.n * p.W)` (the index type of `shortRingProfile p.b p.n p.W`). -/
abbrev RingMat (p : BlockBand.Parameters) : Type := Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ

variable {p : BlockBand.Parameters} {k : ℕ}

/-!
### Hermitian pencils along the VS coordinates
-/

theorem ringMatrixFin_isHermitian (y : Fin (ringDim p) → ℝ) : (ringMatrixFin p y).IsHermitian := by
  rw [ringMatrixFin_apply, reindex_apply]
  exact (ringMatrix_isHermitian p y).submatrix _

theorem isUnit_det_ring {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) {w : ℂ} (hw : w.im ≠ 0)
    (y : Fin (ringDim p) → ℝ) : IsUnit (A₀ + ringMatrixFin p y - w • (1 : RingMat p)).det :=
  isUnit_det_res A₀ (ringMatrixFin p) (hA₀.add (ringMatrixFin_isHermitian y)) hw

/-!
### Drift and bracket densities
-/

/-- The resolvent slots `R_j = (A₀ + L y - z_j(t))⁻¹`, `L = ringMatrixFin p`. -/
abbrev ringSlots (A₀ : RingMat p) (zf : Fin k → ℝ → ℂ) (t : ℝ) (y : Fin (ringDim p) → ℝ) :
    Fin k → RingMat p :=
  resSlots A₀ (ringMatrixFin p) (fun j => zf j t) y

/-- **The chain drift**: `Re tr(K ∑_j ⋯ (ż_j R_j²) ⋯) + ∑_{i ≤ j} Re tr(K · pairIns 𝒮)`. -/
def chainDrift (A₀ : RingMat p) (zf : Fin k → ℝ → ℂ) (B : Fin k → RingMat p) (K : RingMat p)
    (t : ℝ) (y : Fin (ringDim p) → ℝ) : ℝ :=
  reTr K (∑ j, slotProd B (update (ringSlots A₀ zf t y) j
      (deriv (zf j) t • (ringSlots A₀ zf t y j * ringSlots A₀ zf t y j)))) +
    ∑ j, ∑ i with i ≤ j,
      reTr K (pairIns B (ringSlots A₀ zf t y) (bandSelfEnergy (shortRingProfile p.b p.n p.W)) i j)

/-- **The chain bracket density**: `∑_i v_i (Re tr(K firstVar(R)[L e_i]))²`. -/
def chainBracket (A₀ : RingMat p) (zf : Fin k → ℝ → ℂ) (B : Fin k → RingMat p) (K : RingMat p)
    (t : ℝ) (y : Fin (ringDim p) → ℝ) : ℝ :=
  ∑ i, ringVariance p i *
    reTr K (firstVar B (ringSlots A₀ zf t y) (ringMatrixFin p (Pi.single i 1))) ^ 2

/-- **The chain drift identity** (every time, every point): the Itô drift of the chain test
function for zero drift and covariance `diag v` is `chainDrift`. Combines `partialTime_chainTestT`
(flow term), slicing and the ring-coordinate band contraction
`sum_mul_fderiv_fderiv_chainTest_ring` (Itô correction). -/
theorem itoDrift_chainTestT_ring {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) (zf : Fin k → ℝ → ℂ)
    (hzC : ∀ j, ContDiff ℝ 2 (zf j)) (hzim : ∀ j t, (zf j t).im ≠ 0) (B : Fin k → RingMat p)
    (K : RingMat p) (y : Fin (ringDim p) → ℝ) (t : ℝ≥0) :
    itoDrift (chainTestT A₀ (ringMatrixFin p) zf B K) y t 0 (diagonal (ringVariance p)) =
      chainDrift A₀ zf B K t y := by
  have hy : ∀ j, IsUnit (A₀ + ringMatrixFin p y - zf j t • (1 : RingMat p)).det :=
    fun j => isUnit_det_ring hA₀ (hzim j t) y
  have hzd : ∀ j, DifferentiableAt ℝ (zf j) t :=
    fun j => ((hzC j).differentiable (by norm_num)) t
  rw [itoDrift_zero_diagonal, partialTime_chainTestT A₀ _ zf B K hy hzd, chainDrift]
  congr 1
  have h2 : ∀ i, partialSpace2 (chainTestT A₀ (ringMatrixFin p) zf B K) ((t : ℝ), y) i i =
      fderiv ℝ (fderiv ℝ (chainTest A₀ (ringMatrixFin p) (fun j => zf j t) B K)) y
        (Pi.single i 1) (Pi.single i 1) := fun i => by
    rw [partialSpace2_eq_slice (contDiffAt_chainTestT A₀ _ zf B K hy fun j => (hzC j).contDiffAt),
      chainTestT_slice]
  simp only [h2]
  rw [sum_mul_fderiv_fderiv_chainTest_ring p A₀ _ B K hy]
  ring

/-- The bracket density of the chain test function is `chainBracket`. -/
theorem itoBracket_chainTestT_ring {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) (zf : Fin k → ℝ → ℂ)
    (hzC : ∀ j, ContDiff ℝ 2 (zf j)) (hzim : ∀ j t, (zf j t).im ≠ 0) (B : Fin k → RingMat p)
    (K : RingMat p) (y : Fin (ringDim p) → ℝ) (t : ℝ≥0) :
    itoBracket (chainTestT A₀ (ringMatrixFin p) zf B K) y t (diagonal (ringVariance p)) =
      chainBracket A₀ zf B K t y := by
  have hy : ∀ j, IsUnit (A₀ + ringMatrixFin p y - zf j t • (1 : RingMat p)).det :=
    fun j => isUnit_det_ring hA₀ (hzim j t) y
  have hzd : ∀ j, DifferentiableAt ℝ (zf j) t :=
    fun j => ((hzC j).differentiable (by norm_num)) t
  rw [itoBracket_diagonal, chainBracket]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialSpace_chainTestT A₀ _ zf B K hy hzd i, neg_sq]

/-!
### Itô's formula for resolvent chains
-/

/-- **Itô's formula for resolvent chains along the VS flow.** For every
probability law `μ` of the initial state, Hermitian `A₀`, `C²` spectral parameters `z_j : ℝ → ℂ`
that
never touch the real axis, slot observables `B` and weight `K`, the process
`f(t, Y_t - Y_0) = Re tr(K R_0 B_0 ⋯ R_{k-1} B_{k-1})`, `R_j = (A₀ + H_t - z_j(t))⁻¹`,
`H_t = ringMatrixFin p (Y_t - Y_0)`, is a continuous semimartingale for
`(driverLaw μ, driverAugmented μ)` with drift `chainDrift` and bracket density `chainBracket`. -/
theorem resolventChain_ito (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] {A₀ : RingMat p}
    (hA₀ : A₀.IsHermitian) (zf : Fin k → ℝ → ℂ) (hzC : ∀ j, ContDiff ℝ 2 (zf j))
    (hzim : ∀ j t, (zf j t).im ≠ 0) (B : Fin k → RingMat p) (K : RingMat p) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
      (driverAugmented (κ := Fin (ringDim p)) μ)
      (fun t x (_ : Fin 1) => chainTestT A₀ (ringMatrixFin p) zf B K ((t : ℝ), vsNoise p t x))
      (fun t x (_ : Fin 1) => chainDrift A₀ zf B K t (vsNoise p t x))
      (fun t x => Matrix.of fun (_ _ : Fin 1) => chainBracket A₀ zf B K t (vsNoise p t x)) := by
  have hφm : Measurable (chainTestT A₀ (ringMatrixFin p) zf B K) :=
    measurable_chainTestT A₀ _ zf B K fun j => (hzC j).continuous.measurable
  have hφ : ContDiffOn ℝ 2 (chainTestT A₀ (ringMatrixFin p) zf B K) (Set.univ ×ˢ Set.univ) :=
    contDiffOn_chainTestT A₀ _ zf B K (fun t y _ j => isUnit_det_ring hA₀ (hzim j t) y) hzC
  refine isContinuousSemimartingale_congr_data
    (vsNoise_itoFormula μ isOpen_univ (ae_of_all _ fun _ _ => Set.mem_univ _) hφm hφ) rfl ?_ ?_
  · funext t x _
    exact itoDrift_chainTestT_ring hA₀ zf hzC hzim B K _ t
  · funext t x
    simp only [itoBracket_chainTestT_ring hA₀ zf hzC hzim B K]

end BlockBand.Native.ErdosRiabov.VS
