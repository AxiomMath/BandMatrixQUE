module

public import BlockBand.Native.ErdosRiabov.Psi.Tau
public import BlockBand.Native.ErdosRiabov.VS.Band
public import BlockBand.Native.ErdosRiabov.Flow.Const

/-!
# The conclusion of the zig step

The statement of the zig step, as used by the assembly of the local law.

Setting: a ring `p : BlockBand.Parameters`
(`m = p.n ≥ 4` blocks of width `W = p.W`, `N = p.n * p.W`, bond `p.b`); the VS band process
`H_t = VS.vsBandFin p t` on `RingSample p` under `driverLaw model.law`; the control data
`zigPsiData p D z` (`W = p.W`, the contract profile `S = shortRingProfile p.b p.n p.W`, decay `D`,
terminal point `z`); the control quantities `Ψ^iso_{k,t} = bigPsiIso k t H_t` and
`Ψ^av_{k,t} = bigPsiAv k t H_t`; the levels `1 ≤ k ≤ K = 8` (`Psi.kRange`).

* `zigBad p D z X`: the event `sup_{t ∈ [0,1]} max_{1 ≤ k ≤ 8} Ψ^{iso/av}_{k,t} > X`, written as
  "some `t ∈ [0,1]`, some `k` and some of the two quantities exceed `X`".
* **`ZigConclusion`** (the zig proposition): for the data `d : VSData` (`b, δ₀, ζ₀,
  κ, C₀, D` and the tolerance `ε = d.eps`) and every `D₁ > 0` there is `N₀` such that for every
  ring with `p.b = d.b`, `N ≥ N₀`, `N^{1+ζ₀} ≤ W²`, every `GaussianRingModel` and every `z` in the
  bulk domain `𝒟`, `P(zigBad p D z N^{ξ+ε}) ≤ N^{-D₁}` under `driverLaw model.law`, with
  `ξ = d.xi = min(ε, δ₀)/200`.
* **`ZigConclusionK1`**: the same bound for the single quantity `Ψ^iso_{1,1}` (`k = 1`, `t = 1`),
  which is all that the extraction step uses. `zigConclusionK1_of_zigConclusion`:
  `ZigConclusion → ZigConclusionK1`.

The measures are evaluated on possibly non-measurable sets (outer measure), so the bounds are
at least as strong as for any measurable version of the events.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Assembly

open MeasureTheory
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

/-- The control data of the zig step on the ring `p`: bandwidth `p.W`, the contract profile
`shortRingProfile p.b p.n p.W`, decay `D` of the control, terminal point `z`. -/
def zigPsiData (p : BlockBand.Parameters) (D : ℝ) (z : ℂ) : PsiData (p.n * p.W) where
  W := p.W
  S := shortRingProfile p.b p.n p.W
  D := D
  z := z

@[simp] theorem zigPsiData_W (p : BlockBand.Parameters) (D : ℝ) (z : ℂ) :
    (zigPsiData p D z).W = p.W := rfl

@[simp] theorem zigPsiData_S (p : BlockBand.Parameters) (D : ℝ) (z : ℂ) :
    (zigPsiData p D z).S = shortRingProfile p.b p.n p.W := rfl

@[simp] theorem zigPsiData_D (p : BlockBand.Parameters) (D : ℝ) (z : ℂ) :
    (zigPsiData p D z).D = D := rfl

@[simp] theorem zigPsiData_z (p : BlockBand.Parameters) (D : ℝ) (z : ℂ) :
    (zigPsiData p D z).z = z := rfl

/-- The bad event of the zig step, `sup_{t ∈ [0,1]} max_{1 ≤ k ≤ 8} Ψ^{iso/av}_{k,t} > X`: some
time `t ∈ [0,1]`, some level `k ∈ kRange = [1, 8]` and one of `Ψ^iso_{k,t}(H_t)`,
`Ψ^av_{k,t}(H_t)` exceed `X`, along the VS band process `H_t = VS.vsBandFin p t`. -/
def zigBad (p : BlockBand.Parameters) (D : ℝ) (z : ℂ) (X : ℝ) : Set (RingSample p) :=
  {x | ∃ t : ℝ≥0, t ≤ 1 ∧ ∃ k ∈ kRange,
    X < (zigPsiData p D z).bigPsiIso k t (VS.vsBandFin p t x) ∨
      X < (zigPsiData p D z).bigPsiAv k t (VS.vsBandFin p t x)}

/-- **The zig proposition.**
For the data `d` (with the tolerance `ε = d.eps`) and every `D₁ > 0` there is
`N₀: ℕ` (depending only on `d` and `D₁`) such that for every ring `p` with `p.b = d.b`,
`N = p.n * p.W ≥ N₀` and `N^{1+ζ₀} ≤ W²`, every `GaussianRingModel` and every `z` in the bulk
domain `𝒟 = BulkDomain N δ₀ κ C₀`, under `driverLaw model.law`:
`P(sup_{t ∈ [0,1]} max_{k ≤ 8} Ψ^{iso/av}_{k,t} > N^{ξ+ε}) ≤ N^{-D₁}`, `ξ = min(ε, δ₀)/200`.
-/
def ZigConclusion : Prop :=
  ∀ (d : VSData) (D₁ : ℝ), 0 < D₁ →
    ∃ N₀ : ℕ, ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ),
        BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z →
        driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
            (zigBad p d.D z (((p.n * p.W : ℕ) : ℝ) ^ (d.xi + d.eps))) ≤
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D₁))

/-- **The `k = 1`, `t = 1`, isotropic part of `ZigConclusion`.** As
`ZigConclusion`, for the single quantity `Ψ^iso_{1,1}(H_1)`:
`P(Ψ^iso_{1,1} > N^{ξ+ε}) ≤ N^{-D₁}`.
This is all that the extraction step reads.
-/
def ZigConclusionK1 : Prop :=
  ∀ (d : VSData) (D₁ : ℝ), 0 < D₁ →
    ∃ N₀ : ℕ, ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ),
        BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z →
        driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
            {x | ((p.n * p.W : ℕ) : ℝ) ^ (d.xi + d.eps) <
              (zigPsiData p d.D z).bigPsiIso 1 1 (VS.vsBandFin p 1 x)} ≤
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D₁))

theorem one_mem_kRange : 1 ∈ kRange := Finset.mem_Icc.2 ⟨le_rfl, by norm_num [vsK]⟩

/-- The `k = 1`, `t = 1`, isotropic event lies in the zig bad event. -/
theorem psiIso_one_one_subset_zigBad (p : BlockBand.Parameters) (D : ℝ) (z : ℂ) (X : ℝ) :
    {x | X < (zigPsiData p D z).bigPsiIso 1 1 (VS.vsBandFin p 1 x)} ⊆ zigBad p D z X := by
  intro x hx
  refine ⟨1, le_rfl, 1, one_mem_kRange, Or.inl ?_⟩
  simpa only [NNReal.coe_one, Set.mem_ofPred_eq] using hx

/-- `ZigConclusion → ZigConclusionK1` (monotonicity of the measure). -/
theorem zigConclusionK1_of_zigConclusion (h : ZigConclusion) : ZigConclusionK1 := by
  intro d D₁ hD₁
  obtain ⟨N₀, hN₀⟩ := h d D₁ hD₁
  exact ⟨N₀, fun p hpb hN hband model z hz =>
    (measure_mono (psiIso_one_one_subset_zigBad p d.D z _)).trans
      (hN₀ p hpb hN hband model z hz)⟩

end BlockBand.Native.ErdosRiabov.Assembly
