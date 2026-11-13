module

public import BlockBand.SourceProcess.CoupledFrames.FrameForm
public import BlockBand.SourceProcess.CoupledFrames.NativeCongr
public import BlockBand.SourceProcess.ModelExist.TransDef
public import BlockBand.SourceProcess.Stochastic.SourceSDE.MatrixForms

/-!
# The born frame solves the finite source equation with births

Data: the extended solution `Y` (`IsSDESolution` with signature `extSig`), probe birth times
`(σ'_i)⁺` (`𝓖₀`-measurable), probe vectors `pv_i` (`𝓕_{θ_i}`-measurable) and shared birth vectors
`w_k` (`𝓕_{τ_k}`-measurable). The born frame is `bornFrame = N + J_b` with
`N_t = Y_t Lcur + Σ_k birthMat (col_k) ((Y_t − Y_{t∧τ_k}) a_k)` (`frameN`).

* `bornFrame_eq`: where `Y_{τ_k} a_k = w_k` for all `k`, `bornFrame_t = Y_t L_t`
  (`L_t = bornL`, the extended-to-target matrix).
* `isBornSDESolution_bornFrame` (proved in the sibling module): if moreover `Y_{τ_k} a_k = w_k` a.s. and `w_k = 0` when `τ_k = 0`
  a.s., then `bornFrame` is an `IsBornSDESolution` started at `ξ_Y Lcur` with jumps
  `frameBirthJump τ col w`: `bornFrame − J_b = N` is Itô (`isNativeItoProcess_frameN`), and
  its coefficients agree with `sourceDrift(bornFrame)`, `sourceDiffusion(bornFrame)` off the birth
  times (`isNativeItoProcess_congr_coeff`), since `P'` does not see zero-signature columns
  (`sourceDiffusion_mul`, `bornL_sig_probe`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.Stochastic.SourceSDE

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {K R : ℕ} {π : Type*} [Fintype π] [DecidableEq π] {n : ℕ} (eπ : π ≃ Fin n) {Ω : Type*}
  {S : Type*} [MeasurableSpace S] {κ : Type*} [Fintype κ]

/-- Birth times of the shared births. -/
def bτ (σ' : π → Ω → ℝ) (k : Fin n) (x : Ω) : ℝ≥0 := (σ' (eπ.symm k) x).toNNReal

/-- Columns of the shared births. -/
def bcol (k : Fin n) : SrcCol K π := Sum.inr (eπ.symm k)

/-- Extended coefficient vectors of the shared births. -/
def ba (pv : π → Ω → ExtCol K R → ℂ) (k : Fin n) : Ω → ExtCol K R → ℂ := pv (eπ.symm k)

/-- **The born frame.** -/
def bornFrame (Y : ℝ≥0 → DriverSample S κ → Matrix (Amb K R) (ExtCol K R) ℂ)
    (σ' : π → DriverSample S κ → ℝ) (pv : π → DriverSample S κ → ExtCol K R → ℂ)
    (w : Fin n → DriverSample S κ → Amb K R → ℂ) :
    ℝ≥0 → DriverSample S κ → Matrix (Amb K R) (SrcCol K π) ℂ :=
  fun t x => frameN Y (lcur K R π) (bτ eπ σ') (bcol eπ) (ba eπ pv) t x +
    frameBirthJump (bτ eπ σ') (bcol eπ) w t x

omit [Fintype π] [MeasurableSpace S] [Fintype κ] in
theorem bornFrame_eq (Y : ℝ≥0 → DriverSample S κ → Matrix (Amb K R) (ExtCol K R) ℂ)
    (σ' : π → DriverSample S κ → ℝ) (pv : π → DriverSample S κ → ExtCol K R → ℂ)
    (w : Fin n → DriverSample S κ → Amb K R → ℂ) {x : DriverSample S κ}
    (hw : ∀ k, Y (bτ eπ σ' k x) x *ᵥ ba eπ pv k x = w k x) (t : ℝ≥0) :
    bornFrame eπ Y σ' pv w t x = Y t x * bornL (mθ K σ') (glam K R pv) t x := by
  rw [mul_bornL _ σ' pv eπ]
  unfold bornFrame frameN
  rw [frameN_eq', frameN_add_jump _ _ _ _ _ _ t x hw]
  rfl

omit [Fintype π] in
theorem mul_bornL_lt (A : Matrix (Amb K R) (ExtCol K R) ℂ) (σ' : π → Ω → ℝ)
    (pv : π → Ω → ExtCol K R → ℂ) (t : ℝ≥0) (x : Ω)
    (ht : ∀ k, (t : WithTop ℝ≥0) ≠ ((bτ eπ σ' k x : ℝ≥0) : WithTop ℝ≥0)) :
    A * bornL (mθ K σ') (glam K R pv) t x = A * lcur K R π + ∑ k,
      if bτ eπ σ' k x < t then birthMat (bcol eπ k) (A *ᵥ ba eπ pv k x) else 0 := by
  rw [mul_bornL _ σ' pv eπ]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hne : bτ eπ σ' k x ≠ t := fun e => ht k (by rw [e])
  by_cases h : bτ eπ σ' k x < t
  · rw [ite_eq_left h]
    exact ite_eq_left h.le
  · rw [ite_eq_right h]
    exact ite_eq_right fun h' => h (lt_of_le_of_ne h' hne)

end BlockBand.SourceProcess.CoupledFrames
