module

public import BlockBand.SourceProcess.ComplexCoupled.BornIncr
public import BlockBand.SourceProcess.ComplexConstruct.KBornAlg
public import BlockBand.SourceProcess.ComplexUnique.NoiseLip

/-!
# The born `𝒦` integral of a born frame

Driver space over an ambient space `ι`. `𝒴` is an Itô process in `Matrix c' c' ℂ`
with zero drift and diffusion `kNoise D₀ η P 𝖣' (Y)` (`AmbientKIntegral` at the ambient
solution `Y`). For born coordinates `θ, λ` with `L_t 𝖣 L_tᴴ = 𝖣'` (`L = bornL θ λ`) and a frame `X`
with `X_t = Y_t L_t` at all times a.s., the born increment `𝒴ᵇ = (bInc θ λ 𝒴)_{yz}` is a native
Itô process in `Matrix c c ℂ` with zero drift and diffusion `kNoise D₀ η P 𝖣 (X)`
(`isNativeItoProcess_kBorn`). Proof: entries (`entryCLM`), `isNativeItoProcess_bInc`, assembly
(`isNativeItoProcess_ofEntries`), and the coefficient congruence off the birth times with
`kNoise(Y L) = Lᴴ kNoise(Y) L` (`kNoise_mul`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.ModelExist BlockBand.SourceProcess.CoupledFrames
open BlockBand.SourceProcess.ComplexUnique BlockBand.SourceProcess.ComplexConstruct

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- `u ↦ u E_{yz}` as a continuous real-linear map. -/
def sCLM (y z : c) : ℂ →L[ℝ] Matrix c c ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => u • Matrix.single y z (1 : ℂ)
      map_add' := fun u v => add_smul u v _
      map_smul' := fun r u => smul_assoc r u _ }

omit [Fintype c] in
theorem sCLM_apply (y z : c) (u : ℂ) : sCLM y z u = u • Matrix.single y z (1 : ℂ) := rfl

/-- The entry `A ↦ A_{yz}` as a continuous real-linear map. -/
def eCLM {m n : Type*} [Fintype m] [Fintype n] (y : m) (z : n) : Matrix m n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A y z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem eCLM_apply {m n : Type*} [Fintype m] [Fintype n] (y : m) (z : n) (A : Matrix m n ℂ) :
    eCLM y z A = A y z := rfl

theorem sum_sCLM (F : c → c → ℂ) : ∑ p : c × c, sCLM p.1 p.2 (F p.1 p.2) = Matrix.of F := by
  ext y z
  simp [sCLM_apply, Matrix.sum_apply, Matrix.single_apply, Fintype.sum_prod_type, ite_and]

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]

/-- **Assembly of a matrix Itô process from its entries.** -/
theorem isNativeItoProcess_ofEntries {F b : c → c → ℝ≥0 → DriverSample S κ → ℂ}
    {σ : c → c → κ → ℝ≥0 → DriverSample S κ → ℂ}
    (h : ∀ y z, IsNativeItoProcess μ (F y z) (b y z) (σ y z)) :
    IsNativeItoProcess μ (fun t ω => Matrix.of fun y z => F y z t ω)
      (fun t ω => Matrix.of fun y z => b y z t ω)
      (fun a t ω => Matrix.of fun y z => σ y z a t ω) := by
  have h2 := isNativeItoProcess_finsetSum (Finset.univ : Finset (c × c))
    fun p _ => (h p.1 p.2).map_clm (sCLM p.1 p.2)
  convert h2 using 1
  · funext t ω; exact (sum_sCLM _).symm
  · funext t ω; exact (sum_sCLM _).symm
  · funext a t ω; exact (sum_sCLM _).symm

variable {ι c' : Type*} [Fintype ι] [DecidableEq ι] [Fintype c'] [DecidableEq c']

/-- The born `𝒦` increment. -/
def kBorn (θ : c → DriverSample S (SourceNoise ι) → ℝ≥0)
    (lam : c → DriverSample S (SourceNoise ι) → c' → ℂ)
    (𝒴 : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c' c' ℂ) (t : ℝ≥0)
    (ω : DriverSample S (SourceNoise ι)) : Matrix c c ℂ :=
  Matrix.of fun y z => bInc θ lam (fun (_ : Unit) x x' t ω => 𝒴 t ω x x') () y z t ω

omit [Fintype c] [DecidableEq c] [MeasurableSpace S] [Fintype ι] [DecidableEq ι] [DecidableEq c'] in
theorem kBorn_zero (θ : c → DriverSample S (SourceNoise ι) → ℝ≥0)
    (lam : c → DriverSample S (SourceNoise ι) → c' → ℂ)
    (𝒴 : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c' c' ℂ)
    (ω : DriverSample S (SourceNoise ι)) :
    kBorn θ lam 𝒴 0 ω = 0 := by
  ext y z; simp [kBorn, bInc_zero]

/-- The birth times as `WithTop`-valued random times indexed by `Fin`. -/
def bTimes (θ : c → DriverSample S (SourceNoise ι) → ℝ≥0) :
    Fin (Fintype.card c) → DriverSample S (SourceNoise ι) → WithTop ℝ≥0 :=
  fun i ω => ((θ ((Fintype.equivFin c).symm i) ω : ℝ≥0) : WithTop ℝ≥0)

omit [DecidableEq c] [MeasurableSpace S] [Fintype ι] [DecidableEq ι] in
theorem ne_of_ne_bTimes {θ : c → DriverSample S (SourceNoise ι) → ℝ≥0} {t : ℝ≥0}
    {ω : DriverSample S (SourceNoise ι)} (ht : ∀ i, (t : WithTop ℝ≥0) ≠ bTimes θ i ω) (y : c) :
    (t : WithTop ℝ≥0) ≠ ((θ y ω : ℝ≥0) : WithTop ℝ≥0) := by
  have := ht (Fintype.equivFin c y)
  simpa [bTimes] using this

omit [DecidableEq c] [IsProbabilityMeasure μ] [DecidableEq ι] in
theorem measurable_bTimes {θ : c → DriverSample S (SourceNoise ι) → ℝ≥0}
    (hθ : ∀ y, Measurable[driverAugmented (κ := SourceNoise ι) μ 0] (θ y))
    (i : Fin (Fintype.card c)) :
    Measurable (bTimes θ i) :=
  WithTop.measurable_coe.comp ((hθ _).mono ((driverAugmented (κ := SourceNoise ι) μ).le 0) le_rfl)

omit [DecidableEq c'] in
/-- **The born `𝒦` increment is Itô with diffusion `kNoise` of the born frame.** -/
theorem isNativeItoProcess_kBorn {D0 η : ℝ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {D' : Matrix c' c' ℂ} {Y : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c' ℂ}
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    {𝒴 : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c' c' ℂ}
    (h𝒴 : IsNativeItoProcess μ 𝒴 (fun _ _ => 0) (fun a t x => kNoise D0 η P D' a (Y t x)))
    {θ : c → DriverSample S (SourceNoise ι) → ℝ≥0}
    {lam : c → DriverSample S (SourceNoise ι) → c' → ℂ}
    (hθ : ∀ y, Measurable[driverAugmented (κ := SourceNoise ι) μ 0] (θ y))
    (hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace] (lam y))
    (hsig : ∀ t ω, bornL θ lam t ω * D * (bornL θ lam t ω)ᴴ = D')
    (hXp : IsStronglyProgressive (driverAugmented (κ := SourceNoise ι) μ) X)
    (hX : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, X t x = Y t x * bornL θ lam t x) :
    IsNativeItoProcess μ (kBorn θ lam 𝒴) (fun _ _ => 0)
      (fun a t x => kNoise D0 η P D a (X t x)) := by
  have hE : ∀ (_ : Unit) x x', IsNativeItoProcess μ (fun t ω => 𝒴 t ω x x') (fun _ _ => 0)
      (fun a t ω => kNoise D0 η P D' a (Y t ω) x x') := fun _ x x' => by
    exact h𝒴.map_clm (eCLM x x')
  have h1 := isNativeItoProcess_ofEntries fun y z => isNativeItoProcess_bInc hθ hlam hE () y z
  refine isNativeItoProcess_congr_coeff h1 (θ := bTimes θ) (measurable_bTimes hθ)
    (fun _ => stronglyMeasurable_const)
    (fun a => fun T =>
      (contDiff_kNoise D0 η P D a (k := 0)).continuous.comp_stronglyMeasurable (hXp T)) ?_
  filter_upwards [hX] with x hx t ht
  refine ⟨by ext y z; simp only [Matrix.of_apply, mul_zero, ite_self, Finset.sum_const_zero,
    Matrix.zero_apply], fun a => ?_⟩
  ext y z
  rw [hx t, kNoise_mul D0 η P (Y t x) (bornL θ lam t x) (hsig t x) a, sandwich_apply,
    Matrix.of_apply]
  exact (ite_sum_eq_cf θ lam t x y z _ (ne_bTime (ne_of_ne_bTimes ht) 0 y z)).symm

end BlockBand.SourceProcess.ComplexCoupled
