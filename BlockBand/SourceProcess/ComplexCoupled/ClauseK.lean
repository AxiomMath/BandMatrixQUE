module

public import BlockBand.SourceProcess.ComplexCoupled.ClauseTools

/-!
# The stopped `𝒦` clauses for frame-driven Itô integrals

`Yk` is an Itô process in `Matrix c c ℂ` with zero drift and diffusion `kNoise(X)` for a
frame `X` with `Re tr(XᴴX) ≤ L` before an augmented stopping time `ρ`; `g` is a complex Itô
process with zero drift and diffusion `gramEntry e (gramNoise(X))`. For any `σ = ρ` a.s.:
* `kclause_lin`: `(Yk_{yz} - Yk_{yz}(0))^σ` is a martingale;
* `kclause_mul`, `kclause_star`: `(ΔYk_{yz} ΔYk_{y'z'} - ∫ Σ_a k_{yz} k_{y'z'})^σ` and the same
  with `conj ΔYk_{y'z'}` and `conj k_{y'z'}` are martingales;
* `gclause_mul`: `(ΔYk_{yz} Δg - ∫ Σ_a k_{yz} gramEntry e (gramNoise))^σ` is a martingale.
Each is stated for any process `F` a.s. equal to the compensated one.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.ComplexUnique

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c]

/-- `A ↦ (A_{yz}, A_{y'z'})`. -/
def pE (y z y' z' : c) : Matrix c c ℂ →L[ℝ] ℂ × ℂ := (eCLM y z).prod (eCLM y' z')

/-- `A ↦ (A_{yz}, conj A_{y'z'})`. -/
def pS (y z y' z' : c) : Matrix c c ℂ →L[ℝ] ℂ × ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (A y z, star (A y' z'))
      map_add' := fun A B => by simp only [Matrix.add_apply, star_add, Prod.mk_add_mk]
      map_smul' := fun r A => by
        simp only [Matrix.smul_apply, star_smul, star_trivial, RingHom.id_apply, Prod.smul_mk] }

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D0 η : ℝ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
  {Yk : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c c ℂ}
  {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
  {ρ σ : DriverSample S (SourceNoise ι) → WithTop ℝ≥0} {L : ℝ}
  {F : ℝ≥0 → DriverSample S (SourceNoise ι) → ℂ}

theorem continuous_kNoise_apply (D0 η : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (a : SourceNoise ι) : Continuous fun V : Matrix ι c ℂ => kNoise D0 η P D a V :=
  (contDiff_kNoise D0 η P D a (k := 0)).continuous

variable (hK : IsNativeItoProcess μ Yk (fun _ _ => 0) (fun a t x => kNoise D0 η P D a (X t x)))
  (hρ : IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ) ρ)
  (hρσ : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ρ x = σ x)
  (hL : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ s : ℝ≥0, (s : WithTop ℝ≥0) < ρ x →
    ((X s x)ᴴ * X s x).trace.re ≤ L)
include hK hρ hρσ hL

/-- **Linear `𝒦` clause.** -/
theorem kclause_lin (y z : c)
    (hF : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, F t x = Yk t x y z - Yk 0 x y z) :
    ∃ N : ℝ≥0 → DriverSample S (SourceNoise ι) → ℂ, Martingale N
      (driverAugmented (κ := SourceNoise ι) μ) (driverLaw (κ := SourceNoise ι) μ) ∧
      ∀ t, N t =ᵐ[driverLaw (κ := SourceNoise ι) μ] stoppedProcess F σ t := by
  have hZ := map_clm_zero hK (pE y z y z)
  exact clause_fst hZ hρ (nativeIntegrand_of_frame hZ hρ
    (f := fun a V => pE y z y z (kNoise D0 η P D a V))
    (fun a => (pE y z y z).continuous.comp (continuous_kNoise_apply D0 η P D a))
    (fun _ _ _ => rfl) hL) hρσ hF

/-- **Holomorphic `𝒦` product clause.** -/
theorem kclause_mul (y z y' z' : c)
    (hF : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, F t x =
      (Yk t x y z - Yk 0 x y z) * (Yk t x y' z' - Yk 0 x y' z') -
        ∫ s in Ioc (0 : ℝ) t, ∑ a, kNoise D0 η P D a (X s.toNNReal x) y z *
          kNoise D0 η P D a (X s.toNNReal x) y' z') :
    ∃ N : ℝ≥0 → DriverSample S (SourceNoise ι) → ℂ, Martingale N
      (driverAugmented (κ := SourceNoise ι) μ) (driverLaw (κ := SourceNoise ι) μ) ∧
      ∀ t, N t =ᵐ[driverLaw (κ := SourceNoise ι) μ] stoppedProcess F σ t := by
  have hZ := map_clm_zero hK (pE y z y' z')
  exact clause_mul hZ hρ (nativeIntegrand_of_frame hZ hρ
    (f := fun a V => pE y z y' z' (kNoise D0 η P D a V))
    (fun a => (pE y z y' z').continuous.comp (continuous_kNoise_apply D0 η P D a))
    (fun _ _ _ => rfl) hL) hρσ hF

/-- **Antiholomorphic `𝒦` product clause.** -/
theorem kclause_star (y z y' z' : c)
    (hF : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, F t x =
      (Yk t x y z - Yk 0 x y z) * (star (Yk t x y' z') - star (Yk 0 x y' z')) -
        ∫ s in Ioc (0 : ℝ) t, ∑ a, kNoise D0 η P D a (X s.toNNReal x) y z *
          star (kNoise D0 η P D a (X s.toNNReal x) y' z')) :
    ∃ N : ℝ≥0 → DriverSample S (SourceNoise ι) → ℂ, Martingale N
      (driverAugmented (κ := SourceNoise ι) μ) (driverLaw (κ := SourceNoise ι) μ) ∧
      ∀ t, N t =ᵐ[driverLaw (κ := SourceNoise ι) μ] stoppedProcess F σ t := by
  have hZ := map_clm_zero hK (pS y z y' z')
  exact clause_mul hZ hρ (nativeIntegrand_of_frame hZ hρ
    (f := fun a V => pS y z y' z' (kNoise D0 η P D a V))
    (fun a => (pS y z y' z').continuous.comp (continuous_kNoise_apply D0 η P D a))
    (fun _ _ _ => rfl) hL) hρσ hF

/-- **Cross clause with a Gram coordinate.** -/
theorem gclause_mul [DecidableEq c] {g : ℝ≥0 → DriverSample S (SourceNoise ι) → ℂ}
    (e : Fin 2 × c × c)
    (hg : IsNativeItoProcess μ g (fun _ _ => 0)
      (fun a t x => gramEntry e (gramNoise D0 P D a (X t x)))) (y z : c)
    (hF : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, F t x =
      (Yk t x y z - Yk 0 x y z) * (g t x - g 0 x) -
        ∫ s in Ioc (0 : ℝ) t, ∑ a, kNoise D0 η P D a (X s.toNNReal x) y z *
          gramEntry e (gramNoise D0 P D a (X s.toNNReal x))) :
    ∃ N : ℝ≥0 → DriverSample S (SourceNoise ι) → ℂ, Martingale N
      (driverAugmented (κ := SourceNoise ι) μ) (driverLaw (κ := SourceNoise ι) μ) ∧
      ∀ t, N t =ᵐ[driverLaw (κ := SourceNoise ι) μ] stoppedProcess F σ t := by
  have h1 := map_clm_zero hK (eCLM y z)
  have hZ := h1.prod hg
  have hZ' : IsNativeItoProcess μ (fun t x => (eCLM y z (Yk t x), g t x)) (fun _ _ => 0)
      (fun a t x => (eCLM y z (kNoise D0 η P D a (X t x)),
        gramEntry e (gramNoise D0 P D a (X t x)))) := hZ
  exact clause_mul hZ' hρ (nativeIntegrand_of_frame hZ' hρ
    (f := fun a V => (eCLM y z (kNoise D0 η P D a V), gramEntry e (gramNoise D0 P D a V)))
    (fun a => ((eCLM y z).continuous.comp (continuous_kNoise_apply D0 η P D a)).prodMk
      ((Stochastic.GramUniqueness.continuous_gramEntry e).comp
        (Stochastic.GramUniqueness.GramChart.contDiff_gramNoise D0 P D a (k := 0)).continuous))
    (fun _ _ _ => rfl) hL) hρσ hF

end BlockBand.SourceProcess.ComplexCoupled
