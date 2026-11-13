module

public import BlockBand.SourceProcess.SmallLeak.LeakMean

/-!
# The far birth mass of the newborn tag

A normalized tag's far birth mass is `O(g/W)`, by the weighted inverse bound. The newborn
tag is `Y_{j+1;j} = D₊*D₊` (`Bridge.ae_tagResponse_succ_new_full`), `D₊ = [𝒢₁₂, 𝒢₁₁Kℝ₀₁]`, so
`D₊F = (𝒢₁₁K)(ιℝF)` (`freshD_mul_farEmbed`) and
`Re Tr F D₊*D₊ ≤ ‖𝒢₁₁K‖² g/(4η²)` (`birth_leak_le`); the weight `q_j/W²` gives the `1/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `𝒢₁₁K`, `K = z - X`. -/
def birthFactor (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (f : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  freshBlock b E (nearSchur (boundaryZ b E) XX) f true true *
    (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX)

theorem freshD_mul_farSel_conj (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (f : LayerSample W .oneBlockOnePort) :
    freshD b E XX f * (farSel W)ᴴ =
      birthFactor b E XX f * (nearSel W * twoPortResolvent b E XX * (farSel W)ᴴ) := by
  ext x y
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [freshD, birthFactor, farSel, nearSel, Matrix.mul_apply, Matrix.conjTranspose_apply,
    portBlock]

/-- **`D₊F = (𝒢₁₁K)(ιℝF)`.** -/
theorem freshD_mul_farEmbed (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (f : LayerSample W .oneBlockOnePort) (A : Matrix (Fin W) (Fin W) ℂ) :
    freshD b E XX f * farEmbed A = birthFactor b E XX f * leakInput b E XX (farEmbed A) := by
  rw [farEmbed_eq, leakInput, ← Matrix.mul_assoc, ← Matrix.mul_assoc, freshD_mul_farSel_conj]
  simp only [Matrix.mul_assoc]

/-- **The far birth mass**: `Re Tr F D₊*D₊ ≤ ‖𝒢₁₁K‖² g/(4η²)`. -/
theorem birth_leak_le {b E : ℝ} (hη : 0 < etaZ b E)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (f : LayerSample W .oneBlockOnePort)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A) (hA2 : A * A = A) :
    (farEmbed A * ((freshD b E XX f)ᴴ * freshD b E XX f)).trace.re ≤
      ‖birthFactor b E XX f‖ ^ 2 / (4 * etaZ b E ^ 2) * (farEmbed A *
        ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX) *
          farEmbed A).trace.re := by
  set F := farEmbed A
  set Dp := freshD b E XX f
  have hF : Fᴴ = F := farEmbed_conjTranspose_of hA
  have hF2 : F * F = F := by rw [farEmbed_mul, hA2]
  have e : (F * (Dpᴴ * Dp)).trace = ((Dp * F)ᴴ * (Dp * F)).trace := by
    calc (F * (Dpᴴ * Dp)).trace = (F * (F * (Dpᴴ * Dp))).trace := by
          rw [← Matrix.mul_assoc F F, hF2]
      _ = (F * (Dpᴴ * Dp) * F).trace := by rw [Matrix.trace_mul_comm F]
      _ = _ := by rw [Matrix.conjTranspose_mul, hF]; simp only [Matrix.mul_assoc]
  rw [e, trace_conjTranspose_mul_self, Complex.ofReal_re, freshD_mul_farEmbed,
    ← Real.sq_sqrt (show 0 ≤ (F * ((twoPortScattering b E XX)ᴴ * nearProjection W *
      twoPortScattering b E XX) * F).trace.re by
        rw [← hsNorm_sq_nearOut XX hA]; positivity)]
  have hV := hsNorm_leakInput hη XX hA
  have h1 := hsNorm_mul_le_opNorm (birthFactor b E XX f) (leakInput b E XX F)
  rw [hV] at h1
  have h2 := pow_le_pow_left₀ (hsNorm_nonneg _) h1 2
  refine h2.trans (le_of_eq ?_)
  simp only [F]
  ring

end BlockBand.SourceProcess.SmallLeak
