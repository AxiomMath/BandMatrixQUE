module

public import BlockBand.SourceProcess.FullSourceCovariance.WardTensor

/-!
# The covariance of a Ward-form noise is a sum of four `Δ`-covariances

`cov_wardOf`: let `μ` be a probability measure, `D : Ω → Mat_W` with integrable entries and
`L²` centered bilinear forms, and `𝓔 = ι(DF) + (DF)*ι*` a.e. Then, with `x_i = ι*v_i`,
`y_i = Fv_i` and `⟨x, y⟩ := x*(D - ED)y`,
`E[(v₁*𝓔⁰v₂)(v₃*𝓔⁰v₄)] = E[⟨x₁,y₂⟩⟨x₃,y₄⟩] + E[⟨x₁,y₂⟩conj⟨x₄,y₃⟩] + E[⟨x₃,y₄⟩conj⟨x₂,y₁⟩]
  + conj E[⟨x₂,y₁⟩⟨x₄,y₃⟩]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PassiveCovariance

variable {W : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem matrixExpect_congr_ae {ι κ : Type*} {μ : Measure Ω} {U V : Ω → Matrix ι κ ℂ}
    (h : ∀ᵐ ω ∂μ, U ω = V ω) : matrixExpect μ U = matrixExpect μ V := by
  ext i j
  simp only [matrixExpect, Matrix.of_apply]
  exact integral_congr_ae (h.mono fun ω hω => by show U ω i j = V ω i j; rw [hω])

/-- **The four-term expansion** of the covariance of a Ward-form noise. -/
theorem cov_wardOf {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝓔 : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (D : Ω → Matrix (Fin W) (Fin W) ℂ)
    (F : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (hW : ∀ᵐ ω ∂μ, 𝓔 ω = wardOf (D ω) F)
    (hD : ∀ x y, Integrable (fun ω => D ω x y) μ)
    (hL2 : ∀ x y, MemLp (fun ω => bilinear x (D ω - matrixExpect μ D) y) 2 μ)
    (v₁ v₂ v₃ v₄ : Fin 2 × Fin W → ℂ) :
    let x := fun v : Fin 2 × Fin W → ℂ => nearSel W *ᵥ v
    let y := fun v : Fin 2 × Fin W → ℂ => F *ᵥ v
    bilinearCovariance μ 𝓔 v₁ v₂ v₃ v₄ =
      bilinearCovariance μ D (x v₁) (y v₂) (x v₃) (y v₄) +
        bilinearCrossCovariance μ D (x v₁) (y v₂) (x v₄) (y v₃) +
        bilinearCrossCovariance μ D (x v₃) (y v₄) (x v₂) (y v₁) +
        star (bilinearCovariance μ D (x v₂) (y v₁) (x v₄) (y v₃)) := by
  intro x y
  set D₀ := matrixExpect μ D
  set β : (Fin W → ℂ) → (Fin W → ℂ) → Ω → ℂ := fun x y ω => bilinear x (D ω - D₀) y with hβ
  have hE : matrixExpect μ 𝓔 = wardOf D₀ F :=
    (matrixExpect_congr_ae hW).trans (matrixExpect_wardOf D hD F)
  have hpt : ∀ᵐ ω ∂μ, ∀ v w : Fin 2 × Fin W → ℂ,
      bilinear v (𝓔 ω - matrixExpect μ 𝓔) w = β (x v) (y w) ω + star (β (x w) (y v) ω) := by
    filter_upwards [hW] with ω hω v w
    rw [hω, hE, wardOf_sub, wardOf, bilinear_ward]
  have hint : ∀ (f g : Ω → ℂ), MemLp f 2 μ → MemLp g 2 μ → Integrable (fun ω => f ω * g ω) μ :=
    fun f g hf hg => hf.integrable_mul hg
  have hs : ∀ x y, MemLp (fun ω => star (β x y ω)) 2 μ := fun x y => (hL2 x y).star
  have e1 := hint _ _ (hL2 (x v₁) (y v₂)) (hL2 (x v₃) (y v₄))
  have e2 := hint _ _ (hL2 (x v₁) (y v₂)) (hs (x v₄) (y v₃))
  have e3 := hint _ _ (hs (x v₂) (y v₁)) (hL2 (x v₃) (y v₄))
  have e4 := hint _ _ (hs (x v₂) (y v₁)) (hs (x v₄) (y v₃))
  have hcongr : (fun ω => bilinear v₁ (𝓔 ω - matrixExpect μ 𝓔) v₂ *
      bilinear v₃ (𝓔 ω - matrixExpect μ 𝓔) v₄) =ᵐ[μ] fun ω =>
      ((β (x v₁) (y v₂) ω * β (x v₃) (y v₄) ω + β (x v₁) (y v₂) ω * star (β (x v₄) (y v₃) ω)) +
        star (β (x v₂) (y v₁) ω) * β (x v₃) (y v₄) ω) +
        star (β (x v₂) (y v₁) ω) * star (β (x v₄) (y v₃) ω) := by
    filter_upwards [hpt] with ω hω
    rw [hω v₁ v₂, hω v₃ v₄]; ring
  have e12 : Integrable (fun ω => β (x v₁) (y v₂) ω * β (x v₃) (y v₄) ω +
      β (x v₁) (y v₂) ω * star (β (x v₄) (y v₃) ω)) μ := e1.add e2
  have e123 : Integrable (fun ω => (β (x v₁) (y v₂) ω * β (x v₃) (y v₄) ω +
      β (x v₁) (y v₂) ω * star (β (x v₄) (y v₃) ω)) +
      star (β (x v₂) (y v₁) ω) * β (x v₃) (y v₄) ω) μ := e12.add e3
  rw [bilinearCovariance, integral_congr_ae hcongr, integral_add e123 e4,
    integral_add e12 e3, integral_add e1 e2]
  have h4 : ∫ ω, star (β (x v₂) (y v₁) ω) * star (β (x v₄) (y v₃) ω) ∂μ =
      star (∫ ω, β (x v₂) (y v₁) ω * β (x v₄) (y v₃) ω ∂μ) := by
    have e : (fun ω => star (β (x v₂) (y v₁) ω) * star (β (x v₄) (y v₃) ω)) =
        fun ω => star (β (x v₂) (y v₁) ω * β (x v₄) (y v₃) ω) := by
      funext ω; rw [star_mul']
    rw [e]
    exact integral_conj
  have h3 : ∫ ω, star (β (x v₂) (y v₁) ω) * β (x v₃) (y v₄) ω ∂μ =
      ∫ ω, β (x v₃) (y v₄) ω * star (β (x v₂) (y v₁) ω) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  rw [h4, h3]
  rfl

end BlockBand.SourceProcess.FullSourceCovariance
