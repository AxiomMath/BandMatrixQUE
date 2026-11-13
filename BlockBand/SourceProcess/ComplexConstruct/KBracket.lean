module

public import BlockBand.SourceProcess.ComplexConstruct.KInt
public import BlockBand.SourceProcess.ComplexConstruct.BornNoise
public import BlockBand.SourceProcess.Stochastic.ItoNative.Main
public import BlockBand.SourceProcess.Stochastic.GramChar.Bilinear
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AmbientFeasible

/-!
# Ambient products of the `𝒦` integral: product rule

For an Itô process `𝒴` (`IsNativeItoProcess`) in `Matrix c' c' ℂ` with **zero drift** and
diffusion `σ`, and an Itô process `𝒢` in `Matrix c' c' ℂ × Matrix c' c' ℂ` (drift `β`, diffusion
`ν`), Itô's product rule
(`itoProductRuleFor_holds`) gives, entrywise:
* `kk_nativeIto`: `𝒴_xy 𝒴_zw` has drift `Σ_a σ_xy σ_zw`;
* `kks_nativeIto`: `𝒴_xy conj 𝒴_zw` has drift `Σ_a σ_xy conj σ_zw`;
* `kg_nativeIto`: `𝒴_xy 𝒢_e` has drift `𝒴_xy β_e + Σ_a σ_xy ν_e`.
With `σ = kNoise(X)`, `𝒢 = gramPair P X` these drifts are, by the `kNoise` bracket identities,
`0`, `2η²D₀ 𝒢.2_xz (C₀)_wy`, and `𝒴_xy β_e - iηD₀ 𝒢.2_xw (C₀ or C₁ᴴ)_zy`
(`kNoise_brackets`, on feasible states).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.ComplexUnique
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {c' : Type*} [Fintype c'] [DecidableEq c']

/-- `(A, B) ↦ A_xy B_zw`. -/
def kMulBil (x y z w : c') : Matrix c' c' ℂ →L[ℝ] Matrix c' c' ℂ →L[ℝ] ℂ :=
  toCLM₂ (F₁ := Matrix c' c' ℂ) (F₂ := Matrix c' c' ℂ) (F₃ := ℂ)
    (LinearMap.mk₂ ℝ (fun A B => A x y * B z w)
      (fun _ _ _ => by simp only [Matrix.add_apply, add_mul])
      (fun _ _ _ => by simp only [Matrix.smul_apply, smul_mul_assoc])
      (fun _ _ _ => by simp only [Matrix.add_apply, mul_add])
      (fun _ _ _ => by simp only [Matrix.smul_apply, mul_smul_comm]))

/-- `(A, B) ↦ A_xy conj(B_zw)`. -/
def kStarBil (x y z w : c') : Matrix c' c' ℂ →L[ℝ] Matrix c' c' ℂ →L[ℝ] ℂ :=
  toCLM₂ (F₁ := Matrix c' c' ℂ) (F₂ := Matrix c' c' ℂ) (F₃ := ℂ)
    (LinearMap.mk₂ ℝ (fun A B => A x y * star (B z w))
      (fun _ _ _ => by simp only [Matrix.add_apply, add_mul])
      (fun _ _ _ => by simp only [Matrix.smul_apply, smul_mul_assoc])
      (fun _ _ _ => by simp only [Matrix.add_apply, star_add, mul_add])
      (fun _ _ _ => by simp only [Matrix.smul_apply, star_smul, star_trivial, mul_smul_comm]))

/-- `(A, H) ↦ A_xy gramEntry_e(H)`. -/
def kGramBil (x y : c') (e : Fin 2 × c' × c') :
    Matrix c' c' ℂ →L[ℝ] (Matrix c' c' ℂ × Matrix c' c' ℂ) →L[ℝ] ℂ :=
  toCLM₂ (F₁ := Matrix c' c' ℂ) (F₂ := Matrix c' c' ℂ × Matrix c' c' ℂ) (F₃ := ℂ)
    (LinearMap.mk₂ ℝ (fun A H => A x y * gramEntry e H)
      (fun _ _ _ => by simp only [Matrix.add_apply, add_mul])
      (fun _ _ _ => by simp only [Matrix.smul_apply, smul_mul_assoc])
      (fun _ _ _ => by
        simp only [gramEntry, Prod.fst_add, Prod.snd_add, Matrix.add_apply]
        split_ifs <;> ring)
      (fun _ _ _ => by
        simp only [gramEntry, Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply]
        split_ifs <;> exact mul_smul_comm _ _ _))

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {κ : Type*}
  [Fintype κ]

omit [DecidableEq c'] in
/-- **Product rule for `𝒴_xy 𝒴_zw`.** -/
theorem kk_nativeIto {Y : ℝ≥0 → DriverSample S κ → Matrix c' c' ℂ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Matrix c' c' ℂ}
    (hY : IsNativeItoProcess μ Y (fun _ _ => 0) σ) (x y z w : c') :
    IsNativeItoProcess μ (fun t ω => Y t ω x y * Y t ω z w)
      (fun t ω => ∑ a, σ a t ω x y * σ a t ω z w)
      (fun a t ω => σ a t ω x y * Y t ω z w + Y t ω x y * σ a t ω z w) := by
  have h := ItoNative.itoProductRuleFor_holds (κ := κ) μ (E := Matrix c' c' ℂ)
    (F := Matrix c' c' ℂ) (G := ℂ) _ _ _ _ _ _ hY hY (kMulBil x y z w)
  simpa [kMulBil, toCLM₂_apply] using h

omit [DecidableEq c'] in
/-- **Product rule for `𝒴_xy conj 𝒴_zw`.** -/
theorem kks_nativeIto {Y : ℝ≥0 → DriverSample S κ → Matrix c' c' ℂ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Matrix c' c' ℂ}
    (hY : IsNativeItoProcess μ Y (fun _ _ => 0) σ) (x y z w : c') :
    IsNativeItoProcess μ (fun t ω => Y t ω x y * star (Y t ω z w))
      (fun t ω => ∑ a, σ a t ω x y * star (σ a t ω z w))
      (fun a t ω => σ a t ω x y * star (Y t ω z w) + Y t ω x y * star (σ a t ω z w)) := by
  have h := ItoNative.itoProductRuleFor_holds (κ := κ) μ (E := Matrix c' c' ℂ)
    (F := Matrix c' c' ℂ) (G := ℂ) _ _ _ _ _ _ hY hY (kStarBil x y z w)
  simpa [kStarBil, toCLM₂_apply] using h

omit [DecidableEq c'] in
/-- **Product rule for `𝒴_xy 𝒢_e`.** -/
theorem kg_nativeIto {Y : ℝ≥0 → DriverSample S κ → Matrix c' c' ℂ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Matrix c' c' ℂ}
    {𝒢 β : ℝ≥0 → DriverSample S κ → Matrix c' c' ℂ × Matrix c' c' ℂ}
    {ν : κ → ℝ≥0 → DriverSample S κ → Matrix c' c' ℂ × Matrix c' c' ℂ}
    (hY : IsNativeItoProcess μ Y (fun _ _ => 0) σ) (h𝒢 : IsNativeItoProcess μ 𝒢 β ν) (x y : c')
    (e : Fin 2 × c' × c') :
    IsNativeItoProcess μ (fun t ω => Y t ω x y * gramEntry e (𝒢 t ω))
      (fun t ω => Y t ω x y * gramEntry e (β t ω) + ∑ a, σ a t ω x y * gramEntry e (ν a t ω))
      (fun a t ω => σ a t ω x y * gramEntry e (𝒢 t ω) + Y t ω x y * gramEntry e (ν a t ω)) := by
  have h := ItoNative.itoProductRuleFor_holds (κ := κ) μ (E := Matrix c' c' ℂ)
    (F := Matrix c' c' ℂ × Matrix c' c' ℂ) (G := ℂ) _ _ _ _ _ _ hY h𝒢 (kGramBil x y e)
  simpa [kGramBil, toCLM₂_apply] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq c'] in

/-- **The ambient `𝒦` brackets in the form of the complex model clauses**, at a frame satisfying
the two-projection
constraint (`η`, `D₀` arbitrary, `0 ≤ D₀`).
-/
theorem kNoise_brackets {D0 : ℝ} (hD0 : 0 ≤ D0) (η : ℝ) {P : Matrix ι ι ℂ} {D' : Matrix c' c' ℂ}
    (hPH : Pᴴ = P) (hPP : P * P = P) (hDh : D'ᴴ = D') {X : Matrix ι c' ℂ}
    (hX : TwoProjection P D' X) (x y z w : c') :
    (∑ a, kNoise D0 η P D' a X x y * kNoise D0 η P D' a X z w = 0) ∧
    (∑ a, kNoise D0 η P D' a X x y * star (kNoise D0 η P D' a X z w) =
      ((2 * η ^ 2 * D0 : ℝ) : ℂ) * (gramPair P X).2 x z *
        gramC0 (gramPair P X).1 (gramPair P X).2 D' w y) ∧
    (∑ a, kNoise D0 η P D' a X x y * gramEntry (0, z, w) (gramNoise D0 P D' a X) =
      -(Complex.I * ((η * D0 : ℝ) : ℂ)) * (gramPair P X).2 x w *
        gramC0 (gramPair P X).1 (gramPair P X).2 D' z y) ∧
    ∑ a, kNoise D0 η P D' a X x y * gramEntry (1, z, w) (gramNoise D0 P D' a X) =
      -(Complex.I * ((η * D0 : ℝ) : ℂ)) * (gramPair P X).2 x w *
        (gramC1 (gramPair P X).1 (gramPair P X).2 D')ᴴ z y := by
  have hG := gramFeasible_of_twoProjection hPH hPP hX
  exact ⟨sum_kNoise_mul D0 η P D' X x y z w,
    born_bracket_star hD0 η hDh hPH hPP hG rfl x y z w,
    born_bracket_M hD0 η hDh hPH hPP hG rfl x y z w,
    born_bracket_B hD0 η hDh hPH hPP hG rfl x y z w⟩

end BlockBand.SourceProcess.ComplexConstruct
