module

public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GenChain

/-!
# Generator calculus by data

For an SDE with drift `b : E → E` and noise `σ : κ → E → E`, `GenAt b σ g y L Γ` records that
`g : E → ℝ` is `C²`, its generator at `y` is `L` (`sdeGenerator b σ g y = L`) and its noise
derivatives at `y` are `Γ a = Dg(y)[σ_a(y)]`. The rules are the Itô product rule
`𝓛(gh) = g𝓛h + h𝓛g + Σ_a Γ_a g Γ_a h` (`GenAt.mul`, from `vecGen_bilin`), linearity, constants
and coordinates (`GenAt.coord`). They reduce the generator of a polynomial expression in the
coordinates to algebra on the data.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.Stochastic.GramUniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*} [Fintype κ]

/-- Generator data of `g` at `y`. -/
structure GenAt (b : E → E) (σ : κ → E → E) (g : E → ℝ) (y : E) (L : ℝ) (Γ : κ → ℝ) : Prop where
  smooth : ContDiff ℝ 2 g
  gen : sdeGenerator b σ g y = L
  dir : ∀ a, fderiv ℝ g y (σ a y) = Γ a

variable {b : E → E} {σ : κ → E → E} {y : E}

theorem GenAt.vecGen {g : E → ℝ} {L : ℝ} {Γ : κ → ℝ} (h : GenAt b σ g y L Γ) :
    SourceSDE.vecGen b σ g y = L := by
  rw [← sdeGenerator_eq_vecGen]; exact h.gen

theorem GenAt.const (c : ℝ) : GenAt b σ (fun _ => c) y 0 (fun _ => 0) := by
  refine ⟨contDiff_const, ?_, fun a => ?_⟩
  · rw [sdeGenerator_eq_vecGen, vecGen_const]
  · simp

theorem GenAt.add {g h : E → ℝ} {L₁ L₂ : ℝ} {Γ₁ Γ₂ : κ → ℝ} (H₁ : GenAt b σ g y L₁ Γ₁)
    (H₂ : GenAt b σ h y L₂ Γ₂) :
    GenAt b σ (fun q => g q + h q) y (L₁ + L₂) (fun a => Γ₁ a + Γ₂ a) := by
  refine ⟨H₁.smooth.add H₂.smooth, ?_, fun a => ?_⟩
  · rw [sdeGenerator_eq_vecGen, vecGen_add b σ H₁.smooth H₂.smooth, H₁.vecGen, H₂.vecGen]
  · rw [fderiv_add_apply' (differentiable_of_contDiff H₁.smooth y)
      (differentiable_of_contDiff H₂.smooth y), H₁.dir, H₂.dir]

theorem GenAt.sub {g h : E → ℝ} {L₁ L₂ : ℝ} {Γ₁ Γ₂ : κ → ℝ} (H₁ : GenAt b σ g y L₁ Γ₁)
    (H₂ : GenAt b σ h y L₂ Γ₂) :
    GenAt b σ (fun q => g q - h q) y (L₁ - L₂) (fun a => Γ₁ a - Γ₂ a) := by
  refine ⟨H₁.smooth.sub H₂.smooth, ?_, fun a => ?_⟩
  · rw [sdeGenerator_eq_vecGen, vecGen_sub b σ H₁.smooth H₂.smooth, H₁.vecGen, H₂.vecGen]
  · rw [fderiv_sub_apply' (differentiable_of_contDiff H₁.smooth y)
      (differentiable_of_contDiff H₂.smooth y), H₁.dir, H₂.dir]

/-- **Itô product rule.** -/
theorem GenAt.mul {g h : E → ℝ} {L₁ L₂ : ℝ} {Γ₁ Γ₂ : κ → ℝ} (H₁ : GenAt b σ g y L₁ Γ₁)
    (H₂ : GenAt b σ h y L₂ Γ₂) :
    GenAt b σ (fun q => g q * h q) y (g y * L₂ + h y * L₁ + ∑ a, Γ₁ a * Γ₂ a)
      (fun a => g y * Γ₂ a + h y * Γ₁ a) := by
  have hB := vecGen_bilin b σ (ContinuousLinearMap.mul ℝ ℝ) H₁.smooth H₂.smooth y
  simp only [ContinuousLinearMap.mul_apply'] at hB
  refine ⟨H₁.smooth.mul H₂.smooth, ?_, fun a => ?_⟩
  · rw [sdeGenerator_eq_vecGen, hB, H₁.vecGen, H₂.vecGen]
    simp only [H₁.dir, H₂.dir]
    ring
  · have h1 := fderiv_bilin_apply (ContinuousLinearMap.mul ℝ ℝ)
      (differentiable_of_contDiff H₁.smooth y) (differentiable_of_contDiff H₂.smooth y) (σ a y)
    simp only [ContinuousLinearMap.mul_apply'] at h1
    rw [h1, H₁.dir, H₂.dir]
    ring

theorem GenAt.const_mul {g : E → ℝ} {L : ℝ} {Γ : κ → ℝ} (c : ℝ) (H : GenAt b σ g y L Γ) :
    GenAt b σ (fun q => c * g q) y (c * L) (fun a => c * Γ a) := by
  have h := (GenAt.const (b := b) (σ := σ) (y := y) c).mul H
  simp only [mul_zero, add_zero, zero_mul, Finset.sum_const_zero] at h
  exact h

theorem GenAt.congr {g : E → ℝ} {L L' : ℝ} {Γ Γ' : κ → ℝ} (H : GenAt b σ g y L Γ)
    (hL : L = L') (hΓ : ∀ a, Γ a = Γ' a) : GenAt b σ g y L' Γ' :=
  ⟨H.smooth, H.gen.trans hL, fun a => (H.dir a).trans (hΓ a)⟩

theorem GenAt.congr_fun {g g' : E → ℝ} {L : ℝ} {Γ : κ → ℝ} (H : GenAt b σ g y L Γ)
    (hg : g = g') : GenAt b σ g' y L Γ := hg ▸ H

theorem GenAt.sq {g : E → ℝ} {L : ℝ} {Γ : κ → ℝ} (H : GenAt b σ g y L Γ) :
    GenAt b σ (fun q => g q * g q) y (2 * g y * L + ∑ a, Γ a * Γ a)
      (fun a => 2 * g y * Γ a) :=
  (H.mul H).congr (by ring) fun a => by ring

/-- Coordinates. -/
theorem GenAt.coord {n : ℕ} {b : (Fin n → ℝ) → Fin n → ℝ} {σ : κ → (Fin n → ℝ) → Fin n → ℝ}
    {y : Fin n → ℝ} (i : Fin n) :
    GenAt b σ (fun q => q i) y (b y i) (fun a => σ a y i) := by
  have hc : ContDiff ℝ 2 (fun q : Fin n → ℝ => q i) := contDiff_apply ℝ ℝ i
  refine ⟨hc, ?_, fun a => ?_⟩
  · rw [sdeGenerator_eq_vecGen]
    have h := vecGen_clm b σ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
      (G := fun q => q) contDiff_id y
    simp only [ContinuousLinearMap.proj_apply] at h
    rw [h, vecGen_id]
  · have : fderiv ℝ (fun q : Fin n → ℝ => q i) y =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).fderiv
    rw [this]; rfl

end BlockBand.Transmission.DualLift
