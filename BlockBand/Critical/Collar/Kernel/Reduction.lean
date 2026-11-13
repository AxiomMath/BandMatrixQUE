module

public import BlockBand.Critical.Collar.Kernel.Height

/-!
# The collar kernel bound: reduction to its regular clause

`CollarKernelRegularClause` states the regular (`C(1+g)`) clauses of `CollarKernelBounds`, and
`collarKernel_of_regular` shows that, together with the universal clauses, they give
`CollarKernelContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open MeasureTheory Matrix
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open scoped ComplexOrder

/-- The regular (`C(1+g)`) clauses of `CollarKernelBounds`, with the constants of the contract:
for `W ≥ W₀`, `e ∈ bulkInterval κ`, `|s| ≤ s₀`, `0 ≤ ν ≤ ν₀` and `d(X) ≤ d_*/2`,
* (strict) `Y ≻ 0`: `E𝒫(Ur) ⪯ C(1 + g)I`;
* (radial) `Y ⪰ 0`: for every `ε > 0`, `E𝒫(tUr) ⪯ (C(1 + g) + ε)I` for all `t < 1` close to one. -/
def CollarKernelRegularClause (b κ dstar C s₀ ν₀ : ℝ) (W₀ : ℕ) : Prop :=
  (∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ s ∈ Set.Icc (-s₀) s₀,
    ∀ ν ∈ Set.Icc 0 ν₀, ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      (-Critical.imPart X).PosDef → matchedDistance b e X ≤ dstar / 2 →
        (((C * (1 + Critical.conductance (Critical.oldScattering b e X)) : ℝ) : ℂ) •
            (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          Critical.expectedCollarKernel b e s ν 1 X).PosSemidef) ∧
  (∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ s ∈ Set.Icc (-s₀) s₀,
    ∀ ν ∈ Set.Icc 0 ν₀, ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      (-Critical.imPart X).PosSemidef → ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℝ, t₀ < 1 ∧
        ∀ t ∈ Set.Ioo t₀ 1, matchedDistance b e X ≤ dstar / 2 →
          (((C * (1 + Critical.conductance (Critical.oldScattering b e X)) + ε : ℝ) : ℂ) •
              (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
            Critical.expectedCollarKernel b e s ν t X).PosSemidef)

/-- `g = Tr(I - r*r) ≥ 0` for the old scattering matrix when `Y = -Im X ⪰ 0`. -/
theorem conductance_oldScattering_nonneg (b e : ℝ) (hη : 0 < (boundaryZ b e).im) {W : ℕ}
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef) :
    0 ≤ Critical.conductance (Critical.oldScattering b e X) := by
  have h := (one_sub_oldScattering_mul_conjTranspose_posSemidef b e hη hY).trace_nonneg
  rw [Critical.conductance]
  have htr : (1 - (Critical.oldScattering b e X)ᴴ * Critical.oldScattering b e X).trace =
      (1 - Critical.oldScattering b e X * (Critical.oldScattering b e X)ᴴ).trace := by
    rw [trace_sub, trace_sub, Matrix.trace_mul_comm]
  rw [htr]
  exact (Complex.nonneg_iff.1 h).1

/-- **Reduction**: the regular clause (for some constants `d_*, C, s₀, ν₀ > 0`, `W₀`) implies the
`CollarKernelContract`; the universal clauses are supplied by
`collarKernel_universal_all`.
-/
theorem collarKernel_of_regular
    (hreg : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (dstar C s₀ ν₀ : ℝ) (W₀ : ℕ), 0 < dstar ∧ 0 < s₀ ∧ 0 < ν₀ ∧
        CollarKernelRegularClause b κ dstar C s₀ ν₀ W₀) :
    Critical.CollarKernelContract := by
  intro b hb0 hb κ hκ
  obtain ⟨dstar, Cr, s₀, ν₀, W₀, hd, hs₀, hν₀, hstrict, hrad⟩ := hreg b hb0 hb κ hκ
  obtain ⟨Cu, hCu, hu⟩ := collarKernel_universal_all hb0 hb hκ s₀ ν₀
  refine ⟨dstar, max Cr Cu, s₀, ν₀, W₀, hd, hs₀, hν₀, ?_, ?_⟩
  · intro W hW hW₀ e he s hs ν hν X hY
    obtain ⟨hηmin, hηe⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b)
      (by linarith) hκ he
    have hη : 0 < (boundaryZ b e).im := hηmin.trans_le hηe
    obtain ⟨h1, h2⟩ := (hu W hW e he s hs ν hν X).1 hY
    have hg := conductance_oldScattering_nonneg b e hη hY.posSemidef
    refine ⟨h1, posSemidef_smul_one_sub_mono h2 ?_, fun hdX => ?_⟩
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
    · exact posSemidef_smul_one_sub_mono (hstrict W hW hW₀ e he s hs ν hν X hY hdX)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · intro W hW hW₀ e he s hs ν hν X hY ε hε
    obtain ⟨hηmin, hηe⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b)
      (by linarith) hκ he
    have hη : 0 < (boundaryZ b e).im := hηmin.trans_le hηe
    have hg := conductance_oldScattering_nonneg b e hη hY
    obtain ⟨t₁, ht₁, hreg'⟩ := hrad W hW hW₀ e he s hs ν hν X hY ε hε
    refine ⟨max t₁ 0, max_lt ht₁ one_pos, fun t ht => ?_⟩
    have ht0 : 0 ≤ t := (le_max_right _ _).trans ht.1.le
    have ht1 : t₁ < t := (le_max_left _ _).trans_lt ht.1
    obtain ⟨h1, h2⟩ := (hu W hW e he s hs ν hν X).2 hY t ht0 ht.2
    refine ⟨h1, posSemidef_smul_one_sub_mono h2 ?_, fun hdX => ?_⟩
    · have := mul_le_mul_of_nonneg_right (le_max_right Cr Cu) (Real.sqrt_nonneg (W : ℝ))
      linarith
    · have h3 := hreg' t ⟨ht1, ht.2⟩ hdX
      refine posSemidef_smul_one_sub_mono h3 ?_
      have := mul_le_mul_of_nonneg_right (le_max_left Cr Cu) (by linarith : (0 : ℝ) ≤
        1 + Critical.conductance (Critical.oldScattering b e X))
      linarith

end BlockBand.Critical.Collar.Kernel
