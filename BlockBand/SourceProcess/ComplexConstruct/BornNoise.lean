module

public import BlockBand.SourceProcess.ComplexUnique.NoiseTransfer
public import BlockBand.SourceProcess.ComplexUnique.Noise
public import BlockBand.SourceProcess.ModelExist.TransAlg

/-!
# The `𝒦` noise in a born frame: brackets of the model clauses

For an ambient frame `X ∈ ℂ^{ι × c'}` and a congruence `L ∈ ℂ^{c' × c}` with `L𝖣Lᴴ = 𝖣'`, the
born frame is `V = XL`, with Gram state `gramPair P (XL) = congrGram L (gramPair P X)`.
* `gramProjection_mul`: `P'(XL, 𝖣) = P'(X, 𝖣')`, so the `𝒦` noise is a congruence:
  `kNoise_mul : kNoise(XL, 𝖣) = Lᴴ kNoise(X, 𝖣') L` (and the same for the frame diffusion,
  `sourceDiffusion_mul`).
* `born_bracket_star`, `born_bracket_M`, `born_bracket_B`: the `𝒦` brackets of a born frame, in
  the form of the integrands of the complex model clauses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.ComplexUnique BlockBand.SourceProcess.ModelExist

variable {ι c c' : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c] [Fintype c']

omit [Fintype ι] [DecidableEq ι] [DecidableEq c] in
/-- The transported projection of a born frame is that of the ambient frame. -/
theorem gramProjection_mul (P : Matrix ι ι ℂ) (X : Matrix ι c' ℂ) (L : Matrix c' c ℂ)
    {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ} (hsig : L * D * Lᴴ = D') :
    gramProjection P (X * L) D = gramProjection P X D' := by
  unfold gramProjection
  rw [← hsig, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

omit [DecidableEq ι] [Fintype c] [DecidableEq c] in
/-- The born Gram state is the congruent ambient Gram state. -/
theorem gramPair_mul (P : Matrix ι ι ℂ) (X : Matrix ι c' ℂ) (L : Matrix c' c ℂ) :
    gramPair P (X * L) = congrGram L (gramPair P X) := by
  simp only [gramPair, sourceGram, nearGram, congrGram, conjTranspose_mul, Matrix.mul_assoc]

omit [DecidableEq c] in
/-- **The `𝒦` noise of a born frame is a congruence of the ambient one.** -/
theorem kNoise_mul (D0 η : ℝ) (P : Matrix ι ι ℂ) (X : Matrix ι c' ℂ) (L : Matrix c' c ℂ)
    {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ} (hsig : L * D * Lᴴ = D') (a : SourceNoise ι) :
    kNoise D0 η P D a (X * L) = Lᴴ * kNoise D0 η P D' a X * L := by
  unfold kNoise
  rw [gramProjection_mul P X L hsig, conjTranspose_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

omit [DecidableEq c] in
/-- The frame diffusion of a born frame is the ambient diffusion times `L`. -/
theorem sourceDiffusion_mul (D0 : ℝ) (P : Matrix ι ι ℂ) (X : Matrix ι c' ℂ) (L : Matrix c' c ℂ)
    {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ} (hsig : L * D * Lᴴ = D') (a : SourceNoise ι) :
    sourceDiffusion D0 P D a (X * L) = sourceDiffusion D0 P D' a X * L := by
  unfold sourceDiffusion
  rw [gramProjection_mul P X L hsig]
  simp only [Matrix.smul_mul, Matrix.mul_assoc]

variable {D0 : ℝ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} {V : Matrix ι c ℂ}
  {G : Matrix c c ℂ × Matrix c c ℂ}

omit [DecidableEq c] in

/-- **Sesquilinear `𝒦` bracket** in the form `2η²D₀ B_ik (C₀)_lj`
(clause `antiholomorphic`).
-/
theorem born_bracket_star (hD0 : 0 ≤ D0) (η : ℝ) (hDh : Dᴴ = D) (hPH : Pᴴ = P)
    (hPP : P * P = P) (hG : GramFeasible D G) (hV : gramPair P V = G) (i j k l : c) :
    ∑ a, kNoise D0 η P D a V i j * star (kNoise D0 η P D a V k l) =
      ((2 * η ^ 2 * D0 : ℝ) : ℂ) * G.2 i k * gramC0 G.1 G.2 D l j := by
  rw [sum_kNoise_mul_star hD0, raw_B hPH hPP hV, raw_C0 hDh hPH hPP hG hV]

omit [DecidableEq c] in

/-- **`𝒦`–`M` bracket** in the form `-iηD₀ B_il (C₀)_kj` (clause `crossM`). -/
theorem born_bracket_M (hD0 : 0 ≤ D0) (η : ℝ) (hDh : Dᴴ = D) (hPH : Pᴴ = P)
    (hPP : P * P = P) (hG : GramFeasible D G) (hV : gramPair P V = G) (i j k l : c) :
    ∑ a, kNoise D0 η P D a V i j * gramEntry (0, k, l) (gramNoise D0 P D a V) =
      -(Complex.I * ((η * D0 : ℝ) : ℂ)) * G.2 i l * gramC0 G.1 G.2 D k j := by
  have h := sum_kNoise_mul_gram hD0 η P D V 1 i j k l
  simp only [Matrix.mul_one] at h
  have e : ∀ a, gramEntry (0, k, l) (gramNoise D0 P D a V) =
      quadVariation 1 V (sourceDiffusion D0 P D a V) k l := fun a => by
    simp [gramEntry, gramNoise, gramVariation, quadVariation]
  simp only [e]
  rw [h, raw_B hPH hPP hV, raw_C0 hDh hPH hPP hG hV]

omit [DecidableEq c] in

/-- **`𝒦`–`B` bracket** in the form `-iηD₀ B_il (C₁ᴴ)_kj` (clause `crossB`). -/
theorem born_bracket_B (hD0 : 0 ≤ D0) (η : ℝ) (hDh : Dᴴ = D) (hPH : Pᴴ = P)
    (hPP : P * P = P) (hG : GramFeasible D G) (hV : gramPair P V = G) (i j k l : c) :
    ∑ a, kNoise D0 η P D a V i j * gramEntry (1, k, l) (gramNoise D0 P D a V) =
      -(Complex.I * ((η * D0 : ℝ) : ℂ)) * G.2 i l * (gramC1 G.1 G.2 D)ᴴ k j := by
  have h := sum_kNoise_mul_gram hD0 η P D V P i j k l
  have e : ∀ a, gramEntry (1, k, l) (gramNoise D0 P D a V) =
      quadVariation P V (sourceDiffusion D0 P D a V) k l := fun a => by
    simp [gramEntry, gramNoise, nearVariation, quadVariation]
  simp only [e]
  rw [h, raw_B hPH hPP hV, raw_C1 hDh hPH hPP hG hV]

end BlockBand.SourceProcess.ComplexConstruct
