module

public import BlockBand.Endpoints.Response.PassDerivativeNorms

/-!
# The exact signed-source update of a scattering matrix

Abstract two-port pencil. Sites `ι`, lead channels `p`; a pencil `M` (the full path with its
matched leads, `𝓜 = [[H - E, C], [C*, z]]`), a lead coupling `V : ι × p` (inclusion of the lead
sites), the lead width `η = Im z ≥ 0`, and the Ward identity `M - M* = 2iη V V*`. The source is
`Γ = R* R` (in the application `R = Q_q^{1/2}/W` on interior blocks, so `iκR*R = iκQ_q/W²`).
Writing `G₀ = M⁻¹`, `K = R G₀ R*` (`= K_q/W²`), `N = R G₀ V` (`= M/W` in the physical
notation), `B = N* N` (`= B_q`), `𝕊_κ = I - 2iη V*(M + iκR*R)⁻¹V`:

* `pencilScattering_gram`: `𝕊*𝕊 = I - 4η (M⁻¹V)* Γ (M⁻¹V)` whenever
  `M - M* = 2i(ηVV* + Γ)`; hence `𝕊_κ` is a contraction for every `κ ≥ 0`
  (`pencilScattering_contraction`, also when the pencil is singular, with `M⁻¹ = 0`);
* `sourceResolvent_re`, `sourceResolvent_contraction`: `Re⟨v,(I + iκK)v⟩ = |v|² + κη|N* v|²`
  (`-Im K ⪰ 0`), so `(I + iκK)⁻¹` exists and is a contraction;
* `signedSource_update`: `𝕊_κ - 𝕊₀ = -2ηκ 𝕊₀ N*(I + iκK)⁻¹ N`, exactly, for every `κ ≥ 0`;
* `signedSource_error`: for `κ > 0`,
  `‖(𝕊_κ - 𝕊₀)/κ + 2η𝕊₀B‖₁ ≤ 2η Tr B · min(2, κ‖K‖)` (trace norm, `TraceBound`).

The zero-source derivative `∂𝕊 = -2η𝕊₀B` is the `κ ↓ 0` limit of the error bound; it is used
through `signedSource_error`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate

variable {ι p : Type*} [Fintype ι] [DecidableEq ι] [Fintype p] [DecidableEq p]

/-- Scattering matrix of the pencil `M` with lead coupling `V` and lead width `η`:
`𝕊(M) = I - 2iη V* M⁻¹ V` (Lean's totalized inverse; `M⁻¹ = 0` if `M` is singular). -/
def pencilScattering (η : ℝ) (V : Matrix ι p ℂ) (M : Matrix ι ι ℂ) : Matrix p p ℂ :=
  1 - (((2 * η : ℝ) : ℂ) * Complex.I) • (Vᴴ * M⁻¹ * V)

/-- The absorbed pencil `M + iκ R* R`. -/
def absorbedPencil (M R : Matrix ι ι ℂ) (κ : ℝ) : Matrix ι ι ℂ :=
  M + ((κ : ℂ) * Complex.I) • (Rᴴ * R)

/-- The source kernel `K = R M⁻¹ R*` (`= K_q/W²`). -/
def sourceKernel (M R : Matrix ι ι ℂ) : Matrix ι ι ℂ := R * M⁻¹ * Rᴴ

/-- The source frame `N = R M⁻¹ V` (`= Q_q^{1/2} G₀ V / W`). -/
def sourceFrame (M R : Matrix ι ι ℂ) (V : Matrix ι p ℂ) : Matrix ι p ℂ := R * M⁻¹ * V

/-- The source Gram matrix `B = N* N` (`= B_q = W⁻² U* Q_q U`, `U = G₀V`). -/
def pencilSourceGram (M R : Matrix ι ι ℂ) (V : Matrix ι p ℂ) : Matrix p p ℂ :=
  (sourceFrame M R V)ᴴ * sourceFrame M R V

omit [DecidableEq p] in
/-- `G - G* = G*(M* - M)G` for an invertible `M`, `G = M⁻¹`. -/
theorem inv_sub_conjTranspose_inv {M : Matrix ι ι ℂ} (hM : IsUnit M.det) :
    M⁻¹ - (M⁻¹)ᴴ = (M⁻¹)ᴴ * (Mᴴ - M) * M⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, ← conjTranspose_mul, mul_nonsing_inv _ hM,
    conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ hM, Matrix.mul_one]

omit [DecidableEq p] in
/-- `G - G* = G(M* - M)G*` for an invertible `M`, `G = M⁻¹`. -/
theorem inv_sub_conjTranspose_inv' {M : Matrix ι ι ℂ} (hM : IsUnit M.det) :
    M⁻¹ - (M⁻¹)ᴴ = M⁻¹ * (Mᴴ - M) * (M⁻¹)ᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, ← conjTranspose_mul,
    nonsing_inv_mul _ hM, conjTranspose_one, Matrix.mul_one, Matrix.one_mul]

/-- Unitarity defect. If `M - M* = 2i(ηVV* + Γ)`, then
`𝕊(M)*𝕊(M) = I - 4η (M⁻¹V)* Γ (M⁻¹V)` (`M` invertible). -/
theorem pencilScattering_gram {η : ℝ} {V : Matrix ι p ℂ} {M Γ : Matrix ι ι ℂ}
    (hM : IsUnit M.det)
    (hW : M - Mᴴ = ((2 : ℂ) * Complex.I) • ((η : ℂ) • (V * Vᴴ) + Γ)) :
    (pencilScattering η V M)ᴴ * pencilScattering η V M =
      1 - ((4 * η : ℝ) : ℂ) • ((M⁻¹ * V)ᴴ * Γ * (M⁻¹ * V)) := by
  set a : ℂ := ((2 * η : ℝ) : ℂ) * Complex.I with ha
  set X := Vᴴ * M⁻¹ * V
  set Z := (M⁻¹ * V)ᴴ * Γ * (M⁻¹ * V)
  have hXH : Xᴴ = Vᴴ * (M⁻¹)ᴴ * V := by simp [X, conjTranspose_mul, Matrix.mul_assoc]
  have h2 : M⁻¹ - (M⁻¹)ᴴ = -((M⁻¹)ᴴ * (M - Mᴴ) * M⁻¹) := by
    rw [inv_sub_conjTranspose_inv hM, ← neg_sub M Mᴴ, Matrix.mul_neg, Matrix.neg_mul]
  have key : Xᴴ = X + ((2 : ℂ) * Complex.I * η) • (Xᴴ * X) + ((2 : ℂ) * Complex.I) • Z := by
    have h1 : Xᴴ = X - Vᴴ * (M⁻¹ - (M⁻¹)ᴴ) * V := by
      rw [hXH]; simp only [X, Matrix.mul_sub, Matrix.sub_mul]; abel
    conv_lhs => rw [h1, h2, hW]
    rw [hXH]
    simp only [Z, X, conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, smul_add, smul_smul,
      Matrix.mul_assoc, add_assoc]
  have hS : pencilScattering η V M = 1 - a • X := rfl
  have hstar : star a = -a := by simp [ha]
  have hSH : (1 - a • X)ᴴ = 1 + a • Xᴴ := by
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hstar, neg_smul,
      sub_neg_eq_add]
  have hexp : (1 + a • Xᴴ) * (1 - a • X) = 1 - a • X + a • Xᴴ - (a * a) • (Xᴴ * X) := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    abel
  have s1 : a * ((2 : ℂ) * Complex.I * η) = ((-(4 * η ^ 2) : ℝ) : ℂ) := by
    rw [ha]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have s2 : a * ((2 : ℂ) * Complex.I) = ((-(4 * η) : ℝ) : ℂ) := by
    rw [ha]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have s3 : a * a = ((-(4 * η ^ 2) : ℝ) : ℂ) := by
    rw [ha]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hk : a • Xᴴ = a • X + ((-(4 * η ^ 2) : ℝ) : ℂ) • (Xᴴ * X) +
      ((-(4 * η) : ℝ) : ℂ) • Z := by
    conv_lhs => rw [key]
    rw [smul_add, smul_add, smul_smul, smul_smul, s1, s2]
  rw [hS, hSH, hexp, hk, s3]
  push_cast
  module

omit [DecidableEq ι] [DecidableEq p] in
/-- The anti-Hermitian part of the absorbed pencil:
`M_κ - M_κ* = (M - M*) + 2iκ R* R`. -/
theorem absorbedPencil_sub_conjTranspose (M R : Matrix ι ι ℂ) (κ : ℝ) :
    absorbedPencil M R κ - (absorbedPencil M R κ)ᴴ =
      (M - Mᴴ) + (((2 * κ : ℝ) : ℂ) * Complex.I) • (Rᴴ * R) := by
  have hstar : star ((κ : ℂ) * Complex.I) = -((κ : ℂ) * Complex.I) := by
    simp
  simp only [absorbedPencil, conjTranspose_add, conjTranspose_smul, conjTranspose_mul,
    conjTranspose_conjTranspose, hstar, neg_smul]
  have : (((2 * κ : ℝ) : ℂ) * Complex.I) • (Rᴴ * R) =
      ((κ : ℂ) * Complex.I) • (Rᴴ * R) + ((κ : ℂ) * Complex.I) • (Rᴴ * R) := by
    rw [← add_smul]; congr 1; push_cast; ring
  rw [this]
  abel

/-- Contraction. If `M - M* = 2iηVV* + 2iκR*R` with `η, κ ≥ 0`, then `𝕊(M)` is a contraction:
`|𝕊(M)v|² ≤ |v|²` (also for singular `M`, where `𝕊(M) = I`). -/
theorem pencilScattering_contraction {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ) +
      (((2 * κ : ℝ) : ℂ) * Complex.I) • (Rᴴ * R)) (v : p → ℂ) :
    vecNormSq (pencilScattering η V M *ᵥ v) ≤ vecNormSq v := by
  by_cases hM : IsUnit M.det
  · have hW' : M - Mᴴ = ((2 : ℂ) * Complex.I) • ((η : ℂ) • (V * Vᴴ) + (κ : ℂ) • (Rᴴ * R)) := by
      rw [hW, smul_add, smul_smul, smul_smul]
      congr 2 <;> push_cast <;> ring
    have hg := pencilScattering_gram hM hW'
    have hq := star_dotProduct_gram_mulVec (pencilScattering η V M) v
    rw [hg] at hq
    set Y := R * (M⁻¹ * V)
    have hZ : (M⁻¹ * V)ᴴ * ((κ : ℂ) • (Rᴴ * R)) * (M⁻¹ * V) = (κ : ℂ) • (Yᴴ * Y) := by
      simp only [Y, conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [hZ, smul_smul, sub_mulVec, one_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      star_dotProduct_self, star_dotProduct_gram_mulVec, smul_eq_mul] at hq
    have hre := congrArg Complex.re hq
    simp only [Complex.ofReal_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hre
    push_cast at hre
    have : vecNormSq (pencilScattering η V M *ᵥ v) =
        vecNormSq v - 4 * η * κ * vecNormSq (Y *ᵥ v) := by
      rw [← hre]; ring
    rw [this]
    have := vecNormSq_nonneg (Y *ᵥ v)
    have : 0 ≤ 4 * η * κ * vecNormSq (Y *ᵥ v) := by positivity
    linarith
  · have : pencilScattering η V M = 1 := by
      simp [pencilScattering, nonsing_inv_apply_not_isUnit _ hM]
    rw [this, one_mulVec]

/-!
### The signed-source update
-/

/-- Ward identity `V* G₀ = 𝕊₀ V* G₀*` when `M - M* = 2iη VV*`. -/
theorem ward_conjTranspose_inv {η : ℝ} {V : Matrix ι p ℂ} {M : Matrix ι ι ℂ}
    (hM : IsUnit M.det) (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ)) :
    Vᴴ * M⁻¹ = pencilScattering η V M * Vᴴ * (M⁻¹)ᴴ := by
  have h' : M⁻¹ - (M⁻¹)ᴴ =
      -((((2 * η : ℝ) : ℂ) * Complex.I) • (M⁻¹ * V * Vᴴ * (M⁻¹)ᴴ)) := by
    rw [inv_sub_conjTranspose_inv' hM, ← neg_sub M Mᴴ, hW]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  have h'' : M⁻¹ = (M⁻¹)ᴴ + (M⁻¹ - (M⁻¹)ᴴ) := by abel
  conv_lhs => rw [h'', h']
  simp only [pencilScattering, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
  abel

omit [DecidableEq p] in
/-- `K - K* = -2iη N N*` (`N = R M⁻¹ V`) when `M - M* = 2iη VV*`. -/
theorem sourceKernel_sub_conjTranspose {η : ℝ} {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hM : IsUnit M.det) (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ)) :
    sourceKernel M R - (sourceKernel M R)ᴴ =
      -((((2 * η : ℝ) : ℂ) * Complex.I) • (sourceFrame M R V * (sourceFrame M R V)ᴴ)) := by
  have hK : (sourceKernel M R)ᴴ = R * (M⁻¹)ᴴ * Rᴴ := by
    simp [sourceKernel, conjTranspose_mul, Matrix.mul_assoc]
  have hdiff : sourceKernel M R - (sourceKernel M R)ᴴ = R * (M⁻¹ - (M⁻¹)ᴴ) * Rᴴ := by
    rw [hK]; simp only [sourceKernel, Matrix.mul_sub, Matrix.sub_mul]
  rw [hdiff, inv_sub_conjTranspose_inv' hM, ← neg_sub M Mᴴ, hW]
  simp only [sourceFrame, conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]

omit [DecidableEq p] in
/-- `-Im K ⪰ 0`: `Re⟨v, (I + iκK)v⟩ = |v|² + κη |N* v|²`. -/
theorem sourceResolvent_re {η κ : ℝ} {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hM : IsUnit M.det) (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ))
    (v : ι → ℂ) :
    (star v ⬝ᵥ ((1 + ((κ : ℂ) * Complex.I) • sourceKernel M R) *ᵥ v)).re =
      vecNormSq v + κ * η * vecNormSq ((sourceFrame M R V)ᴴ *ᵥ v) := by
  set N := sourceFrame M R V
  set z := star v ⬝ᵥ (sourceKernel M R *ᵥ v)
  have hz : z - star z = -((((2 * η : ℝ) : ℂ) * Complex.I) * (vecNormSq (Nᴴ *ᵥ v) : ℂ)) := by
    have h1 := sourceKernel_sub_conjTranspose (R := R) hM hW
    have h2 : star v ⬝ᵥ ((sourceKernel M R - (sourceKernel M R)ᴴ) *ᵥ v) = z - star z := by
      rw [sub_mulVec, dotProduct_sub, star_dotProduct_conjTranspose_mulVec]
    rw [← h2, h1, neg_mulVec, smul_mulVec, dotProduct_neg, dotProduct_smul, smul_eq_mul]
    have h3 := star_dotProduct_gram_mulVec Nᴴ v
    rw [conjTranspose_conjTranspose] at h3
    rw [h3]
  have him : z.im = -(η * vecNormSq (Nᴴ *ᵥ v)) := by
    have := congrArg Complex.im hz
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.neg_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at this
    linarith
  rw [add_mulVec, one_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, star_dotProduct_self,
    smul_eq_mul, Complex.add_re, Complex.ofReal_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  rw [show (star v ⬝ᵥ (sourceKernel M R *ᵥ v)) = z from rfl, him]
  ring

omit [DecidableEq p] in
/-- `I + iκK` is invertible with `‖(I + iκK)⁻¹‖ ≤ 1` (`κ, η ≥ 0`). -/
theorem sourceResolvent_contraction {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hM : IsUnit M.det) (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ)) :
    IsUnit (1 + ((κ : ℂ) * Complex.I) • sourceKernel M R) ∧
      ‖(1 + ((κ : ℂ) * Complex.I) • sourceKernel M R)⁻¹‖ ≤ 1 := by
  have := accretive_isUnit_norm_inv_le (A := 1 + ((κ : ℂ) * Complex.I) • sourceKernel M R)
    (c := 1) one_pos fun v => by
      rw [sourceResolvent_re hM hW v, one_mul]
      have := vecNormSq_nonneg ((sourceFrame M R V)ᴴ *ᵥ v)
      have : 0 ≤ κ * η * vecNormSq ((sourceFrame M R V)ᴴ *ᵥ v) := by positivity
      linarith
  simpa using this

omit [DecidableEq p] in
/-- Woodbury: `(M + iκR*R)⁻¹ = G₀ - iκ G₀R*(I + iκK)⁻¹RG₀`. -/
theorem absorbedPencil_inv {M R : Matrix ι ι ℂ} {κ : ℝ} (hM : IsUnit M.det)
    (hA : IsUnit (1 + ((κ : ℂ) * Complex.I) • sourceKernel M R).det) :
    (absorbedPencil M R κ) * (M⁻¹ - ((κ : ℂ) * Complex.I) •
      (M⁻¹ * Rᴴ * (1 + ((κ : ℂ) * Complex.I) • sourceKernel M R)⁻¹ * R * M⁻¹)) = 1 := by
  unfold absorbedPencil
  set c : ℂ := (κ : ℂ) * Complex.I
  set K := sourceKernel M R
  set A := 1 + c • K
  have e1 : M * (M⁻¹ * Rᴴ * A⁻¹ * R * M⁻¹) = Rᴴ * A⁻¹ * R * M⁻¹ := by
    simp only [← Matrix.mul_assoc, mul_nonsing_inv M hM, Matrix.one_mul]
  have e2 : Rᴴ * R * (M⁻¹ * Rᴴ * A⁻¹ * R * M⁻¹) = Rᴴ * (K * A⁻¹) * R * M⁻¹ := by
    simp only [K, sourceKernel, Matrix.mul_assoc]
  have e3 : c • (K * A⁻¹) = 1 - A⁻¹ := by
    have h := mul_nonsing_inv A hA
    rw [show A = 1 + c • K from rfl, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h
    rw [eq_sub_iff_add_eq, add_comm]
    exact h
  have e4 : c • (c • (Rᴴ * (K * A⁻¹) * R * M⁻¹)) =
      c • (Rᴴ * R * M⁻¹) - c • (Rᴴ * A⁻¹ * R * M⁻¹) := by
    have : c • (Rᴴ * (K * A⁻¹) * R * M⁻¹) = Rᴴ * (c • (K * A⁻¹)) * R * M⁻¹ := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [this, e3, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, smul_sub]
  simp only [Matrix.add_mul, Matrix.mul_sub, mul_nonsing_inv M hM,
    Matrix.mul_smul, e1, Matrix.smul_mul, e2]
  rw [smul_add, e4]
  abel

/-- The signed-source update, exact for every `κ ≥ 0`: `𝕊_κ - 𝕊₀ = -2ηκ 𝕊₀ N*(I + iκK)⁻¹ N`. -/
theorem signedSource_update {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hM : IsUnit M.det) (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ)) :
    pencilScattering η V (absorbedPencil M R κ) - pencilScattering η V M =
      -(((2 * η * κ : ℝ) : ℂ)) • (pencilScattering η V M * (sourceFrame M R V)ᴴ *
        (1 + ((κ : ℂ) * Complex.I) • sourceKernel M R)⁻¹ * sourceFrame M R V) := by
  obtain ⟨hA, -⟩ := sourceResolvent_contraction (R := R) hη hκ hM hW
  have hAd := (isUnit_iff_isUnit_det _).1 hA
  have hinv := inv_eq_right_inv (absorbedPencil_inv (R := R) (κ := κ) hM hAd)
  have hward := ward_conjTranspose_inv hM hW
  set c : ℂ := (κ : ℂ) * Complex.I
  set A := 1 + c • sourceKernel M R
  have hcore : Vᴴ * (M⁻¹ * Rᴴ * A⁻¹ * R * M⁻¹) * V =
      pencilScattering η V M * (sourceFrame M R V)ᴴ * A⁻¹ * sourceFrame M R V := by
    have : Vᴴ * (M⁻¹ * Rᴴ * A⁻¹ * R * M⁻¹) * V = (Vᴴ * M⁻¹) * Rᴴ * A⁻¹ * (R * M⁻¹ * V) := by
      simp only [Matrix.mul_assoc]
    rw [this, hward]
    simp only [sourceFrame, conjTranspose_mul, Matrix.mul_assoc]
  simp only [pencilScattering]
  rw [hinv]
  have hac : (((2 * η : ℝ) : ℂ) * Complex.I) * c = -(((2 * η * κ : ℝ) : ℂ)) := by
    simp only [c]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hcore, smul_sub,
    smul_smul, hac]
  abel

omit [DecidableEq p] in
/-- `‖(I + iκK)⁻¹ - I‖ ≤ min(2, κ‖K‖)`. -/
theorem sourceResolvent_sub_one_norm_le {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hM : IsUnit M.det) (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ)) :
    ‖(1 + ((κ : ℂ) * Complex.I) • sourceKernel M R)⁻¹ - 1‖ ≤
      min 2 (κ * ‖sourceKernel M R‖) := by
  obtain ⟨hA, hn⟩ := sourceResolvent_contraction (V := V) (R := R) hη hκ hM hW
  have hAd := (isUnit_iff_isUnit_det _).1 hA
  set A := 1 + ((κ : ℂ) * Complex.I) • sourceKernel M R
  refine le_min ?_ ?_
  · calc ‖A⁻¹ - 1‖ ≤ ‖A⁻¹‖ + ‖(1 : Matrix ι ι ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hn l2_opNorm_one_le
      _ = 2 := by norm_num
  · have h := nonsing_inv_mul A hAd
    have hid : A⁻¹ - 1 = -(A⁻¹ * (((κ : ℂ) * Complex.I) • sourceKernel M R)) := by
      rw [show A = 1 + ((κ : ℂ) * Complex.I) • sourceKernel M R from rfl] at h
      conv_lhs => rw [← h]
      rw [Matrix.mul_add, Matrix.mul_one]
      abel
    rw [hid, norm_neg]
    calc ‖A⁻¹ * (((κ : ℂ) * Complex.I) • sourceKernel M R)‖
        ≤ ‖A⁻¹‖ * ‖((κ : ℂ) * Complex.I) • sourceKernel M R‖ := l2_opNorm_mul _ _
      _ ≤ 1 * ‖((κ : ℂ) * Complex.I) • sourceKernel M R‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = κ * ‖sourceKernel M R‖ := by
          rw [one_mul, norm_smul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hκ]

/-- The zero-source scattering matrix is a contraction: `‖𝕊₀‖ ≤ 1`. -/
theorem pencilScattering_norm_le_one {η : ℝ} (hη : 0 ≤ η) {V : Matrix ι p ℂ}
    {M : Matrix ι ι ℂ} (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ)) :
    ‖pencilScattering η V M‖ ≤ 1 :=
  l2_opNorm_le_one_of_contraction fun v =>
    pencilScattering_contraction (κ := 0) (R := 0) hη le_rfl (by simp [hW]) v

/-- The signed-source error, `κ`-multiplied form (every `κ ≥ 0`):
`‖𝕊_κ - 𝕊₀ + 2ηκ 𝕊₀B‖₁ ≤ 2ηκ Tr B · min(2, κ‖K‖)`. -/
theorem signedSource_error_mul {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hM : IsUnit M.det) (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ)) :
    TraceBound (pencilScattering η V (absorbedPencil M R κ) - pencilScattering η V M +
        (((2 * η * κ : ℝ) : ℂ)) • (pencilScattering η V M * pencilSourceGram M R V))
      (2 * η * κ * (pencilSourceGram M R V).trace.re * min 2 (κ * ‖sourceKernel M R‖)) := by
  set N := sourceFrame M R V
  set A := 1 + ((κ : ℂ) * Complex.I) • sourceKernel M R
  set S₀ := pencilScattering η V M
  have hid : pencilScattering η V (absorbedPencil M R κ) - S₀ +
      (((2 * η * κ : ℝ) : ℂ)) • (S₀ * pencilSourceGram M R V) =
      (-(((2 * η * κ : ℝ) : ℂ))) • (S₀ * (Nᴴ * (A⁻¹ - 1) * N)) := by
    rw [signedSource_update hη hκ hM hW]
    simp only [pencilSourceGram, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, smul_sub, neg_smul,
      Matrix.mul_assoc, N, S₀, A]
    abel
  rw [hid]
  have hg := traceBound_gram N (A⁻¹ - 1)
  have h1 := (hg.mul_left S₀).smul (-(((2 * η * κ : ℝ) : ℂ)))
  refine h1.mono ?_
  have hS := pencilScattering_norm_le_one hη hW
  have hm := sourceResolvent_sub_one_norm_le (V := V) (R := R) hη hκ hM hW
  have htr : 0 ≤ (Nᴴ * N).trace.re := by
    rw [trace_conjTranspose_mul_self_re_eq_hsSq]; exact hsSq_nonneg _
  have hnorm : ‖(-(((2 * η * κ : ℝ) : ℂ)))‖ = 2 * η * κ := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm]
  have hgram : (pencilSourceGram M R V).trace.re = (Nᴴ * N).trace.re := rfl
  rw [hgram]
  have h0 : 0 ≤ ‖A⁻¹ - 1‖ := norm_nonneg _
  have hS0 : 0 ≤ ‖S₀‖ := norm_nonneg _
  have : ‖S₀‖ * (‖A⁻¹ - 1‖ * (Nᴴ * N).trace.re) ≤
      (Nᴴ * N).trace.re * min 2 (κ * ‖sourceKernel M R‖) := by
    calc ‖S₀‖ * (‖A⁻¹ - 1‖ * (Nᴴ * N).trace.re) ≤ 1 * (‖A⁻¹ - 1‖ * (Nᴴ * N).trace.re) :=
          mul_le_mul_of_nonneg_right hS (mul_nonneg h0 htr)
      _ ≤ 1 * (min 2 (κ * ‖sourceKernel M R‖) * (Nᴴ * N).trace.re) := by
          gcongr
      _ = _ := by ring
  have h2 : 0 ≤ 2 * η * κ := by positivity
  calc 2 * η * κ * (‖S₀‖ * (‖A⁻¹ - 1‖ * (Nᴴ * N).trace.re))
      ≤ 2 * η * κ * ((Nᴴ * N).trace.re * min 2 (κ * ‖sourceKernel M R‖)) :=
        mul_le_mul_of_nonneg_left this h2
    _ = _ := by ring

/-- The signed-source error (`κ > 0`): `‖(𝕊_κ - 𝕊₀)/κ + 2η𝕊₀B‖₁ ≤ 2η Tr B · min(2, κ‖K‖)`. -/
theorem signedSource_error {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 < κ)
    {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hM : IsUnit M.det) (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ)) :
    TraceBound ((κ : ℂ)⁻¹ • (pencilScattering η V (absorbedPencil M R κ) -
        pencilScattering η V M) +
          ((2 * η : ℝ) : ℂ) • (pencilScattering η V M * pencilSourceGram M R V))
      (2 * η * (pencilSourceGram M R V).trace.re * min 2 (κ * ‖sourceKernel M R‖)) := by
  have h := (signedSource_error_mul (R := R) hη hκ.le hM hW).smul ((κ : ℂ)⁻¹)
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have e : (κ : ℂ)⁻¹ • (pencilScattering η V (absorbedPencil M R κ) - pencilScattering η V M +
      (((2 * η * κ : ℝ) : ℂ)) • (pencilScattering η V M * pencilSourceGram M R V)) =
      (κ : ℂ)⁻¹ • (pencilScattering η V (absorbedPencil M R κ) - pencilScattering η V M) +
        ((2 * η : ℝ) : ℂ) • (pencilScattering η V M * pencilSourceGram M R V) := by
    rw [smul_add, smul_smul]
    congr 2
    push_cast
    field_simp
  rw [e] at h
  refine h.mono (le_of_eq ?_)
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  field_simp

end BlockBand.Endpoints
