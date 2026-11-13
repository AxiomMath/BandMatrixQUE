module

public import BlockBand.Internal.Contracts.Critical
public import BlockBand.Endpoints.Poisson.PhaseFractionalMatrix

/-!
# The collar, its Cayley coordinates and its law

Support for the phase fractional-inverse lemma and the unitary log-comparison lemma. The objects
are those of `BlockBand.Internal.Contracts.Critical` (the setting of the collar kernel theorem):
the collar law `collarLaw W b`, its scattering matrix `U = collarScattering b e s ν ω`, the old
scattering `r = oldScattering b e X = I - 2iη(z_b - X)⁻¹`, `η = Im z_b`, the conductance
`g(r) = Re Tr(I - r*r)` and the matched distance `d(X)`.

* `boundaryZ_im_eq`, `boundaryZ_im_ge`: `η = (1-b)√(4-e²)/2 ≥ etaMin b κ > 0` on
  `bulkInterval κ`.
* `cayleyInv b e r = z_b I - 2iη (I - r)⁻¹` is the old response with scattering matrix `r`
  (the Cayley inverse; `oldScattering_cayleyInv`). For a strict contraction `r`,
  `-Im X ≻ 0` (`neg_imPart_cayleyInv_posDef`), as required by the strict clause of the contract.
* `scatteringDistance b e r = max_i |W⁻¹ Tr[(I - r)/(2iη)]_{ii} - a|` is `d(X)` written through
  `(z_b - X)⁻¹ = (I - r)/(2iη)`; `matchedDistance_cayleyInv`.
* The radial bounds: `d(tr) ≤ d(r) + (1-t)/(2η)` and
  `g(tr) ≤ g(r) + (1-t²)·2W` for a contraction `r`.
* The collar law is a probability measure; almost surely the GUE blocks are Hermitian and
  then `U` is a contraction (`ae_collar_hermitian`, `isContraction_collarScattering`); `U` is Borel
  measurable.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints.PhaseFractional

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexOrder ComplexConjugate

/-!
## The height `η = Im z_b`
-/

theorem matchedA_normSq {e : ℝ} (he : e ^ 2 ≤ 4) : Complex.normSq (matchedA e) = 1 := by
  rw [matchedA, Complex.normSq_mk]
  have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 4 - e ^ 2 by linarith)
  nlinarith

theorem boundaryZ_im_eq (b : ℝ) {e : ℝ} (he : e ^ 2 ≤ 4) :
    (boundaryZ b e).im = (1 - b) * Real.sqrt (4 - e ^ 2) / 2 := by
  rw [boundaryZ, Complex.add_im, Complex.inv_im, matchedA_normSq he, Complex.mul_im]
  simp [matchedA]
  ring

/-- A positive lower bound for `η` on `bulkInterval κ`. -/
def etaMin (b κ : ℝ) : ℝ := (1 - b) * Real.sqrt (3 * min κ 1) / 2

theorem etaMin_pos {b κ : ℝ} (hb : b < 1) (hκ : 0 < κ) : 0 < etaMin b κ := by
  unfold etaMin
  have : 0 < Real.sqrt (3 * min κ 1) := Real.sqrt_pos.mpr (by positivity)
  have : 0 < 1 - b := by linarith
  positivity

theorem sq_le_of_mem_bulk {κ e : ℝ} (he : e ∈ bulkInterval κ) :
    e ^ 2 ≤ (2 - min κ 1) ^ 2 := by
  obtain ⟨h1, h2⟩ := he
  have hm : min κ 1 ≤ κ := min_le_left _ _
  have hm1 : min κ 1 ≤ 1 := min_le_right _ _
  nlinarith

theorem boundaryZ_im_ge {b κ e : ℝ} (hb : b < 1) (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    etaMin b κ ≤ (boundaryZ b e).im := by
  have hsq := sq_le_of_mem_bulk he
  have hm0 : 0 < min κ 1 := lt_min hκ one_pos
  have hm1 : min κ 1 ≤ 1 := min_le_right _ _
  have he4 : e ^ 2 ≤ 4 := by nlinarith
  rw [boundaryZ_im_eq b he4, etaMin]
  have h3 : 3 * min κ 1 ≤ 4 - e ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h3
  have : 0 ≤ 1 - b := by linarith
  have := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h3) this
  linarith

theorem boundaryZ_im_pos {b κ e : ℝ} (hb : b < 1) (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    0 < (boundaryZ b e).im :=
  (etaMin_pos hb hκ).trans_le (boundaryZ_im_ge hb hκ he)

/-!
## Cayley coordinates of old responses
-/

/-- The scalar `2iη` of `oldScattering`. -/
def twoIEta (b e : ℝ) : ℂ := 2 * ((boundaryZ b e).im : ℂ) * Complex.I

theorem twoIEta_ne_zero {b e : ℝ} (hη : 0 < (boundaryZ b e).im) : twoIEta b e ≠ 0 := by
  unfold twoIEta
  have : ((boundaryZ b e).im : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  simp [this, Complex.I_ne_zero]

theorem norm_twoIEta_inv {b e : ℝ} (hη : 0 < (boundaryZ b e).im) :
    ‖(twoIEta b e)⁻¹‖ = 1 / (2 * (boundaryZ b e).im) := by
  rw [norm_inv, twoIEta, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hη]
  simp

/-- The old response with scattering matrix `r`: `X = z_b I - 2iη (I - r)⁻¹`. -/
def cayleyInv (b e : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (r : Matrix κ κ ℂ) :
    Matrix κ κ ℂ :=
  boundaryZ b e • (1 : Matrix κ κ ℂ) - twoIEta b e • (1 - r)⁻¹

theorem boundaryZ_sub_cayleyInv (b e : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r : Matrix κ κ ℂ) : boundaryZ b e • (1 : Matrix κ κ ℂ) - cayleyInv b e r =
      twoIEta b e • (1 - r)⁻¹ := by
  rw [cayleyInv]; abel

theorem inv_boundaryZ_sub_cayleyInv {b e : ℝ} (hη : 0 < (boundaryZ b e).im) {κ : Type*}
    [Fintype κ] [DecidableEq κ] {r : Matrix κ κ ℂ} (hr : IsUnit (1 - r).det) :
    (boundaryZ b e • (1 : Matrix κ κ ℂ) - cayleyInv b e r)⁻¹ = (twoIEta b e)⁻¹ • (1 - r) := by
  rw [boundaryZ_sub_cayleyInv]
  apply inv_eq_right_inv
  rw [smul_mul_smul_comm, nonsing_inv_mul _ hr, mul_inv_cancel₀ (twoIEta_ne_zero hη), one_smul]

theorem oldScattering_cayleyInv {b e : ℝ} (hη : 0 < (boundaryZ b e).im) {W : ℕ}
    {r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hr : IsUnit (1 - r).det) :
    oldScattering b e (cayleyInv b e r) = r := by
  rw [oldScattering, inv_boundaryZ_sub_cayleyInv hη hr, ← twoIEta, smul_smul,
    mul_inv_cancel₀ (twoIEta_ne_zero hη), one_smul]
  abel

/-- `-Im X = η 𝒫(r)` for `X = cayleyInv r`. -/
theorem neg_imPart_cayleyInv (b e : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r : Matrix κ κ ℂ) :
    -imPart (cayleyInv b e r) = (((boundaryZ b e).im : ℝ) : ℂ) • portKernel r := by
  rw [imPart, cayleyInv, portKernel, twoIEta, conjTranspose_sub, conjTranspose_smul,
    conjTranspose_smul, conjTranspose_one, conjTranspose_nonsing_inv, conjTranspose_sub,
    conjTranspose_one]
  have hz : star (boundaryZ b e) = boundaryZ b e - 2 * ((boundaryZ b e).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp; ring
  rw [hz]
  have hI : star (2 * ((boundaryZ b e).im : ℂ) * Complex.I) =
      -(2 * ((boundaryZ b e).im : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp
  rw [hI]
  ext i j
  simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    smul_eq_mul, neg_smul]
  have h2 : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

theorem portKernel_isHermitian {κ : Type*} [Fintype κ] [DecidableEq κ] (r : Matrix κ κ ℂ) :
    (portKernel r).IsHermitian := by
  rw [IsHermitian, portKernel, conjTranspose_sub, conjTranspose_add, conjTranspose_one,
    conjTranspose_nonsing_inv, conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_sub,
    conjTranspose_one, conjTranspose_conjTranspose]
  abel

/-- For a strict contraction `r`, `-Im X ≻ 0`, `X = cayleyInv r` (`η > 0`). -/
theorem neg_imPart_cayleyInv_posDef {b e : ℝ} (hη : 0 < (boundaryZ b e).im) {κ : Type*}
    [Fintype κ] [DecidableEq κ] {r : Matrix κ κ ℂ} (hr : IsStrictContraction r) :
    (-imPart (cayleyInv b e r)).PosDef := by
  rw [neg_imPart_cayleyInv]
  have hu := hr.isUnit_det
  apply PosDef.of_dotProduct_mulVec_pos
  · rw [IsHermitian, conjTranspose_smul, portKernel_isHermitian r]
    simp [Complex.conj_ofReal]
  · intro x hx
    rw [smul_mulVec, dotProduct_smul, quad_portKernel, ← resolventQuad]
    have h1 := two_re_quad_sub_eq r hu x
    set y := (1 - r)⁻¹ *ᵥ x with hy
    have hy0 : y ≠ 0 := by
      intro h0
      apply hx
      rw [eq_sub_mulVec_inv hu x, ← hy, h0]
      simp
    have h2 := hr y hy0
    have hre : resolventQuad r x + conj (resolventQuad r x) - star x ⬝ᵥ x =
        ((2 * (resolventQuad r x).re - quadNorm x : ℝ) : ℂ) := by
      rw [star_dotProduct_self_eq]
      apply Complex.ext <;> simp; ring
    rw [hre, smul_eq_mul, ← Complex.ofReal_mul]
    exact_mod_cast mul_pos hη (by linarith)

/-!
## Scalar distance through the scattering matrix
-/

/-- `d` expressed through `r`: `max_i |W⁻¹ Tr[(I - r)/(2iη)]_{ii} - a|`. -/
def scatteringDistance (b e : ℝ) {W : ℕ} (r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  max ‖blockTrace ((twoIEta b e)⁻¹ • (1 - r)) 0 - matchedA e‖
    ‖blockTrace ((twoIEta b e)⁻¹ • (1 - r)) 1 - matchedA e‖

theorem matchedDistance_cayleyInv {b e : ℝ} (hη : 0 < (boundaryZ b e).im) {W : ℕ}
    {r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hr : IsUnit (1 - r).det) :
    matchedDistance b e (cayleyInv b e r) = scatteringDistance b e r := by
  rw [matchedDistance, inv_boundaryZ_sub_cayleyInv hη hr, scatteringDistance]

theorem blockTrace_sub {W : ℕ} (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) :
    blockTrace (A - B) j = blockTrace A j - blockTrace B j := by
  simp [blockTrace, Finset.sum_sub_distrib, mul_sub]

theorem blockTrace_smul {W : ℕ} (c : ℂ) (A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (j : Fin 2) : blockTrace (c • A) j = c * blockTrace A j := by
  simp [blockTrace, Finset.mul_sum]; ring_nf

/-- Perturbation of the scalar distance by the block traces of `r' - r`. -/
theorem scatteringDistance_le {b e : ℝ} (hη : 0 < (boundaryZ b e).im) {W : ℕ}
    (r r' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {B : ℝ}
    (hB : ∀ j, ‖blockTrace (r' - r) j‖ ≤ B) :
    scatteringDistance b e r' ≤ scatteringDistance b e r + B / (2 * (boundaryZ b e).im) := by
  have key : ∀ j, ‖blockTrace ((twoIEta b e)⁻¹ • (1 - r')) j - matchedA e‖ ≤
      ‖blockTrace ((twoIEta b e)⁻¹ • (1 - r)) j - matchedA e‖ +
        B / (2 * (boundaryZ b e).im) := by
    intro j
    have hdiff : blockTrace ((twoIEta b e)⁻¹ • (1 - r')) j - matchedA e =
        (blockTrace ((twoIEta b e)⁻¹ • (1 - r)) j - matchedA e) -
          (twoIEta b e)⁻¹ * blockTrace (r' - r) j := by
      rw [blockTrace_smul, blockTrace_smul, blockTrace_sub, blockTrace_sub, blockTrace_sub]
      ring
    rw [hdiff]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_twoIEta_inv hη]
    have := hB j
    have h2 : 0 < 2 * (boundaryZ b e).im := by linarith
    gcongr
    calc 1 / (2 * (boundaryZ b e).im) * ‖blockTrace (r' - r) j‖
        ≤ 1 / (2 * (boundaryZ b e).im) * B := by gcongr
      _ = B / (2 * (boundaryZ b e).im) := by ring
  unfold scatteringDistance
  apply max_le
  · exact (key 0).trans (by gcongr; exact le_max_left _ _)
  · exact (key 1).trans (by gcongr; exact le_max_right _ _)

/-!
## Diagonal entries, traces and conductance of contractions
-/

theorem norm_apply_sq_le_quadNorm {κ : Type*} [Fintype κ] (w : κ → ℂ) (x : κ) :
    ‖w x‖ ^ 2 ≤ quadNorm w := by
  have : quadNorm w = ∑ i, ‖w i‖ ^ 2 := by
    rw [quadNorm, dotProduct]
    simp only [Pi.star_apply, Complex.re_sum]
    congr 1; ext i
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [this]
  exact Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ x)

theorem quadNorm_single {κ : Type*} [Fintype κ] [DecidableEq κ] (x : κ) :
    quadNorm (Pi.single x (1 : ℂ)) = 1 := by
  simp [quadNorm, dotProduct, Pi.single_apply]

theorem norm_diag_le_one {κ : Type*} [Fintype κ] [DecidableEq κ] {r : Matrix κ κ ℂ}
    (hr : IsContraction r) (x : κ) : ‖r x x‖ ≤ 1 := by
  have h1 := norm_apply_sq_le_quadNorm (r *ᵥ Pi.single x 1) x
  have h2 := hr (Pi.single x 1)
  rw [quadNorm_single] at h2
  have h3 : (r *ᵥ Pi.single x 1) x = r x x := by simp [mulVec_single]
  rw [h3] at h1
  nlinarith [norm_nonneg (r x x)]

theorem norm_blockTrace_le_one {W : ℕ} {r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hr : IsContraction r) (j : Fin 2) : ‖blockTrace r j‖ ≤ 1 := by
  unfold blockTrace
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have : ‖∑ a : Fin W, r (j, a) (j, a)‖ ≤ W := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a : Fin W, ‖r (j, a) (j, a)‖ ≤ ∑ _a : Fin W, (1 : ℝ) :=
          Finset.sum_le_sum fun a _ => norm_diag_le_one hr _
      _ = W := by simp
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  calc (W : ℝ)⁻¹ * ‖∑ a : Fin W, r (j, a) (j, a)‖ ≤ (W : ℝ)⁻¹ * W := by gcongr
    _ = 1 := inv_mul_cancel₀ hW'.ne'

/-- Radial regularization of the scalar distance. -/
theorem scatteringDistance_smul_le {b e : ℝ} (hη : 0 < (boundaryZ b e).im) {W : ℕ}
    {r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hr : IsContraction r) {t : ℝ}
    (ht1 : t ≤ 1) :
    scatteringDistance b e ((t : ℂ) • r) ≤
      scatteringDistance b e r + (1 - t) / (2 * (boundaryZ b e).im) := by
  apply scatteringDistance_le hη
  intro j
  have : (t : ℂ) • r - r = (((t - 1 : ℝ)) : ℂ) • r := by
    rw [Complex.ofReal_sub, sub_smul, Complex.ofReal_one, one_smul]
  rw [this, blockTrace_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  have := norm_blockTrace_le_one hr j
  nlinarith

theorem trace_conjTranspose_mul_self_re {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r : Matrix κ κ ℂ) : (rᴴ * r).trace.re = ∑ x, quadNorm (r *ᵥ Pi.single x 1) := by
  rw [trace, Complex.re_sum]
  congr 1; ext x
  rw [quadNorm, star_mulVec_dotProduct_mulVec]
  simp [mulVec_single, dotProduct, Pi.single_apply]

theorem trace_conjTranspose_mul_self_re_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r : Matrix κ κ ℂ} (hr : IsContraction r) : (rᴴ * r).trace.re ≤ Fintype.card κ := by
  rw [trace_conjTranspose_mul_self_re]
  calc ∑ x, quadNorm (r *ᵥ Pi.single x 1) ≤ ∑ _x : κ, (1 : ℝ) :=
        Finset.sum_le_sum fun x _ => (hr _).trans (quadNorm_single x).le
    _ = Fintype.card κ := by simp

theorem trace_conjTranspose_mul_self_re_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r : Matrix κ κ ℂ) : 0 ≤ (rᴴ * r).trace.re := by
  rw [trace_conjTranspose_mul_self_re]
  exact Finset.sum_nonneg fun x _ => quadNorm_nonneg _

theorem conductance_eq {κ : Type*} [Fintype κ] [DecidableEq κ] (r : Matrix κ κ ℂ) :
    conductance r = Fintype.card κ - (rᴴ * r).trace.re := by
  simp [conductance, trace_sub]

theorem conductance_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ] {r : Matrix κ κ ℂ}
    (hr : IsContraction r) : 0 ≤ conductance r := by
  rw [conductance_eq]; linarith [trace_conjTranspose_mul_self_re_le hr]

/-- Radial regularization of the conductance: `g(tr) ≤ g(r) + (1 - t²)·#ports`. -/
theorem conductance_smul_le {κ : Type*} [Fintype κ] [DecidableEq κ] {r : Matrix κ κ ℂ}
    (hr : IsContraction r) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    conductance ((t : ℂ) • r) ≤ conductance r + (1 - t ^ 2) * Fintype.card κ := by
  rw [conductance_eq, conductance_eq, conjTranspose_smul, smul_mul_smul_comm, trace_smul]
  have h1 : ((star (t : ℂ) * (t : ℂ)) • (rᴴ * r).trace).re = t ^ 2 * (rᴴ * r).trace.re := by
    simp [Complex.conj_ofReal, smul_eq_mul]
    left; ring
  rw [h1]
  have h2 := trace_conjTranspose_mul_self_re_le hr
  have h3 := trace_conjTranspose_mul_self_re_nonneg r
  have h4 : 0 ≤ 1 - t ^ 2 := by nlinarith
  nlinarith

end BlockBand.Endpoints.PhaseFractional
