module

public import BlockBand.Endpoints.Poisson.SingleCollarWardTrace

/-!
# The Ward core of the remote scattering source for an abstract absorbing network

Setting. Sites `π ⊕ ν` (ports `π`, interior `ν`), a Hermitian `H`, `η ≥ 0`, a source strength
`a ≥ 0` and an orthogonal projection `D` on `ν` (the source set `C`). The network matrix is
`F_a = H + i·diag(ηI_π, aD)` (`scwNet`), `G_a = F_a⁻¹`, the complete scattering matrix
`S_a = I - 2iη (G_a)_{ππ}` (`scwScat`) and the Gram matrix `Q = (D𝒰)*(D𝒰)`, `𝒰 = (G_0)_{νπ}`
(`scwGram`). If `F_0`, `F_a` are invertible:

* `scw_one_sub_scat`: `I - S_a*S_a = 4ηa (G_a)_{νπ}* D (G_a)_{νπ}` (Ward identity);
  so `S_0` is unitary (`scw_scat_unitary`) and `S_a` a contraction (`scw_scat_contraction`);
* `scw_ward_defect`: `4ηa Q - (I - S_a*S_a) ⪰ 0`: `D(G_a)_{νπ} = T D𝒰` with
  `T = (I + iaDG_{νν}D)⁻¹` and `T*T ⪯ I` (the contraction is applied before the Gram product);
* `scw_ward_diff`: `Tr|S_a - S_0|^q ≤ (2ηa)^q Tr Q^q` for every `q > 0`: by the resolvent
  identity and the Ward identity, `S_a - S_0 = -2ηa S_0 (D𝒰)* T (D𝒰)`, and the sandwich bound
  `scw_schattenFrac_sandwich_le`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace)
open BlockBand.Endpoints.PhaseFractional (schattenFrac)
open scoped ComplexOrder

section Core

variable {π ν : Type} [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν]

/-- The absorption pattern `diag(ηI_π, aD)`. -/
def scwAbs (η a : ℝ) (D : Matrix ν ν ℂ) : Matrix (π ⊕ ν) (π ⊕ ν) ℂ :=
  fromBlocks ((η : ℂ) • 1) 0 0 ((a : ℂ) • D)

/-- The network matrix `F_a = H + i diag(ηI_π, aD)`. -/
def scwNet (H : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) (η a : ℝ) (D : Matrix ν ν ℂ) :
    Matrix (π ⊕ ν) (π ⊕ ν) ℂ :=
  H + Complex.I • scwAbs η a D

/-- The complete scattering matrix `S = I - 2iη G_{ππ}`. -/
def scwScat (η : ℝ) (G : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) : Matrix π π ℂ :=
  1 - (2 * (η : ℂ) * Complex.I) • G.toBlocks₁₁

/-- The source Gram matrix `(D G_{νπ})* (D G_{νπ})`. -/
def scwGram (D : Matrix ν ν ℂ) (G : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) : Matrix π π ℂ :=
  (D * G.toBlocks₂₁)ᴴ * (D * G.toBlocks₂₁)

omit [DecidableEq π] [DecidableEq ν] in
theorem scw_posSemidef_gram (D : Matrix ν ν ℂ) (G : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (scwGram D G).PosSemidef := posSemidef_conjTranspose_mul_self _

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_conjTranspose_toBlocks₁₁ (G : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (Gᴴ).toBlocks₁₁ = (G.toBlocks₁₁)ᴴ := by ext i j; rfl

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_conjTranspose_toBlocks₁₂ (G : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (Gᴴ).toBlocks₁₂ = (G.toBlocks₂₁)ᴴ := by ext i j; rfl

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_conjTranspose_toBlocks₂₂ (G : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (Gᴴ).toBlocks₂₂ = (G.toBlocks₂₂)ᴴ := by ext i j; rfl

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_toBlocks₁₁_sub (A B : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (A - B).toBlocks₁₁ = A.toBlocks₁₁ - B.toBlocks₁₁ := by ext i j; rfl

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_toBlocks₁₂_sub (A B : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (A - B).toBlocks₁₂ = A.toBlocks₁₂ - B.toBlocks₁₂ := by ext i j; rfl

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_toBlocks₂₁_sub (A B : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (A - B).toBlocks₂₁ = A.toBlocks₂₁ - B.toBlocks₂₁ := by ext i j; rfl

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_toBlocks₂₂_sub (A B : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (A - B).toBlocks₂₂ = A.toBlocks₂₂ - B.toBlocks₂₂ := by ext i j; rfl

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_toBlocks₁₁_smul (c : ℂ) (A : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ := by ext i j; rfl

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_toBlocks₁₂_smul (c : ℂ) (A : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (c • A).toBlocks₁₂ = c • A.toBlocks₁₂ := by ext i j; rfl

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_toBlocks₂₁_smul (c : ℂ) (A : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (c • A).toBlocks₂₁ = c • A.toBlocks₂₁ := by ext i j; rfl

omit [Fintype π] [DecidableEq π] [Fintype ν] [DecidableEq ν] in
theorem scw_toBlocks₂₂_smul (c : ℂ) (A : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (c • A).toBlocks₂₂ = c • A.toBlocks₂₂ := by ext i j; rfl

omit [Fintype π] [Fintype ν] [DecidableEq ν] in
theorem scw_abs_conjTranspose (η a : ℝ) {D : Matrix ν ν ℂ} (hD : Dᴴ = D) :
    (scwAbs (π := π) η a D)ᴴ = scwAbs η a D := by
  simp [scwAbs, fromBlocks_conjTranspose, conjTranspose_smul, hD]

/-- **Ward identity** `G - G* = -2i G* diag(ηI, aD) G` for `G = F_a⁻¹`. -/
theorem scw_ward_identity {H : Matrix (π ⊕ ν) (π ⊕ ν) ℂ} (hH : H.IsHermitian)
    {D : Matrix ν ν ℂ} (hD : Dᴴ = D) (η a : ℝ) (hF : IsUnit (scwNet H η a D).det) :
    (scwNet H η a D)⁻¹ - ((scwNet H η a D)⁻¹)ᴴ =
      (-2 * Complex.I) • (((scwNet H η a D)⁻¹)ᴴ * scwAbs η a D * (scwNet H η a D)⁻¹) := by
  set F := scwNet H η a D
  set G := F⁻¹
  have h1 : F * G = 1 := mul_nonsing_inv F hF
  have hGh : Gᴴ * Fᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hFh : Fᴴ - F = (-2 * Complex.I) • scwAbs η a D := by
    simp only [F, scwNet, conjTranspose_add, conjTranspose_smul, hH.eq,
      scw_abs_conjTranspose η a hD, Complex.star_def, Complex.conj_I]
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    congr 1; ring
  calc G - Gᴴ = Gᴴ * Fᴴ * G - Gᴴ * F * G := by
        rw [hGh, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    _ = Gᴴ * (Fᴴ - F) * G := by rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = _ := by rw [hFh, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq ν] in
theorem scw_abs_blocks₁₁ (η a : ℝ) (D : Matrix ν ν ℂ) (G : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (Gᴴ * scwAbs η a D * G).toBlocks₁₁ =
      (η : ℂ) • (G.toBlocks₁₁ᴴ * G.toBlocks₁₁) + (a : ℂ) • (G.toBlocks₂₁ᴴ * D * G.toBlocks₂₁) := by
  conv_lhs => rw [← fromBlocks_toBlocks G]
  simp only [fromBlocks_conjTranspose, scwAbs, fromBlocks_multiply, toBlocks_fromBlocks₁₁,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

omit [DecidableEq ν] in
theorem scw_abs_blocks₁₂ (η a : ℝ) (D : Matrix ν ν ℂ) (G : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (Gᴴ * scwAbs η a D * G).toBlocks₁₂ =
      (η : ℂ) • (G.toBlocks₁₁ᴴ * G.toBlocks₁₂) + (a : ℂ) • (G.toBlocks₂₁ᴴ * D * G.toBlocks₂₂) := by
  conv_lhs => rw [← fromBlocks_toBlocks G]
  simp only [fromBlocks_conjTranspose, scwAbs, fromBlocks_multiply, toBlocks_fromBlocks₁₂,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

omit [DecidableEq ν] in
theorem scw_abs_blocks₂₂ (η a : ℝ) (D : Matrix ν ν ℂ) (G : Matrix (π ⊕ ν) (π ⊕ ν) ℂ) :
    (Gᴴ * scwAbs η a D * G).toBlocks₂₂ =
      (η : ℂ) • (G.toBlocks₁₂ᴴ * G.toBlocks₁₂) + (a : ℂ) • (G.toBlocks₂₂ᴴ * D * G.toBlocks₂₂) := by
  conv_lhs => rw [← fromBlocks_toBlocks G]
  simp only [fromBlocks_conjTranspose, scwAbs, fromBlocks_multiply, toBlocks_fromBlocks₂₂,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

theorem scw_star_two_eta_I (η : ℝ) :
    star (2 * (η : ℂ) * Complex.I) = -(2 * (η : ℂ) * Complex.I) := by
  simp [Complex.conj_ofReal]

/-- **`I - S*S = 4ηa (G_{νπ})* D G_{νπ}`** (Ward identity, block `ππ`). -/
theorem scw_one_sub_scat {H : Matrix (π ⊕ ν) (π ⊕ ν) ℂ} (hH : H.IsHermitian)
    {D : Matrix ν ν ℂ} (hD : Dᴴ = D) (η a : ℝ) (hF : IsUnit (scwNet H η a D).det) :
    1 - (scwScat η (scwNet H η a D)⁻¹)ᴴ * scwScat η (scwNet H η a D)⁻¹ =
      (((4 * η * a : ℝ)) : ℂ) • (((scwNet H η a D)⁻¹).toBlocks₂₁ᴴ * D *
        ((scwNet H η a D)⁻¹).toBlocks₂₁) := by
  set G := (scwNet H η a D)⁻¹
  have hW := congrArg Matrix.toBlocks₁₁ (scw_ward_identity hH hD η a hF)
  rw [scw_toBlocks₁₁_sub, scw_toBlocks₁₁_smul, scw_abs_blocks₁₁, scw_conjTranspose_toBlocks₁₁] at hW
  simp only [scwScat, conjTranspose_sub, conjTranspose_one, conjTranspose_smul,
    scw_star_two_eta_I, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  set c : ℂ := 2 * (η : ℂ) * Complex.I
  have hc : c * Complex.I = -(2 * (η : ℂ)) := by
    simp only [c, mul_assoc, Complex.I_mul_I]; ring
  have hcc : c * c = -(4 * (η : ℂ) ^ 2) := by
    simp only [c]; ring_nf; rw [Complex.I_sq]; ring
  have key : c • (G.toBlocks₁₁ - G.toBlocks₁₁ᴴ) = (4 * (η : ℂ)) •
      ((η : ℂ) • (G.toBlocks₁₁ᴴ * G.toBlocks₁₁) + (a : ℂ) • (G.toBlocks₂₁ᴴ * D * G.toBlocks₂₁)) := by
    rw [hW, smul_smul]
    congr 1
    linear_combination (-2 : ℂ) * hc
  calc _ = c • (G.toBlocks₁₁ - G.toBlocks₁₁ᴴ) + (c * c) • (G.toBlocks₁₁ᴴ * G.toBlocks₁₁) := by
        module
    _ = _ := by
        rw [key, hcc]; push_cast; module

/-- `S_0` is unitary. -/
theorem scw_scat_unitary {H : Matrix (π ⊕ ν) (π ⊕ ν) ℂ} (hH : H.IsHermitian)
    {D : Matrix ν ν ℂ} (hD : Dᴴ = D) (η : ℝ) (hF : IsUnit (scwNet H η 0 D).det) :
    (scwScat η (scwNet H η 0 D)⁻¹)ᴴ * scwScat η (scwNet H η 0 D)⁻¹ = 1 := by
  have h := scw_one_sub_scat hH hD η 0 hF
  rw [mul_zero, Complex.ofReal_zero, zero_smul, sub_eq_zero] at h
  exact h.symm

/-- `S_a` is a contraction (`η, a ≥ 0`, `D` a projection). -/
theorem scw_scat_contraction {H : Matrix (π ⊕ ν) (π ⊕ ν) ℂ} (hH : H.IsHermitian)
    {D : Matrix ν ν ℂ} (hD : Dᴴ = D) (hDD : D * D = D) {η a : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a)
    (hF : IsUnit (scwNet H η a D).det) :
    (1 - (scwScat η (scwNet H η a D)⁻¹)ᴴ * scwScat η (scwNet H η a D)⁻¹).PosSemidef := by
  rw [scw_one_sub_scat hH hD η a hF]
  set B := ((scwNet H η a D)⁻¹).toBlocks₂₁
  have hB : Bᴴ * D * B = (D * B)ᴴ * (D * B) := by
    rw [conjTranspose_mul, hD, ← Matrix.mul_assoc, Matrix.mul_assoc Bᴴ D D, hDD]
  rw [hB]
  exact (posSemidef_conjTranspose_mul_self _).smul (by exact_mod_cast (by positivity : (0:ℝ) ≤ 4 * η * a))

/-- The contraction `N = I + iaDG_{νν}D` (for `G = G_0`): `N*N - I ⪰ 0`. -/
theorem scw_N_posSemidef {H : Matrix (π ⊕ ν) (π ⊕ ν) ℂ} (hH : H.IsHermitian)
    {D : Matrix ν ν ℂ} (hD : Dᴴ = D) {η a : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a)
    (hF : IsUnit (scwNet H η 0 D).det) :
    let G := (scwNet H η 0 D)⁻¹
    let N : Matrix ν ν ℂ := 1 + ((a : ℂ) * Complex.I) • (D * G.toBlocks₂₂ * D)
    (Nᴴ * N - 1).PosSemidef := by
  intro G N
  have hW := congrArg Matrix.toBlocks₂₂ (scw_ward_identity hH hD η 0 hF)
  rw [scw_toBlocks₂₂_sub, scw_toBlocks₂₂_smul, scw_abs_blocks₂₂, scw_conjTranspose_toBlocks₂₂,
    Complex.ofReal_zero, zero_smul, add_zero] at hW
  set K : Matrix ν ν ℂ := ((a : ℂ) * Complex.I) • (D * G.toBlocks₂₂ * D)
  have hK : K + Kᴴ = (((2 * a * η : ℝ)) : ℂ) • ((G.toBlocks₁₂ * D)ᴴ * (G.toBlocks₁₂ * D)) := by
    have hstar : star ((a : ℂ) * Complex.I) = -((a : ℂ) * Complex.I) := by
      simp [Complex.conj_ofReal]
    simp only [K, conjTranspose_smul, conjTranspose_mul, hD, hstar, Matrix.mul_assoc]
    rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, ← Matrix.mul_sub, ← Matrix.sub_mul,
      show D * ((G.toBlocks₂₂ - G.toBlocks₂₂ᴴ) * D) = D * (G.toBlocks₂₂ - G.toBlocks₂₂ᴴ) * D by
        rw [Matrix.mul_assoc], hW, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hNN : Nᴴ * N - 1 = (K + Kᴴ) + Kᴴ * K := by
    have hN : N = 1 + K := rfl
    rw [hN]
    simp only [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hNN, hK]
  exact ((posSemidef_conjTranspose_mul_self _).smul
    (by exact_mod_cast (by positivity : (0:ℝ) ≤ 2 * a * η))).add
    (posSemidef_conjTranspose_mul_self _)

/-- `N*N ⪰ I` forces `N` invertible. -/
theorem scw_isUnit_of_posSemidef {N : Matrix ν ν ℂ} (hN : (Nᴴ * N - 1).PosSemidef) :
    IsUnit N.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hNv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h := (posSemidef_iff_dotProduct_mulVec.mp hN).2 v
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hNv, Matrix.mulVec_zero,
    zero_sub, dotProduct_neg] at h
  have hpos : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.mpr hv
  exact absurd (lt_of_lt_of_le hpos (neg_nonneg.mp h)) (lt_irrefl 0)

/-- `Tr |-(r • U X)|^q = r^q Tr |X|^q` for an isometry `U` and `r ≥ 0`. -/
theorem scw_schattenFrac_smul_isometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) (X : Matrix ι ι ℂ) {r : ℝ} (hr : 0 ≤ r)
    (q : ℝ) : schattenFrac q (-((r : ℂ) • (U * X))) = r ^ q * schattenFrac q X := by
  unfold schattenFrac
  have h : (-((r : ℂ) • (U * X)))ᴴ * (-((r : ℂ) • (U * X))) = ((r ^ 2 : ℝ) : ℂ) • (Xᴴ * X) := by
    rw [conjTranspose_neg, neg_mul_neg, conjTranspose_smul, conjTranspose_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
    congr 1
    simp [Complex.conj_ofReal, sq]
  rw [h, fracTrace_smul (posSemidef_conjTranspose_mul_self X).isHermitian (sq_nonneg r),
    ← Real.rpow_natCast, ← Real.rpow_mul hr]
  congr 2
  push_cast; ring

/-- **The Ward factorization** (the signed source update on the network): with
`T = (I + iaDG_{νν}D)⁻¹` (`G = G_0`), `T*T ⪯ I`, `D(G_a)_{νπ} = T D𝒰` and
`S_a - S_0 = -2ηa S_0 (D𝒰)* T (D𝒰)` (`𝒰 = (G_0)_{νπ}`). -/
theorem scw_ward_factor {H : Matrix (π ⊕ ν) (π ⊕ ν) ℂ} (hH : H.IsHermitian)
    {D : Matrix ν ν ℂ} (hD : Dᴴ = D) (hDD : D * D = D) {η a : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a)
    (h0 : IsUnit (scwNet H η 0 D).det) (h1 : IsUnit (scwNet H η a D).det) :
    ∃ T : Matrix ν ν ℂ, (1 - Tᴴ * T).PosSemidef ∧
      D * ((scwNet H η a D)⁻¹).toBlocks₂₁ = T * (D * ((scwNet H η 0 D)⁻¹).toBlocks₂₁) ∧
      scwScat η (scwNet H η a D)⁻¹ - scwScat η (scwNet H η 0 D)⁻¹ =
        -(((2 * η * a : ℝ)) : ℂ) • (scwScat η (scwNet H η 0 D)⁻¹ *
          ((D * ((scwNet H η 0 D)⁻¹).toBlocks₂₁)ᴴ * T *
            (D * ((scwNet H η 0 D)⁻¹).toBlocks₂₁))) := by
  set F0 := scwNet H η 0 D
  set F1 := scwNet H η a D
  set G0 := F0⁻¹
  set G1 := F1⁻¹
  set V := G0.toBlocks₂₁
  set Ψ := D * G1.toBlocks₂₁
  set N : Matrix ν ν ℂ := 1 + ((a : ℂ) * Complex.I) • (D * G0.toBlocks₂₂ * D)
  have hN : (Nᴴ * N - 1).PosSemidef := scw_N_posSemidef hH hD hη ha h0
  have hNu := scw_isUnit_of_posSemidef hN
  set T := N⁻¹
  have hTN : T * N = 1 := nonsing_inv_mul N hNu
  have hNT : N * T = 1 := mul_nonsing_inv N hNu
  -- the resolvent identity `G1 - G0 = -(ia) G0 diag(0, D) G1`
  set E : Matrix (π ⊕ ν) (π ⊕ ν) ℂ := fromBlocks 0 0 0 D
  have hF : F0 - F1 = -((a : ℂ) * Complex.I) • E := by
    ext (i | i) (j | j) <;> simp [F0, F1, scwNet, scwAbs, E]
    ring
  have hres : G1 - G0 = -((a : ℂ) * Complex.I) • (G0 * E * G1) := by
    have e1 : G0 * F0 = 1 := nonsing_inv_mul F0 h0
    have e2 : F1 * G1 = 1 := mul_nonsing_inv F1 h1
    calc G1 - G0 = G0 * F0 * G1 - G0 * (F1 * G1) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = G0 * (F0 - F1) * G1 := by simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = _ := by rw [hF, Matrix.mul_smul, Matrix.smul_mul]
  have hE21 : (G0 * E * G1).toBlocks₂₁ = G0.toBlocks₂₂ * D * G1.toBlocks₂₁ := by
    conv_lhs => rw [← fromBlocks_toBlocks G0, ← fromBlocks_toBlocks G1]
    simp only [E, fromBlocks_multiply, toBlocks_fromBlocks₂₁, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
  have hE11 : (G0 * E * G1).toBlocks₁₁ = G0.toBlocks₁₂ * D * G1.toBlocks₂₁ := by
    conv_lhs => rw [← fromBlocks_toBlocks G0, ← fromBlocks_toBlocks G1]
    simp only [E, fromBlocks_multiply, toBlocks_fromBlocks₁₁, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
  have h21 := congrArg Matrix.toBlocks₂₁ hres
  rw [scw_toBlocks₂₁_sub, scw_toBlocks₂₁_smul, hE21] at h21
  have h11 := congrArg Matrix.toBlocks₁₁ hres
  rw [scw_toBlocks₁₁_sub, scw_toBlocks₁₁_smul, hE11] at h11
  -- `N Ψ = D V`
  have hNΨ : N * Ψ = D * V := by
    have hDΨ : D * (G0.toBlocks₂₂ * D * G1.toBlocks₂₁) = (D * G0.toBlocks₂₂ * D) * Ψ := by
      simp only [Ψ, Matrix.mul_assoc, ← Matrix.mul_assoc D D, hDD]
    have := congrArg (fun M => D * M) h21
    simp only [Matrix.mul_sub, Matrix.mul_smul, hDΨ] at this
    simp only [N, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    change Ψ - D * V = _ at this
    linear_combination (norm := module) this
  have hΨ : Ψ = T * (D * V) := by rw [← hNΨ, ← Matrix.mul_assoc, hTN, Matrix.one_mul]
  refine ⟨T, ?_, hΨ, ?_⟩
  · have : 1 - Tᴴ * T = Tᴴ * (Nᴴ * N - 1) * T := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.mul_assoc Tᴴ Nᴴ,
        ← conjTranspose_mul, Matrix.mul_assoc, hNT, conjTranspose_one, Matrix.one_mul]
    rw [this]
    exact hN.conjTranspose_mul_mul_same T
  · -- Ward block `12` at `a = 0`: `S_0* G0₁₂ = V*`
    have hW := congrArg Matrix.toBlocks₁₂ (scw_ward_identity hH hD η 0 h0)
    rw [scw_toBlocks₁₂_sub, scw_toBlocks₁₂_smul, scw_abs_blocks₁₂, scw_conjTranspose_toBlocks₁₂,
      Complex.ofReal_zero, zero_smul, add_zero] at hW
    have hU := scw_scat_unitary hH hD η h0
    set S0 := scwScat η G0
    have hS0h : S0ᴴ * G0.toBlocks₁₂ = Vᴴ := by
      simp only [S0, scwScat, conjTranspose_sub, conjTranspose_one, conjTranspose_smul,
        scw_star_two_eta_I, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
      have hW' : Vᴴ = G0.toBlocks₁₂ - (-2 * Complex.I) •
          ((η : ℂ) • (G0.toBlocks₁₁ᴴ * G0.toBlocks₁₂)) := by rw [← hW]; abel
      rw [hW', smul_smul]
      congr 2
      ring
    have hS0 : S0 * S0ᴴ = 1 := mul_eq_one_comm.mp hU
    have hG12 : G0.toBlocks₁₂ = S0 * Vᴴ := by
      rw [← hS0h, ← Matrix.mul_assoc, hS0, Matrix.one_mul]
    have hc : -(2 * (η : ℂ) * Complex.I) * (-((a : ℂ) * Complex.I)) = -(((2 * η * a : ℝ)) : ℂ) := by
      push_cast; linear_combination (2 * (η : ℂ) * a) * Complex.I_sq
    have hDV : (D * V)ᴴ = Vᴴ * D := by rw [conjTranspose_mul, hD]
    have hR : (D * V)ᴴ * T * (D * V) = Vᴴ * D * G1.toBlocks₂₁ := by
      rw [Matrix.mul_assoc, ← hΨ, hDV, Matrix.mul_assoc, Matrix.mul_assoc]
      congr 1
      change D * (D * G1.toBlocks₂₁) = D * G1.toBlocks₂₁
      rw [← Matrix.mul_assoc, hDD]
    rw [hR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hG12]
    have hL : scwScat η G1 - S0 =
        -(2 * (η : ℂ) * Complex.I) • (G1.toBlocks₁₁ - G0.toBlocks₁₁) := by
      simp only [S0, scwScat]; module
    rw [hL, h11, smul_smul, hc]

/-- **Ward defect bound** `I - S_a*S_a ⪯ 4ηa Q` (`Q = scwGram D G_0`). -/
theorem scw_ward_defect {H : Matrix (π ⊕ ν) (π ⊕ ν) ℂ} (hH : H.IsHermitian)
    {D : Matrix ν ν ℂ} (hD : Dᴴ = D) (hDD : D * D = D) {η a : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a)
    (h0 : IsUnit (scwNet H η 0 D).det) (h1 : IsUnit (scwNet H η a D).det) :
    ((((4 * η * a : ℝ)) : ℂ) • scwGram D (scwNet H η 0 D)⁻¹ -
      (1 - (scwScat η (scwNet H η a D)⁻¹)ᴴ * scwScat η (scwNet H η a D)⁻¹)).PosSemidef := by
  obtain ⟨T, hT, hΨ, -⟩ := scw_ward_factor hH hD hDD hη ha h0 h1
  rw [scw_one_sub_scat hH hD η a h1]
  set B := ((scwNet H η a D)⁻¹).toBlocks₂₁
  set DV := D * ((scwNet H η 0 D)⁻¹).toBlocks₂₁
  have hB : Bᴴ * D * B = (D * B)ᴴ * (D * B) := by
    rw [conjTranspose_mul, hD, ← Matrix.mul_assoc, Matrix.mul_assoc Bᴴ D D, hDD]
  have hG : scwGram D (scwNet H η 0 D)⁻¹ = DVᴴ * DV := rfl
  rw [hB, hΨ, hG, ← smul_sub]
  have heq : DVᴴ * DV - (T * DV)ᴴ * (T * DV) = DVᴴ * (1 - Tᴴ * T) * DV := by
    simp only [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  rw [heq]
  exact (hT.conjTranspose_mul_mul_same DV).smul
    (by exact_mod_cast (by positivity : (0:ℝ) ≤ 4 * η * a))

/-- **Ward difference bound** `Tr|S_a - S_0|^q ≤ (2ηa)^q Tr Q^q` for every `q > 0`. -/
theorem scw_ward_diff {H : Matrix (π ⊕ ν) (π ⊕ ν) ℂ} (hH : H.IsHermitian)
    {D : Matrix ν ν ℂ} (hD : Dᴴ = D) (hDD : D * D = D) {η a : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a)
    (h0 : IsUnit (scwNet H η 0 D).det) (h1 : IsUnit (scwNet H η a D).det) {q : ℝ}
    (hq : 0 < q) :
    schattenFrac q (scwScat η (scwNet H η a D)⁻¹ - scwScat η (scwNet H η 0 D)⁻¹) ≤
      (2 * η * a) ^ q * fracTrace q (scwGram D (scwNet H η 0 D)⁻¹) := by
  obtain ⟨T, hT, -, hdiff⟩ := scw_ward_factor hH hD hDD hη ha h0 h1
  rw [hdiff, neg_smul, scw_schattenFrac_smul_isometry (scw_scat_unitary hH hD η h0) _
    (by positivity) q]
  exact mul_le_mul_of_nonneg_left (scw_schattenFrac_sandwich_le _ hT hq)
    (Real.rpow_nonneg (by positivity) _)

end Core

end BlockBand.Endpoints
