module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormJoint
public import BlockBand.SourceProcess.PhysApprox.B3CovRepKBound
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanChain

/-!
# The leading terms of the mixed `(𝒦, Gram)` brackets at a chain state

Deterministic. For a Hermitian two-port `𝕏` with scattering `𝕊 = twoPortScattering 𝕏`, the
Ward factor and the far-eliminated `passiveF` are
* `wardF_eq`: `F = -c₀ ι𝕊` (`c₀ = (2iη)⁻¹`; no invertibility needed);
* `passiveF_nearSchur`: `F₁ = passiveF (nearSchur 𝕏) = -c₀ ι𝕊ι*`.
For a frame `V` with Gram state `(M, B)` and the chain current clause `currentOf 𝕏 = V𝖣V*`:
* `gram_current`, `gram_current_P`: `V*𝕊*P𝕊V = B + M𝖣M = C₀` and `V*P𝕊*P𝕊V = B + B𝖣M = C₁*`;
* **`lead_dM`**: `(Fc_k)*(ι𝕊c_j) = conj(-c₀)(C₀)_{kj}`;
* **`lead_dB`**: `(F₁ιc_k)*(ι𝕊c_j) = conj(-c₀)(C₁*)_{kj}`;
* `lead_u`: `(ιc_{d'})*(ιc_d) = B_{d'd}`; norm bounds for `ι𝕊`, `P`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FullSource (wardF)
open BlockBand.SourceProcess.ContractingWords (currentOf)
open BlockBand.Transmission.Bridge
open scoped ComplexConjugate

variable {W : ℕ}

theorem srcSignature_conjTranspose (K : ℕ) (π : Type*) [DecidableEq π] :
    (srcSignature K π)ᴴ = srcSignature K π := by
  rw [srcSignature, diagonal_conjTranspose]
  congr 1
  funext c
  rcases c with ⟨_, σ⟩ | _
  · by_cases hσ : σ = 0 <;> simp [hσ]
  · simp

theorem cZero_eq_inv (b E : ℝ) : cZero b E = ((((2 * etaZ b E : ℝ) : ℂ) * Complex.I))⁻¹ := by
  rw [cZero]; congr 1; push_cast; ring

theorem vecNorm_nearSel_le (w : Fin 2 × Fin W → ℂ) : vecNorm (nearSel W *ᵥ w) ≤ vecNorm w :=
  Real.sqrt_le_sqrt (sum_sq_nearSel_le w)

theorem vecNorm_unitary_eq {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ} (hU : Uᴴ * U = 1)
    (w : n → ℂ) : vecNorm (U *ᵥ w) = vecNorm w := by
  unfold vecNorm
  congr 1
  rw [← re_dot_gram, hU, one_mulVec, re_star_dot_self]

theorem vecNorm_nearSel_conj (x : Fin W → ℂ) : vecNorm ((nearSel W)ᴴ *ᵥ x) = vecNorm x := by
  unfold vecNorm
  congr 1
  rw [← re_dot_gram, conjTranspose_conjTranspose, nearSel_mul_conjTranspose, one_mulVec,
    re_star_dot_self]

theorem vecNorm_nearPortProj_le (w : Fin 2 × Fin W → ℂ) :
    vecNorm (nearPortProj W *ᵥ w) ≤ vecNorm w := by
  rw [show nearPortProj W = (nearSel W)ᴴ * nearSel W from
    (FullSourceCovariance.nearSel_conj_mul_nearSel).symm, ← mulVec_mulVec, vecNorm_nearSel_conj]
  exact vecNorm_nearSel_le w

/-!
## The Ward factor and `passiveF` at a Hermitian two-port
-/

section TwoPort

variable {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}

theorem twoPortResolvent_eq (hη : 0 < etaZ b E) :
    twoPortResolvent b E XX = cZero b E • (1 - twoPortScattering b E XX) := by
  set c : ℂ := ((2 * etaZ b E : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    have : ((2 * etaZ b E : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * etaZ b E ≠ 0)
    exact mul_ne_zero this Complex.I_ne_zero
  rw [cZero_eq_inv]
  change twoPortResolvent b E XX = c⁻¹ • (1 - (1 - c • twoPortResolvent b E XX))
  rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **`F = -c₀ ι𝕊`.** -/
theorem wardF_eq (hη : 0 < etaZ b E) :
    wardF b E XX = (-cZero b E) • (nearSel W * twoPortScattering b E XX) := by
  rw [wardF, twoPortResolvent_eq hη, smul_sub, smul_one_eq_diagonal, sub_sub_cancel_left,
    Matrix.mul_neg, Matrix.mul_smul, neg_smul]

/-- **`F₁ = passiveF (nearSchur 𝕏) = -c₀ ι𝕊ι*`** for Hermitian `𝕏`. -/
theorem passiveF_nearSchur (hη : 0 < etaZ b E) (hXX : XX.IsHermitian) :
    passiveF b E (nearSchur (boundaryZ b E) XX) =
      (-cZero b E) • (nearSel W * twoPortScattering b E XX * (nearSel W)ᴴ) := by
  have hD11 : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1) :=
    BlockBand.Transmission.portPencil_isUnit _
      (BlockBand.SourceProcess.FullSource.portBlock_isHermitian hXX 1) hη
  rw [passiveF, ← portBlock_twoPortResolvent_zero_zero b E XX hD11,
    ← RawTag.nearSel_mul_mul_conjTranspose, twoPortResolvent_eq hη, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, nearSel_mul_conjTranspose,
    smul_sub, sub_sub_cancel_left, neg_smul]

theorem vecNorm_nearSel_scattering_le (hη : 0 < etaZ b E) (hXX : XX.IsHermitian)
    (w : Fin 2 × Fin W → ℂ) :
    vecNorm (nearSel W *ᵥ (twoPortScattering b E XX *ᵥ w)) ≤ vecNorm w := by
  refine (vecNorm_nearSel_le _).trans (le_of_eq ?_)
  exact vecNorm_unitary_eq (twoPortScattering_unitary b E XX hXX hη).1 w

end TwoPort

/-!
## The Gram identities of the current clause and the leading terms
-/

section Lead

variable {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {c : Type*} [Fintype c]
  {V : Matrix (Fin 2 × Fin W) c ℂ} {D : Matrix c c ℂ}

theorem scattering_current (hcur : currentOf b E XX = V * D * Vᴴ) :
    (twoPortScattering b E XX)ᴴ * nearPortProj W * twoPortScattering b E XX =
      nearPortProj W + V * D * Vᴴ := by
  rw [← hcur]
  change _ = nearPortProj W + ((twoPortScattering b E XX)ᴴ * nearPortProj W *
    twoPortScattering b E XX - nearPortProj W)
  abel

theorem gram_current (hcur : currentOf b E XX = V * D * Vᴴ) :
    Vᴴ * ((twoPortScattering b E XX)ᴴ * nearPortProj W * twoPortScattering b E XX) * V =
      gramC0 (Vᴴ * V) (Vᴴ * nearPortProj W * V) D := by
  rw [scattering_current hcur, gramC0]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem gram_current_P (hcur : currentOf b E XX = V * D * Vᴴ) (hD : Dᴴ = D) :
    Vᴴ * (nearPortProj W * ((twoPortScattering b E XX)ᴴ * nearPortProj W *
        twoPortScattering b E XX)) * V =
      (gramC1 (Vᴴ * V) (Vᴴ * nearPortProj W * V) D)ᴴ := by
  rw [scattering_current hcur, gramC1]
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, hD,
    nearPortProj_conjTranspose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (nearPortProj W) (nearPortProj W), nearPortProj_mul_self]

theorem bilinear_smul_left (a : ℂ) (x y : Fin W → ℂ) :
    bilinear (a • x) 1 y = star a * bilinear x 1 y := by
  simp only [bilinear_one, star_smul, smul_dotProduct, smul_eq_mul]

omit [Fintype c] in
/-- `(ιc')*(ιc) = (V*PV)_{d'd}`. -/
theorem lead_u (d' d : c) :
    bilinear (nearSel W *ᵥ fun a => V a d') 1 (nearSel W *ᵥ fun a => V a d) =
      (Vᴴ * nearPortProj W * V) d' d := by
  rw [bilinear_one, dot_nearSel, entry_eq_dot]

/-- **The leading factor of the `(𝒦, M)` bracket**: `(Fc_k)*(ι𝕊c_j) = conj(-c₀)(C₀)_{kj}`. -/
theorem lead_dM (hη : 0 < etaZ b E) (hcur : currentOf b E XX = V * D * Vᴴ) (k j : c) :
    bilinear (wardF b E XX *ᵥ fun a => V a k) 1
        (nearSel W *ᵥ (twoPortScattering b E XX *ᵥ fun a => V a j)) =
      star (-cZero b E) * gramC0 (Vᴴ * V) (Vᴴ * nearPortProj W * V) D k j := by
  rw [wardF_eq hη, smul_mulVec, ← mulVec_mulVec, bilinear_smul_left, bilinear_one,
    dot_nearSel, ← ClosedForm.star_dot_conjTranspose_mulVec', mulVec_mulVec, mulVec_mulVec,
    ← entry_eq_dot, gram_current hcur]

/-- **The leading factor of the `(𝒦, B)` bracket**: `(F₁ιc_k)*(ι𝕊c_j) = conj(-c₀)(C₁*)_{kj}`. -/
theorem lead_dB (hη : 0 < etaZ b E) (hXX : XX.IsHermitian)
    (hcur : currentOf b E XX = V * D * Vᴴ) (hD : Dᴴ = D) (k j : c) :
    bilinear (passiveF b E (nearSchur (boundaryZ b E) XX) *ᵥ (nearSel W *ᵥ fun a => V a k)) 1
        (nearSel W *ᵥ (twoPortScattering b E XX *ᵥ fun a => V a j)) =
      star (-cZero b E) * (gramC1 (Vᴴ * V) (Vᴴ * nearPortProj W * V) D)ᴴ k j := by
  rw [passiveF_nearSchur hη hXX, smul_mulVec, bilinear_smul_left, ← mulVec_mulVec,
    ← mulVec_mulVec, mulVec_mulVec (fun a => V a k) (nearSel W)ᴴ (nearSel W),
    show (nearSel W)ᴴ * nearSel W = nearPortProj W from
      FullSourceCovariance.nearSel_conj_mul_nearSel, bilinear_one, dot_nearSel,
    ← ClosedForm.star_dot_conjTranspose_mulVec', ← ClosedForm.star_dot_conjTranspose_mulVec',
    nearPortProj_conjTranspose, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, ← entry_eq_dot,
    ← gram_current_P hcur hD]
  simp only [Matrix.mul_assoc]

end Lead

end BlockBand.SourceProcess.PhysApprox.B3

