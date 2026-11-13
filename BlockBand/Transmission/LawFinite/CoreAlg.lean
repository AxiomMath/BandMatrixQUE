module

public import BlockBand.Transmission.LawFinite.CoreSpec

/-!
# The deterministic one-layer inequality of the finite core

The paper writes `L⁻¹ = B*R - zB⁻¹T₀` and uses the singular-value min–max principle. Here neither
`B⁻¹` nor min–max is used:
* `cutLow B c = 1_{λ<c}(BB*)`, `cutInv B c = B*·(λ⁻¹1_{λ≥c})(BB*)`: `B·cutInv = 1 - cutLow`
  (`mul_cutInv`), `‖cutInv B h²‖ ≤ h⁻¹` (`norm_cutInv_le`), and the rank of `cutLow` is
  `#{λ_i(BB*) < c} = smallSingularCount c B` (`card_eig_mul_conj_lt`, `charpoly_mul_comm`);
* `layer_blocks`: `𝒢₁₁ = S⁻¹`, `𝒢₁₂ = -w⁻¹S⁻¹B`, `S = A - E - X - w⁻¹BB*` (from
  `layer_schur`), on `A` Hermitian, `B` invertible;
* `core_identity`: `1 = (K𝒢₁₂)(B* - wGP)R + (K𝒢₁₁)ΠPR`, `P = A - E - X`, `KR = 1`;
* `core_trace_le`: for `Q ⪰ 0` and `1 = LF + N`,
  `Re Tr Q ≤ F₀² Re Tr(L*QL) + Re Tr Q/4 + Re Tr(QN)` (`‖F‖ ≤ F₀`), by positivity of
  `(L - cF*)*Q(L - cF*)`; no independence between `Q` and the good subspace is needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-!
## The spectral cut of `BB*`
-/

/-- `#{i : λ_i(BB*) < c} = smallSingularCount c B` (`BB*` and `B*B` have the same
characteristic polynomial). -/
theorem card_eig_mul_conj_lt (B : Matrix (Fin W) (Fin W) ℂ) (c : ℝ) :
    ((Finset.univ.filter fun i =>
        (isHermitian_mul_conjTranspose_self B).eigenvalues i < c).card : ℝ) =
      smallSingularCount c B := by
  have he : (isHermitian_mul_conjTranspose_self B).eigenvalues =
      (isHermitian_conjTranspose_mul_self B).eigenvalues :=
    (IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2 (charpoly_mul_comm _ _)
  rw [he, smallSingularCount, Finset.card_filter, Finset.card_filter,
    sum_increasingEigenvalue (isHermitian_conjTranspose_mul_self B)
      (fun x => if x < c then 1 else 0)]

/-- The projection `1_{λ < c}(BB*)` on the small singular directions. -/
def cutLow (B : Matrix (Fin W) (Fin W) ℂ) (c : ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  (isHermitian_mul_conjTranspose_self B).cfc fun x => if x < c then 1 else 0

/-- The truncated right inverse `G = B*·(λ⁻¹1_{λ ≥ c})(BB*)`. -/
def cutInv (B : Matrix (Fin W) (Fin W) ℂ) (c : ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  Bᴴ * (isHermitian_mul_conjTranspose_self B).cfc fun x => if x < c then 0 else x⁻¹

theorem mul_cutInv (B : Matrix (Fin W) (Fin W) ℂ) {c : ℝ} (hc : 0 < c) :
    B * cutInv B c = 1 - cutLow B c := by
  set hH := isHermitian_mul_conjTranspose_self B
  have e : B * Bᴴ * hH.cfc (fun x => if x < c then 0 else x⁻¹) =
      hH.cfc (fun x => x * if x < c then 0 else x⁻¹) := by
    rw [← cfc_mul_cfc, cfc_id']
  have h1 : (1 : Matrix (Fin W) (Fin W) ℂ) = hH.cfc (fun _ => 1) := by
    rw [cfc_const]; simp
  rw [cutInv, ← Matrix.mul_assoc, e, cutLow, h1, ← cfc_sub]
  congr 1; funext x
  split_ifs with h
  · simp
  · rw [mul_inv_cancel₀ (by linarith [not_lt.mp h])]; simp

theorem norm_cutInv_le (B : Matrix (Fin W) (Fin W) ℂ) {h : ℝ} (hh : 0 < h) :
    ‖cutInv B (h ^ 2)‖ ≤ h⁻¹ := by
  set hH := isHermitian_mul_conjTranspose_self B
  set f : ℝ → ℝ := fun x => if x < h ^ 2 then 0 else x⁻¹
  have hG : (cutInv B (h ^ 2))ᴴ * cutInv B (h ^ 2) = hH.cfc fun x => f x * x * f x := by
    have e : B * Bᴴ * hH.cfc f = hH.cfc (fun x => x * f x) := by
      rw [← cfc_mul_cfc, cfc_id']
    rw [cutInv, conjTranspose_mul, conjTranspose_conjTranspose, cfc_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc B, e, cfc_mul_cfc]
    congr 1; funext x; ring
  have hb : ‖hH.cfc fun x => f x * x * f x‖ ≤ (h ^ 2)⁻¹ := by
    refine norm_cfc_le hH _ (by positivity) fun i => ?_
    set x := hH.eigenvalues i
    simp only [f]
    split_ifs with hx
    · simp; positivity
    · have hx' : h ^ 2 ≤ x := not_lt.mp hx
      have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx'
      rw [show x⁻¹ * x * x⁻¹ = x⁻¹ by field_simp, abs_of_pos (inv_pos.mpr hx0)]
      exact inv_anti₀ (by positivity) hx'
  have h2 : ‖cutInv B (h ^ 2)‖ ^ 2 ≤ h⁻¹ ^ 2 := by
    rw [sq, ← l2_opNorm_conjTranspose_mul_self, hG, inv_pow]; exact hb
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-!
## The fresh layer in `W × W` blocks
-/

/-- The port Schur complement `S = A - E - X - w⁻¹BB*` as a `W × W` matrix. -/
def schurW (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  ω.1 0 - (E : ℂ) • 1 - X - w⁻¹ • (ω.2 0 0 * (ω.2 0 0)ᴴ)

theorem liftX_inv (M : Matrix (Fin W) (Fin W) ℂ) : (liftX M)⁻¹ = liftX M⁻¹ := by
  have e := Equiv.uniqueProd (Fin W) (Fin 1)
  show (M.submatrix (Equiv.uniqueProd (Fin W) (Fin 1)) (Equiv.uniqueProd (Fin W) (Fin 1)))⁻¹ =
    M⁻¹.submatrix (Equiv.uniqueProd (Fin W) (Fin 1)) (Equiv.uniqueProd (Fin W) (Fin 1))
  rw [inv_submatrix_equiv]

theorem liftX_submatrix_embed0 (M : Matrix (Fin W) (Fin W) ℂ) :
    (liftX M).submatrix embed0 embed0 = M := by
  ext x y; simp [liftX, embed0]

theorem schurS_eq_liftX (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : schurS E w X ω = liftX (schurW E w X ω) := by
  rw [schurS, schurW, blockDiag_one_eq, bondL, bondMatrix_one_eq, ← liftX_conjTranspose,
    ← liftX_mul, liftX_sub, liftX_sub, liftX_sub, liftX_smul, liftX_smul, liftX_one]

/-- On `A` Hermitian, `B` invertible: `𝒢₁₁ = S⁻¹`, `𝒢₁₂ = -w⁻¹S⁻¹B`, `S` invertible. -/
theorem layer_blocks (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    IsUnit (schurW E w X ω) ∧ g11 E w X ω = (schurW E w X ω)⁻¹ ∧
      g12 E w X ω = -w⁻¹ • ((schurW E w X ω)⁻¹ * ω.2 0 0) := by
  have h := (layer_schur E hw hY hA hB).2.1
  have hS := isUnit_schurS E hw hY hA hB
  rw [schurS_eq_liftX] at hS
  refine ⟨?_, ?_, ?_⟩
  · rw [isUnit_iff_isUnit_det] at hS ⊢
    have : (liftX (schurW E w X ω)).det = (schurW E w X ω).det :=
      det_submatrix_equiv_self (Equiv.uniqueProd (Fin W) (Fin 1)) _
    rwa [this] at hS
  · rw [g11_eq h, schurS_eq_liftX, liftX_inv, liftX_submatrix_embed0]
  · rw [g12_eq h, schurS_eq_liftX, liftX_inv, bondL, bondMatrix_one_eq, ← liftX_mul,
      ← liftX_smul, liftX_submatrix_embed0]

/-!
## The deterministic identity `1 = LF₁ + K𝒢₁₁PmPR`
-/

/-- Abstract form: `S = P - w⁻¹BB*`, `g₁₁ = S⁻¹`, `g₁₂ = -w⁻¹S⁻¹B`, `BG = 1 - Pm`, `KR = 1`. -/
theorem core_identity {S P B G Pm K R g11 g12 : Matrix (Fin W) (Fin W) ℂ} {w : ℂ} (hw : w ≠ 0)
    (hS : IsUnit S) (hSd : S = P - w⁻¹ • (B * Bᴴ)) (h11 : g11 = S⁻¹)
    (h12 : g12 = -w⁻¹ • (S⁻¹ * B)) (hG : B * G = 1 - Pm) (hKR : K * R = 1) :
    1 = (K * g12) * ((Bᴴ - w • (G * P)) * R) + (K * g11) * Pm * P * R := by
  have hSS : S⁻¹ * S = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hS)
  have h1 : g11 * P + g12 * Bᴴ = 1 := by
    rw [h11, h12, ← hSS, hSd, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
      neg_smul]
    abel
  have h2 : g12 * (w • G) = -g11 + g11 * Pm := by
    rw [h12, h11, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_neg, mul_inv_cancel₀ hw,
      neg_smul, one_smul, Matrix.mul_assoc, hG, Matrix.mul_sub, Matrix.mul_one]
    abel
  have h3 : g12 * (Bᴴ - w • (G * P)) + g11 * Pm * P = 1 := by
    rw [Matrix.mul_sub, ← smul_mul_assoc, ← Matrix.mul_assoc, h2, Matrix.add_mul, Matrix.neg_mul,
      ← h1]
    abel
  calc (1 : Matrix (Fin W) (Fin W) ℂ) = K * (g12 * (Bᴴ - w • (G * P)) + g11 * Pm * P) * R := by
        rw [h3, Matrix.mul_one, hKR]
    _ = _ := by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-!
## The trace inequality
-/

/-- `2c Re Tr(QLF) ≤ Re Tr(L*QL) + c²‖F‖² Re Tr Q` for `Q ⪰ 0` and real `c`. -/
theorem two_mul_re_trace_le {Q L F : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (c : ℝ) :
    2 * c * (Q * (L * F)).trace.re ≤ (Lᴴ * Q * L).trace.re + c ^ 2 * ‖F‖ ^ 2 * Q.trace.re := by
  set M := L - (c : ℂ) • Fᴴ
  have h0 : 0 ≤ (Mᴴ * Q * M).trace.re :=
    (Complex.nonneg_iff.mp (hQ.conjTranspose_mul_mul_same M).trace_nonneg).1
  have hexp : Mᴴ * Q * M = Lᴴ * Q * L - (c : ℂ) • (Lᴴ * Q * Fᴴ) - (c : ℂ) • (F * Q * L) +
      ((c : ℂ) * c) • (F * Q * Fᴴ) := by
    simp only [M, conjTranspose_sub, conjTranspose_smul, conjTranspose_conjTranspose,
      Complex.star_def, Complex.conj_ofReal, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, smul_sub, smul_smul]
    abel
  have hc1 : (Lᴴ * Q * Fᴴ).trace.re = (Q * (L * F)).trace.re := by
    have : Lᴴ * Q * Fᴴ = (F * Q * L)ᴴ := by
      rw [conjTranspose_mul, conjTranspose_mul, hQ.1.eq, Matrix.mul_assoc]
    rw [this, trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc,
      trace_mul_comm F, Matrix.mul_assoc]
  have hc2 : (F * Q * L).trace.re = (Q * (L * F)).trace.re := by
    rw [Matrix.mul_assoc, trace_mul_comm F, Matrix.mul_assoc]
  have hc3 : (F * Q * Fᴴ).trace.re ≤ ‖F‖ ^ 2 * Q.trace.re := by
    have : (F * Q * Fᴴ).trace = (Fᴴ * F * Q).trace := by
      rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, trace_mul_comm]
    rw [this]
    refine (Complex.re_le_norm _).trans ?_
    refine (PassiveCovariance.norm_trace_mul_posSemidef_le hQ _).trans ?_
    rw [l2_opNorm_conjTranspose_mul_self, sq]
  rw [hexp, trace_add, trace_sub, trace_sub, trace_smul, trace_smul, trace_smul] at h0
  simp only [Complex.add_re, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul,
    ← Complex.ofReal_mul] at h0
  rw [hc1, hc2] at h0
  have : c * c * (F * Q * Fᴴ).trace.re ≤ c ^ 2 * (‖F‖ ^ 2 * Q.trace.re) := by
    rw [← sq]; exact mul_le_mul_of_nonneg_left hc3 (sq_nonneg c)
  nlinarith

/-- **The deterministic trace inequality**: if `1 = LF + N`, `‖F‖ ≤ F₀`,
`F₀ > 0` and `Q ⪰ 0`, then `Re Tr Q ≤ F₀² Re Tr(L*QL) + Re Tr Q/4 + Re Tr(QN)`. -/
theorem core_trace_le {Q L F N : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) {F₀ : ℝ}
    (hF₀ : 0 < F₀) (hF : ‖F‖ ≤ F₀) (h1 : 1 = L * F + N) :
    Q.trace.re ≤ F₀ ^ 2 * (Lᴴ * Q * L).trace.re + Q.trace.re / 4 + (Q * N).trace.re := by
  have hq : 0 ≤ Q.trace.re := (Complex.nonneg_iff.mp hQ.trace_nonneg).1
  set c := (2 * F₀ ^ 2)⁻¹
  have hc : 0 < c := by positivity
  have h := two_mul_re_trace_le (L := L) (F := F) hQ c
  have hsplit : Q.trace.re = (Q * (L * F)).trace.re + (Q * N).trace.re := by
    conv_lhs => rw [← Matrix.mul_one Q, h1]
    rw [Matrix.mul_add, trace_add, Complex.add_re]
  have hF2 : ‖F‖ ^ 2 ≤ F₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hF 2
  have h3 : c ^ 2 * ‖F‖ ^ 2 * Q.trace.re ≤ c ^ 2 * F₀ ^ 2 * Q.trace.re := by gcongr
  have hcF : 2 * c * F₀ ^ 2 = 1 := by simp only [c]; field_simp
  have hqp : 0 ≤ (Lᴴ * Q * L).trace.re :=
    (Complex.nonneg_iff.mp (hQ.conjTranspose_mul_mul_same L).trace_nonneg).1
  -- `(Q(LF)).re ≤ F₀² q₊ + q/4`
  have h4 : (Q * (L * F)).trace.re ≤ F₀ ^ 2 * (Lᴴ * Q * L).trace.re + Q.trace.re / 4 := by
    have h5 : 2 * c * (Q * (L * F)).trace.re ≤
        2 * c * (F₀ ^ 2 * (Lᴴ * Q * L).trace.re + Q.trace.re / 4) := by
      have : 2 * c * (F₀ ^ 2 * (Lᴴ * Q * L).trace.re + Q.trace.re / 4) =
          (Lᴴ * Q * L).trace.re + c ^ 2 * F₀ ^ 2 * Q.trace.re := by
        have e : c ^ 2 * F₀ ^ 2 = c / 2 := by
          have : c ^ 2 * F₀ ^ 2 = c * (2 * c * F₀ ^ 2) / 2 := by ring
          rw [this, hcF, mul_one]
        rw [e]; nlinarith [hcF]
      linarith
    exact le_of_mul_le_mul_left h5 (by positivity)
  linarith

end BlockBand.Transmission.LawFinite
