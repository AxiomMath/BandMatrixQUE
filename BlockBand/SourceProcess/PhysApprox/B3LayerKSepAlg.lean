module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanCayley

/-!
# Near-end growth commutes with the padded closing

For a two-port `Y` (near port `0`, far port `1`) put `ζ = z_∂`, `c = 2iη`, `𝕊(Y) = 1 - c(ζ - Y)⁻¹`
(`twoPortScattering`) and, for a scatterer `V` with `1 - V` invertible, the Cayley inverse
`Cay V = ζ - c(1 - V)⁻¹`. With far closing data `A = farEmbed A₀`, `Π = farEmbed Π₀`
(`A₀² = A₀`, `A₀Π₀ = Π₀`) and the padded scatterer `padScat` (`𝕊_pad`):

**`cay_padScat_freshTwoPortSchur`**: `Cay(𝕊_pad(𝕊(Φ_F Y))) = Φ_F(Cay(𝕊_pad(𝕊(Y))))`, where
`Φ_F = freshTwoPortSchur E · F`, given the invertibility of `ζ - Y`, `ζ - Φ_FY`, the two fresh
pivots `A_F - E - Y₀₀`, `A_F - E - (Cay 𝕊_pad)₀₀`, the two closing denominators `1 - zN` and the
two `1 - 𝕊_pad`. No unitarity and no Hermiticity is used. It is proved for every far padding
`Q = farEmbed Q₀` (`padScatQ`, **`cay_padScatQ_freshTwoPortSchur`**), so it covers the phase-`1`
padding `Πᴴ` and the phase-`z` padding `zΠᴴ` (`b3ChainXXz`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedPath BlockBand.Transmission.Bridge

variable {W : ℕ}

/-!
## Port parts of vectors
-/

/-- The near part of a port vector. -/
def nP (v : Fin 2 × Fin W → ℂ) : Fin W → ℂ := fun x => v (0, x)

/-- The far part of a port vector. -/
def fP (v : Fin 2 × Fin W → ℂ) : Fin W → ℂ := fun x => v (1, x)

/-- The port vector with near part `u` and far part `w`. -/
def pVec (u w : Fin W → ℂ) : Fin 2 × Fin W → ℂ := fun p => if p.1 = 0 then u p.2 else w p.2

@[simp] theorem nP_pVec (u w : Fin W → ℂ) : nP (pVec u w) = u := by
  funext x; simp [nP, pVec]

@[simp] theorem fP_pVec (u w : Fin W → ℂ) : fP (pVec u w) = w := by
  funext x; simp [fP, pVec]

@[simp] theorem nP_add (v w : Fin 2 × Fin W → ℂ) : nP (v + w) = nP v + nP w := rfl
@[simp] theorem fP_add (v w : Fin 2 × Fin W → ℂ) : fP (v + w) = fP v + fP w := rfl
@[simp] theorem nP_sub (v w : Fin 2 × Fin W → ℂ) : nP (v - w) = nP v - nP w := rfl
@[simp] theorem fP_sub (v w : Fin 2 × Fin W → ℂ) : fP (v - w) = fP v - fP w := rfl
@[simp] theorem nP_smul (a : ℂ) (v : Fin 2 × Fin W → ℂ) : nP (a • v) = a • nP v := rfl
@[simp] theorem fP_smul (a : ℂ) (v : Fin 2 × Fin W → ℂ) : fP (a • v) = a • fP v := rfl
@[simp] theorem nP_neg (v : Fin 2 × Fin W → ℂ) : nP (-v) = -nP v := rfl
@[simp] theorem fP_neg (v : Fin 2 × Fin W → ℂ) : fP (-v) = -fP v := rfl

theorem vec_ext {v v' : Fin 2 × Fin W → ℂ} (h0 : nP v = nP v') (h1 : fP v = fP v') : v = v' := by
  funext ⟨i, x⟩
  fin_cases i
  · exact congrFun h0 x
  · exact congrFun h1 x

theorem nP_mulVec (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (v : Fin 2 × Fin W → ℂ) :
    nP (M *ᵥ v) = portBlock M 0 0 *ᵥ nP v + portBlock M 0 1 *ᵥ fP v := by
  funext x
  simp [nP, fP, mulVec, dotProduct, portBlock, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem fP_mulVec (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (v : Fin 2 × Fin W → ℂ) :
    fP (M *ᵥ v) = portBlock M 1 0 *ᵥ nP v + portBlock M 1 1 *ᵥ fP v := by
  funext x
  simp [nP, fP, mulVec, dotProduct, portBlock, Fintype.sum_prod_type, Fin.sum_univ_two]

@[simp] theorem nP_one_mulVec (v : Fin 2 × Fin W → ℂ) :
    nP ((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) *ᵥ v) = nP v := by
  rw [one_mulVec]

theorem nP_farEmbed (X : Matrix (Fin W) (Fin W) ℂ) (v : Fin 2 × Fin W → ℂ) :
    nP (farEmbed X *ᵥ v) = 0 := by
  funext x
  simp [nP, farEmbed, mulVec, dotProduct]

theorem fP_farEmbed (X : Matrix (Fin W) (Fin W) ℂ) (v : Fin 2 × Fin W → ℂ) :
    fP (farEmbed X *ᵥ v) = X *ᵥ fP v := by
  funext x
  simp [fP, farEmbed, mulVec, dotProduct, Fintype.sum_prod_type]

/-- A far-embedded matrix only reads the far part. -/
theorem farEmbed_mulVec_congr (X : Matrix (Fin W) (Fin W) ℂ) {v v' : Fin 2 × Fin W → ℂ}
    (h : fP v = fP v') : farEmbed X *ᵥ v = farEmbed X *ᵥ v' :=
  vec_ext (by rw [nP_farEmbed, nP_farEmbed]) (by rw [fP_farEmbed, fP_farEmbed, h])

theorem nP_one_sub_farEmbed (X : Matrix (Fin W) (Fin W) ℂ) (v : Fin 2 × Fin W → ℂ) :
    nP ((1 - farEmbed X) *ᵥ v) = nP v := by
  rw [sub_mulVec, one_mulVec, nP_sub, nP_farEmbed, sub_zero]

theorem fP_one_sub_farEmbed (X : Matrix (Fin W) (Fin W) ℂ) (v : Fin 2 × Fin W → ℂ) :
    fP ((1 - farEmbed X) *ᵥ v) = fP v - X *ᵥ fP v := by
  rw [sub_mulVec, one_mulVec, fP_sub, fP_farEmbed]

/-!
## The closing map on vectors
-/

section Closing

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S A Pi : Matrix ι ι ℂ} {z : ℂ}

/-- `Aa = zΠSa` gives `C(z)(1 - A)a = a`. -/
theorem closingMap_mulVec_of_feedback (hA2 : A * A = A)
    (hU : IsUnit (1 - z • closingN S A Pi).det) {a : ι → ℂ}
    (ha : A *ᵥ a = z • (Pi *ᵥ (S *ᵥ a))) :
    closingMap S A Pi z *ᵥ ((1 - A) *ᵥ a) = a := by
  set K := (1 - z • closingN S A Pi)⁻¹
  have hK : K * (1 - z • closingN S A Pi) = 1 := nonsing_inv_mul _ hU
  have hAA : A *ᵥ (A *ᵥ a) = A *ᵥ a := by rw [mulVec_mulVec, hA2]
  have hA1 : (1 - A) *ᵥ ((1 - A) *ᵥ a) = (1 - A) *ᵥ a := by
    simp only [sub_mulVec, one_mulVec, mulVec_sub, hAA, sub_self, sub_zero]
  have e1 : (1 - z • closingN S A Pi) *ᵥ (A *ᵥ a) =
      z • (Pi *ᵥ (S *ᵥ ((1 - A) *ᵥ a))) := by
    rw [sub_mulVec, one_mulVec, closingN, smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hAA,
      sub_mulVec, one_mulVec, mulVec_sub, mulVec_sub, smul_sub, ha]
  have e2 : K *ᵥ (z • (Pi *ᵥ (S *ᵥ ((1 - A) *ᵥ a)))) = A *ᵥ a := by
    rw [← e1, mulVec_mulVec, hK, one_mulVec]
  rw [closingMap, add_mulVec, hA1, ← mulVec_mulVec, closingT, smul_mulVec, ← mulVec_mulVec,
    ← mulVec_mulVec, hA1, e2]
  simp only [sub_mulVec, one_mulVec, sub_add_cancel]

/-- `(1 - A)C(z) = 1 - A`. -/
theorem one_sub_mul_closingMap (hA2 : A * A = A) (hAPi : A * Pi = Pi)
    (hU : IsUnit (1 - z • closingN S A Pi).det) :
    (1 - A) * closingMap S A Pi z = 1 - A := by
  have hAP : (1 - A) * Pi = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hAPi, sub_self]
  have h1 : (1 - A) * (1 - z • closingN S A Pi) = 1 - A := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, closingN, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hAP, Matrix.zero_mul, Matrix.zero_mul, smul_zero, sub_zero]
  have hK : (1 - z • closingN S A Pi) * (1 - z • closingN S A Pi)⁻¹ = 1 := mul_nonsing_inv _ hU
  have h2 : (1 - A) * (1 - z • closingN S A Pi)⁻¹ = 1 - A := by
    rw [← h1, Matrix.mul_assoc, hK, Matrix.mul_one, h1]
  have h3 : (1 - A) * (1 - A) = 1 - A := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hA2]; simp
  rw [closingMap, Matrix.mul_add, h3, ← Matrix.mul_assoc, h2, closingT, Matrix.mul_smul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAP, Matrix.zero_mul, Matrix.zero_mul, smul_zero,
    add_zero]

/-- **The closed wave obeys the feedback**: for `a = C(z)(1 - A)a'`, `Aa = zΠSa` and
`(1 - A)a = (1 - A)a'`. -/
theorem feedback_closingMap (hA2 : A * A = A) (hAPi : A * Pi = Pi)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (a' : ι → ℂ) :
    A *ᵥ (closingMap S A Pi z *ᵥ ((1 - A) *ᵥ a')) =
        z • (Pi *ᵥ (S *ᵥ (closingMap S A Pi z *ᵥ ((1 - A) *ᵥ a')))) ∧
      (1 - A) *ᵥ (closingMap S A Pi z *ᵥ ((1 - A) *ᵥ a')) = (1 - A) *ᵥ a' := by
  refine ⟨?_, ?_⟩
  · rw [mulVec_mulVec, closingMap_feedback hA2 hAPi hU, smul_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec]
  · rw [mulVec_mulVec, mulVec_mulVec, one_sub_mul_closingMap hA2 hAPi hU, ← mulVec_mulVec]
    have h3 : (1 - A) * (1 - A) = 1 - A := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hA2]; simp
    rw [mulVec_mulVec, h3]

end Closing

/-- The closing map does not change near parts (`A`, `Π` far). -/
theorem nP_closingMap_mulVec {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {A₀ P₀ : Matrix (Fin W) (Fin W) ℂ} {z : ℂ}
    (hU : IsUnit (1 - z • closingN S (farEmbed A₀) (farEmbed P₀)).det)
    (x : Fin 2 × Fin W → ℂ) :
    nP (closingMap S (farEmbed A₀) (farEmbed P₀) z *ᵥ x) = nP x := by
  set N := closingN S (farEmbed A₀) (farEmbed P₀)
  have hK : (1 - z • N) * (1 - z • N)⁻¹ = 1 := mul_nonsing_inv _ hU
  have hKv : ∀ v, nP ((1 - z • N)⁻¹ *ᵥ v) = nP v := by
    intro v
    have h1 : (1 - z • N) *ᵥ ((1 - z • N)⁻¹ *ᵥ v) = v := by rw [mulVec_mulVec, hK, one_mulVec]
    rw [sub_mulVec, one_mulVec, smul_mulVec] at h1
    have e : (1 - z • N)⁻¹ *ᵥ v = v + z • (N *ᵥ ((1 - z • N)⁻¹ *ᵥ v)) := by
      calc (1 - z • N)⁻¹ *ᵥ v = ((1 - z • N)⁻¹ *ᵥ v - z • (N *ᵥ ((1 - z • N)⁻¹ *ᵥ v))) +
            z • (N *ᵥ ((1 - z • N)⁻¹ *ᵥ v)) := by abel
        _ = v + z • (N *ᵥ ((1 - z • N)⁻¹ *ᵥ v)) := by rw [h1]
    rw [e, nP_add, nP_smul]
    simp only [N, closingN, ← mulVec_mulVec, nP_farEmbed, smul_zero, add_zero]
  rw [closingMap, add_mulVec, nP_add, closingT, ← mulVec_mulVec, hKv, smul_mulVec, nP_smul,
    ← mulVec_mulVec, ← mulVec_mulVec, nP_farEmbed, smul_zero, add_zero, sub_mulVec, nP_sub,
    one_mulVec, nP_farEmbed, sub_zero]

/-!
## Scattering and the Cayley inverse as relations between waves
-/

section Cayley

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ζ c : ℂ}

theorem scat_wave {Y : Matrix ι ι ℂ} (hK : IsUnit (ζ • (1 : Matrix ι ι ℂ) - Y)) :
    (1 - c • (ζ • (1 : Matrix ι ι ℂ) - Y)⁻¹) * (ζ • 1 - Y) = (ζ • 1 - Y) - c • 1 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hK)]

theorem cay_wave {V : Matrix ι ι ℂ} (hV : IsUnit (1 - V).det) :
    V * (ζ • 1 - (ζ • 1 - c • (1 - V)⁻¹)) = (ζ • 1 - (ζ • 1 - c • (1 - V)⁻¹)) - c • 1 := by
  rw [sub_sub_cancel]
  have h : (1 - V) * (1 - V)⁻¹ = 1 := mul_nonsing_inv _ hV
  have e : V * (1 - V)⁻¹ = (1 - V)⁻¹ - 1 := by
    have : V * (1 - V)⁻¹ = (1 - V)⁻¹ - (1 - V) * (1 - V)⁻¹ := by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel
    rw [this, h]
  rw [Matrix.mul_smul, e, smul_sub]

theorem cay_of_wave {V Y : Matrix ι ι ℂ} (hV : IsUnit (1 - V).det)
    (h : V * (ζ • 1 - Y) = (ζ • 1 - Y) - c • 1) :
    ζ • (1 : Matrix ι ι ℂ) - c • (1 - V)⁻¹ = Y := by
  have h1 : (1 - V) * (ζ • 1 - Y) = c • 1 := by
    rw [Matrix.sub_mul, Matrix.one_mul, h]; abel
  have h2 : ζ • 1 - Y = c • (1 - V)⁻¹ := by
    have := congrArg ((1 - V)⁻¹ * ·) h1
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hV, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one] at this
    exact this
  rw [← h2]; abel

end Cayley

/-!
## The fresh step on waves
-/

/-- `G(Z, F) = A_F - E - Z₀₀`, the fresh pivot. -/
abbrev freshPivot (E : ℝ) (Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (F : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  F.1 0 - (E : ℂ) • 1 - portBlock Z 0 0

/-- The interface relation of the old wave `w` and the new wave `v` at the old near port. -/
def FreshLink (E : ℝ) (Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (F : LayerSample W .oneBlockOnePort) (v w : Fin 2 × Fin W → ℂ) : Prop :=
  fP w = fP v ∧ nP (Z *ᵥ w) = (F.1 0 - (E : ℂ) • 1) *ᵥ nP w + F.2 0 0 *ᵥ nP v

theorem freshLink_pivot {E : ℝ} {Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {F : LayerSample W .oneBlockOnePort} {v w : Fin 2 × Fin W → ℂ} (h : FreshLink E Z F v w) :
    freshPivot E Z F *ᵥ nP w = portBlock Z 0 1 *ᵥ fP v - F.2 0 0 *ᵥ nP v := by
  obtain ⟨hf, hn⟩ := h
  rw [nP_mulVec, hf, sub_mulVec] at hn
  simp only [freshPivot, sub_mulVec]
  rw [eq_sub_iff_add_eq]
  calc F.1 0 *ᵥ nP w - ((E : ℂ) • 1) *ᵥ nP w - portBlock Z 0 0 *ᵥ nP w + F.2 0 0 *ᵥ nP v =
        (F.1 0 *ᵥ nP w - ((E : ℂ) • 1) *ᵥ nP w + F.2 0 0 *ᵥ nP v) - portBlock Z 0 0 *ᵥ nP w := by
        abel
    _ = portBlock Z 0 1 *ᵥ fP v := by rw [← hn]; abel

theorem fresh_wave_exists (E : ℝ) (Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (F : LayerSample W .oneBlockOnePort) (hG : IsUnit (freshPivot E Z F))
    (v : Fin 2 × Fin W → ℂ) : ∃ w, FreshLink E Z F v w := by
  set g := (freshPivot E Z F)⁻¹ *ᵥ (portBlock Z 0 1 *ᵥ fP v - F.2 0 0 *ᵥ nP v)
  refine ⟨pVec g (fP v), by simp, ?_⟩
  have hg : freshPivot E Z F *ᵥ g = portBlock Z 0 1 *ᵥ fP v - F.2 0 0 *ᵥ nP v := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG), one_mulVec]
  simp only [freshPivot, sub_mulVec] at hg
  have hg' : portBlock Z 0 1 *ᵥ fP v = F.1 0 *ᵥ g - ((E : ℂ) • 1) *ᵥ g -
      portBlock Z 0 0 *ᵥ g + F.2 0 0 *ᵥ nP v := by
    rw [hg]; abel
  rw [nP_mulVec, nP_pVec, fP_pVec, hg', sub_mulVec]
  abel

theorem fresh_wave_unique {E : ℝ} {Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {F : LayerSample W .oneBlockOnePort} (hG : IsUnit (freshPivot E Z F))
    {v w w' : Fin 2 × Fin W → ℂ} (h : FreshLink E Z F v w) (h' : FreshLink E Z F v w') :
    w = w' := by
  refine vec_ext ?_ (h.1.trans h'.1.symm)
  have e := (freshLink_pivot h).trans (freshLink_pivot h').symm
  have hi := (isUnit_iff_isUnit_det _).mp hG
  have := congrArg ((freshPivot E Z F)⁻¹ *ᵥ ·) e
  simp only [mulVec_mulVec, nonsing_inv_mul _ hi, one_mulVec] at this
  exact this

/-- **The fresh step on waves**: if `w` is linked to `v`, then `Φ_F(Z)v` has the far part of
`Zw` and the near part `-B*w₀`. -/
theorem fresh_wave {E : ℝ} {Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {F : LayerSample W .oneBlockOnePort} (hG : IsUnit (freshPivot E Z F))
    {v w : Fin 2 × Fin W → ℂ} (h : FreshLink E Z F v w) :
    fP (freshTwoPortSchur E Z F *ᵥ v) = fP (Z *ᵥ w) ∧
      nP (freshTwoPortSchur E Z F *ᵥ v) = -((F.2 0 0)ᴴ *ᵥ nP w) := by
  have hi := (isUnit_iff_isUnit_det _).mp hG
  have hw : nP w = (freshPivot E Z F)⁻¹ *ᵥ (portBlock Z 0 1 *ᵥ fP v - F.2 0 0 *ᵥ nP v) := by
    have := congrArg ((freshPivot E Z F)⁻¹ *ᵥ ·) (freshLink_pivot h)
    simp only [mulVec_mulVec, nonsing_inv_mul _ hi, one_mulVec] at this
    exact this
  have hf := h.1
  refine ⟨?_, ?_⟩
  · rw [fP_mulVec, fP_mulVec, hf, hw]
    simp only [freshTwoPortSchur, portBlock_ofPortBlocks, Matrix.cons_val_one,
      Matrix.cons_val_zero, freshPivot]
    simp only [neg_mulVec, add_mulVec, ← mulVec_mulVec, mulVec_sub]
    abel
  · rw [nP_mulVec, hw]
    simp only [freshTwoPortSchur, portBlock_ofPortBlocks, Matrix.cons_val_one,
      Matrix.cons_val_zero, freshPivot]
    simp only [neg_mulVec, ← mulVec_mulVec, mulVec_sub]
    abel

/-!
## Padded scatterers with a general far padding
-/

/-- `(1 - ΠᴴΠ)𝕊C(z)(1 - A) + QA`: the padded closed scatterer with far padding `Q`
(`Q = Πᴴ`: `padScat`; `Q = zΠᴴ`: the phase-`z` padding). -/
def padScatQ {ι : Type*} [Fintype ι] [DecidableEq ι] (S A Pi Q : Matrix ι ι ℂ) (z : ℂ) :
    Matrix ι ι ℂ :=
  (1 - Piᴴ * Pi) * S * closingMap S A Pi z * (1 - A) + Q * A

theorem padScat_eq_padScatQ {ι : Type*} [Fintype ι] [DecidableEq ι] (S A Pi : Matrix ι ι ℂ)
    (z : ℂ) : B3LayerMean.padScat S A Pi z = padScatQ S A Pi Piᴴ z := rfl

/-!
## Growth commutes with the padded closing
-/

/-- **Near-end growth commutes with the padded closing** (deterministic):
`Cay(𝕊_pad(𝕊(Φ_F Y))) = Φ_F(Cay(𝕊_pad(𝕊(Y))))`. -/
theorem cay_padScatQ_freshTwoPortSchur (b E : ℝ) (hη : 0 < etaZ b E)
    {A₀ P₀ Q₀ : Matrix (Fin W) (Fin W) ℂ} (hA2 : A₀ * A₀ = A₀) (hAP : A₀ * P₀ = P₀) (z : ℂ)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (F : LayerSample W .oneBlockOnePort)
    (hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Y))
    (hKg : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      freshTwoPortSchur E Y F))
    (hG : IsUnit (freshPivot E Y F))
    (hU : IsUnit (1 - z • closingN (twoPortScattering b E Y) (farEmbed A₀) (farEmbed P₀)).det)
    (hUg : IsUnit (1 - z • closingN (twoPortScattering b E (freshTwoPortSchur E Y F))
      (farEmbed A₀) (farEmbed P₀)).det)
    (hV : IsUnit (1 - padScatQ (twoPortScattering b E Y) (farEmbed A₀)
      (farEmbed P₀) (farEmbed Q₀) z).det)
    (hVg : IsUnit (1 - padScatQ (twoPortScattering b E (freshTwoPortSchur E Y F))
      (farEmbed A₀) (farEmbed P₀) (farEmbed Q₀) z).det)
    (hGp : IsUnit (freshPivot E (boundaryZ b E • 1 - (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
      (1 - padScatQ (twoPortScattering b E Y) (farEmbed A₀) (farEmbed P₀) (farEmbed Q₀) z)⁻¹) F)) :
    boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
          (1 - padScatQ (twoPortScattering b E (freshTwoPortSchur E Y F))
            (farEmbed A₀) (farEmbed P₀) (farEmbed Q₀) z)⁻¹ =
      freshTwoPortSchur E (boundaryZ b E • 1 - (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
        (1 - padScatQ (twoPortScattering b E Y) (farEmbed A₀) (farEmbed P₀) (farEmbed Q₀) z)⁻¹)
        F := by
  set ζ := boundaryZ b E
  set c : ℂ := ((2 * etaZ b E : ℝ) : ℂ) * Complex.I with hcdef
  have hc : c ≠ 0 := by
    have : ((2 * etaZ b E : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * etaZ b E ≠ 0)
    exact mul_ne_zero this Complex.I_ne_zero
  set A := farEmbed A₀ with hAdef
  set Pi := farEmbed P₀ with hPidef
  have hA2' : A * A = A := by rw [hAdef, farEmbed_mul, hA2]
  have hAPi' : A * Pi = Pi := by rw [hAdef, hPidef, farEmbed_mul, hAP]
  have hPiH : Piᴴ = farEmbed P₀ᴴ := farEmbed_conjTranspose _
  have hO : Piᴴ * Pi = farEmbed (P₀ᴴ * P₀) := by rw [hPiH, farEmbed_mul]
  set Yp := freshTwoPortSchur E Y F
  set S := twoPortScattering b E Y with hSdef
  set Sg := twoPortScattering b E Yp with hSgdef
  set V := padScatQ S A Pi (farEmbed Q₀) z with hVdef
  set Vg := padScatQ Sg A Pi (farEmbed Q₀) z with hVgdef
  set X := ζ • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - c • (1 - V)⁻¹ with hXdef
  
  have hSw : ∀ w, S *ᵥ ((ζ • 1 - Y) *ᵥ w) = (ζ • 1 - Y) *ᵥ w - c • w := fun w => by
    show (1 - c • (ζ • 1 - Y)⁻¹) *ᵥ ((ζ • 1 - Y) *ᵥ w) = _
    rw [mulVec_mulVec, scat_wave hK, sub_mulVec, smul_mulVec, one_mulVec]
  have hSgw : ∀ w, Sg *ᵥ ((ζ • 1 - Yp) *ᵥ w) = (ζ • 1 - Yp) *ᵥ w - c • w := fun w => by
    show (1 - c • (ζ • 1 - Yp)⁻¹) *ᵥ ((ζ • 1 - Yp) *ᵥ w) = _
    rw [mulVec_mulVec, scat_wave hKg, sub_mulVec, smul_mulVec, one_mulVec]
  have hVw : ∀ w, V *ᵥ ((ζ • 1 - X) *ᵥ w) = (ζ • 1 - X) *ᵥ w - c • w := fun w => by
    rw [mulVec_mulVec, hXdef, cay_wave hV, sub_mulVec, smul_mulVec, one_mulVec]
  clear_value X
  refine cay_of_wave hVg ?_
  refine Matrix.toLin'.injective (LinearMap.ext fun v'' => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← mulVec_mulVec, sub_mulVec (ζ • 1 - freshTwoPortSchur E X F) (c • 1), smul_mulVec,
    one_mulVec]
  
  obtain ⟨w', hw'⟩ := fresh_wave_exists E X F hGp v''
  obtain ⟨hf'', hn''⟩ := fresh_wave hGp hw'
  set a' := (ζ • 1 - X) *ᵥ w' with ha'def
  have hb' : V *ᵥ a' = a' - c • w' := hVw w'
  clear_value a'
  
  set a := closingMap S A Pi z *ᵥ ((1 - A) *ᵥ a') with hadef
  obtain ⟨hfb, hla⟩ := feedback_closingMap hA2' hAPi' hU a'
  set w := (ζ • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Y)⁻¹ *ᵥ a with hwdef
  have haw : (ζ • 1 - Y) *ᵥ w = a := by
    rw [hwdef, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hK), one_mulVec]
  have hVa : V *ᵥ a' = (1 - Piᴴ * Pi) *ᵥ (S *ᵥ a) + farEmbed Q₀ *ᵥ (A *ᵥ a') := by
    rw [hadef]
    simp only [hVdef, padScatQ, add_mulVec, ← mulVec_mulVec]
  have hna : nP a = nP a' := by
    rw [hadef, nP_closingMap_mulVec hU, sub_mulVec, one_mulVec, nP_sub, hAdef, nP_farEmbed,
      sub_zero]
  rw [← hadef] at hfb hla
  clear_value w a
  have hba : S *ᵥ a = a - c • w := by
    have := hSw w
    rwa [haw] at this
  -- near parts agree
  have hnV : nP (V *ᵥ a') = nP (S *ᵥ a) := by
    rw [hVa, nP_add, hO, nP_one_sub_farEmbed, nP_farEmbed, add_zero]
  have hnw : nP w = nP w' := by
    have h1 : nP a' - c • nP w' = nP a - c • nP w := by
      rw [← nP_smul, ← nP_sub, ← hb', hnV, hba, nP_sub, nP_smul]
    rw [hna] at h1
    have h2 : c • nP w = c • nP w' := by
      have := congrArg (fun t => nP a' - t) h1
      simp only [sub_sub_cancel] at this
      exact this.symm
    exact smul_right_injective _ hc h2
  have hYw : Y *ᵥ w = ζ • w - a := by
    rw [← haw, sub_mulVec, smul_mulVec, one_mulVec]; abel
  have hXw : X *ᵥ w' = ζ • w' - a' := by
    rw [ha'def, sub_mulVec, smul_mulVec, one_mulVec]; abel
  
  set vg := pVec (nP v'') (fP w) with hvgdef
  have hlink : FreshLink E Y F vg w := by
    refine ⟨by rw [hvgdef, fP_pVec], ?_⟩
    rw [hvgdef, nP_pVec, hnw, hYw, nP_sub, nP_smul, hnw, hna, ← nP_smul, ← nP_sub, ← hXw]
    exact hw'.2
  obtain ⟨hfg, hng⟩ := fresh_wave hG hlink
  set ag := (ζ • 1 - Yp) *ᵥ vg with hagdef
  have hbg : Sg *ᵥ ag = ag - c • vg := hSgw vg
  have hfag : fP ag = fP a := by
    rw [hagdef, sub_mulVec, smul_mulVec, one_mulVec, fP_sub, hfg, fP_smul, hvgdef, fP_pVec,
      hYw, fP_sub, fP_smul]
    abel
  set a'' := (ζ • 1 - freshTwoPortSchur E X F) *ᵥ v'' with ha''def
  have hna'' : nP a'' = nP ag := by
    rw [ha''def, hagdef, sub_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec,
      one_mulVec, nP_sub, nP_sub, hn'', hng, nP_smul, nP_smul, hvgdef, nP_pVec, hnw]
  have hfa'' : fP a'' = fP a' := by
    rw [ha''def, sub_mulVec, smul_mulVec, one_mulVec, fP_sub, hf'', fP_smul, ← hw'.1, ha'def,
      sub_mulVec, smul_mulVec, one_mulVec, fP_sub, fP_smul]
  
  have hfeed : A *ᵥ ag = z • (Pi *ᵥ (Sg *ᵥ ag)) := by
    rw [hAdef, farEmbed_mulVec_congr A₀ hfag, ← hAdef, hfb, hba, hbg, hPidef]
    congr 1
    refine farEmbed_mulVec_congr P₀ ?_
    rw [fP_sub, fP_sub, fP_smul, fP_smul, hfag, hvgdef, fP_pVec]
  have hCg := closingMap_mulVec_of_feedback hA2' hUg hfeed
  have hlA : (1 - A) *ᵥ a'' = (1 - A) *ᵥ ag := by
    refine vec_ext ?_ ?_
    · rw [hAdef, nP_one_sub_farEmbed, nP_one_sub_farEmbed, hna'']
    · have := congrArg fP hla
      rw [hAdef, fP_one_sub_farEmbed, fP_one_sub_farEmbed] at this
      rw [hAdef, fP_one_sub_farEmbed, fP_one_sub_farEmbed, hfa'', hfag, this]
  
  have hVga : Vg *ᵥ a'' = (1 - Piᴴ * Pi) *ᵥ (Sg *ᵥ ag) + farEmbed Q₀ *ᵥ (A *ᵥ a'') := by
    have e : Vg *ᵥ a'' = (1 - Piᴴ * Pi) *ᵥ (Sg *ᵥ (closingMap Sg A Pi z *ᵥ ((1 - A) *ᵥ a''))) +
        farEmbed Q₀ *ᵥ (A *ᵥ a'') := by
      simp only [hVgdef, padScatQ, add_mulVec, ← mulVec_mulVec]
    rw [e, hlA, hCg]
  rw [hVga, hbg]
  refine vec_ext ?_ ?_
  · rw [nP_add, hO, nP_one_sub_farEmbed, nP_farEmbed, add_zero, nP_sub, nP_sub, hna'',
      nP_smul, nP_smul, hvgdef, nP_pVec]
  · have hfV := congrArg fP (hVa.symm.trans hb')
    rw [fP_add, hO, fP_one_sub_farEmbed, fP_farEmbed, hba, fP_sub, fP_smul] at hfV
    rw [fP_add, hO, fP_one_sub_farEmbed, fP_farEmbed, fP_sub, fP_smul, hfag, hvgdef,
      fP_pVec, hAdef, fP_farEmbed, hfa'', ← fP_farEmbed, ← hAdef, fP_sub, fP_smul, hfa'',
      ← hw'.1]
    rw [hAdef, fP_farEmbed] at hfV
    rw [← fP_farEmbed A₀ a'] at hfV
    rw [← hAdef] at hfV
    simpa [ha'def] using hfV

/-- **Growth commutes with the padded closing `padScat`** (`Q = Πᴴ`). -/
theorem cay_padScat_freshTwoPortSchur (b E : ℝ) (hη : 0 < etaZ b E)
    {A₀ P₀ : Matrix (Fin W) (Fin W) ℂ} (hA2 : A₀ * A₀ = A₀) (hAP : A₀ * P₀ = P₀) (z : ℂ)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (F : LayerSample W .oneBlockOnePort)
    (hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Y))
    (hKg : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      freshTwoPortSchur E Y F))
    (hG : IsUnit (freshPivot E Y F))
    (hU : IsUnit (1 - z • closingN (twoPortScattering b E Y) (farEmbed A₀) (farEmbed P₀)).det)
    (hUg : IsUnit (1 - z • closingN (twoPortScattering b E (freshTwoPortSchur E Y F))
      (farEmbed A₀) (farEmbed P₀)).det)
    (hV : IsUnit (1 - B3LayerMean.padScat (twoPortScattering b E Y) (farEmbed A₀)
      (farEmbed P₀) z).det)
    (hVg : IsUnit (1 - B3LayerMean.padScat (twoPortScattering b E (freshTwoPortSchur E Y F))
      (farEmbed A₀) (farEmbed P₀) z).det)
    (hGp : IsUnit (freshPivot E (boundaryZ b E • 1 - (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
      (1 - B3LayerMean.padScat (twoPortScattering b E Y) (farEmbed A₀) (farEmbed P₀) z)⁻¹) F)) :
    boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
          (1 - B3LayerMean.padScat (twoPortScattering b E (freshTwoPortSchur E Y F))
            (farEmbed A₀) (farEmbed P₀) z)⁻¹ =
      freshTwoPortSchur E (boundaryZ b E • 1 - (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
        (1 - B3LayerMean.padScat (twoPortScattering b E Y) (farEmbed A₀) (farEmbed P₀) z)⁻¹)
        F := by
  simp only [padScat_eq_padScatQ, farEmbed_conjTranspose] at hV hVg hGp ⊢
  exact cay_padScatQ_freshTwoPortSchur b E hη hA2 hAP z Y F hK hKg hG hU hUg hV hVg hGp

end BlockBand.SourceProcess.PhysApprox.B3
