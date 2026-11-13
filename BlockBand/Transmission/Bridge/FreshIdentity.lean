module

public import BlockBand.Transmission.Bridge.TransportAlgebra

/-!
# The fresh-layer identity behind the transport `N`

`fresh_identity`: with `ι` the near-row selector, `a = A - E`, `B'` the fresh bond and
`N = freshTransport b E 𝕏 ω'`,
`(a - z)(ιℝN) - z⁻¹B'B'ᴴ(ιℝN) + ιN + z⁻¹B'ι = 0`, the hypothesis `hfresh` of
`transport_algebra` (hypotheses: the fresh layer matrix and `z - 𝕏₁₁` invertible, `z ≠ 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix

variable {W : ℕ}

/-- The near-row selector `ι* : ℂ^{2W} → ℂ^W` (`ι*v = v_near`). -/
def nearSel (W : ℕ) : Matrix (Fin W) (Fin 2 × Fin W) ℂ :=
  fun x c => if c = (0, x) then 1 else 0

/-- Column block `i` of a `W × 2W` matrix. -/
def colBlock (M : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => M x (i, y)

theorem colBlock_mul (A : Matrix (Fin W) (Fin W) ℂ) (M : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (i : Fin 2) : colBlock (A * M) i = A * colBlock M i := by
  ext x y; simp [colBlock, Matrix.mul_apply]

theorem colBlock_add (M M' : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    colBlock (M + M') i = colBlock M i + colBlock M' i := by ext x y; simp [colBlock]

theorem colBlock_sub (M M' : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    colBlock (M - M') i = colBlock M i - colBlock M' i := by ext x y; simp [colBlock]

theorem colBlock_smul (c : ℂ) (M : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    colBlock (c • M) i = c • colBlock M i := by ext x y; simp [colBlock]

theorem eq_zero_of_colBlock (M : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (h : ∀ i, colBlock M i = 0) : M = 0 := by
  ext x ⟨i, y⟩; simpa [colBlock] using congrFun (congrFun (h i) x) y

theorem nearSel_mul_apply {q : Type*} (M : Matrix (Fin 2 × Fin W) q ℂ) (x : Fin W) (c : q) :
    (nearSel W * M) x c = M (0, x) c := by
  simp [nearSel, Matrix.mul_apply, ite_mul]

/-- The four `W × W` blocks of the fresh layer resolvent `𝒢`. -/
def freshBlock {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (i j : Bool) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => freshLayer b E X ω
    (if i then Sum.inl ((0 : Fin 1), x) else Sum.inr ((0 : Fin 1), x))
    (if j then Sum.inl ((0 : Fin 1), y) else Sum.inr ((0 : Fin 1), y))

/-- The defining identities `𝒢⁻¹𝒢 = 1` of the fresh layer in `W × W` blocks
(`a = A - E`, block `true` = physical, `false` = port). -/
theorem freshBlock_identities (b E : ℝ) (X A B : Matrix (Fin W) (Fin W) ℂ)
    (hG : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2)
      ((fun _ => A, fun _ _ => B) : LayerSample W .oneBlockOnePort))) :
    let g := freshBlock b E X ((fun _ => A, fun _ _ => B) : LayerSample W .oneBlockOnePort)
    (A - (E : ℂ) • 1 - X) * g true true + B * g false true = 1 ∧
      (A - (E : ℂ) • 1 - X) * g true false + B * g false false = 0 ∧
      Bᴴ * g true true + boundaryZ b E • g false true = 0 ∧
      Bᴴ * g true false + boundaryZ b E • g false false = 1 := by
  intro g
  set M := layerMatrix .oneBlockOnePort E (boundaryZ b E)
    (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2)
    ((fun _ => A, fun _ _ => B) : LayerSample W .oneBlockOnePort) with hMdef
  have hMG : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hG)
  have hg : ∀ i j x y, g i j x y = M⁻¹
      (if i then Sum.inl ((0 : Fin 1), x) else Sum.inr ((0 : Fin 1), x))
      (if j then Sum.inl ((0 : Fin 1), y) else Sum.inr ((0 : Fin 1), y)) := fun _ _ _ _ => rfl
  set G := M⁻¹
  clear_value G
  have key : ∀ (i j : Bool) (x y : Fin W),
      ((if i then (A - (E : ℂ) • 1 - X) else Bᴴ) * g true j +
        (if i then B else boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ)) * g false j) x y =
        (M * G) (if i then Sum.inl ((0 : Fin 1), x) else Sum.inr ((0 : Fin 1), x))
          (if j then Sum.inl ((0 : Fin 1), y) else Sum.inr ((0 : Fin 1), y)) := by
    intro i j x y
    cases i <;> cases j <;>
      simp [hg, hMdef, layerMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
        BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix, LayerShape.incident,
        Matrix.one_apply, Matrix.conjTranspose_apply, sub_mul,
        Finset.sum_sub_distrib, ite_mul]
  rw [hMG] at key
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x y
  · simpa [Matrix.one_apply] using key true true x y
  · simpa [Matrix.one_apply] using key true false x y
  · simpa [Matrix.one_apply] using key false true x y
  · simpa [Matrix.one_apply] using key false false x y

/-- **The fresh identity** (`hfresh` of `transport_algebra`;). -/
theorem fresh_identity (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A B : Matrix (Fin W) (Fin W) ℂ) (hz : boundaryZ b E ≠ 0)
    (hD : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1))
    (hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX))
    (hG : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => nearSchur (boundaryZ b E) XX u.2 v.2)
      ((fun _ => A, fun _ _ => B) : LayerSample W .oneBlockOnePort))) :
    (A - (E : ℂ) • 1 - boundaryZ b E • 1) *
        (nearSel W * twoPortResolvent b E XX * freshTransport b E XX (fun _ => A, fun _ _ => B)) -
      (boundaryZ b E)⁻¹ • (B * Bᴴ * (nearSel W * twoPortResolvent b E XX *
        freshTransport b E XX (fun _ => A, fun _ _ => B))) +
      nearSel W * freshTransport b E XX (fun _ => A, fun _ _ => B) +
      (boundaryZ b E)⁻¹ • (B * nearSel W) = 0 := by
  set z := boundaryZ b E
  set X := nearSchur z XX
  obtain ⟨I1, I2, I3, I4⟩ := freshBlock_identities b E X A B hG
  set ω : LayerSample W .oneBlockOnePort := (fun _ => A, fun _ _ => B)
  set N := freshTransport b E XX ω
  set Rr := twoPortResolvent b E XX
  set K : Matrix (Fin W) (Fin W) ℂ := z • 1 - X
  set g := freshBlock b E X ω
  set R01 := portBlock Rr 0 1
  have hR : portBlock Rr 0 0 = K⁻¹ := portBlock_twoPortResolvent_zero_zero b E XX hD
  have hRK : K⁻¹ * K = 1 := Matrix.nonsing_inv_mul K ((Matrix.isUnit_iff_isUnit_det K).mp hK)
  have hL : freshL b E X ω = K * g true false := rfl
  have hΔ : freshDelta b E X ω = K * g true true * K - K := rfl
  have cb1 : ∀ i, colBlock (nearSel W * Rr * N) i =
      if i = 0 then K⁻¹ * (K * g true false) else K⁻¹ * ((K * g true true * K - K) * R01) + R01 := by
    intro i; rw [← hR, ← hL, ← hΔ]
    ext x y
    simp only [colBlock, Matrix.of_apply, Matrix.mul_assoc, nearSel_mul_apply]
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    fin_cases i <;> simp [N, freshTransport, portBlock, R01, Matrix.mul_apply, Matrix.one_apply] <;> rfl
  have cb2 : ∀ i, colBlock (nearSel W * N) i =
      if i = 0 then K * g true false else (K * g true true * K - K) * R01 := by
    intro i; rw [← hL, ← hΔ]
    ext x y; fin_cases i <;> simp [colBlock, nearSel_mul_apply, N, freshTransport, R01] <;> rfl
  have cb3 : ∀ i, colBlock (B * nearSel W) i = if i = 0 then B else 0 := by
    intro i; ext x y
    fin_cases i <;> simp [colBlock, Matrix.mul_apply, nearSel]
  have hKX : A - (E : ℂ) • 1 - z • 1 + K = A - (E : ℂ) • 1 - X := by
    simp only [K]; abel
  have hzz : z⁻¹ * boundaryZ b E = 1 := inv_mul_cancel₀ hz
  have hg22 : g false false = z⁻¹ • (1 - Bᴴ * g true false) := by
    have := congrArg (z⁻¹ • ·) (eq_sub_of_add_eq' I4)
    simpa only [smul_smul, hzz, one_smul] using this
  have hg21 : g false true = -(z⁻¹ • (Bᴴ * g true true)) := by
    have := congrArg (z⁻¹ • ·) (eq_neg_of_add_eq_zero_right I3)
    simpa only [smul_smul, hzz, one_smul, smul_neg] using this
  have h1 : (A - (E : ℂ) • 1 - X) * g true true - z⁻¹ • (B * (Bᴴ * g true true)) = 1 := by
    have h := I1
    rw [hg21, Matrix.mul_neg, Matrix.mul_smul, ← sub_eq_add_neg] at h
    exact h
  apply eq_zero_of_colBlock
  intro i
  simp only [colBlock_add, colBlock_sub, colBlock_smul, colBlock_mul, cb1, cb2, cb3]
  fin_cases i
  · -- near column: `(a - X)𝒢₁₂ + B𝒢₂₂ = 0` with `𝒢₂₂ = z⁻¹(1 - Bᴴ𝒢₁₂)`
    simp only [Fin.zero_eta, Fin.isValue, ite_true]
    rw [← Matrix.mul_assoc K⁻¹, hRK, Matrix.one_mul]
    refine Eq.trans ?_ I2
    rw [← hKX, hg22]
    simp only [Matrix.add_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    module
  · -- far column: `[(a - X)𝒢₁₁ - z⁻¹BBᴴ𝒢₁₁ - 1] K ℝ₀₁ = 0`
    simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ite_false, smul_zero, add_zero]
    have e2 : K⁻¹ * ((K * g true true * K - K) * R01) + R01 = g true true * (K * R01) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc K⁻¹ K, hRK, Matrix.one_mul, ← Matrix.mul_assoc K⁻¹ K, hRK,
        Matrix.one_mul]
      abel
    rw [e2]
    have e3 : (A - (E : ℂ) • 1 - z • 1) * (g true true * (K * R01)) -
        z⁻¹ • (B * Bᴴ * (g true true * (K * R01))) + (K * g true true * K - K) * R01 =
        ((A - (E : ℂ) • 1 - X) * g true true - z⁻¹ • (B * (Bᴴ * g true true)) - 1) * (K * R01) := by
      rw [← hKX]
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
      abel
    rw [e3, h1, sub_self, Matrix.zero_mul]

end BlockBand.Transmission.Bridge
