module

public import BlockBand.SourceProcess.ProjSeparator.Fluct

/-!
# Deterministic bounds through `Q = ℝ₁₂`

For a matrix `Q` with `‖Q‖ ≤ a` (operator norm) and `S = frob Q` (`= Tr QQ*`):
* `vecNorm_conjQ_le`: `‖Q*v‖ ≤ a‖v‖` and `‖Q*v‖ ≤ √S‖v‖`; `vecNorm_Q_le`: the same for `Q`;
* `norm_bilinear_MQ_le`: `|x*(MQ(MQ)*)y| ≤ min(a², S)‖M‖²‖x‖‖y‖` (the squared mean of `Δ`,
  which is included in `δ₀²`);
* `vecNorm_wVec_le`: `‖QQ*M*x‖ ≤ a√S‖M‖‖x‖` and `≤ S‖M‖‖x‖`;
* `norm_farQ_le`: `‖ℝ₁₂‖ ≤ η⁻¹` (Hermitian `𝕏`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem vecNorm_conjQ_le (Q : Matrix (Fin W) (Fin W) ℂ) {a : ℝ} (ha : ‖Q‖ ≤ a) (v : Fin W → ℂ) :
    vecNorm (Qᴴ *ᵥ v) ≤ a * vecNorm v ∧ vecNorm (Qᴴ *ᵥ v) ≤ Real.sqrt (frob Q) * vecNorm v := by
  refine ⟨(vecNorm_mulVec_le Qᴴ v).trans ?_, ?_⟩
  · rw [Matrix.l2_opNorm_conjTranspose]
    exact mul_le_mul_of_nonneg_right ha (vecNorm_nonneg v)
  · have := vecNorm_mulVec_le_frob Qᴴ v
    rwa [frob_conjTranspose] at this

theorem vecNorm_Q_le (Q : Matrix (Fin W) (Fin W) ℂ) {a : ℝ} (ha : ‖Q‖ ≤ a) (v : Fin W → ℂ) :
    vecNorm (Q *ᵥ v) ≤ a * vecNorm v ∧ vecNorm (Q *ᵥ v) ≤ Real.sqrt (frob Q) * vecNorm v :=
  ⟨(vecNorm_mulVec_le Q v).trans (mul_le_mul_of_nonneg_right ha (vecNorm_nonneg v)),
    vecNorm_mulVec_le_frob Q v⟩

theorem sqrt_frob_mul_self (Q : Matrix (Fin W) (Fin W) ℂ) :
    Real.sqrt (frob Q) * Real.sqrt (frob Q) = frob Q :=
  Real.mul_self_sqrt (frob_nonneg Q)

/-- `|x*(MQ(MQ)*)y| ≤ min(a², S)‖M‖²‖x‖‖y‖`. -/
theorem norm_bilinear_MQ_le (M Q : Matrix (Fin W) (Fin W) ℂ) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : ‖Q‖ ≤ a) (x y : Fin W → ℂ) :
    ‖bilinear x (M * Q * (M * Q)ᴴ) y‖ ≤ min (a ^ 2) (frob Q) * ‖M‖ ^ 2 * vecNorm x * vecNorm y := by
  have e : bilinear x (M * Q * (M * Q)ᴴ) y =
      star ((M * Q)ᴴ *ᵥ x) ⬝ᵥ ((M * Q)ᴴ *ᵥ y) := by
    rw [bilinear, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
      conjTranspose_conjTranspose]
  have hv : ∀ z : Fin W → ℂ, vecNorm ((M * Q)ᴴ *ᵥ z) ^ 2 ≤
      min (a ^ 2) (frob Q) * (‖M‖ * vecNorm z) ^ 2 := by
    intro z
    rw [conjTranspose_mul, ← Matrix.mulVec_mulVec]
    obtain ⟨h1, h2⟩ := vecNorm_conjQ_le Q ha (Mᴴ *ᵥ z)
    have hM : vecNorm (Mᴴ *ᵥ z) ≤ ‖M‖ * vecNorm z := by
      have := vecNorm_mulVec_le Mᴴ z; rwa [Matrix.l2_opNorm_conjTranspose] at this
    have h0 := vecNorm_nonneg (Qᴴ *ᵥ (Mᴴ *ᵥ z))
    have hm0 := vecNorm_nonneg (Mᴴ *ᵥ z)
    have hS := sqrt_frob_mul_self Q
    have hS0 := Real.sqrt_nonneg (frob Q)
    rcases min_choice (a ^ 2) (frob Q) with hc | hc <;> rw [hc]
    · have := mul_le_mul_of_nonneg_left hM ha0
      nlinarith
    · have := mul_le_mul_of_nonneg_left hM hS0
      nlinarith
  have hm0 : 0 ≤ min (a ^ 2) (frob Q) := le_min (by positivity) (frob_nonneg Q)
  have hx := hv x; have hy := hv y
  have hx0 := vecNorm_nonneg x; have hy0 := vecNorm_nonneg y
  have hn := norm_nonneg M
  rw [e]
  refine (norm_star_dotProduct_le _ _).trans ?_
  set m := min (a ^ 2) (frob Q)
  have hxs : vecNorm ((M * Q)ᴴ *ᵥ x) ≤ Real.sqrt m * (‖M‖ * vecNorm x) := by
    rw [← Real.sqrt_sq (vecNorm_nonneg _), ← Real.sqrt_sq (by positivity : 0 ≤ ‖M‖ * vecNorm x),
      ← Real.sqrt_mul hm0]
    exact Real.sqrt_le_sqrt hx
  have hys : vecNorm ((M * Q)ᴴ *ᵥ y) ≤ Real.sqrt m * (‖M‖ * vecNorm y) := by
    rw [← Real.sqrt_sq (vecNorm_nonneg _), ← Real.sqrt_sq (by positivity : 0 ≤ ‖M‖ * vecNorm y),
      ← Real.sqrt_mul hm0]
    exact Real.sqrt_le_sqrt hy
  have hsm := Real.mul_self_sqrt hm0
  have hs0 := Real.sqrt_nonneg m
  calc vecNorm ((M * Q)ᴴ *ᵥ x) * vecNorm ((M * Q)ᴴ *ᵥ y)
      ≤ (Real.sqrt m * (‖M‖ * vecNorm x)) * (Real.sqrt m * (‖M‖ * vecNorm y)) :=
        mul_le_mul hxs hys (vecNorm_nonneg _) (by positivity)
    _ = (Real.sqrt m * Real.sqrt m) * ‖M‖ ^ 2 * vecNorm x * vecNorm y := by ring
    _ = m * ‖M‖ ^ 2 * vecNorm x * vecNorm y := by rw [hsm]

/-- `‖QQ*M*x‖ ≤ a√S‖M‖‖x‖` and `≤ S‖M‖‖x‖`. -/
theorem vecNorm_wVec_le (M Q : Matrix (Fin W) (Fin W) ℂ) {a : ℝ} (ha0 : 0 ≤ a) (ha : ‖Q‖ ≤ a)
    (x : Fin W → ℂ) :
    vecNorm (wVec M Q x) ≤ a * Real.sqrt (frob Q) * (‖M‖ * vecNorm x) ∧
      vecNorm (wVec M Q x) ≤ frob Q * (‖M‖ * vecNorm x) := by
  have e : wVec M Q x = Q *ᵥ (Qᴴ *ᵥ (Mᴴ *ᵥ x)) := by
    simp only [wVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hM : vecNorm (Mᴴ *ᵥ x) ≤ ‖M‖ * vecNorm x := by
    have := vecNorm_mulVec_le Mᴴ x; rwa [Matrix.l2_opNorm_conjTranspose] at this
  obtain ⟨h1, h2⟩ := vecNorm_conjQ_le Q ha (Mᴴ *ᵥ x)
  obtain ⟨g1, g2⟩ := vecNorm_Q_le Q ha (Qᴴ *ᵥ (Mᴴ *ᵥ x))
  have hS0 := Real.sqrt_nonneg (frob Q)
  have hS := sqrt_frob_mul_self Q
  rw [e]
  constructor
  · calc vecNorm (Q *ᵥ (Qᴴ *ᵥ (Mᴴ *ᵥ x))) ≤ a * vecNorm (Qᴴ *ᵥ (Mᴴ *ᵥ x)) := g1
      _ ≤ a * (Real.sqrt (frob Q) * vecNorm (Mᴴ *ᵥ x)) := mul_le_mul_of_nonneg_left h2 ha0
      _ ≤ a * (Real.sqrt (frob Q) * (‖M‖ * vecNorm x)) := by gcongr
      _ = _ := by ring
  · calc vecNorm (Q *ᵥ (Qᴴ *ᵥ (Mᴴ *ᵥ x))) ≤ Real.sqrt (frob Q) * vecNorm (Qᴴ *ᵥ (Mᴴ *ᵥ x)) := g2
      _ ≤ Real.sqrt (frob Q) * (Real.sqrt (frob Q) * vecNorm (Mᴴ *ᵥ x)) :=
          mul_le_mul_of_nonneg_left h2 hS0
      _ ≤ Real.sqrt (frob Q) * (Real.sqrt (frob Q) * (‖M‖ * vecNorm x)) := by gcongr
      _ = (Real.sqrt (frob Q) * Real.sqrt (frob Q)) * (‖M‖ * vecNorm x) := by ring
      _ = _ := by rw [hS]

/-- `‖ℝ₁₂‖ ≤ η⁻¹`. -/
theorem norm_farQ_le (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) : ‖farQ b E XX‖ ≤ (etaZ b E)⁻¹ :=
  (BlockBand.SourceProcess.FullSource.norm_portBlock_le _ 0 1).trans
    (BlockBand.SourceProcess.FullSource.norm_twoPortResolvent_le b E hXX hη)

end BlockBand.SourceProcess.ProjSeparator
