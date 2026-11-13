module

public import BlockBand.Transmission.PassiveCovariance.MainTerm
public import BlockBand.Transmission.PassiveCovariance.Step5
public import BlockBand.Transmission.PassiveCovariance.PhysVec

/-!
# The leading values of the Level-0 means and their exact sum

The Level-0 sources `srcX1`, `srcX2` of `LevelZeroMatch` are sums of products of means of
dressed forms with the block weights `s_{0p}` (`= sRow b p / W`). The leading value of every such
mean is an explicit matrix in `R`, `R*`, `R*R`, `I` with jet
scalars as coefficients:

* `leadA p` (`A₀ = 1/D₋`, `A₁ = ba²/D₋`, `D₋ = 1 + k₋s`), `leadB p` (`1/b`, `1`);
* `leadSv p`, `leadSw p`, `leadSz p` (the weights `σ₁` of the trace means `v_p`, `w_p`, `z_p`);
* `leadM2 p = A_pR + σw_p`, `leadM4 p = B_pR*R + σ̄v_pR* + σv_pR + σz_p`, `leadM5 p = A_pR`,
  `leadM6 p = B_pR*R + σv_pR` (the means `m2, m4, m5, m6`; `g0 ↦ R`, `g1 ↦ I`, `τ̄ ↦ 1`).

Main results (every `s` with `1 + k₋s ≠ 0`, in particular every stationary jet):

* `sum_leadA`, `sum_leadB`, `sum_leadSv`, `sum_leadSw`, `sum_leadSz`: the five weight identities
  `Σ_p w_pA_p = σ₋`, `Σ w_pB_p = σ₊`, `Σ w_pσv_p = Σ w_pσw_p = -r`, `Σ w_pσz_p = r₁₂`
  (`w = (c, b)`; through `ladderRStep_eq`, `ladderR12Step_eq`).
* **`lead_eq_main`**: `conj X₂^lead + X₁^lead = mainTensor` exactly, for every `X` and all vectors
  (through `mainTensor_eq_ladderTensor`; no commutation of `R`, `R*` in the external forms).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexConjugate

variable {W : ℕ}

/-- `D₋ = 1 + k₋s`. -/
def leadDen (b E : ℝ) (s : ℂ) : ℂ := 1 + kMinus b E * s

/-- `A_p = [p=0] + σ₁(u_p)`: `(1/D₋, ba²/D₋)`. -/
def leadA (b E : ℝ) (s : ℂ) (p : Fin 2) : ℂ :=
  ![1 / leadDen b E s, (b : ℂ) * matchedA E ^ 2 / leadDen b E s] p

/-- `B_p = [p=0] + σ₁(r_p)`: `(1/b, 1)`. -/
def leadB (b : ℝ) (p : Fin 2) : ℂ := ((![1 / b, 1] p : ℝ) : ℂ)

/-- `[p = 1]`. -/
def leadInd (p : Fin 2) : ℂ := ![0, 1] p

/-- `r_{p1} = ⟨(𝒢ᴴP_p𝒢)₁₁⟩`: `(d_*/b, d_*)`. -/
def leadR1 (b : ℝ) (p : Fin 2) : ℂ := ((![dStar b / b, dStar b] p : ℝ) : ℂ)

/-- `u_{p1} = ⟨(𝒢P_p𝒢)₁₁⟩`: `(-s/D₋, -sba²/D₋)`. -/
def leadU1 (b E : ℝ) (s : ℂ) (p : Fin 2) : ℂ :=
  ![-s / leadDen b E s, -s * b * matchedA E ^ 2 / leadDen b E s] p

/-- `σv_p = σ₁(E𝒢Π𝒢ᴴP_p𝒢)`. -/
def leadSv (b E : ℝ) (s : ℂ) (p : Fin 2) : ℂ :=
  (kMinus b E * leadB b p * jetB b E s +
    (b : ℂ) * matchedA E * dStar b * (leadInd p + b * leadR1 b p)) / leadDen b E s

/-- `σw_p = σ₁(E𝒢P_p𝒢Π𝒢ᴴ)`. -/
def leadSw (b E : ℝ) (s : ℂ) (p : Fin 2) : ℂ :=
  (sigmaPlus b : ℂ) * leadA b E s p * jetB b E s +
    matchedA E * dStar b * (leadInd p + b * leadU1 b E s p)

/-- `v_{p1} = ⟨(𝒢Π𝒢ᴴP_p𝒢)₁₁⟩ = B_pB_* - sσv_p`. -/
def leadV1 (b E : ℝ) (s : ℂ) (p : Fin 2) : ℂ := leadB b p * jetB b E s - s * leadSv b E s p

/-- `σz_p = σ₁(E𝒢Π𝒢ᴴP_p𝒢Π𝒢ᴴ)` (real). -/
def leadSz (b E : ℝ) (s : ℂ) (p : Fin 2) : ℂ :=
  (sigmaPlus b : ℂ) * (leadB b p * jetC b E s + leadSv b E s p * jetB b E s +
      conj (leadSv b E s p) * conj (jetB b E s)) +
    (dStar b : ℂ) ^ 2 * (leadInd p + b * leadR1 b p) +
    (b : ℂ) * dStar b * (matchedA E * leadV1 b E s p + conj (matchedA E * leadV1 b E s p))

section Matrices

variable (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (p : Fin 2)

/-- Leading value of `m2_p = E[K̂𝒢P_p𝒢Π(K̂𝒢)ᴴ]₁₁`. -/
def leadM2 : Matrix (Fin W) (Fin W) ℂ :=
  leadA b E s p • passiveResolvent b E X + leadSw b E s p • 1

/-- Leading value of `m4_p = E[K̂𝒢Π𝒢ᴴP_p𝒢Π(K̂𝒢)ᴴ]₁₁`. -/
def leadM4 : Matrix (Fin W) (Fin W) ℂ :=
  leadB b p • ((passiveResolvent b E X)ᴴ * passiveResolvent b E X) +
    conj (leadSv b E s p) • (passiveResolvent b E X)ᴴ + leadSv b E s p • passiveResolvent b E X +
    leadSz b E s p • 1

/-- Leading value of `m5_p = E[K̂𝒢P_p𝒢]₁₁`. -/
def leadM5 : Matrix (Fin W) (Fin W) ℂ := leadA b E s p • passiveResolvent b E X

/-- Leading value of `m6_p = E[K̂𝒢Π𝒢ᴴP_p𝒢]₁₁`. -/
def leadM6 : Matrix (Fin W) (Fin W) ℂ :=
  leadB b p • ((passiveResolvent b E X)ᴴ * passiveResolvent b E X) +
    leadSv b E s p • passiveResolvent b E X

end Matrices

/-- Leading value of `X₁`. -/
def leadX1 (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (v₁ v₂ v₃ v₄ : Fin W → ℂ) : ℂ :=
  ∑ p : Fin 2, sRow b p / W *
    (bilinear v₁ (passiveResolvent b E X) v₄ * bilinear v₃ (leadM2 b E s X p) v₂ +
      bilinear v₁ 1 v₄ * bilinear v₃ (leadM4 b E s X p) v₂)

/-- Leading value of `X₂`. -/
def leadX2 (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (v₁ v₂ v₃ v₄ : Fin W → ℂ) : ℂ :=
  ∑ p : Fin 2, sRow b p / W *
    (bilinear v₂ (passiveResolvent b E X) v₃ * bilinear v₄ (leadM5 b E s X p) v₁ +
      bilinear v₂ 1 v₃ * bilinear v₄ (leadM6 b E s X p) v₁)

section Identities

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) {s : ℂ}
  (hu : 1 + kMinus b E * s ≠ 0)

theorem sRow_zero (b : ℝ) : sRow b 0 = 1 - 2 * (b : ℂ) := by simp [sRow]

theorem sRow_one (b : ℝ) : sRow b 1 = (b : ℂ) := by simp [sRow]

theorem conj_sRow (b : ℝ) (p : Fin 2) : conj (sRow b p) = sRow b p := by
  unfold sRow; split_ifs <;> exact Complex.conj_ofReal _

theorem conj_leadB (b : ℝ) (p : Fin 2) : conj (leadB b p) = leadB b p := by
  simp [leadB]

include hb0 hb in
theorem dStar_mul_one_sub : (dStar b : ℂ) * (1 - b) = 1 := by
  have : (1 - b : ℝ) ≠ 0 := by linarith
  have h : (1 - (b : ℂ)) ≠ 0 := by exact_mod_cast this
  rw [dStar_cast, one_div, inv_mul_cancel₀ h]

include hu in
theorem sum_leadA : ∑ p : Fin 2, sRow b p * leadA b E s p = sigmaMinus b E s := by
  have hD : leadDen b E s ≠ 0 := hu
  rw [show sigmaMinus b E s = kMinus b E / leadDen b E s from rfl, Fin.sum_univ_two, sRow_zero,
    sRow_one, kMinus_cast]
  simp only [leadA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp

include hb0 in
theorem sum_leadB : ∑ p : Fin 2, sRow b p * leadB b p = sigmaPlus b := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  rw [Fin.sum_univ_two, sRow_zero, sRow_one, sigmaPlus_cast]
  simp only [leadB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  field_simp

include hb0 hb in
/-- `Σ_p w_p([p=1] + b r_p) = cd_* + b + b²d_* = 1`. -/
theorem sum_leadR : ∑ p : Fin 2, sRow b p * (leadInd p + b * leadR1 b p) = 1 := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hd := dStar_mul_one_sub hb0 hb
  rw [Fin.sum_univ_two, sRow_zero, sRow_one]
  simp only [leadInd, leadR1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  field_simp
  linear_combination (1 - (b : ℂ)) * hd

include hb0 hb hu in
theorem sum_leadSv : ∑ p : Fin 2, sRow b p * leadSv b E s p = -ladderRStep b E s := by
  have hR := sum_leadR hb0 hb
  have hB := sum_leadB hb0
  have e : ∑ p : Fin 2, sRow b p * leadSv b E s p =
      (kMinus b E * (∑ p : Fin 2, sRow b p * leadB b p) * jetB b E s + (b : ℂ) * matchedA E *
        dStar b * ∑ p : Fin 2, sRow b p * (leadInd p + b * leadR1 b p)) / leadDen b E s := by
    simp only [leadSv, Fin.sum_univ_two]
    field_simp
    ring
  rw [e, hR, hB, ladderRStep, ladderEll]
  rw [leadDen]
  field_simp
  ring

include hu in
theorem sum_leadSw : ∑ p : Fin 2, sRow b p * leadSw b E s p = -ladderRStep b E s := by
  have hA := sum_leadA hu
  have e : ∑ p : Fin 2, sRow b p * leadSw b E s p =
      (sigmaPlus b : ℂ) * (∑ p : Fin 2, sRow b p * leadA b E s p) * jetB b E s +
        matchedA E * dStar b * ∑ p : Fin 2, sRow b p * (leadInd p + b * leadU1 b E s p) := by
    simp only [leadSw, Fin.sum_univ_two]
    ring
  have hU : ∑ p : Fin 2, sRow b p * (leadInd p + b * leadU1 b E s p) = (b : ℂ) / leadDen b E s := by
    have hD : leadDen b E s ≠ 0 := hu
    have hDe : leadDen b E s = 1 + ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * matchedA E ^ 2) * s := by
      rw [leadDen, kMinus_cast]
    rw [Fin.sum_univ_two, sRow_zero, sRow_one]
    simp only [leadInd, leadU1, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp
    linear_combination (b : ℂ) * hDe
  rw [e, hA, hU, ladderRStep, ladderEll, sigmaMinus]
  rw [leadDen]
  field_simp
  ring

include hb0 hb hu in
/-- `Σ_p w_p v_{p1} = σ₊B_* + sr = -ℓ_*`. -/
theorem sum_leadV1 : ∑ p : Fin 2, sRow b p * leadV1 b E s p = -ladderEll b E s := by
  have hV := sum_leadSv hb0 hb hu
  have hB := sum_leadB hb0
  have e : ∑ p : Fin 2, sRow b p * leadV1 b E s p =
      (∑ p : Fin 2, sRow b p * leadB b p) * jetB b E s -
        s * ∑ p : Fin 2, sRow b p * leadSv b E s p := by
    simp only [leadV1, Fin.sum_univ_two]
    ring
  rw [e, hV, hB, ladderRStep, ladderEll]
  have hinv := mul_inv_cancel₀ hu
  rw [div_eq_mul_inv]
  linear_combination (-((sigmaPlus b : ℂ) * jetB b E s - s * b * dStar b * matchedA E)) * hinv

theorem sum_conj (f : Fin 2 → ℂ) :
    ∑ p : Fin 2, sRow b p * conj (f p) = conj (∑ p : Fin 2, sRow b p * f p) := by
  simp only [map_sum, map_mul, conj_sRow]

include hb0 hb hu in
theorem sum_leadSz : ∑ p : Fin 2, sRow b p * leadSz b E s p = ladderR12Step b E s := by
  have hV := sum_leadSv hb0 hb hu
  have hB := sum_leadB hb0
  have hR := sum_leadR hb0 hb
  have hV1 := sum_leadV1 hb0 hb hu
  have hd := dStar_mul_one_sub hb0 hb
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have e : ∑ p : Fin 2, sRow b p * leadSz b E s p =
      (sigmaPlus b : ℂ) * ((∑ p : Fin 2, sRow b p * leadB b p) * jetC b E s +
        (∑ p : Fin 2, sRow b p * leadSv b E s p) * jetB b E s +
        conj (∑ p : Fin 2, sRow b p * leadSv b E s p) * conj (jetB b E s)) +
      (dStar b : ℂ) ^ 2 * (∑ p : Fin 2, sRow b p * (leadInd p + b * leadR1 b p)) +
      (b : ℂ) * dStar b * (matchedA E * (∑ p : Fin 2, sRow b p * leadV1 b E s p) +
        conj (matchedA E * ∑ p : Fin 2, sRow b p * leadV1 b E s p)) := by
    rw [map_mul (starRingEnd ℂ) (matchedA E), ← sum_conj, ← sum_conj]
    simp only [leadSz, Fin.sum_univ_two, map_mul]
    ring
  rw [e, hV, hB, hR, hV1, ladderR12Step, ladderEll12, ladderC0, sigmaPlus_cast, kPlus]
  simp only [map_neg, map_mul]
  push_cast
  field_simp
  linear_combination (-(b : ℂ) ^ 2 * ((dStar b : ℂ) ^ 2 - b * dStar b * (matchedA E * ladderEll b E s +
    conj (matchedA E) * conj (ladderEll b E s))) * (1 - b)) * hd

end Identities

section Sum

theorem conj_bilinear {n : Type*} [Fintype n] (u : n → ℂ) (A : Matrix n n ℂ) (v : n → ℂ) :
    conj (bilinear u A v) = bilinear v Aᴴ u := conj_form u v A

variable (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (v₁ v₂ v₃ v₄ : Fin W → ℂ)

theorem conj_leadX2 : conj (leadX2 b E s X v₁ v₂ v₃ v₄) =
    ∑ p : Fin 2, sRow b p / W *
      (conj (leadA b E s p) * (bilinear v₃ (passiveResolvent b E X)ᴴ v₂ *
          bilinear v₁ (passiveResolvent b E X)ᴴ v₄) +
        bilinear v₃ 1 v₂ * (leadB b p * bilinear v₁ ((passiveResolvent b E X)ᴴ *
          passiveResolvent b E X) v₄ +
          conj (leadSv b E s p) * bilinear v₁ (passiveResolvent b E X)ᴴ v₄)) := by
  rw [leadX2, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [leadM5, leadM6, bilinear_add, bilinear_smul, map_mul, map_add, map_div₀, conj_sRow,
    Complex.conj_natCast, conj_bilinear, conj_leadB, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_one]
  ring

theorem leadX1_eq : leadX1 b E s X v₁ v₂ v₃ v₄ =
    ∑ p : Fin 2, sRow b p / W *
      (bilinear v₁ (passiveResolvent b E X) v₄ * (leadA b E s p * bilinear v₃ (passiveResolvent b E X) v₂ +
          leadSw b E s p * bilinear v₃ 1 v₂) +
        bilinear v₁ 1 v₄ * (leadB b p * bilinear v₃ ((passiveResolvent b E X)ᴴ *
          passiveResolvent b E X) v₂ + conj (leadSv b E s p) * bilinear v₃ (passiveResolvent b E X)ᴴ v₂ +
          leadSv b E s p * bilinear v₃ (passiveResolvent b E X) v₂ + leadSz b E s p * bilinear v₃ 1 v₂)) := by
  rw [leadX1]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [leadM2, leadM4, bilinear_add, bilinear_smul]

end Sum

/-- **The leading values sum exactly to the leading tensor**: `conj X₂^lead + X₁^lead = mainTensor`,
for every `X`, all vectors, `W ≠ 0`, and every `s` with `1 + k₋s ≠ 0`. -/
theorem lead_eq_main {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) {s : ℂ}
    (hu : 1 + kMinus b E * s ≠ 0) (hW : W ≠ 0) (X : Matrix (Fin W) (Fin W) ℂ)
    (v₁ v₂ v₃ v₄ : Fin W → ℂ) :
    conj (leadX2 b E s X v₁ v₂ v₃ v₄) + leadX1 b E s X v₁ v₂ v₃ v₄ = mainTensor b E s X v₁ v₂ v₃ v₄ := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hM := mainTensor_eq_ladderTensor h1 h2 hb0 (by linarith) hW s X v₁ v₂ v₃ v₄
  have hA := sum_leadA hu
  have hAc : ∑ p : Fin 2, sRow b p * conj (leadA b E s p) = conj (sigmaMinus b E s) := by
    rw [sum_conj, hA]
  have hB := sum_leadB hb0
  have hV := sum_leadSv hb0 hb hu
  have hVc : ∑ p : Fin 2, sRow b p * conj (leadSv b E s p) = -conj (ladderRStep b E s) := by
    rw [sum_conj, hV, map_neg]
  have hS := sum_leadSw hu
  have hZ := sum_leadSz hb0 hb hu
  rw [ladderRStep_eq hb0 hb h1 h2 s hu] at hV hVc hS
  rw [ladderR12Step_eq hb0 hb h1 h2 s hu] at hZ
  rw [Fin.sum_univ_two] at hA hAc hB hV hVc hS hZ
  apply mul_left_cancel₀ hW'
  rw [hM, conj_leadX2, leadX1_eq, ladderTensor]
  simp only [Fin.sum_univ_two, crossedTensor]
  field_simp
  set R := passiveResolvent b E X
  linear_combination
    (bilinear v₁ R v₄ * bilinear v₃ R v₂) * hA + (bilinear v₁ Rᴴ v₄ * bilinear v₃ Rᴴ v₂) * hAc +
    (bilinear v₁ 1 v₄ * bilinear v₃ (Rᴴ * R) v₂ + bilinear v₁ (Rᴴ * R) v₄ * bilinear v₃ 1 v₂) * hB +
    (bilinear v₁ 1 v₄ * bilinear v₃ R v₂) * hV + (bilinear v₁ R v₄ * bilinear v₃ 1 v₂) * hS +
    (bilinear v₁ 1 v₄ * bilinear v₃ Rᴴ v₂ + bilinear v₁ Rᴴ v₄ * bilinear v₃ 1 v₂) * hVc +
    (bilinear v₁ 1 v₄ * bilinear v₃ 1 v₂) * hZ

end BlockBand.Transmission.PassiveCovariance
