module

public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# The two-dimensional mode blocks of the canonical frame

For `0 ≤ t ≤ 1` the columns `t^{1/4} e_±(t)` of `initialFrame` satisfy
`P_i + t^{1/2}(e_+ e_+ᵀ − e_- e_-ᵀ) = u uᵀ` with `u = (√(1−t), √t)` (`mode_identity`), the
rank-one projection `P_i'` onto `u`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open BlockBand.Internal.Contracts.TransmissionLaws

/-- Real entries of `modeVector`. -/
def ev (t : ℝ) (σ a : Fin 2) : ℝ :=
  if σ = 0 then (if a = 0 then Real.sqrt (1 - Real.sqrt t) / Real.sqrt 2 else
      Real.sqrt (1 + Real.sqrt t) / Real.sqrt 2)
  else (if a = 0 then Real.sqrt (1 + Real.sqrt t) / Real.sqrt 2 else
      -(Real.sqrt (1 - Real.sqrt t) / Real.sqrt 2))

theorem modeVector_eq (t : ℝ) (σ a : Fin 2) : modeVector t σ a = (ev t σ a : ℂ) := by
  fin_cases σ <;> fin_cases a <;> simp [modeVector, ev]

/-- The unit vector `u = (√(1−t), √t)`. -/
def uv (t : ℝ) (a : Fin 2) : ℝ := if a = 0 then Real.sqrt (1 - t) else Real.sqrt t

/-- The sign of the current column `σ`. -/
def sgn (σ : Fin 2) : ℝ := if σ = 0 then 1 else -1

theorem mode_identity {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (a b : Fin 2) :
    Real.sqrt t * (∑ σ, sgn σ * ev t σ a * ev t σ b) + (if a = 0 ∧ b = 0 then 1 else 0) =
      uv t a * uv t b := by
  have hs0 := Real.sqrt_nonneg t
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 h1
  have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt h0
  have ha : Real.sqrt (1 - Real.sqrt t) * Real.sqrt (1 - Real.sqrt t) = 1 - Real.sqrt t :=
    Real.mul_self_sqrt (by linarith)
  have hb : Real.sqrt (1 + Real.sqrt t) * Real.sqrt (1 + Real.sqrt t) = 1 + Real.sqrt t :=
    Real.mul_self_sqrt (by linarith)
  have hab : Real.sqrt (1 - Real.sqrt t) * Real.sqrt (1 + Real.sqrt t) = Real.sqrt (1 - t) := by
    rw [← Real.sqrt_mul (by linarith)]
    congr 1
    nlinarith
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : 0 < Real.sqrt 2 := by positivity
  have hu0 : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t := Real.mul_self_sqrt (by linarith)
  have h2s : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hab3 : Real.sqrt t * Real.sqrt (1 - Real.sqrt t) * Real.sqrt (1 + Real.sqrt t) =
      Real.sqrt t * Real.sqrt (1 - t) := by rw [mul_assoc, hab]
  have hba3 : Real.sqrt t * Real.sqrt (1 + Real.sqrt t) * Real.sqrt (1 - Real.sqrt t) =
      Real.sqrt t * Real.sqrt (1 - t) := by rw [mul_assoc, mul_comm (Real.sqrt (1 + _)), hab]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.sum_univ_two, sgn, ev, uv, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      ↓reduceIte, one_ne_zero, and_self, and_false, false_and] <;>
    field_simp <;> (try simp only [h2s]) <;> nlinarith [hab, ha, hb, hst, h2, hu0, h2s, hab3, hba3]

theorem uv_sq_sum {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∑ a, uv t a * uv t a = 1 := by
  simp only [Fin.sum_univ_two, uv, Fin.isValue, ↓reduceIte, one_ne_zero]
  rw [Real.mul_self_sqrt (by linarith), Real.mul_self_sqrt h0]
  ring

theorem rpow_quarter_mul {t : ℝ} (h0 : 0 ≤ t) :
    t ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) = Real.sqrt t := by
  rw [← Real.rpow_add' h0 (by norm_num), Real.sqrt_eq_rpow]
  norm_num

end BlockBand.SourceProcess.ModelExist
