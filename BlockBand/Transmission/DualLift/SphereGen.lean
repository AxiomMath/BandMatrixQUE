module

public import BlockBand.Transmission.DualLift.Push

/-!
# Invariance of `liftM`, deterministic part: the defect of the invariant manifold

With `u = |v|² − 1` and `Ψ = s S̃ − 1` (so `liftDefect = u² + Ψ²`), the lifted generator gives
* `𝓛̃u = u · D₀(|v|² − 3 − s v₃)`, `Γ_a u = −2√D₀ v_k u` (`genAt_u`): the sphere part, valid
  because neither `σ_v` nor `−D₀v` is cut off;
* `𝓛̃Ψ = Ψ · D₀(s²Q − s(1+x−y)) − (D₀/4) s² v₃² u`, `Γ_a Ψ = −s Ψ m_a` (`genAt_psi`), where
  `m_a = Γ_a S̃`;
* hence `𝓛̃(liftDefect) ≤ defectRate D₀ ξ · liftDefect ξ` everywhere, with `defectRate`
  continuous (`sdeGenerator_liftDefect_le`, `continuous_defectRate`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open Real
open BlockBand.SourceProcess.Stochastic

variable {D0 : ℝ}

/-- `u = |v|² − 1`. -/
def uD (ξ : Fin 6 → ℝ) : ℝ := vSq ξ - 1

/-- `Ψ = s S̃ − 1`. -/
def psiD (ξ : Fin 6 → ℝ) : ℝ := ξ 5 * lS ξ - 1

/-- Noise derivatives of `u`. -/
def gu (D0 : ℝ) (ξ : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![0, 0, -2 * √D0 * ξ 2 * uD ξ, -2 * √D0 * ξ 3 * uD ξ, -2 * √D0 * ξ 4 * uD ξ]

/-- Noise derivatives of `S̃`. -/
def gS (D0 : ℝ) (ξ : Fin 6 → ℝ) : Fin 5 → ℝ := fun a => gx D0 ξ a + gy D0 ξ a

theorem genAt_u (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) :
    GenAt (liftDrift D0) (liftSigma D0) uD ξ
      (uD ξ * (D0 * (vSq ξ - 3 - ξ 5 * ξ 4))) (gu D0 ξ) := by
  have h := (((GenAt.coord (b := liftDrift D0) (σ := liftSigma D0) (y := ξ) 2).sq.add
    (GenAt.coord (b := liftDrift D0) (σ := liftSigma D0) (y := ξ) 3).sq).add
    (GenAt.coord (b := liftDrift D0) (σ := liftSigma D0) (y := ξ) 4).sq).sub
    (GenAt.const (b := liftDrift D0) (σ := liftSigma D0) (y := ξ) 1)
  have hD := Real.mul_self_sqrt hD0
  refine (h.congr_fun rfl).congr ?_ fun a => ?_
  · simp only [Fin.sum_univ_five, liftDrift, liftSigma, Matrix.cons_val, Fin.isValue]
    unfold uD vSq
    linear_combination (ξ 2 ^ 4 + ξ 3 ^ 4 + ξ 4 ^ 4 + 2 * (ξ 2 * ξ 3) ^ 2 + 2 * (ξ 2 * ξ 4) ^ 2 +
      2 * (ξ 3 * ξ 4) ^ 2 - 2 * (ξ 2 * ξ 2 + ξ 3 * ξ 3 + ξ 4 * ξ 4) + 3) * hD
  · fin_cases a <;> simp [gu, liftSigma, uD, vSq] <;> ring

theorem genAt_lS (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) :
    GenAt (liftDrift D0) (liftSigma D0) lS ξ
      (D0 * (1 + lx ξ - ly ξ) - D0 * lQ ξ * ξ 5) (gS D0 ξ) :=
  (((genAt_lx hD0 ξ).add (genAt_ly ξ)).congr_fun rfl).congr (by unfold lQ; ring) fun _ => rfl

theorem gS_sq (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) :
    ∑ a, gS D0 ξ a * gS D0 ξ a = D0 * lQ ξ + D0 / 4 * (ξ 4 * ξ 4) * uD ξ := by
  have hr := rho_sq hD0 ξ
  have hD := Real.mul_self_sqrt hD0
  simp only [Fin.sum_univ_five, gS, gx, gy, Matrix.cons_val, Fin.isValue]
  unfold lQ lx ly uD vSq at *
  linear_combination (ξ 0 * ξ 0 + ξ 1 * ξ 1) * hr + ((ξ 4 * ξ 4 * (ξ 2 * ξ 2 + ξ 3 * ξ 3) +
    (1 - ξ 4 * ξ 4) * (1 - ξ 4 * ξ 4)) / 4) * hD

theorem sigma5_eq (ξ : Fin 6 → ℝ) (a : Fin 5) :
    liftSigma D0 a ξ 5 = -(ξ 5 * ξ 5) * gS D0 ξ a := by
  fin_cases a <;> simp [liftSigma, gS, gx, gy] <;> ring

theorem genAt_psi (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) :
    GenAt (liftDrift D0) (liftSigma D0) psiD ξ
      (psiD ξ * (D0 * (ξ 5 * ξ 5 * lQ ξ - ξ 5 * (1 + lx ξ - ly ξ))) -
        D0 / 4 * (ξ 5 * ξ 5) * (ξ 4 * ξ 4) * uD ξ)
      (fun a => -(ξ 5 * psiD ξ * gS D0 ξ a)) := by
  have h := ((GenAt.coord (b := liftDrift D0) (σ := liftSigma D0) (y := ξ) 5).mul
    (genAt_lS hD0 ξ)).sub (GenAt.const (b := liftDrift D0) (σ := liftSigma D0) (y := ξ) 1)
  refine (h.congr_fun rfl).congr ?_ fun a => ?_
  · have hsum : ∑ a, liftSigma D0 a ξ 5 * gS D0 ξ a =
        -(ξ 5 * ξ 5) * ∑ a, gS D0 ξ a * gS D0 ξ a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by rw [sigma5_eq]; ring
    rw [hsum, gS_sq hD0]
    simp only [liftDrift, Matrix.cons_val, Fin.isValue]
    unfold psiD
    have hQ : lQ ξ = lS ξ * (1 + lx ξ - ly ξ) := by unfold lQ lS; ring
    linear_combination (-(D0 * (ξ 5 * ξ 5))) * hQ
  · rw [sigma5_eq]; unfold psiD; ring

/-!
## The defect
-/

/-- The rate in `𝓛̃(liftDefect) ≤ rate · liftDefect`. -/
def defectRate (D0 : ℝ) (ξ : Fin 6 → ℝ) : ℝ :=
  |2 * (D0 * (vSq ξ - 3 - ξ 5 * ξ 4)) + 4 * D0 * vSq ξ| +
    |2 * (D0 * (ξ 5 * ξ 5 * lQ ξ - ξ 5 * (1 + lx ξ - ly ξ))) +
      ξ 5 * ξ 5 * (D0 * lQ ξ + D0 / 4 * (ξ 4 * ξ 4) * uD ξ)| +
    |D0 / 4 * (ξ 5 * ξ 5) * (ξ 4 * ξ 4)|

theorem continuous_defectRate (D0 : ℝ) : Continuous (defectRate D0) := by
  unfold defectRate vSq lQ lx ly uD vSq; fun_prop

theorem defectRate_nonneg (D0 : ℝ) (ξ : Fin 6 → ℝ) : 0 ≤ defectRate D0 ξ := by
  unfold defectRate; positivity

theorem liftDefect_eq (ξ : Fin 6 → ℝ) : liftDefect ξ = uD ξ * uD ξ + psiD ξ * psiD ξ := rfl

theorem gu_sq (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) :
    ∑ a, gu D0 ξ a * gu D0 ξ a = 4 * D0 * vSq ξ * (uD ξ * uD ξ) := by
  have hD := Real.mul_self_sqrt hD0
  simp only [Fin.sum_univ_five, gu, Matrix.cons_val, Fin.isValue]
  unfold vSq
  linear_combination (4 * (ξ 2 * ξ 2 + ξ 3 * ξ 3 + ξ 4 * ξ 4) * (uD ξ * uD ξ)) * hD

/-- **The defect generator bound.** -/
theorem sdeGenerator_liftDefect_le (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) :
    sdeGenerator (liftDrift D0) (liftSigma D0) liftDefect ξ ≤ defectRate D0 ξ * liftDefect ξ := by
  have H := ((genAt_u hD0 ξ).sq.add (genAt_psi hD0 ξ).sq)
  rw [show liftDefect = fun q => uD q * uD q + psiD q * psiD q from rfl, H.gen]
  have e2 : ∑ a, -(ξ 5 * psiD ξ * gS D0 ξ a) * -(ξ 5 * psiD ξ * gS D0 ξ a) =
      ξ 5 * ξ 5 * (psiD ξ * psiD ξ) * ∑ a, gS D0 ξ a * gS D0 ξ a := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  rw [gu_sq hD0, e2, gS_sq hD0]
  beta_reduce
  set u := uD ξ
  set p := psiD ξ
  set A := 2 * (D0 * (vSq ξ - 3 - ξ 5 * ξ 4)) + 4 * D0 * vSq ξ
  set B := 2 * (D0 * (ξ 5 * ξ 5 * lQ ξ - ξ 5 * (1 + lx ξ - ly ξ))) +
      ξ 5 * ξ 5 * (D0 * lQ ξ + D0 / 4 * (ξ 4 * ξ 4) * u)
  set c := D0 / 4 * (ξ 5 * ξ 5) * (ξ 4 * ξ 4)
  have hrate : defectRate D0 ξ = |A| + |B| + |c| := rfl
  have key : 2 * u * (u * (D0 * (vSq ξ - 3 - ξ 5 * ξ 4))) + 4 * D0 * vSq ξ * (u * u) +
      (2 * p * (p * (D0 * (ξ 5 * ξ 5 * lQ ξ - ξ 5 * (1 + lx ξ - ly ξ))) - c * u) +
        ξ 5 * ξ 5 * (p * p) * (D0 * lQ ξ + D0 / 4 * (ξ 4 * ξ 4) * u)) =
      A * (u * u) + B * (p * p) - 2 * c * (u * p) := by ring
  rw [key, hrate]
  have h1 : A * (u * u) ≤ |A| * (u * u) := mul_le_mul_of_nonneg_right (le_abs_self A)
    (mul_self_nonneg u)
  have h2 : B * (p * p) ≤ |B| * (p * p) := mul_le_mul_of_nonneg_right (le_abs_self B)
    (mul_self_nonneg p)
  have h3 : -(2 * c * (u * p)) ≤ |c| * (u * u + p * p) := by
    have := abs_nonneg c
    have h4 : -(c * (2 * (u * p))) ≤ |c| * |2 * (u * p)| := by
      rw [← abs_mul]; exact neg_le_abs _
    have h5 : |2 * (u * p)| ≤ u * u + p * p := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u + p), sq_nonneg (u - p)]
    nlinarith [mul_le_mul_of_nonneg_left h5 this]
  nlinarith [mul_self_nonneg u, mul_self_nonneg p, abs_nonneg A, abs_nonneg B, abs_nonneg c]

end BlockBand.Transmission.DualLift
