module

public import BlockBand.Critical.Collar.Density.SpectralSum
public import Mathlib.Analysis.Matrix.Order

/-!
# Measurable polar frame

For `V : Matrix ι (Fin J) ℂ` with `J * J ≤ card ι` we construct a Borel map `V ↦ F V` such that
`F V` is an isometry (`(F V)ᴴ * F V = 1`) and `V = F V * (VᴴV)^{1/2}` (polar decomposition).

Construction: with `B = VᴴV`, `Π = χ_{(0,∞)}(B)`, `G = B^{-1/2}` (zero off the support), the
partial isometry `A = V G` satisfies `AᴴA = Π`, `A B^{1/2} = V`. The kernel of `B` is filled
by `N_t = Y_t (Y_tᴴ Y_t)^{-1/2}` with `Y_t = (1 - AAᴴ) E_t (1 - Π)`, where `E_t` (`t : Fin J`)
are coordinate isometries with pairwise disjoint supports (`e : Fin J × Fin J ↪ ι`). The probe
`t` is good when `Y_tᴴ Y_t + Π` is invertible; some probe is always good (`pf_exists_good`),
and the least good one is selected by a finite measurable case split. Measurability of the
Hermitian functional calculus comes from `Collar.Density.measurable_rawCfc_apply`.

Main result: `exists_measurable_polarFrame`. It is used in the closed-source limit step of the
entire law (an old orthonormal frame spanning the `V` columns, padded to full rank), so that
`MatrixClosingStatement.stable_joint_atZero` receives measurable frames.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open Matrix
open scoped ComplexOrder

section PolarFrame

variable {n : Type} [Fintype n] [DecidableEq n]

theorem pf_cont (A : Matrix n n ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
  (Matrix.finite_real_spectrum (A := A)).continuousOn f

theorem pf_mul {A : Matrix n n ℂ} (f g h : ℝ → ℝ)
    (hfg : ∀ x ∈ spectrum ℝ A, f x * g x = h x) : cfc f A * cfc g A = cfc h A := by
  rw [← cfc_mul f g A (pf_cont A f) (pf_cont A g)]
  exact cfc_congr fun x hx => hfg x hx

theorem pf_mul_self {A : Matrix n n ℂ} (hA : A.IsHermitian) (f h : ℝ → ℝ)
    (hfg : ∀ x ∈ spectrum ℝ A, f x * x = h x) : cfc f A * A = cfc h A := by
  have hA' : IsSelfAdjoint A := hA
  calc cfc f A * A = cfc f A * cfc (fun x => x) A := by rw [cfc_id' ℝ A hA']
    _ = cfc h A := pf_mul f (fun x => x) h hfg

theorem pf_self_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (f h : ℝ → ℝ)
    (hfg : ∀ x ∈ spectrum ℝ A, x * f x = h x) : A * cfc f A = cfc h A := by
  have hA' : IsSelfAdjoint A := hA
  calc A * cfc f A = cfc (fun x => x) A * cfc f A := by rw [cfc_id' ℝ A hA']
    _ = cfc h A := pf_mul (fun x => x) f h hfg

theorem pf_herm (A : Matrix n n ℂ) (f : ℝ → ℝ) : (cfc f A)ᴴ = cfc f A :=
  (cfc_predicate f A : IsSelfAdjoint (cfc f A))

theorem pf_spec_nonneg {m : Type} [Fintype m] (X : Matrix m n ℂ) :
    ∀ x ∈ spectrum ℝ (Xᴴ * X), 0 ≤ x := by
  intro x hx
  have hP := posSemidef_conjTranspose_mul_self X
  rw [hP.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, hi⟩ := hx
  rw [← hi]
  exact hP.eigenvalues_nonneg i

/-- Indicator of `(0, ∞)`. -/
def pf_chi (x : ℝ) : ℝ := if 0 < x then 1 else 0

/-- `x ↦ x^{-1/2}` (zero for `x ≤ 0`). -/
def pf_g (x : ℝ) : ℝ := (Real.sqrt x)⁻¹

theorem pf_sqrt_eq_zero {x : ℝ} (hx : ¬ 0 < x) : Real.sqrt x = 0 :=
  Real.sqrt_eq_zero'.mpr (not_lt.mp hx)

theorem pf_chi_chi (x : ℝ) : pf_chi x * pf_chi x = pf_chi x := by
  unfold pf_chi; split_ifs <;> norm_num

theorem pf_g_g (x : ℝ) : pf_g x * pf_g x * x = pf_chi x := by
  unfold pf_g pf_chi
  split_ifs with h
  · have h1 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr h).ne'
    have h2 := Real.mul_self_sqrt h.le
    field_simp
    linarith
  · simp [pf_sqrt_eq_zero h]

theorem pf_g_g' (x : ℝ) : pf_g x * (pf_g x * x) = pf_chi x := by
  rw [← mul_assoc, pf_g_g]

theorem pf_chi_id {x : ℝ} (hx : 0 ≤ x) : pf_chi x * x = x := by
  unfold pf_chi; split_ifs with h
  · ring
  · simp [le_antisymm (not_lt.mp h) hx]

theorem pf_g_chi (x : ℝ) : pf_g x * pf_chi x = pf_g x := by
  unfold pf_g pf_chi; split_ifs with h
  · ring
  · simp [pf_sqrt_eq_zero h]

theorem pf_g_sqrt (x : ℝ) : pf_g x * Real.sqrt x = pf_chi x := by
  unfold pf_g pf_chi; split_ifs with h
  · exact inv_mul_cancel₀ (Real.sqrt_pos.mpr h).ne'
  · simp [pf_sqrt_eq_zero h]

theorem pf_chi_sqrt (x : ℝ) : pf_chi x * Real.sqrt x = Real.sqrt x := by
  unfold pf_chi; split_ifs with h
  · ring
  · simp [pf_sqrt_eq_zero h]

variable {m : Type} [Fintype m]

/-- The support projection `Π = χ(VᴴV)`. -/
def pf_Pi (V : Matrix m n ℂ) : Matrix n n ℂ := cfc pf_chi (Vᴴ * V)
/-- `(VᴴV)^{-1/2}` on the support. -/
def pf_G (V : Matrix m n ℂ) : Matrix n n ℂ := cfc pf_g (Vᴴ * V)
/-- The partial isometry `V (VᴴV)^{-1/2}`. -/
def pf_A (V : Matrix m n ℂ) : Matrix m n ℂ := V * pf_G V
/-- The range projection of `V`. -/
def pf_P (V : Matrix m n ℂ) : Matrix m m ℂ := pf_A V * (pf_A V)ᴴ
omit [DecidableEq n] in
theorem pf_herm_gram (V : Matrix m n ℂ) : (Vᴴ * V).IsHermitian :=
  (posSemidef_conjTranspose_mul_self V).1

theorem pf_Pi_herm (V : Matrix m n ℂ) : (pf_Pi V)ᴴ = pf_Pi V := pf_herm _ _
theorem pf_G_herm (V : Matrix m n ℂ) : (pf_G V)ᴴ = pf_G V := pf_herm _ _

theorem pf_Pi_B (V : Matrix m n ℂ) : pf_Pi V * (Vᴴ * V) = Vᴴ * V := by
  rw [pf_Pi, pf_mul_self (pf_herm_gram V) pf_chi (fun x => x)
    (fun x hx => pf_chi_id (pf_spec_nonneg V x hx))]
  exact cfc_id' ℝ _ (pf_herm_gram V)

theorem pf_B_Pi (V : Matrix m n ℂ) : (Vᴴ * V) * pf_Pi V = Vᴴ * V := by
  rw [pf_Pi, pf_self_mul (pf_herm_gram V) pf_chi (fun x => x)
    (fun x hx => by rw [mul_comm]; exact pf_chi_id (pf_spec_nonneg V x hx))]
  exact cfc_id' ℝ _ (pf_herm_gram V)

theorem pf_Pi_Pi (V : Matrix m n ℂ) : pf_Pi V * pf_Pi V = pf_Pi V :=
  pf_mul _ _ _ fun x _ => pf_chi_chi x

theorem pf_V_Pi (V : Matrix m n ℂ) : V * pf_Pi V = V := by
  set Q := pf_Pi V
  have hh : Qᴴ = Q := pf_Pi_herm V
  have h0 : (V - V * Q)ᴴ * (V - V * Q) = 0 := by
    rw [conjTranspose_sub, conjTranspose_mul, hh, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.mul_assoc, Matrix.mul_assoc Q, ← Matrix.mul_assoc Vᴴ V Q, pf_B_Pi]
    simp
  have := conjTranspose_mul_self_eq_zero.mp h0
  exact (sub_eq_zero.mp this).symm

theorem pf_G_B_G (V : Matrix m n ℂ) : pf_G V * (Vᴴ * V) * pf_G V = pf_Pi V := by
  rw [pf_G, pf_mul_self (pf_herm_gram V) pf_g (fun x => pf_g x * x) (fun _ _ => rfl),
    pf_mul _ _ pf_chi (fun x _ => by rw [mul_right_comm]; exact pf_g_g x)]
  rfl

theorem pf_G_Pi (V : Matrix m n ℂ) : pf_G V * pf_Pi V = pf_G V :=
  pf_mul _ _ _ fun x _ => pf_g_chi x

theorem pf_G_S (V : Matrix m n ℂ) : pf_G V * cfc Real.sqrt (Vᴴ * V) = pf_Pi V :=
  pf_mul _ _ _ fun x _ => pf_g_sqrt x

theorem pf_Pi_S (V : Matrix m n ℂ) : pf_Pi V * cfc Real.sqrt (Vᴴ * V) = cfc Real.sqrt (Vᴴ * V) :=
  pf_mul _ _ _ fun x _ => pf_chi_sqrt x

theorem pf_GG_B (V : Matrix m n ℂ) : pf_G V * pf_G V * (Vᴴ * V) = pf_Pi V := by
  rw [pf_G, pf_mul _ _ (fun x => pf_g x * pf_g x) (fun _ _ => rfl),
    pf_mul_self (pf_herm_gram V) _ pf_chi (fun x _ => pf_g_g x)]
  rfl

theorem pf_AA (V : Matrix m n ℂ) : (pf_A V)ᴴ * pf_A V = pf_Pi V := by
  rw [pf_A, conjTranspose_mul, pf_G_herm, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V,
    ← Matrix.mul_assoc, pf_G_B_G]

theorem pf_AS (V : Matrix m n ℂ) : pf_A V * cfc Real.sqrt (Vᴴ * V) = V := by
  rw [pf_A, Matrix.mul_assoc, pf_G_S, pf_V_Pi]

theorem pf_A_Pi (V : Matrix m n ℂ) : pf_A V * pf_Pi V = pf_A V := by
  rw [pf_A, Matrix.mul_assoc, pf_G_Pi]

theorem pf_P_herm (V : Matrix m n ℂ) : (pf_P V)ᴴ = pf_P V := by
  rw [pf_P, conjTranspose_mul, conjTranspose_conjTranspose]

theorem pf_PV (V : Matrix m n ℂ) : pf_P V * V = V := by
  rw [pf_P, pf_A, conjTranspose_mul, pf_G_herm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (pf_G V) (pf_G V), pf_GG_B, pf_V_Pi]

theorem pf_P_A (V : Matrix m n ℂ) : pf_P V = pf_A V * (pf_Pi V * (pf_A V)ᴴ) := by
  rw [← Matrix.mul_assoc, pf_A_Pi]
  rfl

variable [DecidableEq m]

/-- The compressed probe `(1 - P) E (1 - Π)`. -/
def pf_Y (E V : Matrix m n ℂ) : Matrix m n ℂ := (1 - pf_P V) * E * (1 - pf_Pi V)
/-- The complement isometry candidate. -/
def pf_N (E V : Matrix m n ℂ) : Matrix m n ℂ :=
  pf_Y E V * cfc pf_g ((pf_Y E V)ᴴ * pf_Y E V)

theorem pf_VP (V : Matrix m n ℂ) : Vᴴ * (1 - pf_P V) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← pf_P_herm, ← conjTranspose_mul, pf_PV, sub_self]

theorem pf_V_Y (E V : Matrix m n ℂ) : Vᴴ * pf_Y E V = 0 := by
  rw [pf_Y, ← Matrix.mul_assoc, ← Matrix.mul_assoc, pf_VP, Matrix.zero_mul, Matrix.zero_mul]

theorem pf_Y_Pi (E V : Matrix m n ℂ) : pf_Y E V * pf_Pi V = 0 := by
  rw [pf_Y, Matrix.mul_assoc, sub_mul, one_mul, pf_Pi_Pi, sub_self, Matrix.mul_zero]

theorem pf_C_Pi (E V : Matrix m n ℂ) : (pf_Y E V)ᴴ * pf_Y E V * pf_Pi V = 0 := by
  rw [Matrix.mul_assoc, pf_Y_Pi, Matrix.mul_zero]

theorem pf_Pi_C (E V : Matrix m n ℂ) : pf_Pi V * ((pf_Y E V)ᴴ * pf_Y E V) = 0 := by
  rw [← Matrix.mul_assoc, ← pf_Pi_herm V, ← conjTranspose_mul, pf_Y_Pi, conjTranspose_zero,
    Matrix.zero_mul]

/-- The algebraic core: for a good probe `E`, `A + N` is an isometry with `(A + N) S = V`. -/
theorem pf_core (E V : Matrix m n ℂ) (hgood : IsUnit ((pf_Y E V)ᴴ * pf_Y E V + pf_Pi V)) :
    (pf_A V + pf_N E V)ᴴ * (pf_A V + pf_N E V) = 1 ∧
      V = (pf_A V + pf_N E V) * cfc Real.sqrt (Vᴴ * V) := by
  set Y := pf_Y E V with hY
  set Q := pf_Pi V with hQ
  set C := Yᴴ * Y with hC
  have hCQ : C * Q = 0 := pf_C_Pi E V
  have hQC : Q * C = 0 := pf_Pi_C E V
  have hDQ : pf_Pi Y * Q = 0 := by
    rw [← pf_GG_B Y, Matrix.mul_assoc, hCQ, Matrix.mul_zero]
  have hDC : pf_Pi Y * C = C := pf_Pi_B Y
  have hD : pf_Pi Y = 1 - Q := by
    have h0 : (pf_Pi Y - (1 - Q)) * (C + Q) = 0 := by
      calc (pf_Pi Y - (1 - Q)) * (C + Q)
          = pf_Pi Y * C + pf_Pi Y * Q - (C + Q) + (Q * C + Q * Q) := by noncomm_ring
        _ = 0 := by rw [hDC, hDQ, hQC, pf_Pi_Pi]; abel
    exact sub_eq_zero.mp ((hgood.mul_left_eq_zero).mp h0)
  have hNN : (pf_N E V)ᴴ * pf_N E V = 1 - Q := by
    rw [pf_N, conjTranspose_mul, ← hY, ← hC]
    change (pf_G Y)ᴴ * Yᴴ * (Y * pf_G Y) = 1 - Q
    rw [pf_G_herm, Matrix.mul_assoc, ← Matrix.mul_assoc Yᴴ, ← Matrix.mul_assoc, pf_G_B_G, hD]
  have hAN : (pf_A V)ᴴ * pf_N E V = 0 := by
    rw [pf_A, pf_N, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, pf_V_Y,
      Matrix.zero_mul, Matrix.mul_zero]
  have hNA : (pf_N E V)ᴴ * pf_A V = 0 := by
    rw [← conjTranspose_conjTranspose (pf_A V), ← conjTranspose_mul, hAN, conjTranspose_zero]
  have hNS : pf_N E V * cfc Real.sqrt (Vᴴ * V) = 0 := by
    rw [pf_N, ← hY, ← hC]
    change Y * pf_G Y * cfc Real.sqrt (Vᴴ * V) = 0
    rw [← pf_G_Pi Y, hD, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hQ,
      pf_Pi_S, sub_self, Matrix.mul_zero, Matrix.mul_zero]
  constructor
  · rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, pf_AA, hAN, hNA, hNN]
    abel
  · rw [Matrix.add_mul, pf_AS, hNS, add_zero]

/-- The coordinate isometry `j ↦ e (t, j)`. -/
def pf_E (e : n × n → m) (t : n) : Matrix m n ℂ := Matrix.of fun i j => if i = e (t, j) then 1 else 0

omit [Fintype m] in
theorem pf_E_mulVec {e : n × n → m} (he : Function.Injective e) (t s j : n) (v : n → ℂ) :
    (pf_E e t *ᵥ v) (e (s, j)) = if s = t then v j else 0 := by
  simp only [pf_E, mulVec, dotProduct, of_apply, he.eq_iff, Prod.ext_iff, ite_mul, one_mul,
    zero_mul]
  by_cases h : s = t
  · simp [h]
  · simp [h]

/-- Some probe `E_t` is good, as soon as `n` is nonempty. -/
theorem pf_exists_good (V : Matrix m n ℂ) {e : n × n → m} (he : Function.Injective e) (t0 : n) :
    ∃ t, ((pf_Y (pf_E e t) V)ᴴ * pf_Y (pf_E e t) V + pf_Pi V).det ≠ 0 := by
  by_contra hall
  push Not at hall
  choose y hy0 hy using fun t => exists_mulVec_eq_zero_iff.mpr (hall t)
  have hQy : ∀ t, pf_Pi V *ᵥ y t = 0 := by
    intro t
    have h := congrArg (pf_Pi V *ᵥ ·) (hy t)
    simp only [mulVec_mulVec, mul_add, pf_Pi_C, zero_add, pf_Pi_Pi, mulVec_zero] at h
    exact h
  have hYy : ∀ t, pf_Y (pf_E e t) V *ᵥ y t = 0 := by
    intro t
    have h := hy t
    rw [add_mulVec, hQy, add_zero] at h
    exact (conjTranspose_mul_self_mulVec_eq_zero _ _).mp h
  have hEy : ∀ t, pf_P V *ᵥ (pf_E e t *ᵥ y t) = pf_E e t *ᵥ y t := by
    intro t
    have h := hYy t
    rw [pf_Y, ← mulVec_mulVec, ← mulVec_mulVec, sub_mulVec (1 : Matrix n n ℂ), one_mulVec, hQy,
      sub_zero, sub_mulVec, one_mulVec, sub_eq_zero] at h
    exact h.symm
  set W : Matrix m n ℂ := Matrix.of fun i t => (pf_E e t *ᵥ y t) i with hW
  have hPW : pf_P V * W = W := by
    ext i t
    rw [mul_apply]
    exact congrFun (hEy t) i
  have hdetQ : (pf_Pi V).det = 0 := exists_mulVec_eq_zero_iff.mp ⟨y t0, hy0 t0, hQy t0⟩
  have hdet : (pf_Pi V * ((pf_A V)ᴴ * W)).det = 0 := by rw [det_mul, hdetQ, zero_mul]
  obtain ⟨c, hc0, hc⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have hWc : W *ᵥ c = 0 := by
    have h : pf_P V * W = pf_A V * (pf_Pi V * ((pf_A V)ᴴ * W)) := by
      rw [pf_P_A]
      simp only [Matrix.mul_assoc]
    rw [← hPW, h, ← mulVec_mulVec, hc, mulVec_zero]
  obtain ⟨s, hs⟩ : ∃ s, c s ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  apply hy0 s
  funext j
  have h := congrFun hWc (e (s, j))
  have hcoord : (W *ᵥ c) (e (s, j)) = y s j * c s := by
    change ∑ t, W (e (s, j)) t * c t = _
    simp only [hW, of_apply, pf_E_mulVec he, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  rw [hcoord] at h
  exact (mul_eq_zero.mp h).resolve_right hs

/-!
### Measurability
-/

section Meas

variable {α : Type} [MeasurableSpace α]

omit [DecidableEq m] in
theorem pf_meas_mul {p q r : Type} [Fintype q] {M : α → Matrix p q ℂ} {N : α → Matrix q r ℂ}
    (hM : Measurable M) (hN : Measurable N) : Measurable fun a => M a * N a := by
  refine Measurable.of_eval_matrix _ fun i k => ?_
  simp only [mul_apply]
  exact Finset.measurable_sum _ fun j _ => hM.eval_matrix.mul hN.eval_matrix

omit [DecidableEq m] in
theorem pf_meas_conjT {p q : Type} {M : α → Matrix p q ℂ} (hM : Measurable M) :
    Measurable fun a => (M a)ᴴ := by
  refine Measurable.of_eval_matrix _ fun i k => ?_
  simp only [conjTranspose_apply]
  exact Complex.continuous_conj.measurable.comp hM.eval_matrix

omit [DecidableEq m] in
theorem pf_meas_add {p q : Type} {M N : α → Matrix p q ℂ} (hM : Measurable M)
    (hN : Measurable N) : Measurable fun a => M a + N a := by
  refine Measurable.of_eval_matrix _ fun i k => ?_
  simp only [Matrix.add_apply]
  exact hM.eval_matrix.add hN.eval_matrix

omit [DecidableEq m] in
theorem pf_meas_sub {p q : Type} {M N : α → Matrix p q ℂ} (hM : Measurable M)
    (hN : Measurable N) : Measurable fun a => M a - N a := by
  refine Measurable.of_eval_matrix _ fun i k => ?_
  simp only [Matrix.sub_apply]
  exact hM.eval_matrix.sub hN.eval_matrix

omit [DecidableEq m] in
theorem pf_meas_cfc {M : α → Matrix n n ℂ} (hM : Measurable M) (hH : ∀ a, (M a).IsHermitian)
    {f : ℝ → ℝ} (hf : Measurable f) : Measurable fun a => cfc f (M a) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  have heq : (fun a => cfc f (M a) x y) =
      fun a => BlockBand.Critical.Collar.Density.rawCfc f (M a) x y :=
    funext fun a => by rw [BlockBand.Critical.Collar.Density.rawCfc_eq_cfc (hH a)]
  rw [heq]
  exact BlockBand.Critical.Collar.Density.measurable_rawCfc_apply hM hf x y

omit [DecidableEq m] in
theorem pf_meas_gram {p q : Type} [Fintype p] {M : α → Matrix p q ℂ} (hM : Measurable M) :
    Measurable fun a => (M a)ᴴ * M a :=
  pf_meas_mul (pf_meas_conjT hM) hM

end Meas

theorem pf_meas_chi : Measurable pf_chi := by
  unfold pf_chi
  exact Measurable.ite measurableSet_Ioi measurable_const measurable_const

theorem pf_meas_g : Measurable pf_g := Real.continuous_sqrt.measurable.inv

omit [DecidableEq m] in
theorem pf_meas_Pi : Measurable fun V : Matrix m n ℂ => pf_Pi V :=
  pf_meas_cfc (pf_meas_gram measurable_id) pf_herm_gram pf_meas_chi

omit [DecidableEq m] in
theorem pf_meas_A : Measurable fun V : Matrix m n ℂ => pf_A V :=
  pf_meas_mul measurable_id (pf_meas_cfc (pf_meas_gram measurable_id) pf_herm_gram pf_meas_g)

omit [DecidableEq m] in
theorem pf_meas_P : Measurable fun V : Matrix m n ℂ => pf_P V :=
  pf_meas_mul pf_meas_A (pf_meas_conjT pf_meas_A)

theorem pf_meas_Y (E : Matrix m n ℂ) : Measurable fun V : Matrix m n ℂ => pf_Y E V :=
  pf_meas_mul (pf_meas_mul (pf_meas_sub measurable_const pf_meas_P) measurable_const)
    (pf_meas_sub measurable_const pf_meas_Pi)

theorem pf_meas_N (E : Matrix m n ℂ) : Measurable fun V : Matrix m n ℂ => pf_N E V :=
  pf_meas_mul (pf_meas_Y E)
    (pf_meas_cfc (pf_meas_gram (pf_meas_Y E)) (fun _ => pf_herm_gram _) pf_meas_g)

/-- The good-probe condition. -/
def pf_good (E V : Matrix m n ℂ) : Prop := ((pf_Y E V)ᴴ * pf_Y E V + pf_Pi V).det ≠ 0

theorem pf_meas_good (E : Matrix m n ℂ) : Measurable fun V : Matrix m n ℂ => pf_good E V := by
  have hd : Measurable fun V : Matrix m n ℂ => ((pf_Y E V)ᴴ * pf_Y E V + pf_Pi V).det :=
    (continuous_id.matrix_det).measurable.comp (pf_meas_add (pf_meas_gram (pf_meas_Y E)) pf_meas_Pi)
  exact measurableSet_setOfPred.mp (hd (measurableSet_singleton 0).compl)

end PolarFrame

section Final

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ}

open Classical in
/-- The measurable polar frame: `A + N_t` for the least good probe `t` (junk `A` if none). -/
def pf_F (e : Fin J × Fin J → ι) (V : Matrix ι (Fin J) ℂ) : Matrix ι (Fin J) ℂ :=
  pf_A V + ∑ t : Fin J, if pf_good (pf_E e t) V ∧ ∀ s, s < t → ¬ pf_good (pf_E e s) V then
    pf_N (pf_E e t) V else 0

theorem pf_meas_F (e : Fin J × Fin J → ι) : Measurable (pf_F e) := by
  unfold pf_F
  refine pf_meas_add pf_meas_A ?_
  rw [← Finset.sum_fn]
  refine Finset.sum_induction _ (fun g => Measurable g) (fun a b ha hb => pf_meas_add ha hb)
    measurable_const (fun t _ => ?_)
  refine Measurable.ite (measurableSet_setOfPred.mpr ?_) (pf_meas_N _) measurable_const
  exact (pf_meas_good _).and (Measurable.forall fun s => measurable_const.imp (pf_meas_good _).not)

/-- **Measurable polar decomposition.** For `J * J ≤ card ι` there is a Borel map `F` sending
every `V : ι × J` to an isometry `F V` with `V = F V (VᴴV)^{1/2}`. -/
theorem exists_measurable_polarFrame (hJ : J * J ≤ Fintype.card ι) :
    ∃ F : Matrix ι (Fin J) ℂ → Matrix ι (Fin J) ℂ, Measurable F ∧
      ∀ V : Matrix ι (Fin J) ℂ, (F V)ᴴ * F V = 1 ∧ V = F V * cfc Real.sqrt (Vᴴ * V) := by
  obtain ⟨e⟩ : Nonempty (Fin J × Fin J ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hJ)
  refine ⟨pf_F e, pf_meas_F e, fun V => ?_⟩
  classical
  by_cases hex : ∃ t, pf_good (pf_E e t) V
  · obtain ⟨t, ht, hmin⟩ := WellFounded.has_min wellFounded_lt {t | pf_good (pf_E e t) V} hex
    have hsum : (∑ s : Fin J, if pf_good (pf_E e s) V ∧ ∀ r, r < s → ¬ pf_good (pf_E e r) V then
        pf_N (pf_E e s) V else 0) = pf_N (pf_E e t) V := by
      rw [Finset.sum_eq_single t]
      · exact ite_eq_left ⟨ht, fun r hr hgr => hmin r hgr hr⟩
      · intro b _ hbt
        refine ite_eq_right fun h => ?_
        rcases lt_or_gt_of_ne hbt with hlt | hgt
        · exact hmin b h.1 hlt
        · exact h.2 t hgt ht
      · intro h
        exact absurd (Finset.mem_univ t) h
    have hF : pf_F e V = pf_A V + pf_N (pf_E e t) V := by
      rw [pf_F, ← hsum]
    rw [hF]
    exact pf_core _ V ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht))
  · rcases isEmpty_or_nonempty (Fin J) with hJe | ⟨⟨t0⟩⟩
    · constructor
      · ext i j
        exact (IsEmpty.false i).elim
      · ext i j
        exact (IsEmpty.false j).elim
    · exact absurd (pf_exists_good V e.injective t0) hex

end Final

end BlockBand.Critical.EntireLaw
