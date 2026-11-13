module

public import BlockBand.Native.ErdosRiabov.QV.Phi

/-!
# The quadratic-variation bound for averaged chains

For an averaged chain `Tr[W(β₀, r) S^c]` of length `k = |r| + 1 ≤ 8` (a word `qvW`), the
quadratic-variation density of its first resolvent (`j = 1`; the other `j` are the rotated
chains) is
`qvQAv P C = Σ_{a,b} S_ab |C_ab|²`, `C = W(β₀, r ++ [(c, β₀)]) = G_1 S^{x_1} ⋯ G_k S^{x_k} G_1`.
Under `APriori P psiI psiA LamM s H` (an explicit hypothesis):

  `qvQAv P C ≤ 𝔠 Λ_M³ (φ^{av,qv}_k)² L^{2β_k} η⁻¹ s^av(c :: r.map fst)²`   (`qv_QV_av`),

`𝔠 = qvC d = 4(C₀+1)(1+C_S)(1+C_K) C₁ C_w`, `L = ℓ_sη_s ≥ 1`, `η = η_s`. The three cases are
(a) `k ≤ 3` (doubled chain, the doubling identity, `qvIsoDiag`); (b) `4 ≤ k ≤ 7` (`(k+1)`-chains,
`qvIsoS`, `S_bb ≤ C_S/L`); (c) `k = 8`: the cut `C = Y S^q X` and the reduction inequality in
entry form `qv_reduction_entry`, then the half-av identity, `qvSWeight`, `qvQKdiag`, `qvQKoff`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.QV

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open Expo (lossAlpha lossBeta)
open Matrix

variable {N : ℕ}

/-- The quadratic-variation constant `𝔠 = 4(C₀+1)(1+C_S)(1+C_K) C₁ C_w`. -/
def qvC (d : VSData) : ℝ :=
  4 * (d.C0 + 1) * (1 + qvCS d) * (1 + Propagator.vsCK d) * d.C1pp * d.Cwc

/-- The averaged QV density `Σ_{a,b} S_ab |C_ab|²` of a matrix `C`. -/
def qvQAv (P : PsiData N) (C : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ a, ∑ b, P.S a b * ‖C a b‖ ^ 2

/-!
## Arithmetic helpers
-/

theorem qv_rpow_sq {L : ℝ} (hL : 0 < L) (a : ℝ) : (L ^ a) ^ 2 = L ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  ring_nf

theorem qv_rpow_div_sqrt {L : ℝ} (hL : 0 < L) (a : ℝ) :
    L ^ a / Real.sqrt L = L ^ (-(1 / 2 - a)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hL]
  ring_nf

theorem qv_rpow_div_self {L : ℝ} (hL : 0 < L) (a : ℝ) : L ^ a / L = L ^ (-(1 - a)) := by
  rw [show L ^ a / L = L ^ a / L ^ (1 : ℝ) by rw [Real.rpow_one], ← Real.rpow_sub hL]
  ring_nf

theorem qv_one_le_rpow {L : ℝ} (hL : 1 ≤ L) {a : ℝ} (ha : 0 ≤ a) : 1 ≤ L ^ a :=
  Real.one_le_rpow hL ha

/-- `sqrt(L⁻¹ X²) = X / √L` for `X ≥ 0`. -/
theorem qv_sqrt_inv_sq {L X : ℝ} (hL : 0 < L) (hX : 0 ≤ X) :
    Real.sqrt (L⁻¹ * X ^ 2) = X / Real.sqrt L := by
  rw [Real.sqrt_mul (inv_nonneg.mpr hL.le), Real.sqrt_sq hX, Real.sqrt_inv]
  ring

/-- `sqrt(L⁻¹^2 X²) = X / L` for `X ≥ 0`. -/
theorem qv_sqrt_inv2_sq {L X : ℝ} (hL : 0 < L) (hX : 0 ≤ X) :
    Real.sqrt (L⁻¹ ^ 2 * X ^ 2) = X / L := by
  rw [← mul_pow, Real.sqrt_sq (mul_nonneg (inv_nonneg.mpr hL.le) hX)]
  ring

theorem qvC_facts (d : VSData) :
    1 ≤ d.C1pp ∧ 1 ≤ d.Cwc ∧ 1 ≤ qvCS d ∧ 0 < Propagator.vsCK d ∧ 1 ≤ d.C0 + 1 :=
  ⟨d.one_le_C1pp, d.one_le_Cwc, qvCS_ge_one d, Propagator.vsCK_pos d,
    by linarith [d.C0_ge_one]⟩

theorem qv_ite_pos {α : Type*} {p : Prop} [Decidable p] (h : p) (x y : α) :
    (if p then x else y) = x := by simp [h]

theorem qv_ite_neg {α : Type*} {p : Prop} [Decidable p] (h : ¬ p) (x y : α) :
    (if p then x else y) = y := by simp [h]

theorem qv_sum_diag (f g : Fin N → Fin N → ℝ) :
    ∑ a, ∑ b, ((if a = b then f a b else 0) + g a b) = ∑ a, f a a + ∑ a, ∑ b, g a b := by
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq]

/-!
## Reduction inequality (entry form) and the av sum identity
-/

/-- **Reduction inequality in entry form**: for `S ≥ 0`,
`|(Y S^q X)_ab|² ≤ (Σ_e S_qe |Y_ae|²)(Σ_e S_qe |X_eb|²)` (Cauchy–Schwarz).
Summed against
`S_ab` this is `(X^* S^q Y^* S^a Y S^q X)_bb ≤ Tr[Y^* S^a Y S^q] (X^* S^q X)_bb`.
-/
theorem qv_reduction_entry (S : Matrix (Fin N) (Fin N) ℝ) (hS : ∀ x y, 0 ≤ S x y)
    (Y X : Matrix (Fin N) (Fin N) ℂ) (q a b : Fin N) :
    ‖(Y * obsMat S q * X) a b‖ ^ 2 ≤
      (∑ e, S q e * ‖Y a e‖ ^ 2) * ∑ e, S q e * ‖X e b‖ ^ 2 := by
  rw [qv_mul_obs_apply]
  have h1 : ‖∑ e, Y a e * (S q e : ℂ) * X e b‖ ≤
      ∑ e, Real.sqrt (S q e) * ‖Y a e‖ * (Real.sqrt (S q e) * ‖X e b‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS q e)]
    have hs := Real.mul_self_sqrt (hS q e)
    have e1 : Real.sqrt (S q e) * ‖Y a e‖ * (Real.sqrt (S q e) * ‖X e b‖) =
        ‖Y a e‖ * S q e * ‖X e b‖ := by
      have e0 : Real.sqrt (S q e) * ‖Y a e‖ * (Real.sqrt (S q e) * ‖X e b‖) =
          (Real.sqrt (S q e) * Real.sqrt (S q e)) * ‖Y a e‖ * ‖X e b‖ := by ring
      rw [e0, hs]; ring
    exact le_of_eq e1.symm
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun e => Real.sqrt (S q e) * ‖Y a e‖) (fun e => Real.sqrt (S q e) * ‖X e b‖)
  have e1 : ∀ e, (Real.sqrt (S q e) * ‖Y a e‖) ^ 2 = S q e * ‖Y a e‖ ^ 2 := fun e => by
    rw [mul_pow, Real.sq_sqrt (hS q e)]
  have e2 : ∀ e, (Real.sqrt (S q e) * ‖X e b‖) ^ 2 = S q e * ‖X e b‖ ^ 2 := fun e => by
    rw [mul_pow, Real.sq_sqrt (hS q e)]
  simp only [e1, e2] at h2
  calc ‖∑ e, Y a e * (S q e : ℂ) * X e b‖ ^ 2
      ≤ (∑ e, Real.sqrt (S q e) * ‖Y a e‖ * (Real.sqrt (S q e) * ‖X e b‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem qvQAv_eq_sum_re (P : PsiData N) (hS : ∀ x y, P.S x y = P.S y x)
    (C : Matrix (Fin N) (Fin N) ℂ) :
    qvQAv P C = ∑ b, ((Cᴴ * obsMat P.S b * C) b b).re := by
  unfold qvQAv
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [qv_sandwich_left, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re, hS b a]

/-!
## Cycle forms
-/

section Cycle

variable {d : VSData} {P : PsiData N} {s : ℝ} (hin : QVInputs d P s)
include hin

theorem qvIsoDiag_snoc (u : List (Fin N)) (c : Fin N) :
    ∑ b, qvIsoSq P s b (u ++ [c]) b ≤ d.Cwc / vsHeight P.z s * qvAvSq P s c u := by
  cases u with
  | nil => exact qvIsoDiag hin c []
  | cons y ys =>
    rw [qvAvSq_rotate]
    exact qvIsoDiag hin y (ys ++ [c])

theorem qvIsoS_snoc (u : List (Fin N)) (c : Fin N) :
    ∑ a, ∑ b, P.S a b * qvIsoSq P s a (u ++ [c]) b ≤
      qvCS d * (d.Cwc / vsHeight P.z s) * qvAvSq P s c u := by
  cases u with
  | nil => exact qvIsoS hin c []
  | cons y ys =>
    rw [qvAvSq_rotate]
    exact qvIsoS hin y (ys ++ [c])

end Cycle

/-!
## Scalar steps
-/

theorem qv_arith_long {Λ CS Cw η Av D O ψ g : ℝ} (hCS : 0 ≤ CS) (hψ : 1 ≤ ψ)
    (hg : 1 ≤ g) (hη : 0 < η) (hCw : 0 ≤ Cw) (hAv : 0 ≤ Av) (hD : D ≤ Cw / η * Av)
    (hO : O ≤ CS * (Cw / η) * Av) :
    2 * Λ ^ 2 * (CS * D + ψ ^ 2 * g ^ 2 * O) ≤ 4 * CS * Cw * Λ ^ 2 * ψ ^ 2 * g ^ 2 / η * Av := by
  have hK : 0 ≤ Cw / η * Av := mul_nonneg (div_nonneg hCw hη.le) hAv
  have hX : 1 ≤ ψ ^ 2 * g ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hψ) (one_le_pow₀ hg)
  have h1 : CS * D ≤ ψ ^ 2 * g ^ 2 * (CS * (Cw / η * Av)) := by
    have := mul_le_mul_of_nonneg_left hD hCS
    nlinarith [mul_nonneg hCS hK]
  have h2 : ψ ^ 2 * g ^ 2 * O ≤ ψ ^ 2 * g ^ 2 * (CS * (Cw / η) * Av) :=
    mul_le_mul_of_nonneg_left hO (by positivity)
  have h3 : 2 * Λ ^ 2 * (CS * D + ψ ^ 2 * g ^ 2 * O) ≤
      2 * Λ ^ 2 * (2 * (ψ ^ 2 * g ^ 2 * (CS * (Cw / η * Av)))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  calc _ ≤ _ := h3
    _ = _ := by field_simp; ring

theorem qv_arith_K {Λ E CS C1 Cw C0 η Lv h2 ψ Av T1 T2 : ℝ} (hΛ : 1 ≤ Λ) (hE : 0 ≤ E)
    (hCS : 1 ≤ CS) (hC1 : 1 ≤ C1) (hCw : 1 ≤ Cw) (hη : 0 < η) (hηC : η ≤ C0 + 1)
    (hC0 : 1 ≤ C0 + 1) (hLv : 1 ≤ Lv)
    (hh2 : 1 ≤ h2) (hψ : 1 ≤ ψ) (hAv : 0 ≤ Av) (hT1 : T1 ≤ CS * C1 * Av)
    (hT2 : T2 ≤ Cw / η * Lv * Av) :
    2 * Λ ^ 2 * (Λ * E) * (Lv * T1 + ψ ^ 2 * h2 * CS * T2) ≤
      4 * (C0 + 1) * CS * C1 * Cw * Λ ^ 3 * (ψ ^ 2 * E) * (h2 * Lv) / η * Av := by
  have hρ : 1 ≤ (C0 + 1) / η := by rw [le_div_iff₀ hη]; linarith
  have hK : 0 ≤ 2 * Λ ^ 2 * (Λ * E) := by positivity
  have hP : 0 ≤ CS * C1 * Av := by positivity
  have hL0 : 0 ≤ Lv := by linarith
  have t1 : Lv * T1 ≤ (C0 + 1) / η * (CS * C1 * Cw) * ψ ^ 2 * (h2 * Lv) * Av := by
    have a1 : Lv * T1 ≤ Lv * (CS * C1 * Av) := mul_le_mul_of_nonneg_left hT1 hL0
    have a2 : Lv ≤ h2 * Lv := le_mul_of_one_le_left hL0 hh2
    have a3 : 1 ≤ (C0 + 1) / η * Cw * ψ ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hρ hCw) (one_le_pow₀ hψ)
    have a4 : Lv * (CS * C1 * Av) ≤ (h2 * Lv) * (CS * C1 * Av) := mul_le_mul_of_nonneg_right a2 hP
    have a5 : (h2 * Lv) * (CS * C1 * Av) ≤
        ((C0 + 1) / η * Cw * ψ ^ 2) * ((h2 * Lv) * (CS * C1 * Av)) :=
      le_mul_of_one_le_left (by positivity) a3
    calc Lv * T1 ≤ _ := a1.trans (a4.trans a5)
      _ = _ := by ring
  have t2 : ψ ^ 2 * h2 * CS * T2 ≤ (C0 + 1) / η * (CS * C1 * Cw) * ψ ^ 2 * (h2 * Lv) * Av := by
    have a1 : ψ ^ 2 * h2 * CS * T2 ≤ ψ ^ 2 * h2 * CS * (Cw / η * Lv * Av) :=
      mul_le_mul_of_nonneg_left hT2 (by positivity)
    have a2 : Cw / η ≤ (C0 + 1) / η * (C1 * Cw) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hη.le
      have : 1 ≤ (C0 + 1) * C1 := one_le_mul_of_one_le_of_one_le hC0 hC1
      nlinarith
    have a3 : ψ ^ 2 * h2 * CS * (Cw / η * Lv * Av) ≤
        ψ ^ 2 * h2 * CS * ((C0 + 1) / η * (C1 * Cw) * Lv * Av) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul_of_nonneg_right a2 (mul_nonneg hL0 hAv)
      nlinarith
    calc ψ ^ 2 * h2 * CS * T2 ≤ _ := a1.trans a3
      _ = _ := by ring
  calc 2 * Λ ^ 2 * (Λ * E) * (Lv * T1 + ψ ^ 2 * h2 * CS * T2)
      ≤ 2 * Λ ^ 2 * (Λ * E) * (2 * ((C0 + 1) / η * (CS * C1 * Cw) * ψ ^ 2 * (h2 * Lv) * Av)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        linarith
    _ = _ := by field_simp; ring

theorem qv_scale {c c' Λp Λ3 φ2 B ηi Av : ℝ} (hc : c ≤ c') (hΛ : Λp ≤ Λ3) (hc0 : 0 ≤ c)
    (hΛ0 : 0 ≤ Λp) (hφ : 0 ≤ φ2) (hB : 1 ≤ B) (hηi : 0 ≤ ηi) (hAv : 0 ≤ Av) :
    c * Λp * φ2 * ηi * Av ≤ c' * Λ3 * φ2 * B * ηi * Av := by
  have h1 : c * Λp ≤ c' * Λ3 := mul_le_mul hc hΛ hΛ0 (hc0.trans hc)
  have h2 : 0 ≤ φ2 * ηi * Av := mul_nonneg (mul_nonneg hφ hηi) hAv
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  have h4 : 0 ≤ c' * Λ3 * (φ2 * ηi * Av) :=
    mul_nonneg (mul_nonneg (hc0.trans hc) (hΛ0.trans hΛ)) h2
  have h5 : c' * Λ3 * (φ2 * ηi * Av) ≤ c' * Λ3 * (φ2 * ηi * Av) * B := le_mul_of_one_le_right h4 hB
  calc c * Λp * φ2 * ηi * Av = c * Λp * (φ2 * ηi * Av) := by ring
    _ ≤ c' * Λ3 * (φ2 * ηi * Av) * B := h3.trans h5
    _ = _ := by ring

theorem qvC_ge_Cwc (d : VSData) : d.Cwc ≤ qvC d := by
  obtain ⟨hC1, hCw, hCS, hCK, hC0⟩ := qvC_facts d
  unfold qvC
  calc d.Cwc = 1 * 1 * 1 * 1 * 1 * d.Cwc := by ring
    _ ≤ 4 * (d.C0 + 1) * (1 + qvCS d) * (1 + Propagator.vsCK d) * d.C1pp * d.Cwc := by
        gcongr <;> linarith

theorem qvC_ge_long (d : VSData) : 4 * qvCS d * d.Cwc ≤ qvC d := by
  obtain ⟨hC1, hCw, hCS, hCK, hC0⟩ := qvC_facts d
  unfold qvC
  calc 4 * qvCS d * d.Cwc = 4 * 1 * qvCS d * 1 * 1 * d.Cwc := by ring
    _ ≤ 4 * (d.C0 + 1) * (1 + qvCS d) * (1 + Propagator.vsCK d) * d.C1pp * d.Cwc := by
        gcongr <;> linarith

theorem qvC_ge_long_nonneg (d : VSData) : 0 ≤ 4 * qvCS d * d.Cwc := by
  obtain ⟨hC1, hCw, hCS, hCK, hC0⟩ := qvC_facts d
  positivity

theorem qvC_ge_K (d : VSData) : 4 * (d.C0 + 1) * qvCS d * d.C1pp * d.Cwc ≤ qvC d := by
  obtain ⟨hC1, hCw, hCS, hCK, hC0⟩ := qvC_facts d
  unfold qvC
  calc 4 * (d.C0 + 1) * qvCS d * d.C1pp * d.Cwc =
        4 * (d.C0 + 1) * qvCS d * 1 * d.C1pp * d.Cwc := by ring
    _ ≤ 4 * (d.C0 + 1) * (1 + qvCS d) * (1 + Propagator.vsCK d) * d.C1pp * d.Cwc := by
        gcongr <;> linarith

theorem qvC_ge_K_nonneg (d : VSData) : 0 ≤ 4 * (d.C0 + 1) * qvCS d * d.C1pp * d.Cwc := by
  obtain ⟨hC1, hCw, hCS, hCK, hC0⟩ := qvC_facts d
  positivity

theorem qvC_pos (d : VSData) : 0 < qvC d := by
  obtain ⟨hC1, hCw, hCS, hCK, hC0⟩ := qvC_facts d
  unfold qvC
  positivity

/-!
## The three cases
-/

section Cases

variable {d : VSData} {P : PsiData N} {psiI psiA : ℕ → ℝ} {LamM s : ℝ}
  {H : Matrix (Fin N) (Fin N) ℂ} (hin : QVInputs d P s) (hA : APriori P psiI psiA LamM s H)
  (hH : H.IsHermitian) (hLam : 1 ≤ LamM) (hI : ∀ j, 1 ≤ psiI j) (hAv : ∀ j, 0 ≤ psiA j)
  (hL1 : 1 ≤ P.lEta s)
include hin hA hH hLam hI hAv hL1

omit hAv in
/-- **(a) `k ≤ 3`**. -/
theorem qv_QV_av_short (β₀ : Bool) (r : List (Fin N × Bool)) (c : Fin N)
    (hk : r.length + 1 ≤ 3) :
    qvQAv P (qvW P s H β₀ (r ++ [(c, β₀)])) ≤
      d.Cwc * LamM * qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 / vsHeight P.z s *
        qvAvSq P s c (r.map Prod.fst) := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  set C := qvW P s H β₀ (r ++ [(c, β₀)])
  set u := (r ++ [(c, β₀)]).map Prod.fst
  have hu : u = r.map Prod.fst ++ [c] := by simp [u]
  set A := qvAdj β₀ (r ++ [(c, β₀)])
  have hD : ∀ b, Cᴴ * obsMat P.S b * C =
      qvW P s H A.1 (A.2 ++ (b, β₀) :: (r ++ [(c, β₀)])) := by
    intro b
    rw [qvW_append, qvW_conjTranspose P s hH]
  have hlen : ∀ b, (A.2 ++ (b, β₀) :: (r ++ [(c, β₀)])).length + 1 =
      2 * (r.length + 1) + 2 := by
    intro b
    simp only [A, List.length_append, List.length_cons, qvAdj_length, List.length_nil]
    omega
  have hsites : ∀ b, (A.2 ++ (b, β₀) :: (r ++ [(c, β₀)])).map Prod.fst =
      u.reverse ++ b :: u := by
    intro b
    simp only [List.map_append, List.map_cons, A, qvAdj_sites, u]
  have h0 : 0 ≤ 1 + psiI (2 * (r.length + 1) + 2) *
      P.lEta s ^ (-(1 / 2 - lossAlpha (2 * (r.length + 1) + 2))) := by
    have := Real.rpow_nonneg hL.le (-(1 / 2 - lossAlpha (2 * (r.length + 1) + 2)))
    nlinarith [hI (2 * (r.length + 1) + 2)]
  have hφ : qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 =
      1 + psiI (2 * (r.length + 1) + 2) *
        P.lEta s ^ (-(1 / 2 - lossAlpha (2 * (r.length + 1) + 2))) := by
    unfold qvPhiAv
    rw [qv_ite_pos hk, Real.sq_sqrt h0]
  have hb : ∀ b, ((Cᴴ * obsMat P.S b * C) b b).re ≤
      LamM * qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 * qvIsoSq P s b u b := by
    intro b
    have h := hA.word_iso hU hL hLam A.1 (A.2 ++ (b, β₀) :: (r ++ [(c, β₀)]))
      (by rw [hlen]; linarith [hI (2 * (r.length + 1) + 2)]) (by rw [hlen]; omega) b b
    rw [hlen, hsites, qv_ite_pos rfl, qvIsoSq_double P s hin.symm, ← hD b] at h
    have hX := qvIsoSq_nonneg P s hU hL b u b
    rw [qv_sqrt_inv_sq hL hX] at h
    refine (Complex.re_le_norm _).trans (h.trans_eq ?_)
    rw [hφ]
    have hs : 0 < Real.sqrt (P.lEta s) := Real.sqrt_pos.mpr hL
    rw [← qv_rpow_div_sqrt hL]
    field_simp
  calc qvQAv P C = ∑ b, ((Cᴴ * obsMat P.S b * C) b b).re := qvQAv_eq_sum_re P hin.sSymm C
    _ ≤ ∑ b, LamM * qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 * qvIsoSq P s b u b :=
        Finset.sum_le_sum fun b _ => hb b
    _ = LamM * qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 * ∑ b, qvIsoSq P s b u b := by
        rw [Finset.mul_sum]
    _ ≤ LamM * qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
          (d.Cwc / vsHeight P.z s * qvAvSq P s c (r.map Prod.fst)) := by
        rw [hu]
        exact mul_le_mul_of_nonneg_left (qvIsoDiag_snoc hin _ c)
          (mul_nonneg (by linarith) (sq_nonneg _))
    _ = _ := by ring

omit hH hAv in
/-- **(b) `4 ≤ k ≤ 7`**: `(k+1)`-chains, `qvIsoS`, `S_bb ≤ C_S/L`. -/
theorem qv_QV_av_long (β₀ : Bool) (r : List (Fin N × Bool)) (c : Fin N)
    (hk4 : 4 ≤ r.length + 1) (hk : r.length + 1 ≤ 7) :
    qvQAv P (qvW P s H β₀ (r ++ [(c, β₀)])) ≤
      4 * qvCS d * d.Cwc * LamM ^ 2 * qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
        P.lEta s ^ (2 * lossBeta (r.length + 1)) / vsHeight P.z s *
          qvAvSq P s c (r.map Prod.fst) := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  have hη := hin.height_pos
  have hlen : (r ++ [(c, β₀)]).length + 1 = r.length + 1 + 1 := by simp
  have hφ : qvPhiAv psiI psiA (r.length + 1) (P.lEta s) = psiI (r.length + 1 + 1) := by
    unfold qvPhiAv
    rw [qv_ite_neg (by omega), qv_ite_pos (by omega)]
  have hg : (P.lEta s ^ lossAlpha (r.length + 1 + 1)) ^ 2 =
      P.lEta s ^ (2 * lossBeta (r.length + 1)) := by
    rw [qv_rpow_sq hL, qv_beta_eq_alpha (by omega)]
  rw [hφ, ← hg]
  have hu : (r ++ [(c, β₀)]).map Prod.fst = r.map Prod.fst ++ [c] := by simp
  have hent : ∀ a b, ‖qvW P s H β₀ (r ++ [(c, β₀)]) a b‖ ^ 2 ≤
      2 * LamM ^ 2 * ((if a = b then P.lEta s else 0) + psiI (r.length + 1 + 1) ^ 2 *
        (P.lEta s ^ lossAlpha (r.length + 1 + 1)) ^ 2) *
          qvIsoSq P s a (r.map Prod.fst ++ [c]) b := by
    intro a b
    have h := hA.word_iso_sq hU hL hLam β₀ (r ++ [(c, β₀)])
      (by rw [hlen]; linarith [hI (r.length + 1 + 1)]) (by rw [hlen]; omega) a b
    rwa [hlen, hu] at h
  have hS2 : ∀ a b, P.S a b * ‖qvW P s H β₀ (r ++ [(c, β₀)]) a b‖ ^ 2 ≤
      2 * LamM ^ 2 * ((if a = b then qvCS d * qvIsoSq P s a (r.map Prod.fst ++ [c]) b else 0) +
        psiI (r.length + 1 + 1) ^ 2 * (P.lEta s ^ lossAlpha (r.length + 1 + 1)) ^ 2 *
          (P.S a b * qvIsoSq P s a (r.map Prod.fst ++ [c]) b)) := by
    intro a b
    have hq := qvIsoSq_nonneg P s hU hL a (r.map Prod.fst ++ [c]) b
    have h1 := mul_le_mul_of_nonneg_left (hent a b) (hin.sNonneg a b)
    refine h1.trans ?_
    by_cases hab : a = b
    · subst hab
      rw [qv_ite_pos rfl, qv_ite_pos rfl]
      have hS := hin.sLe a a
      rw [hin.diag] at hS
      have h2 : P.S a a * P.lEta s ≤ qvCS d := by
        have := mul_le_mul_of_nonneg_right hS hL.le
        rwa [mul_assoc, inv_mul_cancel₀ hL.ne', mul_one] at this
      have h3 := mul_le_mul_of_nonneg_right h2 hq
      nlinarith [sq_nonneg LamM]
    · rw [qv_ite_neg hab, qv_ite_neg hab]
      apply le_of_eq
      ring
  have hD := qvIsoDiag_snoc hin (r.map Prod.fst) c
  have hO := qvIsoS_snoc hin (r.map Prod.fst) c
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hS2 a b
  rw [show (∑ a, ∑ b, 2 * LamM ^ 2 *
      ((if a = b then qvCS d * qvIsoSq P s a (r.map Prod.fst ++ [c]) b else 0) +
        psiI (r.length + 1 + 1) ^ 2 * (P.lEta s ^ lossAlpha (r.length + 1 + 1)) ^ 2 *
          (P.S a b * qvIsoSq P s a (r.map Prod.fst ++ [c]) b))) =
      2 * LamM ^ 2 * (qvCS d * ∑ a, qvIsoSq P s a (r.map Prod.fst ++ [c]) a +
        psiI (r.length + 1 + 1) ^ 2 * (P.lEta s ^ lossAlpha (r.length + 1 + 1)) ^ 2 *
          ∑ a, ∑ b, P.S a b * qvIsoSq P s a (r.map Prod.fst ++ [c]) b) by
    simp [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq]] at hsum
  refine hsum.trans (qv_arith_long (by linarith [qvCS_ge_one d]) (hI _)
    (qv_one_le_rpow hL1 (qv_alpha_nonneg _)) hη (by linarith [d.one_le_Cwc])
    (qvAvSq_nonneg P s hU hL c _) hD hO)

/-- **(c) `k = 8`, the cut and the reduction inequality** (cut at `q = x_4`). Here
`r = rY ++ (q, βX) :: rX` with `|rY| = |rX| = 3`. -/
theorem qv_QV_av_K (β₀ : Bool) (rY : List (Fin N × Bool)) (q : Fin N) (βX : Bool)
    (rX : List (Fin N × Bool)) (c : Fin N) (hY : rY.length = 3) (hX : rX.length = 3) :
    qvQAv P (qvW P s H β₀ ((rY ++ (q, βX) :: rX) ++ [(c, β₀)])) ≤
      4 * (d.C0 + 1) * qvCS d * d.C1pp * d.Cwc * LamM ^ 3 *
        qvPhiAv psiI psiA 8 (P.lEta s) ^ 2 * P.lEta s ^ (2 * lossBeta 8) / vsHeight P.z s *
          qvAvSq P s c ((rY ++ (q, βX) :: rX).map Prod.fst) := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  have hC : qvW P s H β₀ ((rY ++ (q, βX) :: rX) ++ [(c, β₀)]) =
      qvW P s H β₀ rY * obsMat P.S q * qvW P s H βX (rX ++ [(c, β₀)]) := by
    rw [List.append_assoc, List.cons_append, qvW_append]
  -- the factor `T_b` (an averaged chain of length `8`)
  have hT : ∀ b, ∑ a, P.S b a * ∑ e, P.S q e * ‖qvW P s H β₀ rY a e‖ ^ 2 ≤
      LamM * (1 + psiA 8 * P.lEta s ^ (-(1 - lossBeta 8))) *
        qvIsoSq P s b (rY.map Prod.fst) q := by
    intro b
    have hW : qvW P s H β₀ rY * obsMat P.S q * (qvW P s H β₀ rY)ᴴ =
        qvW P s H β₀ (rY ++ (q, (qvAdj β₀ rY).1) :: (qvAdj β₀ rY).2) := by
      rw [qvW_append, qvW_conjTranspose P s hH]
    have hlen : (rY ++ (q, (qvAdj β₀ rY).1) :: (qvAdj β₀ rY).2).length + 1 = 8 := by
      simp only [List.length_append, List.length_cons, qvAdj_length]
      omega
    have hsites : (rY ++ (q, (qvAdj β₀ rY).1) :: (qvAdj β₀ rY).2).map Prod.fst =
        rY.map Prod.fst ++ q :: (rY.map Prod.fst).reverse := by
      simp only [List.map_append, List.map_cons, qvAdj_sites]
    have h := hA.word_av hU hL hLam β₀ (rY ++ (q, (qvAdj β₀ rY).1) :: (qvAdj β₀ rY).2)
      (by rw [hlen]; exact hAv 8) (by rw [hlen]) b
    rw [← hW, hlen, hsites, qvAvSq_half P s hin.symm,
      qv_sqrt_inv2_sq hL (qvIsoSq_nonneg P s hU hL b _ q), qv_trace_sandwich] at h
    have hre : ∑ a, P.S b a * ∑ e, P.S q e * ‖qvW P s H β₀ rY a e‖ ^ 2 =
        (∑ a, (P.S b a : ℂ) * ∑ e, (P.S q e : ℂ) *
          ((‖qvW P s H β₀ rY a e‖ ^ 2 : ℝ) : ℂ)).re := by
      simp only [← Complex.ofReal_mul, Complex.ofReal_re, ← Complex.ofReal_sum]
    rw [hre]
    refine (Complex.re_le_norm _).trans (h.trans_eq ?_)
    rw [← qv_rpow_div_self hL]
    field_simp
  -- the factor `R_b` (an isotropic chain of length `5`)
  have hlenX : (rX ++ [(c, β₀)]).length + 1 = 5 := by simp [hX]
  have hR : ∀ b, ∑ e, P.S q e * ‖qvW P s H βX (rX ++ [(c, β₀)]) e b‖ ^ 2 ≤
      2 * LamM ^ 2 * (P.lEta s * (P.S q b * qvIsoSq P s b ((rX ++ [(c, β₀)]).map Prod.fst) b) +
        psiI 5 ^ 2 * P.lEta s ^ (1 / 2 : ℝ) *
          (qvCS d * qvIsoSq P s q ((rX ++ [(c, β₀)]).map Prod.fst) b)) := by
    intro b
    set w := (rX ++ [(c, β₀)]).map Prod.fst
    have hent : ∀ e, P.S q e * ‖qvW P s H βX (rX ++ [(c, β₀)]) e b‖ ^ 2 ≤
        2 * LamM ^ 2 * ((if e = b then P.lEta s * (P.S q e * qvIsoSq P s e w b) else 0) +
          psiI 5 ^ 2 * P.lEta s ^ (1 / 2 : ℝ) * (P.S q e * qvIsoSq P s e w b)) := by
      intro e
      have h := hA.word_iso_sq hU hL hLam βX (rX ++ [(c, β₀)])
        (by rw [hlenX]; linarith [hI 5]) (by rw [hlenX]; norm_num) e b
      rw [hlenX, qv_rpow_sq hL, qv_alpha_five, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num]
        at h
      have h1 := mul_le_mul_of_nonneg_left h (hin.sNonneg q e)
      refine h1.trans (le_of_eq ?_)
      by_cases he : e = b
      · rw [qv_ite_pos he, qv_ite_pos he]; ring
      · rw [qv_ite_neg he, qv_ite_neg he]; ring
    have hsum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) => hent e
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ b,
      qv_ite_pos (Finset.mem_univ b), ← Finset.mul_sum] at hsum
    refine hsum.trans ?_
    have hW := qvSWeight hin q w b
    have h0 : 0 ≤ psiI 5 ^ 2 * P.lEta s ^ (1 / 2 : ℝ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hL.le _)
    have h5 := mul_le_mul_of_nonneg_left hW h0
    nlinarith [sq_nonneg LamM]
  -- reduction inequality
  have hQ : qvQAv P (qvW P s H β₀ rY * obsMat P.S q * qvW P s H βX (rX ++ [(c, β₀)])) ≤
      ∑ b, (∑ a, P.S b a * ∑ e, P.S q e * ‖qvW P s H β₀ rY a e‖ ^ 2) *
        ∑ e, P.S q e * ‖qvW P s H βX (rX ++ [(c, β₀)]) e b‖ ^ 2 := by
    unfold qvQAv
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := mul_le_mul_of_nonneg_left (qv_reduction_entry P.S hin.sNonneg
      (qvW P s H β₀ rY) (qvW P s H βX (rX ++ [(c, β₀)])) q a b) (hin.sNonneg a b)
    rw [hin.sSymm a b] at h ⊢
    linarith
  rw [hC]
  refine hQ.trans ?_
  set u := rY.map Prod.fst
  set w := (rX ++ [(c, β₀)]).map Prod.fst
  have hE : 0 ≤ 1 + psiA 8 * P.lEta s ^ (-(1 - lossBeta 8)) := by
    have := Real.rpow_nonneg hL.le (-(1 - lossBeta 8)); nlinarith [hAv 8]
  have hstep : ∀ b, (∑ a, P.S b a * ∑ e, P.S q e * ‖qvW P s H β₀ rY a e‖ ^ 2) *
      ∑ e, P.S q e * ‖qvW P s H βX (rX ++ [(c, β₀)]) e b‖ ^ 2 ≤
        2 * LamM ^ 2 * (LamM * (1 + psiA 8 * P.lEta s ^ (-(1 - lossBeta 8)))) *
          (P.lEta s * (qvIsoSq P s b u q * P.S q b * qvIsoSq P s b w b) +
            psiI 5 ^ 2 * P.lEta s ^ (1 / 2 : ℝ) * qvCS d *
              (qvIsoSq P s b u q * qvIsoSq P s q w b)) := by
    intro b
    have hR0 : 0 ≤ ∑ e, P.S q e * ‖qvW P s H βX (rX ++ [(c, β₀)]) e b‖ ^ 2 :=
      Finset.sum_nonneg fun e _ => mul_nonneg (hin.sNonneg _ _) (sq_nonneg _)
    have hq0 := qvIsoSq_nonneg P s hU hL b u q
    have h := mul_le_mul (hT b) (hR b) hR0 (mul_nonneg (mul_nonneg (by linarith) hE) hq0)
    refine h.trans (le_of_eq ?_)
    ring
  have hsum := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hstep b
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  refine hsum.trans ?_
  -- the two contractions `qvQKdiag`, `qvQKoff`
  obtain ⟨y1, u', hu'⟩ : ∃ y1 u', u = y1 :: u' := by
    rcases rY with _ | ⟨e, rY'⟩
    · simp at hY
    · exact ⟨e.1, rY'.map Prod.fst, by simp [u]⟩
  obtain ⟨f1, w', hw'⟩ : ∃ f1 w', w = f1 :: w' := by
    rcases rX with _ | ⟨e, rX'⟩
    · simp at hX
    · exact ⟨e.1, (rX' ++ [(c, β₀)]).map Prod.fst, by simp [w]⟩
  have hcyc : qvAvSq P s y1 (u' ++ q :: w) =
      qvAvSq P s c ((rY ++ (q, βX) :: rX).map Prod.fst) := by
    have hmap : (rY ++ (q, βX) :: rX).map Prod.fst = y1 :: (u' ++ q :: rX.map Prod.fst) := by
      simp only [List.map_append, List.map_cons]
      rw [show rY.map Prod.fst = u from rfl, hu']
      rfl
    have hw2 : w = rX.map Prod.fst ++ [c] := by simp [w]
    rw [hmap, qvAvSq_rotate, hw2]
    simp
  have hdiagK := qvQKdiag hin y1 u' q f1 w'
  rw [← hu', ← hw', hcyc] at hdiagK
  have hdiag' : ∑ b, qvIsoSq P s b u q * P.S q b * qvIsoSq P s b w b ≤
      qvCS d * d.C1pp * qvAvSq P s c ((rY ++ (q, βX) :: rX).map Prod.fst) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) hdiagK
    rw [hin.sSymm q b]
  have hoffK := qvQKoff hin y1 u' q w
  rw [← hu', hcyc] at hoffK
  have hφ : qvPhiAv psiI psiA 8 (P.lEta s) ^ 2 =
      psiI 5 ^ 2 * (1 + psiA 8 * P.lEta s ^ (-(1 - lossBeta 8))) := by
    unfold qvPhiAv
    rw [qv_ite_neg (by norm_num), qv_ite_neg (by norm_num), mul_pow, Real.sq_sqrt hE]
  have hβ : P.lEta s ^ (2 * lossBeta 8) = P.lEta s ^ (1 / 2 : ℝ) * P.lEta s := by
    rw [qv_beta_eight, ← Real.rpow_add_one hL.ne']
    norm_num
  rw [hφ, hβ]
  exact qv_arith_K hLam hE (qvCS_ge_one d) d.one_le_C1pp d.one_le_Cwc hin.height_pos
    hin.height_le (by linarith [d.C0_ge_one]) hL1 (qv_one_le_rpow hL1 (by norm_num)) (hI 5)
    (qvAvSq_nonneg P s hU hL c _) hdiag' hoffK

/-- **The averaged quadratic-variation density bound.** Under `APriori P psiI psiA LamM s H`
(an explicit hypothesis), the QV inputs at `s`, `H` Hermitian, `Λ_M ≥ 1`, `ψ ≥ 1`, `ψ^av ≥ 0`,
`L_s ≥ 1`: for every averaged chain `(β₀, r, c)` of length `k = |r| + 1 ≤ 8`,
`Σ_{a,b} S_ab |(G_1 S^{x_1} ⋯ G_k S^{x_k} G_1)_{ab}|² ≤
𝔠 Λ_M³ (φ^{av,qv}_k)² L^{2β_k} η⁻¹ s^av(c:: r.map fst)²`.
-/
theorem qv_QV_av (β₀ : Bool) (r : List (Fin N × Bool)) (c : Fin N) (hk : r.length + 1 ≤ 8) :
    qvQAv P (qvW P s H β₀ (r ++ [(c, β₀)])) ≤
      qvC d * LamM ^ 3 * qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
        P.lEta s ^ (2 * lossBeta (r.length + 1)) / vsHeight P.z s *
          qvAvSq P s c (r.map Prod.fst) := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  have hη := hin.height_pos
  have hav := qvAvSq_nonneg P s hU hL c (r.map Prod.fst)
  have hβ1 : 1 ≤ P.lEta s ^ (2 * lossBeta (r.length + 1)) :=
    qv_one_le_rpow hL1 (by linarith [qv_beta_nonneg (r.length + 1)])
  have hηi : 0 ≤ 1 / vsHeight P.z s := by positivity
  have hΛ3 : LamM ≤ LamM ^ 3 := le_self_pow₀ hLam (by norm_num)
  have hΛ2 : LamM ^ 2 ≤ LamM ^ 3 := pow_le_pow_right₀ hLam (by norm_num)
  have hβ0 : 0 ≤ P.lEta s ^ (2 * lossBeta (r.length + 1)) := by linarith
  rcases (show r.length + 1 ≤ 3 ∨ (4 ≤ r.length + 1 ∧ r.length + 1 ≤ 7) ∨ r.length + 1 = 8 by
    omega) with h | ⟨h4, h7⟩ | h8
  · have hcase := qv_QV_av_short hin hA hH hLam hI hL1 β₀ r c h
    calc _ ≤ _ := hcase
      _ = d.Cwc * LamM * qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
          (1 / vsHeight P.z s) * qvAvSq P s c (r.map Prod.fst) := by ring
      _ ≤ qvC d * LamM ^ 3 * qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
          P.lEta s ^ (2 * lossBeta (r.length + 1)) * (1 / vsHeight P.z s) *
            qvAvSq P s c (r.map Prod.fst) :=
        qv_scale (qvC_ge_Cwc d) hΛ3 (by linarith [d.one_le_Cwc]) (by linarith) (sq_nonneg _)
          hβ1 hηi hav
      _ = _ := by ring
  · have hcase := qv_QV_av_long hin hA hLam hI hL1 β₀ r c h4 h7
    calc _ ≤ _ := hcase
      _ = 4 * qvCS d * d.Cwc * LamM ^ 2 * (qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
          P.lEta s ^ (2 * lossBeta (r.length + 1))) * (1 / vsHeight P.z s) *
            qvAvSq P s c (r.map Prod.fst) := by ring
      _ ≤ qvC d * LamM ^ 3 * (qvPhiAv psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
          P.lEta s ^ (2 * lossBeta (r.length + 1))) * 1 * (1 / vsHeight P.z s) *
            qvAvSq P s c (r.map Prod.fst) :=
        qv_scale (qvC_ge_long d) hΛ2 (by linarith [qvC_ge_long_nonneg d]) (by positivity)
          (mul_nonneg (sq_nonneg _) hβ0) le_rfl hηi hav
      _ = _ := by ring
  · have hr7 : r.length = 7 := by omega
    have hd : (r.drop 3).length = 4 := by simp [hr7]
    obtain ⟨⟨q, βX⟩, rX, hrX⟩ : ∃ qx rX, r.drop 3 = qx :: rX := by
      cases h : r.drop 3 with
      | nil => rw [h] at hd; simp at hd
      | cons qx rX => exact ⟨qx, rX, rfl⟩
    have hsplit : r = r.take 3 ++ (q, βX) :: rX := by
      rw [← hrX, List.take_append_drop]
    have hY : (r.take 3).length = 3 := by simp [hr7]
    have hX : rX.length = 3 := by
      have := congrArg List.length hrX
      simp [hr7] at this
      omega
    have hcase := qv_QV_av_K hin hA hH hLam hI hAv hL1 β₀ (r.take 3) q βX rX c hY hX
    rw [← hsplit] at hcase
    rw [h8]
    rw [h8] at hβ0
    calc _ ≤ _ := hcase
      _ = 4 * (d.C0 + 1) * qvCS d * d.C1pp * d.Cwc * LamM ^ 3 *
          (qvPhiAv psiI psiA 8 (P.lEta s) ^ 2 * P.lEta s ^ (2 * lossBeta 8)) *
            (1 / vsHeight P.z s) * qvAvSq P s c (r.map Prod.fst) := by ring
      _ ≤ qvC d * LamM ^ 3 * (qvPhiAv psiI psiA 8 (P.lEta s) ^ 2 *
          P.lEta s ^ (2 * lossBeta 8)) * 1 * (1 / vsHeight P.z s) *
            qvAvSq P s c (r.map Prod.fst) :=
        qv_scale (qvC_ge_K d) le_rfl (qvC_ge_K_nonneg d) (by positivity)
          (mul_nonneg (sq_nonneg _) hβ0) le_rfl hηi hav
      _ = _ := by ring

end Cases

end BlockBand.Native.ErdosRiabov.QV
