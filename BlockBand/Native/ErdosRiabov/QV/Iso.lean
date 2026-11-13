module

public import BlockBand.Native.ErdosRiabov.QV.Tilde

/-!
# The quadratic-variation bound for isotropic chains

For an isotropic chain `W(β₀, r)` of length `k = |r| + 1 ≤ 8` with end points `a, b` and internal
sites `u = r.map fst`, the quadratic-variation density of its `j`-th resolvent is
`qvQIso P G₁ G₂ a b = Σ_{c,d} S_cd |(G₁)_ad|² |(G₂)_cb|²` with `G₁ = G_{[1,j]}`,
`G₂ = G_{[j,k]}`:
* `j = 1`: `G₁ = G_1 = qvRes β₀`, `G₂ = W(β₀, r)` (`qv_QV_iso_first`);

  `qvQIso ≤ 𝔠 Λ_M³ (φ^{iso,qv}_k)² L^{2α_k} η⁻¹ s(a, u, b)²`.

Proof: `j = 1` by the VS decomposition of the two-chain
(`Θ̂_s = |m|²(I+sΘ̂_s)S`, in the form `M_{[1,2]}(c)_aa = m m̄ Σ_d stabOp(a,d) S_cd`) and
`qv_tilde`; `2 ≤ j ≤ ⌊(k+1)/2⌋` by the doubled chain `G₁ S^c G₁ᴴ` (the squared convolution bound,
middle index included); `j > ⌊(k+1)/2⌋` by the symmetry
`qvQIso G₁ G₂ a b = qvQIso G₂ᴴ G₁ᴴ b a` and the adjoint words.
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
open scoped ComplexConjugate

variable {N : ℕ}

/-- The isotropic quadratic-variation density `Σ_{c,d} S_cd |(G₁)_ad|² |(G₂)_cb|²`. -/
def qvQIso (P : PsiData N) (G₁ G₂ : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) : ℝ :=
  ∑ c, ∑ d, P.S c d * ‖G₁ a d‖ ^ 2 * ‖G₂ c b‖ ^ 2

/-- **Isotropic symmetry**:
`Q(G₁, G₂; a, b) = Q(G₂ᴴ, G₁ᴴ; b, a)`.
-/
theorem qvQIso_symm (P : PsiData N) (hS : ∀ x y, P.S x y = P.S y x)
    (G₁ G₂ : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) :
    qvQIso P G₁ G₂ a b = qvQIso P G₂ᴴ G₁ᴴ b a := by
  unfold qvQIso
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [Matrix.conjTranspose_apply, norm_star]
  rw [hS c d]
  ring

theorem qvAdj_fst_snoc : ∀ (β₀ : Bool) (r : List (Fin N × Bool)) (c : Fin N) (β : Bool),
    (qvAdj β₀ (r ++ [(c, β)])).1 = !β
  | _, [], _, _ => rfl
  | _, (c', β') :: r, c, β => by
    simp only [List.cons_append, qvAdj]
    exact qvAdj_fst_snoc β' r c β

theorem qv_sum_split_first (P : PsiData N) (G₁ G₂ : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) :
    qvQIso P G₁ G₂ a b = ∑ c, (∑ d, P.S c d * ‖G₁ a d‖ ^ 2) * ‖G₂ c b‖ ^ 2 := by
  unfold qvQIso
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]

theorem qv_sandwich_right_re (S : Matrix (Fin N) (Fin N) ℝ) (Y : Matrix (Fin N) (Fin N) ℂ)
    (c a : Fin N) : ∑ d, S c d * ‖Y a d‖ ^ 2 = ((Y * obsMat S c * Yᴴ) a a).re := by
  rw [qv_sandwich_right, Complex.re_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-!
## Scalar steps
-/

theorem qv_arith_mid {Λ F ψ g C1 Cw C0 η q : ℝ} (hΛ : 1 ≤ Λ) (hF : 0 ≤ F) (hψ : 1 ≤ ψ)
    (hg : 1 ≤ g) (hC1 : 1 ≤ C1) (hCw : 1 ≤ Cw) (hη : 0 < η) (hηC : η ≤ C0 + 1)
    (hC0' : 1 ≤ C0 + 1) (hq : 0 ≤ q) :
    2 * Λ ^ 3 * F * (C1 * q + ψ ^ 2 * g ^ 2 * (Cw / η * q)) ≤
      4 * (C0 + 1) * C1 * Cw * Λ ^ 3 * (F * ψ ^ 2 * g ^ 2) / η * q := by
  have hρ : 1 ≤ (C0 + 1) / η := by rw [le_div_iff₀ hη]; linarith
  have hX : 1 ≤ ψ ^ 2 * g ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hψ) (one_le_pow₀ hg)
  have hC0 : 0 < C0 + 1 := by linarith
  have t1 : C1 * q ≤ (C0 + 1) / η * (C1 * Cw) * (ψ ^ 2 * g ^ 2) * q := by
    have a : 1 ≤ (C0 + 1) / η * Cw * (ψ ^ 2 * g ^ 2) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hρ hCw) hX
    have := mul_le_mul_of_nonneg_left a (mul_nonneg (by linarith : (0 : ℝ) ≤ C1) hq)
    nlinarith
  have t2 : ψ ^ 2 * g ^ 2 * (Cw / η * q) ≤ (C0 + 1) / η * (C1 * Cw) * (ψ ^ 2 * g ^ 2) * q := by
    have a : Cw / η ≤ (C0 + 1) / η * (C1 * Cw) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hη.le
      have : 1 ≤ (C0 + 1) * C1 := one_le_mul_of_one_le_of_one_le hC0' hC1
      nlinarith
    have := mul_le_mul_of_nonneg_right a (mul_nonneg (by linarith : (0 : ℝ) ≤ ψ ^ 2 * g ^ 2) hq)
    nlinarith
  have hK : 0 ≤ 2 * Λ ^ 3 * F := by positivity
  calc 2 * Λ ^ 3 * F * (C1 * q + ψ ^ 2 * g ^ 2 * (Cw / η * q))
      ≤ 2 * Λ ^ 3 * F * (2 * ((C0 + 1) / η * (C1 * Cw) * (ψ ^ 2 * g ^ 2) * q)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        linarith
    _ = _ := by field_simp; ring

theorem qv_arith_first {Q Λ ψ2 sL X C1 Cw CS CK C0 η q Tt : ℝ} (hΛ : 1 ≤ Λ) (hψ2 : 0 ≤ ψ2)
    (hsL : 0 ≤ sL) (hX : 1 ≤ X) (hC1 : 1 ≤ C1) (hCw : 1 ≤ Cw) (hCS : 1 ≤ CS) (hCK : 0 ≤ CK)
    (hC0 : 1 ≤ C0 + 1) (hη : 0 < η) (hηC : η ≤ C0 + 1) (hq : 0 ≤ q) (hTt : 0 ≤ Tt)
    (hQ : Q ≤ ψ2 * sL * (2 * Λ ^ 2 * (C1 * q + X * (Cw / η * q))) +
      4 * CS * C1 * Λ ^ 3 * Tt * (q + CK * (Cw / η * q))) :
    Q ≤ 4 * (C0 + 1) * (1 + CS) * (1 + CK) * C1 * Cw * Λ ^ 3 * (ψ2 * sL * X + Tt) / η * q := by
  have hρ : 1 ≤ (C0 + 1) / η := by rw [le_div_iff₀ hη]; linarith
  have hΛ2 : Λ ^ 2 ≤ Λ ^ 3 := pow_le_pow_right₀ hΛ (by norm_num)
  set K := (C0 + 1) / η
  have hK : 1 ≤ K := hρ
  -- first part
  have a1 : C1 * q + X * (Cw / η * q) ≤ 2 * (K * C1 * Cw * X * q) := by
    have b1 : C1 * q ≤ K * C1 * Cw * X * q := by
      have : 1 ≤ K * Cw * X := one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hK hCw) hX
      have := mul_le_mul_of_nonneg_left this (mul_nonneg (by linarith : (0 : ℝ) ≤ C1) hq)
      nlinarith
    have b2 : X * (Cw / η * q) ≤ K * C1 * Cw * X * q := by
      have c1 : Cw / η ≤ K * C1 * Cw := by
        unfold K
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hη.le
        have : 1 ≤ (C0 + 1) * C1 := one_le_mul_of_one_le_of_one_le hC0 hC1
        nlinarith
      have := mul_le_mul_of_nonneg_right c1 (mul_nonneg (by linarith : (0 : ℝ) ≤ X) hq)
      nlinarith
    linarith
  have hp1 : ψ2 * sL * (2 * Λ ^ 2 * (C1 * q + X * (Cw / η * q))) ≤
      4 * (C0 + 1) * C1 * Cw * Λ ^ 3 * (ψ2 * sL * X) / η * q := by
    have h0 : 0 ≤ ψ2 * sL := mul_nonneg hψ2 hsL
    have e1 := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ 2 * Λ ^ 2)
    have e2 := mul_le_mul_of_nonneg_left e1 h0
    have e3 : ψ2 * sL * (2 * Λ ^ 2 * (2 * (K * C1 * Cw * X * q))) ≤
        ψ2 * sL * (2 * Λ ^ 3 * (2 * (K * C1 * Cw * X * q))) := by
      apply mul_le_mul_of_nonneg_left _ h0
      apply mul_le_mul_of_nonneg_right (by linarith)
      have : 0 ≤ K := by linarith
      positivity
    calc _ ≤ _ := e2.trans e3
      _ = _ := by unfold K; field_simp; ring
  -- second part
  have a2 : q + CK * (Cw / η * q) ≤ K * (1 + CK) * Cw * q := by
    have b1 : q ≤ K * Cw * q := by
      have : 1 ≤ K * Cw := one_le_mul_of_one_le_of_one_le hK hCw
      nlinarith
    have b2 : CK * (Cw / η * q) ≤ K * CK * Cw * q := by
      have c1 : Cw / η ≤ K * Cw := by
        unfold K
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hη.le
        nlinarith
      have := mul_le_mul_of_nonneg_right c1 (mul_nonneg hCK hq)
      nlinarith
    nlinarith
  have hp2 : 4 * CS * C1 * Λ ^ 3 * Tt * (q + CK * (Cw / η * q)) ≤
      4 * (C0 + 1) * CS * (1 + CK) * C1 * Cw * Λ ^ 3 * Tt / η * q := by
    have h0 : 0 ≤ 4 * CS * C1 * Λ ^ 3 * Tt := by positivity
    have e1 := mul_le_mul_of_nonneg_left a2 h0
    calc _ ≤ _ := e1
      _ = _ := by unfold K; field_simp
  have hfin : 4 * (C0 + 1) * C1 * Cw * Λ ^ 3 * (ψ2 * sL * X) / η * q +
      4 * (C0 + 1) * CS * (1 + CK) * C1 * Cw * Λ ^ 3 * Tt / η * q ≤
      4 * (C0 + 1) * (1 + CS) * (1 + CK) * C1 * Cw * Λ ^ 3 * (ψ2 * sL * X + Tt) / η * q := by
    have hηi : 0 ≤ 1 / η := by positivity
    have hA : 0 ≤ ψ2 * sL * X := by positivity
    have g1 : 4 * (C0 + 1) * C1 * Cw * Λ ^ 3 * (ψ2 * sL * X) ≤
        4 * (C0 + 1) * (1 + CS) * (1 + CK) * C1 * Cw * Λ ^ 3 * (ψ2 * sL * X) := by
      have : 1 ≤ (1 + CS) * (1 + CK) := one_le_mul_of_one_le_of_one_le (by linarith)
        (by linarith)
      have h0 : 0 ≤ 4 * (C0 + 1) * C1 * Cw * Λ ^ 3 * (ψ2 * sL * X) := by positivity
      nlinarith
    have g2 : 4 * (C0 + 1) * CS * (1 + CK) * C1 * Cw * Λ ^ 3 * Tt ≤
        4 * (C0 + 1) * (1 + CS) * (1 + CK) * C1 * Cw * Λ ^ 3 * Tt := by
      have h0 : 0 ≤ 4 * (C0 + 1) * (1 + CK) * C1 * Cw * Λ ^ 3 * Tt := by positivity
      nlinarith
    have g3 := add_le_add g1 g2
    have := mul_le_mul_of_nonneg_right g3 (mul_nonneg hηi hq)
    calc _ = (4 * (C0 + 1) * C1 * Cw * Λ ^ 3 * (ψ2 * sL * X) +
          4 * (C0 + 1) * CS * (1 + CK) * C1 * Cw * Λ ^ 3 * Tt) * (1 / η * q) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  linarith

theorem qv_scale2 {c c' x x' R : ℝ} (hc : c ≤ c') (hc0 : 0 ≤ c) (hx : x ≤ x') (hx0 : 0 ≤ x)
    (hR : 0 ≤ R) : c * x * R ≤ c' * x' * R :=
  mul_le_mul_of_nonneg_right (mul_le_mul hc hx hx0 (hc0.trans hc)) hR

theorem qvPhiTilde_nonneg {psiI psiA : ℕ → ℝ} (hI : ∀ j, 0 ≤ psiI j) (k : ℕ) (L : ℝ) :
    0 ≤ qvPhiTilde psiI psiA k L := by
  unfold qvPhiTilde
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _
  · exact mul_nonneg (hI 4) (Real.sqrt_nonneg _)

theorem qvPhiMid_nonneg {psiI : ℕ → ℝ} (hI : ∀ j, 0 ≤ psiI j) (k j : ℕ) {L : ℝ} (hL : 0 < L) :
    0 ≤ qvPhiMid psiI k j L := by
  unfold qvPhiMid
  have := Real.rpow_nonneg hL.le (-(lossAlpha k - lossAlpha (k - j + 1)))
  have := hI (k - j + 1)
  positivity

/-- A middle term of `φ^{iso,qv}_k` is at most `φ^{iso,qv}_k`. -/
theorem qvPhiMid_le_phiIso {psiI psiA : ℕ → ℝ} (hI : ∀ j, 0 ≤ psiI j) {k j : ℕ} {L : ℝ}
    (hL : 0 < L) (hj : j ∈ Finset.Icc 2 ((k + 1) / 2)) :
    qvPhiMid psiI k j L ≤ qvPhiIso psiI psiA k L := by
  unfold qvPhiIso
  have h1 : qvPhiMid psiI k j L ≤ ∑ i ∈ Finset.Icc 2 ((k + 1) / 2), qvPhiMid psiI k i L :=
    Finset.single_le_sum (fun i _ => qvPhiMid_nonneg hI k i hL) hj
  have h2 : 0 ≤ psiI k * Real.sqrt (psiI 2) * L ^ (-(1 / 4 : ℝ)) := by
    have := Real.rpow_nonneg hL.le (-(1 / 4 : ℝ))
    have := hI k
    positivity
  have h3 := qvPhiTilde_nonneg (psiA := psiA) hI k L
  linarith

/-!
## The cases
-/

section Cases

variable {d : VSData} {P : PsiData N} {psiI psiA : ℕ → ℝ} {LamM s : ℝ}
  {H : Matrix (Fin N) (Fin N) ℂ} (hin : QVInputs d P s) (hA : APriori P psiI psiA LamM s H)
  (hH : H.IsHermitian) (hLam : 1 ≤ LamM) (hI : ∀ j, 1 ≤ psiI j) (hAv : ∀ j, 0 ≤ psiA j)
  (hL1 : 1 ≤ P.lEta s)
include hin hA hH hLam hI hAv hL1

omit hAv in
/-- **`2 ≤ j`, `2j ≤ 8`**: with `G₁ = W(β₀, r₁ ++ [(c, β)])`
(length `j = |r₁| + 2`) and `G₂ = W(β, r₂)` (length `k - j + 1`), `k = |r₁| + |r₂| + 2 ≤ 8`. -/
theorem qv_QV_iso_mid_direct (β₀ : Bool) (r₁ : List (Fin N × Bool)) (c : Fin N) (β : Bool)
    (r₂ : List (Fin N × Bool)) (hj : 2 * (r₁.length + 2) ≤ 8)
    (hk : r₁.length + r₂.length + 2 ≤ 8) (a b : Fin N) :
    qvQIso P (qvW P s H β₀ (r₁ ++ [(c, β)])) (qvW P s H β r₂) a b ≤
      4 * (d.C0 + 1) * d.C1pp * d.Cwc * LamM ^ 3 *
        qvPhiMid psiI (r₁.length + r₂.length + 2) (r₁.length + 2) (P.lEta s) ^ 2 *
          P.lEta s ^ (2 * lossAlpha (r₁.length + r₂.length + 2)) / vsHeight P.z s *
            qvIsoSq P s a (r₁.map Prod.fst ++ c :: r₂.map Prod.fst) b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  set G₁ := qvW P s H β₀ (r₁ ++ [(c, β)])
  set u₁ := (r₁ ++ [(c, β)]).map Prod.fst
  set u₂ := r₂.map Prod.fst
  set A := qvAdj β₀ (r₁ ++ [(c, β)])
  set j := r₁.length + 2
  set k := r₁.length + r₂.length + 2
  have hlen1 : ∀ c', ((r₁ ++ [(c, β)]) ++ (c', A.1) :: A.2).length + 1 = 2 * j := by
    intro c'
    simp only [A, j, List.length_append, List.length_cons, qvAdj_length, List.length_nil]
    omega
  have hsites1 : ∀ c', ((r₁ ++ [(c, β)]) ++ (c', A.1) :: A.2).map Prod.fst =
      u₁ ++ c' :: u₁.reverse := by
    intro c'
    simp only [List.map_append, List.map_cons, A, qvAdj_sites, u₁]
  set F := 1 + psiI (2 * j) * P.lEta s ^ (-(1 / 2 - lossAlpha (2 * j)))
  have hF : 0 ≤ F := by
    have := Real.rpow_nonneg hL.le (-(1 / 2 - lossAlpha (2 * j))); nlinarith [hI (2 * j)]
  -- the left factor
  have hleft : ∀ c', ∑ d, P.S c' d * ‖G₁ a d‖ ^ 2 ≤ LamM * F * qvIsoSq P s a u₁ c' := by
    intro c'
    rw [qv_sandwich_right_re]
    have hW : G₁ * obsMat P.S c' * G₁ᴴ = qvW P s H β₀ ((r₁ ++ [(c, β)]) ++ (c', A.1) :: A.2) := by
      rw [qvW_append, qvW_conjTranspose P s hH]
    have h := hA.word_iso hU hL hLam β₀ ((r₁ ++ [(c, β)]) ++ (c', A.1) :: A.2)
      (by rw [hlen1]; linarith [hI (2 * j)]) (by rw [hlen1]; omega) a a
    rw [hlen1, hsites1, qv_ite_pos rfl, qvIsoSq_double' P s hin.symm, ← hW,
      qv_sqrt_inv_sq hL (qvIsoSq_nonneg P s hU hL a u₁ c')] at h
    refine (Complex.re_le_norm _).trans (h.trans_eq ?_)
    have hs : 0 < Real.sqrt (P.lEta s) := Real.sqrt_pos.mpr hL
    unfold F
    rw [← qv_rpow_div_sqrt hL]
    field_simp
  -- the right factor
  have hlen2 : r₂.length + 1 = k - j + 1 := by omega
  set ψ := psiI (k - j + 1) with hψdef
  set g := P.lEta s ^ lossAlpha (k - j + 1) with hgdef
  have hright : ∀ c', ‖qvW P s H β r₂ c' b‖ ^ 2 ≤
      2 * LamM ^ 2 * ((if c' = b then P.lEta s else 0) + ψ ^ 2 * g ^ 2) * qvIsoSq P s c' u₂ b := by
    intro c'
    have h := hA.word_iso_sq hU hL hLam β r₂ (by rw [hlen2]; linarith [hI (k - j + 1)])
      (by omega) c' b
    rwa [hlen2] at h
  have hterm : ∀ c', (∑ d, P.S c' d * ‖G₁ a d‖ ^ 2) * ‖qvW P s H β r₂ c' b‖ ^ 2 ≤
      2 * LamM ^ 3 * F * ((if c' = b then P.lEta s * (qvIsoSq P s a u₁ c' *
        qvIsoSq P s c' u₂ b) else 0) + ψ ^ 2 * g ^ 2 *
          (qvIsoSq P s a u₁ c' * qvIsoSq P s c' u₂ b)) := by
    intro c'
    have h0 : 0 ≤ ∑ d, P.S c' d * ‖G₁ a d‖ ^ 2 :=
      Finset.sum_nonneg fun d _ => mul_nonneg (hin.sNonneg _ _) (sq_nonneg _)
    have h1 := mul_le_mul (hleft c') (hright c') (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by linarith) hF) (qvIsoSq_nonneg P s hU hL a u₁ c'))
    refine h1.trans (le_of_eq ?_)
    split_ifs <;> ring
  rw [qv_sum_split_first]
  have hsum := Finset.sum_le_sum fun c' (_ : c' ∈ Finset.univ) => hterm c'
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ b,
    qv_ite_pos (Finset.mem_univ b), ← Finset.mul_sum] at hsum
  refine hsum.trans ?_
  have hu : u₁ ++ u₂ = r₁.map Prod.fst ++ c :: r₂.map Prod.fst := by simp [u₁, u₂]
  have hc3 := qvIsoConcat hin a u₁ b u₂ b
  have hc2 := qvIsoQj hin a u₁ u₂ b
  rw [hu] at hc3 hc2
  set q := qvIsoSq P s a (r₁.map Prod.fst ++ c :: r₂.map Prod.fst) b
  have hq := qvIsoSq_nonneg P s hU hL a (r₁.map Prod.fst ++ c :: r₂.map Prod.fst) b
  have hc3' : P.lEta s * (qvIsoSq P s a u₁ b * qvIsoSq P s b u₂ b) ≤ d.C1pp * q := by
    have := mul_le_mul_of_nonneg_left hc3 hL.le
    calc _ ≤ P.lEta s * (d.C1pp / P.lEta s * q) := this
      _ = _ := by field_simp
  have hψ : 1 ≤ ψ := hI _
  have hg : 1 ≤ g := qv_one_le_rpow hL1 (qv_alpha_nonneg _)
  have hX0 : 0 ≤ ψ ^ 2 * g ^ 2 := by positivity
  have hstep : 2 * LamM ^ 3 * F * (P.lEta s * (qvIsoSq P s a u₁ b * qvIsoSq P s b u₂ b) +
      ψ ^ 2 * g ^ 2 * ∑ c', qvIsoSq P s a u₁ c' * qvIsoSq P s c' u₂ b) ≤
      2 * LamM ^ 3 * F * (d.C1pp * q + ψ ^ 2 * g ^ 2 * (d.Cwc / vsHeight P.z s * q)) :=
    mul_le_mul_of_nonneg_left (add_le_add hc3' (mul_le_mul_of_nonneg_left hc2 hX0))
      (by positivity)
  refine hstep.trans ((qv_arith_mid hLam hF hψ hg d.one_le_C1pp d.one_le_Cwc hin.height_pos
    hin.height_le (by linarith [d.C0_ge_one]) hq).trans (le_of_eq ?_))
  -- `φ_mid² L^{2α_k} = F ψ² g²`
  have hmid : qvPhiMid psiI k j (P.lEta s) ^ 2 * P.lEta s ^ (2 * lossAlpha k) =
      F * ψ ^ 2 * g ^ 2 := by
    unfold qvPhiMid
    rw [mul_pow, mul_pow, Real.sq_sqrt hF, qv_rpow_sq hL, qv_rpow_sq hL]
    have e : P.lEta s ^ (2 * -(lossAlpha k - lossAlpha (k - j + 1))) *
        P.lEta s ^ (2 * lossAlpha k) = g ^ 2 := by
      rw [← Real.rpow_add hL, qv_rpow_sq hL]
      congr 1
      ring
    calc psiI (k - j + 1) ^ 2 * P.lEta s ^ (2 * -(lossAlpha k - lossAlpha (k - j + 1))) * F *
          P.lEta s ^ (2 * lossAlpha k)
        = psiI (k - j + 1) ^ 2 * F * (P.lEta s ^ (2 * -(lossAlpha k - lossAlpha (k - j + 1))) *
          P.lEta s ^ (2 * lossAlpha k)) := by ring
      _ = _ := by rw [e, hψdef, hgdef, qv_rpow_sq hL]; ring
  calc 4 * (d.C0 + 1) * d.C1pp * d.Cwc * LamM ^ 3 * (F * ψ ^ 2 * g ^ 2) / vsHeight P.z s * q
      = 4 * (d.C0 + 1) * d.C1pp * d.Cwc * LamM ^ 3 *
          (qvPhiMid psiI k j (P.lEta s) ^ 2 * P.lEta s ^ (2 * lossAlpha k)) /
            vsHeight P.z s * q := by rw [hmid]
    _ = _ := by ring

/-- **The isotropic quadratic variation, first term `j = 1`** (VS form), under the hypotheses
`Split.ExplicitShortStatement` (`hES`, proved as `MTerms.explicitShort_holds`) and (K1) for the
stability operator (`hstab`, supplied by `qv_stabOp_le` in VS form): for `k = |r| + 1 ≤ 8`,
`Σ_{c,e} S_ce |(G_1)_ae|² |W(β₀,r)_cb|² ≤ 𝔠 Λ_M³ (φ^{iso,qv}_k)² L^{2α_k} η⁻¹ s(a, r.map fst, b)²`.
-/
theorem qv_QV_iso_first (hES : Split.ExplicitShortStatement) (hS : StochasticSymm P.S)
    (hz : P.z.im ≠ 0) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hstab : ∀ x y, ‖Split.stabOp s P.S (semicircleM P.z * conj (semicircleM P.z)) x y‖ ≤
      (if x = y then 1 else 0) + Propagator.vsCK d * P.ups s x y)
    (β₀ : Bool) (r : List (Fin N × Bool)) (hk : r.length + 1 ≤ 8) (a b : Fin N) :
    qvQIso P (qvRes P s H β₀) (qvW P s H β₀ r) a b ≤
      qvC d * LamM ^ 3 * qvPhiIso psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
        P.lEta s ^ (2 * lossAlpha (r.length + 1)) / vsHeight P.z s *
          qvIsoSq P s a (r.map Prod.fst) b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  have hη := hin.height_pos
  set m := semicircleM P.z
  set W := qvW P s H β₀ r
  set u := r.map Prod.fst
  set q := qvIsoSq P s a u b
  have hq := qvIsoSq_nonneg P s hU hL a u b
  -- the two-chain `G_1 S^c G_1ᴴ`
  have hXc : ∀ c, ∑ e, P.S c e * ‖qvRes P s H β₀ a e‖ ^ 2 =
      ((qvW P s H β₀ [(c, !β₀)]) a a).re := by
    intro c
    rw [qv_sandwich_right_re, qvRes_conjTranspose P s hH, qvW_cons, qvW_nil]
  set M : Fin N → ℂ := fun c => P.mChain (qvSig β₀ [(c, !β₀)]) (qvSites [(c, !β₀)] a) s a
  have hXM : ∀ c, ‖(qvW P s H β₀ [(c, !β₀)]) a a - M c‖ ≤
      psiI 2 * (P.ups s a c / Real.sqrt (P.lEta s)) := by
    intro c
    have h := hA.word_iso_err hU hL β₀ [(c, !β₀)] (by simp) a a
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil] at h
    rw [qv_alpha_of_le_four (by norm_num), Real.rpow_zero, mul_one, qvIsoSq_cons, qvIsoSq_nil,
      hin.symm c a, show (P.lEta s)⁻¹ * P.ups s a c * P.ups s a c =
        (P.lEta s)⁻¹ * P.ups s a c ^ 2 by ring, qv_sqrt_inv_sq hL (hU a c)] at h
    exact h
  have hM : ∀ c, M c = m * conj m * ∑ e, Split.stabOp s P.S (m * conj m) a e * (P.S c e : ℂ) := by
    intro c
    simp only [M]
    rw [qv_mChain_two hES P hS hz hs β₀ (!β₀) c a a, qv_patConj_mul_not]
  -- `f c = |W_cb|²`
  set α := lossAlpha (r.length + 1)
  have hf : ∀ c, ‖W c b‖ ^ 2 ≤ 2 * LamM ^ 2 * ((if c = b then P.lEta s else 0) +
      psiI (r.length + 1) ^ 2 * (P.lEta s ^ α) ^ 2) * qvIsoSq P s c u b :=
    fun c => hA.word_iso_sq hU hL hLam β₀ r (by linarith [hI (r.length + 1)]) hk c b
  -- decomposition: `Q ≤ Σ_c |X_c - M_c| f_c + Re Σ_c M_c f_c`
  have hdec : qvQIso P (qvRes P s H β₀) W a b ≤
      ∑ c, psiI 2 * (P.ups s a c / Real.sqrt (P.lEta s)) * ‖W c b‖ ^ 2 +
        ‖∑ c, M c * ((‖W c b‖ ^ 2 : ℝ) : ℂ)‖ := by
    rw [qv_sum_split_first]
    simp_rw [hXc]
    have hre : ∀ c, ((qvW P s H β₀ [(c, !β₀)]) a a).re * ‖W c b‖ ^ 2 ≤
        psiI 2 * (P.ups s a c / Real.sqrt (P.lEta s)) * ‖W c b‖ ^ 2 +
          (M c * ((‖W c b‖ ^ 2 : ℝ) : ℂ)).re := by
      intro c
      have h1 : ((qvW P s H β₀ [(c, !β₀)]) a a).re ≤
          ‖(qvW P s H β₀ [(c, !β₀)]) a a - M c‖ + (M c).re := by
        have := Complex.re_le_norm ((qvW P s H β₀ [(c, !β₀)]) a a - M c)
        rw [Complex.sub_re] at this
        linarith
      have h2 := mul_le_mul_of_nonneg_right (h1.trans (add_le_add (hXM c) le_rfl))
        (sq_nonneg ‖W c b‖)
      rw [Complex.re_mul_ofReal]
      linarith
    refine (Finset.sum_le_sum fun c _ => hre c).trans ?_
    rw [Finset.sum_add_distrib, ← Complex.re_sum]
    exact add_le_add le_rfl (Complex.re_le_norm _)
  -- the M-part through `Q̃`
  have hMsum : ∑ c, M c * ((‖W c b‖ ^ 2 : ℝ) : ℂ) =
      m * conj m * ∑ e, Split.stabOp s P.S (m * conj m) a e * ((qvQTilde P W e b : ℝ) : ℂ) := by
    calc ∑ c, M c * ((‖W c b‖ ^ 2 : ℝ) : ℂ)
        = ∑ c, ∑ e, m * conj m * Split.stabOp s P.S (m * conj m) a e * (P.S c e : ℂ) *
            ((‖W c b‖ ^ 2 : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hM, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
      _ = ∑ e, ∑ c, m * conj m * Split.stabOp s P.S (m * conj m) a e * (P.S c e : ℂ) *
            ((‖W c b‖ ^ 2 : ℝ) : ℂ) := Finset.sum_comm
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [qvQTilde, Complex.ofReal_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hin.sSymm c e]
          push_cast
          ring
  have hmm : ‖m * conj m‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    have h1 := (norm_semicircleM_lt_one hz).le
    nlinarith [norm_nonneg m]
  have hT0 : ∀ e, 0 ≤ qvQTilde P W e b := fun e => qvQTilde_nonneg P hin.sNonneg W e b
  have hMnorm : ‖∑ c, M c * ((‖W c b‖ ^ 2 : ℝ) : ℂ)‖ ≤
      ∑ e, ((if a = e then 1 else 0) + Propagator.vsCK d * P.ups s a e) * qvQTilde P W e b := by
    rw [hMsum, norm_mul]
    calc ‖m * conj m‖ * ‖∑ e, Split.stabOp s P.S (m * conj m) a e *
          ((qvQTilde P W e b : ℝ) : ℂ)‖
        ≤ 1 * ∑ e, ‖Split.stabOp s P.S (m * conj m) a e‖ * qvQTilde P W e b := by
          apply mul_le_mul hmm _ (norm_nonneg _) zero_le_one
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun e _ => ?_))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hT0 e)]
      _ ≤ _ := by
          rw [one_mul]
          exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hstab a e) (hT0 e)
  -- `Q̃` bound and the `Υ`-convolution
  set Tt := qvPhiTilde psiI psiA (r.length + 1) (P.lEta s) ^ 2 * P.lEta s ^ (2 * α)
  have hTt0 : 0 ≤ Tt := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hL.le _)
  have htil : ∀ e, qvQTilde P W e b ≤ 4 * qvCS d * d.C1pp * LamM ^ 3 * Tt * qvIsoSq P s e u b := by
    intro e
    have h := qv_tilde hin hA hH hLam hI hAv hL1 β₀ r hk e b
    refine h.trans (le_of_eq ?_)
    unfold Tt
    ring
  have hconv := qvIsoQj hin a [] u b
  simp only [qvIsoSq_nil, List.nil_append] at hconv
  have hcat := qvIsoConcat hin a [] b u b
  simp only [qvIsoSq_nil, List.nil_append] at hcat
  have hCK := (Propagator.vsCK_pos d).le
  have hK0 : 0 ≤ 4 * qvCS d * d.C1pp * LamM ^ 3 * Tt := by
    have := qvCS_ge_one d
    have := d.one_le_C1pp
    positivity
  have hsecond : ∑ e, ((if a = e then 1 else 0) + Propagator.vsCK d * P.ups s a e) *
      qvQTilde P W e b ≤ 4 * qvCS d * d.C1pp * LamM ^ 3 * Tt *
        (q + Propagator.vsCK d * (d.Cwc / vsHeight P.z s * q)) := by
    have hterm : ∀ e, ((if a = e then 1 else 0) + Propagator.vsCK d * P.ups s a e) *
        qvQTilde P W e b ≤ 4 * qvCS d * d.C1pp * LamM ^ 3 * Tt *
          ((if a = e then qvIsoSq P s e u b else 0) +
            Propagator.vsCK d * (P.ups s a e * qvIsoSq P s e u b)) := by
      intro e
      have h0 : 0 ≤ (if a = e then (1 : ℝ) else 0) + Propagator.vsCK d * P.ups s a e := by
        have := mul_nonneg hCK (hU a e)
        split_ifs <;> linarith
      have h1 := mul_le_mul_of_nonneg_left (htil e) h0
      refine h1.trans (le_of_eq ?_)
      split_ifs <;> ring
    have hsum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) => hterm e
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ a,
      qv_ite_pos (Finset.mem_univ a), ← Finset.mul_sum] at hsum
    refine hsum.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hconv hCK)
  -- the first part
  set X := psiI (r.length + 1) ^ 2 * (P.lEta s ^ α) ^ 2
  have hfirst : ∑ c, psiI 2 * (P.ups s a c / Real.sqrt (P.lEta s)) * ‖W c b‖ ^ 2 ≤
      psiI 2 * (1 / Real.sqrt (P.lEta s)) *
        (2 * LamM ^ 2 * (d.C1pp * q + X * (d.Cwc / vsHeight P.z s * q))) := by
    have hterm : ∀ c, psiI 2 * (P.ups s a c / Real.sqrt (P.lEta s)) * ‖W c b‖ ^ 2 ≤
        psiI 2 * (1 / Real.sqrt (P.lEta s)) * (2 * LamM ^ 2 *
          ((if c = b then P.lEta s * (P.ups s a c * qvIsoSq P s c u b) else 0) +
            X * (P.ups s a c * qvIsoSq P s c u b))) := by
      intro c
      have h0 : 0 ≤ psiI 2 * (P.ups s a c / Real.sqrt (P.lEta s)) :=
        mul_nonneg (by linarith [hI 2]) (div_nonneg (hU a c) (Real.sqrt_nonneg _))
      have h1 := mul_le_mul_of_nonneg_left (hf c) h0
      refine h1.trans (le_of_eq ?_)
      split_ifs <;> ring
    have hsum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hterm c
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq'
      Finset.univ b, qv_ite_pos (Finset.mem_univ b), ← Finset.mul_sum] at hsum
    refine hsum.trans ?_
    have hX0 : 0 ≤ X := by positivity
    have h2 : P.lEta s * (P.ups s a b * qvIsoSq P s b u b) ≤ d.C1pp * q := by
      have := mul_le_mul_of_nonneg_left hcat hL.le
      calc _ ≤ P.lEta s * (d.C1pp / P.lEta s * q) := this
        _ = _ := by field_simp
    have h3 := add_le_add h2 (mul_le_mul_of_nonneg_left hconv hX0)
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * LamM ^ 2)
    exact mul_le_mul_of_nonneg_left h4
      (mul_nonneg (by linarith [hI 2]) (by positivity))
  have hQ := hdec.trans (add_le_add hfirst (hMnorm.trans hsecond))
  have hfin := qv_arith_first hLam (by linarith [hI 2]) (by positivity)
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (hI _))
      (one_le_pow₀ (qv_one_le_rpow hL1 (qv_alpha_nonneg _)))) d.one_le_C1pp d.one_le_Cwc
    (qvCS_ge_one d) hCK (by linarith [d.C0_ge_one]) hη hin.height_le hq hTt0 hQ
  refine hfin.trans ?_
  -- `ψ₂ L^{-1/2} X + Tt ≤ φ_iso² L^{2α}`
  have hT1 : psiI 2 * (1 / Real.sqrt (P.lEta s)) * X =
      (psiI (r.length + 1) * Real.sqrt (psiI 2) * P.lEta s ^ (-(1 / 4 : ℝ))) ^ 2 *
        P.lEta s ^ (2 * α) := by
    have e1 : 1 / Real.sqrt (P.lEta s) = P.lEta s ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hL.le, one_div]
    have e2 : (P.lEta s ^ (-(1 / 4 : ℝ))) ^ 2 = P.lEta s ^ (-(1 / 2 : ℝ)) := by
      rw [qv_rpow_sq hL]
      norm_num
    unfold X
    rw [e1, mul_pow, mul_pow, Real.sq_sqrt (by linarith [hI 2]), e2, qv_rpow_sq hL α]
    ring
  have hmid0 : 0 ≤ ∑ j ∈ Finset.Icc 2 ((r.length + 1 + 1) / 2),
      qvPhiMid psiI (r.length + 1) j (P.lEta s) := by
    refine Finset.sum_nonneg fun j _ => ?_
    unfold qvPhiMid
    have := hI (r.length + 1 - j + 1)
    have := Real.rpow_nonneg hL.le (-(lossAlpha (r.length + 1) - lossAlpha (r.length + 1 - j + 1)))
    positivity
  have hT10 : 0 ≤ psiI (r.length + 1) * Real.sqrt (psiI 2) * P.lEta s ^ (-(1 / 4 : ℝ)) := by
    have := hI (r.length + 1)
    have := Real.rpow_nonneg hL.le (-(1 / 4 : ℝ))
    positivity
  have hφt0 : 0 ≤ qvPhiTilde psiI psiA (r.length + 1) (P.lEta s) := by
    unfold qvPhiTilde
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
    · exact mul_nonneg (by linarith [hI 4]) (Real.sqrt_nonneg _)
  have hsq : (psiI (r.length + 1) * Real.sqrt (psiI 2) * P.lEta s ^ (-(1 / 4 : ℝ))) ^ 2 +
      qvPhiTilde psiI psiA (r.length + 1) (P.lEta s) ^ 2 ≤
      qvPhiIso psiI psiA (r.length + 1) (P.lEta s) ^ 2 := by
    unfold qvPhiIso
    nlinarith
  have hLa := Real.rpow_nonneg hL.le (2 * α)
  have hcomb : psiI 2 * (1 / Real.sqrt (P.lEta s)) * X + Tt ≤
      qvPhiIso psiI psiA (r.length + 1) (P.lEta s) ^ 2 * P.lEta s ^ (2 * α) := by
    rw [hT1]
    unfold Tt
    nlinarith
  have hc0 : 0 ≤ 4 * (d.C0 + 1) * (1 + qvCS d) * (1 + Propagator.vsCK d) * d.C1pp * d.Cwc *
      LamM ^ 3 := by
    have := qvCS_ge_one d
    have := d.one_le_C1pp
    have := d.one_le_Cwc
    have := d.C0_ge_one
    positivity
  have hηq : 0 ≤ 1 / vsHeight P.z s * q := by positivity
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomb hc0) hηq
  calc _ = 4 * (d.C0 + 1) * (1 + qvCS d) * (1 + Propagator.vsCK d) * d.C1pp * d.Cwc *
        LamM ^ 3 * (psiI 2 * (1 / Real.sqrt (P.lEta s)) * X + Tt) * (1 / vsHeight P.z s * q) := by
        ring
    _ ≤ _ := this
    _ = _ := by unfold qvC; ring

/-- **The isotropic quadratic variation, terms `j ≥ 2`**: for `r = r₁ ++ (c, β) :: r₂` of
length `k ≤ 8`, `Σ_{c',e} S_{c'e} |G_{[1,j]}(a,e)|² |G_{[j,k]}(c',b)|² ≤
𝔠 Λ_M³ (φ^{iso,qv}_k)² L^{2α_k} η⁻¹ s(a, r.map fst, b)²`, `j = |r₁| + 2`. For
`j ≤ ⌊(k+1)/2⌋` this is `qv_QV_iso_mid_direct`; otherwise the symmetry `qvQIso_symm` maps it to
`j* = k + 1 - j` of the adjoint chain (`qv_QV_iso_first` when `j = k`). -/
theorem qv_QV_iso_mid (hES : Split.ExplicitShortStatement) (hS : StochasticSymm P.S)
    (hz : P.z.im ≠ 0) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hstab : ∀ x y, ‖Split.stabOp s P.S (semicircleM P.z * conj (semicircleM P.z)) x y‖ ≤
      (if x = y then 1 else 0) + Propagator.vsCK d * P.ups s x y)
    (β₀ : Bool) (r₁ : List (Fin N × Bool)) (c : Fin N) (β : Bool) (r₂ : List (Fin N × Bool))
    (hk : r₁.length + r₂.length + 2 ≤ 8) (a b : Fin N) :
    qvQIso P (qvW P s H β₀ (r₁ ++ [(c, β)])) (qvW P s H β r₂) a b ≤
      qvC d * LamM ^ 3 * qvPhiIso psiI psiA (r₁.length + r₂.length + 2) (P.lEta s) ^ 2 *
        P.lEta s ^ (2 * lossAlpha (r₁.length + r₂.length + 2)) / vsHeight P.z s *
          qvIsoSq P s a (r₁.map Prod.fst ++ c :: r₂.map Prod.fst) b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  have hη := hin.height_pos
  have hI0 : ∀ j, 0 ≤ psiI j := fun j => by linarith [hI j]
  have hcm : 4 * (d.C0 + 1) * d.C1pp * d.Cwc ≤ qvC d := by
    obtain ⟨hC1, hCw, hCS, hCK, hC0⟩ := qvC_facts d
    unfold qvC
    calc 4 * (d.C0 + 1) * d.C1pp * d.Cwc = 4 * (d.C0 + 1) * 1 * 1 * d.C1pp * d.Cwc := by ring
      _ ≤ _ := by gcongr <;> linarith
  have hcm0 : 0 ≤ 4 * (d.C0 + 1) * d.C1pp * d.Cwc := by
    obtain ⟨hC1, hCw, hCS, hCK, hC0⟩ := qvC_facts d
    positivity
  set k := r₁.length + r₂.length + 2
  have hRk : 0 ≤ P.lEta s ^ (2 * lossAlpha k) / vsHeight P.z s *
      qvIsoSq P s a (r₁.map Prod.fst ++ c :: r₂.map Prod.fst) b := by
    have := Real.rpow_nonneg hL.le (2 * lossAlpha k)
    have := qvIsoSq_nonneg P s hU hL a (r₁.map Prod.fst ++ c :: r₂.map Prod.fst) b
    positivity
  have hΛ3 : 0 ≤ LamM ^ 3 := by positivity
  by_cases hdir : 2 * (r₁.length + 2) ≤ k + 1
  · have h := qv_QV_iso_mid_direct hin hA hH hLam hI hL1 β₀ r₁ c β r₂ (by omega) hk a b
    have hj : r₁.length + 2 ∈ Finset.Icc 2 ((k + 1) / 2) := by
      rw [Finset.mem_Icc]; constructor <;> omega
    have hle := qvPhiMid_le_phiIso (psiA := psiA) hI0 hL hj
    have hm0 := qvPhiMid_nonneg hI0 k (r₁.length + 2) hL
    have hsq := pow_le_pow_left₀ hm0 hle 2
    refine h.trans (le_of_eq_of_le (by ring) ((qv_scale2 hcm hcm0 hsq (sq_nonneg _)
      (mul_nonneg hΛ3 hRk)).trans_eq (by ring)))
  · rw [qvQIso_symm P hin.sSymm]
    have hfst := qvAdj_fst_snoc β₀ r₁ c β
    have h1 : (qvW P s H β₀ (r₁ ++ [(c, β)]))ᴴ =
        qvW P s H (!β) (qvAdj β₀ (r₁ ++ [(c, β)])).2 := by
      rw [qvW_conjTranspose P s hH, hfst]
    rw [h1]
    have hsR : ((qvAdj β₀ (r₁ ++ [(c, β)])).2).map Prod.fst = c :: (r₁.map Prod.fst).reverse := by
      rw [qvAdj_sites]; simp
    have hlR : ((qvAdj β₀ (r₁ ++ [(c, β)])).2).length = r₁.length + 1 := by
      rw [qvAdj_length]; simp
    cases r₂ with
    | nil =>
      have h2 : (qvW P s H β [])ᴴ = qvRes P s H (!β) := by
        rw [qvW_nil, qvRes_conjTranspose P s hH]
      rw [h2]
      have h := qv_QV_iso_first hin hA hH hLam hI hAv hL1 hES hS hz hs hstab (!β)
        (qvAdj β₀ (r₁ ++ [(c, β)])).2 (by rw [hlR]; simp [k] at hk ⊢; omega) b a
      rw [hlR, hsR] at h
      have hrev : qvIsoSq P s b (c :: (r₁.map Prod.fst).reverse) a =
          qvIsoSq P s a (r₁.map Prod.fst ++ [c]) b := by
        rw [qvIsoSq_reverse P s hin.symm a]
        simp
      rw [hrev] at h
      refine h.trans (le_of_eq ?_)
      simp [k]
    | cons q2 r₂' =>
      obtain ⟨c₂, β₂⟩ := q2
      have h2 : (qvW P s H β ((c₂, β₂) :: r₂'))ᴴ =
          qvW P s H (qvAdj β₂ r₂').1 ((qvAdj β₂ r₂').2 ++ [(c₂, !β)]) := by
        rw [qvW_conjTranspose P s hH]
        rfl
      rw [h2]
      have hlR2 : (qvAdj β₂ r₂').2.length = r₂'.length := qvAdj_length β₂ r₂'
      have hk' : r₁.length + r₂'.length + 3 ≤ 8 := by
        have := hk; simp only [k, List.length_cons] at this; omega
      have hdir' : ¬ 2 * (r₁.length + 2) ≤ r₁.length + r₂'.length + 4 := by
        have := hdir; simp only [k, List.length_cons] at this; omega
      have hj2 : 2 * ((qvAdj β₂ r₂').2.length + 2) ≤ 8 := by rw [hlR2]; omega
      have hk2 : (qvAdj β₂ r₂').2.length + (qvAdj β₀ (r₁ ++ [(c, β)])).2.length + 2 ≤ 8 := by
        rw [hlR2, hlR]; omega
      have h := qv_QV_iso_mid_direct hin hA hH hLam hI hL1 (qvAdj β₂ r₂').1 (qvAdj β₂ r₂').2
        c₂ (!β) (qvAdj β₀ (r₁ ++ [(c, β)])).2 hj2 hk2 b a
      have hkk : (qvAdj β₂ r₂').2.length + (qvAdj β₀ (r₁ ++ [(c, β)])).2.length + 2 = k := by
        rw [hlR2, hlR]; simp only [k, List.length_cons]; omega
      rw [hkk, hsR, qvAdj_sites] at h
      have hrev : qvIsoSq P s b
          ((r₂'.map Prod.fst).reverse ++ c₂ :: c :: (r₁.map Prod.fst).reverse) a
          = qvIsoSq P s a (r₁.map Prod.fst ++ c :: List.map Prod.fst ((c₂, β₂) :: r₂')) b := by
        rw [qvIsoSq_reverse P s hin.symm a]
        simp
      rw [hrev] at h
      have hj : (qvAdj β₂ r₂').2.length + 2 ∈ Finset.Icc 2 ((k + 1) / 2) := by
        rw [Finset.mem_Icc, hlR2]; constructor
        · omega
        · simp only [k, List.length_cons]; omega
      have hle := qvPhiMid_le_phiIso (psiA := psiA) hI0 hL hj
      have hm0 := qvPhiMid_nonneg hI0 k ((qvAdj β₂ r₂').2.length + 2) hL
      have hsq := pow_le_pow_left₀ hm0 hle 2
      refine h.trans (le_of_eq_of_le (by ring) ((qv_scale2 hcm hcm0 hsq (sq_nonneg _)
        (mul_nonneg hΛ3 hRk)).trans_eq (by ring)))

end Cases

end BlockBand.Native.ErdosRiabov.QV
