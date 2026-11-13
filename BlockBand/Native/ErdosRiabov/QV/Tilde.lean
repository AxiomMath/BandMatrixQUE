module

public import BlockBand.Native.ErdosRiabov.QV.Av

/-!
# Quadratic variation: the auxiliary quantity `Q̃` of the isotropic `j = 1` decomposition

For an isotropic word `W = W(β₀, r)` of length `k = |r| + 1 ≤ 8` with internal sites
`u = r.map fst`, `qvQTilde P W d b = Σ_c S_dc |W_cb|²` (the Erdős–Riabov `Q̃` without `|m|²`).
Under
`APriori` (explicit hypothesis):

  `Q̃(d, b) ≤ 4 C_S C₁ Λ_M³ (φ̃^{iso,qv}_k)² L^{2α_k} s(d, u, b)²`   (`qv_tilde`),

by three cases: `k ≤ 4` (the doubled chain `Wᴴ S^d W`, the doubling identity); `5 ≤ k ≤ 7`
(the split `W = G_1 S^{x_1} W'`, `Q̃ = Σ_q S_{x_1q} W'_qb conj((G_1ᴴ S^d W)_qb)`, then
`qvSSchwarz` and `qvSTriangle` in the chain form `qvSChain`); `k = 8` (the cut
`W = Y S^{x_4} X` and the reduction inequality).
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

/-- `Q̃(d, b) = Σ_c S_dc |W_cb|²`. -/
def qvQTilde (P : PsiData N) (W : Matrix (Fin N) (Fin N) ℂ) (d b : Fin N) : ℝ :=
  ∑ c, P.S d c * ‖W c b‖ ^ 2

theorem qvQTilde_nonneg (P : PsiData N) (hS : ∀ x y, 0 ≤ P.S x y)
    (W : Matrix (Fin N) (Fin N) ℂ) (d b : Fin N) : 0 ≤ qvQTilde P W d b :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (hS _ _) (sq_nonneg _)

theorem qvQTilde_eq_re (P : PsiData N) (W : Matrix (Fin N) (Fin N) ℂ) (d b : Fin N) :
    qvQTilde P W d b = ((Wᴴ * obsMat P.S d * W) b b).re := by
  rw [qv_sandwich_left, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- The split identity for `5 ≤ k ≤ 7`: for `W = R S^{x} W'`,
`Σ_c S_dc |W_cb|² = Σ_q S_xq W'_qb conj((Rᴴ S^d W)_qb)`. -/
theorem qv_tilde_split (S : Matrix (Fin N) (Fin N) ℝ) (R W' : Matrix (Fin N) (Fin N) ℂ)
    (x d b : Fin N) :
    ((∑ c, S d c * ‖(R * obsMat S x * W') c b‖ ^ 2 : ℝ) : ℂ) =
      ∑ q, (S x q : ℂ) * W' q b * conj ((Rᴴ * obsMat S d * (R * obsMat S x * W')) q b) := by
  set W := R * obsMat S x * W'
  have hW : ∀ c, W c b = ∑ q, R c q * (S x q : ℂ) * W' q b := fun c =>
    qv_mul_obs_apply S R W' x c b
  have hcB : ∀ q, conj ((Rᴴ * obsMat S d * W) q b) =
      ∑ c, R c q * (S d c : ℂ) * conj (W c b) := by
    intro q
    rw [qv_mul_obs_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Matrix.conjTranspose_apply, map_mul, Complex.conj_ofReal]
  symm
  calc ∑ q, (S x q : ℂ) * W' q b * conj ((Rᴴ * obsMat S d * W) q b)
      = ∑ q, ∑ c, (S x q : ℂ) * W' q b * (R c q * (S d c : ℂ) * conj (W c b)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hcB, Finset.mul_sum]
    _ = ∑ c, ∑ q, (S x q : ℂ) * W' q b * (R c q * (S d c : ℂ) * conj (W c b)) :=
        Finset.sum_comm
    _ = ∑ c, ((S d c : ℂ) * conj (W c b)) * ∑ q, R c q * (S x q : ℂ) * W' q b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = ∑ c, ((S d c : ℂ) * conj (W c b)) * W c b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← hW c]
    _ = _ := by
        push_cast
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [mul_assoc, Complex.conj_mul']

/-!
## The chain form of the profile bounds
-/

section Chain

variable {d : VSData} {P : PsiData N} {s : ℝ} (hin : QVInputs d P s)
include hin

theorem qv_sqrt_chain_eq (q dd x y : Fin N) (u : List (Fin N)) (b : Fin N) :
    Real.sqrt (qvIsoSq P s q (y :: u) b * qvIsoSq P s q (dd :: x :: y :: u) b) =
      (P.lEta s)⁻¹ ^ 2 * Real.sqrt (P.ups s q y * P.ups s q dd) *
        Real.sqrt (P.ups s dd x * P.ups s x y) * qvIsoSq P s y u b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  have hZ := qvIsoSq_nonneg P s hU hL y u b
  rw [qvIsoSq_cons, qvIsoSq_cons, qvIsoSq_cons, qvIsoSq_cons]
  have e : (P.lEta s)⁻¹ * P.ups s q y * qvIsoSq P s y u b *
      ((P.lEta s)⁻¹ * P.ups s q dd * ((P.lEta s)⁻¹ * P.ups s dd x *
        ((P.lEta s)⁻¹ * P.ups s x y * qvIsoSq P s y u b))) =
      ((P.lEta s)⁻¹ ^ 2 * qvIsoSq P s y u b) ^ 2 *
        ((P.ups s q y * P.ups s q dd) * (P.ups s dd x * P.ups s x y)) := by ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (pow_nonneg
    (inv_nonneg.mpr hL.le) _) hZ), Real.sqrt_mul (mul_nonneg (hU _ _) (hU _ _))]
  ring

/-- **(C5), chain form.** `Σ_q S_xq √(s(q,y::u,b)² s(q,d::x::y::u,b)²) ≤ C_S s(d,x::y::u,b)²`. -/
theorem qvSChain (dd x y : Fin N) (u : List (Fin N)) (b : Fin N) :
    ∑ q, P.S x q * Real.sqrt (qvIsoSq P s q (y :: u) b * qvIsoSq P s q (dd :: x :: y :: u) b) ≤
      qvCS d * qvIsoSq P s dd (x :: y :: u) b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  simp_rw [qv_sqrt_chain_eq hin]
  set K := (P.lEta s)⁻¹ ^ 2 * Real.sqrt (P.ups s dd x * P.ups s x y) * qvIsoSq P s y u b
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hL.le) _)
    (Real.sqrt_nonneg _)) (qvIsoSq_nonneg P s hU hL y u b)
  have e : ∀ q, P.S x q * ((P.lEta s)⁻¹ ^ 2 * Real.sqrt (P.ups s q y * P.ups s q dd) *
      Real.sqrt (P.ups s dd x * P.ups s x y) * qvIsoSq P s y u b) =
      K * (P.S x q * Real.sqrt (P.ups s q y * P.ups s q dd)) := fun q => by ring
  simp_rw [e, ← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (qvSSchwarz hin x y dd) hK
  refine h.trans (le_of_eq ?_)
  rw [qvIsoSq_cons, qvIsoSq_cons]
  have hs : Real.sqrt (P.ups s x y * P.ups s x dd) * Real.sqrt (P.ups s dd x * P.ups s x y) =
      P.ups s dd x * P.ups s x y := by
    rw [← Real.sqrt_mul (mul_nonneg (hU _ _) (hU _ _)), hin.symm x dd,
      show P.ups s x y * P.ups s dd x * (P.ups s dd x * P.ups s x y) =
        (P.ups s dd x * P.ups s x y) ^ 2 by ring, Real.sqrt_sq (mul_nonneg (hU _ _) (hU _ _))]
  calc K * (qvCS d * Real.sqrt (P.ups s x y * P.ups s x dd))
      = qvCS d * (P.lEta s)⁻¹ ^ 2 * qvIsoSq P s y u b *
          (Real.sqrt (P.ups s x y * P.ups s x dd) * Real.sqrt (P.ups s dd x * P.ups s x y)) := by
        unfold K; ring
    _ = _ := by rw [hs]; ring

/-- **(C6), chain form.** `S_xb √(s(b,y::u,b)² s(b,d::x::y::u,b)²) ≤ C_S C₁/L · s(d,x::y::u,b)²`. -/
theorem qvSChainPt (dd x y : Fin N) (u : List (Fin N)) (b : Fin N) :
    P.S x b * Real.sqrt (qvIsoSq P s b (y :: u) b * qvIsoSq P s b (dd :: x :: y :: u) b) ≤
      qvCS d * (d.C1pp / P.lEta s) * qvIsoSq P s dd (x :: y :: u) b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  rw [qv_sqrt_chain_eq hin]
  set K := (P.lEta s)⁻¹ ^ 2 * Real.sqrt (P.ups s dd x * P.ups s x y) * qvIsoSq P s y u b
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hL.le) _)
    (Real.sqrt_nonneg _)) (qvIsoSq_nonneg P s hU hL y u b)
  have e : P.S x b * ((P.lEta s)⁻¹ ^ 2 * Real.sqrt (P.ups s b y * P.ups s b dd) *
      Real.sqrt (P.ups s dd x * P.ups s x y) * qvIsoSq P s y u b) =
      K * (P.S x b * Real.sqrt (P.ups s b y * P.ups s b dd)) := by ring
  rw [e]
  have h := mul_le_mul_of_nonneg_left (qvSTriangleSqrt hin x b y dd) hK
  refine h.trans (le_of_eq ?_)
  rw [qvIsoSq_cons, qvIsoSq_cons]
  have hs : Real.sqrt (P.ups s x y * P.ups s x dd) * Real.sqrt (P.ups s dd x * P.ups s x y) =
      P.ups s dd x * P.ups s x y := by
    rw [← Real.sqrt_mul (mul_nonneg (hU _ _) (hU _ _)), hin.symm x dd,
      show P.ups s x y * P.ups s dd x * (P.ups s dd x * P.ups s x y) =
        (P.ups s dd x * P.ups s x y) ^ 2 by ring, Real.sqrt_sq (mul_nonneg (hU _ _) (hU _ _))]
  calc K * (qvCS d * (d.C1pp / P.lEta s) * Real.sqrt (P.ups s x y * P.ups s x dd))
      = qvCS d * (d.C1pp / P.lEta s) * (P.lEta s)⁻¹ ^ 2 * qvIsoSq P s y u b *
          (Real.sqrt (P.ups s x y * P.ups s x dd) * Real.sqrt (P.ups s dd x * P.ups s x y)) := by
        unfold K; ring
    _ = _ := by rw [hs]; ring

/-- `qvSTriangle` for one link of a word: `L S_xb s(b, y::u, b)² ≤ C_S C₁ s(x, y::u, b)²`. -/
theorem qvSLink (x b y : Fin N) (u : List (Fin N)) :
    P.lEta s * (P.S x b * qvIsoSq P s b (y :: u) b) ≤
      qvCS d * d.C1pp * qvIsoSq P s x (y :: u) b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  rw [qvIsoSq_cons, qvIsoSq_cons]
  have hZ := qvIsoSq_nonneg P s hU hL y u b
  have h := qvSTriangle hin x b y
  have e1 : P.lEta s * (P.S x b * ((P.lEta s)⁻¹ * P.ups s b y * qvIsoSq P s y u b)) =
      (P.S x b * P.ups s b y) * qvIsoSq P s y u b := by
    field_simp
  have e2 : qvCS d * d.C1pp * ((P.lEta s)⁻¹ * P.ups s x y * qvIsoSq P s y u b) =
      (qvCS d * (d.C1pp / P.lEta s) * P.ups s x y) * qvIsoSq P s y u b := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right h hZ

end Chain

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
/-- **`k ≤ 4`**. -/
theorem qv_tilde_short (β₀ : Bool) (r : List (Fin N × Bool)) (hk : r.length + 1 ≤ 4)
    (dd b : Fin N) :
    qvQTilde P (qvW P s H β₀ r) dd b ≤
      LamM * qvPhiTilde psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
        qvIsoSq P s dd (r.map Prod.fst) b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  set A := qvAdj β₀ r
  have hD : (qvW P s H β₀ r)ᴴ * obsMat P.S dd * qvW P s H β₀ r =
      qvW P s H A.1 (A.2 ++ (dd, β₀) :: r) := by
    rw [qvW_append, qvW_conjTranspose P s hH]
  have hlen : (A.2 ++ (dd, β₀) :: r).length + 1 = 2 * (r.length + 1) := by
    simp only [A, List.length_append, List.length_cons, qvAdj_length]
    omega
  have hsites : (A.2 ++ (dd, β₀) :: r).map Prod.fst =
      (r.map Prod.fst).reverse ++ dd :: r.map Prod.fst := by
    simp only [List.map_append, List.map_cons, A, qvAdj_sites]
  have h0 : 0 ≤ 1 + psiI (2 * (r.length + 1)) *
      P.lEta s ^ (-(1 / 2 - lossAlpha (2 * (r.length + 1)))) := by
    have := Real.rpow_nonneg hL.le (-(1 / 2 - lossAlpha (2 * (r.length + 1))))
    nlinarith [hI (2 * (r.length + 1))]
  have hφ : qvPhiTilde psiI psiA (r.length + 1) (P.lEta s) ^ 2 =
      1 + psiI (2 * (r.length + 1)) * P.lEta s ^ (-(1 / 2 - lossAlpha (2 * (r.length + 1)))) := by
    unfold qvPhiTilde
    rw [qv_ite_pos hk, Real.sq_sqrt h0]
  have h := hA.word_iso hU hL hLam A.1 (A.2 ++ (dd, β₀) :: r)
    (by rw [hlen]; linarith [hI (2 * (r.length + 1))]) (by rw [hlen]; omega) b b
  rw [hlen, hsites, qv_ite_pos rfl, qvIsoSq_double P s hin.symm, ← hD,
    qv_sqrt_inv_sq hL (qvIsoSq_nonneg P s hU hL dd _ b)] at h
  rw [qvQTilde_eq_re]
  refine (Complex.re_le_norm _).trans (h.trans_eq ?_)
  rw [hφ, ← qv_rpow_div_sqrt hL]
  have hs : 0 < Real.sqrt (P.lEta s) := Real.sqrt_pos.mpr hL
  field_simp

omit hAv in
/-- **`5 ≤ k ≤ 7`**: `r = (x₁, β₁) :: (y, β₂) :: r'`. -/
theorem qv_tilde_long (β₀ : Bool) (x₁ : Fin N) (β₁ : Bool) (y : Fin N) (β₂ : Bool)
    (r' : List (Fin N × Bool)) (hk5 : 5 ≤ r'.length + 3) (hk7 : r'.length + 3 ≤ 7) (dd b : Fin N) :
    qvQTilde P (qvW P s H β₀ ((x₁, β₁) :: (y, β₂) :: r')) dd b ≤
      4 * qvCS d * d.C1pp * LamM ^ 2 *
        (psiI (r'.length + 2) * P.lEta s ^ lossAlpha (r'.length + 2) *
          (psiI (r'.length + 4) * P.lEta s ^ lossAlpha (r'.length + 4))) *
        qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  have hW : qvW P s H β₀ ((x₁, β₁) :: (y, β₂) :: r') =
      qvRes P s H β₀ * obsMat P.S x₁ * qvW P s H β₁ ((y, β₂) :: r') := qvW_cons _ _ _ _ _ _ _
  have hB : (qvRes P s H β₀)ᴴ * obsMat P.S dd *
      (qvRes P s H β₀ * obsMat P.S x₁ * qvW P s H β₁ ((y, β₂) :: r')) =
      qvW P s H (!β₀) ((dd, β₀) :: (x₁, β₁) :: (y, β₂) :: r') := by
    rw [qvRes_conjTranspose P s hH, ← hW]
    exact (qvW_cons P s H (!β₀) dd β₀ _).symm
  -- `Q̃ ≤ Σ_q S_{x₁q} |W'_qb| |B_qb|`
  have hsplit : qvQTilde P (qvW P s H β₀ ((x₁, β₁) :: (y, β₂) :: r')) dd b ≤
      ∑ q, P.S x₁ q * (‖qvW P s H β₁ ((y, β₂) :: r') q b‖ *
        ‖qvW P s H (!β₀) ((dd, β₀) :: (x₁, β₁) :: (y, β₂) :: r') q b‖) := by
    have h := qv_tilde_split P.S (qvRes P s H β₀) (qvW P s H β₁ ((y, β₂) :: r')) x₁ dd b
    rw [hB] at h
    rw [hW]
    have hnn := qvQTilde_nonneg P hin.sNonneg
      (qvRes P s H β₀ * obsMat P.S x₁ * qvW P s H β₁ ((y, β₂) :: r')) dd b
    calc qvQTilde P (qvRes P s H β₀ * obsMat P.S x₁ * qvW P s H β₁ ((y, β₂) :: r')) dd b
        = ‖((qvQTilde P (qvRes P s H β₀ * obsMat P.S x₁ * qvW P s H β₁ ((y, β₂) :: r')) dd b
            : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      _ = ‖∑ q, (P.S x₁ q : ℂ) * qvW P s H β₁ ((y, β₂) :: r') q b *
            conj (qvW P s H (!β₀) ((dd, β₀) :: (x₁, β₁) :: (y, β₂) :: r') q b)‖ := by
          rw [qvQTilde, h]
      _ ≤ _ := norm_sum_le _ _
      _ = _ := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hin.sNonneg _ _), Complex.norm_conj]
          ring
  -- entry bounds
  have hW'len : ((y, β₂) :: r').length + 1 = r'.length + 2 := by simp
  have hBlen : ((dd, β₀) :: (x₁, β₁) :: (y, β₂) :: r').length + 1 = r'.length + 4 := by simp
  have hA1 : 1 ≤ psiI (r'.length + 2) * P.lEta s ^ lossAlpha (r'.length + 2) :=
    one_le_mul_of_one_le_of_one_le (hI _) (qv_one_le_rpow hL1 (qv_alpha_nonneg _))
  have hA2 : 1 ≤ psiI (r'.length + 4) * P.lEta s ^ lossAlpha (r'.length + 4) :=
    one_le_mul_of_one_le_of_one_le (hI _) (qv_one_le_rpow hL1 (qv_alpha_nonneg _))
  generalize hA1e : psiI (r'.length + 2) * P.lEta s ^ lossAlpha (r'.length + 2) = A1 at hA1 ⊢
  generalize hA2e : psiI (r'.length + 4) * P.lEta s ^ lossAlpha (r'.length + 4) = A2 at hA2 ⊢
  have hW'b : ∀ q, ‖qvW P s H β₁ ((y, β₂) :: r') q b‖ ≤
      LamM * ((if q = b then Real.sqrt (P.lEta s) else 0) + A1) *
        Real.sqrt (qvIsoSq P s q (y :: r'.map Prod.fst) b) := by
    intro q
    have h := hA.word_iso hU hL hLam β₁ ((y, β₂) :: r')
      (by rw [hW'len]; linarith [hI (r'.length + 2)])
      (by rw [hW'len]; omega) q b
    simp only [hW'len, List.map_cons, hA1e] at h
    exact h
  have hBb : ∀ q, ‖qvW P s H (!β₀) ((dd, β₀) :: (x₁, β₁) :: (y, β₂) :: r') q b‖ ≤
      LamM * ((if q = b then Real.sqrt (P.lEta s) else 0) + A2) *
        Real.sqrt (qvIsoSq P s q (dd :: x₁ :: y :: r'.map Prod.fst) b) := by
    intro q
    have h := hA.word_iso hU hL hLam (!β₀) ((dd, β₀) :: (x₁, β₁) :: (y, β₂) :: r')
      (by rw [hBlen]; linarith [hI (r'.length + 4)]) (by rw [hBlen]; omega) q b
    simp only [hBlen, List.map_cons, hA2e] at h
    exact h
  have hsL := Real.mul_self_sqrt hL.le
  have hsq0 := Real.sqrt_nonneg (P.lEta s)
  -- the summand
  have hterm : ∀ q, P.S x₁ q * (‖qvW P s H β₁ ((y, β₂) :: r') q b‖ *
      ‖qvW P s H (!β₀) ((dd, β₀) :: (x₁, β₁) :: (y, β₂) :: r') q b‖) ≤
      LamM ^ 2 * (A1 * A2 * (P.S x₁ q * Real.sqrt (qvIsoSq P s q (y :: r'.map Prod.fst) b *
        qvIsoSq P s q (dd :: x₁ :: y :: r'.map Prod.fst) b)) +
      (if q = b then (Real.sqrt (P.lEta s) * A2 + A1 * Real.sqrt (P.lEta s) + P.lEta s) *
        (P.S x₁ b * Real.sqrt (qvIsoSq P s b (y :: r'.map Prod.fst) b *
          qvIsoSq P s b (dd :: x₁ :: y :: r'.map Prod.fst) b)) else 0)) := by
    intro q
    have hS0 := hin.sNonneg x₁ q
    have hq1 := qvIsoSq_nonneg P s hU hL q (y :: r'.map Prod.fst) b
    have hc0 : 0 ≤ (if q = b then Real.sqrt (P.lEta s) else 0) + A1 := by
      split_ifs <;> linarith
    have h1 := mul_le_mul (hW'b q) (hBb q) (norm_nonneg _)
      (mul_nonneg (mul_nonneg (by linarith) hc0) (Real.sqrt_nonneg _))
    have h2 := mul_le_mul_of_nonneg_left h1 hS0
    refine h2.trans (le_of_eq ?_)
    rw [Real.sqrt_mul hq1]
    split_ifs with hqb
    · subst hqb
      rw [Real.sqrt_mul hq1]
      linear_combination (LamM ^ 2 * P.S x₁ q * Real.sqrt (qvIsoSq P s q (y :: r'.map Prod.fst) q) *
        Real.sqrt (qvIsoSq P s q (dd :: x₁ :: y :: r'.map Prod.fst) q)) * hsL
    · ring
  have hsum := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => hterm q
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq'
    Finset.univ b, qv_ite_pos (Finset.mem_univ b)] at hsum
  refine hsplit.trans (hsum.trans ?_)
  have hc1 := qvSChain hin dd x₁ y (r'.map Prod.fst) b
  have hc2 := qvSChainPt hin dd x₁ y (r'.map Prod.fst) b
  have hCS := qvCS_ge_one d
  have hC1 := d.one_le_C1pp
  have hT0 := qvIsoSq_nonneg P s hU hL dd (x₁ :: y :: r'.map Prod.fst) b
  have hsq : Real.sqrt (P.lEta s) ≤ P.lEta s := by
    have h1 : 1 ≤ Real.sqrt (P.lEta s) := Real.one_le_sqrt.mpr hL1
    nlinarith
  have hY0 : 0 ≤ Real.sqrt (P.lEta s) * A2 + A1 * Real.sqrt (P.lEta s) + P.lEta s := by
    have : 0 ≤ A1 := by linarith
    have : 0 ≤ A2 := by linarith
    positivity
  have hX : (Real.sqrt (P.lEta s) * A2 + A1 * Real.sqrt (P.lEta s) + P.lEta s) *
      (qvCS d * (d.C1pp / P.lEta s) * qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b) ≤
      3 * (A1 * A2) * (qvCS d * d.C1pp * qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b) := by
    have e : (Real.sqrt (P.lEta s) * A2 + A1 * Real.sqrt (P.lEta s) + P.lEta s) *
        (qvCS d * (d.C1pp / P.lEta s) * qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b) =
        ((Real.sqrt (P.lEta s) * A2 + A1 * Real.sqrt (P.lEta s) + P.lEta s) / P.lEta s) *
          (qvCS d * d.C1pp * qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b) := by
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ hL]
    have hA12 : 1 ≤ A1 * A2 := one_le_mul_of_one_le_of_one_le hA1 hA2
    have t1 : Real.sqrt (P.lEta s) * A2 ≤ P.lEta s * (A1 * A2) := by
      have u1 := mul_le_mul_of_nonneg_right hsq (by linarith : (0 : ℝ) ≤ A2)
      have u2 : A2 ≤ A1 * A2 := le_mul_of_one_le_left (by linarith) hA1
      have u3 := mul_le_mul_of_nonneg_left u2 hL.le
      linarith
    have t2 : A1 * Real.sqrt (P.lEta s) ≤ P.lEta s * (A1 * A2) := by
      have u1 := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ A1)
      have u2 : A1 ≤ A1 * A2 := le_mul_of_one_le_right (by linarith) hA2
      have u3 := mul_le_mul_of_nonneg_left u2 hL.le
      linarith
    have t3 : P.lEta s ≤ P.lEta s * (A1 * A2) := le_mul_of_one_le_right hL.le hA12
    linarith
  have hAA : 0 ≤ A1 * A2 := by nlinarith
  have s1 := mul_le_mul_of_nonneg_left hc1 hAA
  have s2 := mul_le_mul_of_nonneg_left hc2 hY0
  have s3 : A1 * A2 * (qvCS d * qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b) ≤
      A1 * A2 * (qvCS d * d.C1pp * qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b) := by
    apply mul_le_mul_of_nonneg_left _ hAA
    have h := mul_le_mul_of_nonneg_left hC1 (mul_nonneg (by linarith : (0 : ℝ) ≤ qvCS d) hT0)
    linarith
  have hΛ0 : 0 ≤ LamM ^ 2 := sq_nonneg _
  calc _ ≤ LamM ^ 2 * (A1 * A2 * (qvCS d * d.C1pp *
        qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b) + 3 * (A1 * A2) * (qvCS d * d.C1pp *
          qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b)) := by
        apply mul_le_mul_of_nonneg_left _ hΛ0
        linarith
    _ = _ := by ring

omit hI in

/-- The trace factor of a `K`-cut: for `|rY| = 3`,
`Σ_a S_ba Σ_e S_qe |W(β₀,rY)_ae|² ≤ Λ_M (1 + ψ^av_8 L^{-(1-β_8)}) s(b, rY.map fst, q)²`
(an averaged chain of length `8`, (S4)).
-/
theorem qv_cut_trace (β₀ : Bool) (rY : List (Fin N × Bool)) (hY : rY.length = 3) (q b : Fin N) :
    ∑ a, P.S b a * ∑ e, P.S q e * ‖qvW P s H β₀ rY a e‖ ^ 2 ≤
      LamM * (1 + psiA 8 * P.lEta s ^ (-(1 - lossBeta 8))) *
        qvIsoSq P s b (rY.map Prod.fst) q := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
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

/-- **`k = 8`**: `r = rY ++ (x₄, β') :: rX`, `|rY| = |rX| = 3`. -/
theorem qv_tilde_K (β₀ : Bool) (rY : List (Fin N × Bool)) (x₄ : Fin N) (β' : Bool)
    (rX : List (Fin N × Bool)) (hY : rY.length = 3) (hX : rX.length = 3) (dd b : Fin N) :
    qvQTilde P (qvW P s H β₀ (rY ++ (x₄, β') :: rX)) dd b ≤
      4 * qvCS d * d.C1pp * LamM ^ 3 *
        (psiI 4 ^ 2 * (1 + psiA 8 * P.lEta s ^ (-(1 - lossBeta 8)))) * P.lEta s *
          qvIsoSq P s dd ((rY ++ (x₄, β') :: rX).map Prod.fst) b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  rw [qvW_append]
  set Y := qvW P s H β₀ rY
  set X := qvW P s H β' rX
  set u := rY.map Prod.fst
  set v := rX.map Prod.fst
  -- reduction inequality
  have hred : qvQTilde P (Y * obsMat P.S x₄ * X) dd b ≤
      (∑ c, P.S dd c * ∑ e, P.S x₄ e * ‖Y c e‖ ^ 2) * ∑ e, P.S x₄ e * ‖X e b‖ ^ 2 := by
    unfold qvQTilde
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => ?_
    have h := mul_le_mul_of_nonneg_left (qv_reduction_entry P.S hin.sNonneg Y X x₄ c b)
      (hin.sNonneg dd c)
    linarith
  have hT := qv_cut_trace hin hA hH hLam hAv hL1 β₀ rY hY x₄ dd
  -- the factor `R'_b` (an isotropic chain of length `4`, `α₄ = 0`)
  have hlenX : rX.length + 1 = 4 := by omega
  have hent : ∀ e, P.S x₄ e * ‖X e b‖ ^ 2 ≤ 2 * LamM ^ 2 *
      ((if e = b then P.lEta s * (P.S x₄ e * qvIsoSq P s e v b) else 0) +
        psiI 4 ^ 2 * (P.S x₄ e * qvIsoSq P s e v b)) := by
    intro e
    have h := hA.word_iso_sq hU hL hLam β' rX (by rw [hlenX]; linarith [hI 4])
      (by rw [hlenX]; norm_num) e b
    rw [hlenX, qv_alpha_of_le_four le_rfl, Real.rpow_zero, one_pow, mul_one] at h
    have h1 := mul_le_mul_of_nonneg_left h (hin.sNonneg x₄ e)
    refine h1.trans (le_of_eq ?_)
    split_ifs <;> ring
  have hsum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) => hent e
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ b,
    qv_ite_pos (Finset.mem_univ b), ← Finset.mul_sum] at hsum
  obtain ⟨y1, v', hv'⟩ : ∃ y1 v', v = y1 :: v' := by
    rcases rX with _ | ⟨e, rX'⟩
    · simp at hX
    · exact ⟨e.1, rX'.map Prod.fst, by simp [v]⟩
  have hlink := qvSLink hin x₄ b y1 v'
  rw [← hv'] at hlink
  have hwt := qvSWeight hin x₄ v b
  have hCS := qvCS_ge_one d
  have hC1 := d.one_le_C1pp
  have hψ4 : 1 ≤ psiI 4 ^ 2 := one_le_pow₀ (hI 4)
  have hq := qvIsoSq_nonneg P s hU hL x₄ v b
  have hR : ∑ e, P.S x₄ e * ‖X e b‖ ^ 2 ≤
      4 * qvCS d * d.C1pp * LamM ^ 2 * psiI 4 ^ 2 * qvIsoSq P s x₄ v b := by
    refine hsum.trans ?_
    have h1 : P.lEta s * (P.S x₄ b * qvIsoSq P s b v b) + psiI 4 ^ 2 *
        ∑ e, P.S x₄ e * qvIsoSq P s e v b ≤
        qvCS d * d.C1pp * qvIsoSq P s x₄ v b + psiI 4 ^ 2 * (qvCS d * qvIsoSq P s x₄ v b) :=
      add_le_add hlink (mul_le_mul_of_nonneg_left hwt (by positivity))
    have h2 : qvCS d * d.C1pp * qvIsoSq P s x₄ v b + psiI 4 ^ 2 * (qvCS d * qvIsoSq P s x₄ v b) ≤
        2 * (qvCS d * d.C1pp * psiI 4 ^ 2 * qvIsoSq P s x₄ v b) := by
      have a1 : qvCS d * d.C1pp * qvIsoSq P s x₄ v b ≤
          qvCS d * d.C1pp * psiI 4 ^ 2 * qvIsoSq P s x₄ v b := by
        have := mul_le_mul_of_nonneg_left hψ4 (mul_nonneg (mul_nonneg (by linarith :
          (0 : ℝ) ≤ qvCS d) (by linarith : (0 : ℝ) ≤ d.C1pp)) hq)
        linarith
      have a2 : psiI 4 ^ 2 * (qvCS d * qvIsoSq P s x₄ v b) ≤
          qvCS d * d.C1pp * psiI 4 ^ 2 * qvIsoSq P s x₄ v b := by
        have := mul_le_mul_of_nonneg_left hC1 (mul_nonneg (mul_nonneg (by linarith :
          (0 : ℝ) ≤ psiI 4 ^ 2) (by linarith : (0 : ℝ) ≤ qvCS d)) hq)
        linarith
      linarith
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0 : ℝ) ≤ 2 * LamM ^ 2)
    refine h3.trans (le_of_eq ?_)
    ring
  have hR0 : 0 ≤ ∑ e, P.S x₄ e * ‖X e b‖ ^ 2 :=
    Finset.sum_nonneg fun e _ => mul_nonneg (hin.sNonneg _ _) (sq_nonneg _)
  have hE : 0 ≤ 1 + psiA 8 * P.lEta s ^ (-(1 - lossBeta 8)) := by
    have := Real.rpow_nonneg hL.le (-(1 - lossBeta 8)); nlinarith [hAv 8]
  have hprod := mul_le_mul hT hR hR0 (mul_nonneg (mul_nonneg (by linarith) hE)
    (qvIsoSq_nonneg P s hU hL dd u x₄))
  refine hred.trans (hprod.trans (le_of_eq ?_))
  have hsplit := qvIsoSq_split P s dd u x₄ v b
  have hsites : (rY ++ (x₄, β') :: rX).map Prod.fst = u ++ x₄ :: v := by
    simp [u, v]
  rw [hsites, hsplit]
  field_simp
  ring

/-- **Bound on `Q̃`**: for every word `(β₀, r)` of length `k ≤ 8`,
`Q̃(d, b) ≤ 4 C_S C₁ Λ_M³ (φ̃^{iso,qv}_k)² L^{2α_k} s(d, r.map fst, b)²`.
-/
theorem qv_tilde (β₀ : Bool) (r : List (Fin N × Bool)) (hk : r.length + 1 ≤ 8) (dd b : Fin N) :
    qvQTilde P (qvW P s H β₀ r) dd b ≤
      4 * qvCS d * d.C1pp * LamM ^ 3 * qvPhiTilde psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
        P.lEta s ^ (2 * lossAlpha (r.length + 1)) * qvIsoSq P s dd (r.map Prod.fst) b := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  have hq := qvIsoSq_nonneg P s hU hL dd (r.map Prod.fst) b
  have hCS := qvCS_ge_one d
  have hC1 := d.one_le_C1pp
  have hΛ3 : LamM ≤ LamM ^ 3 := le_self_pow₀ hLam (by norm_num)
  have hΛ2 : LamM ^ 2 ≤ LamM ^ 3 := pow_le_pow_right₀ hLam (by norm_num)
  have hβ1 : 1 ≤ P.lEta s ^ (2 * lossAlpha (r.length + 1)) :=
    qv_one_le_rpow hL1 (by linarith [qv_alpha_nonneg (r.length + 1)])
  rcases (show r.length + 1 ≤ 4 ∨ (5 ≤ r.length + 1 ∧ r.length + 1 ≤ 7) ∨ r.length + 1 = 8 by
    omega) with h | ⟨h5, h7⟩ | h8
  · refine (qv_tilde_short hin hA hH hLam hI hL1 β₀ r h dd b).trans ?_
    have hc : 1 ≤ 4 * qvCS d * d.C1pp := by nlinarith
    have hφ := sq_nonneg (qvPhiTilde psiI psiA (r.length + 1) (P.lEta s))
    have h1 : LamM ≤ 4 * qvCS d * d.C1pp * LamM ^ 3 :=
      hΛ3.trans (le_mul_of_one_le_left (by positivity) hc)
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hφ hq)
    have h3 : 4 * qvCS d * d.C1pp * LamM ^ 3 *
        (qvPhiTilde psiI psiA (r.length + 1) (P.lEta s) ^ 2 * qvIsoSq P s dd (r.map Prod.fst) b) ≤
        4 * qvCS d * d.C1pp * LamM ^ 3 *
          (qvPhiTilde psiI psiA (r.length + 1) (P.lEta s) ^ 2 * qvIsoSq P s dd (r.map Prod.fst) b) *
            P.lEta s ^ (2 * lossAlpha (r.length + 1)) :=
      le_mul_of_one_le_right (by positivity) hβ1
    calc _ = LamM * (qvPhiTilde psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
          qvIsoSq P s dd (r.map Prod.fst) b) := by ring
      _ ≤ _ := h2.trans h3
      _ = _ := by ring
  · rcases r with _ | ⟨⟨x₁, β₁⟩, _ | ⟨⟨y, β₂⟩, r'⟩⟩
    · simp at h5
    · simp at h5
    · simp only [List.length_cons] at h5 h7 ⊢
      refine (qv_tilde_long hin hA hH hLam hI hL1 β₀ x₁ β₁ y β₂ r' (by omega) (by omega)
        dd b).trans ?_
      have hk1 : r'.length + 1 + 1 + 1 - 1 = r'.length + 2 := by omega
      have hk2 : r'.length + 1 + 1 + 1 + 1 = r'.length + 4 := by omega
      have hX0 : 0 ≤ psiI (r'.length + 1 + 1 + 1 - 1) * psiI (r'.length + 1 + 1 + 1 + 1) *
          P.lEta s ^ (-(2 * lossAlpha (r'.length + 1 + 1 + 1) -
            lossAlpha (r'.length + 1 + 1 + 1 - 1) - lossAlpha (r'.length + 1 + 1 + 1 + 1))) := by
        have := Real.rpow_nonneg hL.le (-(2 * lossAlpha (r'.length + 1 + 1 + 1) -
            lossAlpha (r'.length + 1 + 1 + 1 - 1) - lossAlpha (r'.length + 1 + 1 + 1 + 1)))
        have := hI (r'.length + 1 + 1 + 1 - 1)
        have := hI (r'.length + 1 + 1 + 1 + 1)
        positivity
      have hφ : qvPhiTilde psiI psiA (r'.length + 1 + 1 + 1) (P.lEta s) ^ 2 *
          P.lEta s ^ (2 * lossAlpha (r'.length + 1 + 1 + 1)) =
          psiI (r'.length + 2) * P.lEta s ^ lossAlpha (r'.length + 2) *
            (psiI (r'.length + 4) * P.lEta s ^ lossAlpha (r'.length + 4)) := by
        unfold qvPhiTilde
        rw [qv_ite_neg (by omega), qv_ite_pos (by omega), Real.sq_sqrt hX0, hk1, hk2]
        rw [mul_assoc, ← Real.rpow_add hL]
        have e : -(2 * lossAlpha (r'.length + 1 + 1 + 1) - lossAlpha (r'.length + 2) -
            lossAlpha (r'.length + 4)) + 2 * lossAlpha (r'.length + 1 + 1 + 1) =
            lossAlpha (r'.length + 2) + lossAlpha (r'.length + 4) := by ring
        rw [e, Real.rpow_add hL]
        ring
      have hrw : 4 * qvCS d * d.C1pp * LamM ^ 3 *
          qvPhiTilde psiI psiA (r'.length + 1 + 1 + 1) (P.lEta s) ^ 2 *
          P.lEta s ^ (2 * lossAlpha (r'.length + 1 + 1 + 1)) *
            qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b =
          4 * qvCS d * d.C1pp * LamM ^ 3 * (psiI (r'.length + 2) *
            P.lEta s ^ lossAlpha (r'.length + 2) *
              (psiI (r'.length + 4) * P.lEta s ^ lossAlpha (r'.length + 4))) *
            qvIsoSq P s dd (x₁ :: y :: r'.map Prod.fst) b := by
        rw [← hφ]; ring
      simp only [List.map_cons]
      rw [hrw]
      have hAA : 0 ≤ psiI (r'.length + 2) * P.lEta s ^ lossAlpha (r'.length + 2) *
          (psiI (r'.length + 4) * P.lEta s ^ lossAlpha (r'.length + 4)) := by
        have := hI (r'.length + 2)
        have := hI (r'.length + 4)
        have := Real.rpow_nonneg hL.le (lossAlpha (r'.length + 2))
        have := Real.rpow_nonneg hL.le (lossAlpha (r'.length + 4))
        positivity
      have hq' := qvIsoSq_nonneg P s hU hL dd (x₁ :: y :: r'.map Prod.fst) b
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΛ2 (by positivity : (0 : ℝ) ≤ 4 * qvCS d * d.C1pp))
        (mul_nonneg hAA hq')
      linarith
  · have hr7 : r.length = 7 := by omega
    have hd : (r.drop 3).length = 4 := by simp [hr7]
    obtain ⟨⟨x₄, β'⟩, rX, hrX⟩ : ∃ qx rX, r.drop 3 = qx :: rX := by
      cases h : r.drop 3 with
      | nil => rw [h] at hd; simp at hd
      | cons qx rX => exact ⟨qx, rX, rfl⟩
    have hsplit : r = r.take 3 ++ (x₄, β') :: rX := by
      rw [← hrX, List.take_append_drop]
    have hY : (r.take 3).length = 3 := by simp [hr7]
    have hX : rX.length = 3 := by
      have := congrArg List.length hrX
      simp [hr7] at this
      omega
    have hcase := qv_tilde_K hin hA hH hLam hI hAv hL1 β₀ (r.take 3) x₄ β' rX hY hX dd b
    rw [← hsplit] at hcase
    refine hcase.trans (le_of_eq ?_)
    have hE : 0 ≤ 1 + psiA 8 * P.lEta s ^ (-(1 - lossBeta 8)) := by
      have := Real.rpow_nonneg hL.le (-(1 - lossBeta 8)); nlinarith [hAv 8]
    rw [h8]
    unfold qvPhiTilde
    rw [qv_ite_neg (by norm_num), qv_ite_neg (by norm_num), mul_pow, Real.sq_sqrt hE,
      qv_alpha_eight, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]

end Cases

end BlockBand.Native.ErdosRiabov.QV
