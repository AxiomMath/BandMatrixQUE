module

public import BlockBand.Native.ErdosRiabov.QV.FirstVar

/-!
# Quadratic variation: the bracket of a propagated chain martingale

The bracket density of a linear combination of chain martingales is bounded by the
quadratic-variation bounds of the individual chains.

* `qv_bracket_le`: for `S ≥ 0`, coefficients `c_α` and terms `v_{α,j}`,
  `Σ_{ab} S_ab |Σ_α c_α Σ_j v_{αj}(a,b)|² ≤ |J| Σ_j (Σ_α |c_α| (Σ_{ab} S_ab |v_{αj}(a,b)|²)^{1/2})²`
  (Cauchy–Schwarz over `j`, Minkowski in `ℓ²(S)` over `α`).
* `qv_bracket_av`, `qv_bracket_iso`: the bracket density
  `Σ_{ab} S_ab |Σ_α c_α tr(K_α firstVar_α[E_ab])|²` of a linear combination of the averaged
  (`K = 1`, slots `avSlots`) resp. isotropic (`K = E_{b'a'}`, slots `isoSlots`) chains of length
  `k = n + 1 ≤ 8` along a pattern `σ`, with resolvent slots `qvRes`, is
  `≤ k² · 𝔠 Λ_M³ φ² L^{2γ} η⁻¹ · (Σ_α |c_α| s_α)²`, under `APriori` (by `qv_QV_av` and
  `qv_QV_iso_*`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.QV

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Chains (slotList slotProd segProd firstVar)
open Expo (lossAlpha lossBeta)
open Matrix Function
open scoped ComplexConjugate

variable {N : ℕ}

/-!
## The weighted Cauchy–Schwarz and Minkowski bound
-/

theorem qv_sum_swap4 {ι : Type*} [Fintype ι] (F : Fin N → Fin N → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ α, ∑ β, F a b α β = ∑ α, ∑ β, ∑ a, ∑ b, F a b α β := by
  calc ∑ a, ∑ b, ∑ α, ∑ β, F a b α β = ∑ a, ∑ α, ∑ b, ∑ β, F a b α β :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ α, ∑ a, ∑ b, ∑ β, F a b α β := Finset.sum_comm
    _ = ∑ α, ∑ a, ∑ β, ∑ b, F a b α β :=
        Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ α, ∑ β, ∑ a, ∑ b, F a b α β := Finset.sum_congr rfl fun α _ => Finset.sum_comm

theorem qv_sum_swap3 {J : Type*} [Fintype J] (F : Fin N → Fin N → J → ℝ) :
    ∑ a, ∑ b, ∑ j, F a b j = ∑ j, ∑ a, ∑ b, F a b j := by
  calc ∑ a, ∑ b, ∑ j, F a b j = ∑ a, ∑ j, ∑ b, F a b j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Weighted Cauchy–Schwarz on `Fin N × Fin N`. -/
theorem qv_weighted_cs (S : Matrix (Fin N) (Fin N) ℝ) (hS : ∀ a b, 0 ≤ S a b)
    (f g : Fin N → Fin N → ℝ) :
    ∑ a, ∑ b, S a b * (f a b * g a b) ≤
      Real.sqrt (∑ a, ∑ b, S a b * f a b ^ 2) * Real.sqrt (∑ a, ∑ b, S a b * g a b ^ 2) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : Fin N × Fin N => Real.sqrt (S p.1 p.2) * f p.1 p.2)
    (fun p : Fin N × Fin N => Real.sqrt (S p.1 p.2) * g p.1 p.2)
  have e1 : ∀ p : Fin N × Fin N, Real.sqrt (S p.1 p.2) * f p.1 p.2 *
      (Real.sqrt (S p.1 p.2) * g p.1 p.2) = S p.1 p.2 * (f p.1 p.2 * g p.1 p.2) := by
    intro p
    have := Real.mul_self_sqrt (hS p.1 p.2)
    linear_combination (f p.1 p.2 * g p.1 p.2) * this
  have e2 : ∀ (p : Fin N × Fin N) (h : Fin N → Fin N → ℝ),
      (Real.sqrt (S p.1 p.2) * h p.1 p.2) ^ 2 = S p.1 p.2 * h p.1 p.2 ^ 2 := by
    intro p h
    rw [mul_pow, Real.sq_sqrt (hS p.1 p.2)]
  simp only [e1, e2] at h
  have h0f : 0 ≤ ∑ p : Fin N × Fin N, S p.1 p.2 * f p.1 p.2 ^ 2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hS _ _) (sq_nonneg _)
  have h0g : 0 ≤ ∑ p : Fin N × Fin N, S p.1 p.2 * g p.1 p.2 ^ 2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hS _ _) (sq_nonneg _)
  rw [← Real.sqrt_mul h0f]
  exact Real.le_sqrt_of_sq_le h

/-- Minkowski in `ℓ²(S)`. -/
theorem qv_minkowski {ι : Type*} [Fintype ι] (S : Matrix (Fin N) (Fin N) ℝ) (hS : ∀ a b, 0 ≤ S a b)
    (c : ι → ℂ) (v : ι → Fin N → Fin N → ℂ) :
    ∑ a, ∑ b, S a b * ‖∑ α, c α * v α a b‖ ^ 2 ≤
      (∑ α, ‖c α‖ * Real.sqrt (∑ a, ∑ b, S a b * ‖v α a b‖ ^ 2)) ^ 2 := by
  set A : ι → ℝ := fun α => Real.sqrt (∑ a, ∑ b, S a b * ‖v α a b‖ ^ 2)
  have hpt : ∀ a b, S a b * ‖∑ α, c α * v α a b‖ ^ 2 ≤
      ∑ α, ∑ β, ‖c α‖ * ‖c β‖ * (S a b * (‖v α a b‖ * ‖v β a b‖)) := by
    intro a b
    have h1 : ‖∑ α, c α * v α a b‖ ≤ ∑ α, ‖c α‖ * ‖v α a b‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun α _ => norm_mul _ _))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := mul_le_mul_of_nonneg_left h2 (hS a b)
    refine h3.trans (le_of_eq ?_)
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  calc ∑ a, ∑ b, S a b * ‖∑ α, c α * v α a b‖ ^ 2
      ≤ ∑ a, ∑ b, ∑ α, ∑ β, ‖c α‖ * ‖c β‖ * (S a b * (‖v α a b‖ * ‖v β a b‖)) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
    _ = ∑ α, ∑ β, ‖c α‖ * ‖c β‖ * ∑ a, ∑ b, S a b * (‖v α a b‖ * ‖v β a b‖) := by
        rw [qv_sum_swap4 (fun a b α β => ‖c α‖ * ‖c β‖ * (S a b * (‖v α a b‖ * ‖v β a b‖)))]
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ α, ∑ β, ‖c α‖ * ‖c β‖ * (A α * A β) := by
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => ?_
        exact mul_le_mul_of_nonneg_left (qv_weighted_cs S hS _ _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
        ring

/-- **Cauchy–Schwarz for the bracket density**:
`Σ_{ab} S_ab |Σ_α c_α Σ_j v_{αj}|² ≤
|J| Σ_j (Σ_α |c_α| ‖v_{αj}‖_{ℓ²(S)})²`.
-/
theorem qv_bracket_le {ι J : Type*} [Fintype ι] [Fintype J] (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : ∀ a b, 0 ≤ S a b) (c : ι → ℂ) (v : ι → J → Fin N → Fin N → ℂ) :
    ∑ a, ∑ b, S a b * ‖∑ α, c α * ∑ j, v α j a b‖ ^ 2 ≤
      (Fintype.card J : ℝ) *
        ∑ j, (∑ α, ‖c α‖ * Real.sqrt (∑ a, ∑ b, S a b * ‖v α j a b‖ ^ 2)) ^ 2 := by
  have hre : ∀ a b, ∑ α, c α * ∑ j, v α j a b = ∑ j, ∑ α, c α * v α j a b := by
    intro a b
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hpt : ∀ a b, S a b * ‖∑ j, ∑ α, c α * v α j a b‖ ^ 2 ≤
      (Fintype.card J : ℝ) * ∑ j, S a b * ‖∑ α, c α * v α j a b‖ ^ 2 := by
    intro a b
    have h1 := norm_sum_le Finset.univ (fun j => ∑ α, c α * v α j a b)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => ‖∑ α, c α * v α j a b‖)
    rw [Finset.card_univ] at h3
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) (hS a b)
    refine h4.trans (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc ∑ a, ∑ b, S a b * ‖∑ α, c α * ∑ j, v α j a b‖ ^ 2
      = ∑ a, ∑ b, S a b * ‖∑ j, ∑ α, c α * v α j a b‖ ^ 2 := by simp_rw [hre]
    _ ≤ ∑ a, ∑ b, (Fintype.card J : ℝ) * ∑ j, S a b * ‖∑ α, c α * v α j a b‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
    _ = (Fintype.card J : ℝ) * ∑ j, ∑ a, ∑ b, S a b * ‖∑ α, c α * v α j a b‖ ^ 2 := by
        rw [← qv_sum_swap3 (fun a b j => S a b * ‖∑ α, c α * v α j a b‖ ^ 2), Finset.mul_sum]
        simp_rw [Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum fun j _ => qv_minkowski S hS c (fun α => v α j)

/-!
## The densities of the `j`-th terms
-/

section Densities

variable {d : VSData} {P : PsiData N} {psiI psiA : ℕ → ℝ} {LamM s : ℝ}
  {H : Matrix (Fin N) (Fin N) ℂ} (hin : QVInputs d P s) (hA : APriori P psiI psiA LamM s H)
  (hH : H.IsHermitian) (hLam : 1 ≤ LamM) (hI : ∀ j, 1 ≤ psiI j) (hAv : ∀ j, 0 ≤ psiA j)
  (hL1 : 1 ≤ P.lEta s)
include hin hA hH hLam hI hAv hL1

/-- The bound `𝔠 Λ_M³ (φ^{av,qv}_k)² L^{2β_k} η⁻¹` of `qv_QV_av` at length `k`. -/
def qvBndAv (d : VSData) (P : PsiData N) (psiI psiA : ℕ → ℝ) (LamM s : ℝ) (k : ℕ) : ℝ :=
  qvC d * LamM ^ 3 * qvPhiAv psiI psiA k (P.lEta s) ^ 2 * P.lEta s ^ (2 * lossBeta k) /
    vsHeight P.z s

/-- The bound `𝔠 Λ_M³ (φ^{iso,qv}_k)² L^{2α_k} η⁻¹` of `qv_QV_iso_*` at length `k`. -/
def qvBndIso (d : VSData) (P : PsiData N) (psiI psiA : ℕ → ℝ) (LamM s : ℝ) (k : ℕ) : ℝ :=
  qvC d * LamM ^ 3 * qvPhiIso psiI psiA k (P.lEta s) ^ 2 * P.lEta s ^ (2 * lossAlpha k) /
    vsHeight P.z s

omit hH hLam hI hAv hL1 hA in
theorem qvBndAv_nonneg (k : ℕ) (hLam : 1 ≤ LamM) : 0 ≤ qvBndAv d P psiI psiA LamM s k := by
  unfold qvBndAv
  have := qvC_pos d
  have := Real.rpow_nonneg hin.lEta_pos.le (2 * lossBeta k)
  have := hin.height_pos
  positivity

omit hH hLam hI hAv hL1 hA in
theorem qvBndIso_nonneg (k : ℕ) (hLam : 1 ≤ LamM) : 0 ≤ qvBndIso d P psiI psiA LamM s k := by
  unfold qvBndIso
  have := qvC_pos d
  have := Real.rpow_nonneg hin.lEta_pos.le (2 * lossAlpha k)
  have := hin.height_pos
  positivity

/-- **The density of the `j`-th term, averaged** (all `j`, by rotation): the density of the
rotated chain is `≤ qvBndAv · s^av(x)²`. -/
theorem qv_av_density {n : ℕ} (hn : n + 1 ≤ 8) (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N)
    (j : Fin (n + 1)) :
    qvQAv P (qvW P s H (σ j) ((qvPairs σ x).drop j ++ (x (Fin.last n), σ 0) ::
      (qvPairs σ x).take j)) ≤ qvBndAv d P psiI psiA LamM s (n + 1) * P.sAv x s ^ 2 := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  rw [sAv_qvPairs P hU hL σ x, Real.sq_sqrt (qvAvSq_nonneg P s hU hL _ _)]
  have hr : (qvPairs σ x).length = n := qvPairs_length σ x
  rcases j with ⟨_ | i, hj⟩
  · have h := qv_QV_av hin hA hH hLam hI hAv hL1 (σ 0) (qvPairs σ x) (x (Fin.last n))
      (by rw [hr]; exact hn)
    rw [hr] at h
    simpa [qvBndAv] using h
  · have hi : i < (qvPairs σ x).length := by rw [hr]; omega
    have hget : (qvPairs σ x)[i] = (x ⟨i, by omega⟩, σ ⟨i + 1, hj⟩) := by
      simp [qvPairs, List.getElem_ofFn]
    have htake : (qvPairs σ x).take (i + 1) =
        (qvPairs σ x).take i ++ [(x ⟨i, by omega⟩, σ ⟨i + 1, hj⟩)] := by
      rw [List.take_succ_eq_append_getElem hi, hget]
    set r' := (qvPairs σ x).drop (i + 1) ++ (x (Fin.last n), σ 0) :: (qvPairs σ x).take i
    have hw : (qvPairs σ x).drop (i + 1) ++ (x (Fin.last n), σ 0) :: (qvPairs σ x).take (i + 1) =
        r' ++ [(x ⟨i, by omega⟩, σ ⟨i + 1, hj⟩)] := by
      rw [htake]; simp [r']
    have hlen : r'.length = n := by simp [r', hr]; omega
    have h := qv_QV_av hin hA hH hLam hI hAv hL1 (σ ⟨i + 1, hj⟩) r' (x ⟨i, by omega⟩)
      (by rw [hlen]; exact hn)
    rw [hlen] at h
    have hsites : qvAvSq P s (x ⟨i, by omega⟩) (r'.map Prod.fst) =
        qvAvSq P s (x (Fin.last n)) ((qvPairs σ x).map Prod.fst) := by
      have hl : qvPairs σ x = (qvPairs σ x).take i ++ (x ⟨i, by omega⟩, σ ⟨i + 1, hj⟩) ::
          (qvPairs σ x).drop (i + 1) := by
        rw [← hget, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
      have hsplit : (qvPairs σ x).map Prod.fst = ((qvPairs σ x).take i).map Prod.fst ++
          x ⟨i, by omega⟩ :: ((qvPairs σ x).drop (i + 1)).map Prod.fst := by
        conv_lhs => rw [hl]
        simp
      rw [hsplit, qvAvSq_rot]
      simp [r']
    rw [hsites] at h
    show qvQAv P (qvW P s H (σ ⟨i + 1, hj⟩) _) ≤ _
    rw [hw]
    simpa [qvBndAv] using h

/-- **The density of the `j`-th term, isotropic**: the density of the split at `j` is
`≤ qvBndIso · s^iso(a,x,b)²`. Under `Split.ExplicitShortStatement` and the stability bound (as
`qv_QV_iso_first`). -/
theorem qv_iso_density (hES : Split.ExplicitShortStatement) (hS : StochasticSymm P.S)
    (hz : P.z.im ≠ 0) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hstab : ∀ x y, ‖Split.stabOp s P.S (semicircleM P.z * conj (semicircleM P.z)) x y‖ ≤
      (if x = y then 1 else 0) + Propagator.vsCK d * P.ups s x y)
    {n : ℕ} (hn : n + 1 ≤ 8) (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N)
    (j : Fin (n + 1)) (a b : Fin N) :
    qvQIso P (qvW P s H (σ 0) ((qvPairs σ x).take j)) (qvW P s H (σ j) ((qvPairs σ x).drop j))
      a b ≤ qvBndIso d P psiI psiA LamM s (n + 1) * P.sIso a b x s ^ 2 := by
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  rw [sIso_qvPairs P hU hL σ a b x, Real.sq_sqrt (qvIsoSq_nonneg P s hU hL _ _ _)]
  have hr : (qvPairs σ x).length = n := qvPairs_length σ x
  rcases j with ⟨_ | i, hj⟩
  · have h := qv_QV_iso_first hin hA hH hLam hI hAv hL1 hES hS hz hs hstab (σ 0) (qvPairs σ x)
      (by rw [hr]; exact hn) a b
    rw [hr] at h
    simpa [qvBndIso, qvW_nil] using h
  · have hi : i < (qvPairs σ x).length := by rw [hr]; omega
    have hget : (qvPairs σ x)[i] = (x ⟨i, by omega⟩, σ ⟨i + 1, hj⟩) := by
      simp [qvPairs, List.getElem_ofFn]
    have htake : (qvPairs σ x).take (i + 1) =
        (qvPairs σ x).take i ++ [(x ⟨i, by omega⟩, σ ⟨i + 1, hj⟩)] := by
      rw [List.take_succ_eq_append_getElem hi, hget]
    have hk : ((qvPairs σ x).take i).length + ((qvPairs σ x).drop (i + 1)).length + 2 = n + 1 := by
      simp [hr]; omega
    have h := qv_QV_iso_mid hin hA hH hLam hI hAv hL1 hES hS hz hs hstab (σ 0)
      ((qvPairs σ x).take i) (x ⟨i, by omega⟩) (σ ⟨i + 1, hj⟩) ((qvPairs σ x).drop (i + 1))
      (by rw [hk]; exact hn) a b
    rw [hk] at h
    have hsites : ((qvPairs σ x).take i).map Prod.fst ++ x ⟨i, by omega⟩ ::
        ((qvPairs σ x).drop (i + 1)).map Prod.fst = (qvPairs σ x).map Prod.fst := by
      have hl : qvPairs σ x = (qvPairs σ x).take i ++ (x ⟨i, by omega⟩, σ ⟨i + 1, hj⟩) ::
          (qvPairs σ x).drop (i + 1) := by
        rw [← hget, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
      conv_rhs => rw [hl]
      simp
    rw [hsites] at h
    show qvQIso P (qvW P s H (σ 0) ((qvPairs σ x).take (i + 1))) _ a b ≤ _
    rw [htake]
    simpa [qvBndIso] using h

omit hin hA hH hLam hI hAv hL1 in
/-- The `α`-sum step: `Σ_j (Σ_α |c_α| √Q_{αj})² ≤ |J| B (Σ_α |c_α| s_α)²` from `Q_{αj} ≤ B s_α²`. -/
theorem qv_sum_sqrt_le {ι J : Type*} [Fintype ι] [Fintype J] (c : ι → ℂ) (Q : ι → J → ℝ)
    (sz : ι → ℝ) {B : ℝ} (hB : 0 ≤ B) (hsz : ∀ α, 0 ≤ sz α) (hQ : ∀ α j, Q α j ≤ B * sz α ^ 2) :
    ∑ j, (∑ α, ‖c α‖ * Real.sqrt (Q α j)) ^ 2 ≤
      (Fintype.card J : ℝ) * (B * (∑ α, ‖c α‖ * sz α) ^ 2) := by
  have h1 : ∀ j, ∑ α, ‖c α‖ * Real.sqrt (Q α j) ≤ Real.sqrt B * ∑ α, ‖c α‖ * sz α := by
    intro j
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun α _ => ?_
    have h := Real.sqrt_le_sqrt (hQ α j)
    rw [Real.sqrt_mul hB, Real.sqrt_sq (hsz α)] at h
    nlinarith [norm_nonneg (c α)]
  have h0 : ∀ j, 0 ≤ ∑ α, ‖c α‖ * Real.sqrt (Q α j) :=
    fun j => Finset.sum_nonneg fun α _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  calc ∑ j, (∑ α, ‖c α‖ * Real.sqrt (Q α j)) ^ 2
      ≤ ∑ _j : J, (Real.sqrt B * ∑ α, ‖c α‖ * sz α) ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (h0 j) (h1 j) 2
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow, Real.sq_sqrt hB]

/-- **The bracket density, averaged chains**: for chains of length `k = n + 1 ≤ 8` along `σ`
and coefficients `c_α`, the bracket density is
`Σ_{ab} S_ab |Σ_α c_α tr(firstVar_α[E_ab])|² ≤ k² · qvBndAv_k · (Σ_α |c_α| s^av(α))²`.
-/
theorem qv_bracket_av {n : ℕ} (hn : n + 1 ≤ 8) (σ : Fin (n + 1) → Bool)
    (c : (Fin (n + 1) → Fin N) → ℂ) :
    ∑ a, ∑ b, P.S a b * ‖∑ α, c α * Matrix.trace ((1 : Matrix (Fin N) (Fin N) ℂ) *
      firstVar (avSlots P.S α) (fun j => qvRes P s H (σ j))
        (Matrix.single a b (1 : ℂ)))‖ ^ 2 ≤
      ((n : ℝ) + 1) ^ 2 * qvBndAv d P psiI psiA LamM s (n + 1) *
        (∑ α, ‖c α‖ * P.sAv α s) ^ 2 := by
  have hL := hin.lEta_pos
  set Cw : (Fin (n + 1) → Fin N) → Fin (n + 1) → Matrix (Fin N) (Fin N) ℂ := fun α j =>
    qvW P s H (σ j) ((qvPairs σ α).drop j ++ (α (Fin.last n), σ 0) :: (qvPairs σ α).take j)
  have hterm : ∀ α a b, Matrix.trace ((1 : Matrix (Fin N) (Fin N) ℂ) *
      firstVar (avSlots P.S α) (fun j => qvRes P s H (σ j)) (Matrix.single a b (1 : ℂ))) =
      ∑ j, Cw α j b a := by
    intro α a b
    rw [Matrix.one_mul, firstVar, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun j _ => qv_av_term P s H σ α j a b
  simp_rw [hterm]
  refine (qv_bracket_le P.S hin.sNonneg c (fun α j a b => Cw α j b a)).trans ?_
  rw [Fintype.card_fin]
  have hQ : ∀ α j, ∑ a, ∑ b, P.S a b * ‖Cw α j b a‖ ^ 2 ≤
      qvBndAv d P psiI psiA LamM s (n + 1) * P.sAv α s ^ 2 := by
    intro α j
    have h := qv_av_density hin hA hH hLam hI hAv hL1 hn σ α j
    refine le_trans (le_of_eq ?_) h
    unfold qvQAv
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hin.sSymm]
  have h := qv_sum_sqrt_le c (fun α j => ∑ a, ∑ b, P.S a b * ‖Cw α j b a‖ ^ 2) (fun α => P.sAv α s)
    (qvBndAv_nonneg hin (n + 1) hLam) (fun α => by
      rw [sAv_eq_sqrt P hin.nonneg hL]; exact Real.sqrt_nonneg _) hQ
  rw [Fintype.card_fin] at h
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
  refine this.trans (le_of_eq ?_)
  push_cast
  ring

/-- **The bracket density, isotropic chains**: for chains of length `k = n + 1 ≤ 8` along `σ`
with end points `a', b'` (`K = E_{b'a'}`, as in `Evol.duhamel_iso`), the bracket density is
`≤ k² · qvBndIso_k · (Σ_α |c_α| s^iso(a', α, b'))²`.
Conditional as `qv_QV_iso_first`.
-/
theorem qv_bracket_iso (hES : Split.ExplicitShortStatement) (hS : StochasticSymm P.S)
    (hz : P.z.im ≠ 0) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hstab : ∀ x y, ‖Split.stabOp s P.S (semicircleM P.z * conj (semicircleM P.z)) x y‖ ≤
      (if x = y then 1 else 0) + Propagator.vsCK d * P.ups s x y)
    {n : ℕ} (hn : n + 1 ≤ 8) (σ : Fin (n + 1) → Bool) (a' b' : Fin N)
    (c : (Fin (n + 1) → Fin N) → ℂ) :
    ∑ a, ∑ b, P.S a b * ‖∑ α, c α * Matrix.trace ((Matrix.single b' a' (1 : ℂ) :
      Matrix (Fin N) (Fin N) ℂ) * firstVar (isoSlots P.S α) (fun j => qvRes P s H (σ j))
        (Matrix.single a b (1 : ℂ)))‖ ^ 2 ≤
      ((n : ℝ) + 1) ^ 2 * qvBndIso d P psiI psiA LamM s (n + 1) *
        (∑ α, ‖c α‖ * P.sIso a' b' α s) ^ 2 := by
  have hL := hin.lEta_pos
  set v : (Fin (n + 1) → Fin N) → Fin (n + 1) → Fin N → Fin N → ℂ := fun α j a b =>
    qvW P s H (σ 0) ((qvPairs σ α).take j) a' a * qvW P s H (σ j) ((qvPairs σ α).drop j) b b'
  have hterm : ∀ α a b, Matrix.trace ((Matrix.single b' a' (1 : ℂ) :
      Matrix (Fin N) (Fin N) ℂ) * firstVar (isoSlots P.S α) (fun j => qvRes P s H (σ j))
        (Matrix.single a b (1 : ℂ))) = ∑ j, v α j a b := by
    intro α a b
    rw [firstVar, Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.trace_single_mul, one_smul]
    exact qv_iso_term P s H σ α j a' b' a b
  simp_rw [hterm]
  refine (qv_bracket_le P.S hin.sNonneg c v).trans ?_
  rw [Fintype.card_fin]
  have hQ : ∀ α j, ∑ a, ∑ b, P.S a b * ‖v α j a b‖ ^ 2 ≤
      qvBndIso d P psiI psiA LamM s (n + 1) * P.sIso a' b' α s ^ 2 := by
    intro α j
    have h := qv_iso_density hin hA hH hLam hI hAv hL1 hES hS hz hs hstab hn σ α j a' b'
    refine le_trans (le_of_eq ?_) h
    unfold qvQIso
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [v, norm_mul, mul_pow]
    rw [hin.sSymm]
    ring
  have h := qv_sum_sqrt_le c (fun α j => ∑ a, ∑ b, P.S a b * ‖v α j a b‖ ^ 2)
    (fun α => P.sIso a' b' α s) (qvBndIso_nonneg hin (n + 1) hLam) (fun α => by
      rw [Contr.contr_sIso_eq]
      exact mul_nonneg (Real.rpow_nonneg hL.le _) (Real.sqrt_nonneg _)) hQ
  rw [Fintype.card_fin] at h
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
  refine this.trans (le_of_eq ?_)
  push_cast
  ring

end Densities

end BlockBand.Native.ErdosRiabov.QV
