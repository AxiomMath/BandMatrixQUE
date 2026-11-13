module

public import BlockBand.Native.ErdosRiabov.Psi.Defs

/-!
# Local contractions: generic part

Contraction lemmas for products of square roots of a nonnegative weight, and size functions as
path products.

* **Generic contraction lemmas** for a nonnegative weight `U` on a finite index type, with all
  factors not containing the contracted index `q` collected in `R ≥ 0` and a scalar `c ≥ 0`:
  - `localContraction_sum` (four factors, summed, by a Schwarz bound (U6) with constant `K`);
  - `localContraction_max` (four factors, pointwise, by the triangle bound (U4) used twice);
  - `localContraction_two_sum` (two factors, summed, by a √-convolution bound such as (U7));
  - `localContraction_two_max` (two factors, pointwise, by (U4); constant `√K`).
  - `localContraction_profile` (the `S`-weighted double sum of the `S`-bound, by the profile
    bound `S Υ ≤ C_S Υ` and (U5)).

  Here (U4)–(U7) are the corresponding hypotheses on `U`, named after the properties of the
  control `Υ` given by `LemmaK.ups_U2_U8_vs`.
* **Path products** `contrPathProd U p n = ∏_{m<n} U(p_m, p_{m+1})` and the cyclic site sequence
  `contrCycPt`, with the splitting rules used to reassemble size functions:
  `PsiData.sIso` is `(ℓη)^{-(k-1)/2} √(contrPathProd Υ (isoPoint a b x) k)` (`contr_sIso_eq`),
  and for `k ≥ 2`, `PsiData.sAv` is `(ℓη)^{-k/2} √(contrPathProd Υ (contrCycPt x x₀) k)`
  (`contr_sAv_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Contr

open BlockBand.Native.ErdosRiabov.Psi

/-!
## Generic contraction lemmas
-/

section Generic

variable {ι : Type} {U : ι → ι → ℝ}

/-- **Generic four-factor contraction (sum).** If `U ≥ 0` satisfies the Schwarz bound
`Σ_q √(U(x₁,q)U(x₂,q)U(q,y₁)U(q,y₂)) ≤ K √(U(x₁,y₁)U(x₂,y₂))`, then for `c, R ≥ 0`:
`Σ_q c √(R · U(x₁,q)U(x₂,q)U(q,y₁)U(q,y₂)) ≤ K · c √(R · U(x₁,y₁)U(x₂,y₂))`. -/
theorem localContraction_sum [Fintype ι] {K : ℝ}
    (h6 : ∀ x₁ x₂ y₁ y₂, ∑ q, Real.sqrt (U x₁ q * U x₂ q * U q y₁ * U q y₂) ≤
      K * Real.sqrt (U x₁ y₁ * U x₂ y₂))
    {c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R) (x₁ x₂ y₁ y₂ : ι) :
    ∑ q, c * Real.sqrt (R * (U x₁ q * U x₂ q * U q y₁ * U q y₂)) ≤
      K * (c * Real.sqrt (R * (U x₁ y₁ * U x₂ y₂))) := by
  simp_rw [Real.sqrt_mul hR]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (h6 x₁ x₂ y₁ y₂) (mul_nonneg hc (Real.sqrt_nonneg R))
  calc c * (Real.sqrt R * ∑ q, Real.sqrt (U x₁ q * U x₂ q * U q y₁ * U q y₂))
      = c * Real.sqrt R * ∑ q, Real.sqrt (U x₁ q * U x₂ q * U q y₁ * U q y₂) := by ring
    _ ≤ c * Real.sqrt R * (K * Real.sqrt (U x₁ y₁ * U x₂ y₂)) := h
    _ = K * (c * (Real.sqrt R * Real.sqrt (U x₁ y₁ * U x₂ y₂))) := by ring

/-- **Generic four-factor contraction (maximum).** If `U ≥ 0` satisfies the triangle bound
`U(x,a)U(a,y) ≤ K U(x,y)` with `K ≥ 0`, then for `c, R ≥ 0` and every `q`:
`c √(R · U(x₁,q)U(x₂,q)U(q,y₁)U(q,y₂)) ≤ K · c √(R · U(x₁,y₁)U(x₂,y₂))`. -/
theorem localContraction_max (hU : ∀ x y, 0 ≤ U x y) {K : ℝ} (hK : 0 ≤ K)
    (h4 : ∀ x a y, U x a * U a y ≤ K * U x y) {c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R)
    (x₁ x₂ y₁ y₂ q : ι) :
    c * Real.sqrt (R * (U x₁ q * U x₂ q * U q y₁ * U q y₂)) ≤
      K * (c * Real.sqrt (R * (U x₁ y₁ * U x₂ y₂))) := by
  have h1 : U x₁ q * U x₂ q * U q y₁ * U q y₂ ≤ K ^ 2 * (U x₁ y₁ * U x₂ y₂) := by
    have e : U x₁ q * U x₂ q * U q y₁ * U q y₂ = (U x₁ q * U q y₁) * (U x₂ q * U q y₂) := by
      ring
    rw [e]
    calc (U x₁ q * U q y₁) * (U x₂ q * U q y₂) ≤ (K * U x₁ y₁) * (K * U x₂ y₂) :=
          mul_le_mul (h4 _ _ _) (h4 _ _ _) (mul_nonneg (hU _ _) (hU _ _))
            (mul_nonneg hK (hU _ _))
      _ = K ^ 2 * (U x₁ y₁ * U x₂ y₂) := by ring
  have h2 : Real.sqrt (R * (U x₁ q * U x₂ q * U q y₁ * U q y₂)) ≤
      K * Real.sqrt (R * (U x₁ y₁ * U x₂ y₂)) := by
    calc Real.sqrt (R * (U x₁ q * U x₂ q * U q y₁ * U q y₂))
        ≤ Real.sqrt (K ^ 2 * (R * (U x₁ y₁ * U x₂ y₂))) := by
          apply Real.sqrt_le_sqrt
          nlinarith [mul_le_mul_of_nonneg_left h1 hR]
      _ = K * Real.sqrt (R * (U x₁ y₁ * U x₂ y₂)) := by
          rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
  calc c * Real.sqrt (R * (U x₁ q * U x₂ q * U q y₁ * U q y₂))
      ≤ c * (K * Real.sqrt (R * (U x₁ y₁ * U x₂ y₂))) := mul_le_mul_of_nonneg_left h2 hc
    _ = K * (c * Real.sqrt (R * (U x₁ y₁ * U x₂ y₂))) := by ring

/-- **Two-factor contraction (sum).** If `Σ_q √(U(x,q)U(q,y)) ≤ K √(U(x,y))`, then for
`c, R ≥ 0`: `Σ_q c √(R · U(x,q)U(q,y)) ≤ K · c √(R · U(x,y))`. -/
theorem localContraction_two_sum [Fintype ι] {K : ℝ}
    (h7 : ∀ x y, ∑ q, Real.sqrt (U x q * U q y) ≤ K * Real.sqrt (U x y))
    {c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R) (x y : ι) :
    ∑ q, c * Real.sqrt (R * (U x q * U q y)) ≤ K * (c * Real.sqrt (R * U x y)) := by
  simp_rw [Real.sqrt_mul hR]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (h7 x y) (mul_nonneg hc (Real.sqrt_nonneg R))
  calc c * (Real.sqrt R * ∑ q, Real.sqrt (U x q * U q y))
      = c * Real.sqrt R * ∑ q, Real.sqrt (U x q * U q y) := by ring
    _ ≤ c * Real.sqrt R * (K * Real.sqrt (U x y)) := h
    _ = K * (c * (Real.sqrt R * Real.sqrt (U x y))) := by ring

/-- **Two-factor contraction (maximum).** If `U(x,a)U(a,y) ≤ K U(x,y)`, `K ≥ 0`, then for
`c, R ≥ 0` and every `q`: `c √(R · U(x,q)U(q,y)) ≤ √K · c √(R · U(x,y))`. -/
theorem localContraction_two_max {K : ℝ} (hK : 0 ≤ K)
    (h4 : ∀ x a y, U x a * U a y ≤ K * U x y) {c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R)
    (x y q : ι) :
    c * Real.sqrt (R * (U x q * U q y)) ≤ Real.sqrt K * (c * Real.sqrt (R * U x y)) := by
  have h2 : Real.sqrt (R * (U x q * U q y)) ≤ Real.sqrt K * Real.sqrt (R * U x y) := by
    rw [← Real.sqrt_mul hK]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_left (h4 x q y) hR]
  calc c * Real.sqrt (R * (U x q * U q y))
      ≤ c * (Real.sqrt K * Real.sqrt (R * U x y)) := mul_le_mul_of_nonneg_left h2 hc
    _ = Real.sqrt K * (c * Real.sqrt (R * U x y)) := by ring

/-- The `S`-weighted double contraction behind: if `S` is symmetric,
`Σ_a S(x,a)U(a,y) ≤ C_S U(x,y)` and `Σ_a U(x,a)U(a,y) ≤ K U(x,y)`, then for `c, R ≥ 0`,
`U ≥ 0`:
`Σ_{q'} Σ_q S(q',q) · c (U(q',a) R U(b,q)) ≤ C_S K · c R U(b,a)`.
-/
theorem localContraction_profile [Fintype ι] (hU : ∀ x y, 0 ≤ U x y)
    {S : ι → ι → ℝ} (hSsym : ∀ x y, S x y = S y x) {CS K : ℝ} (hCS : 0 ≤ CS)
    (hSU : ∀ x y, ∑ a, S x a * U a y ≤ CS * U x y)
    (h5 : ∀ x y, ∑ a, U x a * U a y ≤ K * U x y) {c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R)
    (a b : ι) :
    ∑ q', ∑ q, S q' q * (c * (U q' a * R * U b q)) ≤ CS * K * (c * R * U b a) := by
  rw [Finset.sum_comm]
  have hin : ∀ q, ∑ q', S q' q * (c * (U q' a * R * U b q)) ≤
      c * R * CS * (U b q * U q a) := by
    intro q
    have e : ∑ q', S q' q * (c * (U q' a * R * U b q)) =
        c * R * U b q * ∑ q', S q q' * U q' a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q' _ => ?_
      rw [hSsym q' q]
      ring
    rw [e]
    have hcr : 0 ≤ c * R * U b q := mul_nonneg (mul_nonneg hc hR) (hU _ _)
    calc c * R * U b q * ∑ q', S q q' * U q' a ≤ c * R * U b q * (CS * U q a) :=
          mul_le_mul_of_nonneg_left (hSU q a) hcr
      _ = c * R * CS * (U b q * U q a) := by ring
  calc ∑ q, ∑ q', S q' q * (c * (U q' a * R * U b q))
      ≤ ∑ q, c * R * CS * (U b q * U q a) := Finset.sum_le_sum fun q _ => hin q
    _ = c * R * CS * ∑ q, U b q * U q a := (Finset.mul_sum _ _ _).symm
    _ ≤ c * R * CS * (K * U b a) :=
        mul_le_mul_of_nonneg_left (h5 b a) (mul_nonneg (mul_nonneg hc hR) hCS)
    _ = CS * K * (c * R * U b a) := by ring

end Generic

/-!
## Path products
-/

variable {N : ℕ}

/-- The path product `∏_{m<n} U(p_m, p_{m+1})`. -/
def contrPathProd (U : Matrix (Fin N) (Fin N) ℝ) (p : ℕ → Fin N) (n : ℕ) : ℝ :=
  ∏ m ∈ Finset.range n, U (p m) (p (m + 1))

/-- The cyclic site sequence of `x : Fin k → Fin N`: `x_m` for `m < k`, the base point `a`
otherwise (used with `a = x₀`). -/
def contrCycPt {k : ℕ} (x : Fin k → Fin N) (a : Fin N) (m : ℕ) : Fin N :=
  if h : m < k then x ⟨m, h⟩ else a

/-- A path product of a nonnegative weight is nonnegative. -/
theorem contrPathProd_nonneg {U : Matrix (Fin N) (Fin N) ℝ} (hU : ∀ x y, 0 ≤ U x y)
    (p : ℕ → Fin N) (n : ℕ) : 0 ≤ contrPathProd U p n :=
  Finset.prod_nonneg fun _ _ => hU _ _

/-- `contrPathProd U p n` depends only on `p_0, …, p_n`. -/
theorem contrPathProd_congr (U : Matrix (Fin N) (Fin N) ℝ) {p p' : ℕ → Fin N} {n : ℕ}
    (h : ∀ m ≤ n, p m = p' m) : contrPathProd U p n = contrPathProd U p' n := by
  unfold contrPathProd
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [h m hm.le, h (m + 1) hm]

/-- The empty path product is `1`. -/
theorem contrPathProd_zero (U : Matrix (Fin N) (Fin N) ℝ) (p : ℕ → Fin N) :
    contrPathProd U p 0 = 1 := Finset.prod_range_zero _

/-- Splitting off the last edge. -/
theorem contrPathProd_succ (U : Matrix (Fin N) (Fin N) ℝ) (p : ℕ → Fin N) (n : ℕ) :
    contrPathProd U p (n + 1) = contrPathProd U p n * U (p n) (p (n + 1)) :=
  Finset.prod_range_succ _ _

/-- Splitting off the first edge. -/
theorem contrPathProd_succ' (U : Matrix (Fin N) (Fin N) ℝ) (p : ℕ → Fin N) (n : ℕ) :
    contrPathProd U p (n + 1) = U (p 0) (p 1) * contrPathProd U (fun m => p (m + 1)) n := by
  unfold contrPathProd
  rw [Finset.prod_range_succ', mul_comm]

/-- Splitting a path product at `n₁`. -/
theorem contrPathProd_add (U : Matrix (Fin N) (Fin N) ℝ) (p : ℕ → Fin N) (n₁ n₂ : ℕ) :
    contrPathProd U p (n₁ + n₂) =
      contrPathProd U p n₁ * contrPathProd U (fun m => p (n₁ + m)) n₂ := by
  unfold contrPathProd
  rw [Finset.prod_range_add]
  simp only [add_assoc]

/-- The cyclic product of `s^av` is a path product along `contrCycPt x x₀`. -/
theorem contr_cyc_prod (U : Matrix (Fin N) (Fin N) ℝ) {k : ℕ} (hk : 0 < k)
    (x : Fin k → Fin N) :
    ∏ j : Fin k, U (x j) (x (finRotate k j)) = contrPathProd U (contrCycPt x (x ⟨0, hk⟩)) k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  unfold contrPathProd
  rw [← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : contrCycPt x (x ⟨0, hk⟩) j = x j := by
    unfold contrCycPt
    rw [dite_eq_left j.isLt]
  rw [h1]
  congr 1
  unfold contrCycPt
  by_cases hj : j = Fin.last n
  · subst hj
    rw [finRotate_last, dite_eq_right (by simp)]
    rfl
  · have hv := coe_finRotate_of_ne_last hj
    have hlt : (j : ℕ) + 1 < n + 1 := by
      have := Fin.val_lt_last hj
      omega
    rw [dite_eq_left hlt]
    congr 1
    exact Fin.ext hv

/-!
## Site sequences
-/

/-- The first isotropic site is `a`. -/
theorem contr_isoPoint_zero {k : ℕ} (a b : Fin N) (x : Fin k → Fin N) : isoPoint a b x 0 = a := by
  unfold isoPoint
  rw [ite_eq_left rfl]

/-- The interior isotropic sites are the entries of `x`. -/
theorem contr_isoPoint_succ {k : ℕ} (a b : Fin N) (x : Fin k → Fin N) {m : ℕ} (h : m + 1 < k) :
    isoPoint a b x (m + 1) = x ⟨m, by omega⟩ := by
  unfold isoPoint
  rw [ite_eq_right (Nat.succ_ne_zero m), dite_eq_left h]
  rfl

/-- The isotropic sites from position `k` on are `b`. -/
theorem contr_isoPoint_of_le {k : ℕ} (a b : Fin N) (x : Fin k → Fin N) {m : ℕ} (h0 : m ≠ 0)
    (h : k ≤ m) : isoPoint a b x m = b := by
  unfold isoPoint
  rw [ite_eq_right h0, dite_eq_right (by omega)]

/-- The cyclic sites below `k` are the entries of `x`. -/
theorem contr_cycPt_lt {k : ℕ} (x : Fin k → Fin N) (a : Fin N) {m : ℕ} (h : m < k) :
    contrCycPt x a m = x ⟨m, h⟩ := by
  unfold contrCycPt
  rw [dite_eq_left h]

/-- The cyclic sites from `k` on are the base point. -/
theorem contr_cycPt_ge {k : ℕ} (x : Fin k → Fin N) (a : Fin N) {m : ℕ} (h : k ≤ m) :
    contrCycPt x a m = a := by
  unfold contrCycPt
  rw [dite_eq_right (by omega)]

/-!
## Size functions as path products
-/

variable (P : PsiData N)

/-- `s^iso_k = (ℓη)^{-(k-1)/2} √(Π Υ)` along `isoPoint a b x` (definitional). -/
theorem contr_sIso_eq {k : ℕ} (a b : Fin N) (x : Fin k → Fin N) (t : ℝ) :
    P.sIso a b x t = P.lEta t ^ (-((k : ℝ) - 1) / 2) *
      Real.sqrt (contrPathProd (P.ups t) (isoPoint a b x) k) := rfl

/-- For `k ≥ 2`, `s^av_k = (ℓη)^{-k/2} √(Π Υ)` along the cyclic sites `contrCycPt x x₀`. -/
theorem contr_sAv_eq {k : ℕ} (hk : 2 ≤ k) (x : Fin k → Fin N) (t : ℝ) :
    P.sAv x t = P.lEta t ^ (-(k : ℝ) / 2) *
      Real.sqrt (contrPathProd (P.ups t) (contrCycPt x (x ⟨0, by omega⟩)) k) := by
  unfold PsiData.sAv
  rw [ite_eq_right (by omega), contr_cyc_prod]

/-- `s^av_1 = 1/(ℓη)`. -/
theorem contr_sAv_one {k : ℕ} (hk : k = 1) (x : Fin k → Fin N) (t : ℝ) :
    P.sAv x t = (P.lEta t)⁻¹ := by
  unfold PsiData.sAv
  rw [ite_eq_left hk]

end BlockBand.Native.ErdosRiabov.Contr
