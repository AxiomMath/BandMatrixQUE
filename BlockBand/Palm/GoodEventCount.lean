module

public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Good spectral event: deterministic counting combinatorics

Pure deterministic statements about a finite real sequence `lam : Fin N → ℝ` (in use, the
increasing eigenvalues `λ_k(s)`), with no measure:

* `count_le_of_mesh`: the floor covering `λ ∈ [⌊λ/h⌋h, ⌊λ/h⌋h + h]` turns mesh counts
  `#{|λ - kh| ≤ h} ≤ M` into `#[x,y] ≤ M((y-x)/h + 2)`.
* `longGap_of_upper`: the upper count gives `|λ_i - λ_j| ≥ (|i-j|+1)/(CN) - h`, the long-gap
  lower bound once `Nh = o(ℓ)`.
* `shortGap_of_lower`: the lower count on the window `[E - r₀/4, E + r₀/4]` gives the gap upper
  bound `|λ_i - λ_j| ≤ (1 + 1/c')ℓ/N` for bulk labels at label distance `< ℓ`.
* `longCoupling_sum_le`, `longCoupling_sum_ge`: `β_i ≤ 4N/(c₁²ℓ)` from the long-gap lower bound,
  and `β_i ≥ c'²N/(9ℓ)` for bulk labels from the lower count.
* `count_upper_transfer`, `count_lower_transfer`: Weyl transfer of counts.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-!
## Label distance
-/

theorem labelDist_comm (i j : Fin N) : labelDist i j = labelDist j i := by
  simp only [labelDist]; omega

theorem labelDist_of_le {i j : Fin N} (h : i ≤ j) : labelDist i j = j.val - i.val := by
  have : i.val ≤ j.val := h
  simp only [labelDist]; omega

/-!
## Weyl transfer of counts
-/

theorem count_upper_transfer (lam lam' : Fin N → ℝ) {ε : ℝ} (hε : ∀ i, |lam i - lam' i| ≤ ε)
    (x y : ℝ) :
    (Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card ≤
      (Finset.univ.filter fun i => lam' i ∈ Set.Icc (x - ε) (y + ε)).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc] at hi ⊢
  have := abs_le.mp (hε i)
  constructor <;> linarith [hi.1, hi.2]

theorem count_lower_transfer (lam lam' : Fin N → ℝ) {ε : ℝ} (hε : ∀ i, |lam i - lam' i| ≤ ε)
    (x y : ℝ) :
    (Finset.univ.filter fun i => lam' i ∈ Set.Icc (x + ε) (y - ε)).card ≤
      (Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc] at hi ⊢
  have := abs_le.mp (hε i)
  constructor <;> linarith [hi.1, hi.2]

/-!
## Upper count from a mesh
-/

/-- **Floor covering.** Mesh counts `#{|λ - kh| ≤ h} ≤ M` for `|k| ≤ K+1` and the range
`|λ_i| ≤ Kh` give `#{λ ∈ [x,y]} ≤ M((y-x)/h + 2)` for every `x ≤ y`. -/
theorem count_le_of_mesh (lam : Fin N → ℝ) {h M : ℝ} (hh : 0 < h) (K : ℕ)
    (hrange : ∀ i, |lam i| ≤ (K : ℝ) * h)
    (hmesh : ∀ k : ℤ, |k| ≤ (K : ℤ) + 1 →
      ((Finset.univ.filter fun i => |lam i - (k : ℝ) * h| ≤ h).card : ℝ) ≤ M)
    (x y : ℝ) (hxy : x ≤ y) :
    ((Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card : ℝ) ≤ M * ((y - x) / h + 2) := by
  classical
  have hM : 0 ≤ M := le_trans (Nat.cast_nonneg _) (hmesh 0 (by positivity))
  set S := Finset.univ.filter fun i => lam i ∈ Set.Icc x y with hS
  set f : Fin N → ℤ := fun i => ⌊lam i / h⌋ with hf
  set T : Finset ℤ := Finset.Icc ⌊x / h⌋ ⌊y / h⌋ with hT
  have hfl : ∀ i, (f i : ℝ) * h ≤ lam i ∧ lam i < ((f i : ℝ) + 1) * h := by
    intro i
    have h1 := Int.floor_le (lam i / h)
    have h2 := Int.lt_floor_add_one (lam i / h)
    constructor
    · have := mul_le_mul_of_nonneg_right h1 hh.le
      rwa [div_mul_cancel₀ _ hh.ne'] at this
    · have := mul_lt_mul_of_pos_right h2 hh
      rwa [div_mul_cancel₀ _ hh.ne'] at this
  have hmaps : Set.MapsTo f (S : Set (Fin N)) (T : Set ℤ) := by
    intro i hi
    simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Set.mem_Icc] at hi
    simp only [hT, Finset.coe_Icc, Set.mem_Icc]
    constructor
    · exact Int.floor_le_floor (div_le_div_of_nonneg_right hi.1 hh.le)
    · exact Int.floor_le_floor (div_le_div_of_nonneg_right hi.2 hh.le)
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ k ∈ T, (({i ∈ S | f i = k}).card : ℝ) ≤ M := by
    intro k _
    by_cases hne : ({i ∈ S | f i = k}).Nonempty
    · obtain ⟨i₀, hi₀⟩ := hne
      have hi₀k : f i₀ = k := (Finset.mem_filter.mp hi₀).2
      have hk : |k| ≤ (K : ℤ) + 1 := by
        have hr := abs_le.mp (hrange i₀)
        obtain ⟨h1, h2⟩ := hfl i₀
        rw [hi₀k] at h1 h2
        have hu : (k : ℝ) ≤ (K : ℝ) + 1 := by
          have : (k : ℝ) * h ≤ (K : ℝ) * h := le_trans h1 hr.2
          have := le_of_mul_le_mul_right this hh
          linarith
        have hl : -((K : ℝ) + 1) ≤ (k : ℝ) := by
          have : -((K : ℝ) * h) < ((k : ℝ) + 1) * h := lt_of_le_of_lt hr.1 h2
          have h3 : (-(K : ℝ) - 1) * h < (k : ℝ) * h := by nlinarith
          have := lt_of_mul_lt_mul_right h3 hh.le
          linarith
        rw [abs_le]
        constructor
        · exact_mod_cast hl
        · exact_mod_cast hu
      refine le_trans ?_ (hmesh k hk)
      exact_mod_cast Finset.card_le_card (by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        obtain ⟨h1, h2⟩ := hfl i
        rw [hi.2] at h1 h2
        rw [abs_le]
        constructor <;> nlinarith)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      exact hM
  have hsum : (S.card : ℝ) ≤ T.card * M := by
    rw [hcard, Nat.cast_sum]
    calc ∑ k ∈ T, (({i ∈ S | f i = k}).card : ℝ) ≤ ∑ _k ∈ T, M := Finset.sum_le_sum hfib
      _ = T.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
  have hTc : (T.card : ℝ) ≤ (y - x) / h + 2 := by
    rw [hT, Int.card_Icc]
    have hle : ⌊x / h⌋ ≤ ⌊y / h⌋ := Int.floor_le_floor (div_le_div_of_nonneg_right hxy hh.le)
    have hnn : 0 ≤ ⌊y / h⌋ + 1 - ⌊x / h⌋ := by omega
    rw [show (((⌊y / h⌋ + 1 - ⌊x / h⌋).toNat : ℕ) : ℝ) = ((⌊y / h⌋ + 1 - ⌊x / h⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg hnn]
    push_cast
    have h1 := Int.floor_le (y / h)
    have h2 := Int.lt_floor_add_one (x / h)
    rw [sub_div]
    linarith
  calc (S.card : ℝ) ≤ T.card * M := hsum
    _ ≤ ((y - x) / h + 2) * M := mul_le_mul_of_nonneg_right hTc hM
    _ = M * ((y - x) / h + 2) := mul_comm _ _

/-!
## Long gaps from the upper count
-/

theorem longGap_aux (lam : Fin N → ℝ) (hmono : Monotone lam) {C h : ℝ} (hC : 0 < C)
    (hN : 0 < N)
    (hup : ∀ x y, x ≤ y →
      ((Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card : ℝ) ≤ C * N * ((y - x) + h))
    {i j : Fin N} (hij : i ≤ j) :
    ((labelDist i j : ℝ) + 1) / (C * N) - h ≤ |lam i - lam j| := by
  have hlij : lam i ≤ lam j := hmono hij
  have hsub : Finset.Icc i j ⊆ Finset.univ.filter fun k => lam k ∈ Set.Icc (lam i) (lam j) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
    exact ⟨hmono hk.1, hmono hk.2⟩
  have hc := Finset.card_le_card hsub
  rw [Fin.card_Icc] at hc
  have hd : ((labelDist i j : ℝ) + 1) ≤ ((j.val + 1 - i.val : ℕ) : ℝ) := by
    rw [labelDist_of_le hij]
    have : i.val ≤ j.val := hij
    exact_mod_cast (by omega : j.val - i.val + 1 ≤ j.val + 1 - i.val)
  have h1 : ((labelDist i j : ℝ) + 1) ≤ C * N * ((lam j - lam i) + h) :=
    hd.trans ((Nat.cast_le.mpr hc).trans (hup _ _ hlij))
  have hCN : 0 < C * N := mul_pos hC (by exact_mod_cast hN)
  rw [abs_sub_comm, abs_of_nonneg (by linarith), sub_le_iff_le_add, div_le_iff₀ hCN]
  linarith

theorem longGap_of_upper (lam : Fin N → ℝ) (hmono : Monotone lam) {C h : ℝ} (hC : 0 < C)
    (hN : 0 < N)
    (hup : ∀ x y, x ≤ y →
      ((Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card : ℝ) ≤ C * N * ((y - x) + h))
    (i j : Fin N) : ((labelDist i j : ℝ) + 1) / (C * N) - h ≤ |lam i - lam j| := by
  rcases le_total i j with hij | hij
  · exact longGap_aux lam hmono hC hN hup hij
  · rw [labelDist_comm, abs_sub_comm]
    exact longGap_aux lam hmono hC hN hup hij

/-!
## Short gaps in the bulk from the lower count
-/

/-- Values strictly between `λ_a` and `λ_b` have ranks strictly between `a` and `b`. -/
theorem card_between_lt (lam : Fin N → ℝ) (hmono : Monotone lam) {a b : Fin N} {x y : ℝ}
    (hxy : x ≤ y) (hx : lam a < x) (hy : y < lam b) :
    (Finset.univ.filter fun k => lam k ∈ Set.Icc x y).card < labelDist a b := by
  have hab : a < b := by
    by_contra hc
    have := hmono (not_lt.mp hc)
    linarith
  have hsub : (Finset.univ.filter fun k => lam k ∈ Set.Icc x y) ⊆ Finset.Ioo a b := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc] at hk
    rw [Finset.mem_Ioo]
    constructor
    · by_contra hc
      have := hmono (not_lt.mp hc)
      linarith
    · by_contra hc
      have := hmono (not_lt.mp hc)
      linarith
  have hc := Finset.card_le_card hsub
  rw [Fin.card_Ioo] at hc
  rw [labelDist_of_le hab.le]
  have : a.val < b.val := hab
  omega

theorem shortGap_aux (lam : Fin N → ℝ) (hmono : Monotone lam) {c' Lmin E r₀ : ℝ} {ℓ : ℕ}
    (hc' : 0 < c') (hN : 0 < N)
    (hlow : ∀ x y, E - r₀ / 4 ≤ x → y ≤ E + r₀ / 4 → Lmin ≤ y - x →
      c' * N * (y - x) ≤ ((Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card : ℝ))
    (hlen : Lmin ≤ ℓ / (c' * N)) (hwin : (1 + 1 / c') * ℓ / N ≤ r₀ / 8)
    (i j : Fin N) (hij : labelDist i j < ℓ) (hE : |lam i - E| ≤ r₀ / 8) :
    |lam i - lam j| ≤ (1 + 1 / c') * ℓ / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓ : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hij)
  have hD : (1 + 1 / c') * ℓ / N = ℓ / N + ℓ / (c' * N) := by field_simp
  have hp1 : 0 < (ℓ : ℝ) / N := div_pos hℓ hNr
  have hp2 : 0 < (ℓ : ℝ) / (c' * N) := div_pos hℓ (mul_pos hc' hNr)
  have hEi := abs_le.mp hE
  have hr : 0 ≤ r₀ := by linarith
  have hcount : c' * N * ((ℓ : ℝ) / (c' * N)) = ℓ := by field_simp
  by_contra hc
  rw [not_le, hD] at hc
  rcases lt_abs.mp hc with hc | hc
  · -- `λ_i` far above `λ_j`
    have hcl := hlow (lam i - ℓ / N - ℓ / (c' * N)) (lam i - ℓ / N) (by linarith) (by linarith)
      (by linarith)
    have hlt := card_between_lt lam hmono (a := j) (b := i) (x := lam i - ℓ / N - ℓ / (c' * N))
      (y := lam i - ℓ / N) (by linarith) (by linarith) (by linarith)
    rw [labelDist_comm] at hlt
    have h1 : ((Finset.univ.filter fun k => lam k ∈ Set.Icc
        (lam i - ℓ / N - ℓ / (c' * N)) (lam i - ℓ / N)).card : ℝ) < ℓ := by
      exact_mod_cast lt_trans hlt hij
    have h2 : c' * N * ((lam i - ℓ / N) - (lam i - ℓ / N - ℓ / (c' * N))) = ℓ := by
      rw [show (lam i - ℓ / N) - (lam i - ℓ / N - ℓ / (c' * N)) = ℓ / (c' * N) by ring, hcount]
    linarith
  · -- `λ_j` far above `λ_i`
    have hcl := hlow (lam i + ℓ / N) (lam i + ℓ / N + ℓ / (c' * N)) (by linarith) (by linarith)
      (by linarith)
    have hlt := card_between_lt lam hmono (a := i) (b := j) (x := lam i + ℓ / N)
      (y := lam i + ℓ / N + ℓ / (c' * N)) (by linarith) (by linarith) (by linarith)
    have h1 : ((Finset.univ.filter fun k => lam k ∈ Set.Icc
        (lam i + ℓ / N) (lam i + ℓ / N + ℓ / (c' * N))).card : ℝ) < ℓ := by
      exact_mod_cast lt_trans hlt hij
    have h2 : c' * N * ((lam i + ℓ / N + ℓ / (c' * N)) - (lam i + ℓ / N)) = ℓ := by
      rw [show (lam i + ℓ / N + ℓ / (c' * N)) - (lam i + ℓ / N) = ℓ / (c' * N) by ring, hcount]
    linarith

theorem shortGap_of_lower (lam : Fin N → ℝ) (hmono : Monotone lam) {c' Lmin E r₀ : ℝ} {ℓ : ℕ}
    (hc' : 0 < c') (hN : 0 < N)
    (hlow : ∀ x y, E - r₀ / 4 ≤ x → y ≤ E + r₀ / 4 → Lmin ≤ y - x →
      c' * N * (y - x) ≤ ((Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card : ℝ))
    (hlen : Lmin ≤ ℓ / (c' * N)) (hwin : (1 + 1 / c') * ℓ / N ≤ r₀ / 8)
    (i j : Fin N) (hij : labelDist i j < ℓ) (hE : min |lam i - E| |lam j - E| ≤ r₀ / 8) :
    |lam i - lam j| ≤ (1 + 1 / c') * ℓ / N := by
  rcases min_le_iff.mp hE with hE | hE
  · exact shortGap_aux lam hmono hc' hN hlow hlen hwin i j hij hE
  · rw [abs_sub_comm]
    exact shortGap_aux lam hmono hc' hN hlow hlen hwin j i (by rwa [labelDist_comm]) hE

/-!
## Long couplings
-/

/-- `Σ_{d ∈ [ℓ, ℓ+n)} d⁻² ≤ 2/ℓ - 2/(ℓ+n)`. -/
theorem sum_inv_sq_Ico_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (n : ℕ) :
    ∑ d ∈ Finset.Ico ℓ (ℓ + n), 1 / ((d : ℝ) ^ 2) ≤ 2 / (ℓ : ℝ) - 2 / ((ℓ + n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have hx : (1 : ℝ) ≤ ((ℓ + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ ℓ + n)
    set x : ℝ := ((ℓ + n : ℕ) : ℝ) with hxdef
    have hstep : 1 / x ^ 2 ≤ 2 / x - 2 / ((ℓ + n + 1 : ℕ) : ℝ) := by
      rw [show ((ℓ + n + 1 : ℕ) : ℝ) = x + 1 by rw [hxdef]; push_cast; ring]
      have hx0 : 0 < x := by linarith
      rw [div_sub_div _ _ hx0.ne' (by linarith), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

theorem sum_inv_sq_Ico_le' {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (M : ℕ) :
    ∑ d ∈ Finset.Ico ℓ M, 1 / ((d : ℝ) ^ 2) ≤ 2 / (ℓ : ℝ) := by
  rcases le_or_gt M ℓ with h | h
  · rw [Finset.Ico_eq_empty (not_lt.mpr h)]
    simp only [Finset.sum_empty]
    positivity
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h.le
    refine (sum_inv_sq_Ico_le hℓ n).trans ?_
    have : 0 ≤ 2 / ((ℓ + n : ℕ) : ℝ) := by positivity
    linarith

/-- `Σ_{m : ℓ ≤ |i-m|} |i-m|⁻² ≤ 4/ℓ`. -/
theorem sum_inv_labelDist_sq_le (i : Fin N) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∑ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist i m), 1 / ((labelDist i m : ℝ) ^ 2) ≤
      4 / (ℓ : ℝ) := by
  classical
  set A := Finset.univ.filter (fun m : Fin N => ℓ ≤ labelDist i m)
  set g : ℕ → ℝ := fun d => 1 / ((d : ℝ) ^ 2) with hg
  have hg0 : ∀ d, 0 ≤ g d := fun d => by positivity
  have hpart : ∀ (P : Fin N → Prop) [DecidablePred P],
      (Set.InjOn (fun m => labelDist i m) ↑(A.filter P)) →
      ∑ m ∈ A.filter P, g (labelDist i m) ≤ 2 / (ℓ : ℝ) := by
    intro P _ hinj
    rw [← Finset.sum_image hinj]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Ico ℓ N) ?_
      (fun d _ _ => hg0 d)) (sum_inv_sq_Ico_le' hℓ N)
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨m, hm, rfl⟩ := hd
    rw [Finset.mem_filter] at hm
    have hm1 := (Finset.mem_filter.mp hm.1).2
    rw [Finset.mem_Ico]
    refine ⟨hm1, ?_⟩
    have := i.isLt
    have := m.isLt
    simp only [labelDist]
    omega
  have h1 := hpart (fun m => i < m) (by
    intro m hm m' hm' he
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hm hm'
    have h1 : i.val < m.val := hm.2
    have h2 : i.val < m'.val := hm'.2
    simp only [labelDist] at he
    exact Fin.ext (by omega))
  have h2 := hpart (fun m => ¬ i < m) (by
    intro m hm m' hm' he
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, not_lt] at hm hm'
    have h1 : m.val ≤ i.val := hm.2
    have h2 : m'.val ≤ i.val := hm'.2
    simp only [labelDist] at he
    exact Fin.ext (by omega))
  rw [← Finset.sum_filter_add_sum_filter_not A (fun m => i < m)]
  have : (4 : ℝ) / ℓ = 2 / ℓ + 2 / ℓ := by ring
  rw [this]
  exact add_le_add h1 h2

/-- **`β_i ≤ CN/ℓ`** from the long-gap lower bound. -/
theorem longCoupling_sum_le (lam : Fin N → ℝ) {c₁ : ℝ} (hc₁ : 0 < c₁) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hN : 0 < N)
    (hgap : ∀ i j : Fin N, ℓ ≤ labelDist i j → c₁ * (labelDist i j : ℝ) / N ≤ |lam i - lam j|)
    (i : Fin N) :
    ∑ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist i m), ((N : ℝ) * (lam i - lam m) ^ 2)⁻¹ ≤
      4 / c₁ ^ 2 * N / ℓ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist i m),
      ((N : ℝ) * (lam i - lam m) ^ 2)⁻¹ ≤ (N / c₁ ^ 2) * (1 / ((labelDist i m : ℝ) ^ 2)) := by
    intro m hm
    have hd := (Finset.mem_filter.mp hm).2
    have hd1 : (1 : ℝ) ≤ labelDist i m := by exact_mod_cast le_trans hℓ hd
    have hg := hgap i m hd
    have hpos : 0 < c₁ * (labelDist i m : ℝ) / N := by positivity
    have hsq : (c₁ * (labelDist i m : ℝ) / N) ^ 2 ≤ (lam i - lam m) ^ 2 := by
      rw [← sq_abs (lam i - lam m)]
      exact pow_le_pow_left₀ hpos.le hg 2
    have hlow : 0 < (N : ℝ) * (c₁ * (labelDist i m : ℝ) / N) ^ 2 := by positivity
    calc ((N : ℝ) * (lam i - lam m) ^ 2)⁻¹ ≤ ((N : ℝ) * (c₁ * (labelDist i m : ℝ) / N) ^ 2)⁻¹ :=
          inv_anti₀ hlow (mul_le_mul_of_nonneg_left hsq hNr.le)
      _ = (N / c₁ ^ 2) * (1 / ((labelDist i m : ℝ) ^ 2)) := by
          field_simp
  calc _ ≤ ∑ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist i m),
        (N / c₁ ^ 2) * (1 / ((labelDist i m : ℝ) ^ 2)) := Finset.sum_le_sum hterm
    _ = (N / c₁ ^ 2) * ∑ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist i m),
        1 / ((labelDist i m : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (N / c₁ ^ 2) * (4 / ℓ) :=
        mul_le_mul_of_nonneg_left (sum_inv_labelDist_sq_le i hℓ) (by positivity)
    _ = 4 / c₁ ^ 2 * N / ℓ := by ring

/-- `#{k : |i-k| < ℓ} ≤ 2ℓ - 1`. -/
theorem card_near_le (i : Fin N) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ((Finset.univ.filter fun k : Fin N => labelDist i k < ℓ).card : ℝ) ≤ 2 * ℓ - 1 := by
  have h := Finset.card_le_card_of_injOn (fun k : Fin N => (k.val : ℤ))
    (t := Finset.Ioo ((i.val : ℤ) - ℓ) ((i.val : ℤ) + ℓ))
    (s := Finset.univ.filter fun k : Fin N => labelDist i k < ℓ)
    (by
      intro k hk
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hk
      simp only [Finset.coe_Ioo, Set.mem_Ioo]
      simp only [labelDist] at hk
      omega)
    (by
      intro k _ k' _ he
      exact Fin.ext (by simpa using he))
  rw [Int.card_Ioo] at h
  have : ((i.val : ℤ) + ℓ - ((i.val : ℤ) - ℓ) - 1).toNat = 2 * ℓ - 1 := by omega
  rw [this] at h
  have h' : ((2 * ℓ - 1 : ℕ) : ℝ) = 2 * ℓ - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [← h']
  exact_mod_cast h

/-- **`β_i ≥ b₀N/ℓ`** for bulk labels from the lower count. -/
theorem longCoupling_sum_ge (lam : Fin N → ℝ) (_hmono : Monotone lam) {c' c₁ Lmin E r₀ : ℝ}
    {ℓ : ℕ} (hc' : 0 < c') (hc₁ : 0 < c₁) (hℓ : 1 ≤ ℓ) (hN : 0 < N)
    (hlow : ∀ x y, E - r₀ / 4 ≤ x → y ≤ E + r₀ / 4 → Lmin ≤ y - x →
      c' * N * (y - x) ≤ ((Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card : ℝ))
    (hgap : ∀ i j : Fin N, ℓ ≤ labelDist i j → c₁ * (labelDist i j : ℝ) / N ≤ |lam i - lam j|)
    (hKwin : 3 / c' * ℓ / N ≤ r₀ / 8) (hKlen : Lmin ≤ 3 / c' * ℓ / N)
    (i : Fin N) (hi : |lam i - E| ≤ r₀ / 8) :
    c' ^ 2 / 9 * N / ℓ ≤
      ∑ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist i m), ((N : ℝ) * (lam i - lam m) ^ 2)⁻¹ := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set L : ℝ := 3 / c' * ℓ / N with hL
  have hL0 : 0 < L := by positivity
  have hEi := abs_le.mp hi
  set S := Finset.univ.filter fun k => lam k ∈ Set.Icc (lam i) (lam i + L) with hS
  have hSc : 3 * (ℓ : ℝ) ≤ S.card := by
    have h := hlow (lam i) (lam i + L) (by linarith) (by linarith) (by linarith)
    have : c' * N * (lam i + L - lam i) = 3 * ℓ := by rw [hL]; field_simp; ring
    linarith
  set T := S.filter (fun m => ℓ ≤ labelDist i m) with hT
  have hTc : (ℓ : ℝ) + 1 ≤ T.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S) (fun m => ℓ ≤ labelDist i m)
    have hnear : ((S.filter fun m => ¬ ℓ ≤ labelDist i m).card : ℝ) ≤ 2 * ℓ - 1 := by
      refine le_trans ?_ (card_near_le i hℓ)
      exact_mod_cast Finset.card_le_card (by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk ⊢
        exact hk.2)
    have : (T.card : ℝ) + (S.filter fun m => ¬ ℓ ≤ labelDist i m).card = S.card := by
      exact_mod_cast hsplit
    linarith
  have hTsub : T ⊆ Finset.univ.filter (fun m => ℓ ≤ labelDist i m) := by
    intro m hm
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact hm.2
  have hterm : ∀ m ∈ T, c' ^ 2 / 9 * N / (ℓ : ℝ) ^ 2 ≤ ((N : ℝ) * (lam i - lam m) ^ 2)⁻¹ := by
    intro m hm
    simp only [hT, hS, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc] at hm
    obtain ⟨⟨hm1, hm2⟩, hd⟩ := hm
    have hg := hgap i m hd
    have hd1 : (1 : ℝ) ≤ labelDist i m := by exact_mod_cast le_trans hℓ hd
    have hpos : 0 < |lam i - lam m| := lt_of_lt_of_le (by positivity) hg
    have hsq : (lam i - lam m) ^ 2 ≤ L ^ 2 := by
      rw [← sq_abs]
      have : |lam i - lam m| ≤ L := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hp2 : 0 < (N : ℝ) * (lam i - lam m) ^ 2 := by
      have : 0 < (lam i - lam m) ^ 2 := by rw [← sq_abs]; positivity
      positivity
    calc c' ^ 2 / 9 * N / (ℓ : ℝ) ^ 2 = ((N : ℝ) * L ^ 2)⁻¹ := by
          rw [hL]; field_simp; ring
      _ ≤ ((N : ℝ) * (lam i - lam m) ^ 2)⁻¹ :=
          inv_anti₀ hp2 (mul_le_mul_of_nonneg_left hsq hNr.le)
  have hnn : ∀ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist i m), m ∉ T →
      0 ≤ ((N : ℝ) * (lam i - lam m) ^ 2)⁻¹ := fun _ _ _ => by positivity
  calc c' ^ 2 / 9 * N / ℓ ≤ ((ℓ : ℝ) + 1) * (c' ^ 2 / 9 * N / (ℓ : ℝ) ^ 2) := by
        rw [div_le_iff₀ (by positivity)]
        have : ((ℓ : ℝ) + 1) * (c' ^ 2 / 9 * N / (ℓ : ℝ) ^ 2) * ℓ =
            c' ^ 2 / 9 * N * ((ℓ + 1) / ℓ) := by field_simp
        rw [this]
        have : (1 : ℝ) ≤ (ℓ + 1) / ℓ := by
          rw [le_div_iff₀ (by positivity)]; linarith
        have h0 : 0 ≤ c' ^ 2 / 9 * N := by positivity
        nlinarith
    _ ≤ (T.card : ℝ) * (c' ^ 2 / 9 * N / (ℓ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hTc (by positivity)
    _ = ∑ _m ∈ T, c' ^ 2 / 9 * N / (ℓ : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ T, ((N : ℝ) * (lam i - lam m) ^ 2)⁻¹ := Finset.sum_le_sum hterm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hTsub hnn

end BlockBand.Palm.GoodEvent
