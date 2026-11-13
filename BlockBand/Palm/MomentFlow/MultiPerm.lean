module

public import BlockBand.Palm.MomentFlow.MultiAux

/-!
# `r`-particle finite speed: the matching (permanent) weight and its drift

Fix centres `c : Fin r → ℝ` (in the use, `c_m = λ_{x_m}(s)` for a labelling `x` of `ξ`). For a
labelled tuple `y : Fin r → Fin N` put `pW y = ∏_m φ(λ_{y_m} - c_m)`, and on configurations

`permW ζ = ζ! · Σ_{y labelling ζ} pW y`   (`ζ! = ∏_i ζ_i!`; this is the permanent of
`[φ(λ_{y⁰_n} - c_m)]_{m,n}` for any labelling `y⁰` of `ζ`).

Deterministic, at one time and one eigenvalue vector:

* `occOf_update`, `occOf_comp_swap`, `cfgFact_move`, `sum_labs_move` (moving the particle at
  position `p` from `i` to `j` is a `(ζ_j+1)`-to-one map of labellings), `jump_permW`;
* `momentGenerator_permW`: `𝓑_c W(ζ) = ζ! Σ_y Σ_p Σ_{j ≠ y_p} c_{y_p j}(1 + ζ_j)(pW(y^{p→j}) - pW y)`;
* `pair_fg_le`, `sum_dyson_permD1`, `sum_permD2`: the derivative terms `permD1`, `permD2`.

Cited from the sibling modules `MultiPermDrift` (`quad_eq`) and `MultiPermPoint` (the two drift
bounds):
* `quad_eq` (**the pairwise symmetrization**): for `p ≠ q`, `y_p = i ≠ j = y_q`, the four terms of
  the `ζ_j` part attached to `(p,q)`, `(q,p)` at `y` and at `y∘(p q)` sum to
  `2 c_ij (a_j - a_i)(b_j - b_i) R` with `a = φ(·-c_p)`, `b = φ(·-c_q)`, `R` the other factors;
* `perm_point_drift_le`: with exact short rates, under the hypotheses of `label_drift_le`,
  `𝓢W(ζ) + Σ_i (D_i ∂_iW + ∂²_iW/(2N)) ≤ (r κ₁ + r²A²(K²+1)/(2N)) W(ζ)` for every `ζ`, where
  `∂_iW = ζ! Σ_y permD1 y i`, `∂²_iW = ζ! Σ_y permD2 y i`;
* `perm_drift_le`: the summed form against `v ≥ 0` on the sector.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization

variable {N r : ℕ}

/-!
### Labellings
-/

/-- Labellings of a configuration by `r`-tuples. -/
def labs (r : ℕ) (ζ : Occ N) : Finset (Fin r → Fin N) := univ.filter fun y => occOf y = ζ

theorem mem_labs {ζ : Occ N} {y : Fin r → Fin N} : y ∈ labs r ζ ↔ occOf y = ζ := by
  simp [labs]

theorem occOf_eq_sum (y : Fin r → Fin N) (k : Fin N) :
    occOf y k = ∑ m, if y m = k then 1 else 0 := by
  classical
  simp only [occOf, Finset.card_filter]

theorem occOf_mem_sector (y : Fin r → Fin N) : occOf y ∈ sector N r := by
  classical
  rw [mem_sector]
  have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin r))) (t := univ) (f := y)
    (fun _ _ => Finset.mem_coe.2 (mem_univ _))
  simp only [card_univ, Fintype.card_fin] at this
  exact this.symm

theorem occOf_update {y : Fin r → Fin N} {p : Fin r} {j : Fin N} (h : y p ≠ j) :
    occOf (Function.update y p j) = move (occOf y) (y p) j := by
  classical
  funext k
  have hs : ∀ g : Fin r → ℕ, ∑ m, g m = g p + ∑ m ∈ univ.erase p, g m :=
    fun g => (Finset.add_sum_erase _ _ (mem_univ p)).symm
  have h1 := hs (fun m => if Function.update y p j m = k then 1 else 0)
  have h2 := hs (fun m => if y m = k then 1 else 0)
  have hrest : ∑ m ∈ univ.erase p, (if Function.update y p j m = k then 1 else 0) =
      ∑ m ∈ univ.erase p, (if y m = k then 1 else 0) :=
    Finset.sum_congr rfl fun m hm => by rw [Function.update_of_ne (mem_erase.1 hm).1]
  simp only [Function.update_self] at h1
  rw [occOf_eq_sum, h1, hrest]
  by_cases hk1 : k = y p
  · subst hk1
    rw [move_apply_source _ h, occOf_eq_sum, h2]
    simp [Ne.symm h]
  · by_cases hk2 : k = j
    · subst hk2
      rw [move_apply_target, occOf_eq_sum, h2]
      simp [h]; omega
    · rw [move_apply_of_ne _ hk1 hk2, occOf_eq_sum, h2]
      simp [Ne.symm hk1, Ne.symm hk2]

theorem occOf_comp_swap (y : Fin r → Fin N) (p q : Fin r) :
    occOf (y ∘ Equiv.swap p q) = occOf y := by
  classical
  funext k
  rw [occOf_eq_sum, occOf_eq_sum]
  exact Equiv.sum_comp (Equiv.swap p q) (fun m => if y m = k then 1 else 0)

theorem card_filter_eq_occOf (y : Fin r → Fin N) (i : Fin N) :
    (univ.filter fun p => y p = i).card = occOf y i := rfl

/-!
### Factorials
-/

/-- `ζ! = ∏_i ζ_i!`. -/
def cfgFact (ζ : Occ N) : ℝ := ∏ i, ((ζ i).factorial : ℝ)

theorem cfgFact_pos (ζ : Occ N) : 0 < cfgFact ζ :=
  Finset.prod_pos fun i _ => by positivity

theorem cfgFact_move {ζ : Occ N} {i j : Fin N} (hij : i ≠ j) (hi : 0 < ζ i) :
    (ζ i : ℝ) * cfgFact (move ζ i j) = ((ζ j : ℝ) + 1) * cfgFact ζ := by
  classical
  have hsplit : ∀ g : Occ N, cfgFact g = ((g i).factorial : ℝ) * ((g j).factorial : ℝ) *
      ∏ k ∈ (univ.erase i).erase j, ((g k).factorial : ℝ) := by
    intro g
    unfold cfgFact
    rw [← Finset.mul_prod_erase _ _ (mem_univ i),
      ← Finset.mul_prod_erase _ _ (mem_erase.2 ⟨Ne.symm hij, mem_univ j⟩)]
    ring
  rw [hsplit (move ζ i j), hsplit ζ, move_apply_source _ hij, move_apply_target]
  have hrest : ∏ k ∈ (univ.erase i).erase j, ((move ζ i j k).factorial : ℝ) =
      ∏ k ∈ (univ.erase i).erase j, ((ζ k).factorial : ℝ) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [move_apply_of_ne _ (mem_erase.1 (mem_erase.1 hk).2).1 (mem_erase.1 hk).1]
  rw [hrest]
  obtain ⟨n, hn⟩ : ∃ n, ζ i = n + 1 := ⟨ζ i - 1, by omega⟩
  rw [hn, Nat.add_sub_cancel, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

/-- **Moving one particle**: `Σ_{y ⊢ ζ} Σ_{p : y_p = i} G(y^{p→j}) = (ζ_j + 1) Σ_{y ⊢ ζ^{ij}} G(y)`.
-/
theorem sum_labs_move (G : (Fin r → Fin N) → ℝ) {ζ : Occ N} {i j : Fin N} (hij : i ≠ j)
    (hi : 0 < ζ i) :
    ∑ y ∈ labs r ζ, ∑ p ∈ univ.filter (fun p => y p = i), G (Function.update y p j) =
      ((ζ j : ℝ) + 1) * ∑ y ∈ labs r (move ζ i j), G y := by
  classical
  have hL : ∑ y ∈ labs r ζ, ∑ p ∈ univ.filter (fun p => y p = i), G (Function.update y p j) =
      ∑ z ∈ (labs r ζ ×ˢ (univ : Finset (Fin r))).filter (fun z => z.1 z.2 = i),
        G (Function.update z.1 z.2 j) := by
    rw [Finset.sum_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun y _ => by rw [Finset.sum_filter]
  have hR : ∑ z ∈ (labs r (move ζ i j) ×ˢ (univ : Finset (Fin r))).filter (fun z => z.1 z.2 = j),
      G z.1 = ((ζ j : ℝ) + 1) * ∑ y ∈ labs r (move ζ i j), G y := by
    rw [Finset.sum_filter, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_filter_eq_occOf,
      mem_labs.1 hy, move_apply_target]
    push_cast; ring
  rw [hL, ← hR]
  refine Finset.sum_nbij' (fun z => (Function.update z.1 z.2 j, z.2))
    (fun z => (Function.update z.1 z.2 i, z.2)) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_product, mem_univ, and_true, mem_labs] at hz ⊢
    refine ⟨?_, by simp⟩
    rw [occOf_update (by rw [hz.2]; exact hij), hz.2, hz.1]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_product, mem_univ, and_true, mem_labs] at hz ⊢
    refine ⟨?_, by simp⟩
    rw [occOf_update (by rw [hz.2]; exact Ne.symm hij), hz.2, hz.1, move_move ζ hij hi]
  · rintro ⟨y, p⟩ hz
    simp only [Finset.mem_filter, Finset.mem_product, mem_univ, and_true] at hz
    show (Function.update (Function.update y p j) p i, p) = (y, p)
    rw [Function.update_idem, ← hz.2, Function.update_eq_self]
  · rintro ⟨y, p⟩ hz
    simp only [Finset.mem_filter, Finset.mem_product, mem_univ, and_true] at hz
    show (Function.update (Function.update y p i) p j, p) = (y, p)
    rw [Function.update_idem, ← hz.2, Function.update_eq_self]
  · intro z _; rfl

/-!
### The weight
-/

/-- `∏_m φ(λ_{y_m} - c_m)` for a labelled tuple. -/
def pW (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N) : ℝ :=
  ∏ m, φ (lam (y m) - c m)

/-- The matching weight `ζ! Σ_{y ⊢ ζ} ∏_m φ(λ_{y_m} - c_m)`. -/
def permW (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (ζ : Occ N) : ℝ :=
  cfgFact ζ * ∑ y ∈ labs r ζ, pW φ lam c y

/-- The product without the factor `m`. -/
def pWx (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N) (m : Fin r) : ℝ :=
  ∏ m' ∈ univ.erase m, φ (lam (y m') - c m')

/-- The product without the factors `m, m'`. -/
def pWxx (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N) (m m' : Fin r) : ℝ :=
  ∏ m'' ∈ (univ.erase m).erase m', φ (lam (y m'') - c m'')

theorem pW_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (lam : Fin N → ℝ) (c : Fin r → ℝ)
    (y : Fin r → Fin N) : 0 ≤ pW φ lam c y :=
  Finset.prod_nonneg fun _ _ => hφ0 _

theorem pWx_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (lam : Fin N → ℝ) (c : Fin r → ℝ)
    (y : Fin r → Fin N) (m : Fin r) : 0 ≤ pWx φ lam c y m :=
  Finset.prod_nonneg fun _ _ => hφ0 _

theorem pWxx_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (lam : Fin N → ℝ) (c : Fin r → ℝ)
    (y : Fin r → Fin N) (m m' : Fin r) : 0 ≤ pWxx φ lam c y m m' :=
  Finset.prod_nonneg fun _ _ => hφ0 _

theorem pW_eq_mul (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N)
    (p : Fin r) : pW φ lam c y = φ (lam (y p) - c p) * pWx φ lam c y p :=
  (Finset.mul_prod_erase _ _ (mem_univ p)).symm

theorem pWx_eq_mul (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N)
    {p q : Fin r} (hpq : p ≠ q) :
    pWx φ lam c y p = φ (lam (y q) - c q) * pWxx φ lam c y p q :=
  (Finset.mul_prod_erase _ _ (mem_erase.2 ⟨Ne.symm hpq, mem_univ q⟩)).symm

theorem pW_eq_mul_mul (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N)
    {p q : Fin r} (hpq : p ≠ q) :
    pW φ lam c y = φ (lam (y p) - c p) * φ (lam (y q) - c q) * pWxx φ lam c y p q := by
  rw [pW_eq_mul _ _ _ _ p, pWx_eq_mul _ _ _ _ hpq]; ring

theorem pWx_congr (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) {y z : Fin r → Fin N}
    {p : Fin r} (h : ∀ m, m ≠ p → z m = y m) : pWx φ lam c z p = pWx φ lam c y p :=
  Finset.prod_congr rfl fun m hm => by rw [h m (mem_erase.1 hm).1]

theorem pWxx_congr (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) {y z : Fin r → Fin N}
    {p q : Fin r} (h : ∀ m, m ≠ p → m ≠ q → z m = y m) :
    pWxx φ lam c z p q = pWxx φ lam c y p q :=
  Finset.prod_congr rfl fun m hm =>
    by rw [h m (mem_erase.1 (mem_erase.1 hm).2).1 (mem_erase.1 hm).1]

theorem pW_update (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N)
    (p : Fin r) (j : Fin N) :
    pW φ lam c (Function.update y p j) = φ (lam j - c p) * pWx φ lam c y p := by
  rw [pW_eq_mul _ _ _ _ p, Function.update_self]
  congr 1
  exact pWx_congr φ lam c fun m hm => Function.update_of_ne hm _ _

/-!
### Jumps of the weight and the generator
-/

theorem jump_permW (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) {ζ : Occ N} {i j : Fin N}
    (hij : i ≠ j) (hi : 0 < ζ i) :
    (ζ i : ℝ) * (permW φ lam c (move ζ i j) - permW φ lam c ζ) =
      cfgFact ζ * ∑ y ∈ labs r ζ, ∑ p ∈ univ.filter (fun p => y p = i),
        (pW φ lam c (Function.update y p j) - pW φ lam c y) := by
  classical
  have h1 := sum_labs_move (r := r) (pW φ lam c) hij hi
  have h2 : ∑ y ∈ labs r ζ, ∑ p ∈ univ.filter (fun p => y p = i), pW φ lam c y =
      (ζ i : ℝ) * ∑ y ∈ labs r ζ, pW φ lam c y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_filter_eq_occOf, mem_labs.1 hy]
  simp only [Finset.sum_sub_distrib, mul_sub, permW]
  rw [h1, h2, ← mul_assoc, cfgFact_move hij hi]
  ring

theorem momentGenerator_permW (cr : Fin N → Fin N → ℝ) (φ : ℝ → ℝ) (lam : Fin N → ℝ)
    (c : Fin r → ℝ) (ζ : Occ N) :
    momentGenerator cr (permW φ lam c) ζ = cfgFact ζ * ∑ y ∈ labs r ζ, ∑ p,
      ∑ j ∈ univ.erase (y p), cr (y p) j * (1 + (occOf y j : ℝ)) *
        (pW φ lam c (Function.update y p j) - pW φ lam c y) := by
  classical
  set F : (Fin r → Fin N) → Fin N → Fin N → Fin r → ℝ := fun y i j p =>
    cr i j * (1 + (occOf y j : ℝ)) * (pW φ lam c (Function.update y p j) - pW φ lam c y) with hF
  -- regroup the right side by the source label `i = y p`
  have hR : ∀ y : Fin r → Fin N, ∑ p, ∑ j ∈ univ.erase (y p), F y (y p) j p =
      ∑ i, ∑ j ∈ univ.erase i, ∑ p ∈ univ.filter (fun p => y p = i), F y i j p := by
    intro y
    rw [← Finset.sum_fiberwise univ y (fun p => ∑ j ∈ univ.erase (y p), F y (y p) j p)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpi : y p = i := (Finset.mem_filter.1 hp).2
    subst hpi; rfl
  have hswap : ∑ y ∈ labs r ζ, ∑ i, ∑ j ∈ univ.erase i,
      ∑ p ∈ univ.filter (fun p => y p = i), F y i j p =
      ∑ i, ∑ j ∈ univ.erase i, ∑ y ∈ labs r ζ, ∑ p ∈ univ.filter (fun p => y p = i),
        F y i j p := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  show _ = cfgFact ζ * ∑ y ∈ labs r ζ, ∑ p, ∑ j ∈ univ.erase (y p), F y (y p) j p
  simp only [hR]
  rw [hswap, Finset.mul_sum]
  unfold momentGenerator
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := Ne.symm (mem_erase.1 hj).1
  rcases Nat.eq_zero_or_pos (ζ i) with hi | hi
  · rw [jumpCoeff_eq_zero_of_eq_zero ζ j hi, mul_zero, zero_mul]
    refine (mul_eq_zero_of_right _ ?_).symm
    refine Finset.sum_eq_zero fun y hy => Finset.sum_eq_zero fun p hp => ?_
    exfalso
    have : 0 < occOf y i := by
      rw [← card_filter_eq_occOf]; exact Finset.card_pos.2 ⟨p, hp⟩
    rw [mem_labs.1 hy] at this; omega
  · have hJ := jump_permW (r := r) φ lam c hij hi
    have hocc : ∀ y ∈ labs r ζ, (occOf y j : ℝ) = ζ j := fun y hy => by rw [mem_labs.1 hy]
    calc cr i j * jumpCoeff ζ i j * (permW φ lam c (move ζ i j) - permW φ lam c ζ)
        = cr i j * (1 + (ζ j : ℝ)) * ((ζ i : ℝ) *
            (permW φ lam c (move ζ i j) - permW φ lam c ζ)) := by unfold jumpCoeff; ring
      _ = _ := by
          rw [hJ]
          simp only [Finset.mul_sum, hF]
          refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun p _ => ?_
          rw [hocc y hy]; ring

/-!
### The derivative fields
-/

/-- `∂_{λ_i} pW`. -/
def permD1 (φ φ1 : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N) (i : Fin N) :
    ℝ :=
  ∑ m, if y m = i then φ1 (lam i - c m) * pWx φ lam c y m else 0

/-- `∂²_{λ_i} pW`. -/
def permD2 (φ φ1 φ2 : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N)
    (i : Fin N) : ℝ :=
  ∑ m, if y m = i then φ2 (lam i - c m) * pWx φ lam c y m + φ1 (lam i - c m) *
    ∑ m' ∈ univ.erase m, (if y m' = i then φ1 (lam i - c m') * pWxx φ lam c y m m' else 0)
    else 0

theorem sum_dyson_permD1 (φ φ1 : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N)
    (D : Fin N → ℝ) :
    ∑ i, D i * permD1 φ φ1 lam c y i =
      ∑ m, D (y m) * φ1 (lam (y m) - c m) * pWx φ lam c y m := by
  classical
  simp only [permD1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, ite_true]; ring

theorem sum_permD2 (φ φ1 φ2 : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N) :
    ∑ i, permD2 φ φ1 φ2 lam c y i =
      ∑ m, (φ2 (lam (y m) - c m) * pWx φ lam c y m + φ1 (lam (y m) - c m) *
        ∑ m' ∈ univ.erase m, (if y m' = y m then
          φ1 (lam (y m) - c m') * pWxx φ lam c y m m' else 0)) := by
  classical
  simp only [permD2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-!
### The pair bound
-/

/-- **Second-order pair bound for two weights**:
`c_ij (f(λ_j) - f(λ_i))(g(λ_j) - g(λ_i)) ≤ A²K² f(λ_i) g(λ_j) / N`. -/
theorem pair_fg_le (lam : Fin N → ℝ) (ℓ : ℕ) {f f1 g g1 : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f1 z) z) (hg : ∀ z, HasDerivAt g (g1 z) z) {A K G : ℝ}
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hAf : ∀ z, |f1 z| ≤ A * f z) (hAg : ∀ z, |g1 z| ≤ A * g z)
    (hcf : ∀ x z, |z - x| ≤ G → f z ≤ K * f x) (hcg : ∀ x z, |z - x| ≤ G → g z ≤ K * g x)
    {i j : Fin N}
    (hshort : labelDist i j < ℓ → i ≠ j → |lam j - lam i| ≤ G ∨ f (lam j) = f (lam i)) :
    cfgRate N lam ℓ 0 i j * ((f (lam j) - f (lam i)) * (g (lam j) - g (lam i))) ≤
      A ^ 2 * K ^ 2 * (f (lam i) * g (lam j)) / N := by
  have hR : 0 ≤ A ^ 2 * K ^ 2 * (f (lam i) * g (lam j)) / N := by
    have := hf0 (lam i); have := hg0 (lam j); positivity
  by_cases hs : i ≠ j ∧ labelDist i j < ℓ
  · rw [cfgRate_zero_apply lam ℓ hs.1 hs.2]
    rcases hshort hs.2 hs.1 with hc | hfl
    · by_cases hij : lam i = lam j
      · have h0 : f (lam j) - f (lam i) = 0 := by rw [hij, sub_self]
        rw [h0, zero_mul, mul_zero]; exact hR
      obtain ⟨z₁, hz1, -, hz⟩ := exists_mvt_between hf (lam i) (lam j)
      obtain ⟨z₂, -, hz2, hz'⟩ := exists_mvt_between hg (lam i) (lam j)
      rw [hz, hz']
      have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have h1 : |f1 z₁| ≤ A * K * f (lam i) := by
        have := hcf (lam i) z₁ (hz1.trans hc)
        calc |f1 z₁| ≤ A * f z₁ := hAf z₁
          _ ≤ A * (K * f (lam i)) := mul_le_mul_of_nonneg_left this hA0
          _ = A * K * f (lam i) := by ring
      have h2 : |g1 z₂| ≤ A * K * g (lam j) := by
        have := hcg (lam j) z₂ (hz2.trans hc)
        calc |g1 z₂| ≤ A * g z₂ := hAg z₂
          _ ≤ A * (K * g (lam j)) := mul_le_mul_of_nonneg_left this hA0
          _ = A * K * g (lam j) := by ring
      have hprod : f1 z₁ * g1 z₂ ≤ A ^ 2 * K ^ 2 * (f (lam i) * g (lam j)) := by
        have := mul_le_mul h1 h2 (abs_nonneg _) (by have := hf0 (lam i); positivity)
        rw [← abs_mul] at this
        calc f1 z₁ * g1 z₂ ≤ |f1 z₁ * g1 z₂| := le_abs_self _
          _ ≤ A * K * f (lam i) * (A * K * g (lam j)) := this
          _ = _ := by ring
      have heq : pairRate N lam i j * (f1 z₁ * (lam j - lam i) * (g1 z₂ * (lam j - lam i))) =
          f1 z₁ * g1 z₂ / N := by
        unfold pairRate
        rcases eq_or_ne (N : ℝ) 0 with hN | hN
        · rw [hN]; simp
        · have hd : (lam i - lam j) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hij)
          have : (lam j - lam i) * (lam j - lam i) = (lam i - lam j) ^ 2 := by ring
          calc ((N : ℝ) * (lam i - lam j) ^ 2)⁻¹ *
                (f1 z₁ * (lam j - lam i) * (g1 z₂ * (lam j - lam i)))
              = ((N : ℝ) * (lam i - lam j) ^ 2)⁻¹ * (f1 z₁ * g1 z₂) *
                  ((lam j - lam i) * (lam j - lam i)) := by ring
            _ = _ := by rw [this]; field_simp
      rw [heq]
      exact div_le_div_of_nonneg_right hprod hNr
    · rw [hfl, sub_self, zero_mul, mul_zero]; exact hR
  · have : cfgRate N lam ℓ 0 i j = 0 := by unfold cfgRate; rw [ite_eq_right hs]
    rw [this, zero_mul]; exact hR

end BlockBand.Palm.MomentFlow
