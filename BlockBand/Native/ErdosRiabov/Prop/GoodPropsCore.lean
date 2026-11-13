module

public import BlockBand.Native.ErdosRiabov.Psi.Defs

/-!
# Generic machinery for the propagator estimates on size functions, part 1

* `tensorR F`: the real tensor kernel `(⊗_j F_j)_{xy} = Π_j (F_j)_{x_j y_j}` on
  `Fin k → Fin N`; `tensorRSet F T` keeps the factors in `T` and puts `1` elsewhere;
  `tensorRSet_insert` (`= O_j * G_T = G_T * O_j`), `mulVec_tensorRSet_single`
  (`O_j *ᵥ g = slotOp j …`).
* `slotOp j K g x = Σ_c K(x,c) g(x[j ↦ c])`, a one-coordinate operator whose kernel may depend
  on the other coordinates (used for the regularized kernels `Θ̊^{(j)}`); monotonicity and
  `slotOp_comm` (commutation for different coordinates).
* `linkProd V a b x = Π_{i<k} V_i(p_i, p_{i+1})`, `p = Psi.isoPoint a b x`, the product of the
  links of the isotropic size function with a height per link (`sIso_eq_linkProd`,
  `sAv_eq_linkProd`: `s^av_{n+2}(x) = (ℓη)^{-(n+2)/2} √(linkProd Υ (x_last) (x_last) x)`).
* the one-step lemmas `slotOp_sqrt_linkProd_le` (interior coordinate `j`, `j + 1 < k`: links `j`,
  `j+1` change) and `slotOp_sqrt_linkProd_last_le` (last coordinate with both endpoints equal to
  it, the averaged case: links `0` and `k-1` change).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Propagator

open Matrix
open scoped BigOperators

variable {N k : ℕ}

/-!
## Real tensor kernels
-/

/-- `(⊗_j F_j)_{xy} = Π_j (F_j)_{x_j y_j}`. -/
def tensorR (F : Fin k → Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin k → Fin N) (Fin k → Fin N) ℝ :=
  fun x y => ∏ j, F j (x j) (y j)

/-- The partial tensor with the factors of `T` and `1` elsewhere. -/
def tensorRSet (F : Fin k → Matrix (Fin N) (Fin N) ℝ) (T : Finset (Fin k)) :
    Matrix (Fin k → Fin N) (Fin k → Fin N) ℝ :=
  tensorR (fun j => if j ∈ T then F j else 1)

/-- One-coordinate operator `slotOp j K g x = Σ_c K(x,c) g(x[j ↦ c])`. -/
def slotOp (j : Fin k) (K : (Fin k → Fin N) → Fin N → ℝ) (g : (Fin k → Fin N) → ℝ) :
    (Fin k → Fin N) → ℝ :=
  fun x => ∑ c, K x c * g (Function.update x j c)

theorem tensorR_mul (F B : Fin k → Matrix (Fin N) (Fin N) ℝ) :
    tensorR (fun j => F j * B j) = tensorR F * tensorR B := by
  ext x y
  simp only [tensorR, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun z _ => Finset.prod_mul_distrib

theorem tensorR_one : tensorR (fun _ => (1 : Matrix (Fin N) (Fin N) ℝ)) =
    (1 : Matrix (Fin k → Fin N) (Fin k → Fin N) ℝ) := by
  ext x y
  simp only [tensorR, Matrix.one_apply]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

theorem tensorRSet_univ (F : Fin k → Matrix (Fin N) (Fin N) ℝ) :
    tensorRSet F Finset.univ = tensorR F := by
  simp [tensorRSet]

theorem tensorRSet_empty (F : Fin k → Matrix (Fin N) (Fin N) ℝ) :
    tensorRSet F ∅ = 1 := by
  simp only [tensorRSet, Finset.notMem_empty, ite_false]
  exact tensorR_one

/-- Adding a slot: `G_{T ∪ {j}} = O_j G_T = G_T O_j` (`j ∉ T`). -/
theorem tensorRSet_insert (F : Fin k → Matrix (Fin N) (Fin N) ℝ) {T : Finset (Fin k)}
    {j : Fin k} (hj : j ∉ T) :
    tensorRSet F (insert j T) = tensorRSet F {j} * tensorRSet F T ∧
    tensorRSet F (insert j T) = tensorRSet F T * tensorRSet F {j} := by
  constructor
  · rw [tensorRSet, tensorRSet, tensorRSet, ← tensorR_mul]
    congr 1
    funext i
    by_cases h : i = j
    · subst h
      simp [hj]
    · simp [h]
  · rw [tensorRSet, tensorRSet, tensorRSet, ← tensorR_mul]
    congr 1
    funext i
    by_cases h : i = j
    · subst h
      simp [hj]
    · simp [h]

private theorem tensorR_single_apply (F : Fin k → Matrix (Fin N) (Fin N) ℝ) (j : Fin k)
    (x y : Fin k → Fin N) :
    tensorRSet F {j} x y = if y = Function.update x j (y j) then F j (x j) (y j) else 0 := by
  simp only [tensorRSet, tensorR, Finset.mem_singleton]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j), ite_eq_left rfl]
  split_ifs with h
  · have hrest : ∏ i ∈ Finset.univ \ {j},
        (if i = j then F i else 1) (x i) (y i) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      have hij : i ≠ j := by simpa using hi
      have : y i = x i := by rw [h, Function.update_of_ne hij]
      rw [ite_eq_right hij, this, Matrix.one_apply_eq]
    rw [hrest, mul_one]
  · have : ∃ i, i ≠ j ∧ y i ≠ x i := by
      by_contra hc
      push Not at hc
      exact h (Function.eq_update_iff.mpr ⟨rfl, hc⟩)
    obtain ⟨i, hij, hi⟩ := this
    have hmem : i ∈ Finset.univ \ {j} := by simpa using hij
    have hz : (if i = j then F i else 1) (x i) (y i) = 0 := by
      rw [ite_eq_right hij]
      exact Matrix.one_apply_ne (fun e => hi e.symm)
    rw [Finset.prod_eq_zero hmem hz, mul_zero]

/-- `O_j *ᵥ g = slotOp j (F_j(x_j, ·)) g`. -/
theorem mulVec_tensorRSet_single (F : Fin k → Matrix (Fin N) (Fin N) ℝ) (j : Fin k)
    (g : (Fin k → Fin N) → ℝ) :
    tensorRSet F {j} *ᵥ g = slotOp j (fun x c => F j (x j) c) g := by
  ext x
  simp only [Matrix.mulVec, dotProduct, tensorR_single_apply, ite_mul, zero_mul, slotOp]
  have hinj : Set.InjOn (fun c : Fin N => Function.update x j c) (Finset.univ : Finset (Fin N)) :=
    fun c _ c' _ hcc => by simpa using congrFun hcc j
  rw [← Finset.sum_filter]
  have hfil : (Finset.univ.filter fun y : Fin k → Fin N => y = Function.update x j (y j)) =
      Finset.univ.image (fun c : Fin N => Function.update x j c) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      exact ⟨y j, hy.symm⟩
    · rintro ⟨c, rfl⟩
      simp
  rw [hfil, Finset.sum_image hinj]
  simp

theorem tensorR_nonneg {F : Fin k → Matrix (Fin N) (Fin N) ℝ}
    (hF : ∀ j u v, 0 ≤ F j u v) (x y : Fin k → Fin N) : 0 ≤ tensorR F x y :=
  Finset.prod_nonneg fun j _ => hF j _ _

theorem tensorRSet_nonneg {F : Fin k → Matrix (Fin N) (Fin N) ℝ}
    (hF : ∀ j u v, 0 ≤ F j u v) (T : Finset (Fin k)) (x y : Fin k → Fin N) :
    0 ≤ tensorRSet F T x y := by
  refine tensorR_nonneg (fun j u v => ?_) x y
  by_cases h : j ∈ T
  · rw [ite_eq_left h]
    exact hF j u v
  · rw [ite_eq_right h, Matrix.one_apply]
    split_ifs <;> norm_num

theorem mulVec_mono_of_nonneg {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : ∀ x y, 0 ≤ M x y) {g g' : ι → ℝ} (h : ∀ y, g y ≤ g' y) (x : ι) :
    (M *ᵥ g) x ≤ (M *ᵥ g') x :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (hM x y)

/-!
## One-coordinate operators
-/

theorem slotOp_mono (j : Fin k) {K : (Fin k → Fin N) → Fin N → ℝ} (hK : ∀ x c, 0 ≤ K x c)
    {g g' : (Fin k → Fin N) → ℝ} (h : ∀ y, g y ≤ g' y) (x : Fin k → Fin N) :
    slotOp j K g x ≤ slotOp j K g' x :=
  Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h _) (hK x c)

theorem slotOp_nonneg (j : Fin k) {K : (Fin k → Fin N) → Fin N → ℝ} (hK : ∀ x c, 0 ≤ K x c)
    {g : (Fin k → Fin N) → ℝ} (h : ∀ y, 0 ≤ g y) (x : Fin k → Fin N) : 0 ≤ slotOp j K g x :=
  Finset.sum_nonneg fun c _ => mul_nonneg (hK x c) (h _)

/-- Commutation of one-coordinate operators on different coordinates, when neither kernel
depends on the other coordinate. -/
theorem slotOp_comm {j j' : Fin k} (hjj : j ≠ j') {K K' : (Fin k → Fin N) → Fin N → ℝ}
    (hK : ∀ x c c', K (Function.update x j' c') c = K x c)
    (hK' : ∀ x c c', K' (Function.update x j c) c' = K' x c')
    (g : (Fin k → Fin N) → ℝ) :
    slotOp j K (slotOp j' K' g) = slotOp j' K' (slotOp j K g) := by
  ext x
  simp only [slotOp, hK, hK', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Function.update_comm hjj]
  ring

/-!
## Links of the isotropic size function
-/

/-- `Π_{i<k} V_i(p_i, p_{i+1})`, `p = Psi.isoPoint a b x`. -/
def linkProd (V : ℕ → Fin N → Fin N → ℝ) (a b : Fin N) (x : Fin k → Fin N) : ℝ :=
  ∏ i ∈ Finset.range k, V i (Psi.isoPoint a b x i) (Psi.isoPoint a b x (i + 1))

theorem linkProd_nonneg {V : ℕ → Fin N → Fin N → ℝ} (hV : ∀ i u w, 0 ≤ V i u w) (a b : Fin N)
    (x : Fin k → Fin N) : 0 ≤ linkProd V a b x :=
  Finset.prod_nonneg fun i _ => hV i _ _

theorem isoPoint_succ (a b : Fin N) (x : Fin k → Fin N) (j : Fin k) (hj : j.val + 1 < k) :
    Psi.isoPoint a b x (j.val + 1) = x j := by
  simp only [Psi.isoPoint, Nat.add_one_ne_zero, ite_false, dite_eq_left hj]
  congr

/-- Updating an interior coordinate `j` (`j + 1 < k`) changes only `p_{j+1}`. -/
theorem isoPoint_update_of_lt (a b : Fin N) (x : Fin k → Fin N) (j : Fin k)
    (hj : j.val + 1 < k) (c : Fin N) (i : ℕ) :
    Psi.isoPoint a b (Function.update x j c) i =
      if i = j.val + 1 then c else Psi.isoPoint a b x i := by
  unfold Psi.isoPoint
  by_cases h0 : i = 0
  · subst h0
    simp
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases hi : i < k
    · rw [dite_eq_left hi, dite_eq_left hi, Function.update_apply]
      by_cases he : i = j.val + 1
      · subst he
        simp
      · rw [ite_eq_right he, ite_eq_right]
        intro e
        apply he
        have := congrArg Fin.val e
        simp at this
        omega
    · rw [dite_eq_right hi, dite_eq_right hi, ite_eq_right (by omega)]

/-- Updating the last coordinate (`j + 1 = k`) does not change any `p_i`. -/
theorem isoPoint_update_of_last (a b : Fin N) (x : Fin k → Fin N) (j : Fin k)
    (hj : j.val + 1 = k) (c : Fin N) (i : ℕ) :
    Psi.isoPoint a b (Function.update x j c) i = Psi.isoPoint a b x i := by
  unfold Psi.isoPoint
  by_cases h0 : i = 0
  · simp [h0]
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases hi : i < k
    · rw [dite_eq_left hi, dite_eq_left hi, Function.update_of_ne]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    · rw [dite_eq_right hi, dite_eq_right hi]

private theorem linkProd_split (V : ℕ → Fin N → Fin N → ℝ) (a b : Fin N) (x : Fin k → Fin N)
    (j : ℕ) (hj : j + 1 < k) :
    linkProd V a b x =
      V j (Psi.isoPoint a b x j) (Psi.isoPoint a b x (j + 1)) *
        (V (j + 1) (Psi.isoPoint a b x (j + 1)) (Psi.isoPoint a b x (j + 2)) *
          ∏ i ∈ ((Finset.range k).erase j).erase (j + 1),
            V i (Psi.isoPoint a b x i) (Psi.isoPoint a b x (i + 1))) := by
  unfold linkProd
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr (by omega : j < k)),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hj⟩)]

/-- **Interior one-step lemma.** For `j + 1 < k`, link families `V, V'` that agree off the links
`j, j+1`, nonnegative `V` and a kernel `K ≥ 0`: if, at `x`,
`Σ_c K(x,c) √(V_j(p_j,c) V_{j+1}(c,p_{j+2})) ≤ κ √(V'_j(p_j,x_j) V'_{j+1}(x_j,p_{j+2}))`, then
`slotOp j K (√ linkProd V a b) x ≤ κ √(linkProd V' a b x)`. -/
theorem slotOp_sqrt_linkProd_le (j : Fin k) (hj : j.val + 1 < k)
    {K : (Fin k → Fin N) → Fin N → ℝ} {V V' : ℕ → Fin N → Fin N → ℝ}
    (hVV : ∀ i, i ≠ j.val → i ≠ j.val + 1 → V i = V' i) (hV : ∀ i u w, 0 ≤ V i u w)
    (a b : Fin N) (x : Fin k → Fin N) {κ : ℝ}
    (hstep : ∑ c, K x c * Real.sqrt (V j.val (Psi.isoPoint a b x j.val) c *
        V (j.val + 1) c (Psi.isoPoint a b x (j.val + 2))) ≤
      κ * Real.sqrt (V' j.val (Psi.isoPoint a b x j.val) (x j) *
        V' (j.val + 1) (x j) (Psi.isoPoint a b x (j.val + 2)))) :
    slotOp j K (fun y => Real.sqrt (linkProd V a b y)) x ≤
      κ * Real.sqrt (linkProd V' a b x) := by
  set R := ∏ i ∈ ((Finset.range k).erase j.val).erase (j.val + 1),
    V i (Psi.isoPoint a b x i) (Psi.isoPoint a b x (i + 1)) with hR
  have hR0 : 0 ≤ R := Finset.prod_nonneg fun i _ => hV i _ _
  have hupd : ∀ c, linkProd V a b (Function.update x j c) =
      V j.val (Psi.isoPoint a b x j.val) c *
        V (j.val + 1) c (Psi.isoPoint a b x (j.val + 2)) * R := by
    intro c
    rw [linkProd_split V a b _ j.val hj, isoPoint_update_of_lt a b x j hj c j.val,
      isoPoint_update_of_lt a b x j hj c (j.val + 1),
      isoPoint_update_of_lt a b x j hj c (j.val + 2), ite_eq_right (by omega), ite_eq_left rfl,
      ite_eq_right (by omega), hR, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun i hi => ?_
    have h1 : i ≠ j.val + 1 := (Finset.mem_erase.mp hi).1
    have h2 : i ≠ j.val := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    rw [isoPoint_update_of_lt a b x j hj c i, isoPoint_update_of_lt a b x j hj c (i + 1),
      ite_eq_right h1, ite_eq_right (by omega)]
  have hx : linkProd V' a b x = V' j.val (Psi.isoPoint a b x j.val) (x j) *
      V' (j.val + 1) (x j) (Psi.isoPoint a b x (j.val + 2)) * R := by
    rw [linkProd_split V' a b x j.val hj, isoPoint_succ a b x j hj, hR, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun i hi => ?_
    have h1 : i ≠ j.val + 1 := (Finset.mem_erase.mp hi).1
    have h2 : i ≠ j.val := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    rw [hVV i h2 h1]
  unfold slotOp
  simp_rw [hupd]
  calc ∑ c, K x c * Real.sqrt (V j.val (Psi.isoPoint a b x j.val) c *
          V (j.val + 1) c (Psi.isoPoint a b x (j.val + 2)) * R)
      = (∑ c, K x c * Real.sqrt (V j.val (Psi.isoPoint a b x j.val) c *
          V (j.val + 1) c (Psi.isoPoint a b x (j.val + 2)))) * Real.sqrt R := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Real.sqrt_mul (mul_nonneg (hV _ _ _) (hV _ _ _))]
        ring
    _ ≤ κ * Real.sqrt (V' j.val (Psi.isoPoint a b x j.val) (x j) *
          V' (j.val + 1) (x j) (Psi.isoPoint a b x (j.val + 2))) * Real.sqrt R :=
        mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg _)
    _ = κ * Real.sqrt (linkProd V' a b x) := by
        rw [hx, Real.sqrt_mul' _ hR0]
        ring

/-- **Last-coordinate one-step lemma (averaged form).** For `k = n + 2`, the function
`y ↦ √(linkProd V y_last y_last y)`, link families agreeing off the links `0, n+1`, and a kernel
`K ≥ 0`: if `Σ_c K(x,c) √(V_{n+1}(x_n,c) V_0(c,x_0)) ≤ κ √(V'_{n+1}(x_n,x_last) V'_0(x_last,x_0))`
then `slotOp last K (…) x ≤ κ √(linkProd V' x_last x_last x)`. -/
theorem slotOp_sqrt_linkProd_last_le {n : ℕ} {K : (Fin (n + 2) → Fin N) → Fin N → ℝ}
    {V V' : ℕ → Fin N → Fin N → ℝ} (hVV : ∀ i, i ≠ 0 → i ≠ n + 1 → V i = V' i)
    (hV : ∀ i u w, 0 ≤ V i u w) (x : Fin (n + 2) → Fin N) {κ : ℝ}
    (hstep : ∑ c, K x c * Real.sqrt (V (n + 1) (x ⟨n, by omega⟩) c * V 0 c (x 0)) ≤
      κ * Real.sqrt (V' (n + 1) (x ⟨n, by omega⟩) (x (Fin.last (n + 1))) *
        V' 0 (x (Fin.last (n + 1))) (x 0))) :
    slotOp (Fin.last (n + 1)) K
        (fun y => Real.sqrt (linkProd V (y (Fin.last (n + 1))) (y (Fin.last (n + 1))) y)) x ≤
      κ * Real.sqrt (linkProd V' (x (Fin.last (n + 1))) (x (Fin.last (n + 1))) x) := by
  set q := Psi.isoPoint (x 0) (x 0) x with hq
  have hpt : ∀ (e : Fin N) (i : ℕ), 1 ≤ i → i < n + 2 → Psi.isoPoint e e x i = q i := by
    intro e i h1 h2
    rw [hq]
    simp only [Psi.isoPoint, ite_eq_right (by omega : i ≠ 0), dite_eq_left h2]
  have hq1 : q 1 = x 0 := by
    rw [hq]
    simp [Psi.isoPoint]
  have hqn : q (n + 1) = x ⟨n, by omega⟩ := by
    rw [hq]
    simp only [Psi.isoPoint, ite_eq_right (by omega : n + 1 ≠ 0),
      dite_eq_left (by omega : n + 1 < n + 2)]
    rfl
  have hsplit : ∀ (V : ℕ → Fin N → Fin N → ℝ) (e : Fin N), linkProd V e e x =
      V 0 e (x 0) * (V (n + 1) (x ⟨n, by omega⟩) e *
        ∏ i ∈ ((Finset.range (n + 2)).erase 0).erase (n + 1), V i (q i) (q (i + 1))) := by
    intro V e
    unfold linkProd
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr (by omega : 0 < n + 2)),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨by omega,
        Finset.mem_range.mpr (by omega : n + 1 < n + 2)⟩)]
    have h0 : Psi.isoPoint e e x 0 = e := by simp [Psi.isoPoint]
    have hn2 : Psi.isoPoint e e x (n + 1 + 1) = e := by simp [Psi.isoPoint]
    rw [h0, zero_add, hpt e 1 le_rfl (by omega), hq1, hpt e (n + 1) (by omega) (by omega), hqn,
      hn2]
    congr 2
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi1 : i ≠ n + 1 := (Finset.mem_erase.mp hi).1
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hik : i < n + 2 := Finset.mem_range.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
    rw [hpt e i (by omega) hik, hpt e (i + 1) (by omega) (by omega)]
  have hupd : ∀ c, Function.update x (Fin.last (n + 1)) c (Fin.last (n + 1)) = c := fun c => by
    simp
  have hlink : ∀ (V : ℕ → Fin N → Fin N → ℝ) (c : Fin N),
      linkProd V c c (Function.update x (Fin.last (n + 1)) c) = linkProd V c c x := by
    intro V c
    unfold linkProd
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [isoPoint_update_of_last c c x (Fin.last (n + 1)) (by simp) c i,
      isoPoint_update_of_last c c x (Fin.last (n + 1)) (by simp) c (i + 1)]
  set R := ∏ i ∈ ((Finset.range (n + 2)).erase 0).erase (n + 1), V i (q i) (q (i + 1)) with hR
  have hR0 : 0 ≤ R := Finset.prod_nonneg fun i _ => hV i _ _
  have hR' : ∏ i ∈ ((Finset.range (n + 2)).erase 0).erase (n + 1), V' i (q i) (q (i + 1)) = R := by
    rw [hR]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi1 : i ≠ n + 1 := (Finset.mem_erase.mp hi).1
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    rw [hVV i hi0 hi1]
  unfold slotOp
  simp_rw [hupd, hlink, hsplit V]
  calc ∑ c, K x c * Real.sqrt (V 0 c (x 0) * (V (n + 1) (x ⟨n, by omega⟩) c * R))
      = (∑ c, K x c * Real.sqrt (V (n + 1) (x ⟨n, by omega⟩) c * V 0 c (x 0))) *
          Real.sqrt R := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [show V 0 c (x 0) * (V (n + 1) (x ⟨n, by omega⟩) c * R) =
          V (n + 1) (x ⟨n, by omega⟩) c * V 0 c (x 0) * R by ring,
          Real.sqrt_mul (mul_nonneg (hV _ _ _) (hV _ _ _))]
        ring
    _ ≤ κ * Real.sqrt (V' (n + 1) (x ⟨n, by omega⟩) (x (Fin.last (n + 1))) *
          V' 0 (x (Fin.last (n + 1))) (x 0)) * Real.sqrt R :=
        mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg _)
    _ = _ := by
        rw [hsplit V', hR', show V' 0 (x (Fin.last (n + 1))) (x 0) *
          (V' (n + 1) (x ⟨n, by omega⟩) (x (Fin.last (n + 1))) * R) =
          V' (n + 1) (x ⟨n, by omega⟩) (x (Fin.last (n + 1))) *
            V' 0 (x (Fin.last (n + 1))) (x 0) * R by ring, Real.sqrt_mul' _ hR0]
        ring

/-!
## Iteration over the interior coordinates
-/

/-- The first `m` slots `{j : j < m}`. -/
def slotsBelow (k m : ℕ) : Finset (Fin k) := Finset.univ.filter fun j => j.val < m

theorem slotsBelow_zero (k : ℕ) : slotsBelow k 0 = ∅ := by
  ext j
  simp [slotsBelow]

theorem slotsBelow_succ {m : ℕ} (hm : m < k) :
    slotsBelow k (m + 1) = insert ⟨m, hm⟩ (slotsBelow k m) ∧
      (⟨m, hm⟩ : Fin k) ∉ slotsBelow k m := by
  refine ⟨?_, by simp [slotsBelow]⟩
  ext j
  simp only [slotsBelow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

theorem slotOp_const_mul (j : Fin k) (K : (Fin k → Fin N) → Fin N → ℝ) (C : ℝ)
    (g : (Fin k → Fin N) → ℝ) (x : Fin k → Fin N) :
    slotOp j K (fun y => C * g y) x = C * slotOp j K g x := by
  simp only [slotOp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **Iteration over the interior coordinates** `0, …, m-1` (`m + 1 ≤ k`): link families
`V m` (after `m` steps), endpoints `ea, eb` unchanged by interior updates, and per-step
constants `κ`. If step `m` (slot `m`, links `m, m+1`) costs `κ m`, then
`(G_{<m} *ᵥ √ linkProd (V 0)) x ≤ (Π_{i<m} κ i) √(linkProd (V m) (ea x) (eb x) x)`. -/
theorem tensorRSet_iter_le (F : Fin k → Matrix (Fin N) (Fin N) ℝ) (hF : ∀ j u v, 0 ≤ F j u v)
    (V : ℕ → ℕ → Fin N → Fin N → ℝ) (hV : ∀ m i u w, 0 ≤ V m i u w)
    (ea eb : (Fin k → Fin N) → Fin N)
    (hea : ∀ (y : Fin k → Fin N) (j : Fin k) (c : Fin N), j.val + 1 < k →
      ea (Function.update y j c) = ea y)
    (heb : ∀ (y : Fin k → Fin N) (j : Fin k) (c : Fin N), j.val + 1 < k →
      eb (Function.update y j c) = eb y)
    (κ : ℕ → ℝ) (hκ : ∀ m, 0 ≤ κ m)
    (hVV : ∀ m i, i ≠ m → i ≠ m + 1 → V m i = V (m + 1) i)
    (hstep : ∀ (m : ℕ) (hm : m + 1 < k) (x : Fin k → Fin N),
      ∑ c, F ⟨m, by omega⟩ (x ⟨m, by omega⟩) c *
          Real.sqrt (V m m (Psi.isoPoint (ea x) (eb x) x m) c *
            V m (m + 1) c (Psi.isoPoint (ea x) (eb x) x (m + 2))) ≤
        κ m * Real.sqrt (V (m + 1) m (Psi.isoPoint (ea x) (eb x) x m) (x ⟨m, by omega⟩) *
          V (m + 1) (m + 1) (x ⟨m, by omega⟩) (Psi.isoPoint (ea x) (eb x) x (m + 2)))) :
    ∀ m, m + 1 ≤ k → ∀ x,
      (tensorRSet F (slotsBelow k m) *ᵥ fun y => Real.sqrt (linkProd (V 0) (ea y) (eb y) y)) x ≤
        (∏ i ∈ Finset.range m, κ i) * Real.sqrt (linkProd (V m) (ea x) (eb x) x) := by
  intro m
  induction m with
  | zero =>
    intro _ x
    rw [slotsBelow_zero, tensorRSet_empty, Matrix.one_mulVec, Finset.prod_range_zero, one_mul]
  | succ m ih =>
    intro hmk x
    have hm : m < k := by omega
    obtain ⟨hins, hnot⟩ := slotsBelow_succ (k := k) hm
    rw [hins, (tensorRSet_insert F hnot).1, ← Matrix.mulVec_mulVec, mulVec_tensorRSet_single]
    have hK : ∀ (y : Fin k → Fin N) (c : Fin N), 0 ≤ F ⟨m, hm⟩ (y ⟨m, hm⟩) c :=
      fun y c => hF _ _ _
    have hP0 : 0 ≤ ∏ i ∈ Finset.range m, κ i := Finset.prod_nonneg fun i _ => hκ i
    calc slotOp ⟨m, hm⟩ (fun y c => F ⟨m, hm⟩ (y ⟨m, hm⟩) c)
          (tensorRSet F (slotsBelow k m) *ᵥ
            fun y => Real.sqrt (linkProd (V 0) (ea y) (eb y) y)) x
        ≤ slotOp ⟨m, hm⟩ (fun y c => F ⟨m, hm⟩ (y ⟨m, hm⟩) c)
          (fun y => (∏ i ∈ Finset.range m, κ i) *
            Real.sqrt (linkProd (V m) (ea y) (eb y) y)) x :=
          slotOp_mono _ hK (fun y => ih (by omega) y) x
      _ = (∏ i ∈ Finset.range m, κ i) * slotOp ⟨m, hm⟩ (fun y c => F ⟨m, hm⟩ (y ⟨m, hm⟩) c)
          (fun y => Real.sqrt (linkProd (V m) (ea x) (eb x) y)) x := by
          rw [← slotOp_const_mul]
          unfold slotOp
          refine Finset.sum_congr rfl fun c _ => ?_
          beta_reduce
          rw [hea x ⟨m, hm⟩ c (by simp; omega), heb x ⟨m, hm⟩ c (by simp; omega)]
      _ ≤ (∏ i ∈ Finset.range m, κ i) *
          (κ m * Real.sqrt (linkProd (V (m + 1)) (ea x) (eb x) x)) := by
          refine mul_le_mul_of_nonneg_left ?_ hP0
          exact slotOp_sqrt_linkProd_le ⟨m, hm⟩ (by simp; omega) (hVV m) (hV m) (ea x) (eb x) x
            (hstep m (by omega) x)
      _ = _ := by rw [Finset.prod_range_succ]; ring

theorem linkProd_congr {V V' : ℕ → Fin N → Fin N → ℝ} (h : ∀ i, i < k → V i = V' i)
    (a b : Fin N) (x : Fin k → Fin N) : linkProd V a b x = linkProd V' a b x :=
  Finset.prod_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

/-!
## Size functions as link products
-/

theorem sIso_eq_linkProd (P : Psi.PsiData N) (a b : Fin N) (x : Fin k → Fin N) (t : ℝ) :
    P.sIso a b x t =
      P.lEta t ^ (-((k : ℝ) - 1) / 2) * Real.sqrt (linkProd (fun _ => P.ups t) a b x) := rfl

/-- `s^av_{n+2}(x) = (ℓη)^{-(n+2)/2} √(linkProd Υ x_last x_last x)` (cyclic product). -/
theorem sAv_eq_linkProd (P : Psi.PsiData N) {n : ℕ} (x : Fin (n + 2) → Fin N) (t : ℝ) :
    P.sAv x t = P.lEta t ^ (-((n + 2 : ℕ) : ℝ) / 2) *
      Real.sqrt (linkProd (fun _ => P.ups t) (x (Fin.last (n + 1))) (x (Fin.last (n + 1))) x) := by
  unfold Psi.PsiData.sAv
  rw [ite_eq_right (by omega)]
  congr 2
  set e := x (Fin.last (n + 1)) with he
  set p := Psi.isoPoint e e x with hp
  have ha : ∀ j : Fin (n + 1), p (j.val + 1) = x j.castSucc := by
    intro j
    rw [hp]
    simp only [Psi.isoPoint, Nat.add_one_ne_zero, ite_false,
      dite_eq_left (by omega : j.val + 1 < n + 2)]
    congr
  have hb : ∀ j : Fin (n + 1), p (j.val + 1 + 1) = x (finRotate (n + 2) j.castSucc) := by
    intro j
    have hrot : finRotate (n + 2) j.castSucc = j.succ := by
      ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last j)]
      simp
    rw [hrot, hp]
    unfold Psi.isoPoint
    rw [ite_eq_right (by omega)]
    by_cases hj : j.val + 1 + 1 < n + 2
    · rw [dite_eq_left hj]
      congr 1
    · rw [dite_eq_right hj, he]
      congr 1
      ext
      simp
      omega
  have h0 : p 0 = e := by rw [hp]; simp [Psi.isoPoint]
  have h1 : p (0 + 1) = x 0 := by rw [hp]; simp [Psi.isoPoint]
  have hmain : ∏ j : Fin (n + 1), P.ups t (x j.castSucc) (x (finRotate (n + 2) j.castSucc)) =
      ∏ j : Fin (n + 1), P.ups t (p (j.val + 1)) (p (j.val + 1 + 1)) :=
    Finset.prod_congr rfl fun j _ => by rw [ha j, hb j]
  have hfin := Fin.prod_univ_eq_prod_range (fun i : ℕ => P.ups t (p (i + 1)) (p (i + 1 + 1)))
    (n + 1)
  unfold linkProd
  rw [Fin.prod_univ_castSucc, Finset.prod_range_succ', finRotate_last, hmain, hfin, ← hp, h0, h1]

end BlockBand.Native.ErdosRiabov.Propagator
