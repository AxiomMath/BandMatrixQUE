module

public import BlockBand.SourceProcess.ContractingWords.CutSpec

/-!
# Products of words as sums of products of bilinear forms

A word is a list `[(A₁,s₁),…,(A_r,s_r)]` of Hermitian letters `A_i` and separator symbols `s_i`;
its value at an assignment `T : S → Matrix` of the separators is `Tr Π_i (A_i T(s_i))`.
Cutting at **every** letter (`A_i = Σ_m λ_{im} e_{im}e_{im}*`, `CutSpec`) writes the value as
`Σ_ℓ c_ℓ Π_p (x_{ℓp}* T(σ_p) y_{ℓp})` with unit vectors independent of `T` and
`Σ_ℓ |c_ℓ| ≤ Π_i Tr|A_i|` (`HasCutRep`). No free trace of `I` or `P` occurs: this is the paper's
"products do not lose a dimension factor". The paper cuts only the segments between centered
factors; cutting at every letter costs `Π_i Tr|A_i| ≤ K^{deg}` before the stop, which is enough.

* `chain_rep`: `u*(T(s₀) Π_i A_iT(s_i))v` (open chain);
* `word_rep`: one nonempty word; `HasCutRep.mul`, `HasCutRep.one`; `product_rep`: products.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix BlockBand.Internal.Contracts.TransmissionStatements

variable {n : Type} [Fintype n] [DecidableEq n] {S : Type}

/-- The value `Tr Π_i (A_i T(s_i))` of a matrix word at a separator assignment `T`. -/
def matWord (T : S → Matrix n n ℂ) (w : List (Matrix n n ℂ × S)) : ℂ :=
  (w.map fun x : Matrix n n ℂ × S => x.1 * T x.2).prod.trace

/-- `Π_i Tr|A_i|` of a matrix word. -/
def wordNuc (w : List (Matrix n n ℂ × S)) : ℝ :=
  (w.map fun x : Matrix n n ℂ × S => nuclearNorm x.1).prod

/-- The separator symbols of an open chain `T(s₀) A₁T(s₁) ⋯ A_rT(s_r)`. -/
def chainSeps (s₀ : S) : (L : List (Matrix n n ℂ × S)) → Fin (L.length + 1) → S
  | [] => fun _ => s₀
  | x :: L => Fin.cons s₀ (chainSeps x.2 L)

/-- **Cut representation** of `F : (S → Matrix) → ℂ` with at most `d` factors and total
coefficient `Γ`: `F T = Σ_ℓ c_ℓ Π_p x_{ℓp}* T(σ_p) y_{ℓp}` for every `T`, unit vectors. -/
def HasCutRep (F : (S → Matrix n n ℂ) → ℂ) (d : ℕ) (Γ : ℝ) : Prop :=
  ∃ (P : Type) (_ : Fintype P) (σ : P → S) (ι : Type) (_ : Fintype ι) (c : ι → ℂ)
    (x y : ι → P → n → ℂ), Fintype.card P ≤ d ∧ ∑ l, ‖c l‖ ≤ Γ ∧
    (∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1) ∧
    ∀ T, F T = ∑ l, c l * ∏ p, bilinear (x l p) (T (σ p)) (y l p)

theorem wordNuc_nonneg (w : List (Matrix n n ℂ × S)) : 0 ≤ wordNuc w := by
  induction w with
  | nil => simp [wordNuc]
  | cons x w ih =>
    simp only [wordNuc, List.map_cons, List.prod_cons] at ih ⊢
    exact mul_nonneg (nuclearNorm_nonneg _) ih

/-- **Open chains.** -/
theorem chain_rep (L : List (Matrix n n ℂ × S)) (hL : ∀ x ∈ L, x.1.IsHermitian) :
    ∀ (s₀ : S) (u v : n → ℂ), vecNorm u ≤ 1 → vecNorm v ≤ 1 →
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (x y : ι → Fin (L.length + 1) → n → ℂ),
      ∑ l, ‖c l‖ ≤ wordNuc L ∧ (∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1) ∧
      ∀ T : S → Matrix n n ℂ, bilinear u (T s₀ * (L.map fun x => x.1 * T x.2).prod) v =
        ∑ l, c l * ∏ p, bilinear (x l p) (T (chainSeps s₀ L p)) (y l p) := by
  induction L with
  | nil =>
    intro s₀ u v hu hv
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => u, fun _ _ => v, ?_, fun _ _ => ⟨hu, hv⟩,
      fun T => ?_⟩
    · simp [wordNuc]
    · simp [chainSeps]
  | cons a L ih =>
    intro s₀ u v hu hv
    have hA : a.1.IsHermitian := hL a (List.mem_cons_self ..)
    have ih' := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    choose ι hι c x y hc hxy hrep using fun m => ih' a.2 (eigVec hA m) v
      (vecNorm_eigVec hA m).le hv
    let _ : ∀ m, Fintype (ι m) := hι
    refine ⟨Σ m, ι m, inferInstance, fun l => ((hA.eigenvalues l.1 : ℝ) : ℂ) * c l.1 l.2,
      fun l => Fin.cons u (x l.1 l.2), fun l => Fin.cons (eigVec hA l.1) (y l.1 l.2), ?_, ?_, ?_⟩
    · rw [Fintype.sum_sigma]
      have h1 : ∀ m, ∑ l, ‖((hA.eigenvalues m : ℝ) : ℂ) * c m l‖ ≤
          |hA.eigenvalues m| * wordNuc L := fun m => by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hc m) (abs_nonneg _)
      calc _ ≤ ∑ m, |hA.eigenvalues m| * wordNuc L := Finset.sum_le_sum fun m _ => h1 m
        _ = wordNuc (a :: L) := by
          rw [← Finset.sum_mul, ← nuclearNorm_eq_sum hA]; simp [wordNuc]
    · intro l p
      refine Fin.cases ?_ (fun i => ?_) p
      · exact ⟨by simpa using hu, by simpa using (vecNorm_eigVec hA l.1).le⟩
      · simpa using hxy l.1 l.2 i
    · intro T
      have e : T s₀ * ((a :: L).map fun x => x.1 * T x.2).prod =
          T s₀ * a.1 * (T a.2 * (L.map fun x => x.1 * T x.2).prod) := by
        simp only [List.map_cons, List.prod_cons, Matrix.mul_assoc]
      rw [e, bilinear_mul_herm_mul hA, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hrep m T, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      conv_rhs => rw [Fin.prod_univ_succ]
      simp only [chainSeps, Fin.cons_zero, Fin.cons_succ]
      have hP : (∏ p : Fin (a :: L).length,
          bilinear (x m l p) (T (chainSeps a.2 L p)) (y m l p)) =
          ∏ p : Fin (L.length + 1), bilinear (x m l p) (T (chainSeps a.2 L p)) (y m l p) := rfl
      rw [hP]; ring

/-- **One nonempty word** with Hermitian letters. -/
theorem word_rep (w : List (Matrix n n ℂ × S)) (hw : w ≠ []) (hH : ∀ x ∈ w, x.1.IsHermitian) :
    HasCutRep (fun T => matWord T w) w.length (wordNuc w) := by
  obtain ⟨a, L, rfl⟩ := List.exists_cons_of_ne_nil hw
  have hA : a.1.IsHermitian := hH a (List.mem_cons_self ..)
  choose ι hι c x y hc hxy hrep using fun m =>
    chain_rep L (fun z hz => hH z (List.mem_cons_of_mem _ hz)) a.2 (eigVec hA m) (eigVec hA m)
      (vecNorm_eigVec hA m).le (vecNorm_eigVec hA m).le
  let _ : ∀ m, Fintype (ι m) := hι
  refine ⟨Fin (L.length + 1), inferInstance, chainSeps a.2 L, Σ m, ι m, inferInstance,
    fun l => ((hA.eigenvalues l.1 : ℝ) : ℂ) * c l.1 l.2, fun l => x l.1 l.2, fun l => y l.1 l.2,
    by simp, ?_, fun l p => hxy l.1 l.2 p, fun T => ?_⟩
  · rw [Fintype.sum_sigma]
    have h1 : ∀ m, ∑ l, ‖((hA.eigenvalues m : ℝ) : ℂ) * c m l‖ ≤
        |hA.eigenvalues m| * wordNuc L := fun m => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hc m) (abs_nonneg _)
    calc _ ≤ ∑ m, |hA.eigenvalues m| * wordNuc L := Finset.sum_le_sum fun m _ => h1 m
      _ = wordNuc (a :: L) := by
        rw [← Finset.sum_mul, ← nuclearNorm_eq_sum hA]; simp [wordNuc]
  · have e : ((a :: L).map fun x => x.1 * T x.2).prod =
        a.1 * (T a.2 * (L.map fun x => x.1 * T x.2).prod) := by
      simp only [List.map_cons, List.prod_cons, Matrix.mul_assoc]
    simp only [matWord]
    rw [e, trace_herm_mul hA, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hrep m T, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

omit [DecidableEq n] in
theorem HasCutRep.one : HasCutRep (n := n) (S := S) (fun _ => 1) 0 1 :=
  ⟨Empty, inferInstance, Empty.elim, Unit, inferInstance, fun _ => 1, fun _ e => e.elim,
    fun _ e => e.elim, by simp, by simp, fun _ e => e.elim, fun T => by simp⟩

omit [DecidableEq n] in
theorem HasCutRep.mul {F G : (S → Matrix n n ℂ) → ℂ} {d e : ℕ} {Γ Δ : ℝ}
    (hF : HasCutRep F d Γ) (hG : HasCutRep G e Δ) :
    HasCutRep (fun T => F T * G T) (d + e) (Γ * Δ) := by
  obtain ⟨P, hP, σ, ι, hι, c, x, y, hd, hc, hxy, hrep⟩ := hF
  obtain ⟨P', hP', σ', ι', hι', c', x', y', hd', hc', hxy', hrep'⟩ := hG
  refine ⟨P ⊕ P', inferInstance, Sum.elim σ σ', ι × ι', inferInstance,
    fun l => c l.1 * c' l.2, fun l => Sum.elim (x l.1) (x' l.2),
    fun l => Sum.elim (y l.1) (y' l.2), ?_, ?_, ?_, fun T => ?_⟩
  · rw [Fintype.card_sum]; omega
  · rw [Fintype.sum_prod_type]
    simp only [norm_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    have h0 : 0 ≤ ∑ l, ‖c' l‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    exact mul_le_mul hc hc' h0 ((Finset.sum_nonneg fun _ _ => norm_nonneg _).trans hc)
  · intro l p
    cases p with
    | inl p => exact hxy l.1 p
    | inr p => exact hxy' l.2 p
  · show F T * G T = _
    rw [hrep T, hrep' T, Fintype.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    ring

/-- **Products of nonempty words** with Hermitian letters. -/
theorem product_rep (Zs : List (List (Matrix n n ℂ × S))) (hne : ∀ w ∈ Zs, w ≠ [])
    (hH : ∀ w ∈ Zs, ∀ x ∈ w, x.1.IsHermitian) :
    HasCutRep (fun T => (Zs.map (matWord T)).prod) (Zs.map List.length).sum
      (Zs.map wordNuc).prod := by
  induction Zs with
  | nil => simpa using HasCutRep.one
  | cons w Zs ih =>
    have h := (word_rep w (hne w (List.mem_cons_self ..)) (hH w (List.mem_cons_self ..))).mul
      (ih (fun v hv => hne v (List.mem_cons_of_mem _ hv))
        (fun v hv => hH v (List.mem_cons_of_mem _ hv)))
    simpa only [List.map_cons, List.prod_cons, List.sum_cons] using h

end BlockBand.SourceProcess.ContractingWords
