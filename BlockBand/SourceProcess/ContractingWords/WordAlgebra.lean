module

public import BlockBand.SourceProcess.ContractingWords.CutRep
public import BlockBand.SourceProcess.FullSource.TraceAlgebra
public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# Matrix-word algebra for the one-step update

* `trace_prod_conj`: `Tr Π_i(N*A_iN S_i) = Tr Π_i(A_i·NS_iN*)` (the separator becomes `NBN*`);
* `trace_inj_le`: an injection `A_i ↦ A_i + c_iD*D` changes `Tr Π_i(A_iS_i)` by at most
  `(Σ|c_i|)·Tr(D*D)·s·Π_i(1 + (‖A_i‖ + |c_i|‖D*D‖)s)`, `‖S_i‖ ≤ s` (no dimension factor:
  the injection is cut at its own trace).

The sibling module `WordBounds` proves the scalar companions `norm_list_prod_sub_le`
(`|Π a_i - Π b_i| ≤ (Σ|a_i - b_i|) Π(1 + |a_i| + |b_i|)`), `norm_le_nuclearNorm` (`‖A‖ ≤ Tr|A|` for
Hermitian `A`) and `list_prod_smul_sep` (scalars of the separators come out of a word).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance BlockBand.SourceProcess.FullSource
open scoped Matrix.Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n]

theorem list_prod_conj_mul (N : Matrix n n ℂ) (L : List (Matrix n n ℂ × Matrix n n ℂ)) :
    (L.map fun x : Matrix n n ℂ × Matrix n n ℂ => Nᴴ * x.1 * N * x.2).prod * Nᴴ =
      Nᴴ * (L.map fun x : Matrix n n ℂ × Matrix n n ℂ => x.1 * (N * x.2 * Nᴴ)).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_assoc] at ih ⊢
    rw [ih]

/-- **Rotation of the transport onto the separators.** -/
theorem trace_prod_conj (N : Matrix n n ℂ) (L : List (Matrix n n ℂ × Matrix n n ℂ)) :
    (L.map fun x : Matrix n n ℂ × Matrix n n ℂ => Nᴴ * x.1 * N * x.2).prod.trace =
      (L.map fun x : Matrix n n ℂ × Matrix n n ℂ => x.1 * (N * x.2 * Nᴴ)).prod.trace := by
  cases L with
  | nil => simp
  | cons x L =>
    have h := list_prod_conj_mul N L
    simp only [List.map_cons, List.prod_cons]
    rw [show Nᴴ * x.1 * N * x.2 * (L.map fun x : Matrix n n ℂ × Matrix n n ℂ => Nᴴ * x.1 * N * x.2).prod =
        Nᴴ * (x.1 * N * x.2 * (L.map fun x : Matrix n n ℂ × Matrix n n ℂ => Nᴴ * x.1 * N * x.2).prod) by
        simp only [Matrix.mul_assoc], trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, h]
    simp only [Matrix.mul_assoc]

theorem list_prod_le_of_le {α : Type*} (L : List α) (f g : α → ℝ) (h0 : ∀ t ∈ L, 0 ≤ f t)
    (h : ∀ t ∈ L, f t ≤ g t) : (L.map f).prod ≤ (L.map g).prod := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.prod_cons]
    have hf0 : 0 ≤ (L.map f).prod := List.prod_nonneg fun x hx => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx; exact h0 u (List.mem_cons_of_mem _ hu)
    exact mul_le_mul (h t (List.mem_cons_self ..))
      (ih (fun u hu => h0 u (List.mem_cons_of_mem _ hu)) (fun u hu => h u (List.mem_cons_of_mem _ hu)))
      hf0 ((h0 t (List.mem_cons_self ..)).trans (h t (List.mem_cons_self ..)))

theorem norm_list_prod_le (L : List (Matrix n n ℂ)) :
    ‖L.prod‖ ≤ (L.map fun X => 1 + ‖X‖).prod := by
  induction L with
  | nil => simpa using norm_one_matrix_le
  | cons X L ih =>
    simp only [List.prod_cons, List.map_cons]
    refine (norm_mul_le _ _).trans ?_
    have h0 : 0 ≤ ‖L.prod‖ := norm_nonneg _
    nlinarith [norm_nonneg X]

theorem inj_step {m : Type} [Fintype m] [DecidableEq m] (D : Matrix m n ℂ)
    (M X S P' P'' : Matrix n n ℂ) (c s Sg R : ℝ) (hs : 0 ≤ s) (hS : ‖S‖ ≤ s) (hP' : ‖P'‖ ≤ R)
    (hR0 : 0 ≤ R) (hSg0 : 0 ≤ Sg)
    (ih : ‖((M * X * S) * P').trace - ((M * X * S) * P'').trace‖ ≤
      ‖M * X * S‖ * (Sg * ((Dᴴ * D).trace.re * s) * R)) :
    ‖(M * ((X + (c : ℂ) • (Dᴴ * D)) * S * P')).trace - (M * (X * S * P'')).trace‖ ≤
      ‖M‖ * ((|c| + Sg) * ((Dᴴ * D).trace.re * s) *
        ((1 + (‖X‖ + |c| * ‖Dᴴ * D‖) * s) * R)) := by
  have hτ : 0 ≤ (Dᴴ * D).trace.re := trace_factor_re_nonneg D
  generalize hτd : (Dᴴ * D).trace.re = τ at hτ ih ⊢
  have e : (M * ((X + (c : ℂ) • (Dᴴ * D)) * S * P')).trace - (M * (X * S * P'')).trace =
      ((M * X * S) * P').trace - ((M * X * S) * P'').trace +
        (c : ℂ) * (Dᴴ * D * (S * P' * M)).trace := by
    have h1 : (M * ((Dᴴ * D) * S * P')).trace = (Dᴴ * D * (S * P' * M)).trace := by
      rw [trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, trace_add, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul, h1]
    simp only [Matrix.mul_assoc]; ring
  rw [e]
  have h2 : ‖(Dᴴ * D * (S * P' * M)).trace‖ ≤ s * R * ‖M‖ * τ := by
    refine (norm_trace_factor_le D _).trans ?_
    rw [hτd]
    have : ‖S * P' * M‖ ≤ s * R * ‖M‖ := by
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact (norm_mul_le _ _).trans (mul_le_mul hS hP' (norm_nonneg _) hs)
    exact mul_le_mul_of_nonneg_right this hτ
  have h3 : ‖M * X * S‖ ≤ ‖M‖ * ‖X‖ * s :=
    (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le _ _) hS (norm_nonneg _) (by positivity))
  have hM := norm_nonneg M
  have hX := norm_nonneg X
  have hc := abs_nonneg c
  have hn := norm_nonneg (Dᴴ * D)
  calc ‖((M * X * S) * P').trace - ((M * X * S) * P'').trace +
        (c : ℂ) * (Dᴴ * D * (S * P' * M)).trace‖ ≤
        ‖M‖ * ‖X‖ * s * (Sg * (τ * s) * R) + |c| * (s * R * ‖M‖ * τ) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact ih.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left h2 hc
    _ ≤ ‖M‖ * ((|c| + Sg) * (τ * s) * ((1 + (‖X‖ + |c| * ‖Dᴴ * D‖) * s) * R)) := by
        have hA : 0 ≤ ‖M‖ * (τ * s) * R := by positivity
        have hB : 0 ≤ (‖X‖ + |c| * ‖Dᴴ * D‖) * s := by positivity
        have key : ‖X‖ * s * Sg + |c| ≤ (|c| + Sg) * (1 + (‖X‖ + |c| * ‖Dᴴ * D‖) * s) := by
          nlinarith [mul_nonneg hc hB, mul_nonneg hSg0 (mul_nonneg (mul_nonneg hc hn) hs)]
        calc ‖M‖ * ‖X‖ * s * (Sg * (τ * s) * R) + |c| * (s * R * ‖M‖ * τ) =
              (‖M‖ * (τ * s) * R) * (‖X‖ * s * Sg + |c|) := by ring
          _ ≤ (‖M‖ * (τ * s) * R) * ((|c| + Sg) * (1 + (‖X‖ + |c| * ‖Dᴴ * D‖) * s)) :=
              mul_le_mul_of_nonneg_left key hA
          _ = _ := by ring

/-- **The injection bound.** `C = D*D`, `τ = Re Tr C`, `‖S_i‖ ≤ s`. -/
theorem trace_inj_le {m : Type} [Fintype m] [DecidableEq m] (D : Matrix m n ℂ) {s : ℝ}
    (hs : 0 ≤ s) (L : List (Matrix n n ℂ × ℝ × Matrix n n ℂ)) (hL : ∀ t ∈ L, ‖t.2.2‖ ≤ s) :
    ∀ M : Matrix n n ℂ,
      ‖(M * (L.map fun t => (t.1 + (t.2.1 : ℂ) • (Dᴴ * D)) * t.2.2).prod).trace -
          (M * (L.map fun t => t.1 * t.2.2).prod).trace‖ ≤
        ‖M‖ * ((L.map fun t => |t.2.1|).sum * ((Dᴴ * D).trace.re * s) *
          (L.map fun t => 1 + (‖t.1‖ + |t.2.1| * ‖Dᴴ * D‖) * s).prod) := by
  induction L with
  | nil => intro M; simp
  | cons t L ih =>
    intro M
    have hS : ‖t.2.2‖ ≤ s := hL _ (List.mem_cons_self ..)
    have ih' := ih (fun t ht => hL t (List.mem_cons_of_mem _ ht))
    have hR0 : 0 ≤ (L.map fun t => 1 + (‖t.1‖ + |t.2.1| * ‖Dᴴ * D‖) * s).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx; positivity
    have hSg0 : 0 ≤ (L.map fun t => |t.2.1|).sum := List.sum_nonneg fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx; positivity
    have hP' : ‖(L.map fun t => (t.1 + (t.2.1 : ℂ) • (Dᴴ * D)) * t.2.2).prod‖ ≤
        (L.map fun t => 1 + (‖t.1‖ + |t.2.1| * ‖Dᴴ * D‖) * s).prod := by
      refine (norm_list_prod_le _).trans ?_
      rw [List.map_map]
      refine list_prod_le_of_le L _ _ (fun t _ => by simp only [Function.comp_apply]; positivity) fun t ht => ?_
      have hSt := hL t (List.mem_cons_of_mem _ ht)
      simp only [Function.comp_apply]
      have : ‖(t.1 + (t.2.1 : ℂ) • (Dᴴ * D)) * t.2.2‖ ≤ (‖t.1‖ + |t.2.1| * ‖Dᴴ * D‖) * s := by
        refine (norm_mul_le _ _).trans (mul_le_mul ?_ hSt (norm_nonneg _) (by positivity))
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      linarith
    have := inj_step D M t.1 t.2.2 _ _ t.2.1 s _ _ hs hS hP' hR0 hSg0 (ih' (M * t.1 * t.2.2))
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    simpa only [Matrix.mul_assoc] using this

end BlockBand.SourceProcess.ContractingWords
