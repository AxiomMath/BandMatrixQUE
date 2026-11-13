module

public import BlockBand.SourceProcess.ContractingWords.CutRep
public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# Positional cut representation of one word

The cut representation `word_rep` labels the slots by separator *symbols*. Here every separator
slot is labelled by its *position*: for Hermitian letters `A : Fin (k+1) → Matrix` and any separator
assignment `T : Fin (k+1) → Matrix`,
`posTr A T = Tr Π_i (A_i T_i) = Σ_l c_l Π_p x_{lp}* T_p y_{lp}` (`posCut_of_herm`), unit vectors,
`Σ_l |c_l| ≤ Π_i Tr|A_i|`. Consequences, for every `T = σ + Δ`:
* `posTr_add`: `posTr A (σ + Δ) = Σ_{t ⊆ positions} posTr A (pw σ Δ t)` (noncommutative multilinear
  expansion, `pw` puts `Δ` on `t` and `σ` elsewhere), proved through the cut;
* `norm_posTr_pw_le`: `|posTr A (pw σ Δ t)| ≤ Σ_l |c_l| Π_{p∈t} |x_{lp}*Δ_p y_{lp}|` when `‖σ_p‖ ≤ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `Tr Π_i (A_i T_i)` with letters and separators indexed by position. -/
def posTr {r : ℕ} (A T : Fin r → Matrix n n ℂ) : ℂ :=
  (List.ofFn fun i => A i * T i).prod.trace

/-- A positional cut representation with total coefficient `Γ`. -/
def PosCut {r : ℕ} (A : Fin r → Matrix n n ℂ) (Γ : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (x y : ι → Fin r → n → ℂ), ∑ l, ‖c l‖ ≤ Γ ∧
    (∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1) ∧
    ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p)

/-- **Open chains** `u*(T₀ Π_{i<k} A_iT_{i+1})v`. -/
theorem posChain (k : ℕ) : ∀ (A : Fin k → Matrix n n ℂ), (∀ i, (A i).IsHermitian) →
    ∀ u v : n → ℂ, vecNorm u ≤ 1 → vecNorm v ≤ 1 →
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (x y : ι → Fin (k + 1) → n → ℂ),
      ∑ l, ‖c l‖ ≤ ∏ i, nuclearNorm (A i) ∧ (∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1) ∧
      ∀ T : Fin (k + 1) → Matrix n n ℂ,
        bilinear u (T 0 * (List.ofFn fun i : Fin k => A i * T i.succ).prod) v =
          ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p) := by
  induction k with
  | zero =>
    intro A _ u v hu hv
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => u, fun _ _ => v, by simp,
      fun _ _ => ⟨hu, hv⟩, fun T => ?_⟩
    simp
  | succ k ih =>
    intro A hA u v hu hv
    have hA0 := hA 0
    choose ι hι c x y hc hxy hrep using fun m =>
      ih (fun i => A i.succ) (fun i => hA i.succ) (eigVec hA0 m) v (vecNorm_eigVec hA0 m).le hv
    let _ : ∀ m, Fintype (ι m) := hι
    refine ⟨Σ m, ι m, inferInstance, fun l => ((hA0.eigenvalues l.1 : ℝ) : ℂ) * c l.1 l.2,
      fun l => Fin.cons u (x l.1 l.2), fun l => Fin.cons (eigVec hA0 l.1) (y l.1 l.2), ?_, ?_, ?_⟩
    · rw [Fintype.sum_sigma]
      have h1 : ∀ m, ∑ l, ‖((hA0.eigenvalues m : ℝ) : ℂ) * c m l‖ ≤
          |hA0.eigenvalues m| * ∏ i : Fin k, nuclearNorm (A i.succ) := fun m => by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hc m) (abs_nonneg _)
      calc _ ≤ ∑ m, |hA0.eigenvalues m| * ∏ i : Fin k, nuclearNorm (A i.succ) :=
            Finset.sum_le_sum fun m _ => h1 m
        _ = ∏ i, nuclearNorm (A i) := by
          rw [← Finset.sum_mul, ← nuclearNorm_eq_sum hA0, Fin.prod_univ_succ]
    · intro l p
      refine Fin.cases ?_ (fun i => ?_) p
      · exact ⟨by simpa using hu, by simpa using (vecNorm_eigVec hA0 l.1).le⟩
      · simpa using hxy l.1 l.2 i
    · intro T
      have e : T 0 * (List.ofFn fun i : Fin (k + 1) => A i * T i.succ).prod =
          T 0 * A 0 * (T (Fin.succ 0) *
            (List.ofFn fun i : Fin k => A i.succ * T i.succ.succ).prod) := by
        rw [List.ofFn_succ, List.prod_cons]; simp only [Matrix.mul_assoc]
      rw [e, bilinear_mul_herm_mul hA0, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hrep m (fun p => T p.succ), Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      conv_rhs => rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring

/-- **One nonempty word, positional slots.** -/
theorem posCut_of_herm {k : ℕ} (A : Fin (k + 1) → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    PosCut A (∏ i, nuclearNorm (A i)) := by
  have hA0 := hA 0
  choose ι hι c x y hc hxy hrep using fun m =>
    posChain k (fun i => A i.succ) (fun i => hA i.succ) (eigVec hA0 m) (eigVec hA0 m)
      (vecNorm_eigVec hA0 m).le (vecNorm_eigVec hA0 m).le
  let _ : ∀ m, Fintype (ι m) := hι
  refine ⟨Σ m, ι m, inferInstance, fun l => ((hA0.eigenvalues l.1 : ℝ) : ℂ) * c l.1 l.2,
    fun l => x l.1 l.2, fun l => y l.1 l.2, ?_, fun l p => hxy l.1 l.2 p, fun T => ?_⟩
  · rw [Fintype.sum_sigma]
    have h1 : ∀ m, ∑ l, ‖((hA0.eigenvalues m : ℝ) : ℂ) * c m l‖ ≤
        |hA0.eigenvalues m| * ∏ i : Fin k, nuclearNorm (A i.succ) := fun m => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hc m) (abs_nonneg _)
    calc _ ≤ ∑ m, |hA0.eigenvalues m| * ∏ i : Fin k, nuclearNorm (A i.succ) :=
          Finset.sum_le_sum fun m _ => h1 m
      _ = ∏ i, nuclearNorm (A i) := by
        rw [← Finset.sum_mul, ← nuclearNorm_eq_sum hA0, Fin.prod_univ_succ]
  · have e : (List.ofFn fun i => A i * T i).prod =
        A 0 * (T 0 * (List.ofFn fun i : Fin k => A i.succ * T i.succ).prod) := by
      rw [List.ofFn_succ, List.prod_cons]; simp only [Matrix.mul_assoc]
    rw [posTr, e, trace_herm_mul hA0, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hrep m T, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

/-- `Δ` on the positions of `t`, `σ` elsewhere. -/
def pw {r : ℕ} (σ Δ : Fin r → Matrix n n ℂ) (t : Finset (Fin r)) : Fin r → Matrix n n ℂ :=
  fun i => if i ∈ t then Δ i else σ i

section Expansion

variable {r : ℕ} {A : Fin r → Matrix n n ℂ} {ι : Type} [Fintype ι] {c : ι → ℂ}
  {x y : ι → Fin r → n → ℂ}

omit [DecidableEq n] in
theorem bilinear_add_mat (u : n → ℂ) (M M' : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u (M + M') v = bilinear u M v + bilinear u M' v := by
  simp [bilinear, Matrix.add_mulVec]

/-- The cut value at `pw σ Δ t`. -/
theorem posTr_pw (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (σ Δ : Fin r → Matrix n n ℂ) (t : Finset (Fin r)) :
    posTr A (pw σ Δ t) = ∑ l, c l * ((∏ p ∈ t, bilinear (x l p) (Δ p) (y l p)) *
      ∏ p ∈ Finset.univ \ t, bilinear (x l p) (σ p) (y l p)) := by
  rw [hrep]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [← Finset.prod_sdiff (Finset.subset_univ t), mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun p hp => by simp [pw, hp]
  · exact Finset.prod_congr rfl fun p hp => by
      simp only [Finset.mem_sdiff] at hp; simp [pw, hp.2]

/-- **Multilinear expansion** `posTr A (σ + Δ) = Σ_t posTr A (pw σ Δ t)`. -/
theorem posTr_add (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (σ Δ : Fin r → Matrix n n ℂ) :
    posTr A (σ + Δ) = ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset, posTr A (pw σ Δ t) := by
  simp only [posTr_pw hrep]
  rw [hrep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have e : ∀ p, bilinear (x l p) ((σ + Δ) p) (y l p) =
      bilinear (x l p) (Δ p) (y l p) + bilinear (x l p) (σ p) (y l p) := fun p => by
    rw [Pi.add_apply, bilinear_add_mat, add_comm]
  simp only [e]
  exact Finset.prod_add _ _ _

/-- **Size of one term** when `‖σ_p‖ ≤ 1`. -/
theorem norm_posTr_pw_le
    (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (hxy : ∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1)
    {σ : Fin r → Matrix n n ℂ} (hσ : ∀ p, ‖σ p‖ ≤ 1) (Δ : Fin r → Matrix n n ℂ)
    (t : Finset (Fin r)) :
    ‖posTr A (pw σ Δ t)‖ ≤ ∑ l, ‖c l‖ * ∏ p ∈ t, ‖bilinear (x l p) (Δ p) (y l p)‖ := by
  rw [posTr_pw hrep]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine mul_le_of_le_one_right (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun p _ => ?_
  have h := norm_bilinear_le (x l p) (σ p) (y l p)
  have hx := (hxy l p).1
  have hy := (hxy l p).2
  have h0 := vecNorm_nonneg (x l p)
  calc _ ≤ vecNorm (x l p) * ‖σ p‖ * vecNorm (y l p) := h
    _ ≤ 1 * 1 * 1 := by
        have := hσ p
        have := vecNorm_nonneg (y l p)
        gcongr
    _ = 1 := by ring

end Expansion

end BlockBand.SourceProcess.ContractingWords
