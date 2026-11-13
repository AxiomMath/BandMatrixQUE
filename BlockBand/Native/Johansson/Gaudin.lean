module

public import BlockBand.Native.Johansson.Defs
public import BlockBand.Native.Johansson.Biorthogonal

/-!
# Johansson's formula (2.18): Gaudin marginals of the real kernel

Integrating out variables of the determinant of a biorthogonal kernel gives the lower
determinants with the factors `N - m`.

* `gaudin_snoc` (abstract Gaudin/Mehta lemma): for `φ, ψ : Fin N → ℝ → ℝ` with every `φ_a ψ_b`
  integrable and `∫ φ_a ψ_b = δ_ab`, and `K(u, v) = Σ_j φ_j(u) ψ_j(v)`,
  `∫ det[K]_{m+1}(x, y) dy = (N - m) det[K]_m(x)` for every `x`, with integrability.
  The proof expands the bordered determinant (`det_border_zero`) into the bilinear form
  `Σ_{a,b} C_ab φ_a(y) ψ_b(y)` and evaluates the diagonal sum by Cramer's rule.
* `integrable_kdet_append`: integrability of every section, from the Leibniz expansion into
  products of one-variable functions `φ_a ψ_b`.
* `gaudin_append`: the iterated marginal, by Fubini on `Fin (n+1) → ℝ ≃ ℝ × (Fin n → ℝ)`.
* `kernelMarginal_of_biorthogonal : BiorthogonalStatement → KernelMarginalStatement`, and
  `kernelMarginal_holds : KernelMarginalStatement` with `biorthogonal_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory Matrix
open scoped BigOperators

/-- Deleting row `0` and column `l+1` of a bordered matrix leaves the corner block with its
column `l` replaced by the border column, up to the column cycle `l.cycleRange.symm`. -/
theorem submatrix_succAbove_eq {R : Type*} [CommRing R] {m : ℕ}
    (B : Matrix (Fin (m+2)) (Fin (m+2)) R) (l : Fin (m+1)) :
    B.submatrix Fin.succ l.succ.succAbove =
      ((B.submatrix Fin.succ Fin.succ).updateCol l (fun i => B i.succ 0)).submatrix id
        l.cycleRange.symm := by
  ext i k
  refine Fin.cases ?_ (fun k' => ?_) k
  · simp [Fin.cycleRange_symm_zero]
  · simp [Fin.cycleRange_symm_succ, Fin.succ_succAbove_succ,
      Fin.succAbove_ne]

/-- **Bordered determinant** (border at index `0`): with `A` the lower-right corner block,
`det B = B₀₀ det A - Σ_l B₀,ₗ₊₁ det (A with column l replaced by (Bᵢ₊₁,₀)ᵢ)`. -/
theorem det_border_zero {R : Type*} [CommRing R] {m : ℕ}
    (B : Matrix (Fin (m+1)) (Fin (m+1)) R) :
    B.det = B 0 0 * (B.submatrix Fin.succ Fin.succ).det -
      ∑ l : Fin m, B 0 l.succ *
        ((B.submatrix Fin.succ Fin.succ).updateCol l (fun i => B i.succ 0)).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  cases m with
  | zero => simp
  | succ m =>
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [submatrix_succAbove_eq, det_permute', Equiv.Perm.sign_symm, Fin.sign_cycleRange]
    simp only [Fin.val_succ, pow_succ]
    push_cast
    have h1 : ((-1 : R) ^ (l : ℕ)) * (-1) ^ (l : ℕ) = 1 := by rw [← mul_pow]; simp
    linear_combination (-(B 0 l.succ *
      ((B.submatrix Fin.succ Fin.succ).updateCol l fun i => B i.succ 0).det)) * h1

/-- Integral of a bilinear combination `Σ_{a,b} C_ab φ_a ψ_b` of biorthogonal products. -/
theorem integral_bilin {N : ℕ} (φ ψ : Fin N → ℝ → ℝ)
    (hint : ∀ a b, Integrable (fun u => φ a u * ψ b u))
    (hδ : ∀ a b, ∫ u, φ a u * ψ b u = if a = b then 1 else 0) (C : Fin N → Fin N → ℝ) :
    Integrable (fun y => ∑ a, ∑ b, C a b * (φ a y * ψ b y)) ∧
      ∫ y, ∑ a, ∑ b, C a b * (φ a y * ψ b y) = ∑ a, C a a := by
  have hi : ∀ a b, Integrable (fun y => C a b * (φ a y * ψ b y)) :=
    fun a b => (hint a b).const_mul _
  refine ⟨integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi a b, ?_⟩
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hi a b]
  simp [integral_const_mul, hδ]

/-- Expansion of `det[K]_{m+1}(y, x)` as a bilinear combination of `φ_a(y) ψ_b(y)`. -/
theorem kdet_cons_expand {N m : ℕ} (φ ψ : Fin N → ℝ → ℝ) (x : Fin m → ℝ) (y : ℝ) :
    (Matrix.of fun i l => ∑ j, φ j ((Fin.cons y x : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.cons y x : Fin (m+1) → ℝ) l)).det =
      ∑ a, ∑ b, ((if a = b then (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l)).det else 0) -
        ∑ l, ψ a (x l) * cramer (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l))
          (fun i => φ b (x i)) l) * (φ a y * ψ b y) := by
  set A := (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l)) with hA
  rw [det_border_zero]
  have hsub : ((Matrix.of fun i l => ∑ j, φ j ((Fin.cons y x : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.cons y x : Fin (m+1) → ℝ) l)).submatrix Fin.succ Fin.succ) = A := by
    ext i l; simp [hA]
  rw [hsub]
  have hcol : ∀ l : Fin m, (A.updateCol l fun i => (Matrix.of fun i l => ∑ j,
      φ j ((Fin.cons y x : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.cons y x : Fin (m+1) → ℝ) l)) i.succ 0).det =
      ∑ b, ψ b y * cramer A (fun i => φ b (x i)) l := by
    intro l
    rw [← cramer_apply]
    have : (fun i => (Matrix.of fun i l => ∑ j, φ j ((Fin.cons y x : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.cons y x : Fin (m+1) → ℝ) l)) i.succ 0) =
        ∑ b, ψ b y • (fun i => φ b (x i)) := by
      ext i; simp [mul_comm]
    rw [this, map_sum]
    simp [Finset.sum_apply]
  simp only [hcol]
  simp only [of_apply, Fin.cons_zero, Fin.cons_succ]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => by ring
  · conv_rhs => rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

/-- The diagonal sum of the coefficients of `kdet_cons_expand` is `(N - m) det[K]_m(x)`. -/
theorem gaudin_diag {N m : ℕ} (φ ψ : Fin N → ℝ → ℝ) (x : Fin m → ℝ) :
    ∑ a : Fin N, ((if a = a then (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l)).det else 0) -
        ∑ l, ψ a (x l) * cramer (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l))
          (fun i => φ a (x i)) l) =
      ((N : ℝ) - m) * (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l)).det := by
  set A := (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l)) with hA
  have hl : ∀ l : Fin m, ∑ a : Fin N, ψ a (x l) * cramer A (fun i => φ a (x i)) l = A.det := by
    intro l
    have hv : (fun i => A i l) = ∑ a : Fin N, ψ a (x l) • (fun i => φ a (x i)) := by
      ext i; simp [hA, Finset.sum_apply, mul_comm]
    have := congrArg (fun v => cramer A v l) hv
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this, cramer_apply, updateCol_eq_self]
  simp only [ite_true, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_comm]
  simp only [hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Gaudin lemma**, new variable in front. -/
theorem gaudin_cons {N m : ℕ} (φ ψ : Fin N → ℝ → ℝ)
    (hint : ∀ a b, Integrable (fun u => φ a u * ψ b u))
    (hδ : ∀ a b, ∫ u, φ a u * ψ b u = if a = b then 1 else 0) (x : Fin m → ℝ) :
    Integrable (fun y => (Matrix.of fun i l => ∑ j, φ j ((Fin.cons y x : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.cons y x : Fin (m+1) → ℝ) l)).det) ∧
      ∫ y, (Matrix.of fun i l => ∑ j, φ j ((Fin.cons y x : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.cons y x : Fin (m+1) → ℝ) l)).det =
      ((N : ℝ) - m) * (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l)).det := by
  simp only [kdet_cons_expand]
  obtain ⟨h1, h2⟩ := integral_bilin φ ψ hint hδ (fun a b =>
    (if a = b then (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l)).det else 0) -
        ∑ l, ψ a (x l) * cramer (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l))
          (fun i => φ b (x i)) l)
  exact ⟨h1, h2.trans (gaudin_diag φ ψ x)⟩

/-- `det[K(z_i, z_l)]` is invariant under a simultaneous reindexing of the points. -/
theorem kdet_comp_equiv {N M M' : ℕ} (φ ψ : Fin N → ℝ → ℝ) (z : Fin M → ℝ)
    (e : Fin M' ≃ Fin M) :
    (Matrix.of fun i l => ∑ j, φ j (z (e i)) * ψ j (z (e l))).det =
      (Matrix.of fun i l => ∑ j, φ j (z i) * ψ j (z l)).det :=
  det_submatrix_equiv_self e (Matrix.of fun i l => ∑ j, φ j (z i) * ψ j (z l))

/-- `snoc x y` reindexed by `(last m).cycleRange.symm` is `cons y x`. -/
theorem snoc_comp_cycleRange {m : ℕ} (x : Fin m → ℝ) (y : ℝ) :
    (fun k => (Fin.snoc x y : Fin (m+1) → ℝ) ((Fin.last m).cycleRange.symm k)) =
      (Fin.cons y x : Fin (m+1) → ℝ) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [Fin.cycleRange_symm_zero, Fin.snoc_last, Fin.cons_zero]
  · rw [Fin.cycleRange_symm_succ, Fin.succAbove_last, Fin.snoc_castSucc, Fin.cons_succ]

/-- **Gaudin lemma (abstract)**: for biorthogonal `φ, ψ` and `K(u,v) = Σ_j φ_j(u) ψ_j(v)`,
`y ↦ det[K]_{m+1}(snoc x y)` is integrable with integral `(N - m) det[K]_m(x)`. -/
theorem gaudin_snoc {N m : ℕ} (φ ψ : Fin N → ℝ → ℝ)
    (hint : ∀ a b, Integrable (fun u => φ a u * ψ b u))
    (hδ : ∀ a b, ∫ u, φ a u * ψ b u = if a = b then 1 else 0) (x : Fin m → ℝ) :
    Integrable (fun y => (Matrix.of fun i l => ∑ j, φ j ((Fin.snoc x y : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.snoc x y : Fin (m+1) → ℝ) l)).det) ∧
      ∫ y, (Matrix.of fun i l => ∑ j, φ j ((Fin.snoc x y : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.snoc x y : Fin (m+1) → ℝ) l)).det =
      ((N : ℝ) - m) * (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l)).det := by
  have h : ∀ y, (Matrix.of fun i l => ∑ j, φ j ((Fin.snoc x y : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.snoc x y : Fin (m+1) → ℝ) l)).det =
      (Matrix.of fun i l => ∑ j, φ j ((Fin.cons y x : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.cons y x : Fin (m+1) → ℝ) l)).det := by
    intro y
    rw [← kdet_comp_equiv φ ψ _ (Fin.last m).cycleRange.symm]
    have hk := congrFun (snoc_comp_cycleRange x y)
    simp only [hk]
  simp only [h]
  exact gaudin_cons φ ψ hint hδ x

/-- **Gaudin lemma**, with natural subtraction: for `m + 1 ≤ N`, the integral is `(N - m) det[K]_m(x)`
with natural subtraction. -/
theorem gaudin_snoc_nat {N m : ℕ} (φ ψ : Fin N → ℝ → ℝ)
    (hint : ∀ a b, Integrable (fun u => φ a u * ψ b u))
    (hδ : ∀ a b, ∫ u, φ a u * ψ b u = if a = b then 1 else 0) (hm : m + 1 ≤ N)
    (x : Fin m → ℝ) :
    Integrable (fun y => (Matrix.of fun i l => ∑ j, φ j ((Fin.snoc x y : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.snoc x y : Fin (m+1) → ℝ) l)).det) ∧
      ∫ y, (Matrix.of fun i l => ∑ j, φ j ((Fin.snoc x y : Fin (m+1) → ℝ) i) *
        ψ j ((Fin.snoc x y : Fin (m+1) → ℝ) l)).det =
      ((N - m : ℕ) : ℝ) * (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l)).det := by
  rw [Nat.cast_sub (by omega)]
  exact gaudin_snoc φ ψ hint hδ x

/-- Leibniz expansion of `det[K(z_i, z_l)]` into products of one-variable functions. -/
theorem kdet_leibniz {N M : ℕ} (φ ψ : Fin N → ℝ → ℝ) (z : Fin M → ℝ) :
    (Matrix.of fun i l => ∑ j, φ j (z i) * ψ j (z l)).det =
      ∑ σ : Equiv.Perm (Fin M), ∑ p : Fin M → Fin N, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, (φ (p (σ⁻¹ i)) (z i) * ψ (p i) (z i)) := by
  rw [det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Units.smul_def,
    zsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  congr 1
  rw [← Equiv.prod_comp σ (fun i => φ (p (σ⁻¹ i)) (z i))]
  simp

/-- Every section `y ↦ det[K](append x y)` is integrable when every `φ_a ψ_b` is. -/
theorem integrable_kdet_append {N k n : ℕ} (φ ψ : Fin N → ℝ → ℝ)
    (hint : ∀ a b, Integrable (fun u => φ a u * ψ b u)) (x : Fin k → ℝ) :
    Integrable (fun y : Fin n → ℝ => (Matrix.of fun i l => ∑ j,
      φ j (Fin.append x y i) * ψ j (Fin.append x y l)).det) := by
  simp only [kdet_leibniz]
  refine integrable_finsetSum _ fun σ _ => integrable_finsetSum _ fun p _ => ?_
  refine Integrable.const_mul ?_ _
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  refine Integrable.const_mul ?_ _
  exact Integrable.fintype_prod (μ := fun _ => volume) (fun j => hint _ _)

/-- **Iterated Gaudin lemma**: `∫ det[K]_{k+n}(append x y) dy = (N-k)⋯(N-k-n+1) det[K]_k(x)`. -/
theorem gaudin_append {N k : ℕ} (φ ψ : Fin N → ℝ → ℝ)
    (hint : ∀ a b, Integrable (fun u => φ a u * ψ b u))
    (hδ : ∀ a b, ∫ u, φ a u * ψ b u = if a = b then 1 else 0) (x : Fin k → ℝ) :
    ∀ n : ℕ, k + n ≤ N →
      ∫ y : Fin n → ℝ, (Matrix.of fun i l => ∑ j,
        φ j (Fin.append x y i) * ψ j (Fin.append x y l)).det =
      ((N - k).descFactorial n : ℝ) * (Matrix.of fun i l => ∑ j, φ j (x i) * ψ j (x l)).det := by
  intro n
  induction n with
  | zero =>
    intro _
    have h0 : ∀ y : Fin 0 → ℝ, (Fin.append x y : Fin (k + 0) → ℝ) = x := by
      intro y; ext i; simp [Fin.append_right_nil]
    simp only [h0, integral_const, Nat.descFactorial_zero, Nat.cast_one, one_mul, smul_eq_mul]
    rw [measureReal_def, MeasureTheory.volume_pi, Measure.pi_univ]
    simp
  | succ n ih =>
    intro hn
    set f : (Fin (n + 1) → ℝ) → ℝ := fun y => (Matrix.of fun i l => ∑ j,
        φ j (Fin.append x y i) * ψ j (Fin.append x y l)).det with hf
    have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
    have hfi : Integrable f := integrable_kdet_append φ ψ hint x
    rw [← hmp.integral_comp' f]
    have hfi' := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hfi
    rw [Measure.volume_eq_prod] at hfi' ⊢
    rw [integral_prod_symm (fun p => f ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ)
        (Fin.last n)).symm p)) hfi']
    have hin : ∀ y' : Fin n → ℝ, ∫ a, f ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ)
        (Fin.last n)).symm (a, y')) = ((N : ℝ) - (k + n : ℕ)) * (Matrix.of fun i l => ∑ j,
          φ j (Fin.append x y' i) * ψ j (Fin.append x y' l)).det := by
      intro y'
      simp only [hf, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.insertNth_last', Fin.append_snoc]
      exact (gaudin_snoc φ ψ hint hδ (Fin.append x y')).2
    simp only [hin]
    rw [integral_const_mul, ih (by omega), Nat.descFactorial_succ]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : n ≤ N - k), Nat.cast_sub (by omega : k ≤ N)]
    push_cast
    ring

/-- The Gaudin marginals of the real kernel, from biorthogonality. -/
theorem kernelMarginal_of_biorthogonal (hB : BiorthogonalStatement) :
    KernelMarginalStatement := by
  intro N S hS d hd k hk x
  have hint : ∀ a b, Integrable (fun u => (fun j u => gaussKernel S (d j) u) a u *
      (fun j v => (biorthPoly S d j).eval v) b u) := fun a b => (hB S hS d hd b a).1
  have hδ : ∀ a b, ∫ u, (fun j u => gaussKernel S (d j) u) a u *
      (fun j v => (biorthPoly S d j).eval v) b u = if a = b then 1 else 0 := by
    intro a b
    rw [(hB S hS d hd b a).2]
    simp only [eq_comm]
  have hre : ∀ y : Fin (N - k) → ℝ, kernelMatDet S d (appendCast hk x y) =
      (Matrix.of fun i l => ∑ j, (fun j u => gaussKernel S (d j) u) j (Fin.append x y i) *
        (fun j v => (biorthPoly S d j).eval v) j (Fin.append x y l)).det := by
    intro y
    refine Eq.trans ?_ (kdet_comp_equiv (fun j u => gaussKernel S (d j) u)
      (fun j v => (biorthPoly S d j).eval v) (Fin.append x y)
      (finCongr (by omega : N = k + (N - k))))
    rfl
  simp only [hre]
  refine ⟨integrable_kdet_append _ _ hint x, ?_⟩
  rw [gaudin_append _ _ hint hδ x (N - k) (by omega), Nat.descFactorial_self]
  rfl

/-- `KernelMarginalStatement`, with `biorthogonal_holds`. -/
theorem kernelMarginal_holds : KernelMarginalStatement :=
  kernelMarginal_of_biorthogonal biorthogonal_holds

end BlockBand.Native.Johansson
