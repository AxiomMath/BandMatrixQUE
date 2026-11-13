module

public import BlockBand.SourceProcess.ContractingWords.LayerWord
public import BlockBand.SourceProcess.FullSource.Birth

/-!
# The interval injection costs `O(W⁻¹)`

`newProd_sub_core_le`: for Hermitian letters with `Tr|A_ℓ| ≤ K`, injection weights
`|c_ℓ| ≤ c₀/W²` and separators of norm at most `1`, a product of new words differs from the
transported product without injection by `O(d²/W)`, with a constant polynomial in
`1 + ‖N‖ + ‖D‖`. The bound is deterministic.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance BlockBand.SourceProcess.FullSource
open scoped Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

theorem list_sum_le_length_mul {α : Type*} (L : List α) (f : α → ℝ) {M : ℝ}
    (h : ∀ t ∈ L, f t ≤ M) : (L.map f).sum ≤ L.length * M := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    have := ih fun u hu => h u (List.mem_cons_of_mem _ hu)
    have := h t (List.mem_cons_self ..)
    linarith

theorem list_prod_le_pow_length {α : Type*} (L : List α) (f : α → ℝ) {M : ℝ}
    (h0 : ∀ t ∈ L, 0 ≤ f t) (h : ∀ t ∈ L, f t ≤ M) : (L.map f).prod ≤ M ^ L.length := by
  have := list_prod_le_of_le L f (fun _ => M) h0 h
  simpa [List.map_const', List.prod_replicate] using this

theorem length_le_productDegree {Zs : List (TraceWord nT nI)} (hZ : IsAdmittedProduct Zs) :
    Zs.length ≤ productDegree Zs := by
  induction Zs with
  | nil => simp
  | cons w Zs ih =>
    have hw : 1 ≤ w.length := List.length_pos_iff.mpr (hZ w (List.mem_cons_self ..))
    have := ih fun v hv => hZ v (List.mem_cons_of_mem _ hv)
    simp only [productDegree, List.map_cons, List.sum_cons, List.length_cons] at this ⊢
    omega

theorem length_le_of_mem_degree {Zs : List (TraceWord nT nI)} {w : TraceWord nT nI}
    (hw : w ∈ Zs) : w.length ≤ productDegree Zs := by
  simp only [productDegree]
  exact List.le_sum_of_mem (List.mem_map_of_mem hw)

/-- `|Tr Π(A_{x₁}T_{x₂})| ≤ Π(Tr|A|... )`: the crude word bound through the first letter. -/
theorem norm_matWord_le (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {K ρ : ℝ}
    (hA : ∀ ℓ, (A ℓ).IsHermitian) (hAK : ∀ ℓ, nuclearNorm (A ℓ) ≤ K) (hK : 0 ≤ K)
    (hT : ∀ σ, K * ‖T σ‖ + 1 ≤ ρ) (w : TraceWord nT nI) (hw : w ≠ []) :
    ‖matWord T (letWord A w)‖ ≤ ρ ^ w.length := by
  obtain ⟨x, L, rfl⟩ := List.exists_cons_of_ne_nil hw
  have hρ1 : 1 ≤ ρ := by have := hT .id; nlinarith [norm_nonneg (T .id)]
  simp only [matWord, letWord, List.map_cons, List.map_map, List.prod_cons, List.length_cons]
  rw [Matrix.mul_assoc]
  refine (norm_trace_herm_mul_le (hA x.1) _).trans ?_
  have hP : ‖(L.map ((fun x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Separator =>
      x.1 * T x.2) ∘ fun x => (A x.1, x.2))).prod‖ ≤ ρ ^ L.length := by
    refine (norm_list_prod_le _).trans ?_
    rw [List.map_map]
    refine list_prod_le_pow_length L _ (fun _ _ => by simp only [Function.comp_apply]; positivity)
      fun t _ => ?_
    simp only [Function.comp_apply]
    have h1 := norm_mul_le (A t.1) (T t.2)
    have h2 := (norm_le_nuclearNorm (hA t.1)).trans (hAK t.1)
    have := hT t.2
    nlinarith [norm_nonneg (T t.2), norm_nonneg (A t.1)]
  have h3 := norm_mul_le (T x.2) (L.map ((fun x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
    Separator => x.1 * T x.2) ∘ fun x => (A x.1, x.2))).prod
  have h4 := hT x.2
  have hn := nuclearNorm_nonneg (A x.1)
  calc nuclearNorm (A x.1) * ‖T x.2 * (L.map ((fun x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Separator => x.1 * T x.2) ∘ fun x => (A x.1, x.2))).prod‖ ≤
        K * (‖T x.2‖ * ρ ^ L.length) := by
        refine mul_le_mul (hAK x.1) (h3.trans ?_) (norm_nonneg _) hK
        exact mul_le_mul_of_nonneg_left hP (norm_nonneg _)
    _ ≤ ρ * ρ ^ L.length := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ρ ^ (L.length + 1) := by ring

/-- **The injection, a product of words.** -/
theorem newProd_sub_core_le (hW : 1 ≤ W)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (c : TraceLetter nT nI → ℝ)
    (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (S : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {K c₀ : ℝ} (hK : 0 ≤ K)
    (hc₀ : 0 ≤ c₀) (hA : ∀ ℓ, (A ℓ).IsHermitian) (hAK : ∀ ℓ, nuclearNorm (A ℓ) ≤ K)
    (hc : ∀ ℓ, |c ℓ| ≤ c₀ / (W : ℝ) ^ 2) (hS : ∀ σ, ‖S σ‖ ≤ 1) {d : ℕ}
    (Zs : List (TraceWord nT nI)) (hZ : IsAdmittedProduct Zs) (hd : productDegree Zs ≤ d) :
    ‖newProd A c N D S Zs - coreProd A (fun σ => N * S σ * Nᴴ) Zs‖ ≤
      d * d / W * (3 * (1 + K + c₀) * (1 + ‖N‖ + ‖D‖) ^ 2) ^ (d + 1) *
        ((3 + d) * (3 * (1 + K + c₀) * (1 + ‖N‖ + ‖D‖) ^ 2) ^ (d + 1)) ^ d := by
  set G := 1 + ‖N‖ + ‖D‖
  set ρ := 3 * (1 + K + c₀) * G ^ 2
  have hN := norm_nonneg N
  have hD := norm_nonneg D
  have hG1 : 1 ≤ G := by simp only [G]; linarith
  have hG2 : 1 ≤ G ^ 2 := one_le_pow₀ hG1
  have hρ1 : 1 ≤ ρ := by simp only [ρ]; nlinarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hNG : ‖N‖ ≤ G := by simp only [G]; linarith
  have hDG : ‖D‖ ≤ G := by simp only [G]; linarith
  set T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fun σ => N * S σ * Nᴴ
  have hT : ∀ σ, ‖T σ‖ ≤ G ^ 2 := fun σ => by
    have h1 := norm_mul_le (N * S σ) Nᴴ
    have h2 := norm_mul_le N (S σ)
    rw [Matrix.l2_opNorm_conjTranspose] at h1
    have := hS σ
    calc ‖T σ‖ ≤ ‖N‖ * ‖S σ‖ * ‖N‖ := h1.trans (mul_le_mul_of_nonneg_right h2 hN)
      _ ≤ G * 1 * G := by gcongr
      _ = G ^ 2 := by ring
  have hKT : ∀ σ, K * ‖T σ‖ + 1 ≤ ρ := fun σ => by
    have := hT σ
    have : K * ‖T σ‖ ≤ K * G ^ 2 := mul_le_mul_of_nonneg_left this hK
    simp only [ρ]; nlinarith
  have hDD : ‖Dᴴ * D‖ ≤ G ^ 2 := by
    have := Matrix.l2_opNorm_mul Dᴴ D
    rw [Matrix.l2_opNorm_conjTranspose] at this
    nlinarith
  have htr : (Dᴴ * D).trace.re ≤ W * G ^ 2 := by
    calc (Dᴴ * D).trace.re ≤ (W : ℝ) * ‖D‖ ^ 2 := by simpa using re_trace_le_card D
      _ ≤ W * G ^ 2 := by gcongr
  have hcG : ∀ ℓ, |c ℓ| * ‖Dᴴ * D‖ ≤ c₀ * G ^ 2 := fun ℓ => by
    have h1 : |c ℓ| ≤ c₀ := (hc ℓ).trans (div_le_self hc₀ (by nlinarith))
    exact mul_le_mul h1 hDD (norm_nonneg _) hc₀
  -- one word
  have hword : ∀ w ∈ Zs, ‖newWord A c N D S w - matWord T (letWord A w)‖ ≤ d / W * ρ ^ (d + 1) ∧
      ‖matWord T (letWord A w)‖ ≤ ρ ^ d := fun w hw => by
    have hwl : w.length ≤ d := (length_le_of_mem_degree hw).trans hd
    have hb := norm_matWord_le A T hA hAK hK hKT w (hZ w hw)
    refine ⟨?_, hb.trans (pow_le_pow_right₀ hρ1 hwl)⟩
    have h := newWord_sub_le A N D S c hS w
    rw [newWord_zero] at h
    refine h.trans ?_
    have hsum : (w.map fun x => |c x.1|).sum ≤ w.length * (c₀ / (W : ℝ) ^ 2) :=
      list_sum_le_length_mul w _ fun x _ => hc x.1
    have hprod : (w.map fun x => 1 + (‖Nᴴ * A x.1 * N‖ + |c x.1| * ‖Dᴴ * D‖) * 1).prod ≤
        ρ ^ w.length := by
      refine list_prod_le_pow_length w _ (fun _ _ => by positivity) fun x _ => ?_
      have h1 : ‖Nᴴ * A x.1 * N‖ ≤ K * G ^ 2 := by
        have e1 := norm_mul_le (Nᴴ * A x.1) N
        have e2 := norm_mul_le Nᴴ (A x.1)
        rw [Matrix.l2_opNorm_conjTranspose] at e2
        have e3 := (norm_le_nuclearNorm (hA x.1)).trans (hAK x.1)
        calc ‖Nᴴ * A x.1 * N‖ ≤ ‖N‖ * ‖A x.1‖ * ‖N‖ :=
              e1.trans (mul_le_mul_of_nonneg_right e2 hN)
          _ ≤ G * K * G := by gcongr
          _ = K * G ^ 2 := by ring
      have := hcG x.1
      simp only [ρ]; nlinarith
    have hl : (w.length : ℝ) ≤ d := by exact_mod_cast hwl
    have hsum0 : 0 ≤ (w.map fun x => |c x.1|).sum := List.sum_nonneg fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _
    calc (w.map fun x => |c x.1|).sum * ((Dᴴ * D).trace.re * 1) *
          (w.map fun x => 1 + (‖Nᴴ * A x.1 * N‖ + |c x.1| * ‖Dᴴ * D‖) * 1).prod ≤
          (d * (c₀ / (W : ℝ) ^ 2)) * (W * G ^ 2) * ρ ^ d := by
          refine mul_le_mul (mul_le_mul ?_ (by linarith) (by simpa using trace_factor_re_nonneg D)
            (by positivity)) (hprod.trans (pow_le_pow_right₀ hρ1 hwl)) (List.prod_nonneg
              fun x hx => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; positivity) (by positivity)
          exact hsum.trans (mul_le_mul_of_nonneg_right hl (by positivity))
      _ = d / W * (c₀ * G ^ 2) * ρ ^ d := by field_simp
      _ ≤ d / W * ρ * ρ ^ d := by
          gcongr; simp only [ρ]; nlinarith
      _ = d / W * ρ ^ (d + 1) := by ring
  -- the product
  have hlen : (Zs.length : ℝ) ≤ d := by exact_mod_cast (length_le_productDegree hZ).trans hd
  have hdW : (d : ℝ) / W ≤ d := div_le_self (Nat.cast_nonneg d) hW1
  have key := norm_list_prod_sub_le Zs (newWord A c N D S) fun w => matWord T (letWord A w)
  simp only [newProd, coreProd]
  refine key.trans (mul_le_mul ?_ ?_ (List.prod_nonneg fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; positivity) (by positivity))
  · calc (Zs.map fun x => ‖newWord A c N D S x - matWord T (letWord A x)‖).sum ≤
          Zs.length * (d / W * ρ ^ (d + 1)) :=
          list_sum_le_length_mul Zs _ fun w hw => (hword w hw).1
      _ ≤ d * (d / W * ρ ^ (d + 1)) := mul_le_mul_of_nonneg_right hlen (by positivity)
      _ = d * d / W * ρ ^ (d + 1) := by ring
  · calc (Zs.map fun x => 1 + ‖newWord A c N D S x‖ + ‖matWord T (letWord A x)‖).prod ≤
          ((3 + d) * ρ ^ (d + 1)) ^ Zs.length := by
          refine list_prod_le_pow_length Zs _ (fun _ _ => by positivity) fun w hw => ?_
          obtain ⟨h1, h2⟩ := hword w hw
          have h3 : ‖newWord A c N D S w‖ ≤ d / W * ρ ^ (d + 1) + ρ ^ d := by
            have := norm_sub_norm_le (newWord A c N D S w) (matWord T (letWord A w))
            linarith
          have h4 : ρ ^ d ≤ ρ ^ (d + 1) := pow_le_pow_right₀ hρ1 (Nat.le_succ d)
          have h5 : 1 ≤ ρ ^ (d + 1) := one_le_pow₀ hρ1
          nlinarith [mul_le_mul_of_nonneg_right hdW (by positivity : (0 : ℝ) ≤ ρ ^ (d + 1))]
      _ ≤ ((3 + d) * ρ ^ (d + 1)) ^ d := by
          refine pow_le_pow_right₀ ?_ ((length_le_productDegree hZ).trans hd)
          have : (1 : ℝ) ≤ 3 + d := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
          nlinarith [one_le_pow₀ (n := d + 1) hρ1]

end BlockBand.SourceProcess.ContractingWords
