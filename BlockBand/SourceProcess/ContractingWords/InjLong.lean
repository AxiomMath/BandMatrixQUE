module

public import BlockBand.SourceProcess.ContractingWords.InjAlg
public import BlockBand.SourceProcess.ContractingWords.LayerInj

/-!
# The injection into a word of length `≥ 2` is `O(W⁻²)`

`newWord_long_sub_le`: for Hermitian letters with `Tr|A_ℓ| ≤ K`, `|c_ℓ| ≤ c₀/W²`, `‖S_σ‖ ≤ 1`,
`W ≥ 1` and `w = x₀ :: x₁ :: u`,
`|newWord A c N D S w - newWord A 0 N D S w| ≤ (|u|+4)Λ^{|u|+5}/W²`,
`Λ = 1 + 3(1+K+c₀)(1+‖N‖+‖D‖)²`. Split `F_x = X_x + Y_x` (`X = N*A_xNS`, `Y = c_xD*DS`):
`Tr F₀F₁Π - Tr X₀X₁Π⁰ = Tr X₀(F₁Π - X₁Π⁰) + Tr Y₀X₁Π + Tr Y₀Y₁Π`; the first two carry a
trace-class letter, the last has two factors `c = O(W⁻²)` against `Tr ≤ 2W‖·‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

theorem long_arith {Γ Λ ε u : ℝ} (hΓ : 1 ≤ Γ) (hΛ : Λ = 1 + 3 * Γ) (hε : 0 ≤ ε) (hu : 0 ≤ u)
    (k : ℕ) (a b c : ℝ) (ha : a ≤ Γ * ((u + 1) * (Γ * ε) * Λ ^ (k + 1)))
    (hb : b ≤ Γ * (Λ ^ k * (Γ * ε))) (hc : c ≤ 2 * (Γ ^ 2 * Λ ^ k) * ε) :
    a + b + c ≤ (u + 4) * Λ ^ (k + 5) * ε := by
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; linarith
  have hΓΛ : Γ ≤ Λ := by rw [hΛ]; linarith
  have p1 : Γ * (Γ * Λ ^ (k + 1)) ≤ Λ ^ (k + 5) := by
    calc Γ * (Γ * Λ ^ (k + 1)) ≤ Λ * (Λ * Λ ^ (k + 1)) := by gcongr
      _ = Λ ^ (k + 3) := by ring
      _ ≤ Λ ^ (k + 5) := pow_le_pow_right₀ hΛ1 (by omega)
  have p2 : Γ * (Λ ^ k * Γ) ≤ Λ ^ (k + 5) := by
    calc Γ * (Λ ^ k * Γ) ≤ Λ * (Λ ^ k * Λ) := by gcongr
      _ = Λ ^ (k + 2) := by ring
      _ ≤ Λ ^ (k + 5) := pow_le_pow_right₀ hΛ1 (by omega)
  have p3 : Γ ^ 2 * Λ ^ k ≤ Λ ^ (k + 5) := by
    calc Γ ^ 2 * Λ ^ k ≤ Λ ^ 2 * Λ ^ k := by gcongr
      _ = Λ ^ (k + 2) := by ring
      _ ≤ Λ ^ (k + 5) := pow_le_pow_right₀ hΛ1 (by omega)
  have e1 : Γ * ((u + 1) * (Γ * ε) * Λ ^ (k + 1)) = (u + 1) * ε * (Γ * (Γ * Λ ^ (k + 1))) := by
    ring
  have e2 : Γ * (Λ ^ k * (Γ * ε)) = ε * (Γ * (Λ ^ k * Γ)) := by ring
  have hue : 0 ≤ (u + 1) * ε := by positivity
  have q1 := mul_le_mul_of_nonneg_left p1 hue
  have q2 := mul_le_mul_of_nonneg_left p2 hε
  have q3 := mul_le_mul_of_nonneg_left p3 (by positivity : (0 : ℝ) ≤ 2 * ε)
  have hA' : a ≤ (u + 1) * ε * Λ ^ (k + 5) := ha.trans (by rw [e1]; exact q1)
  have hB' : b ≤ ε * Λ ^ (k + 5) := hb.trans (by rw [e2]; exact q2)
  have hC' : c ≤ 2 * ε * Λ ^ (k + 5) := hc.trans (by
    rw [show 2 * (Γ ^ 2 * Λ ^ k) * ε = 2 * ε * (Γ ^ 2 * Λ ^ k) by ring]; exact q3)
  calc a + b + c ≤ (u + 1) * ε * Λ ^ (k + 5) + ε * Λ ^ (k + 5) + 2 * ε * Λ ^ (k + 5) := by
        linarith
    _ = (u + 4) * Λ ^ (k + 5) * ε := by ring

theorem long_split {n : Type} [Fintype n] [DecidableEq n] (X0 Y0 X1 Y1 P P0 : Matrix n n ℂ) :
    ((X0 + Y0) * ((X1 + Y1) * P)).trace - (X0 * (X1 * P0)).trace =
      (X0 * ((X1 + Y1) * P - X1 * P0)).trace + (Y0 * (X1 * P)).trace + (Y0 * (Y1 * P)).trace := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
  ring

section Core

variable {α : Type*} (X Y : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {Γ ε : ℝ}

theorem long_prod_le (hΓ : 1 ≤ Γ) (hε1 : ε ≤ 1) (hX : ∀ x, ‖X x‖ ≤ Γ) (hY : ∀ x, ‖Y x‖ ≤ Γ * ε)
    (u : List α) : ‖(u.map fun x => X x + Y x).prod‖ ≤ (1 + 3 * Γ) ^ u.length := by
  refine (norm_list_prod_le _).trans ?_
  rw [List.map_map]
  refine list_prod_le_pow_length u _ (fun _ _ => by simp only [Function.comp_apply]; positivity)
    fun x _ => ?_
  have : Γ * ε ≤ Γ := mul_le_of_le_one_right (by linarith) hε1
  simp only [Function.comp_apply]
  linarith [norm_add_le (X x) (Y x), hX x, hY x]

theorem long_diff_le (hΓ : 1 ≤ Γ) (hε1 : ε ≤ 1) (hX : ∀ x, ‖X x‖ ≤ Γ) (hY : ∀ x, ‖Y x‖ ≤ Γ * ε)
    (hε0 : 0 ≤ ε) (x₁ : α) (u : List α) :
    ‖(X x₁ + Y x₁) * (u.map fun x => X x + Y x).prod - X x₁ * (u.map X).prod‖ ≤
      (u.length + 1) * (Γ * ε) * (1 + 3 * Γ) ^ (u.length + 1) := by
  have h := norm_list_prod_sub_le_mat (x₁ :: u) (fun x => X x + Y x) X
  simp only [List.map_cons, List.prod_cons] at h
  have hP0 : 0 ≤ ((x₁ :: u).map fun x => 1 + ‖X x + Y x‖ + ‖X x‖).prod :=
    List.prod_nonneg fun z hz => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hz; show 0 ≤ 1 + ‖X x + Y x‖ + ‖X x‖; positivity
  simp only [List.map_cons, List.prod_cons] at hP0
  refine h.trans (mul_le_mul ?_ ?_ hP0 (by positivity))
  · have := list_sum_le_length_mul (x₁ :: u) (fun x => ‖X x + Y x - X x‖) (M := Γ * ε)
      fun x _ => by rw [add_sub_cancel_left]; exact hY x
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ] at this ⊢
    linarith
  · have := list_prod_le_pow_length (x₁ :: u) (fun x => 1 + ‖X x + Y x‖ + ‖X x‖)
      (M := 1 + 3 * Γ) (fun _ _ => by positivity) fun x _ => by
        have : Γ * ε ≤ Γ := mul_le_of_le_one_right (by linarith) hε1
        linarith [norm_add_le (X x) (Y x), hX x, hY x]
    simpa using this

/-- **The abstract long-word injection bound.** -/
theorem long_core (hΓ : 1 ≤ Γ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hWε : (W : ℝ) * ε ^ 2 ≤ ε)
    (hX : ∀ x, ‖X x‖ ≤ Γ) (hY : ∀ x, ‖Y x‖ ≤ Γ * ε)
    (hXtr : ∀ x M, ‖(X x * M).trace‖ ≤ Γ * ‖M‖) (x₀ x₁ : α) (u : List α) :
    ‖((x₀ :: x₁ :: u).map fun x => X x + Y x).prod.trace - ((x₀ :: x₁ :: u).map X).prod.trace‖ ≤
      (u.length + 4) * (1 + 3 * Γ) ^ (u.length + 5) * ε := by
  simp only [List.map_cons, List.prod_cons]
  rw [long_split]
  have hPu := long_prod_le X Y hΓ hε1 hX hY u
  have hQ := long_diff_le X Y hΓ hε1 hX hY hε0 x₁ u
  have ha := (hXtr x₀ _).trans (mul_le_mul_of_nonneg_left hQ (by linarith))
  have hb : ‖(Y x₀ * (X x₁ * (u.map fun x => X x + Y x).prod)).trace‖ ≤
      Γ * ((1 + 3 * Γ) ^ u.length * (Γ * ε)) := by
    rw [Matrix.trace_mul_comm (Y x₀), Matrix.mul_assoc]
    refine (hXtr x₁ _).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    exact (norm_mul_le _ _).trans (mul_le_mul hPu (hY x₀) (norm_nonneg _) (by positivity))
  have hc : ‖(Y x₀ * (Y x₁ * (u.map fun x => X x + Y x).prod)).trace‖ ≤
      2 * (Γ ^ 2 * (1 + 3 * Γ) ^ u.length) * ε := by
    refine (norm_trace_le_card _).trans ?_
    have h3 : ‖Y x₀ * (Y x₁ * (u.map fun x => X x + Y x).prod)‖ ≤
        (Γ * ε) * ((Γ * ε) * (1 + 3 * Γ) ^ u.length) :=
      (norm_mul_le _ _).trans (mul_le_mul (hY x₀) ((norm_mul_le _ _).trans
        (mul_le_mul (hY x₁) hPu (norm_nonneg _) (by positivity))) (norm_nonneg _) (by positivity))
    calc 2 * (W : ℝ) * ‖Y x₀ * (Y x₁ * (u.map fun x => X x + Y x).prod)‖ ≤
          2 * W * ((Γ * ε) * ((Γ * ε) * (1 + 3 * Γ) ^ u.length)) := by gcongr
      _ = 2 * (Γ ^ 2 * (1 + 3 * Γ) ^ u.length) * ((W : ℝ) * ε ^ 2) := by ring
      _ ≤ 2 * (Γ ^ 2 * (1 + 3 * Γ) ^ u.length) * ε := by gcongr
  have h1 := norm_add_le
    ((X x₀ * ((X x₁ + Y x₁) * (u.map fun x => X x + Y x).prod - X x₁ * (u.map X).prod)).trace +
      (Y x₀ * (X x₁ * (u.map fun x => X x + Y x).prod)).trace)
    (Y x₀ * (Y x₁ * (u.map fun x => X x + Y x).prod)).trace
  have h2 := norm_add_le
    (X x₀ * ((X x₁ + Y x₁) * (u.map fun x => X x + Y x).prod - X x₁ * (u.map X).prod)).trace
    (Y x₀ * (X x₁ * (u.map fun x => X x + Y x).prod)).trace
  have := long_arith hΓ rfl hε0 (Nat.cast_nonneg _) u.length _ _ _ ha hb hc
  linarith

end Core

theorem inj_consts {n d K c₀ : ℝ} (hn : 0 ≤ n) (hd : 0 ≤ d) (hK : 0 ≤ K) (hc₀ : 0 ≤ c₀) :
    1 ≤ (1 + K + c₀) * (1 + n + d) ^ 2 ∧ K * (1 + n + d) ^ 2 ≤ (1 + K + c₀) * (1 + n + d) ^ 2 ∧
      c₀ * (1 + n + d) ^ 2 ≤ (1 + K + c₀) * (1 + n + d) ^ 2 ∧ n ≤ 1 + n + d ∧ d ≤ 1 + n + d := by
  have hG2 : 1 ≤ (1 + n + d) ^ 2 := one_le_pow₀ (by linarith)
  exact ⟨one_le_mul_of_one_le_of_one_le (by linarith) hG2,
    mul_le_mul_of_nonneg_right (by linarith) (by positivity),
    mul_le_mul_of_nonneg_right (by linarith) (by positivity), by linarith, by linarith⟩

theorem w_eps (hW : 1 ≤ W) :
    0 ≤ ((W : ℝ) ^ 2)⁻¹ ∧ ((W : ℝ) ^ 2)⁻¹ ≤ 1 ∧ (W : ℝ) * (((W : ℝ) ^ 2)⁻¹) ^ 2 ≤ ((W : ℝ) ^ 2)⁻¹ := by
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hε0 : 0 ≤ ((W : ℝ) ^ 2)⁻¹ := by positivity
  have e : (W : ℝ) * ((W : ℝ) ^ 2)⁻¹ = (W : ℝ)⁻¹ := by field_simp
  have h1 : (W : ℝ) * ((W : ℝ) ^ 2)⁻¹ ≤ 1 := e ▸ inv_le_one_of_one_le₀ hWr
  refine ⟨hε0, inv_le_one_of_one_le₀ (one_le_pow₀ hWr), ?_⟩
  calc (W : ℝ) * (((W : ℝ) ^ 2)⁻¹) ^ 2 = ((W : ℝ) * ((W : ℝ) ^ 2)⁻¹) * ((W : ℝ) ^ 2)⁻¹ := by ring
    _ ≤ 1 * ((W : ℝ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h1 hε0
    _ = _ := one_mul _

theorem normX_le {A N S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hA : A.IsHermitian)
    {K G : ℝ} (hAK : nuclearNorm A ≤ K) (hS : ‖S‖ ≤ 1) (hNG : ‖N‖ ≤ G) :
    ‖Nᴴ * A * N * S‖ ≤ K * G ^ 2 := by
  have e1 := norm_mul_le (Nᴴ * A * N) S
  have e2 := norm_mul_le (Nᴴ * A) N
  have e3 := norm_mul_le Nᴴ A
  rw [Matrix.l2_opNorm_conjTranspose] at e3
  have e4 := (norm_le_nuclearNorm hA).trans hAK
  have hN := norm_nonneg N; have := norm_nonneg A
  have hK0 : 0 ≤ K := this.trans e4
  have hG0 : 0 ≤ G := hN.trans hNG
  calc ‖Nᴴ * A * N * S‖ ≤ ‖N‖ * ‖A‖ * ‖N‖ * ‖S‖ :=
        e1.trans (mul_le_mul (e2.trans (mul_le_mul_of_nonneg_right e3 hN)) le_rfl
          (norm_nonneg _) (by positivity))
    _ ≤ G * K * G * 1 := by gcongr
    _ = K * G ^ 2 := by ring

theorem normY_le (r : ℝ) (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ) {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hS : ‖S‖ ≤ 1) {G : ℝ} (hDG : ‖D‖ ≤ G) : ‖(r : ℂ) • (Dᴴ * D) * S‖ ≤ |r| * G ^ 2 := by
  have e1 := norm_mul_le ((r : ℂ) • (Dᴴ * D)) S
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs] at e1
  have hDD : ‖Dᴴ * D‖ ≤ G ^ 2 := by
    calc ‖Dᴴ * D‖ ≤ ‖Dᴴ‖ * ‖D‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖D‖ * ‖D‖ := by rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ G * G := mul_le_mul hDG hDG (norm_nonneg _) ((norm_nonneg _).trans hDG)
      _ = G ^ 2 := by ring
  calc ‖(r : ℂ) • (Dᴴ * D) * S‖ ≤ |r| * ‖Dᴴ * D‖ * ‖S‖ := e1
    _ ≤ |r| * G ^ 2 * 1 := by gcongr
    _ = |r| * G ^ 2 := mul_one _

/-- **The injection into a word of length `≥ 2`.** -/
theorem newWord_long_sub_le (hW : 1 ≤ W)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (c : TraceLetter nT nI → ℝ)
    (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (S : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {K c₀ : ℝ} (hK : 0 ≤ K)
    (hc₀ : 0 ≤ c₀) (hA : ∀ ℓ, (A ℓ).IsHermitian) (hAK : ∀ ℓ, nuclearNorm (A ℓ) ≤ K)
    (hc : ∀ ℓ, |c ℓ| ≤ c₀ / (W : ℝ) ^ 2) (hS : ∀ σ, ‖S σ‖ ≤ 1)
    (x₀ x₁ : TraceLetter nT nI × Separator) (u : TraceWord nT nI) :
    ‖newWord A c N D S (x₀ :: x₁ :: u) - newWord A (fun _ => 0) N D S (x₀ :: x₁ :: u)‖ ≤
      (u.length + 4) * (1 + 3 * ((1 + K + c₀) * (1 + ‖N‖ + ‖D‖) ^ 2)) ^ (u.length + 5) /
        (W : ℝ) ^ 2 := by
  obtain ⟨hΓ, hKΓ, hcΓ, hNG, hDG⟩ := inj_consts (norm_nonneg N) (norm_nonneg D) hK hc₀
  obtain ⟨hε0, hε1, hWε⟩ := w_eps hW
  have hX : ∀ x : TraceLetter nT nI × Separator, ‖Nᴴ * A x.1 * N * S x.2‖ ≤
      (1 + K + c₀) * (1 + ‖N‖ + ‖D‖) ^ 2 := fun x =>
    (normX_le (hA x.1) (hAK x.1) (hS x.2) hNG).trans hKΓ
  have hY : ∀ x : TraceLetter nT nI × Separator, ‖(c x.1 : ℂ) • (Dᴴ * D) * S x.2‖ ≤
      (1 + K + c₀) * (1 + ‖N‖ + ‖D‖) ^ 2 * ((W : ℝ) ^ 2)⁻¹ := fun x => by
    refine (normY_le (c x.1) D (hS x.2) hDG).trans ?_
    have h1 : |c x.1| ≤ c₀ * ((W : ℝ) ^ 2)⁻¹ := (hc x.1).trans_eq (div_eq_mul_inv _ _)
    calc |c x.1| * (1 + ‖N‖ + ‖D‖) ^ 2 ≤ c₀ * ((W : ℝ) ^ 2)⁻¹ * (1 + ‖N‖ + ‖D‖) ^ 2 := by gcongr
      _ = (c₀ * (1 + ‖N‖ + ‖D‖) ^ 2) * ((W : ℝ) ^ 2)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcΓ hε0
  have hXtr : ∀ (x : TraceLetter nT nI × Separator) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      ‖(Nᴴ * A x.1 * N * S x.2 * M).trace‖ ≤ (1 + K + c₀) * (1 + ‖N‖ + ‖D‖) ^ 2 * ‖M‖ :=
    fun x M => by
      refine (norm_trace_letter_le (hA x.1) N (S x.2) M).trans ?_
      have := hS x.2; have := norm_nonneg M; have := norm_nonneg N
      calc nuclearNorm (A x.1) * (‖N‖ * ‖S x.2‖ * ‖M‖ * ‖N‖) ≤
            K * ((1 + ‖N‖ + ‖D‖) * 1 * ‖M‖ * (1 + ‖N‖ + ‖D‖)) := by gcongr; exact hAK _
        _ = (K * (1 + ‖N‖ + ‖D‖) ^ 2) * ‖M‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hKΓ (norm_nonneg _)
  set X : TraceLetter nT nI × Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    fun x => Nᴴ * A x.1 * N * S x.2 with hXdef
  set Y : TraceLetter nT nI × Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    fun x => (c x.1 : ℂ) • (Dᴴ * D) * S x.2 with hYdef
  set Γ := (1 + K + c₀) * (1 + ‖N‖ + ‖D‖) ^ 2 with hΓdef
  set ε := ((W : ℝ) ^ 2)⁻¹ with hεdef
  have h := long_core (W := W) (Γ := Γ) (ε := ε) X Y hΓ hε0 hε1 hWε hX hY hXtr x₀ x₁ u
  rw [div_eq_mul_inv]
  have e1 : newWord A c N D S (x₀ :: x₁ :: u) = ((x₀ :: x₁ :: u).map fun x => X x + Y x).prod.trace :=
    congrArg Matrix.trace (congrArg List.prod (List.map_congr_left fun x _ => Matrix.add_mul _ _ _))
  have e0 : newWord A (fun _ => 0) N D S (x₀ :: x₁ :: u) = ((x₀ :: x₁ :: u).map X).prod.trace :=
    congrArg Matrix.trace (congrArg List.prod (List.map_congr_left fun x _ => by
      simp only [Complex.ofReal_zero, zero_smul, add_zero, hXdef]))
  rw [e1, e0]
  exact h

end BlockBand.SourceProcess.ContractingWords
