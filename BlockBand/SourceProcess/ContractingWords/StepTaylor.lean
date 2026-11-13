module

public import BlockBand.SourceProcess.ContractingWords.Taylor

/-!
# The Taylor expansion between two evaluation points

For a polynomial `Φ` with `vars Φ ⊆ S`, two
points `x, x'` with `|x_w| + |x'_w| ≤ M` on `S` (`M ≥ 1`), and `Δ_w = x'_w - x_w`:

* `taylorRem` `R = Φ(x') - Φ(x) - Σ_{w∈S}∂_wΦ(x)Δ_w - ½Σ_{w,v∈S}∂_v∂_wΦ(x)Δ_wΔ_v`;
* `norm_taylorRem_le`: `|R| ≤ CM^N(Σ_{w∈S}|Δ_w|)³` (the constants of `taylor_bound`);
* `norm_eval_le_of_tay`: `|Ψ(x)| ≤ CM^N` for `vars Ψ ⊆ S`.
Both through the truncations `x̃ = x·1_S`, `h̃ = Δ·1_S` (`eval_congr_vars`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MvPolynomial

variable {σ : Type*} [DecidableEq σ]

/-- The cubic remainder between `x` and `x'`. -/
def taylorRem (S : Finset σ) (Φ : MvPolynomial σ ℂ) (x x' : σ → ℂ) : ℂ :=
  eval x' Φ - eval x Φ - ∑ w ∈ S, eval x (pderiv w Φ) * (x' w - x w) -
    (1 / 2 : ℂ) * ∑ w ∈ S, ∑ v ∈ S,
      eval x (pderiv v (pderiv w Φ)) * ((x' w - x w) * (x' v - x v))

/-- `x·1_S`. -/
def truncPt (S : Finset σ) (x : σ → ℂ) : σ → ℂ := fun w => if w ∈ S then x w else 0

theorem eval_truncPt {S : Finset σ} {Ψ : MvPolynomial σ ℂ} (h : Ψ.vars ⊆ S) (x : σ → ℂ) :
    eval (truncPt S x) Ψ = eval x Ψ :=
  eval_congr_vars fun w hw => by simp [truncPt, h hw]

theorem norm_truncPt_le {S : Finset σ} {x : σ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ w ∈ S, ‖x w‖ ≤ M) (w : σ) : ‖truncPt S x w‖ ≤ M := by
  unfold truncPt; split_ifs with h
  · exact hb w h
  · simpa using hM

theorem norm_taylorRem_le {S : Finset σ} {Φ : MvPolynomial σ ℂ} (hS : Φ.vars ⊆ S) {C : ℝ}
    {N : ℕ} (hT : TayBound S Φ C N) {x x' : σ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hb : ∀ w ∈ S, ‖x w‖ + ‖x' w‖ ≤ M) :
    ‖taylorRem S Φ x x'‖ ≤ C * M ^ N * (∑ w ∈ S, ‖x' w - x w‖) ^ 3 := by
  set h : σ → ℂ := truncPt S fun w => x' w - x w
  have hx : ∀ w ∈ S, ‖x w‖ ≤ M := fun w hw => by
    have := norm_nonneg (x' w); linarith [hb w hw]
  have hh : ∀ w ∈ S, ‖x' w - x w‖ ≤ M := fun w hw =>
    (norm_sub_le _ _).trans (by linarith [hb w hw])
  have hS0 : ∀ w ∉ S, h w = 0 := fun w hw => by simp [h, truncPt, hw]
  obtain ⟨-, -, -, h4⟩ := hT M hM (truncPt S x) h (norm_truncPt_le (by linarith) hx)
    (norm_truncPt_le (by linarith) hh) hS0
  have hd1 : ∀ w, (pderiv w Φ).vars ⊆ S := fun w => (vars_pderiv_subset Φ w).trans hS
  have hd2 : ∀ w v, (pderiv v (pderiv w Φ)).vars ⊆ S := fun w v =>
    (vars_pderiv_subset _ v).trans (hd1 w)
  have hsum : ∀ w ∈ S, h w = x' w - x w := fun w hw => by simp [h, truncPt, hw]
  have e : tayR S Φ (truncPt S x) h = taylorRem S Φ x x' := by
    have e0 : eval (truncPt S x + h) Φ = eval x' Φ := eval_congr_vars fun w hw => by
      simp [h, truncPt, hS hw]
    have s1 : ∑ w ∈ S, eval (truncPt S x) (pderiv w Φ) * h w =
        ∑ w ∈ S, eval x (pderiv w Φ) * (x' w - x w) :=
      Finset.sum_congr rfl fun w hw => by rw [eval_truncPt (hd1 w), hsum w hw]
    have s2 : ∑ w ∈ S, ∑ v ∈ S, eval (truncPt S x) (pderiv v (pderiv w Φ)) * (h w * h v) =
        ∑ w ∈ S, ∑ v ∈ S, eval x (pderiv v (pderiv w Φ)) * ((x' w - x w) * (x' v - x v)) :=
      Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun v hv => by
        rw [eval_truncPt (hd2 w v), hsum w hw, hsum v hv]
    simp only [tayR, tay1, tay2, taylorRem, e0, eval_truncPt hS, s1, s2]
  have hη : ∑ w ∈ S, ‖h w‖ = ∑ w ∈ S, ‖x' w - x w‖ :=
    Finset.sum_congr rfl fun w hw => by rw [hsum w hw]
  rw [← e, ← hη]; exact h4

theorem norm_eval_le_of_tay {S : Finset σ} {Ψ : MvPolynomial σ ℂ} (hS : Ψ.vars ⊆ S) {C : ℝ}
    {N : ℕ} (hT : TayBound S Ψ C N) {x : σ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hb : ∀ w ∈ S, ‖x w‖ ≤ M) : ‖eval x Ψ‖ ≤ C * M ^ N := by
  have := (hT M hM (truncPt S x) 0 (norm_truncPt_le (by linarith) hb)
    (fun _ => by simp; linarith) (fun _ _ => rfl)).1
  rwa [eval_truncPt hS] at this

theorem arith_sq {P η s M a b : ℝ} (hη : 0 ≤ η) (hs : 0 ≤ s) (hM : 1 ≤ M)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ P * η ^ 2 * (1 + s * M))
    (hb : b ≤ P * η * (2 + s * M * (1 + s * M))) :
    a * b ≤ 3 * P ^ 2 * (1 + s) ^ 3 * M ^ 3 * η ^ 3 := by
  have hM0 : 0 ≤ M := by linarith
  have hsM : 0 ≤ s * M := by positivity
  have h1 : 1 + s * M ≤ (1 + s) * M := by nlinarith
  have h2 : 2 + s * M * (1 + s * M) ≤ 3 * (1 + s) ^ 2 * M ^ 2 := by
    have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
    have : s * M ≤ s * M ^ 2 := by nlinarith
    nlinarith [sq_nonneg s, mul_nonneg hs hs]
  have hab : a * b ≤ (P * η ^ 2 * (1 + s * M)) * (P * η * (2 + s * M * (1 + s * M))) :=
    mul_le_mul ha hb hb0 (ha0.trans ha)
  have hc : (1 + s * M) * (2 + s * M * (1 + s * M)) ≤ ((1 + s) * M) * (3 * (1 + s) ^ 2 * M ^ 2) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have hP2 : 0 ≤ P ^ 2 * η ^ 3 := by positivity
  calc a * b ≤ (P * η ^ 2 * (1 + s * M)) * (P * η * (2 + s * M * (1 + s * M))) := hab
    _ = P ^ 2 * η ^ 3 * ((1 + s * M) * (2 + s * M * (1 + s * M))) := by ring
    _ ≤ P ^ 2 * η ^ 3 * (((1 + s) * M) * (3 * (1 + s) ^ 2 * M ^ 2)) :=
        mul_le_mul_of_nonneg_left hc hP2
    _ = _ := by ring

/-- **The squared increment**: `|(ΔΦ)² - (Σ_w∂_wΦ Δ_w)²| ≤ 3C²(1+|S|)³M^{2N+3}(Σ|Δ_w|)³`. -/
theorem norm_sqRem_le {S : Finset σ} {Φ : MvPolynomial σ ℂ} (hS : Φ.vars ⊆ S) {C : ℝ}
    {N : ℕ} (hC : 0 ≤ C) (hT : TayBound S Φ C N) {x x' : σ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hb : ∀ w ∈ S, ‖x w‖ + ‖x' w‖ ≤ M) :
    ‖(eval x' Φ - eval x Φ) ^ 2 - (∑ w ∈ S, eval x (pderiv w Φ) * (x' w - x w)) ^ 2‖ ≤
      3 * C ^ 2 * (1 + S.card) ^ 3 * M ^ (2 * N + 3) * (∑ w ∈ S, ‖x' w - x w‖) ^ 3 := by
  set h : σ → ℂ := truncPt S fun w => x' w - x w
  have hx : ∀ w ∈ S, ‖x w‖ ≤ M := fun w hw => by
    have := norm_nonneg (x' w); linarith [hb w hw]
  have hh : ∀ w ∈ S, ‖x' w - x w‖ ≤ M := fun w hw =>
    (norm_sub_le _ _).trans (by linarith [hb w hw])
  have hS0 : ∀ w ∉ S, h w = 0 := fun w hw => by simp [h, truncPt, hw]
  obtain ⟨-, h2, h3, h4⟩ := hT M hM (truncPt S x) h (norm_truncPt_le (by linarith) hx)
    (norm_truncPt_le (by linarith) hh) hS0
  have hd1 : ∀ w, (pderiv w Φ).vars ⊆ S := fun w => (vars_pderiv_subset Φ w).trans hS
  have hd2 : ∀ w v, (pderiv v (pderiv w Φ)).vars ⊆ S := fun w v =>
    (vars_pderiv_subset _ v).trans (hd1 w)
  have hsum : ∀ w ∈ S, h w = x' w - x w := fun w hw => by simp [h, truncPt, hw]
  have e0 : eval (truncPt S x + h) Φ = eval x' Φ := eval_congr_vars fun w hw => by
    simp [h, truncPt, hS hw]
  have s1 : tay1 S Φ (truncPt S x) h = ∑ w ∈ S, eval x (pderiv w Φ) * (x' w - x w) :=
    Finset.sum_congr rfl fun w hw => by rw [eval_truncPt (hd1 w), hsum w hw]
  have hη : ∑ w ∈ S, ‖h w‖ = ∑ w ∈ S, ‖x' w - x w‖ :=
    Finset.sum_congr rfl fun w hw => by rw [hsum w hw]
  set D1 := tay1 S Φ (truncPt S x) h
  set D2 := tay2 S Φ (truncPt S x) h
  set R := tayR S Φ (truncPt S x) h
  set η := ∑ w ∈ S, ‖h w‖
  have hF : eval x' Φ - eval x Φ = D1 + (1 / 2 : ℂ) * D2 + R := by
    simp only [R, tayR, e0, eval_truncPt hS]; ring
  rw [hF, ← s1, ← hη]
  have hM0 : 0 ≤ M := by linarith
  have hη0 : 0 ≤ η := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hηs : η ≤ S.card * M := by
    have := Finset.sum_le_sum fun w hw => (show ‖h w‖ ≤ M from by rw [hsum w hw]; exact hh w hw)
    simpa [Finset.sum_const, nsmul_eq_mul, η] using this
  set P := C * M ^ N
  have hP : 0 ≤ P := by positivity
  have e : (D1 + 1 / 2 * D2 + R) ^ 2 - D1 ^ 2 =
      ((1 / 2 : ℂ) * D2 + R) * (2 * D1 + (1 / 2 * D2 + R)) := by
    ring
  rw [e, norm_mul]
  have hH : ‖(1 / 2 : ℂ) * D2 + R‖ ≤ P * η ^ 2 * (1 + S.card * M) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have : P * η ^ 3 ≤ P * η ^ 2 * (S.card * M) := by
      have e3 : P * η ^ 3 = P * η ^ 2 * η := by ring
      rw [e3]
      exact mul_le_mul_of_nonneg_left hηs (by positivity)
    nlinarith [mul_nonneg hP (sq_nonneg η)]
  have hK : ‖2 * D1 + ((1 / 2 : ℂ) * D2 + R)‖ ≤ P * η * (2 + S.card * M * (1 + S.card * M)) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_ofNat]
    have : P * η ^ 2 * (1 + S.card * M) ≤ P * η * (S.card * M * (1 + S.card * M)) := by
      have hsM : 0 ≤ 1 + (S.card : ℝ) * M := by positivity
      calc P * η ^ 2 * (1 + S.card * M) = P * η * η * (1 + S.card * M) := by ring
        _ ≤ P * η * (S.card * M) * (1 + S.card * M) := by
            gcongr
        _ = _ := by ring
    nlinarith [mul_nonneg hP hη0]
  have := arith_sq hη0 (Nat.cast_nonneg S.card) hM (norm_nonneg _) (norm_nonneg _) hH hK
  calc ‖(1 / 2 : ℂ) * D2 + R‖ * ‖2 * D1 + ((1 / 2 : ℂ) * D2 + R)‖ ≤
      3 * P ^ 2 * (1 + S.card) ^ 3 * M ^ 3 * η ^ 3 := this
    _ = _ := by simp only [P]; ring

end BlockBand.SourceProcess.ContractingWords
