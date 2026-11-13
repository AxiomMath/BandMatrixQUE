module

public import BlockBand.Endpoints.Clock.DetClockTaylor

/-!
# The deterministic-clock lemma: the deterministic one-step expansion

For `Q ⪰ 0`, `a ≥ 0`, any `L`, `U = LL* - I`, `A = A_a = aQ(I + aQ)⁻¹`, `τ = Re Tr(AU)`,
`σ = Re Tr(AUAU) = ‖A^{1/2}UA^{1/2}‖²_HS`:

* `taylor_global`: `|F_a(L*QL) - F_a(Q)(1 - τ + τ²/2 + σ/2)| ≤ 400((√σ)³ + |τ|³)` for **every**
  `L` (on the event `σ ≤ 1/16`, `|τ| ≤ 1/4` this is `detLaplace_transport_taylor`; off it both
  Laplace functions are in `(0, 1]` and `1 < 4√σ` or `1 < 4|τ|`, so the polynomial of degree two
  is dominated by the cube). This replaces an event splitting with Markov at a fixed
  `p > 6` by a deterministic bound; the moments paid are the same third moments.
* `laplace_diff_le`: `|F_a(L*QL) - F_a(Q)| ≤ 4(|τ| + √σ)` ("the same first-order bounds").
* `step_expansion`: with a PSD injection `B`,
  `|F_a(L*QL + B) - F_a(Q) - (-F_a(Q)τ + F_a(Q)(τ² + σ)/2 - aF_a(Q)Tr B)|
   ≤ a²((Tr B)² + ‖B‖ Tr(L*QL)) + 4a(|τ| + √σ)Tr B + 400((√σ)³ + |τ|³)`
  (the Taylor remainder and the positive injection, `detLaplace_injection`).
* Weight bounds in the eigenbasis of `Q`: `|Tr(A_a f)| ≤ a|Tr(Qf)| + a²γ√S`,
  `Tr(A_a f A_a f*) ≤ a²S`, `Tr A_a² ≤ (Tr A_a)²`, `Tr A_a ≤ W`; `γ = Tr Q`, `S = Tr(QfQf*)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace DetClockProof

open ClockMixingAlg DetClockTaylor

variable {n : ℕ}

/-- `τ = Re Tr(A_a(LL* - I))`. -/
def tauA (Q L : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) : ℝ :=
  (resolventWeight Q a * (L * Lᴴ - 1)).trace.re

/-- `σ = Re Tr(A_a(LL* - I)A_a(LL* - I))`. -/
def sigA (Q L : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) : ℝ :=
  (resolventWeight Q a * (L * Lᴴ - 1) * resolventWeight Q a * (L * Lᴴ - 1)).trace.re

theorem sigA_eq_sq {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a)
    (L : Matrix (Fin n) (Fin n) ℂ) :
    sigA Q L a = hsSandwich (resolventWeight Q a) (L * Lᴴ - 1) ^ 2 := by
  have hA := resolventWeight_posSemidef hQ ha
  have hU : (L * Lᴴ - 1)ᴴ = L * Lᴴ - 1 := by
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one]
  unfold sigA
  rw [hsSandwich_eq_sqrt hA.1, Real.sq_sqrt (sandwichSum_nonneg hA _), ← Complex.ofReal_re
    (sandwichSum hA.1 (L * Lᴴ - 1)), ← trace_sandwich_eq_sum, hU]

theorem sigA_nonneg {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a)
    (L : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ sigA Q L a := by
  rw [sigA_eq_sq hQ ha]; exact sq_nonneg _

theorem sqrt_sigA {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a)
    (L : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (sigA Q L a) = hsSandwich (resolventWeight Q a) (L * Lᴴ - 1) := by
  rw [sigA_eq_sq hQ ha, Real.sqrt_sq (hsSandwich_nonneg _ _)]

/-!
## 1. Scalar facts
-/

/-- Off the good event the quadratic polynomial is dominated by the cube. -/
theorem quad_le_cube {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : 1 / 4 < s ∨ 1 / 4 < t) :
    2 + t + t ^ 2 / 2 + s ^ 2 / 2 ≤ 400 * (s ^ 3 + t ^ 3) := by
  have hs3 := pow_nonneg hs 3
  have ht3 := pow_nonneg ht 3
  rcases h with h | h
  · have h1 : 1 ≤ 64 * s ^ 3 := by
      have : 1 < (4 * s) ^ 3 := one_lt_pow₀ (by linarith) (by norm_num)
      nlinarith
    have h2 : t ≤ 64 * s ^ 3 + t ^ 3 := by
      rcases le_total t 1 with h' | h'
      · linarith
      · have := pow_le_pow_right₀ h' (show 1 ≤ 3 by norm_num); rw [pow_one] at this; linarith
    have h3 : t ^ 2 ≤ 64 * s ^ 3 + t ^ 3 := by
      rcases le_total t 1 with h' | h'
      · have : t ^ 2 ≤ 1 := pow_le_one₀ ht h'
        linarith
      · have := pow_le_pow_right₀ h' (show 2 ≤ 3 by norm_num); linarith
    have h4 : s ^ 2 ≤ 4 * s ^ 3 := by
      have : s ^ 3 = s * s ^ 2 := by ring
      have hs2 := sq_nonneg s
      nlinarith
    linarith
  · have h1 : 1 ≤ 64 * t ^ 3 := by
      have : 1 < (4 * t) ^ 3 := one_lt_pow₀ (by linarith) (by norm_num)
      nlinarith
    have h2 : t ≤ 16 * t ^ 3 := by
      have ht2 : 1 / 16 ≤ t ^ 2 := by nlinarith
      have : t ^ 3 = t * t ^ 2 := by ring
      nlinarith
    have h3 : t ^ 2 ≤ 4 * t ^ 3 := by
      have : t ^ 3 = t * t ^ 2 := by ring
      have ht2 := sq_nonneg t
      nlinarith
    have h4 : s ^ 2 ≤ 64 * t ^ 3 + s ^ 3 := by
      rcases le_total s 1 with h' | h'
      · have : s ^ 2 ≤ 1 := pow_le_one₀ hs h'
        linarith
      · have := pow_le_pow_right₀ h' (show 2 ≤ 3 by norm_num); linarith
    linarith

/-!
## 2. The global Taylor bound
-/

/-- **Global second-order Taylor bound**: for every `L`,
`|F_a(L*QL) - F_a(Q)(1 - τ + τ²/2 + σ/2)| ≤ 400((√σ)³ + |τ|³)`. -/
theorem taylor_global {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a)
    (L : Matrix (Fin n) (Fin n) ℂ) :
    |detLaplace (Lᴴ * Q * L) a - detLaplace Q a *
        (1 - tauA Q L a + tauA Q L a ^ 2 / 2 + sigA Q L a / 2)| ≤
      400 * (Real.sqrt (sigA Q L a) ^ 3 + |tauA Q L a| ^ 3) := by
  set τ := tauA Q L a with hτ
  set σ := sigA Q L a with hσ
  have hσ0 : 0 ≤ σ := sigA_nonneg hQ ha L
  set s := Real.sqrt σ with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = σ := Real.sq_sqrt hσ0
  have hF0 := detLaplace_pos hQ ha
  have hF1 := detLaplace_le_one hQ ha
  have hP : (Lᴴ * Q * L).PosSemidef := by
    have := hQ.conjTranspose_mul_mul_same L
    simpa [Matrix.mul_assoc] using this
  have hG0 := detLaplace_pos hP ha
  have hG1 := detLaplace_le_one hP ha
  by_cases hgood : σ ≤ 1 / 16 ∧ |τ| ≤ 1 / 4
  · have h : |detLaplace (Lᴴ * Q * L) a - detLaplace Q a * (1 - τ + τ ^ 2 / 2 + σ / 2)| ≤
        10 * detLaplace Q a * (Real.sqrt σ ^ 3 + |τ| ^ 3) :=
      detLaplace_transport_taylor hQ ha L hgood.1 hgood.2
    refine h.trans ?_
    have h0 : 0 ≤ Real.sqrt σ ^ 3 + |τ| ^ 3 := by positivity
    nlinarith
  · have hbad : 1 / 4 < s ∨ 1 / 4 < |τ| := by
      rcases not_and_or.mp hgood with h | h
      · left
        have h' : 1 / 16 < σ := lt_of_not_ge h
        by_contra hc
        have hc' : s ≤ 1 / 4 := le_of_not_gt hc
        have : s ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hs0 hc' 2
        linarith
      · right; exact lt_of_not_ge h
    have hq := quad_le_cube hs0 (abs_nonneg τ) hbad
    have hτ2 : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
    calc |detLaplace (Lᴴ * Q * L) a - detLaplace Q a * (1 - τ + τ ^ 2 / 2 + σ / 2)|
        ≤ |detLaplace (Lᴴ * Q * L) a| + |detLaplace Q a * (1 - τ + τ ^ 2 / 2 + σ / 2)| :=
          abs_sub _ _
      _ ≤ 1 + (1 + |τ| + τ ^ 2 / 2 + σ / 2) := by
          rw [abs_of_pos hG0, abs_mul, abs_of_pos hF0]
          refine add_le_add hG1 ?_
          have h1 : |1 - τ + τ ^ 2 / 2 + σ / 2| ≤ 1 + |τ| + τ ^ 2 / 2 + σ / 2 := by
            refine (abs_le.mpr ⟨?_, ?_⟩)
            · have := neg_abs_le τ; nlinarith [sq_nonneg τ]
            · have := le_abs_self (-τ); rw [abs_neg] at this; nlinarith
          calc detLaplace Q a * |1 - τ + τ ^ 2 / 2 + σ / 2|
              ≤ 1 * |1 - τ + τ ^ 2 / 2 + σ / 2| :=
                mul_le_mul_of_nonneg_right hF1 (abs_nonneg _)
            _ ≤ _ := by rw [one_mul]; exact h1
      _ = 2 + |τ| + |τ| ^ 2 / 2 + s ^ 2 / 2 := by rw [hss, hτ2]; ring
      _ ≤ 400 * (s ^ 3 + |τ| ^ 3) := hq

/-- `|F_a(L*QL) - F_a(Q)| ≤ 4(|τ| + √σ)` for every `L`. -/
theorem laplace_diff_le {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a)
    (L : Matrix (Fin n) (Fin n) ℂ) :
    |detLaplace (Lᴴ * Q * L) a - detLaplace Q a| ≤
      4 * (|tauA Q L a| + Real.sqrt (sigA Q L a)) := by
  set τ := tauA Q L a with hτ
  set σ := sigA Q L a with hσ
  have hσ0 : 0 ≤ σ := sigA_nonneg hQ ha L
  set s := Real.sqrt σ with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = σ := Real.sq_sqrt hσ0
  have hF0 := detLaplace_pos hQ ha
  have hF1 := detLaplace_le_one hQ ha
  have hP : (Lᴴ * Q * L).PosSemidef := by
    have := hQ.conjTranspose_mul_mul_same L
    simpa [Matrix.mul_assoc] using this
  have hG0 := detLaplace_pos hP ha
  have hG1 := detLaplace_le_one hP ha
  by_cases hgood : σ ≤ 1 / 16 ∧ |τ| ≤ 1 / 4
  · have h : |detLaplace (Lᴴ * Q * L) a - detLaplace Q a * (1 - τ + τ ^ 2 / 2 + σ / 2)| ≤
        10 * detLaplace Q a * (s ^ 3 + |τ| ^ 3) :=
      detLaplace_transport_taylor hQ ha L hgood.1 hgood.2
    have hs4 : s ≤ 1 / 4 := by
      rw [hs, show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hgood.1
    have ht4 := hgood.2
    have ht0 := abs_nonneg τ
    have hτ2 : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
    have hP1 : |detLaplace Q a * (1 - τ + τ ^ 2 / 2 + σ / 2) - detLaplace Q a| ≤
        |τ| + |τ| ^ 2 / 2 + s ^ 2 / 2 := by
      rw [show detLaplace Q a * (1 - τ + τ ^ 2 / 2 + σ / 2) - detLaplace Q a =
        detLaplace Q a * (-τ + τ ^ 2 / 2 + σ / 2) by ring, abs_mul, abs_of_pos hF0]
      have h1 : |-τ + τ ^ 2 / 2 + σ / 2| ≤ |τ| + |τ| ^ 2 / 2 + s ^ 2 / 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg (by positivity : 0 ≤ σ / 2), ← hss]
        refine add_le_add ((abs_add_le _ _).trans ?_) le_rfl
        rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ τ ^ 2 / 2), hτ2]
      calc detLaplace Q a * |-τ + τ ^ 2 / 2 + σ / 2| ≤ 1 * |-τ + τ ^ 2 / 2 + σ / 2| :=
            mul_le_mul_of_nonneg_right hF1 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h1
    have h10 : 10 * detLaplace Q a * (s ^ 3 + |τ| ^ 3) ≤ 10 * (s ^ 3 + |τ| ^ 3) := by
      have : 0 ≤ s ^ 3 + |τ| ^ 3 := by positivity
      nlinarith
    calc |detLaplace (Lᴴ * Q * L) a - detLaplace Q a|
        ≤ |detLaplace (Lᴴ * Q * L) a - detLaplace Q a * (1 - τ + τ ^ 2 / 2 + σ / 2)| +
            |detLaplace Q a * (1 - τ + τ ^ 2 / 2 + σ / 2) - detLaplace Q a| := abs_sub_le _ _ _
      _ ≤ 10 * (s ^ 3 + |τ| ^ 3) + (|τ| + |τ| ^ 2 / 2 + s ^ 2 / 2) :=
          add_le_add (h.trans h10) hP1
      _ ≤ 4 * (|τ| + s) := by
          have e1 : s ^ 3 ≤ s / 16 := by nlinarith
          have e2 : |τ| ^ 3 ≤ |τ| / 16 := by nlinarith
          have e3 : |τ| ^ 2 ≤ |τ| / 4 := by nlinarith
          have e4 : s ^ 2 ≤ s / 4 := by nlinarith
          linarith
  · have hbad : 1 / 4 < s ∨ 1 / 4 < |τ| := by
      rcases not_and_or.mp hgood with h | h
      · left
        have h' : 1 / 16 < σ := lt_of_not_ge h
        by_contra hc
        have hc' : s ≤ 1 / 4 := le_of_not_gt hc
        have : s ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hs0 hc' 2
        linarith
      · right; exact lt_of_not_ge h
    have h1 : |detLaplace (Lᴴ * Q * L) a - detLaplace Q a| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    rcases hbad with h | h <;> nlinarith [abs_nonneg τ]

/-!
## 3. The one-step expansion
-/

/-- **One-step expansion**: for `Q, B ⪰ 0`, `a ≥ 0` and any `L`,
`|F_a(L*QL + B) - F_a(Q) - (-F_a(Q)τ + F_a(Q)(τ² + σ)/2 - aF_a(Q)Tr B)|
  ≤ a²((Tr B)² + ‖B‖Tr(L*QL)) + 4a(|τ| + √σ)Tr B + 400((√σ)³ + |τ|³)`. -/
theorem step_expansion {Q B : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) (hB : B.PosSemidef)
    {a : ℝ} (ha : 0 ≤ a) (L : Matrix (Fin n) (Fin n) ℂ) :
    |detLaplace (Lᴴ * Q * L + B) a - detLaplace Q a -
        (-(detLaplace Q a * tauA Q L a) +
          detLaplace Q a * (tauA Q L a ^ 2 + sigA Q L a) / 2 -
          a * detLaplace Q a * B.trace.re)| ≤
      a ^ 2 * (B.trace.re ^ 2 + ‖B‖ * (Lᴴ * Q * L).trace.re) +
        4 * a * (|tauA Q L a| + Real.sqrt (sigA Q L a)) * B.trace.re +
        400 * (Real.sqrt (sigA Q L a) ^ 3 + |tauA Q L a| ^ 3) := by
  have hP : (Lᴴ * Q * L).PosSemidef := by
    have := hQ.conjTranspose_mul_mul_same L
    simpa [Matrix.mul_assoc] using this
  have h1 := detLaplace_injection hP hB ha
  have h2 := laplace_diff_le hQ ha L
  have h3 := taylor_global hQ ha L
  have hTB : 0 ≤ B.trace.re := trace_re_nonneg hB
  have h4 : |a * (detLaplace Q a - detLaplace (Lᴴ * Q * L) a) * B.trace.re| ≤
      4 * a * (|tauA Q L a| + Real.sqrt (sigA Q L a)) * B.trace.re := by
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hTB, abs_sub_comm]
    have := mul_le_mul_of_nonneg_left h2 ha
    nlinarith
  have e : detLaplace (Lᴴ * Q * L + B) a - detLaplace Q a -
      (-(detLaplace Q a * tauA Q L a) + detLaplace Q a * (tauA Q L a ^ 2 + sigA Q L a) / 2 -
        a * detLaplace Q a * B.trace.re) =
      (detLaplace (Lᴴ * Q * L + B) a - detLaplace (Lᴴ * Q * L) a +
          a * detLaplace (Lᴴ * Q * L) a * B.trace.re) +
        a * (detLaplace Q a - detLaplace (Lᴴ * Q * L) a) * B.trace.re +
        (detLaplace (Lᴴ * Q * L) a - detLaplace Q a *
          (1 - tauA Q L a + tauA Q L a ^ 2 / 2 + sigA Q L a / 2)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  refine add_le_add ((abs_add_le _ _).trans (add_le_add h1 h4)) h3

/-!
## 4. Weight bounds in the eigenbasis of `Q`
-/

section Weights

variable {Q : Matrix (Fin n) (Fin n) ℂ}

/-- `A_a = U diag(aλ/(1+aλ)) U*` in the eigenbasis of `Q`. -/
theorem resolventWeight_spec (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    resolventWeight Q a = eU hQ.1 * diagonal (fun i => ((a * hQ.1.eigenvalues i /
      (1 + a * hQ.1.eigenvalues i) : ℝ) : ℂ)) * star (eU hQ.1) := by
  set U := eU hQ.1
  set μ := hQ.1.eigenvalues
  have hpos : ∀ i, 0 < 1 + a * μ i := fun i => by
    have := hQ.eigenvalues_nonneg i; positivity
  have hU1 : star U * U = 1 := eU_star_mul hQ.1
  have hU2 : U * star U = 1 := eU_mul_star hQ.1
  have hsp := spec hQ.1
  have hconj : ∀ M N : Matrix (Fin n) (Fin n) ℂ,
      (U * M * star U) * (U * N * star U) = U * (M * N) * star U := by
    intro M N
    calc (U * M * star U) * (U * N * star U) = U * M * (star U * U) * N * star U := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hone : 1 + (a : ℂ) • Q = U * diagonal (fun i => ((1 + a * μ i : ℝ) : ℂ)) * star U := by
    have hd : diagonal (fun i => ((1 + a * μ i : ℝ) : ℂ)) =
        1 + (a : ℂ) • diagonal (fun i => (μ i : ℂ)) := by
      ext i j; by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU2, Matrix.mul_smul, Matrix.smul_mul,
      ← hsp]
  have hinv : (1 + (a : ℂ) • Q)⁻¹ = U * diagonal (fun i => (((1 + a * μ i)⁻¹ : ℝ) : ℂ)) * star U := by
    rw [hone]
    apply Matrix.inv_eq_left_inv
    rw [hconj, diagonal_mul_diagonal]
    have : (fun i => (((1 + a * μ i)⁻¹ : ℝ) : ℂ) * ((1 + a * μ i : ℝ) : ℂ)) = fun _ => (1 : ℂ) :=
      funext fun i => by rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hpos i).ne', Complex.ofReal_one]
    rw [this, diagonal_one, Matrix.mul_one, hU2]
  have hs : (a : ℂ) • Q = U * diagonal (fun i => ((a * μ i : ℝ) : ℂ)) * star U := by
    rw [hsp, ← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j; by_cases h : i = j
    · subst h; simp [μ]
    · simp [h]
  unfold resolventWeight
  rw [hinv, hs, hconj, diagonal_mul_diagonal]
  refine congrArg (fun d => U * diagonal d * star U) (funext fun i => ?_)
  rw [← Complex.ofReal_mul, div_eq_mul_inv]

/-- `Tr(D M) = Σ dᵢ (U*MU)ᵢᵢ` for `D = U diag(d) U*`. -/
theorem trace_diagConj_mul (hQ : Q.IsHermitian) (d : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (eU hQ * diagonal (fun i => (d i : ℂ)) * star (eU hQ) * M).trace =
      ∑ i, (d i : ℂ) * rot hQ M i i := by
  have : eU hQ * diagonal (fun i => (d i : ℂ)) * star (eU hQ) * M =
      eU hQ * (diagonal (fun i => (d i : ℂ)) * star (eU hQ) * M) := by
    simp only [Matrix.mul_assoc]
  rw [this, trace_mul_comm]
  have : diagonal (fun i => (d i : ℂ)) * star (eU hQ) * M * eU hQ =
      diagonal (fun i => (d i : ℂ)) * rot hQ M := by
    unfold rot; simp only [Matrix.mul_assoc]
  rw [this]
  simp [trace, diagonal_mul]

/-- `Tr(D M D M*) = Σ dᵢd_k |(U*MU)ᵢₖ|²` for `D = U diag(d) U*`. -/
theorem trace_diagConj_sandwich (hQ : Q.IsHermitian) (d : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (eU hQ * diagonal (fun i => (d i : ℂ)) * star (eU hQ) * M *
        (eU hQ * diagonal (fun i => (d i : ℂ)) * star (eU hQ)) * Mᴴ).trace =
      ((∑ i, ∑ k, d i * d k * ‖rot hQ M i k‖ ^ 2 : ℝ) : ℂ) := by
  have key : eU hQ * diagonal (fun i => (d i : ℂ)) * star (eU hQ) * M *
      (eU hQ * diagonal (fun i => (d i : ℂ)) * star (eU hQ)) * Mᴴ =
      eU hQ * (diagonal (fun i => (d i : ℂ)) * rot hQ M * diagonal (fun i => (d i : ℂ)) *
        (rot hQ M)ᴴ * star (eU hQ)) := by
    rw [← rot_conjTranspose]
    unfold rot
    calc eU hQ * diagonal (fun i => (d i : ℂ)) * star (eU hQ) * M *
          (eU hQ * diagonal (fun i => (d i : ℂ)) * star (eU hQ)) * Mᴴ
        = eU hQ * diagonal (fun i => (d i : ℂ)) * (star (eU hQ) * M * eU hQ) *
            diagonal (fun i => (d i : ℂ)) * (star (eU hQ) * Mᴴ * (eU hQ * star (eU hQ))) := by
          rw [eU_mul_star hQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [key, trace_mul_comm, Matrix.mul_assoc, eU_star_mul hQ, Matrix.mul_one]
  exact trace_diag_sandwich _ _

/-- `|Tr(A_a f)| ≤ a|Tr(Qf)| + a²γ√S` (from `A_a = aQ - a²Q²(I+aQ)⁻¹`). -/
theorem norm_trace_weight_mul_le {W : ℕ} {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    {a : ℝ} (ha : 0 ≤ a) (f : Matrix (Fin W) (Fin W) ℂ) :
    ‖(resolventWeight Q a * f).trace‖ ≤
      a * ‖(Q * f).trace‖ + a ^ 2 * Q.trace.re * hsSandwich Q f := by
  set μ := hQ.1.eigenvalues
  have hμ : ∀ i, 0 ≤ μ i := hQ.eigenvalues_nonneg
  set F := rot hQ.1 f
  have h1 : (resolventWeight Q a * f).trace = ∑ i, (((a * μ i / (1 + a * μ i)) : ℝ) : ℂ) * F i i := by
    rw [resolventWeight_spec hQ ha, trace_diagConj_mul]
  have h2 : (Q * f).trace = ∑ i, ((μ i : ℝ) : ℂ) * F i i := trace_mul_eq_sum hQ.1 f
  have hS : ∀ i, μ i * ‖F i i‖ ≤ hsSandwich Q f := by
    intro i
    rw [hsSandwich_eq_sqrt hQ.1]
    refine Real.le_sqrt_of_sq_le ?_
    unfold sandwichSum
    calc (μ i * ‖F i i‖) ^ 2 = μ i * μ i * ‖rot hQ.1 f i i‖ ^ 2 := by ring
      _ ≤ ∑ k, μ i * μ k * ‖rot hQ.1 f i k‖ ^ 2 :=
          Finset.single_le_sum (f := fun k => μ i * μ k * ‖rot hQ.1 f i k‖ ^ 2)
            (fun k _ => by have := hμ i; have := hμ k; positivity) (Finset.mem_univ i)
      _ ≤ ∑ j, ∑ k, μ j * μ k * ‖rot hQ.1 f j k‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ∑ k, μ j * μ k * ‖rot hQ.1 f j k‖ ^ 2)
            (fun j _ => Finset.sum_nonneg fun k _ => by
              have := hμ j; have := hμ k; positivity) (Finset.mem_univ i)
  have hdiff : (resolventWeight Q a * f).trace - (a : ℂ) * (Q * f).trace =
      ∑ i, (((a * μ i / (1 + a * μ i) - a * μ i) : ℝ) : ℂ) * F i i := by
    rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  have hbound : ‖(resolventWeight Q a * f).trace - (a : ℂ) * (Q * f).trace‖ ≤
      a ^ 2 * Q.trace.re * hsSandwich Q f := by
    rw [hdiff, trace_re_eq_sum hQ.1, Finset.mul_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < 1 + a * μ i := by have := hμ i; positivity
    have he : a * μ i / (1 + a * μ i) - a * μ i = -(a ^ 2 * μ i ^ 2 / (1 + a * μ i)) := by
      field_simp; ring
    have hle : a ^ 2 * μ i ^ 2 / (1 + a * μ i) ≤ a ^ 2 * μ i ^ 2 :=
      div_le_self (by have := hμ i; positivity) (by have := hμ i; nlinarith)
    rw [he, abs_neg, abs_of_nonneg (by have := hμ i; positivity)]
    calc a ^ 2 * μ i ^ 2 / (1 + a * μ i) * ‖F i i‖ ≤ a ^ 2 * μ i ^ 2 * ‖F i i‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ = a ^ 2 * μ i * (μ i * ‖F i i‖) := by ring
      _ ≤ a ^ 2 * μ i * hsSandwich Q f :=
          mul_le_mul_of_nonneg_left (hS i) (by have := hμ i; positivity)
  calc ‖(resolventWeight Q a * f).trace‖
      ≤ ‖(a : ℂ) * (Q * f).trace‖ +
          ‖(resolventWeight Q a * f).trace - (a : ℂ) * (Q * f).trace‖ := by
        have := norm_add_le ((a : ℂ) * (Q * f).trace)
          ((resolventWeight Q a * f).trace - (a : ℂ) * (Q * f).trace)
        simpa using this
    _ ≤ a * ‖(Q * f).trace‖ + a ^ 2 * Q.trace.re * hsSandwich Q f := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
        exact add_le_add le_rfl hbound

/-- `Tr(A_a f A_a f*) ≤ a² Tr(QfQf*)` (from `0 ⪯ A_a ⪯ aQ`). -/
theorem trace_weight_sandwich_le {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {a : ℝ}
    (ha : 0 ≤ a) (f : Matrix (Fin n) (Fin n) ℂ) :
    (resolventWeight Q a * f * resolventWeight Q a * fᴴ).trace.re ≤
      a ^ 2 * (Q * f * Q * fᴴ).trace.re := by
  set μ := hQ.1.eigenvalues
  have hμ : ∀ i, 0 ≤ μ i := hQ.eigenvalues_nonneg
  rw [resolventWeight_spec hQ ha, trace_diagConj_sandwich, trace_sandwich_eq_sum hQ.1,
    Complex.ofReal_re, Complex.ofReal_re]
  unfold sandwichSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hpi : 0 < 1 + a * μ i := by have := hμ i; positivity
  have hpk : 0 < 1 + a * μ k := by have := hμ k; positivity
  have h1 : a * μ i / (1 + a * μ i) ≤ a * μ i :=
    div_le_self (by have := hμ i; positivity) (by have := hμ i; nlinarith)
  have h2 : a * μ k / (1 + a * μ k) ≤ a * μ k :=
    div_le_self (by have := hμ k; positivity) (by have := hμ k; nlinarith)
  have h1' : 0 ≤ a * μ i / (1 + a * μ i) := by have := hμ i; positivity
  have h2' : 0 ≤ a * μ k / (1 + a * μ k) := by have := hμ k; positivity
  have := mul_le_mul h1 h2 h2' (by have := hμ i; positivity)
  have hn := sq_nonneg ‖rot hQ.1 f i k‖
  calc a * μ i / (1 + a * μ i) * (a * μ k / (1 + a * μ k)) * ‖rot hQ.1 f i k‖ ^ 2
      ≤ a * μ i * (a * μ k) * ‖rot hQ.1 f i k‖ ^ 2 := mul_le_mul_of_nonneg_right this hn
    _ = a ^ 2 * (μ i * μ k * ‖rot hQ.1 f i k‖ ^ 2) := by ring

/-- `Tr A_a² ≤ (Tr A_a)²`. -/
theorem trace_weight_sq_le {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {a : ℝ}
    (ha : 0 ≤ a) : ((resolventWeight Q a) ^ 2).trace.re ≤ (resolventWeight Q a).trace.re ^ 2 := by
  rw [trace_resolventWeight_sq_eq_sum hQ ha, trace_resolventWeight_eq_sum hQ ha,
    Complex.ofReal_re, Complex.ofReal_re]
  refine Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => ?_
  have := hQ.eigenvalues_nonneg i
  have : 0 < 1 + a * hQ.isHermitian.eigenvalues i := by positivity
  positivity

/-- `Tr A_a ≤ n` (every eigenvalue of `A_a` is below one). -/
theorem trace_weight_le_card {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {a : ℝ}
    (ha : 0 ≤ a) : (resolventWeight Q a).trace.re ≤ n := by
  rw [trace_resolventWeight_eq_sum hQ ha, Complex.ofReal_re]
  calc ∑ i, a * hQ.isHermitian.eigenvalues i / (1 + a * hQ.isHermitian.eigenvalues i)
      ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        have := hQ.eigenvalues_nonneg i
        have hp : 0 < 1 + a * hQ.isHermitian.eigenvalues i := by positivity
        rw [div_le_one hp]; linarith
    _ = n := by simp

end Weights

end DetClockProof

end BlockBand.Endpoints.Clock
