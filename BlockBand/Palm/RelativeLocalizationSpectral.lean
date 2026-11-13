module

public import BlockBand.Palm.RelativeLocalizationODE
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Relative localization: spectral inputs to Steps 3–4 at one time

* `rlPhi_drift_le` : the drift inequality of Step 3 for the weight `rlPhi`, any generator
  dominated by the short one on nonnegative vectors, with
  `κ = 2ℓ B e^{νC₀C₁ℓ/N}/N + 2νC₀(1 + log N)/c₁ + B/(2N)`,
  `B = ν(C₀/R + C₀/d) + ν²C₀²` (`C₀ = weightConst`);
* `rlPhi_bracket_le` : the bracket bound with `A = νC₀`;
* `far_of_not_window` (Step 4, initial weight): with `k₀ = #{l : λ_l(a) ≤ E}` and the upper
  count at time `a`, every label with `|j - k₀| > w` has
  `|λ_j(s) - E| ≥ (w+1)/(C N) - h - D₀` if eigenvalues moved by at most `D₀`;
* `initial_mass_le`, `terminal_le` : the initial weighted mass of `1_{J^c}` is at most
  `N e^{-ν min(δ - d, R)}`, and `v_k ≤ e^{ν|λ_k - E|} Σ_j φ(λ_j) v_j` (final weight).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Set Finset BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- The concrete weight is flat (`φ = e^{-νR}`, `φ' = 0`) outside the `r₀/8` window. -/
theorem rlPhi_short_close_or_flat {ν E d R r₀ G : ℝ} (hR : 0 < R)
    (hρ : d + 2 * R ≤ r₀ / 8) (lam : Fin N → ℝ) (ℓ : ℕ)
    (h2 : ∀ i j : Fin N, labelDist i j < ℓ → min |lam i - E| |lam j - E| ≤ r₀ / 8 →
      |lam i - lam j| ≤ G) :
    ∀ k l : Fin N, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨
        (rlPhi1 ν E d R (lam k) = 0 ∧ rlPhi ν E d R (lam l) = rlPhi ν E d R (lam k)) := by
  intro k l _ hkl
  by_cases hmin : min |lam k - E| |lam l - E| ≤ r₀ / 8
  · left; rw [abs_sub_comm]; exact h2 k l hkl hmin
  · right
    push Not at hmin
    have hk : d + 2 * R < |lam k - E| := lt_of_le_of_lt hρ (lt_of_lt_of_le hmin (min_le_left _ _))
    have hl : d + 2 * R < |lam l - E| := lt_of_le_of_lt hρ (lt_of_lt_of_le hmin (min_le_right _ _))
    exact ⟨rlPhi1_eq_zero_of_far hR hk, by rw [rlPhi_eq_of_far hR hl, rlPhi_eq_of_far hR hk]⟩

/-- **Step 3 drift inequality for the concrete weight.** -/
theorem rlPhi_drift_le {ν E d R r₀ c₁ C₁ : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hR : 0 < R)
    (hρ : d + 2 * R ≤ r₀ / 8) (hc₁ : 0 < c₁) (lam : Fin N → ℝ) (ℓ : ℕ)
    (L : Fin N → Fin N → ℝ) (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hLS : ∀ k, ∑ l, L k l * v l ≤ ∑ l, shortGen N lam ℓ k l * v l)
    (h1 : ∀ i j : Fin N, ℓ ≤ labelDist i j → c₁ * labelDist i j / N ≤ |lam i - lam j|)
    (h2 : ∀ i j : Fin N, labelDist i j < ℓ → min |lam i - E| |lam j - E| ≤ r₀ / 8 →
      |lam i - lam j| ≤ C₁ * ℓ / N) :
    ∑ k, rlPhi ν E d R (lam k) * ∑ l, L k l * v l +
        ∑ k, v k * (rlPhi1 ν E d R (lam k) * dysonDrift N lam k +
          rlPhi2 ν E d R (lam k) / (2 * N)) ≤
      (2 * ℓ * (ν * (weightConst / R + weightConst / d) + ν ^ 2 * weightConst ^ 2) *
            Real.exp (ν * weightConst * (C₁ * ℓ / N)) / N +
          2 * (ν * weightConst) * (1 + Real.log N) / c₁ +
          (ν * (weightConst / R + weightConst / d) + ν ^ 2 * weightConst ^ 2) / (2 * N)) *
        ∑ k, rlPhi ν E d R (lam k) * v k := by
  have hC := weightConst_pos
  refine weighted_drift_le lam ℓ L v hv (rlPhi_hasDerivAt hd hR) (rlPhi1_hasDerivAt hd hR)
    (fun z => (rlPhi_pos z).le) (abs_rlPhi1_le hν hd hR) (by positivity)
    (abs_rlPhi2_le hν hd hR) (by positivity) (Real.exp_pos _).le ?_ hc₁ hLS
    (rlPhi_short_close_or_flat hR hρ lam ℓ h2) (fun k l _ hkl => h1 k l hkl)
  intro x z hxz
  refine (rlPhi_le_exp_mul hν hd hR x z).trans (mul_le_mul_of_nonneg_right ?_ (rlPhi_pos x).le)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxz (by positivity))

/-- **Step 3 bracket bound for the concrete weight.** -/
theorem rlPhi_bracket_le {ν E d R : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hR : 0 < R)
    (lam : Fin N → ℝ) (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k) :
    ∑ k, (v k * rlPhi1 ν E d R (lam k)) ^ 2 / N ≤
      (ν * weightConst) ^ 2 / N * (∑ k, rlPhi ν E d R (lam k) * v k) ^ 2 :=
  weighted_bracket_le lam v hv (fun z => (rlPhi_pos z).le) (abs_rlPhi1_le hν hd hR)

/-!
### Step 4: the initial and the final weights
-/

theorem lt_of_card_le_of_mono {lam : Fin N → ℝ} (hmono : Monotone lam) {E : ℝ} (m : Fin N)
    (hm : (Finset.univ.filter fun l : Fin N => lam l ≤ E).card ≤ m.val) : E < lam m := by
  by_contra hle
  push Not at hle
  have hsub : Finset.Iic m ⊆ Finset.univ.filter fun l : Fin N => lam l ≤ E := by
    intro l hl
    simp only [Finset.mem_Iic] at hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hmono hl).trans hle
  have := Finset.card_le_card hsub
  rw [Fin.card_Iic] at this
  omega

theorem le_of_lt_card_of_mono {lam : Fin N → ℝ} (hmono : Monotone lam) {E : ℝ} (m : Fin N)
    (hm : m.val < (Finset.univ.filter fun l : Fin N => lam l ≤ E).card) : lam m ≤ E := by
  by_contra hlt
  push Not at hlt
  have hsub : (Finset.univ.filter fun l : Fin N => lam l ≤ E) ⊆ Finset.Iio m := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    simp only [Finset.mem_Iio]
    by_contra hge
    push Not at hge
    exact absurd ((hlt.trans_le (hmono hge)).trans_le hl) (lt_irrefl _)
  have := Finset.card_le_card hsub
  rw [Fin.card_Iio] at this
  omega

/-- **Initial weight geometry**. Let `k₀ = #{l : λ_l(a) ≤ E}` (first rank
above `E` at time `a`, zero-based), the time-`a` upper count
`#{i : λ_i(a) ∈ [x,y]} ≤ C N((y - x) + h)`, and a displacement bound `|λ_j(s) - λ_j(a)| ≤ D₀`.
Every label `j` with `|j - k₀| > w` satisfies `|λ_j(s) - E| ≥ (w+1)/(CN) - h - D₀`. -/
theorem far_of_not_window (lamA lamS : Fin N → ℝ) (hmono : Monotone lamA) (E : ℝ) (w : ℕ)
    {C h D₀ : ℝ} (hC : 0 < C)
    (hcount : ∀ x y : ℝ, x ≤ y →
      ((Finset.univ.filter fun i : Fin N => lamA i ∈ Set.Icc x y).card : ℝ) ≤
        C * N * ((y - x) + h))
    (hdisp : ∀ j, |lamS j - lamA j| ≤ D₀) (j : Fin N)
    (hj : w < Int.natAbs ((j : ℤ) -
      ((Finset.univ.filter fun l : Fin N => lamA l ≤ E).card : ℤ))) :
    ((w : ℝ) + 1) / (C * N) - h - D₀ ≤ |lamS j - E| := by
  classical
  have hN : 0 < N := Fin.pos j
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set k₀ := (Finset.univ.filter fun l : Fin N => lamA l ≤ E).card with hk₀
  have hdj := hdisp j
  rw [abs_le] at hdj
  -- the distance at time `a`
  have ha : ((w : ℝ) + 1) / (C * N) - h ≤ |lamA j - E| := by
    rcases le_or_gt k₀ j.val with hge | hlt
    · -- `j` above the window
      have hk0N : k₀ < N := lt_of_le_of_lt hge j.isLt
      set m₀ : Fin N := ⟨k₀, hk0N⟩
      have hEj : E < lamA j := lt_of_card_le_of_mono hmono j hge
      have hsub : Finset.Icc m₀ j ⊆
          Finset.univ.filter fun i : Fin N => lamA i ∈ Set.Icc E (lamA j) := by
        intro m hm
        rw [Finset.mem_Icc] at hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
        exact ⟨(lt_of_card_le_of_mono hmono m (by
          have := hm.1; rw [Fin.le_def] at this; exact this)).le, hmono hm.2⟩
      have hc1 := Finset.card_le_card hsub
      rw [Fin.card_Icc] at hc1
      have hw : w + 1 ≤ j.val + 1 - k₀ := by
        have : (Int.natAbs ((j : ℤ) - (k₀ : ℤ))) = j.val - k₀ := by omega
        omega
      have hc2 := hcount E (lamA j) hEj.le
      have : ((w : ℝ) + 1) ≤ C * N * ((lamA j - E) + h) := by
        have h3 : ((w + 1 : ℕ) : ℝ) ≤ ((j.val + 1 - k₀ : ℕ) : ℝ) := by exact_mod_cast hw
        have h4 : ((j.val + 1 - k₀ : ℕ) : ℝ) ≤
            ((Finset.univ.filter fun i : Fin N => lamA i ∈ Set.Icc E (lamA j)).card : ℝ) := by
          exact_mod_cast hc1
        push_cast at h3
        linarith
      rw [abs_of_pos (by linarith)]
      have h5 : ((w : ℝ) + 1) / (C * N) ≤ (lamA j - E) + h := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    · -- `j` below the window
      have hk1 : 1 ≤ k₀ := by omega
      have hk0N : k₀ - 1 < N := by
        have : k₀ ≤ N := by
          rw [hk₀]; exact (Finset.card_le_univ _).trans (by simp)
        omega
      set m₁ : Fin N := ⟨k₀ - 1, hk0N⟩
      have hjE : lamA j ≤ E := le_of_lt_card_of_mono hmono j hlt
      have hsub : Finset.Icc j m₁ ⊆
          Finset.univ.filter fun i : Fin N => lamA i ∈ Set.Icc (lamA j) E := by
        intro m hm
        rw [Finset.mem_Icc] at hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
        refine ⟨hmono hm.1, le_of_lt_card_of_mono hmono m ?_⟩
        have := hm.2; rw [Fin.le_def] at this; simp only [m₁] at this; omega
      have hc1 := Finset.card_le_card hsub
      rw [Fin.card_Icc] at hc1
      have hw : w + 1 ≤ (k₀ - 1) + 1 - j.val := by
        have : (Int.natAbs ((j : ℤ) - (k₀ : ℤ))) = k₀ - j.val := by omega
        omega
      have hc2 := hcount (lamA j) E hjE
      have : ((w : ℝ) + 1) ≤ C * N * ((E - lamA j) + h) := by
        have h3 : ((w + 1 : ℕ) : ℝ) ≤ (((k₀ - 1) + 1 - j.val : ℕ) : ℝ) := by exact_mod_cast hw
        have h4 : (((k₀ - 1) + 1 - j.val : ℕ) : ℝ) ≤
            ((Finset.univ.filter fun i : Fin N => lamA i ∈ Set.Icc (lamA j) E).card : ℝ) := by
          exact_mod_cast hc1
        push_cast at h3
        linarith
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have h5 : ((w : ℝ) + 1) / (C * N) ≤ (E - lamA j) + h := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
  have : |lamA j - E| ≤ |lamS j - E| + D₀ := by
    have := abs_sub_le (lamA j) (lamS j) E
    have h' : |lamA j - lamS j| ≤ D₀ := by rw [abs_sub_comm]; exact abs_le.mpr ⟨hdj.1, hdj.2⟩
    linarith
  linarith

/-- **Initial weighted mass**: if every label outside the window is at
distance `≥ δ` from `E`, the weighted mass of `1_{J^c}` is at most `N e^{-ν min(δ - d, R)}`. -/
theorem initial_mass_le {ν E d R δ : ℝ} (hν : 0 ≤ ν) (hR : 0 < R) (lam : Fin N → ℝ)
    (out : Fin N → Prop) [DecidablePred out]
    (hfar : ∀ j, out j → δ ≤ |lam j - E|) :
    ∑ j, rlPhi ν E d R (lam j) * (if out j then 1 else 0) ≤
      N * Real.exp (-(ν * min (δ - d) R)) := by
  have hpt : ∀ j, rlPhi ν E d R (lam j) * (if out j then 1 else 0) ≤
      Real.exp (-(ν * min (δ - d) R)) := by
    intro j
    by_cases hj : out j
    · rw [ite_eq_left hj, mul_one]
      refine (rlPhi_le_exp hν hR (lam j)).trans (Real.exp_le_exp.mpr ?_)
      have : min (δ - d) R ≤ min (|lam j - E| - d) R :=
        min_le_min_right _ (by linarith [hfar j hj])
      nlinarith
    · rw [ite_eq_right hj, mul_zero]; exact (Real.exp_pos _).le
  calc _ ≤ ∑ _j : Fin N, Real.exp (-(ν * min (δ - d) R)) := Finset.sum_le_sum fun j _ => hpt j
    _ = _ := by simp

/-- **Final weight**: `v_k ≤ e^{ν|λ_k - E|} Σ_j φ(λ_j) v_j`. -/
theorem terminal_le {ν E d R : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hR : 0 < R) (lam : Fin N → ℝ)
    (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k) (k : Fin N) :
    v k ≤ Real.exp (ν * |lam k - E|) * ∑ j, rlPhi ν E d R (lam j) * v j := by
  have h1 : rlPhi ν E d R (lam k) * v k ≤ ∑ j, rlPhi ν E d R (lam j) * v j :=
    Finset.single_le_sum (f := fun j => rlPhi ν E d R (lam j) * v j)
      (fun j _ => mul_nonneg (rlPhi_pos _).le (hv j)) (Finset.mem_univ k)
  have h2 := exp_neg_le_rlPhi (E := E) (d := d) (R := R) hν hd hR (lam k)
  have he : Real.exp (ν * |lam k - E|) * Real.exp (-(ν * |lam k - E|)) = 1 := by
    rw [← Real.exp_add]; simp
  calc v k = Real.exp (ν * |lam k - E|) * (Real.exp (-(ν * |lam k - E|)) * v k) := by
        rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp (ν * |lam k - E|) * (rlPhi ν E d R (lam k) * v k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (hv k)) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

end BlockBand.Palm.RelativeLocalization
