module

public import BlockBand.Critical.RelativeVectors.DiagSums

/-!
# The diagonal relative error

Deterministic, at one time, in quadratic-form form (`p^*Δ_jp`, hence `‖Δ_j‖` for the Hermitian
`Δ_j`). Abstract data: increasing points `λ_i`, `Q_i = |p^*z_i|² ≥ 0`, `γ_i = p^*Γ_i p`,
`P = ‖p‖²`. Hypotheses (the good events at that time):
* gaps: `|λ_i - λ_j| ≥ c₁|i-j|/N` for `|i-j| ≥ ℓ` (`SpectralGoodEventContract` clause 1);
* the middle line of the interval bound: `|Σ_{λ_i ∈ [x,y]} (Q_i - γ_i)| ≤ M` on the window
  `[E - r₀/4, E + r₀/4]` (`relativeInterval_event`, `M = C_r N^{1-α+ε}P`);
* the third line of the interval bound: `|γ_i - P| ≤ C_γ(|λ_i - E| + t)P` in the window
  (`frame_gamma_shift_le`);
* the distant-label bound: `Σ_{|λ_i - E| > r₀/4} Q_i/(N(λ_i - λ_j)²) ≤ C_d P`
  (`relativeCoarse_event`);
* the tested label is central: `|λ_j - E| ≤ ρ ≤ r₀/8`.

`diagonal_le`:
`|p^*Δ_jp| ≤ 2NM/(c₁²ℓ²) + C_γP(2(1 + log N)/c₁ + 4N(ρ + t)/(c₁²ℓ)) + C_dP + 64P/r₀²`.
The first term is of order `N^{2-α+ε}/ℓ²` (one summation by parts per side, `abel_antitone`,
instead of dyadic shells); the second is `(N/ℓ)(t + w/N)` with `ρ` the distance of `λ_j` to `E`
(`O(w/N + √t)` for `|j - k₀| ≤ w`, from the counts and Weyl) and the `O(log N)` linear variation;
the last two are the exterior energy region.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Finset Set
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- One side of the window: summation by parts. -/
theorem diag_side_le {lam : Fin N → ℝ} (hlam : StrictMono lam) (X : Fin N → ℝ) {E r₀ M c₁ : ℝ}
    (hM : 0 ≤ M) (hc₁ : 0 < c₁) (hN : 0 < N) (j : Fin N) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hgap : ∀ i, ℓ ≤ labelDist i j → c₁ * labelDist i j / N ≤ |lam i - lam j|)
    (hS1 : ∀ x y, E - r₀ / 4 ≤ x → x ≤ y → y ≤ E + r₀ / 4 →
      |∑ i ∈ univ.filter (fun i => lam i ∈ Icc x y), X i| ≤ M) :
    |∑ i ∈ univ.filter (fun i => ℓ ≤ labelDist i j ∧ |lam i - E| ≤ r₀ / 4 ∧ lam j < lam i),
        X i / (N * (lam i - lam j) ^ 2)| ≤ M * (N / (c₁ ^ 2 * ℓ ^ 2)) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set R := univ.filter (fun i => ℓ ≤ labelDist i j ∧ |lam i - E| ≤ r₀ / 4 ∧ lam j < lam i)
  set m₀ := lam j + c₁ * ℓ / N with hm₀def
  have hm₀pos : lam j < m₀ := by rw [hm₀def]; have : 0 < c₁ * ℓ / N := by positivity
                                 linarith
  set g : ℝ → ℝ := fun u => 1 / (N * (u - lam j) ^ 2) with hgdef
  have hm₀ : ∀ i ∈ R, m₀ ≤ lam i := by
    intro i hi
    obtain ⟨hd, -, hji⟩ := (mem_filter.1 hi).2
    have := hgap i hd
    rw [abs_of_pos (by linarith)] at this
    have h2 : c₁ * ℓ / N ≤ c₁ * labelDist i j / N := by
      apply div_le_div_of_nonneg_right _ hNr.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hd) hc₁.le
    rw [hm₀def]; linarith
  have hg : ∀ u v, m₀ ≤ u → u ≤ v → g v ≤ g u := by
    intro u v hu huv
    simp only [hgdef]
    apply one_div_le_one_div_of_le (by have : 0 < u - lam j := by linarith
                                       positivity)
    apply mul_le_mul_of_nonneg_left _ hNr.le
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hg0 : ∀ u, m₀ ≤ u → 0 ≤ g u := fun u _ => by simp only [hgdef]; positivity
  have hpre : ∀ u, |∑ i ∈ R.filter (fun i => lam i ≤ u), X i| ≤ M := by
    intro u
    set T := R.filter (fun i => lam i ≤ u)
    rcases T.eq_empty_or_nonempty with hT | hT
    · rw [hT, sum_empty, abs_zero]; exact hM
    obtain ⟨i₀, hi₀, hmin⟩ := R.exists_min_image lam
      (let ⟨i, hi⟩ := hT; ⟨i, (mem_filter.1 hi).1⟩)
    obtain ⟨i₁, hi₁⟩ := hT
    have hi₁R := (mem_filter.1 hi₁).1
    have hi₁u := (mem_filter.1 hi₁).2
    obtain ⟨hd₀, hW₀, hj₀⟩ := (mem_filter.1 hi₀).2
    obtain ⟨-, hW₁, -⟩ := (mem_filter.1 hi₁R).2
    set y := min u (E + r₀ / 4)
    have hxy : lam i₀ ≤ y := le_min ((hmin i₁ hi₁R).trans hi₁u)
      (by have := hmin i₁ hi₁R; have := (abs_le.1 hW₁).2; linarith)
    have hTeq : T = univ.filter (fun i => lam i ∈ Icc (lam i₀) y) := by
      ext i
      simp only [T, R, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
      constructor
      · rintro ⟨⟨hd, hW, hji⟩, hiu⟩
        exact ⟨hmin i (mem_filter.2 ⟨mem_univ _, hd, hW, hji⟩),
          le_min hiu (by linarith [(abs_le.1 hW).2])⟩
      · rintro ⟨h1, h2⟩
        have hii₀ : i₀ ≤ i := hlam.le_iff_le.1 h1
        have hji₀ : j < i₀ := hlam.lt_iff_lt.1 hj₀
        have hd : ℓ ≤ labelDist i j := by
          unfold labelDist at hd₀ ⊢
          have a1 : (i₀ : ℕ) ≤ i := hii₀
          have a2 : (j : ℕ) < i₀ := hji₀
          omega
        refine ⟨⟨hd, ?_, lt_of_lt_of_le hj₀ h1⟩, le_trans h2 (min_le_left _ _)⟩
        rw [abs_le]
        constructor
        · linarith [(abs_le.1 hW₀).1]
        · linarith [min_le_right u (E + r₀ / 4)]
    rw [hTeq]
    exact hS1 _ _ (by linarith [(abs_le.1 hW₀).1]) hxy (min_le_right _ _)
  have hab := abel_antitone R lam (hlam.injective.injOn) g m₀ hm₀ hg hg0 X hM hpre
  have e : ∑ i ∈ R, X i / (N * (lam i - lam j) ^ 2) = ∑ i ∈ R, g (lam i) * X i :=
    sum_congr rfl fun i _ => by simp only [hgdef]; ring
  rw [e]
  refine hab.trans (le_of_eq ?_)
  simp only [hgdef, hm₀def]
  have : c₁ * ℓ / N ≠ 0 := by positivity
  field_simp
  ring

/-- The other side of the window (reflected summation by parts). -/
theorem diag_side_left_le {lam : Fin N → ℝ} (hlam : StrictMono lam) (X : Fin N → ℝ)
    {E r₀ M c₁ : ℝ} (hM : 0 ≤ M) (hc₁ : 0 < c₁) (hN : 0 < N) (j : Fin N) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hgap : ∀ i, ℓ ≤ labelDist i j → c₁ * labelDist i j / N ≤ |lam i - lam j|)
    (hS1 : ∀ x y, E - r₀ / 4 ≤ x → x ≤ y → y ≤ E + r₀ / 4 →
      |∑ i ∈ univ.filter (fun i => lam i ∈ Icc x y), X i| ≤ M) :
    |∑ i ∈ univ.filter (fun i => ℓ ≤ labelDist i j ∧ |lam i - E| ≤ r₀ / 4 ∧ lam i < lam j),
        X i / (N * (lam i - lam j) ^ 2)| ≤ M * (N / (c₁ ^ 2 * ℓ ^ 2)) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set L := univ.filter (fun i => ℓ ≤ labelDist i j ∧ |lam i - E| ≤ r₀ / 4 ∧ lam i < lam j)
  set lam' : Fin N → ℝ := fun i => -lam i with hlam'
  set m₀ := -lam j + c₁ * ℓ / N with hm₀def
  set g : ℝ → ℝ := fun u => 1 / (N * (u + lam j) ^ 2) with hgdef
  have hm₀ : ∀ i ∈ L, m₀ ≤ lam' i := by
    intro i hi
    obtain ⟨hd, -, hij⟩ := (mem_filter.1 hi).2
    have := hgap i hd
    rw [abs_of_neg (by linarith)] at this
    have h2 : c₁ * ℓ / N ≤ c₁ * labelDist i j / N := by
      apply div_le_div_of_nonneg_right _ hNr.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hd) hc₁.le
    simp only [hm₀def, hlam']; linarith
  have hg : ∀ u v, m₀ ≤ u → u ≤ v → g v ≤ g u := by
    intro u v hu huv
    have hpos : 0 < c₁ * ℓ / N := by positivity
    simp only [hgdef]
    apply one_div_le_one_div_of_le (by have : 0 < u + lam j := by linarith
                                       positivity)
    apply mul_le_mul_of_nonneg_left _ hNr.le
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hg0 : ∀ u, m₀ ≤ u → 0 ≤ g u := fun u _ => by simp only [hgdef]; positivity
  have hpre : ∀ u, |∑ i ∈ L.filter (fun i => lam' i ≤ u), X i| ≤ M := by
    intro u
    set T := L.filter (fun i => lam' i ≤ u)
    rcases T.eq_empty_or_nonempty with hT | hT
    · rw [hT, sum_empty, abs_zero]; exact hM
    obtain ⟨i₀, hi₀, hmax⟩ := L.exists_max_image lam
      (let ⟨i, hi⟩ := hT; ⟨i, (mem_filter.1 hi).1⟩)
    obtain ⟨i₁, hi₁⟩ := hT
    have hi₁L := (mem_filter.1 hi₁).1
    have hi₁u : -lam i₁ ≤ u := (mem_filter.1 hi₁).2
    obtain ⟨hd₀, hW₀, hj₀⟩ := (mem_filter.1 hi₀).2
    obtain ⟨-, hW₁, -⟩ := (mem_filter.1 hi₁L).2
    set x := max (-u) (E - r₀ / 4)
    have hxy : x ≤ lam i₀ := max_le (by have := hmax i₁ hi₁L; linarith)
      (by have := hmax i₁ hi₁L; have := (abs_le.1 hW₁).1; linarith)
    have hTeq : T = univ.filter (fun i => lam i ∈ Icc x (lam i₀)) := by
      ext i
      simp only [T, L, hlam', Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
      constructor
      · rintro ⟨⟨hd, hW, hij⟩, hiu⟩
        exact ⟨max_le (by linarith) (by linarith [(abs_le.1 hW).1]),
          hmax i (mem_filter.2 ⟨mem_univ _, hd, hW, hij⟩)⟩
      · rintro ⟨h1, h2⟩
        have hii₀ : i ≤ i₀ := hlam.le_iff_le.1 h2
        have hi₀j : i₀ < j := hlam.lt_iff_lt.1 hj₀
        have hd : ℓ ≤ labelDist i j := by
          unfold labelDist at hd₀ ⊢
          have a1 : (i : ℕ) ≤ i₀ := hii₀
          have a2 : (i₀ : ℕ) < j := hi₀j
          omega
        refine ⟨⟨hd, ?_, lt_of_le_of_lt h2 hj₀⟩, ?_⟩
        · rw [abs_le]
          constructor
          · linarith [le_max_right (-u) (E - r₀ / 4)]
          · linarith [(abs_le.1 hW₀).2]
        · linarith [le_max_left (-u) (E - r₀ / 4)]
    rw [hTeq]
    exact hS1 _ _ (le_max_right _ _) hxy (by linarith [(abs_le.1 hW₀).2])
  have hinj : Set.InjOn lam' L := fun a _ b _ hab => hlam.injective (neg_inj.1 hab)
  have hab := abel_antitone L lam' hinj g m₀ hm₀ hg hg0 X hM hpre
  have e : ∑ i ∈ L, X i / (N * (lam i - lam j) ^ 2) = ∑ i ∈ L, g (lam' i) * X i :=
    sum_congr rfl fun i _ => by simp only [hgdef, hlam']; ring
  rw [e]
  refine hab.trans (le_of_eq ?_)
  simp only [hgdef, hm₀def]
  have : c₁ * ℓ / N ≠ 0 := by positivity
  field_simp
  ring

/-- **The diagonal relative error** (deterministic, quadratic-form form). See the module
docstring. -/
theorem diagonal_le {lam : Fin N → ℝ} (hlam : StrictMono lam) (Q γ : Fin N → ℝ)
    (hQ : ∀ i, 0 ≤ Q i) {P : ℝ} (hP : 0 ≤ P) {E r₀ ρ t c₁ M Cγ Cd : ℝ} (hN : 0 < N)
    (hr₀ : 0 < r₀) (hc₁ : 0 < c₁) (hCγ : 0 ≤ Cγ) (ht : 0 ≤ t) (j : Fin N) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hρ : |lam j - E| ≤ ρ) (hρ8 : ρ ≤ r₀ / 8)
    (hgap : ∀ i, ℓ ≤ labelDist i j → c₁ * labelDist i j / N ≤ |lam i - lam j|)
    (hS1 : ∀ x y, E - r₀ / 4 ≤ x → x ≤ y → y ≤ E + r₀ / 4 →
      |∑ i ∈ univ.filter (fun i => lam i ∈ Icc x y), (Q i - γ i)| ≤ M)
    (hγ : ∀ i, |lam i - E| ≤ r₀ / 4 → |γ i - P| ≤ Cγ * (|lam i - E| + t) * P)
    (hS2 : ∑ i ∈ univ.filter (fun i => r₀ / 4 < |lam i - E|),
      Q i / (N * (lam i - lam j) ^ 2) ≤ Cd * P) :
    |∑ i ∈ univ.filter (fun i => ℓ ≤ labelDist i j), (Q i - P) / (N * (lam i - lam j) ^ 2)| ≤
      2 * (M * (N / (c₁ ^ 2 * ℓ ^ 2))) +
        Cγ * P * (2 * (1 + Real.log N) / c₁ + 4 * N * (ρ + t) / (c₁ ^ 2 * ℓ)) +
        Cd * P + 64 * P / r₀ ^ 2 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hM : 0 ≤ M := (abs_nonneg _).trans (hS1 E E (by linarith) le_rfl (by linarith))
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans hρ
  set D := univ.filter (fun i : Fin N => ℓ ≤ labelDist i j) with hD
  set a : Fin N → ℝ := fun i => 1 / (N * (lam i - lam j) ^ 2) with ha
  have hne : ∀ i ∈ D, lam i ≠ lam j := by
    intro i hi h
    have := hlam.injective h
    have hd := (mem_filter.1 hi).2
    rw [this] at hd
    unfold labelDist at hd
    simp at hd
    omega
  have hdpos : ∀ i ∈ D, c₁ * labelDist i j / N ≤ |lam i - lam j| := fun i hi =>
    hgap i (mem_filter.1 hi).2
  -- the right and left window sets
  set Rt := univ.filter (fun i => ℓ ≤ labelDist i j ∧ |lam i - E| ≤ r₀ / 4 ∧ lam j < lam i)
  set Lt := univ.filter (fun i => ℓ ≤ labelDist i j ∧ |lam i - E| ≤ r₀ / 4 ∧ lam i < lam j)
  set W := D.filter (fun i => |lam i - E| ≤ r₀ / 4)
  set X := D.filter (fun i => ¬ |lam i - E| ≤ r₀ / 4)
  have hW : W = Rt ∪ Lt := by
    ext i
    simp only [W, Rt, Lt, D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hd, hw⟩
      rcases lt_or_gt_of_ne (hne i (mem_filter.2 ⟨mem_univ _, hd⟩)) with h | h
      · exact Or.inr ⟨hd, hw, h⟩
      · exact Or.inl ⟨hd, hw, h⟩
    · rintro (⟨hd, hw, _⟩ | ⟨hd, hw, _⟩) <;> exact ⟨hd, hw⟩
  have hdisj : Disjoint Rt Lt := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    have := (mem_filter.1 h1).2.2.2
    have := (mem_filter.1 h2).2.2.2
    linarith
  have hsplit : ∑ i ∈ D, (Q i - P) / (N * (lam i - lam j) ^ 2) =
      (∑ i ∈ Rt, (Q i - γ i) / (N * (lam i - lam j) ^ 2) +
        ∑ i ∈ Lt, (Q i - γ i) / (N * (lam i - lam j) ^ 2)) +
      ∑ i ∈ W, (γ i - P) * a i + ∑ i ∈ X, (Q i - P) * a i := by
    rw [← sum_filter_add_sum_filter_not D (fun i => |lam i - E| ≤ r₀ / 4)]
    have e1 : ∑ i ∈ W, (Q i - P) / (N * (lam i - lam j) ^ 2) =
        ∑ i ∈ W, (Q i - γ i) / (N * (lam i - lam j) ^ 2) + ∑ i ∈ W, (γ i - P) * a i := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => by simp only [ha]; ring
    have e2 : ∑ i ∈ X, (Q i - P) / (N * (lam i - lam j) ^ 2) = ∑ i ∈ X, (Q i - P) * a i :=
      sum_congr rfl fun i _ => by simp only [ha]; ring
    rw [e1, e2, hW, sum_union hdisj]
  rw [hsplit]
  -- the four bounds
  have hR := diag_side_le hlam (fun i => Q i - γ i) hM hc₁ hN j hℓ hgap hS1
  have hL := diag_side_left_le hlam (fun i => Q i - γ i) hM hc₁ hN j hℓ hgap hS1
  have ha_le : ∀ i ∈ D, a i ≤ N / (c₁ ^ 2 * (labelDist i j : ℝ) ^ 2) := by
    intro i hi
    have hd1 : (1 : ℝ) ≤ labelDist i j := by exact_mod_cast hℓ.trans (mem_filter.1 hi).2
    have h := hdpos i hi
    have hpos : 0 < c₁ * labelDist i j / N := by positivity
    have h2 : (c₁ * labelDist i j / N) ^ 2 ≤ (lam i - lam j) ^ 2 := by
      rw [← sq_abs (lam i - lam j)]; exact pow_le_pow_left₀ hpos.le h 2
    have hsq : 0 < (lam i - lam j) ^ 2 := lt_of_lt_of_le (by positivity) h2
    simp only [ha]
    rw [div_le_div_iff₀ (mul_pos hNr hsq) (by positivity), one_mul]
    have : (c₁ * labelDist i j / N) ^ 2 * N ^ 2 = c₁ ^ 2 * (labelDist i j : ℝ) ^ 2 := by
      field_simp
    nlinarith
  have hsumA : ∑ i ∈ D, a i ≤ 4 * N / (c₁ ^ 2 * ℓ) := by
    refine (sum_le_sum ha_le).trans ?_
    have := sum_labelDist_le j ℓ (fun k => (N : ℝ) / (c₁ ^ 2 * (k : ℝ) ^ 2)) (fun k => by positivity)
    refine this.trans ?_
    have h2 := sum_inv_sq_le hℓ N
    have e : ∑ k ∈ Icc ℓ N, (N : ℝ) / (c₁ ^ 2 * (k : ℝ) ^ 2) =
        N / c₁ ^ 2 * ∑ k ∈ Icc ℓ N, (1 : ℝ) / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]; exact sum_congr rfl fun k _ => by ring
    rw [e]
    have hc2 : 0 ≤ (N : ℝ) / c₁ ^ 2 := by positivity
    calc 2 * (N / c₁ ^ 2 * ∑ k ∈ Icc ℓ N, (1 : ℝ) / (k : ℝ) ^ 2) ≤ 2 * (N / c₁ ^ 2 * (2 / ℓ)) := by
          nlinarith
      _ = 4 * N / (c₁ ^ 2 * ℓ) := by field_simp; ring
  have hsumB : ∑ i ∈ D, |lam i - lam j| * a i ≤ 2 * (1 + Real.log N) / c₁ := by
    have hb : ∀ i ∈ D, |lam i - lam j| * a i ≤ 1 / (c₁ * labelDist i j) := by
      intro i hi
      have hd1 : (1 : ℝ) ≤ labelDist i j := by exact_mod_cast hℓ.trans (mem_filter.1 hi).2
      have h := hdpos i hi
      have hpos : 0 < c₁ * labelDist i j / N := by positivity
      have habs : 0 < |lam i - lam j| := lt_of_lt_of_le hpos h
      simp only [ha]
      rw [← sq_abs (lam i - lam j)]
      rw [show |lam i - lam j| * (1 / (N * |lam i - lam j| ^ 2)) = 1 / (N * |lam i - lam j|) by
        field_simp]
      apply one_div_le_one_div_of_le (by positivity)
      rw [div_le_iff₀ hNr] at h
      linarith
    refine (sum_le_sum hb).trans ?_
    have := sum_labelDist_le j ℓ (fun k => 1 / (c₁ * (k : ℝ))) (fun k => by positivity)
    refine this.trans ?_
    have h2 := sum_inv_le hℓ N
    have e : ∑ k ∈ Icc ℓ N, 1 / (c₁ * (k : ℝ)) = 1 / c₁ * ∑ k ∈ Icc ℓ N, (1 : ℝ) / (k : ℝ) := by
      rw [Finset.mul_sum]; exact sum_congr rfl fun k _ => by field_simp
    rw [e]
    have hc : 0 ≤ 1 / c₁ := by positivity
    calc 2 * (1 / c₁ * ∑ k ∈ Icc ℓ N, (1 : ℝ) / (k : ℝ)) ≤ 2 * (1 / c₁ * (1 + Real.log N)) := by
          nlinarith
      _ = 2 * (1 + Real.log N) / c₁ := by ring
  have ha0 : ∀ i, 0 ≤ a i := fun i => by simp only [ha]; positivity
  have hY : |∑ i ∈ W, (γ i - P) * a i| ≤
      Cγ * P * (2 * (1 + Real.log N) / c₁ + 4 * N * (ρ + t) / (c₁ ^ 2 * ℓ)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hWD : W ⊆ D := filter_subset _ _
    have hb : ∀ i ∈ W, |(γ i - P) * a i| ≤ Cγ * P * (|lam i - lam j| * a i + (ρ + t) * a i) := by
      intro i hi
      have hw := (mem_filter.1 hi).2
      rw [abs_mul, abs_of_nonneg (ha0 i)]
      have h1 := hγ i hw
      have h2 : |lam i - E| ≤ |lam i - lam j| + ρ := by
        have := abs_sub_le (lam i) (lam j) E
        linarith
      calc |γ i - P| * a i ≤ Cγ * (|lam i - E| + t) * P * a i :=
            mul_le_mul_of_nonneg_right h1 (ha0 i)
        _ ≤ Cγ * (|lam i - lam j| + ρ + t) * P * a i := by
            apply mul_le_mul_of_nonneg_right _ (ha0 i)
            apply mul_le_mul_of_nonneg_right _ hP
            exact mul_le_mul_of_nonneg_left (by linarith) hCγ
        _ = Cγ * P * (|lam i - lam j| * a i + (ρ + t) * a i) := by ring
    refine (sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum, sum_add_distrib, ← Finset.mul_sum]
    have hCP : 0 ≤ Cγ * P := mul_nonneg hCγ hP
    apply mul_le_mul_of_nonneg_left _ hCP
    have hB := (sum_le_sum_of_subset_of_nonneg hWD fun i _ _ =>
      mul_nonneg (abs_nonneg _) (ha0 i)).trans hsumB
    have hA := (sum_le_sum_of_subset_of_nonneg hWD fun i _ _ => ha0 i).trans hsumA
    have : (ρ + t) * ∑ i ∈ W, a i ≤ (ρ + t) * (4 * N / (c₁ ^ 2 * ℓ)) :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    have e : (ρ + t) * (4 * N / (c₁ ^ 2 * ℓ)) = 4 * N * (ρ + t) / (c₁ ^ 2 * ℓ) := by ring
    linarith
  have hExt : |∑ i ∈ X, (Q i - P) * a i| ≤ Cd * P + 64 * P / r₀ ^ 2 := by
    have e : ∑ i ∈ X, (Q i - P) * a i = ∑ i ∈ X, Q i * a i - P * ∑ i ∈ X, a i := by
      rw [Finset.mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
    rw [e]
    have hQX : ∑ i ∈ X, Q i * a i ≤ Cd * P := by
      refine le_trans ?_ hS2
      have hsub : X ⊆ univ.filter (fun i => r₀ / 4 < |lam i - E|) := by
        intro i hi
        simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi ⊢
        exact hi.2
      refine (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => ?_).trans' (le_of_eq ?_)
      · have := hQ i; positivity
      · exact sum_congr rfl fun i _ => by simp only [ha]; ring
    have hQX0 : 0 ≤ ∑ i ∈ X, Q i * a i := sum_nonneg fun i _ => mul_nonneg (hQ i) (ha0 i)
    have haX : ∑ i ∈ X, a i ≤ 64 / r₀ ^ 2 := by
      have hb : ∀ i ∈ X, a i ≤ 64 / (N * r₀ ^ 2) := by
        intro i hi
        have hw : r₀ / 4 < |lam i - E| := not_le.1 (mem_filter.1 hi).2
        have h8 : r₀ / 8 ≤ |lam i - lam j| := by
          have := abs_sub_abs_le_abs_sub (lam i - E) (lam j - E)
          rw [show lam i - E - (lam j - E) = lam i - lam j by ring] at this
          linarith
        have h2 : (r₀ / 8) ^ 2 ≤ (lam i - lam j) ^ 2 := by
          rw [← sq_abs (lam i - lam j)]; exact pow_le_pow_left₀ (by positivity) h8 2
        have hsq : 0 < (lam i - lam j) ^ 2 := lt_of_lt_of_le (by positivity) h2
        simp only [ha]
        rw [div_le_div_iff₀ (mul_pos hNr hsq) (by positivity)]
        nlinarith
      refine (sum_le_sum hb).trans ?_
      rw [sum_const, nsmul_eq_mul]
      have hc : (X.card : ℝ) ≤ N := by
        have := card_le_univ X
        rw [Fintype.card_fin] at this
        exact_mod_cast this
      calc (X.card : ℝ) * (64 / (N * r₀ ^ 2)) ≤ N * (64 / (N * r₀ ^ 2)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = 64 / r₀ ^ 2 := by field_simp
    have haX0 : 0 ≤ ∑ i ∈ X, a i := sum_nonneg fun i _ => ha0 i
    rw [abs_le]
    constructor
    · have : P * ∑ i ∈ X, a i ≤ P * (64 / r₀ ^ 2) := mul_le_mul_of_nonneg_left haX hP
      have e2 : P * (64 / r₀ ^ 2) = 64 * P / r₀ ^ 2 := by ring
      have : 0 ≤ Cd * P := le_trans hQX0 hQX
      linarith
    · have : 0 ≤ P * ∑ i ∈ X, a i := mul_nonneg hP haX0
      have : 0 ≤ 64 * P / r₀ ^ 2 := by positivity
      linarith
  calc |(∑ i ∈ Rt, (Q i - γ i) / (N * (lam i - lam j) ^ 2) +
          ∑ i ∈ Lt, (Q i - γ i) / (N * (lam i - lam j) ^ 2)) +
        ∑ i ∈ W, (γ i - P) * a i + ∑ i ∈ X, (Q i - P) * a i|
      ≤ (|∑ i ∈ Rt, (Q i - γ i) / (N * (lam i - lam j) ^ 2)| +
          |∑ i ∈ Lt, (Q i - γ i) / (N * (lam i - lam j) ^ 2)|) +
        |∑ i ∈ W, (γ i - P) * a i| + |∑ i ∈ X, (Q i - P) * a i| :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (M * (N / (c₁ ^ 2 * ℓ ^ 2)) + M * (N / (c₁ ^ 2 * ℓ ^ 2))) +
        Cγ * P * (2 * (1 + Real.log N) / c₁ + 4 * N * (ρ + t) / (c₁ ^ 2 * ℓ)) +
        (Cd * P + 64 * P / r₀ ^ 2) :=
        add_le_add (add_le_add (add_le_add hR hL) hY) hExt
    _ = _ := by ring

end BlockBand.Critical.RelativeVectors
