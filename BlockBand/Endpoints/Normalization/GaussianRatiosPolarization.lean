module

public import BlockBand.Endpoints.Normalization.GaussianRatiosPalm

/-!
# Polarization: mixed moments of positive clocks under the Palm law

Replacing each `B_j` by `D + B_j ⪰ 0`, the real polarization identity compares all fixed mixed
moments of the positive clocks, uniformly.

* `polarization`: in every commutative ring,
  `Σ_{S ⊆ [r]} (-1)^{r-|S|} (Σ_{m∈S} x_m)^r = r! Π_m x_m`.
* `palmExpect_eq_integral_of_continuous`: `Â[φ] = ∫ φ dÂ` for every continuous `φ` (continuous
  functions are bounded on the unit ball, which carries `Â`).
* `mixed_moment_uniform` (the mixed-moment comparison), from `FreshPalmContract` and the
  normalizer lower bound `NormalizerLowerBound` (`hZ`). Fixed first: the constants
  `A, c₀, r₀, s₀, v₀`, a finite index type `ι`, a trace ratio `R`, the order `r` and the
  multi-index `f : Fin r → ι`; then for every `η > 0` there is `N₀`; for `N ≥ N₀`, every `F` in
  the class, every family `P : ι → M_N(ℂ)` of positive semidefinite matrices, every `T > 0` with
  `Tr(ΓP_i) ≤ R T` for all `i`, and every `M` with `MM* = Γ`:
  `Z > 0` and `|Â[Π_m N v*P_{f m}v/T] - E_g Π_m g*M*P_{f m}Mg/T| ≤ η`.
  (No norm, condition-number or Loewner restriction on `P`.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexOrder Matrix

/-!
## The polarization identity
-/

theorem sign_indicator_sum {r : ℕ} {R : Type*} [CommRing R] (p : Fin r → Fin r) :
    ∑ S : Finset (Fin r), (-1 : R) ^ Sᶜ.card * ∏ i, (if p i ∈ S then (1 : R) else 0) =
      if Function.Surjective p then 1 else 0 := by
  classical
  have key := Fintype.prod_add (fun _ : Fin r => (1 : R))
    (fun a => -(if a ∈ Set.range p then (0 : R) else 1))
  have hl : ∏ a : Fin r, ((1 : R) + -(if a ∈ Set.range p then (0 : R) else 1)) =
      if Function.Surjective p then 1 else 0 := by
    have : ∀ a : Fin r, ((1 : R) + -(if a ∈ Set.range p then (0 : R) else 1)) =
        if a ∈ Set.range p then 1 else 0 := fun a => by split_ifs <;> simp
    simp_rw [this]
    rw [Finset.prod_boole]
    simp only [Finset.mem_univ, true_implies, Set.mem_range]
    exact if_congr Iff.rfl rfl rfl
  rw [hl] at key
  rw [key]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hnot : ∀ a, (if a ∈ Set.range p then (0 : R) else 1) =
      if a ∉ Set.range p then 1 else 0 := fun a => by split_ifs <;> simp_all
  simp_rw [hnot]
  rw [Finset.prod_const_one, one_mul, Finset.prod_neg, Finset.prod_boole, Finset.prod_boole]
  congr 1
  have : (∀ a ∈ Sᶜ, ¬ a ∈ Set.range p) ↔ ∀ i ∈ (Finset.univ : Finset (Fin r)), p i ∈ S := by
    constructor
    · intro h i _
      by_contra hi
      exact h (p i) (Finset.mem_compl.mpr hi) ⟨i, rfl⟩
    · rintro h a ha ⟨i, rfl⟩
      exact Finset.mem_compl.mp ha (h i (Finset.mem_univ _))
  by_cases h : ∀ a ∈ Sᶜ, ¬ a ∈ Set.range p
  · rw [ite_eq_left (this.mp h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (this.mpr h')), ite_eq_right h]

theorem sum_surjective_eq_perm {r : ℕ} {R : Type*} [CommRing R] (f : (Fin r → Fin r) → R) :
    ∑ p : Fin r → Fin r, (if Function.Surjective p then f p else 0) =
      ∑ σ : Equiv.Perm (Fin r), f σ := by
  classical
  rw [← Finset.sum_filter]
  have hmap : (Finset.univ.filter fun p : Fin r → Fin r => Function.Surjective p) =
      (Finset.univ : Finset (Equiv.Perm (Fin r))).map
        ⟨fun σ : Equiv.Perm (Fin r) => (σ : Fin r → Fin r),
          fun a b h => Equiv.ext (congrFun h)⟩ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hp
      exact ⟨Equiv.ofBijective p ⟨Finite.injective_iff_surjective.mpr hp, hp⟩, rfl⟩
    · rintro ⟨σ, rfl⟩
      exact σ.surjective
  rw [hmap, Finset.sum_map]
  rfl

/-- **Real polarization identity**:
`Σ_{S ⊆ [r]} (-1)^{r-|S|} (Σ_{m∈S} x_m)^r = r! x_1 ⋯ x_r`. -/
theorem polarization {R : Type*} [CommRing R] (r : ℕ) (x : Fin r → R) :
    ∑ S : Finset (Fin r), (-1 : R) ^ Sᶜ.card * (∑ m ∈ S, x m) ^ r =
      (r.factorial : R) * ∏ m, x m := by
  classical
  have hexp : ∀ S : Finset (Fin r), (∑ m ∈ S, x m) ^ r =
      ∑ p : Fin r → Fin r, (∏ i, (if p i ∈ S then (1 : R) else 0)) * ∏ i, x (p i) := by
    intro S
    have : (∑ m ∈ S, x m) = ∑ m, (if m ∈ S then x m else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [this, Fintype.sum_pow]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ p : Fin r → Fin r, ∑ S : Finset (Fin r), (-1 : R) ^ Sᶜ.card *
      ((∏ i, (if p i ∈ S then (1 : R) else 0)) * ∏ i, x (p i)) =
      if Function.Surjective p then ∏ i, x (p i) else 0 := by
    intro p
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, sign_indicator_sum]
    split_ifs <;> simp
  simp_rw [this]
  rw [sum_surjective_eq_perm (fun p => ∏ i, x (p i))]
  have : ∀ σ : Equiv.Perm (Fin r), ∏ i, x (σ i) = ∏ m, x m := fun σ => Equiv.prod_comp σ x
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-!
## Continuous observables of the Palm law
-/

variable {N : ℕ}

theorem isCompact_unitBall : IsCompact {v : Fin N → ℂ | sqNorm v ≤ 1} := by
  have hc : Continuous (sqNorm (N := N)) := by
    unfold sqNorm; fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hc continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin N → ℂ)) (r := 1)).subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq] at hv
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h1 : Complex.normSq (v i) ≤ 1 :=
    le_trans (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
      (Finset.mem_univ i)) hv
  rw [Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (v i)]

theorem exists_bound_on_ball {φ : (Fin N → ℂ) → ℝ} (hφ : Continuous φ) :
    ∃ B : ℝ, ∀ v, sqNorm v ≤ 1 → |φ v| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_unitBall.exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨B, fun v hv => by simpa [Real.norm_eq_abs] using hB v hv⟩

theorem palmExpect_eq_integral_of_continuous (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    {φ : (Fin N → ℂ) → ℝ} (hφ : Continuous φ) :
    palmExpect F c₀ E φ = ∫ v, φ v ∂palmMeasure F c₀ E := by
  obtain ⟨B, hB⟩ := exists_bound_on_ball hφ
  exact palmExpect_eq_integral F c₀ E hφ.measurable hB

theorem integrable_palmMeasure_of_continuous (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    {φ : (Fin N → ℂ) → ℝ} (hφ : Continuous φ) : Integrable φ (palmMeasure F c₀ E) := by
  obtain ⟨B, hB⟩ := exists_bound_on_ball hφ
  exact integrable_palmMeasure F c₀ E hφ.measurable hB

/-!
## Linear algebra of the clocks
-/

theorem quadForm_add (A B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    quadForm (A + B) v = quadForm A v + quadForm B v := by
  unfold quadForm; rw [add_mulVec, dotProduct_add, Complex.add_re]

theorem quadForm_smul (c : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    quadForm ((c : ℂ) • A) v = c * quadForm A v := by
  unfold quadForm; rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem quadForm_sum {s : Type*} (t : Finset s) (A : s → Matrix (Fin N) (Fin N) ℂ)
    (v : Fin N → ℂ) : quadForm (∑ m ∈ t, A m) v = ∑ m ∈ t, quadForm (A m) v := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [quadForm]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, quadForm_add, ih]

theorem traceAgainst_add (Γ A B : Matrix (Fin N) (Fin N) ℂ) :
    traceAgainst Γ (A + B) = traceAgainst Γ A + traceAgainst Γ B := by
  unfold traceAgainst; rw [Matrix.mul_add, trace_add, Complex.add_re]

theorem traceAgainst_finset_sum {s : Type*} (t : Finset s) (Γ : Matrix (Fin N) (Fin N) ℂ)
    (A : s → Matrix (Fin N) (Fin N) ℂ) :
    traceAgainst Γ (∑ m ∈ t, A m) = ∑ m ∈ t, traceAgainst Γ (A m) := by
  unfold traceAgainst; rw [Matrix.mul_sum, trace_sum, Complex.re_sum]

theorem posSemidef_finset_sum {s : Type*} (t : Finset s) {A : s → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ m, (A m).PosSemidef) : (∑ m ∈ t, A m).PosSemidef := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using PosSemidef.zero
  | insert a t ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

/-- The Palm clock vector `y_i(v) = N v*P_iv / T`. -/
def palmClocks {ι : Type*} (N : ℕ) (P : ι → Matrix (Fin N) (Fin N) ℂ) (T : ℝ) (v : Fin N → ℂ) :
    ι → ℝ := fun i => (N : ℝ) * quadForm (P i) v / T

/-- The Gaussian clock vector `ỹ_i(x) = x*P_ix / T` (evaluated at `x = Mg`). -/
def gaussClocks {ι : Type*} (P : ι → Matrix (Fin N) (Fin N) ℂ) (T : ℝ) (x : Fin N → ℂ) :
    ι → ℝ := fun i => quadForm (P i) x / T

/-- The mixed monomial `Π_m y_{f m}`. -/
def monomial {ι : Type*} {r : ℕ} (f : Fin r → ι) (y : ι → ℝ) : ℝ := ∏ m, y (f m)

/-- The polarization matrices `Y_S = T⁻¹ Σ_{m∈S} P_{f m}`. -/
def polMatrix {ι : Type*} {r : ℕ} (P : ι → Matrix (Fin N) (Fin N) ℂ) (T : ℝ) (f : Fin r → ι)
    (S : Finset (Fin r)) : Matrix (Fin N) (Fin N) ℂ :=
  ((T⁻¹ : ℝ) : ℂ) • ∑ m ∈ S, P (f m)

theorem quadForm_polMatrix {ι : Type*} {r : ℕ} (P : ι → Matrix (Fin N) (Fin N) ℂ) (T : ℝ)
    (f : Fin r → ι) (S : Finset (Fin r)) (x : Fin N → ℂ) :
    quadForm (polMatrix P T f S) x = ∑ m ∈ S, quadForm (P (f m)) x / T := by
  unfold polMatrix
  rw [quadForm_smul, quadForm_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [div_eq_inv_mul]

theorem monomial_palmClocks_eq {ι : Type*} {r : ℕ} (P : ι → Matrix (Fin N) (Fin N) ℂ) (T : ℝ)
    (f : Fin r → ι) (v : Fin N → ℂ) :
    monomial f (palmClocks N P T v) = (r.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin r),
      (-1 : ℝ) ^ Sᶜ.card * ((N : ℝ) * quadForm (polMatrix P T f S) v) ^ r := by
  have h := polarization r fun m => palmClocks N P T v (f m)
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  unfold monomial
  rw [eq_inv_mul_iff_mul_eq₀ hfac, ← h]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 2
  rw [quadForm_polMatrix, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by unfold palmClocks; ring

theorem monomial_gaussClocks_eq {ι : Type*} {r : ℕ} (P : ι → Matrix (Fin N) (Fin N) ℂ) (T : ℝ)
    (f : Fin r → ι) (x : Fin N → ℂ) :
    monomial f (gaussClocks P T x) = (r.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin r),
      (-1 : ℝ) ^ Sᶜ.card * quadForm (polMatrix P T f S) x ^ r := by
  have h := polarization r fun m => gaussClocks P T x (f m)
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  unfold monomial
  rw [eq_inv_mul_iff_mul_eq₀ hfac, ← h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [quadForm_polMatrix]
  rfl

theorem polMatrix_posSemidef {ι : Type*} {r : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ}
    (hP : ∀ i, (P i).PosSemidef) {T : ℝ} (hT : 0 < T) (f : Fin r → ι) (S : Finset (Fin r)) :
    (polMatrix P T f S).PosSemidef := by
  unfold polMatrix
  have h : 0 ≤ ((T⁻¹ : ℝ) : ℂ) := by exact_mod_cast (inv_pos.mpr hT).le
  exact (posSemidef_finset_sum S fun m => hP (f m)).smul h

theorem traceAgainst_polMatrix_le {ι : Type*} {r : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ}
    {Γ : Matrix (Fin N) (Fin N) ℂ} {T R : ℝ} (hT : 0 < T) (hR' : 0 ≤ R)
    (hR : ∀ i, traceAgainst Γ (P i) ≤ R * T) (f : Fin r → ι) (S : Finset (Fin r)) :
    traceAgainst Γ (polMatrix P T f S) ≤ r * R := by
  have hR0 : ∀ i, T⁻¹ * traceAgainst Γ (P i) ≤ R := fun i => by
    rw [inv_mul_eq_div, div_le_iff₀ hT]; exact hR i
  unfold polMatrix traceAgainst
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have : (Γ * ∑ m ∈ S, P (f m)).trace.re = ∑ m ∈ S, traceAgainst Γ (P (f m)) :=
    traceAgainst_finset_sum S Γ _
  rw [this, Finset.mul_sum]
  calc ∑ m ∈ S, T⁻¹ * traceAgainst Γ (P (f m)) ≤ ∑ _m ∈ S, R :=
        Finset.sum_le_sum fun m _ => hR0 _
    _ = S.card * R := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ r * R := by
        refine mul_le_mul_of_nonneg_right ?_ hR'
        exact_mod_cast (Finset.card_le_univ S).trans (by simp)

theorem palmExpect_linear_comb (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) {s : Type*}
    (t : Finset s) (a : s → ℝ) (φ : s → (Fin N → ℂ) → ℝ) (hφ : ∀ S, Continuous (φ S)) (c : ℝ) :
    palmExpect F c₀ E (fun v => c * ∑ S ∈ t, a S * φ S v) =
      c * ∑ S ∈ t, a S * palmExpect F c₀ E (φ S) := by
  have hc : Continuous fun v => c * ∑ S ∈ t, a S * φ S v :=
    continuous_const.mul (continuous_finsetSum _ fun S _ => continuous_const.mul (hφ S))
  rw [palmExpect_eq_integral_of_continuous F c₀ E hc, integral_const_mul,
    integral_finsetSum _ fun S _ =>
      (integrable_palmMeasure_of_continuous F c₀ E (hφ S)).const_mul (a S)]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [integral_const_mul, palmExpect_eq_integral_of_continuous F c₀ E (hφ S)]

/-- **Uniform mixed-moment comparison**, from `FreshPalmContract` and the normalizer lower bound
`hZ`. -/
theorem mixed_moment_uniform (hP : FreshPalmContract) (hZ : NormalizerLowerBound)
    {A c₀ r₀ s₀ v₀ : ℝ} (hc : FreshConstants c₀ r₀ s₀ v₀) {ι : Type*} (R : ℝ) (hR0 : 0 ≤ R)
    {r : ℕ} (f : Fin r → ι) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
      FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ P : ι → Matrix (Fin N) (Fin N) ℂ, (∀ i, (P i).PosSemidef) →
      ∀ T : ℝ, 0 < T → (∀ i, traceAgainst (freshGamma F c₀ E) (P i) ≤ R * T) →
      ∀ M : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = freshGamma F c₀ E →
        0 < palmMass F c₀ E ∧
        |palmExpect F c₀ E (fun v => monomial f (palmClocks N P T v)) -
            ∫ g, monomial f (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N)| ≤ η := by
  classical
  set K : ℝ := (2 : ℝ) ^ r * (r * R + 1) ^ r with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨N₀, hN₀⟩ := palm_quadForm_moment_uniform hP hZ (A := A) hc r (η / K) (by positivity)
  refine ⟨N₀, fun N hN F E hF P hPsd T hT hR M hM => ?_⟩
  have hZpos := (hN₀ N hN F E hF 0 PosSemidef.zero M hM).1
  refine ⟨hZpos, ?_⟩
  set Γ := freshGamma F c₀ E
  set sgn : Finset (Fin r) → ℝ := fun S => (-1 : ℝ) ^ Sᶜ.card
  set φ : Finset (Fin r) → (Fin N → ℂ) → ℝ := fun S v =>
    ((N : ℝ) * quadForm (polMatrix P T f S) v) ^ r
  set γ : Finset (Fin r) → ℝ := fun S =>
    ∫ g, quadForm (polMatrix P T f S) (M *ᵥ g) ^ r ∂circularVectorLaw (Fin N)
  have hφc : ∀ S, Continuous (φ S) := fun S =>
    (continuous_const.mul (continuous_quadForm' _)).pow r
  have hpalm : palmExpect F c₀ E (fun v => monomial f (palmClocks N P T v)) =
      (r.factorial : ℝ)⁻¹ * ∑ S, sgn S * palmExpect F c₀ E (φ S) := by
    simp_rw [monomial_palmClocks_eq]
    exact palmExpect_linear_comb F c₀ E Finset.univ sgn φ hφc _
  have hgauss : ∫ g, monomial f (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N) =
      (r.factorial : ℝ)⁻¹ * ∑ S, sgn S * γ S := by
    simp_rw [monomial_gaussClocks_eq]
    rw [integral_const_mul, integral_finsetSum _ fun S _ =>
      (integrable_quadForm_mulVec_pow (polMatrix_posSemidef hPsd hT f S) M r).const_mul _]
    congr 1
    exact Finset.sum_congr rfl fun S _ => integral_const_mul _ _
  rw [hpalm, hgauss, ← mul_sub, ← Finset.sum_sub_distrib]
  have hterm : ∀ S : Finset (Fin r), |sgn S * palmExpect F c₀ E (φ S) - sgn S * γ S| ≤ η / K *
      (r * R + 1) ^ r := by
    intro S
    have hb := (hN₀ N hN F E hF (polMatrix P T f S) (polMatrix_posSemidef hPsd hT f S) M hM).2
    have htr := traceAgainst_polMatrix_le (Γ := Γ) hT hR0 hR f S
    have htr0 : 0 ≤ traceAgainst Γ (polMatrix P T f S) :=
      BlockBand.Endpoints.Clock.traceAgainst_nonneg
        (BlockBand.Endpoints.Clock.freshGamma_posSemidef F hc.1.le E)
        (polMatrix_posSemidef hPsd hT f S)
    rw [← mul_sub, abs_mul]
    have hs : |sgn S| = 1 := by simp [sgn]
    rw [hs, one_mul]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact pow_le_pow_left₀ htr0 (by linarith) r
  have hfac : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hcard : ((Finset.univ : Finset (Finset (Fin r))).card : ℝ) = 2 ^ r := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]; push_cast; ring
  rw [abs_mul, abs_of_pos (inv_pos.mpr (by linarith))]
  calc (r.factorial : ℝ)⁻¹ * |∑ S, (sgn S * palmExpect F c₀ E (φ S) - sgn S * γ S)| ≤
        1 * ∑ S : Finset (Fin r), η / K * (r * R + 1) ^ r := by
        refine mul_le_mul (inv_le_one_of_one_le₀ hfac) ?_ (abs_nonneg _) zero_le_one
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => hterm S)
    _ = η := by
        rw [one_mul, Finset.sum_const, nsmul_eq_mul, hcard, hK]
        field_simp

end BlockBand.Endpoints.Normalization
