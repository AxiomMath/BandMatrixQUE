module

public import BlockBand.Critical.RelativeVectors.Window

/-!
# The phase pairing

Phase averaging the squared absolute value of a bilinear sum leaves only the index pairings
`(i,j) = (k,l)` or `(l,k)`.

*Measure:* `phaseVectorLaw N` (i.i.d. uniform phases `e^{2πiθ}`). *Domain:* every `N`, every
coefficient array; exact identities.

* `phaseLaw_moment`: `∫ θ^a θ̄^b dphaseLaw = δ_{ab}`.
* `phaseVectorLaw_four`: `E[θ_iθ_jθ̄_kθ̄_l] = 1` if `(k,l) = (i,j)` or `(j,i)`, else `0`
  (`i ≠ j`); `phaseVectorLaw_four_conj`: `E[θ̄_iθ_jθ_kθ̄_l] = δ_{ik}δ_{jl}` (`i ≠ j`).
* `phase_pairing`: for `c_ii = 0`,
  `E|Σ_{i,j} c_ij θ_iθ_j|² = Σ_{i,j}(|c_ij|² + Re(c_ij c̄_ji))`, hence `phase_pairing_le`
  `≤ Σ_{i,j}(|c_ij|² + |c_ij||c_ji|)`; `phase_pairing_conj`:
  `E|Σ_{i,j} c_ij θ̄_iθ_j|² = Σ_{i,j}|c_ij|²`.
* `phase_pairing_frame_le`: with `z_i = θ_i ζ_i`, `c_ij = Θ_ij ζ_i^a ζ_j^b`, `Θ_ii = 0` and
  `|ζ_i^a|², |ζ_i^b|² ≤ B`: `E|Σ_{i,j} Θ_ij z_i^a z_j^b|² ≤ B² Σ_{i,j}(|Θ_ij|² + |Θ_ijΘ_ji|)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Set
open scoped ComplexConjugate

variable {N : ℕ}

/-- The phase map `x ↦ e^{2πix}`. -/
def phaseMap (x : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I)

theorem continuous_phaseMap : Continuous phaseMap := by unfold phaseMap; fun_prop

theorem phaseLaw_eq_map : phaseLaw = (volume.restrict (Icc (0 : ℝ) 1)).map phaseMap := rfl

theorem integrable_phaseLaw {g : ℂ → ℂ} (hg : Continuous g) : Integrable g phaseLaw := by
  rw [phaseLaw_eq_map, integrable_map_measure hg.aestronglyMeasurable
    continuous_phaseMap.measurable.aemeasurable]
  exact (hg.comp continuous_phaseMap).integrableOn_Icc

theorem integral_phaseLaw {g : ℂ → ℂ} (hg : Continuous g) :
    ∫ θ, g θ ∂phaseLaw = ∫ x in Icc (0 : ℝ) 1, g (phaseMap x) := by
  rw [phaseLaw_eq_map, integral_map continuous_phaseMap.measurable.aemeasurable
    hg.aestronglyMeasurable]

theorem phaseMap_pow_conj_pow (x : ℝ) (a b : ℕ) :
    phaseMap x ^ a * conj (phaseMap x) ^ b =
      Complex.exp ((((a : ℤ) - b : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * x) := by
  unfold phaseMap
  rw [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  simp only [map_ofNat]
  ring

/-- `∫ θ^a θ̄^b dphaseLaw = δ_{ab}`. -/
theorem phaseLaw_moment (a b : ℕ) :
    ∫ θ, θ ^ a * conj θ ^ b ∂phaseLaw = if a = b then 1 else 0 := by
  rw [integral_phaseLaw (by fun_prop)]
  simp_rw [phaseMap_pow_conj_pow]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hab
  · subst hab
    simp
  · have hne : ((((a : ℤ) - b : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
      refine mul_ne_zero ?_ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
      exact Int.cast_ne_zero.2 (sub_ne_zero.2 (fun h => hab (by exact_mod_cast h)))
    rw [integral_exp_mul_complex hne]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- Exponent of label `m` in `θ_i θ_j`. -/
def pairExp (i j m : Fin N) : ℕ := (if m = i then 1 else 0) + (if m = j then 1 else 0)

theorem prod_pow_pairExp (θ : Fin N → ℂ) (i j : Fin N) :
    ∏ m, θ m ^ pairExp i j m = θ i * θ j := by
  simp only [pairExp, pow_add, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_eq_single i (fun m _ hm => by simp [hm]) (by simp)]; simp
  · rw [Finset.prod_eq_single j (fun m _ hm => by simp [hm]) (by simp)]; simp

/-- The general product moment over `phaseVectorLaw`. -/
theorem phaseVectorLaw_prod_moment (a b : Fin N → ℕ) :
    ∫ θ, ∏ m, (θ m ^ a m * conj (θ m) ^ b m) ∂phaseVectorLaw N =
      if ∀ m, a m = b m then 1 else 0 := by
  unfold phaseVectorLaw
  rw [integral_fintype_prod_eq_prod (fun m (x : ℂ) => x ^ a m * conj x ^ b m)]
  simp_rw [phaseLaw_moment]
  rw [Finset.prod_boole]
  simp

theorem integrable_phaseVectorLaw_monomial (a b : Fin N → ℕ) :
    Integrable (fun θ : Fin N → ℂ => ∏ m, (θ m ^ a m * conj (θ m) ^ b m)) (phaseVectorLaw N) := by
  unfold phaseVectorLaw
  exact Integrable.fintype_prod (f := fun m (x : ℂ) => x ^ a m * conj x ^ b m)
    (fun m => integrable_phaseLaw (by fun_prop))

theorem four_eq_monomial (θ : Fin N → ℂ) (i j k l : Fin N) :
    θ i * θ j * (conj (θ k) * conj (θ l)) =
      ∏ m, (θ m ^ pairExp i j m * conj (θ m) ^ pairExp k l m) := by
  rw [Finset.prod_mul_distrib, prod_pow_pairExp]
  have h : ∏ m, conj (θ m) ^ pairExp k l m = conj (θ k) * conj (θ l) :=
    prod_pow_pairExp (fun m => conj (θ m)) k l
  rw [h]

theorem pairExp_eq_iff {i j k l : Fin N} (hij : i ≠ j) :
    (∀ m, pairExp i j m = pairExp k l m) ↔ (k = i ∧ l = j) ∨ (k = j ∧ l = i) := by
  constructor
  · intro h
    have hi := h i
    have hj := h j
    simp only [pairExp] at hi hj
    split_ifs at hi hj <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) m
    · rfl
    · simp only [pairExp]; omega

/-- `E[θ_iθ_jθ̄_kθ̄_l]` for `i ≠ j`. -/
theorem phaseVectorLaw_four {i j : Fin N} (hij : i ≠ j) (k l : Fin N) :
    ∫ θ, θ i * θ j * (conj (θ k) * conj (θ l)) ∂phaseVectorLaw N =
      (if k = i ∧ l = j then 1 else 0) + (if k = j ∧ l = i then 1 else 0) := by
  simp_rw [four_eq_monomial]
  rw [phaseVectorLaw_prod_moment, if_congr (pairExp_eq_iff hij) rfl rfl]
  by_cases h1 : k = i ∧ l = j
  · have h2 : ¬ (k = j ∧ l = i) := fun h2 => hij (h1.1.symm.trans h2.1)
    rw [ite_eq_left (Or.inl h1), ite_eq_left h1, ite_eq_right h2]; ring
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left (Or.inr h2), ite_eq_right h1, ite_eq_left h2]; ring
    · rw [ite_eq_right (fun h => h.elim h1 h2), ite_eq_right h1, ite_eq_right h2]; ring

theorem sum_sum_ite_and (f : Fin N → Fin N → ℂ) (i j : Fin N) :
    ∑ k, ∑ l, (if k = i ∧ l = j then f k l else 0) = f i j := by
  rw [Finset.sum_eq_single i (fun k _ hk => Finset.sum_eq_zero fun l _ =>
      ite_eq_right (fun h => hk h.1)) (by simp),
    Finset.sum_eq_single j (fun l _ hl => ite_eq_right (fun h => hl h.2)) (by simp)]
  exact ite_eq_left ⟨rfl, rfl⟩

/-- **Phase pairing** (exact form). -/
theorem phase_pairing (c : Fin N → Fin N → ℂ) (hc : ∀ i, c i i = 0) :
    ∫ θ, ‖∑ i, ∑ j, c i j * (θ i * θ j)‖ ^ 2 ∂phaseVectorLaw N =
      ∑ i, ∑ j, (‖c i j‖ ^ 2 + (c i j * conj (c j i)).re) := by
  set X : (Fin N → ℂ) → ℂ := fun θ => ∑ i, ∑ j, c i j * (θ i * θ j)
  have hexp : ∀ θ, ((‖X θ‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, ∑ k, ∑ l,
      c i j * conj (c k l) * (θ i * θ j * (conj (θ k) * conj (θ l))) := by
    intro θ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', show X θ = ∑ i, ∑ j, c i j * (θ i * θ j) from rfl,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul]
    ring
  have hint : ∀ i j k l : Fin N, Integrable (fun θ : Fin N → ℂ =>
      c i j * conj (c k l) * (θ i * θ j * (conj (θ k) * conj (θ l)))) (phaseVectorLaw N) := by
    intro i j k l
    simp_rw [four_eq_monomial]
    exact (integrable_phaseVectorLaw_monomial _ _).const_mul _
  have hC : ∫ θ, ((‖X θ‖ ^ 2 : ℝ) : ℂ) ∂phaseVectorLaw N =
      ∑ i, ∑ j, c i j * (conj (c i j) + conj (c j i)) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint i j k l]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => hint i j k l]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      simp [hc]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint i j k l]
    simp_rw [integral_finsetSum _ fun l _ => hint i j _ l, integral_const_mul,
      phaseVectorLaw_four hij]
    have hsplit : ∀ k l : Fin N, c i j * conj (c k l) *
        ((if k = i ∧ l = j then 1 else 0) + (if k = j ∧ l = i then 1 else 0)) =
        (if k = i ∧ l = j then c i j * conj (c k l) else 0) +
          (if k = j ∧ l = i then c i j * conj (c k l) else 0) := by
      intro k l; split_ifs <;> ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [show (∑ k, ∑ l, if k = i ∧ l = j then c i j * conj (c k l) else 0) =
        c i j * conj (c i j) from sum_sum_ite_and (fun k l => c i j * conj (c k l)) i j,
      show (∑ k, ∑ l, if k = j ∧ l = i then c i j * conj (c k l) else 0) =
        c i j * conj (c j i) from sum_sum_ite_and (fun k l => c i j * conj (c k l)) j i]
    ring
  have hre := congrArg Complex.re hC
  rw [integral_complex_ofReal, Complex.ofReal_re] at hre
  refine hre.trans ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_add, Complex.add_re, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem phase_pairing_le (c : Fin N → Fin N → ℂ) (hc : ∀ i, c i i = 0) :
    ∫ θ, ‖∑ i, ∑ j, c i j * (θ i * θ j)‖ ^ 2 ∂phaseVectorLaw N ≤
      ∑ i, ∑ j, (‖c i j‖ ^ 2 + ‖c i j‖ * ‖c j i‖) := by
  rw [phase_pairing c hc]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => add_le_add le_rfl ?_
  refine (Complex.re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_conj]

/-- `E[θ̄_iθ_jθ_kθ̄_l] = δ_{ik}δ_{jl}` for `i ≠ j`. -/
theorem pairExp_conj_iff {i j k l : Fin N} (hij : i ≠ j) :
    (∀ m, pairExp j k m = pairExp i l m) ↔ (k = i ∧ l = j) := by
  constructor
  · intro h
    have hi := h i
    have hj := h j
    simp only [pairExp] at hi hj
    split_ifs at hi hj <;> omega
  · rintro ⟨rfl, rfl⟩ m
    simp only [pairExp]
    omega

theorem phaseVectorLaw_four_conj {i j : Fin N} (hij : i ≠ j) (k l : Fin N) :
    ∫ θ, θ j * θ k * (conj (θ i) * conj (θ l)) ∂phaseVectorLaw N =
      if k = i ∧ l = j then 1 else 0 := by
  simp_rw [four_eq_monomial]
  rw [phaseVectorLaw_prod_moment, if_congr (pairExp_conj_iff hij) rfl rfl]

/-- **Phase pairing, conjugated version.** -/
theorem phase_pairing_conj (c : Fin N → Fin N → ℂ) (hc : ∀ i, c i i = 0) :
    ∫ θ, ‖∑ i, ∑ j, c i j * (conj (θ i) * θ j)‖ ^ 2 ∂phaseVectorLaw N =
      ∑ i, ∑ j, ‖c i j‖ ^ 2 := by
  set X : (Fin N → ℂ) → ℂ := fun θ => ∑ i, ∑ j, c i j * (conj (θ i) * θ j)
  have hexp : ∀ θ, ((‖X θ‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, ∑ k, ∑ l,
      c i j * conj (c k l) * (θ j * θ k * (conj (θ i) * conj (θ l))) := by
    intro θ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', show X θ = ∑ i, ∑ j, c i j * (conj (θ i) * θ j) from rfl,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  have hint : ∀ i j k l : Fin N, Integrable (fun θ : Fin N → ℂ =>
      c i j * conj (c k l) * (θ j * θ k * (conj (θ i) * conj (θ l)))) (phaseVectorLaw N) := by
    intro i j k l
    simp_rw [four_eq_monomial]
    exact (integrable_phaseVectorLaw_monomial _ _).const_mul _
  have hC : ∫ θ, ((‖X θ‖ ^ 2 : ℝ) : ℂ) ∂phaseVectorLaw N =
      ∑ i, ∑ j, c i j * conj (c i j) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint i j k l]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => hint i j k l]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      simp [hc]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint i j k l]
    simp_rw [integral_finsetSum _ fun l _ => hint i j _ l, integral_const_mul,
      phaseVectorLaw_four_conj hij]
    have hsplit : ∀ k l : Fin N, c i j * conj (c k l) * (if k = i ∧ l = j then 1 else 0) =
        (if k = i ∧ l = j then c i j * conj (c k l) else 0) := by
      intro k l; split_ifs <;> ring
    simp_rw [hsplit]
    exact sum_sum_ite_and (fun k l => c i j * conj (c k l)) i j
  have hre := congrArg Complex.re hC
  rw [integral_complex_ofReal, Complex.ofReal_re] at hre
  refine hre.trans ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **The phase-averaged cross sum**: phases on the vectors, bounded components. -/
theorem phase_pairing_frame_le (Θ : Fin N → Fin N → ℂ) (hΘ : ∀ i, Θ i i = 0)
    (ζa ζb : Fin N → ℂ) {B : ℝ} (ha : ∀ i, ‖ζa i‖ ^ 2 ≤ B) (hb : ∀ i, ‖ζb i‖ ^ 2 ≤ B) :
    ∫ θ, ‖∑ i, ∑ j, Θ i j * ((θ i * ζa i) * (θ j * ζb j))‖ ^ 2 ∂phaseVectorLaw N ≤
      B ^ 2 * ∑ i, ∑ j, (‖Θ i j‖ ^ 2 + ‖Θ i j * Θ j i‖) := by
  set c : Fin N → Fin N → ℂ := fun i j => Θ i j * (ζa i * ζb j)
  have hcz : ∀ i, c i i = 0 := fun i => by simp [c, hΘ]
  have he : ∀ θ : Fin N → ℂ, ∑ i, ∑ j, Θ i j * ((θ i * ζa i) * (θ j * ζb j)) =
      ∑ i, ∑ j, c i j * (θ i * θ j) := fun θ => by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [c]; ring
  simp_rw [he]
  refine (phase_pairing_le c hcz).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hB0 : 0 ≤ B := le_trans (by positivity) (ha i)
  have hai := ha i
  have hbj := hb j
  have haj := ha j
  have hbi := hb i
  have h1 : ‖c i j‖ ^ 2 ≤ B ^ 2 * ‖Θ i j‖ ^ 2 := by
    simp only [c, norm_mul, mul_pow]
    have : ‖ζa i‖ ^ 2 * ‖ζb j‖ ^ 2 ≤ B * B := mul_le_mul hai hbj (by positivity) hB0
    nlinarith [sq_nonneg ‖Θ i j‖]
  have h2 : ‖c i j‖ * ‖c j i‖ ≤ B ^ 2 * ‖Θ i j * Θ j i‖ := by
    simp only [c, norm_mul]
    have hprod : (‖ζa i‖ * ‖ζb j‖) * (‖ζa j‖ * ‖ζb i‖) ≤ B ^ 2 := by
      have e : (‖ζa i‖ * ‖ζb j‖) * (‖ζa j‖ * ‖ζb i‖) =
          (‖ζa i‖ * ‖ζb i‖) * (‖ζa j‖ * ‖ζb j‖) := by ring
      have hi : ‖ζa i‖ * ‖ζb i‖ ≤ B := by nlinarith [sq_nonneg (‖ζa i‖ - ‖ζb i‖)]
      have hj : ‖ζa j‖ * ‖ζb j‖ ≤ B := by nlinarith [sq_nonneg (‖ζa j‖ - ‖ζb j‖)]
      rw [e, sq]
      exact mul_le_mul hi hj (by positivity) hB0
    have h0 : 0 ≤ ‖Θ i j‖ * ‖Θ j i‖ := by positivity
    calc ‖Θ i j‖ * (‖ζa i‖ * ‖ζb j‖) * (‖Θ j i‖ * (‖ζa j‖ * ‖ζb i‖))
        = (‖Θ i j‖ * ‖Θ j i‖) * ((‖ζa i‖ * ‖ζb j‖) * (‖ζa j‖ * ‖ζb i‖)) := by ring
      _ ≤ (‖Θ i j‖ * ‖Θ j i‖) * B ^ 2 := mul_le_mul_of_nonneg_left hprod h0
      _ = B ^ 2 * (‖Θ i j‖ * ‖Θ j i‖) := by ring
  rw [mul_add]
  exact add_le_add h1 h2

end BlockBand.Critical.RelativeVectors
