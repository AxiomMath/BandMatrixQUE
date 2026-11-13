module

public import BlockBand.DeterminantScore.NegativeSpreadLaw

/-!
# Convexity facts for the inverse-moment clause of the negative spread

* the fixed-inertia chamber is open and convex (`isOpen_chamber`, `convex_chamber`);
* `curvatureForm ≥ 0` for `t > 0`, and a `C²` function with nonnegative second derivative on an
  open convex set is convex (`convexOn_of_iteratedFDeriv_two_nonneg`): with the spectral
  curvature identity this makes `𝒰` convex on the chamber;
* `f = spreadF = (Σ_jλ_j⁻²)^{-1/2}` is concave on the chamber (`spreadF_concave`). Instead of
  computing `D²f ≤ 0` after `x_j = |λ_j|`, the sign change is linear on the chamber
  (`abs_combo_of_mem_chamber`) and concavity of the `-2` power mean is the reverse Minkowski
  inequality `sum_inv_sq_add_le`, from convexity of `x ↦ x⁻²` (`convexOn_zpow`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.NegativeSpread

open BlockBand.DeterminantScore
open scoped ContDiff

variable {m : ℕ}

theorem convex_chamber (ℓ : ℕ) : Convex ℝ (chamber m ℓ) := by
  refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab => ?_
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨fun i j hij => ?_, fun k => ⟨fun hk => ?_, fun hk => ?_⟩⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx1 hij; have := hy1 hij
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := (hx2 k).1 hk; have := (hy2 k).1 hk
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := (hx2 k).2 hk; have := (hy2 k).2 hk
    nlinarith

theorem isOpen_chamber (ℓ : ℕ) : IsOpen (chamber m ℓ) := by
  have hset : chamber m ℓ = (⋂ i : Fin m, ⋂ j : Fin m, {lam : Fin m → ℝ | i < j → lam i < lam j}) ∩
      ⋂ k : Fin m, ({lam : Fin m → ℝ | k.val < ℓ → lam k < 0} ∩
        {lam : Fin m → ℝ | ℓ ≤ k.val → 0 < lam k}) := by
    ext lam
    simp only [chamber, StrictMono, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun k => IsOpen.inter ?_ ?_)
  · by_cases hij : i < j
    · simpa [hij] using isOpen_lt (continuous_apply i) (continuous_apply j)
    · simp [hij]
  · by_cases hk : k.val < ℓ
    · simpa [hk] using isOpen_lt (continuous_apply k) continuous_const
    · simp [hk]
  · by_cases hk : ℓ ≤ k.val
    · simpa [hk] using isOpen_lt continuous_const (continuous_apply k)
    · simp [hk]

theorem curvatureForm_nonneg {t : ℝ} (ht : 0 < t) (lam a : Fin m → ℝ) :
    0 ≤ curvatureForm t lam a := by
  unfold curvatureForm
  have h1 : 0 ≤ t⁻¹ * ∑ j, a j ^ 2 := by positivity
  have h2 : 0 ≤ 2 * ∑ j, a j ^ 2 / lam j ^ 2 := by positivity
  have h3 : 0 ≤ ∑ k, ∑ j, (if k < j then (a k - a j) ^ 2 / (lam k - lam j) ^ 2 else 0) :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

/-- A function `C²` on an open convex set with nonnegative second derivative is convex there. -/
theorem convexOn_of_iteratedFDeriv_two_nonneg {s : Set (Fin m → ℝ)} (hs : Convex ℝ s)
    (ho : IsOpen s) {𝒰 : (Fin m → ℝ) → ℝ} (h2 : ContDiffOn ℝ 2 𝒰 s)
    (hH : ∀ p ∈ s, ∀ v, 0 ≤ iteratedFDeriv ℝ 2 𝒰 p (fun _ => v)) : ConvexOn ℝ s 𝒰 := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  set v := y - x
  set L : ℝ → (Fin m → ℝ) := fun s => x + s • v with hL
  have hLc : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
  set S := L ⁻¹' s
  have hSo : IsOpen S := ho.preimage hLc
  have hSc : Convex ℝ S := by
    refine fun p hp q hq c d hc hd hcd => ?_
    have : L (c • p + d • q) = c • L p + d • L q := by
      simp only [hL, smul_eq_mul, add_smul, smul_add, mul_smul]
      have hx' : x = c • x + d • x := by rw [← add_smul, hcd, one_smul]
      calc x + (c • p • v + d • q • v) = (c • x + d • x) + (c • p • v + d • q • v) := by
            rw [← hx']
        _ = _ := by abel
    show L (c • p + d • q) ∈ s
    rw [this]; exact hs hp hq hc hd hcd
  have hLd : ∀ r, HasDerivAt L v r := fun r => by
    have h := ((hasDerivAt_id r).smul_const v).const_add x
    rw [one_smul] at h
    exact h
  have hat : ∀ r ∈ S, ContDiffAt ℝ 2 𝒰 (L r) := fun r hr => h2.contDiffAt (ho.mem_nhds hr)
  set g : ℝ → ℝ := fun r => 𝒰 (L r)
  set g' : ℝ → ℝ := fun r => fderiv ℝ 𝒰 (L r) v
  set g'' : ℝ → ℝ := fun r => fderiv ℝ (fderiv ℝ 𝒰) (L r) v v
  have hg : ∀ r ∈ S, HasDerivAt g (g' r) r := fun r hr => by
    have hd := ((hat r hr).differentiableAt (by norm_num)).hasFDerivAt
    exact hd.comp_hasDerivAt r (hLd r)
  have hg' : ∀ r ∈ S, HasDerivAt g' (g'' r) r := fun r hr => by
    have hd := (((hat r hr).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
    have h1 := hd.comp_hasDerivAt r (hLd r)
    exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt r h1
  have hconv : ConvexOn ℝ S g := by
    refine convexOn_of_hasDerivWithinAt2_nonneg hSc (f' := g') (f'' := g'')
      (fun r hr => (hg r hr).continuousAt.continuousWithinAt) ?_ ?_ ?_ <;>
      rw [hSo.interior_eq]
    · exact fun r hr => (hg r hr).hasDerivWithinAt
    · exact fun r hr => (hg' r hr).hasDerivWithinAt
    · intro r hr
      have := hH (L r) hr v
      rw [iteratedFDeriv_two_apply] at this
      exact this
  have h0 : (0 : ℝ) ∈ S := by show L 0 ∈ s; simpa [hL] using hx
  have h1 : (1 : ℝ) ∈ S := by show L 1 ∈ s; simpa [hL, v] using hy
  have key := hconv.2 h0 h1 ha hb hab
  have e : L (a • (0 : ℝ) + b • 1) = a • x + b • y := by
    simp only [hL, v, smul_eq_mul, mul_zero, zero_add, mul_one]
    rw [show a = 1 - b by linarith, sub_smul, one_smul, smul_sub]; abel
  simp only [g] at key
  rw [e] at key
  simpa [hL, v] using key

theorem inv_sq_add_le {x y A B : ℝ} (hx : 0 < x) (hy : 0 < y) (hA : 0 < A) (hB : 0 < B) :
    (x + y)⁻¹ ^ 2 ≤ ((A + B) ^ 2)⁻¹ *
      (A / (A + B) * (A ^ 2 * x⁻¹ ^ 2) + B / (A + B) * (B ^ 2 * y⁻¹ ^ 2)) := by
  have hAB : 0 < A + B := by linarith
  have key := (convexOn_zpow (𝕜 := ℝ) (-2)).2 (show x / A ∈ Set.Ioi 0 from div_pos hx hA)
    (show y / B ∈ Set.Ioi 0 from div_pos hy hB) (div_pos hA hAB).le (div_pos hB hAB).le
    (by field_simp)
  have e : (A / (A + B)) • (x / A) + (B / (A + B)) • (y / B) = (x + y) / (A + B) := by
    simp only [smul_eq_mul]; field_simp
  simp only at key
  rw [e] at key
  simp only [smul_eq_mul, zpow_neg, zpow_ofNat] at key
  have e2 : ((x + y) / (A + B)) ^ 2 = (x + y) ^ 2 / (A + B) ^ 2 := div_pow _ _ _
  rw [e2, inv_div] at key
  have e3 : (x + y)⁻¹ ^ 2 = ((A + B) ^ 2)⁻¹ * ((A + B) ^ 2 / (x + y) ^ 2) := by
    field_simp
  rw [e3]
  refine mul_le_mul_of_nonneg_left (key.trans_eq ?_) (by positivity)
  field_simp

/-- Reverse Minkowski for the `-2` power mean. -/
theorem sum_inv_sq_add_le {x y : Fin m → ℝ} (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hSx : ∑ j, (x j)⁻¹ ^ 2 = (A ^ 2)⁻¹)
    (hSy : ∑ j, (y j)⁻¹ ^ 2 = (B ^ 2)⁻¹) :
    ∑ j, (x j + y j)⁻¹ ^ 2 ≤ ((A + B) ^ 2)⁻¹ := by
  have hAB : 0 < A + B := by linarith
  calc ∑ j, (x j + y j)⁻¹ ^ 2 ≤ ∑ j, ((A + B) ^ 2)⁻¹ *
        (A / (A + B) * (A ^ 2 * (x j)⁻¹ ^ 2) + B / (A + B) * (B ^ 2 * (y j)⁻¹ ^ 2)) :=
        Finset.sum_le_sum fun j _ => inv_sq_add_le (hx j) (hy j) hA hB
    _ = ((A + B) ^ 2)⁻¹ * (A / (A + B) * (A ^ 2 * ∑ j, (x j)⁻¹ ^ 2) +
          B / (A + B) * (B ^ 2 * ∑ j, (y j)⁻¹ ^ 2)) := by
        rw [← Finset.mul_sum]; simp only [Finset.mul_sum, Finset.sum_add_distrib]
    _ = ((A + B) ^ 2)⁻¹ := by
        rw [hSx, hSy]; field_simp

/-- `f(λ) = U(λ)^{-1/2} = (Σλ_j⁻²)^{-1/2}`. -/
def spreadF (lam : Fin m → ℝ) : ℝ := Real.sqrt (invSqSum lam)⁻¹

theorem spreadF_nonneg (lam : Fin m → ℝ) : 0 ≤ spreadF lam := Real.sqrt_nonneg _

theorem spreadF_sq (lam : Fin m → ℝ) : spreadF lam ^ 2 = (invSqSum lam)⁻¹ :=
  Real.sq_sqrt (inv_nonneg.2 (invSqSum_nonneg _))

theorem measurable_spreadF : Measurable (spreadF (m := m)) :=
  Real.continuous_sqrt.measurable.comp measurable_invSqSum.inv

theorem abs_combo_of_mem_chamber {ℓ : ℕ} {lam mu : Fin m → ℝ} (hl : lam ∈ chamber m ℓ)
    (hu : mu ∈ chamber m ℓ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (j : Fin m) :
    |a * lam j + b * mu j| = a * |lam j| + b * |mu j| := by
  rcases lt_or_ge j.val ℓ with hj | hj
  · have h1 := (hl.2 j).1 hj; have h2 := (hu.2 j).1 hj
    rw [abs_of_neg h1, abs_of_neg h2, abs_of_nonpos (by nlinarith)]; ring
  · have h1 := (hl.2 j).2 hj; have h2 := (hu.2 j).2 hj
    rw [abs_of_pos h1, abs_of_pos h2, abs_of_nonneg (by nlinarith)]

/-- Concavity of `f = U^{-1/2}` on the chamber. -/
theorem spreadF_concave (hm : 0 < m) {ℓ : ℕ} {lam mu : Fin m → ℝ} (hl : lam ∈ chamber m ℓ)
    (hu : mu ∈ chamber m ℓ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    a * spreadF lam + (1 - a) * spreadF mu ≤ spreadF (a • lam + (1 - a) • mu) := by
  have hb : 0 < 1 - a := by linarith
  have hnl := ne_zero_of_mem_chamber hl
  have hnu := ne_zero_of_mem_chamber hu
  have hSl := invSqSum_pos hnl ⟨0, hm⟩
  have hSu := invSqSum_pos hnu ⟨0, hm⟩
  set A' := spreadF lam
  set B' := spreadF mu
  have hA' : 0 < A' := Real.sqrt_pos.2 (inv_pos.2 hSl)
  have hB' : 0 < B' := Real.sqrt_pos.2 (inv_pos.2 hSu)
  have hA2 : A' ^ 2 = (invSqSum lam)⁻¹ := spreadF_sq lam
  have hB2 : B' ^ 2 = (invSqSum mu)⁻¹ := spreadF_sq mu
  set c := a • lam + (1 - a) • mu
  have hc : c ∈ chamber m ℓ := convex_chamber ℓ hl hu ha.le hb.le (by ring)
  have hSc := invSqSum_pos (ne_zero_of_mem_chamber hc) ⟨0, hm⟩
  have habs : ∀ (z : Fin m → ℝ) (j : Fin m), (z j)⁻¹ ^ 2 = (|z j|)⁻¹ ^ 2 := fun z j => by
    rw [inv_pow, inv_pow, sq_abs]
  have hsumx : ∑ j, (a * |lam j|)⁻¹ ^ 2 = ((a * A') ^ 2)⁻¹ := by
    have : ∀ j, (a * |lam j|)⁻¹ ^ 2 = (a ^ 2)⁻¹ * (lam j)⁻¹ ^ 2 := fun j => by
      rw [habs lam j, mul_inv, mul_pow, inv_pow]
    simp_rw [this]
    rw [← Finset.mul_sum, ← invSqSum, mul_pow, hA2, mul_inv, inv_inv]
  have hsumy : ∑ j, ((1 - a) * |mu j|)⁻¹ ^ 2 = (((1 - a) * B') ^ 2)⁻¹ := by
    have : ∀ j, ((1 - a) * |mu j|)⁻¹ ^ 2 = ((1 - a) ^ 2)⁻¹ * (mu j)⁻¹ ^ 2 := fun j => by
      rw [habs mu j, mul_inv, mul_pow, inv_pow]
    simp_rw [this]
    rw [← Finset.mul_sum, ← invSqSum, mul_pow, hB2, mul_inv, inv_inv]
  have hmain := sum_inv_sq_add_le (x := fun j => a * |lam j|) (y := fun j => (1 - a) * |mu j|)
    (fun j => mul_pos ha (abs_pos.2 (hnl j))) (fun j => mul_pos hb (abs_pos.2 (hnu j)))
    (mul_pos ha hA') (mul_pos hb hB') hsumx hsumy
  have hcS : invSqSum c = ∑ j, (a * |lam j| + (1 - a) * |mu j|)⁻¹ ^ 2 := by
    unfold invSqSum
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [habs c j]
    simp only [c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [abs_combo_of_mem_chamber hl hu ha.le hb.le j]
  rw [← hcS] at hmain
  have hP : 0 ≤ a * A' + (1 - a) * B' := by positivity
  have h2 : (a * A' + (1 - a) * B') ^ 2 ≤ (invSqSum c)⁻¹ :=
    (le_inv_comm₀ (by positivity) hSc).2 hmain
  calc a * A' + (1 - a) * B' = Real.sqrt ((a * A' + (1 - a) * B') ^ 2) := (Real.sqrt_sq hP).symm
    _ ≤ spreadF c := Real.sqrt_le_sqrt h2

end BlockBand.DeterminantScore.NegativeSpread
