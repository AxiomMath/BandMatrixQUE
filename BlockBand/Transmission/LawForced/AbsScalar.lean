module

public import BlockBand.Transmission.LawForced.AbsLayer

/-!
# Scalar bookkeeping of the absorbed shift terms

Generic reals: `x = 1/W ∈ (0,1]`, `A = g' + 1 ≥ 1`, `D = Wδ₀' + 1 ≥ 1`, `0 ≤ g ≤ 4A`,
`0 ≤ s ≤ s₀x² ≤ 1` (`s = ε/η`), `0 ≤ ε ≤ Kx²`, `0 ≤ dq ≤ (D + c_qA)x`. Then
* **`inShiftErr_le`**: `inShiftErr ≤ shK·A³Dx²`;
* **`driftShift_le`**: `|D₀|/2·(M·dsB·A² + dsK·c·5A)·x ≤ dsC·A³Dx²` for `|D₀| ≤ D₀max`, with
  `c = (2s+s²)g + 4εW/η`, `M = Rc + e` the bounds that feed `ratioDrift_shift_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.LawDuality

variable {p : ℕ}

/-- `c_e = 28·lamLip·s₀ + 49·quadK·s₀² + 343·cubK·s₀³`. -/
def shCe (z : DualCoord p) (s₀ : ℝ) : ℝ :=
  28 * lamLip z * s₀ + 49 * quadK z * s₀ ^ 2 + 343 * cubK z * s₀ ^ 3

/-- `c_M = 16Rs₀ + c_e`. -/
def shCM (z : DualCoord p) (s₀ : ℝ) : ℝ := 16 * (∑ i, (z.1 i + z.2 i)) * s₀ + shCe z s₀

/-- The constant of `inShiftErr_le`. -/
def shK (z : DualCoord p) (s₀ K cq : ℝ) : ℝ :=
  shCe z s₀ + shCM z s₀ ^ 2 / 2 + 4 * shCM z s₀ ^ 3 +
    (∑ i, (z.1 i + z.2 i)) * (12 * s₀ + 4 * K + 4 * K * cq)

/-- The constant of `driftShift_le`. -/
def dsC (z : DualCoord p) (s₀ D0m : ℝ) : ℝ := D0m / 2 * (shCM z s₀ * dsB z + 80 * dsK z * s₀)

section Scalar

variable {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {W : ℕ} {x A D g s s₀ ε K η dq cq : ℝ}
  (hx : x = (W : ℝ)⁻¹) (hW : 1 ≤ W) (hA : 1 ≤ A) (hD : 1 ≤ D) (hg0 : 0 ≤ g) (hgA : g ≤ 4 * A)
  (hs0 : 0 ≤ s) (hss : s ≤ s₀ * x ^ 2) (hs1 : s ≤ 1) (hη : 0 < η) (hs : s = ε / η)
  (hε : 0 ≤ ε) (hεK : ε ≤ K * x ^ 2) (hcq : 0 ≤ cq)
include hz hx hW hA hD hg0 hgA hs0 hss hs1 hη hs hε hεK hcq

omit hz hA hD hg0 hgA hη hε hεK hcq in
theorem sh_basic : 0 < x ∧ x ≤ 1 ∧ 0 ≤ s₀ ∧ 6 * s + s ^ 2 ≤ 7 * s₀ * x ^ 2 ∧
    4 * ε * W / η ≤ 4 * s₀ * x := by
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by rw [hx]; exact inv_le_one_of_one_le₀ hWr
  have hs₀ : 0 ≤ s₀ := by
    by_contra h0; have h := not_le.1 h0
    have : s₀ * x ^ 2 < 0 := mul_neg_of_neg_of_pos h (by positivity)
    linarith
  refine ⟨hx0, hx1, hs₀, by nlinarith, ?_⟩
  have hxW : x * W = 1 := by rw [hx]; field_simp
  have e : 4 * ε * W / η = 4 * s * W := by rw [hs]; ring
  rw [e]
  have : s * W ≤ s₀ * x ^ 2 * W := mul_le_mul_of_nonneg_right hss (by positivity)
  have e2 : s₀ * x ^ 2 * W = s₀ * x := by
    calc s₀ * x ^ 2 * W = s₀ * x * (x * W) := by ring
      _ = s₀ * x := by rw [hxW, mul_one]
  nlinarith

omit hD hεK hcq hg0 hη hε in
theorem sh_e : shiftErr z g (6 * s + s ^ 2) W ≤ shCe z s₀ * A * x ^ 2 := by
  obtain ⟨hx0, hx1, hs₀, hn, -⟩ := sh_basic hx hW hs0 hss hs1 hs
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hxW : x * W = 1 := by rw [hx]; field_simp
  set n := 6 * s + s ^ 2
  have hn0 : 0 ≤ n := by positivity
  have hm2 : n ^ 2 * W ≤ 49 * s₀ ^ 2 * x ^ 2 := by
    have h1 : n ^ 2 ≤ (7 * s₀ * x ^ 2) ^ 2 := pow_le_pow_left₀ hn0 hn 2
    have h2 : (7 * s₀ * x ^ 2) ^ 2 * W = 49 * s₀ ^ 2 * x ^ 2 * (x * (x * W)) := by ring
    have h3 : x * (x * W) ≤ 1 := by rw [hxW, mul_one]; exact hx1
    calc n ^ 2 * W ≤ (7 * s₀ * x ^ 2) ^ 2 * W := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 49 * s₀ ^ 2 * x ^ 2 * (x * (x * W)) := h2
      _ ≤ 49 * s₀ ^ 2 * x ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := mul_one _
  have hsq : Real.sqrt (n ^ 2 * W) ≤ 7 * s₀ := by
    rw [show 7 * s₀ = Real.sqrt ((7 * s₀) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    exact Real.sqrt_le_sqrt (hm2.trans (by nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg s₀)]))
  have hL := lamLip_nonneg hz; have hQ := quadK_nonneg z; have hC := cubK_nonneg hz
  unfold shiftErr shCe
  have t1 : lamLip z * g * n ≤ 28 * lamLip z * s₀ * A * x ^ 2 := by
    have : g * n ≤ 4 * A * (7 * s₀ * x ^ 2) := mul_le_mul hgA hn hn0 (by positivity)
    nlinarith
  have t2 : quadK z * (n ^ 2 * W) ≤ 49 * quadK z * s₀ ^ 2 * A * x ^ 2 := by
    have := mul_le_mul_of_nonneg_left hm2 hQ
    have : 49 * quadK z * s₀ ^ 2 * x ^ 2 ≤ 49 * quadK z * s₀ ^ 2 * A * x ^ 2 := by
      have h0 : 0 ≤ 49 * quadK z * s₀ ^ 2 * x ^ 2 := by positivity
      nlinarith
    nlinarith
  have t3 : cubK z * (Real.sqrt (n ^ 2 * W) * (n ^ 2 * W)) ≤ 343 * cubK z * s₀ ^ 3 * A * x ^ 2 := by
    have h1 : Real.sqrt (n ^ 2 * W) * (n ^ 2 * W) ≤ 7 * s₀ * (49 * s₀ ^ 2 * x ^ 2) :=
      mul_le_mul hsq hm2 (by positivity) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 hC
    have : 343 * cubK z * s₀ ^ 3 * x ^ 2 ≤ 343 * cubK z * s₀ ^ 3 * A * x ^ 2 := by
      have h0 : 0 ≤ 343 * cubK z * s₀ ^ 3 * x ^ 2 := by positivity
      nlinarith
    nlinarith
  nlinarith

omit hD hεK hcq hz hη hε in
theorem sh_c : (2 * s + s ^ 2) * g + 4 * ε * W / η ≤ 16 * s₀ * A * x := by
  obtain ⟨hx0, hx1, hs₀, -, h4⟩ := sh_basic hx hW hs0 hss hs1 hs
  have a1 : (2 * s + s ^ 2) * g ≤ 3 * s * (4 * A) :=
    mul_le_mul (by nlinarith) hgA hg0 (by positivity)
  have a2 : s ≤ s₀ * x := hss.trans (by nlinarith [sq_nonneg x])
  have a3 : 4 * s₀ * x ≤ 4 * s₀ * A * x := by nlinarith [mul_nonneg hs₀ hx0.le]
  nlinarith [mul_nonneg hs₀ hx0.le]

end Scalar

theorem mono_P {A D x : ℝ} (hA : 1 ≤ A) (hD : 1 ≤ D) :
    A * x ^ 2 ≤ A ^ 3 * D * x ^ 2 ∧ A ^ 2 * x ^ 2 ≤ A ^ 3 * D * x ^ 2 ∧
      A ^ 3 * x ^ 2 ≤ A ^ 3 * D * x ^ 2 ∧ D * x ^ 2 ≤ A ^ 3 * D * x ^ 2 := by
  have hx2 := sq_nonneg x
  have h1 : A ≤ A ^ 2 := by nlinarith
  have h2 : A ^ 2 ≤ A ^ 3 := by nlinarith
  have h3 : A ^ 3 ≤ A ^ 3 * D := le_mul_of_one_le_right (by positivity) hD
  have h4 : D ≤ A ^ 3 * D := le_mul_of_one_le_left (by linarith) (by nlinarith)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply mul_le_mul_of_nonneg_right _ hx2 <;> linarith

theorem shift_core {R e c t CM Ce k A D x : ℝ} (hR : 0 ≤ R) (he0 : 0 ≤ e) (hc0 : 0 ≤ c)
    (hCM : 0 ≤ CM) (hA : 1 ≤ A) (hD : 1 ≤ D) (hx1 : x ≤ 1)
    (he : e ≤ Ce * (A ^ 3 * D * x ^ 2)) (hM : R * c + e ≤ CM * A * x)
    (ht : t ≤ k * (A ^ 3 * D * x ^ 2)) :
    e + (R * c + e) ^ 2 / 2 + 4 * (R * c + e) ^ 3 + R * t ≤
      (Ce + CM ^ 2 / 2 + 4 * CM ^ 3 + R * k) * (A ^ 3 * D * x ^ 2) := by
  obtain ⟨-, p2, p3, -⟩ := mono_P (x := x) hA hD
  have hM0 : 0 ≤ R * c + e := by positivity
  have h2 : (R * c + e) ^ 2 ≤ CM ^ 2 * (A ^ 3 * D * x ^ 2) := by
    have := pow_le_pow_left₀ hM0 hM 2
    have e2 : (CM * A * x) ^ 2 = CM ^ 2 * (A ^ 2 * x ^ 2) := by ring
    rw [e2] at this
    exact this.trans (mul_le_mul_of_nonneg_left p2 (sq_nonneg _))
  have h3 : (R * c + e) ^ 3 ≤ CM ^ 3 * (A ^ 3 * D * x ^ 2) := by
    have := pow_le_pow_left₀ hM0 hM 3
    have hx3 : x ^ 3 ≤ x ^ 2 := by
      calc x ^ 3 = x ^ 2 * x := pow_succ x 2
        _ ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left hx1 (sq_nonneg x)
        _ = x ^ 2 := mul_one _
    have e3 : (CM * A * x) ^ 3 = CM ^ 3 * (A ^ 3 * x ^ 3) := by ring
    rw [e3] at this
    have h4 : A ^ 3 * x ^ 3 ≤ A ^ 3 * D * x ^ 2 :=
      (mul_le_mul_of_nonneg_left hx3 (by positivity)).trans p3
    exact this.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
  have h5 := mul_le_mul_of_nonneg_left ht hR
  have e5 : R * (k * (A ^ 3 * D * x ^ 2)) = R * k * (A ^ 3 * D * x ^ 2) := by ring
  rw [e5] at h5
  have e6 : (Ce + CM ^ 2 / 2 + 4 * CM ^ 3 + R * k) * (A ^ 3 * D * x ^ 2) =
      Ce * (A ^ 3 * D * x ^ 2) + CM ^ 2 * (A ^ 3 * D * x ^ 2) / 2 +
        4 * (CM ^ 3 * (A ^ 3 * D * x ^ 2)) + R * k * (A ^ 3 * D * x ^ 2) := by ring
  rw [e6]
  linarith

/-- **The input-shift error is `O(A³D/W²)`.** -/
theorem inShiftErr_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {W : ℕ}
    {x A D g s s₀ ε K η dq cq : ℝ} (hx : x = (W : ℝ)⁻¹) (hW : 1 ≤ W) (hA : 1 ≤ A) (hD : 1 ≤ D)
    (hg0 : 0 ≤ g) (hgA : g ≤ 4 * A) (hs0 : 0 ≤ s) (hss : s ≤ s₀ * x ^ 2) (hs1 : s ≤ 1)
    (hη : 0 < η) (hs : s = ε / η) (hε : 0 ≤ ε) (hεK : ε ≤ K * x ^ 2) (hcq : 0 ≤ cq)
    (hdq0 : 0 ≤ dq) (hdq : dq ≤ (D + cq * A) * x) :
    inShiftErr z g s ε η dq W ≤ shK z s₀ K cq * (A ^ 3 * D * x ^ 2) := by
  obtain ⟨hx0, hx1, hs₀, -, -⟩ := sh_basic hx hW hs0 hss hs1 hs
  have he := sh_e hz hx hW hA hgA hs0 hss hs1 hs
  have hc := sh_c hx hW hA hg0 hgA hs0 hss hs1 hs
  have hxW : x * W = 1 := by rw [hx]; field_simp
  have hR : 0 ≤ ∑ i, (z.1 i + z.2 i) := Finset.sum_nonneg fun i _ => by
    have := hz.1 i; have := (hz.2 i).1; linarith
  have he0 : 0 ≤ shiftErr z g (6 * s + s ^ 2) W := shiftErr_nonneg hz hg0 (by positivity)
  have hc0 : 0 ≤ (2 * s + s ^ 2) * g + 4 * ε * W / η := by positivity
  have hCe : 0 ≤ shCe z s₀ := by
    unfold shCe; have := lamLip_nonneg hz; have := quadK_nonneg z; have := cubK_nonneg hz
    positivity
  have hCM : 0 ≤ shCM z s₀ := by unfold shCM; positivity
  have hxx : x ^ 2 ≤ x := by
    calc x ^ 2 = x * x := sq x
      _ ≤ 1 * x := mul_le_mul_of_nonneg_right hx1 hx0.le
      _ = x := one_mul x
  obtain ⟨p1, -, -, p4⟩ := mono_P (x := x) hA hD
  have hM : (∑ i, (z.1 i + z.2 i)) * ((2 * s + s ^ 2) * g + 4 * ε * W / η) +
      shiftErr z g (6 * s + s ^ 2) W ≤ shCM z s₀ * A * x := by
    have a1 := mul_le_mul_of_nonneg_left hc hR
    have a2 : shCe z s₀ * A * x ^ 2 ≤ shCe z s₀ * A * x :=
      mul_le_mul_of_nonneg_left hxx (by positivity)
    unfold shCM; linarith
  have hK0 : 0 ≤ K := by
    by_contra h0; have h := not_le.1 h0
    have : K * x ^ 2 < 0 := mul_neg_of_neg_of_pos h (by positivity)
    linarith
  have hlast : (2 * s + s ^ 2) * g + 4 * ε * W * dq ≤
      (12 * s₀ + 4 * K + 4 * K * cq) * (A ^ 3 * D * x ^ 2) := by
    have a1 : (2 * s + s ^ 2) * g ≤ 3 * (s₀ * x ^ 2) * (4 * A) :=
      mul_le_mul (by nlinarith) hgA hg0 (by positivity)
    have hεW : ε * W ≤ K * x := by
      have := mul_le_mul_of_nonneg_right hεK (Nat.cast_nonneg W)
      calc ε * W ≤ K * x ^ 2 * W := this
        _ = K * x * (x * W) := by ring
        _ = K * x := by rw [hxW, mul_one]
    have a2 : ε * W * dq ≤ K * x * ((D + cq * A) * x) :=
      mul_le_mul hεW hdq hdq0 (by positivity)
    have b1 := mul_le_mul_of_nonneg_left p1 (by positivity : (0 : ℝ) ≤ 12 * s₀ + 4 * K * cq)
    have b2 := mul_le_mul_of_nonneg_left p4 (by positivity : (0 : ℝ) ≤ 4 * K)
    linarith
  have heP : shiftErr z g (6 * s + s ^ 2) W ≤ shCe z s₀ * (A ^ 3 * D * x ^ 2) :=
    he.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left p1 hCe)
  have key := shift_core hR he0 hc0 hCM hA hD hx1 heP hM hlast
  unfold inShiftErr shK
  exact key

theorem drift_core {R e c dB dK g g' CM s₀ A D x D0a D0m : ℝ} (hR : 0 ≤ R) (he0 : 0 ≤ e)
    (hc0 : 0 ≤ c) (hB : 0 ≤ dB) (hK : 0 ≤ dK) (hCM : 0 ≤ CM) (hs₀ : 0 ≤ s₀) (hA : 1 ≤ A)
    (hD : 1 ≤ D) (hx0 : 0 ≤ x) (hD0a : 0 ≤ D0a) (hD0 : D0a ≤ D0m)
    (hM : R * c + e ≤ CM * A * x) (hc : c ≤ 16 * s₀ * A * x) (hsum : g + g' + 1 ≤ 5 * A)
    (hg' : g' + 1 = A) (hgg : 0 ≤ g + g' + 1) :
    D0a / 2 * ((R * c + e) * (dB * (g' + 1) ^ 2) + dK * c * (g + g' + 1)) * x ≤
      D0m / 2 * (CM * dB + 80 * dK * s₀) * (A ^ 3 * D * x ^ 2) := by
  rw [hg']
  have hA3 : A ^ 2 ≤ A ^ 3 := by nlinarith
  have t1 : (R * c + e) * (dB * A ^ 2) ≤ CM * dB * (A ^ 3 * x) := by
    have := mul_le_mul_of_nonneg_right hM (by positivity : (0 : ℝ) ≤ dB * A ^ 2)
    have e1 : CM * A * x * (dB * A ^ 2) = CM * dB * (A ^ 3 * x) := by ring
    linarith
  have t2 : dK * c * (g + g' + 1) ≤ 80 * dK * s₀ * (A ^ 3 * x) := by
    have h1 : c * (g + g' + 1) ≤ 16 * s₀ * A * x * (5 * A) :=
      mul_le_mul hc hsum hgg (by positivity)
    have h3 : 16 * s₀ * A * x * (5 * A) ≤ 80 * s₀ * (A ^ 3 * x) := by
      have := mul_le_mul_of_nonneg_left hA3 (by positivity : (0 : ℝ) ≤ 80 * s₀ * x)
      have e1 : 16 * s₀ * A * x * (5 * A) = 80 * s₀ * x * A ^ 2 := by ring
      have e2 : 80 * s₀ * (A ^ 3 * x) = 80 * s₀ * x * A ^ 3 := by ring
      linarith
    have := mul_le_mul_of_nonneg_left (h1.trans h3) hK
    have e3 : dK * c * (g + g' + 1) = dK * (c * (g + g' + 1)) := by ring
    have e4 : dK * (80 * s₀ * (A ^ 3 * x)) = 80 * dK * s₀ * (A ^ 3 * x) := by ring
    linarith
  have hT0 : 0 ≤ (R * c + e) * (dB * A ^ 2) + dK * c * (g + g' + 1) := by positivity
  have hsT : (R * c + e) * (dB * A ^ 2) + dK * c * (g + g' + 1) ≤
      (CM * dB + 80 * dK * s₀) * (A ^ 3 * x) := by
    have e5 : (CM * dB + 80 * dK * s₀) * (A ^ 3 * x) =
        CM * dB * (A ^ 3 * x) + 80 * dK * s₀ * (A ^ 3 * x) := by ring
    linarith
  have h6 : D0a / 2 * ((R * c + e) * (dB * A ^ 2) + dK * c * (g + g' + 1)) ≤
      D0m / 2 * ((CM * dB + 80 * dK * s₀) * (A ^ 3 * x)) :=
    mul_le_mul (by linarith) hsT hT0 (by linarith)
  have h7 := mul_le_mul_of_nonneg_right h6 hx0
  have hp3 : A ^ 3 * x * x ≤ A ^ 3 * D * x ^ 2 := by
    have : A ^ 3 ≤ A ^ 3 * D := le_mul_of_one_le_right (by positivity) hD
    have := mul_le_mul_of_nonneg_right this (sq_nonneg x)
    have e6 : A ^ 3 * x * x = A ^ 3 * x ^ 2 := by ring
    linarith
  have h8 : D0m / 2 * ((CM * dB + 80 * dK * s₀) * (A ^ 3 * x)) * x =
      D0m / 2 * (CM * dB + 80 * dK * s₀) * (A ^ 3 * x * x) := by ring
  have h9 := mul_le_mul_of_nonneg_left hp3
    (by have := hD0a.trans hD0; positivity : (0 : ℝ) ≤ D0m / 2 * (CM * dB + 80 * dK * s₀))
  linarith

/-- **The drift shift is `O(A³D/W²)`.** -/
theorem driftShift_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {W : ℕ}
    {x A D g g' s s₀ ε η D0 D0m : ℝ} (hx : x = (W : ℝ)⁻¹) (hW : 1 ≤ W) (hA : 1 ≤ A)
    (hD : 1 ≤ D) (hg0 : 0 ≤ g) (hgA : g ≤ 4 * A) (hs0 : 0 ≤ s) (hss : s ≤ s₀ * x ^ 2)
    (hs1 : s ≤ 1) (hη : 0 < η) (hs : s = ε / η) (hε : 0 ≤ ε) (hg' : g' + 1 = A)
    (hD0 : |D0| ≤ D0m) :
    |D0| / 2 * (((∑ i, (z.1 i + z.2 i)) * ((2 * s + s ^ 2) * g + 4 * ε * W / η) +
        shiftErr z g (6 * s + s ^ 2) W) * (dsB z * (g' + 1) ^ 2) +
        dsK z * ((2 * s + s ^ 2) * g + 4 * ε * W / η) * (g + g' + 1)) / W ≤
      dsC z s₀ D0m * (A ^ 3 * D * x ^ 2) := by
  obtain ⟨hx0, hx1, hs₀, -, -⟩ := sh_basic hx hW hs0 hss hs1 hs
  have he := sh_e hz hx hW hA hgA hs0 hss hs1 hs
  have hc := sh_c hx hW hA hg0 hgA hs0 hss hs1 hs
  have hR : 0 ≤ ∑ i, (z.1 i + z.2 i) := Finset.sum_nonneg fun i _ => by
    have := hz.1 i; have := (hz.2 i).1; linarith
  have he0 : 0 ≤ shiftErr z g (6 * s + s ^ 2) W := shiftErr_nonneg hz hg0 (by positivity)
  have hc0 : 0 ≤ (2 * s + s ^ 2) * g + 4 * ε * W / η := by positivity
  have hCe : 0 ≤ shCe z s₀ := by
    unfold shCe; have := lamLip_nonneg hz; have := quadK_nonneg z; have := cubK_nonneg hz
    positivity
  have hCM : 0 ≤ shCM z s₀ := by unfold shCM; positivity
  have hxx : x ^ 2 ≤ x := by
    calc x ^ 2 = x * x := sq x
      _ ≤ 1 * x := mul_le_mul_of_nonneg_right hx1 hx0.le
      _ = x := one_mul x
  have hM : (∑ i, (z.1 i + z.2 i)) * ((2 * s + s ^ 2) * g + 4 * ε * W / η) +
      shiftErr z g (6 * s + s ^ 2) W ≤ shCM z s₀ * A * x := by
    have a1 := mul_le_mul_of_nonneg_left hc hR
    have a2 : shCe z s₀ * A * x ^ 2 ≤ shCe z s₀ * A * x :=
      mul_le_mul_of_nonneg_left hxx (by positivity)
    unfold shCM; linarith
  rw [div_eq_mul_inv, ← hx]
  have key := drift_core (g := g) (g' := g') hR he0 hc0 (dsB_nonneg hz) (dsK_nonneg hz) hCM hs₀ hA hD hx0.le
    (abs_nonneg D0) hD0 hM hc (by linarith) hg' (by linarith)
  unfold dsC
  exact key

end BlockBand.Transmission.LawForced
