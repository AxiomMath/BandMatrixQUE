module

public import BlockBand.Endpoints.Response.RemoteHigherFiniteStopped
public import BlockBand.Endpoints.Response.NearSchattenExit

/-!
# Tools for the exit and stop removal of the higher functional

Part of the proof of the remote higher-moment theorem: trace stopping passes the chain rule and
Gronwall to the limit. Deterministic, at every path `ω` and length `j`, for the one-source
family.

**Proved here.**
* `rhx_shift_rpow_le`: `(H + ε^p)^s ≤ L^s 2^m (1 + A^m)` for `0 ≤ H ≤ pε^{p-1}A`, `0 ≤ s ≤ m`
  (`L = pε^{p-1} + ε^p + 1`).
* `rhxPowPoly k = (Tr QP)^{k+2}` (the ordinary composite `rhfComposite 1 1 (X^{k+2})`) and
  `rhx_drift_lower_pow`: after the injection, with `𝕊` unitary,
  `(D/2) g (Tr A)^{k+2} ≤ |𝒜 (Tr QP)^{k+2}| + (k+2)² D (Tr A)^{k+2}` (the word generator of the
  composite, `rhf_polyValue_wordGenerator_composite_path` at `π = id`: drift
  `-(D/2)(k+2) g (Tr A)^{k+2}` plus `½(k+2)(k+1)(Tr A)^k Γ_id`, `0 ≤ Γ_id ≤ D (Tr A)²`).
* `rhx_neg_rhlGenExpr_le`: `-rhlGenExpr ≤ r Hδ^{r-1} |𝒢_ε|` (the bracket is `≥ 0`; no unitarity).
* `rhx_afterStop_real`, `rhx_mass_pointwise`: after the stop,
  `(-rhlGenExpr)⁺ ≤ κ₁(|𝒜 Tr(QP)| + |𝒜 (Tr QP)^{k+2}|) + κ₂(1 + (sup Tr Q)^{k+3})`,
  constants depending on `b, E, p, r, ε, k` only.
* `rhxDrift`, `rhx_drift_ui`: the drift total variation of an ordinary trace polynomial in the
  exact form of `FullSourceStopsContract.compensatorUI`, and its uniform integrability.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset Polynomial
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

variable {W : ℕ}

/-!
## Scalar bounds
-/

/-- `L = pε^{p-1} + ε^p + 1`. -/
def rhxL (p ε : ℝ) : ℝ := p * ε ^ (p - 1) + ε ^ p + 1

theorem rhx_one_le_L {p ε : ℝ} (hp0 : 0 ≤ p) (hε : 0 < ε) : 1 ≤ rhxL p ε := by
  have := Real.rpow_pos_of_pos hε p
  have := mul_nonneg hp0 (Real.rpow_nonneg hε.le (p - 1))
  unfold rhxL; linarith

/-- `(1 + A)^m ≤ 2^m (1 + A^m)`. -/
theorem rhx_one_add_pow_le {A : ℝ} (hA : 0 ≤ A) (m : ℕ) : (1 + A) ^ m ≤ 2 ^ m * (1 + A ^ m) := by
  have h1 : 1 + A ≤ 2 * max 1 A := by
    have := le_max_left 1 A; have := le_max_right 1 A; linarith
  calc (1 + A) ^ m ≤ (2 * max 1 A) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    _ = 2 ^ m * max 1 A ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (1 + A ^ m) := by gcongr; exact rhf_pow_le_one_add hA m

/-- `A^k ≤ 1 + A^m` for `0 ≤ A`, `k ≤ m`. -/
theorem rhx_pow_le_one_add {A : ℝ} (hA : 0 ≤ A) {k m : ℕ} (hkm : k ≤ m) : A ^ k ≤ 1 + A ^ m :=
  calc A ^ k ≤ max 1 A ^ k := pow_le_pow_left₀ hA (le_max_right _ _) k
    _ ≤ max 1 A ^ m := pow_le_pow_right₀ (le_max_left _ _) hkm
    _ ≤ 1 + A ^ m := rhf_pow_le_one_add hA m

/-- **`(H + ε^p)^s ≤ L^s 2^m (1 + A^m)`** for `0 ≤ H ≤ pε^{p-1}A`, `0 ≤ s ≤ m`. -/
theorem rhx_shift_rpow_le {p ε H A s : ℝ} (hp0 : 0 ≤ p) (hε : 0 < ε) (hH0 : 0 ≤ H)
    (hHA : H ≤ p * ε ^ (p - 1) * A) (hA : 0 ≤ A) (hs : 0 ≤ s) {m : ℕ} (hsm : s ≤ m) :
    (H + ε ^ p) ^ s ≤ rhxL p ε ^ s * 2 ^ m * (1 + A ^ m) := by
  have hεp := Real.rpow_pos_of_pos hε p
  have hc := mul_nonneg hp0 (Real.rpow_nonneg hε.le (p - 1))
  have hL1 := rhx_one_le_L hp0 hε
  have h1 : H + ε ^ p ≤ rhxL p ε * (1 + A) := by
    unfold rhxL
    nlinarith [mul_nonneg hc hA, mul_nonneg hεp.le hA]
  calc (H + ε ^ p) ^ s ≤ (rhxL p ε * (1 + A)) ^ s := Real.rpow_le_rpow (by positivity) h1 hs
    _ = rhxL p ε ^ s * (1 + A) ^ s := Real.mul_rpow (by linarith) (by linarith)
    _ ≤ rhxL p ε ^ s * (1 + A) ^ (m : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hsm)
          (Real.rpow_nonneg (by linarith) _)
    _ = rhxL p ε ^ s * (1 + A) ^ m := by rw [Real.rpow_natCast]
    _ ≤ rhxL p ε ^ s * (2 ^ m * (1 + A ^ m)) := by
        gcongr; exact rhx_one_add_pow_le hA m
    _ = _ := by ring

/-!
## The power `(Tr QP)^{k+2}`
-/

/-- `(Tr QP)^{k+2}`, the ordinary composite `rhfComposite 1 1 (X^{k+2})`. -/
def rhxPowPoly (k : ℕ) : TracePoly 0 1 := rhfComposite (fun _ => 1) 1 (X ^ (k + 2))

theorem rhx_isOrdinaryPoly_pow (k : ℕ) : IsOrdinaryPoly (rhxPowPoly k) :=
  rhf_isOrdinaryPoly_composite _ _ _

theorem rhx_clockVal_one (b E : ℝ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x) (W j : ℕ)
    (ω : GrowthPath W) :
    rhfClockVal b E q (fun _ => 1) 1 W j ω = (nearClock b E W j q ω).trace.re := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq0 ω
  unfold rhfClockVal
  rw [nsf_polyValue_clockPoly_path b E hq0 W j ω (noTags W) _ 1, Complex.ofReal_re]
  simp only [nsfPolyFun, Finset.sum_range_one, one_mul, zero_add, pow_one]
  rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp

theorem rhx_polyD1_one : nsfPolyD1 (fun _ => 1) 1 = fun _ => 1 := by
  funext x; simp [nsfPolyD1]

theorem rhx_polyD2_one : nsfPolyD2 (fun _ => 1) 1 = fun _ => 0 := by
  funext x; simp [nsfPolyD2]

/-- The trace generator of `Tr(QP)` at the path: `-(D/2) g Tr A`. -/
theorem rhx_genExpr_one (b E : ℝ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x) (W j : ℕ)
    (ω : GrowthPath W) :
    nsfGenExpr (nsfPolyD1 (fun _ => 1) 1) (nsfPolyD2 (fun _ => 1) 1) b E q W j ω =
      -(transportD0 b E / 2) * nsgConductance (scatteringMatrix b E W j ω) *
        (nearClock b E W j q ω).trace.re := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq0 ω
  unfold nsfGenExpr
  rw [dite_eq_left hpsd.1, rhx_polyD1_one, rhx_polyD2_one]
  have hDD : ∀ x y : ℝ, nsfDivDiff (fun _ => (1 : ℝ)) (fun _ => 0) x y = 0 := by
    intro x y; unfold nsfDivDiff; split_ifs <;> simp
  unfold nsfSpecGen
  simp only [hDD, mul_zero, Finset.sum_const_zero, add_zero, mul_one]
  rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp

theorem rhx_eval_derivative_pow (k : ℕ) (y : ℝ) :
    (derivative (X ^ (k + 2) : ℝ[X])).eval y = ((k : ℝ) + 2) * y ^ (k + 1) := by
  rw [derivative_X_pow]; simp

theorem rhx_eval_derivative2_pow (k : ℕ) (y : ℝ) :
    (derivative (derivative (X ^ (k + 2) : ℝ[X]))).eval y =
      ((k : ℝ) + 2) * ((k : ℝ) + 1) * y ^ k := by
  rw [derivative_X_pow, derivative_C_mul, derivative_X_pow]
  simp
  ring

/-- **The drift of `(Tr QP)^{k+2}` after the injection** (`𝕊` unitary, `q(t) = 0`):
`(D/2) g (Tr A)^{k+2} ≤ |𝒜_t (Tr QP)^{k+2}| + (k+2)² D (Tr A)^{k+2}`. -/
theorem rhx_drift_lower_pow {b E : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) {q : ℝ → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) {j : ℕ} {ω : GrowthPath W}
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) {t : ℝ}
    (hqt : q t = 0) (k : ℕ) :
    transportD0 b E / 2 * nsgConductance (scatteringMatrix b E W j ω) *
        (nearClock b E W j q ω).trace.re ^ (k + 2) ≤
      ‖polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t (rhxPowPoly k))‖ +
        ((k : ℝ) + 2) ^ 2 * transportD0 b E * (nearClock b E W j q ω).trace.re ^ (k + 2) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq0 ω
  obtain ⟨hV, -⟩ := nsf_eigenframe hpsd.1
  have hD := (ns_transportD0_pos hb hE hE').le
  have hg0 := nsg_conductance_nonneg hS
  have hA0 := (trace_nearClock_le b E W j q hq0 ω).1
  set A := (nearClock b E W j q ω).trace.re with hAdef
  set g := nsgConductance (scatteringMatrix b E W j ω)
  set D := transportD0 b E
  set Γ := rhfBracketExpr (nsfPolyD1 (fun _ => 1) 1) b E q W j ω with hΓdef
  have hsum : ∑ i, hpsd.1.eigenvalues i = A := by
    rw [hAdef, hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  have hlam : ∀ i, hpsd.1.eigenvalues i ∈ Icc 0 A := fun i =>
    ⟨hpsd.eigenvalues_nonneg i, nsf_eigenvalue_le_trace hpsd i⟩
  have hΓ : |Γ| ≤ D * A ^ 2 := by
    rw [hΓdef, rhx_polyD1_one]
    unfold rhfBracketExpr
    rw [dite_eq_left hpsd.1]
    have h := rhf_abs_specBracket_le (M₁ := 1) hD hlam (fun i => nsg_frameDiag_nonneg _ _ i)
      (fun i => nsg_frameDiag_le_one hS hV i) (e₁ := fun _ => 1) (fun x _ => by simp)
    rw [hsum, one_pow, mul_one] at h
    exact h
  have e : polyValue b E (noTags W) (fun _ => q) W j ω
      (wordGenerator b E (fun _ => q) t (rhxPowPoly k)) =
      (((((k : ℝ) + 2) * A ^ (k + 1)) * (-(D / 2) * g * A) +
        1 / 2 * (((k : ℝ) + 2) * ((k : ℝ) + 1) * A ^ k) * Γ : ℝ) : ℂ) := by
    unfold rhxPowPoly
    rw [rhf_polyValue_wordGenerator_composite_path b E hq0 _ 1 W j ω _ hqt, rhx_clockVal_one b E hq0,
      rhx_genExpr_one b E hq0, rhx_eval_derivative_pow, rhx_eval_derivative2_pow]
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  set X := ((k : ℝ) + 2) * A ^ (k + 1) * (-(D / 2) * g * A) +
    1 / 2 * (((k : ℝ) + 2) * ((k : ℝ) + 1) * A ^ k) * Γ with hX
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hAk := pow_nonneg hA0 k
  have hpow : A ^ k * A ^ 2 = A ^ (k + 2) := by rw [pow_add]
  have hpow' : A ^ (k + 1) * A = A ^ (k + 2) := by ring
  have hgA : 0 ≤ D / 2 * g * A ^ (k + 2) := by positivity
  have hAkΓ : A ^ k * Γ ≤ A ^ k * (D * A ^ 2) :=
    mul_le_mul_of_nonneg_left ((le_abs_self Γ).trans hΓ) hAk
  have hneg : -X ≤ |X| := neg_le_abs X
  have hXe : -X = ((k : ℝ) + 2) * (D / 2 * g * A ^ (k + 2)) -
      1 / 2 * ((k : ℝ) + 2) * ((k : ℝ) + 1) * (A ^ k * Γ) := by
    rw [hX, ← hpow']; ring
  have hc : 0 ≤ 1 / 2 * ((k : ℝ) + 2) * ((k : ℝ) + 1) := by positivity
  have h1 : 1 / 2 * ((k : ℝ) + 2) * ((k : ℝ) + 1) * (A ^ k * Γ) ≤
      1 / 2 * ((k : ℝ) + 2) * ((k : ℝ) + 1) * (D * A ^ (k + 2)) := by
    rw [← hpow, show D * (A ^ k * A ^ 2) = A ^ k * (D * A ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left hAkΓ hc
  have h2 : 1 / 2 * ((k : ℝ) + 2) * ((k : ℝ) + 1) * (D * A ^ (k + 2)) ≤
      ((k : ℝ) + 2) ^ 2 * D * A ^ (k + 2) := by
    have hDA : 0 ≤ D * A ^ (k + 2) := by positivity
    nlinarith
  have h3 : D / 2 * g * A ^ (k + 2) ≤ ((k : ℝ) + 2) * (D / 2 * g * A ^ (k + 2)) := by
    nlinarith
  linarith

/-!
## The chain-rule generator after the stop
-/

/-- **`-rhlGenExpr ≤ r Hδ^{r-1} |𝒢_ε|`** (the bracket is `≥ 0`; no unitarity). -/
theorem rhx_neg_rhlGenExpr_le {b E p r ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    (hp0 : 0 ≤ p) (hr : 1 ≤ r) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {j : ℕ}
    (ω : GrowthPath W) :
    -rhlGenExpr b E p r ε q W j ω ≤
      r * rhlShiftTrace b E p ε q W j ω ^ (r - 1) * |nsgGenExpr b E p ε q W j ω| := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  have hD := (ns_transportD0_pos hb hE hE').le
  have hH := rhl_shiftTrace_pos (b := b) (E := E) (W := W) (j := j) hp0 hε hq ω
  have hΓ : 0 ≤ rhlBracketExpr b E p ε q W j ω := by
    rw [rhf_rhlBracketExpr_eq]
    unfold rhfBracketExpr rhfSpecBracket
    rw [dite_eq_left hpsd.1]
    exact mul_nonneg hD (Finset.sum_nonneg fun i _ =>
      mul_nonneg (sq_nonneg _) (nsg_frameDiag_nonneg _ _ i))
  have h1 : 0 ≤ r * (r - 1) / 2 * rhlShiftTrace b E p ε q W j ω ^ (r - 2) *
      rhlBracketExpr b E p ε q W j ω := by
    have hr1 : 0 ≤ r - 1 := by linarith
    have : 0 ≤ r * (r - 1) / 2 := by positivity
    have := Real.rpow_nonneg hH.le (r - 2)
    positivity
  have h2 : 0 ≤ r * rhlShiftTrace b E p ε q W j ω ^ (r - 1) := by
    have := Real.rpow_nonneg hH.le (r - 1)
    have : 0 ≤ r := by linarith
    positivity
  have h3 := mul_le_mul_of_nonneg_left (neg_le_abs (nsgGenExpr b E p ε q W j ω)) h2
  unfold rhlGenExpr
  linarith

/-- `κ₁ = r L^{r-1} 2^{k+1} M_ε`. -/
def rhxK1 (p r ε : ℝ) (k : ℕ) : ℝ := r * (rhxL p ε ^ (r - 1) * 2 ^ (k + 1)) * nssGenConst p ε

/-- `κ₂ = κ₁ D (1 + (k+2)²)`. -/
def rhxK2 (b E p r ε : ℝ) (k : ℕ) : ℝ :=
  rhxK1 p r ε k * (transportD0 b E * (1 + ((k : ℝ) + 2) ^ 2))

theorem rhx_K_nonneg {b E p r ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hr : 1 ≤ r) (hε : 0 < ε) (k : ℕ) : 0 ≤ rhxK1 p r ε k ∧ 0 ≤ rhxK2 b E p r ε k := by
  have hM : 0 ≤ nssGenConst p ε :=
    (mul_nonneg hp0 (Real.rpow_nonneg hε.le _)).trans (le_max_left _ _)
  have hL := rhx_one_le_L hp0 hε
  have hLr := Real.rpow_nonneg (show (0 : ℝ) ≤ rhxL p ε by linarith) (r - 1)
  have hD := (ns_transportD0_pos hb hE hE').le
  have hr0 : 0 ≤ r := by linarith
  have h1 : 0 ≤ rhxK1 p r ε k := by unfold rhxK1; positivity
  refine ⟨h1, ?_⟩
  unfold rhxK2; positivity

/-- **After the stop, the real bound** (`𝕊` unitary, after the injection, `r ≤ k + 1`):
`-rhlGenExpr ≤ κ₁(|𝒜 Tr(QP)| + |𝒜 (Tr QP)^{k+2}|) + κ₂(1 + (Tr A)^{k+3})`. -/
theorem rhx_afterStop_real {b E p r ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r) (hε : 0 < ε) {k : ℕ} (hrk : r ≤ k + 1)
    {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {j : ℕ} {ω : GrowthPath W}
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) {t : ℝ}
    (hqt : q t = 0) :
    -rhlGenExpr b E p r ε q W j ω ≤
      rhxK1 p r ε k * ‖polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t nsxClockOne)‖ +
        rhxK1 p r ε k * ‖polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t (rhxPowPoly k))‖ +
        rhxK2 b E p r ε k * (1 + (nearClock b E W j q ω).trace.re ^ (k + 3)) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  have hD := (ns_transportD0_pos hb hE hE').le
  have hM : 0 ≤ nssGenConst p ε :=
    (mul_nonneg hp0 (Real.rpow_nonneg hε.le _)).trans (le_max_left _ _)
  have hg0 := nsg_conductance_nonneg hS
  have hA0 := (trace_nearClock_le b E W j q hq ω).1
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨hH0, hHle⟩ := rhf_clockSum_regKernel_bounds hp0 hp1 hε hpsd
  set A := (nearClock b E W j q ω).trace.re with hAdef
  set g := nsgConductance (scatteringMatrix b E W j ω)
  set D := transportD0 b E
  set M := nssGenConst p ε
  set X₁ := ‖polyValue b E (noTags W) (fun _ => q) W j ω
    (wordGenerator b E (fun _ => q) t nsxClockOne)‖
  set Xn := ‖polyValue b E (noTags W) (fun _ => q) W j ω
    (wordGenerator b E (fun _ => q) t (rhxPowPoly k))‖
  set c := rhxL p ε ^ (r - 1) * 2 ^ (k + 1) with hc
  have hL := rhx_one_le_L hp0 hε
  have hc0 : 0 ≤ c := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ rhxL p ε by linarith) (r - 1); positivity
  -- the three ingredients
  have hneg := rhx_neg_rhlGenExpr_le hb hE hE' hp0 hr hε hq (j := j) ω
  have hG := nss_abs_genExpr_le hb hE hE' hp0 hp1 hε hq hS
  have hHd : rhlShiftTrace b E p ε q W j ω ^ (r - 1) ≤ c * (1 + A ^ (k + 1)) := by
    unfold rhlShiftTrace
    have := rhx_shift_rpow_le hp0 hε hH0 hHle hA0 (by linarith : 0 ≤ r - 1)
      (m := k + 1) (by push_cast; linarith)
    rw [hc]; linarith
  have hd1 : D / 2 * g * A ≤ X₁ := nsx_drift_lower hb hE hE' hq hS hqt
  have hdn := rhx_drift_lower_pow hb hE hE' hq hS hqt k
  have hHd0 := Real.rpow_nonneg (rhl_shiftTrace_pos (b := b) (E := E) (W := W) (j := j) hp0 hε
    hq ω).le (r - 1)
  -- chain
  have hstep1 : r * rhlShiftTrace b E p ε q W j ω ^ (r - 1) * |nsgGenExpr b E p ε q W j ω| ≤
      r * (c * (1 + A ^ (k + 1))) * (D / 2 * M * (g * A + A ^ 2)) := by
    have hrH : r * rhlShiftTrace b E p ε q W j ω ^ (r - 1) ≤ r * (c * (1 + A ^ (k + 1))) :=
      mul_le_mul_of_nonneg_left hHd hr0
    exact mul_le_mul hrH hG (abs_nonneg _) (by positivity)
  have hexp : r * (c * (1 + A ^ (k + 1))) * (D / 2 * M * (g * A + A ^ 2)) =
      r * c * M * (D / 2 * g * A + D / 2 * g * A ^ (k + 2) + D / 2 * A ^ 2 +
        D / 2 * A ^ (k + 3)) := by ring
  have hp2 := rhx_pow_le_one_add hA0 (show 2 ≤ k + 3 by omega)
  have hp3 := rhx_pow_le_one_add hA0 (show k + 2 ≤ k + 3 by omega)
  have hp4 : A ^ (k + 3) ≤ 1 + A ^ (k + 3) := by linarith
  have hinner : D / 2 * g * A + D / 2 * g * A ^ (k + 2) + D / 2 * A ^ 2 + D / 2 * A ^ (k + 3) ≤
      X₁ + Xn + D * (1 + ((k : ℝ) + 2) ^ 2) * (1 + A ^ (k + 3)) := by
    have hk2 : 0 ≤ ((k : ℝ) + 2) ^ 2 * D := by positivity
    have e1 : ((k : ℝ) + 2) ^ 2 * D * A ^ (k + 2) ≤ ((k : ℝ) + 2) ^ 2 * D * (1 + A ^ (k + 3)) :=
      mul_le_mul_of_nonneg_left hp3 hk2
    have e2 : D / 2 * A ^ 2 ≤ D / 2 * (1 + A ^ (k + 3)) :=
      mul_le_mul_of_nonneg_left hp2 (by positivity)
    have e3 : D / 2 * A ^ (k + 3) ≤ D / 2 * (1 + A ^ (k + 3)) :=
      mul_le_mul_of_nonneg_left hp4 (by positivity)
    have e4 : D * (1 + ((k : ℝ) + 2) ^ 2) * (1 + A ^ (k + 3)) =
        D / 2 * (1 + A ^ (k + 3)) + D / 2 * (1 + A ^ (k + 3)) +
          ((k : ℝ) + 2) ^ 2 * D * (1 + A ^ (k + 3)) := by ring
    linarith
  have hrcM : 0 ≤ r * c * M := by positivity
  have hfin := mul_le_mul_of_nonneg_left hinner hrcM
  have eK : rhxK1 p r ε k * X₁ + rhxK1 p r ε k * Xn +
      rhxK2 b E p r ε k * (1 + A ^ (k + 3)) =
      r * c * M * (X₁ + Xn + D * (1 + ((k : ℝ) + 2) ^ 2) * (1 + A ^ (k + 3))) := by
    unfold rhxK2 rhxK1; rw [← hc]; ring
  rw [eK]
  linarith

/-- **After the stop, one length** (`𝕊` unitary, after the injection, `j ≤ j₂` in the window):
`1{j≥σ}(-rhlGenExpr)⁺ ≤ 1{σ≤j₂}(κ₁(|𝒜 Tr(QP)| + |𝒜 (Tr QP)^{k+2}|) + κ₂ + κ₂ (sup Tr Q)^{k+3})`. -/
theorem rhx_mass_pointwise {b E p r ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r) (hε : 0 < ε) {k : ℕ} (hrk : r ≤ k + 1)
    {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K u₁ u₂ : ℝ} {j j₂ : ℕ}
    {ω : GrowthPath W} (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1)
    (hqt : q (((j + 1 : ℕ) : ℝ) / W) = 0) (hj1 : u₁ / 2 * W ≤ j)
    (hjT : (j : ℝ) ≤ (u₂ + 1) * W) (hj2 : j ≤ j₂) :
    (nsfAlive b E q K u₁ W j)ᶜ.indicator
        (fun ω => ENNReal.ofReal (-rhlGenExpr b E p r ε q W j ω)) ω ≤
      (nsfAlive b E q K u₁ W j₂)ᶜ.indicator (fun ω => ENNReal.ofReal (rhxK1 p r ε k) *
          ‖polyValue b E (noTags W) (fun _ => q) W j ω
            (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) nsxClockOne)‖ₑ +
        ENNReal.ofReal (rhxK1 p r ε k) *
          ‖polyValue b E (noTags W) (fun _ => q) W j ω
            (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhxPowPoly k))‖ₑ +
        ENNReal.ofReal (rhxK2 b E p r ε k) +
        ENNReal.ofReal (rhxK2 b E p r ε k) *
          nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (k + 3)) ω := by
  by_cases hal : ω ∈ nsfAlive b E q K u₁ W j
  · rw [Set.indicator_of_notMem (show ω ∉ (nsfAlive b E q K u₁ W j)ᶜ from fun h => h hal)]
    exact zero_le
  have hd : ω ∉ nsfAlive b E q K u₁ W j₂ := fun h => hal
    (show (j : ℕ∞) < _ from lt_of_le_of_lt (by exact_mod_cast hj2) h)
  rw [Set.indicator_of_mem (show ω ∈ (nsfAlive b E q K u₁ W j)ᶜ from hal),
    Set.indicator_of_mem (show ω ∈ (nsfAlive b E q K u₁ W j₂)ᶜ from hd)]
  obtain ⟨hK1, hK2⟩ := rhx_K_nonneg hb hE hE' hp0 hr hε k
  have hA0 := (trace_nearClock_le b E W j q hq ω).1
  have hreal := rhx_afterStop_real hb hE hE' hp0 hp1 hr hε hrk hq hS hqt
  set A := (nearClock b E W j q ω).trace.re
  set X₁ := ‖polyValue b E (noTags W) (fun _ => q) W j ω
    (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) nsxClockOne)‖
  set Xn := ‖polyValue b E (noTags W) (fun _ => q) W j ω
    (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhxPowPoly k))‖
  calc ENNReal.ofReal (-rhlGenExpr b E p r ε q W j ω)
      ≤ ENNReal.ofReal (rhxK1 p r ε k * X₁ + rhxK1 p r ε k * Xn +
          (rhxK2 b E p r ε k + rhxK2 b E p r ε k * A ^ (k + 3))) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (rhxK1 p r ε k * X₁) + ENNReal.ofReal (rhxK1 p r ε k * Xn) +
        (ENNReal.ofReal (rhxK2 b E p r ε k) +
          ENNReal.ofReal (rhxK2 b E p r ε k * A ^ (k + 3))) := by
        refine ENNReal.ofReal_add_le.trans ?_
        gcongr
        · exact ENNReal.ofReal_add_le
        · exact ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (rhxK1 p r ε k) * ENNReal.ofReal X₁ +
        ENNReal.ofReal (rhxK1 p r ε k) * ENNReal.ofReal Xn +
        (ENNReal.ofReal (rhxK2 b E p r ε k) +
          ENNReal.ofReal (rhxK2 b E p r ε k) * ENNReal.ofReal A ^ (k + 3)) := by
        rw [ENNReal.ofReal_mul hK1, ENNReal.ofReal_mul hK1, ENNReal.ofReal_mul hK2,
          ENNReal.ofReal_pow hA0]
    _ ≤ _ := by
        rw [ofReal_norm, ofReal_norm, ← add_assoc]
        gcongr
        exact nsx_trA_le_supQ b E hq hj1 hjT ω

/-!
## The drift total variation of an ordinary trace polynomial
-/

/-- The drift total variation `Σ_{εW≤j<TW} W⁻¹|𝒜_{(j+1)/W} Φ|` of `compensatorUI`
(`ε = u₁/2`, `T = u₂ + 1`). -/
def rhxDrift (b E : ℝ) (q : ℝ → ℝ) (u₁ u₂ : ℝ) (Φ : TracePoly 0 1) (W : ℕ)
    (ω : GrowthPath W) : ℝ≥0∞ :=
  ∑ j ∈ (Finset.range ⌊(u₂ + 1) * W⌋₊).filter (fun j : ℕ => u₁ / 2 * W ≤ (j : ℝ)),
    (W : ℝ≥0∞)⁻¹ * ‖polyValue b E (noTags W) (fun _ => q) W j ω
      (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) Φ)‖ₑ

theorem rhx_measurable_drift (b E : ℝ) (q : ℝ → ℝ) (u₁ u₂ : ℝ) (Φ : TracePoly 0 1) (W : ℕ) :
    Measurable (rhxDrift b E q u₁ u₂ Φ W) := by
  unfold rhxDrift
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.mul (nss_measurable_polyValue b E (noTags W) _ W j _).enorm

/-- **Uniform integrability of the drift total variation** (`compensatorUI`). -/
theorem rhx_drift_ui (hStops : FullSourceStopsContract) {b E : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {q : ℝ → ℝ}
    (hIT : IsIntervalTests (fun _ : Fin 1 => q)) {u₁ u₂ : ℝ} (hu₁ : 0 < u₁) (hu : u₁ ≤ u₂)
    {Φ : TracePoly 0 1} (hΦ : IsOrdinaryPoly Φ) :
    ∀ η : ℝ, 0 < η → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∫⁻ ω, {ω | ENNReal.ofReal M < rhxDrift b E q u₁ u₂ Φ W ω}.indicator
        (rhxDrift b E q u₁ u₂ Φ W) ω ∂growthPathLaw W b ≤ ENNReal.ofReal η := fun η hη => by
  obtain ⟨M, W₀, h⟩ := hStops.compensatorUI b hb hb1 E hE hE' 0 1 (fun _ => q) hIT
    Φ hΦ (u₁ / 2) (u₂ + 1) η (by positivity) (by linarith) hη
  exact ⟨M, W₀, fun W hW => (h W hW (noTags W)).1⟩

end BlockBand.Endpoints
