module

public import BlockBand.Native.ErdosRiabov.VS.Modulus

set_option autoImplicit false

/-!
# Regularity of the VS band process with very high probability

Sup and modulus bounds for the VS band process in the forms used by the grid step: a named sup
lemma, the mesh power, the dimension bound, very-high-probability forms, and the transfer to
`vsBandFin`.

* `vsBand_sup_tail_one`: `P(sup_{t ≤ 1} ‖H_t‖_max ≥ λ) ≤ d · 2 exp(-λ²/8)`.
* `meshPow N C = (N^{-C}).toNNReal` and `vsBand_modulus_meshPow`: the power form of
  `vsBand_modulus` without an anonymous subtype in the statement.
* `card_site`, `ringDim_eq` (`d = N + 2N²`), `ringDim_le` (`d ≤ 3N²`).
* `vsBand_modulus_whp_bound`, `vsBand_modulus_whp`, `vsBand_sup_whp`: at `T = 1`, mesh
  `N^{-C}` and level `N^{-C/3}` the modulus event has probability
  `≤ 6 (N^C + 1) N² exp(-N^{C/3}/512)`, and for every `D` there is `N₀` (depending only on `C`,
  `D`) with probability `≤ N^{-D}` once `N ≥ N₀`; likewise `P(sup_{t ≤ 1} ‖H_t‖_max ≥ N) ≤ N^{-D}`.
* `vsBandFin_apply`, `vsBandFin_apply_equiv`, `vsBandFin_sup_tail`, `vsBandFin_modulus`: the
  entry transfer `vsBandFin p t x (e a) (e b) = vsBand p t x a b` (`e = ringSiteEquiv p`) and the
  sup and modulus bounds for the entries of the `Fin (p.n * p.W)` process used by the resolvents.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Function
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Native.ErdosRiabov.Stochastic
open scoped NNReal ENNReal

variable {p : BlockBand.Parameters}

/-!
### The named sup lemma
-/

/-- **Sup bound at `T = 1`**: `P(∃ t ≤ 1, ∃ a b, λ ≤ |H_t(a,b)|) ≤ d · 2 exp(-λ²/8)`. -/
theorem vsBand_sup_tail_one (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] {lam : ℝ}
    (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ 1 ∧ ∃ a b : p.Site,
        lam ≤ ‖vsBand p t x a b‖} ≤
      (ringDim p : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / 8)))) := by
  have h := vsBand_sup_tail μ 1 one_pos hlam
  simpa using h

/-!
### The mesh power
-/

/-- The mesh `N^{-C}` as an element of `ℝ≥0`. -/
def meshPow (N C : ℝ) : ℝ≥0 := (N ^ (-C)).toNNReal

theorem meshPow_coe {N : ℝ} (hN : 0 ≤ N) (C : ℝ) : (meshPow N C : ℝ) = N ^ (-C) :=
  Real.coe_toNNReal _ (Real.rpow_nonneg hN _)

theorem meshPow_pos {N : ℝ} (hN : 0 < N) (C : ℝ) : 0 < meshPow N C :=
  Real.toNNReal_pos.2 (Real.rpow_pos_of_pos hN _)

/-- **Modulus bound, power form** with the named mesh `meshPow N C = N^{-C}` and level `N^{-C/3}`. -/
theorem vsBand_modulus_meshPow (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (T : ℝ≥0)
    {N : ℝ} (hN : 1 ≤ N) (C : ℝ) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ s t : ℝ≥0, s ≤ t ∧ t ≤ s + meshPow N C ∧
        t ≤ T ∧ ∃ a b : p.Site, N ^ (-C / 3) ≤ ‖vsBand p t x a b - vsBand p s x a b‖} ≤
      (((⌊T / meshPow N C⌋₊ + 1) * ringDim p : ℕ) : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-(N ^ (C / 3) / 512)))) := by
  have hN0 : 0 < N := by linarith
  have hlam : 0 ≤ N ^ (-C / 3) := Real.rpow_nonneg hN0.le _
  have e : (N ^ (-C / 3)) ^ 2 / (512 * (meshPow N C : ℝ)) = N ^ (C / 3) / 512 := by
    rw [meshPow_coe hN0.le, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, mul_comm (512 : ℝ),
      ← div_div, ← Real.rpow_sub hN0]
    congr 2
    push_cast
    ring
  have hm := vsBand_modulus μ T (meshPow N C) (meshPow_pos hN0 C) hlam
  rwa [e] at hm

/-!
### The dimension bound
-/

theorem card_site (p : BlockBand.Parameters) : Fintype.card p.Site = p.n * p.W := by
  rw [Fintype.card_congr (ringSiteEquiv p), Fintype.card_fin]

theorem ringDim_eq (p : BlockBand.Parameters) : ringDim p = p.n * p.W + 2 * (p.n * p.W) ^ 2 := by
  simp only [ringDim, BlockBand.Parameters.GaussianCoordinate, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_bool, ZMod.card, Fintype.card_fin]
  ring

/-- `d = ringDim p ≤ 3 N²`. -/
theorem ringDim_le (p : BlockBand.Parameters) : ringDim p ≤ 3 * (p.n * p.W) ^ 2 := by
  have h1 : 1 ≤ p.n * p.W := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by have := p.n_ge_four; omega) p.W_pos.ne')
  rw [ringDim_eq]
  nlinarith

theorem one_le_dim (p : BlockBand.Parameters) : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by have := p.n_ge_four; omega) p.W_pos.ne')

/-!
### Very high probability
-/

/-- **Explicit modulus bound** at `T = 1`, mesh `N^{-C}`, level `N^{-C/3}`, `N = p.n * p.W`:
probability `≤ 6 (N^C + 1) N² exp(-N^{C/3}/512)`. -/
theorem vsBand_modulus_whp_bound (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (C : ℝ) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ s t : ℝ≥0, s ≤ t ∧
        t ≤ s + meshPow ((p.n * p.W : ℕ) : ℝ) C ∧ t ≤ 1 ∧ ∃ a b : p.Site,
        ((p.n * p.W : ℕ) : ℝ) ^ (-C / 3) ≤ ‖vsBand p t x a b - vsBand p s x a b‖} ≤
      ENNReal.ofReal (6 * (((p.n * p.W : ℕ) : ℝ) ^ C + 1) * ((p.n * p.W : ℕ) : ℝ) ^ 2 *
        Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ (C / 3) / 512))) := by
  set N : ℝ := ((p.n * p.W : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := one_le_dim p
  have hN0 : 0 < N := by linarith
  refine (vsBand_modulus_meshPow μ 1 hN1 C).trans ?_
  set e := Real.exp (-(N ^ (C / 3) / 512)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set k : ℕ := (⌊(1 : ℝ≥0) / meshPow N C⌋₊ + 1) * ringDim p with hk
  have hconv : ((k : ℕ) : ℝ≥0∞) * (2 * ENNReal.ofReal e) = ENNReal.ofReal ((k : ℝ) * (2 * e)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  rw [hconv]
  refine ENNReal.ofReal_le_ofReal ?_
  have hfloor : (⌊(1 : ℝ≥0) / meshPow N C⌋₊ : ℝ) ≤ N ^ C := by
    have h1 : (⌊(1 : ℝ≥0) / meshPow N C⌋₊ : ℝ≥0) ≤ (1 : ℝ≥0) / meshPow N C :=
      Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ _)
    have hm : (((1 : ℝ≥0) / meshPow N C : ℝ≥0) : ℝ) = N ^ C := by
      rw [NNReal.coe_div, NNReal.coe_one, meshPow_coe hN0.le, Real.rpow_neg hN0.le, one_div,
        inv_inv]
    have h2 := NNReal.coe_le_coe.2 h1
    rw [hm, NNReal.coe_natCast] at h2
    exact h2
  have hd : (ringDim p : ℝ) ≤ 3 * N ^ 2 := by
    rw [hNdef]
    exact_mod_cast ringDim_le p
  have hkr : (k : ℝ) = ((⌊(1 : ℝ≥0) / meshPow N C⌋₊ : ℝ) + 1) * ringDim p := by
    rw [hk]
    push_cast
    ring
  rw [hkr]
  have hd0 : (0 : ℝ) ≤ ringDim p := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ (⌊(1 : ℝ≥0) / meshPow N C⌋₊ : ℝ) := Nat.cast_nonneg _
  calc ((⌊(1 : ℝ≥0) / meshPow N C⌋₊ : ℝ) + 1) * ringDim p * (2 * e)
      ≤ (N ^ C + 1) * (3 * N ^ 2) * (2 * e) := by gcongr
    _ = 6 * (N ^ C + 1) * N ^ 2 * e := by ring

/-- `N^s exp(-b N^a) → 0`: eventually (in `N`) it is `≤ ε`, and `N ≥ 1`. -/
theorem exists_rpow_mul_exp_le {s a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ N₀ : ℝ, ∀ N ≥ N₀, 1 ≤ N ∧ N ^ s * Real.exp (-b * N ^ a) ≤ ε := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / a) b hb).comp
    (tendsto_rpow_atTop ha)
  have h2 : ∀ᶠ N in atTop, ((fun x : ℝ => x ^ (s / a) * Real.exp (-b * x)) ∘
      fun x : ℝ => x ^ a) N < ε := h1.eventually (gt_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (h2.and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN => ⟨(hN₀ N hN).2, ?_⟩⟩
  have hlt := (hN₀ N hN).1
  have hN0 : 0 ≤ N := by linarith [(hN₀ N hN).2]
  simp only [Function.comp_apply] at hlt
  rw [← Real.rpow_mul hN0, mul_div_cancel₀ s ha.ne'] at hlt
  exact hlt.le

/-- **Modulus, very high probability**: for `C > 0` and every `D` there is `N₀` such that
for every parameter set with `N = p.n * p.W ≥ N₀` and every initial law `μ`, the modulus event
at `T = 1`, mesh `N^{-C}`, level `N^{-C/3}` has probability `≤ N^{-D}`. -/
theorem vsBand_modulus_whp {C : ℝ} (hC : 0 < C) (D : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ],
      N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ s t : ℝ≥0, s ≤ t ∧
          t ≤ s + meshPow ((p.n * p.W : ℕ) : ℝ) C ∧ t ≤ 1 ∧ ∃ a b : p.Site,
          ((p.n * p.W : ℕ) : ℝ) ^ (-C / 3) ≤ ‖vsBand p t x a b - vsBand p s x a b‖} ≤
        ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀⟩ := exists_rpow_mul_exp_le (s := C + 2 + D) (a := C / 3) (b := 1 / 512)
    (ε := 1 / 12) (by positivity) (by norm_num) (by norm_num)
  refine ⟨N₀, fun p μ _ hp => (vsBand_modulus_whp_bound μ C).trans
    (ENNReal.ofReal_le_ofReal ?_)⟩
  set N : ℝ := ((p.n * p.W : ℕ) : ℝ)
  obtain ⟨hN1, hle⟩ := hN₀ N hp
  have hN0 : 0 < N := by linarith
  have hNC : 1 ≤ N ^ C := Real.one_le_rpow hN1 hC.le
  set e := Real.exp (-(N ^ (C / 3) / 512))
  have he : Real.exp (-(1 / 512) * N ^ (C / 3)) = e := by
    congr 1
    ring
  rw [he] at hle
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hsplit : N ^ (C + 2 + D) = N ^ C * N ^ 2 * N ^ D := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_two]
  have hD : N ^ (-D) * N ^ D = 1 := by
    rw [← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero]
  have hDpos : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  rw [hsplit] at hle
  calc 6 * (N ^ C + 1) * N ^ 2 * e = 6 * ((N ^ C + 1) * (N ^ 2 * e)) := by ring
    _ ≤ 6 * ((2 * N ^ C) * (N ^ 2 * e)) := by gcongr; linarith
    _ = 12 * (N ^ C * N ^ 2 * e) := by ring
    _ = 12 * (N ^ (-D) * (N ^ C * N ^ 2 * N ^ D * e)) := by
        rw [show N ^ (-D) * (N ^ C * N ^ 2 * N ^ D * e) =
          (N ^ (-D) * N ^ D) * (N ^ C * N ^ 2 * e) by ring, hD, one_mul]
    _ ≤ 12 * (N ^ (-D) * (1 / 12)) := by gcongr
    _ = N ^ (-D) := by ring

/-- **Sup, very high probability**: for every `D` there is `N₀` with
`P(∃ t ≤ 1, ∃ a b, N ≤ |H_t(a,b)|) ≤ N^{-D}` once `N = p.n * p.W ≥ N₀`. -/
theorem vsBand_sup_whp (D : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ],
      N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ 1 ∧ ∃ a b : p.Site,
          ((p.n * p.W : ℕ) : ℝ) ≤ ‖vsBand p t x a b‖} ≤
        ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀⟩ := exists_rpow_mul_exp_le (s := 2 + D) (a := 2) (b := 1 / 8) (ε := 1 / 6)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨N₀, fun p μ _ hp => ?_⟩
  set N : ℝ := ((p.n * p.W : ℕ) : ℝ) with hNdef
  obtain ⟨hN1, hle⟩ := hN₀ N hp
  have hN0 : 0 < N := by linarith
  refine (vsBand_sup_tail_one μ hN0.le).trans ?_
  set e := Real.exp (-(N ^ 2 / 8))
  have he : Real.exp (-(1 / 8) * N ^ (2 : ℝ)) = e := by
    rw [Real.rpow_two]
    congr 1
    ring
  rw [he] at hle
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hconv : ((ringDim p : ℕ) : ℝ≥0∞) * (2 * ENNReal.ofReal e) =
      ENNReal.ofReal ((ringDim p : ℝ) * (2 * e)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  rw [hconv]
  refine ENNReal.ofReal_le_ofReal ?_
  have hd : (ringDim p : ℝ) ≤ 3 * N ^ 2 := by
    rw [hNdef]
    exact_mod_cast ringDim_le p
  have hsplit : N ^ (2 + D) = N ^ 2 * N ^ D := by
    rw [Real.rpow_add hN0, Real.rpow_two]
  have hD : N ^ (-D) * N ^ D = 1 := by
    rw [← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero]
  rw [hsplit] at hle
  calc (ringDim p : ℝ) * (2 * e) ≤ 3 * N ^ 2 * (2 * e) := by gcongr
    _ = 6 * (N ^ (-D) * (N ^ 2 * N ^ D * e)) := by
        rw [show N ^ (-D) * (N ^ 2 * N ^ D * e) = (N ^ (-D) * N ^ D) * (N ^ 2 * e) by ring, hD]
        ring
    _ ≤ 6 * (N ^ (-D) * (1 / 6)) := by gcongr
    _ = N ^ (-D) := by ring

/-!
### Entry transfer to `vsBandFin`
-/

theorem vsBandFin_apply (t : ℝ≥0) (x : RingSample p) (a b : Fin (p.n * p.W)) :
    vsBandFin p t x a b =
      vsBand p t x ((ringSiteEquiv p).symm a) ((ringSiteEquiv p).symm b) := rfl

theorem vsBandFin_apply_equiv (t : ℝ≥0) (x : RingSample p) (a b : p.Site) :
    vsBandFin p t x (ringSiteEquiv p a) (ringSiteEquiv p b) = vsBand p t x a b := by
  rw [vsBandFin_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Sup bound for the entries of `vsBandFin`. -/
theorem vsBandFin_sup_tail (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (T : ℝ≥0)
    (hT : 0 < T) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ ∃ a b : Fin (p.n * p.W),
        lam ≤ ‖vsBandFin p t x a b‖} ≤
      (ringDim p : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (8 * T))))) := by
  refine le_trans (measure_mono fun x hx => ?_) (vsBand_sup_tail μ T hT hlam)
  obtain ⟨t, htT, a, b, h⟩ := hx
  exact ⟨t, htT, _, _, h⟩

/-- Modulus bound for the entries of `vsBandFin`. -/
theorem vsBandFin_modulus (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (T h : ℝ≥0)
    (hh : 0 < h) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ s t : ℝ≥0, s ≤ t ∧ t ≤ s + h ∧ t ≤ T ∧
        ∃ a b : Fin (p.n * p.W), lam ≤ ‖vsBandFin p t x a b - vsBandFin p s x a b‖} ≤
      (((⌊T / h⌋₊ + 1) * ringDim p : ℕ) : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (512 * h))))) := by
  refine le_trans (measure_mono fun x hx => ?_) (vsBand_modulus μ T h hh hlam)
  obtain ⟨s, t, hst, hts, htT, a, b, hl⟩ := hx
  exact ⟨s, t, hst, hts, htT, _, _, hl⟩

end BlockBand.Native.ErdosRiabov.VS
