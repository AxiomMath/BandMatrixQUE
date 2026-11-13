module

public import BlockBand.Native.ErdosRiabov.Flow.Anchor
public import BlockBand.Native.ErdosRiabov.Kernel.VSKernelExtra

/-!
# The anchor decomposition

The regularized kernel `Θ̊^x_t` is propagated by `P̂_{s,t}`, and is decomposed at the anchor time
`t♭`.

Definitions: for a kernel `A_t = vsKernel S μ μ' t` and a site `x`, the regularized kernel
`vsThetaRing S μ μ' t x = Θ̊^x_t`, `(Θ̊^x_t)_{ab} = A_t(a,b) - A_t(a,x)` (as in Erdős–Riabov).

* `vsThetaRing_propagate` (any stochastic symmetric `S`, `|μ|, |μ'| < 1`, `s, t ∈ [0,1]`):
  `Θ̊^x_t = P̂_{s,t} Θ̊^x_s = Θ̊^x_s + (t-s)(A_t - Π A_t) Θ̊^x_s` and `Π Θ̊^x_s = 0`.
* `anchor_decomp` (`T̂_t = A_t(z, z̄)`, `z ∈ 𝒟`, `t♭ = anchorTime z N W`, `t♭ ≤ t ≤ 1`):
  the above at `s = t♭`, the cocycle `P̂_{t♭,t} P̂_{s,t♭} = P̂_{s,t}` and `Θ̊^x_t = P̂_{s,t} Θ̊^x_s`
  for every `s ∈ [0,1]`, `0 ≤ t - t♭ ≤ η_{t♭}/c_m`, and `η_{t♭} N²/W² ≤ 1` if `t♭ < 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.LemmaK

open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open scoped BigOperators ComplexConjugate

variable {N : ℕ}

/-- The regularized kernel `Θ̊^x_t`, `(Θ̊^x_t)_{ab} = A_t(a,b) - A_t(a,x)`,
`A_t = vsKernel S μ μ' t`. -/
def vsThetaRing (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (t : ℝ) (x : Fin N) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun a b => vsKernel S μ μ' t a b - vsKernel S μ μ' t a x

/-- The column selector `E_x`, `(E_x)_{cb} = δ_{cx}`. -/
private def lemmaKColSel (x : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun c _ => if c = x then 1 else 0

private theorem lemmaK_mul_colSel (A : Matrix (Fin N) (Fin N) ℂ) (x a b : Fin N) :
    (A * lemmaKColSel x) a b = A a x := by
  rw [Matrix.mul_apply]
  simp [lemmaKColSel]

private theorem lemmaK_thetaRing_eq (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (t : ℝ)
    (x : Fin N) :
    vsThetaRing S μ μ' t x = vsKernel S μ μ' t * (1 - lemmaKColSel x) := by
  ext a b
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, lemmaK_mul_colSel]
  rfl

private theorem lemmaK_vsPi_mul_colSel (x : Fin N) : vsPi N * lemmaKColSel x = vsPi N := by
  ext a b
  rw [Matrix.mul_apply]
  simp [vsPi, lemmaKColSel]

/-- **Propagation of `Θ̊`** (the anchor-time corollary of Lemma K, general times). For a
stochastic symmetric `S`, `|μ|, |μ'| < 1`, `s, t ∈ [0,1]` and a site `x`:
`Θ̊^x_t = P̂_{s,t} Θ̊^x_s`, `Θ̊^x_t = Θ̊^x_s + (t-s)(A_t - Π A_t) Θ̊^x_s`, and `Π Θ̊^x_s = 0`
(`Π = vsPi N`, `P̂ = vsPropagator`, closed form).
-/
theorem vsThetaRing_propagate {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {μ μ' : ℂ} (hμ : ‖μ‖ < 1) (hμ' : ‖μ'‖ < 1) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Fin N) :
    vsThetaRing S μ μ' t x = vsPropagator S μ μ' s t * vsThetaRing S μ μ' s x ∧
    vsThetaRing S μ μ' t x = vsThetaRing S μ μ' s x + ((t : ℂ) - s) •
      ((vsKernel S μ μ' t - vsPi N * vsKernel S μ μ' t) * vsThetaRing S μ μ' s x) ∧
    vsPi N * vsThetaRing S μ μ' s x = 0 := by
  have hs := norm_smul_lt_one hμ hμ' hs0 hs1
  have ht := norm_smul_lt_one hμ hμ' ht0 ht1
  have hPi0 : vsPi N * vsThetaRing S μ μ' s x = 0 := by
    rw [lemmaK_thetaRing_eq, ← Matrix.mul_assoc, vsPi_mul_vsKernel hS hs, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.mul_one, lemmaK_vsPi_mul_colSel, sub_self, smul_zero]
  have h1 : vsThetaRing S μ μ' t x = vsPropagator S μ μ' s t * vsThetaRing S μ μ' s x := by
    rw [lemmaK_thetaRing_eq, lemmaK_thetaRing_eq, ← Matrix.mul_assoc,
      ← vsKernel_eq_propagator_mul hS hs ht]
  have hcomm : vsPi N * vsKernel S μ μ' t = vsKernel S μ μ' t * vsPi N := by
    rw [vsPi_mul_vsKernel hS ht, vsKernel_mul_vsPi hS ht]
  refine ⟨h1, ?_, hPi0⟩
  rw [h1, vsPropagator_eq hS ht, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_mul,
    hcomm, Matrix.mul_assoc, hPi0, Matrix.mul_zero, sub_zero]

/-- `η_{t♭} ≤ η♭ = (W/N)²` whenever `t♭ < 1` (`Im z > 0`). -/
theorem lemmaK_anchorTime_height_le {z : ℂ} (hη : 0 < z.im) {N W : ℕ}
    (h1 : anchorTime z N W < 1) : vsHeight z (anchorTime z N W) ≤ etaFlat N W := by
  have hy := semicircleM_im_pos hη
  unfold anchorTime at h1 ⊢
  split_ifs with h
  · exact h.le
  · simp only [h, ite_false] at h1
    have hlt : (vsHeight z 0 - etaFlat N W) / (semicircleM z).im < 1 := by
      by_contra hc
      rw [not_lt] at hc
      rw [min_eq_left hc] at h1
      exact lt_irrefl _ h1
    rw [min_eq_right hlt.le, vsHeight_affine]
    field_simp
    linarith

/-- For a stochastic
symmetric `S` on `Fin N` (`N ≥ 1`), `W ≥ 1`, `κ > 0`, `z ∈ 𝒟` (`BulkDomain N δ₀ κ C₀ z`),
`m = semicircleM z`, `T̂_t = vsKernel S m (conj m) t`, `t♭ = anchorTime z N W`, a site `x` and
`t♭ ≤ t ≤ 1`:
`Θ̊^x_t = P̂_{t♭,t} Θ̊^x_{t♭} = Θ̊^x_{t♭} + (t-t♭)(T̂_t - Π T̂_t) Θ̊^x_{t♭}`;
`Π Θ̊^x_{t♭} = 0`; for every `s ∈ [0,1]`, `P̂_{t♭,t} P̂_{s,t♭} = P̂_{s,t}` and
`Θ̊^x_t = P̂_{s,t} Θ̊^x_s`;
`0 ≤ t - t♭ ≤ η_{t♭}/c_m`; and if `t♭ < 1`, `η_{t♭} N²/W² ≤ 1`.
-/
theorem anchor_decomp {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) (hN : 0 < N)
    {W : ℕ} (hW : 0 < W) {δ₀ κ C₀ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : BulkDomain N δ₀ κ C₀ z)
    (x : Fin N)
    {t : ℝ} (ht : anchorTime z N W ≤ t) (ht1 : t ≤ 1) :
    vsThetaRing S (semicircleM z) (conj (semicircleM z)) t x =
      vsPropagator S (semicircleM z) (conj (semicircleM z)) (anchorTime z N W) t *
        vsThetaRing S (semicircleM z) (conj (semicircleM z)) (anchorTime z N W) x ∧
    vsThetaRing S (semicircleM z) (conj (semicircleM z)) t x =
      vsThetaRing S (semicircleM z) (conj (semicircleM z)) (anchorTime z N W) x +
        ((t : ℂ) - anchorTime z N W) •
          ((vsKernel S (semicircleM z) (conj (semicircleM z)) t -
              vsPi N * vsKernel S (semicircleM z) (conj (semicircleM z)) t) *
            vsThetaRing S (semicircleM z) (conj (semicircleM z)) (anchorTime z N W) x) ∧
    vsPi N * vsThetaRing S (semicircleM z) (conj (semicircleM z)) (anchorTime z N W) x = 0 ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      vsPropagator S (semicircleM z) (conj (semicircleM z)) (anchorTime z N W) t *
          vsPropagator S (semicircleM z) (conj (semicircleM z)) s (anchorTime z N W) =
        vsPropagator S (semicircleM z) (conj (semicircleM z)) s t ∧
      vsThetaRing S (semicircleM z) (conj (semicircleM z)) t x =
        vsPropagator S (semicircleM z) (conj (semicircleM z)) s t *
          vsThetaRing S (semicircleM z) (conj (semicircleM z)) s x) ∧
    0 ≤ t - anchorTime z N W ∧
    t - anchorTime z N W ≤ vsHeight z (anchorTime z N W) / imLower κ C₀ ∧
    (anchorTime z N W < 1 →
      vsHeight z (anchorTime z N W) * ((N : ℝ) ^ 2 / (W : ℝ) ^ 2) ≤ 1) := by
  have hη := hz.im_pos hN
  have hC0 : 0 ≤ C₀ := (norm_nonneg z).trans hz.2.2
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hmc : ‖conj (semicircleM z)‖ < 1 := by rwa [Complex.norm_conj]
  obtain ⟨hf0, hf1⟩ := anchorTime_mem hη N W
  have ht0 : 0 ≤ t := hf0.trans ht
  obtain ⟨h1, h2, h3⟩ := vsThetaRing_propagate hS hm1 hmc hf0 hf1 ht0 ht1 x
  have hcm := semicircleM_im_ge hC0 hz.1 hη hz.2.2
  have hy := semicircleM_im_pos hη
  have hcm0 : 0 < imLower κ C₀ := by
    have hk0 : 0 < min κ 2 := lt_min hκ two_pos
    have hk2 : min κ 2 ≤ 2 := min_le_right _ _
    unfold imLower bulkSin
    exact div_pos (div_pos (Real.sqrt_pos.2 (mul_pos hk0 (by linarith))) two_pos)
      (by linarith)
  refine ⟨h1, h2, h3, fun s hs0 hs1 => ?_, by linarith, ?_, fun hlt => ?_⟩
  · have hsn := norm_smul_lt_one hm1 hmc hs0 hs1
    have hfn := norm_smul_lt_one hm1 hmc hf0 hf1
    exact ⟨vsPropagator_mul hS hfn (norm_smul_lt_one hm1 hmc ht0 ht1),
      (vsThetaRing_propagate hS hm1 hmc hs0 hs1 ht0 ht1 x).1⟩
  · have hηt := vsHeight_pos hη ht1
    have he : vsHeight z (anchorTime z N W) =
        vsHeight z t + (t - anchorTime z N W) * (semicircleM z).im := by
      unfold vsHeight
      ring
    rw [le_div_iff₀ hcm0, he]
    nlinarith
  · have hle := lemmaK_anchorTime_height_le hη hlt
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    unfold etaFlat at hle
    have hk : ((W : ℝ) / N) ^ 2 * ((N : ℝ) ^ 2 / (W : ℝ) ^ 2) = 1 := by
      field_simp
    have hq : 0 ≤ (N : ℝ) ^ 2 / (W : ℝ) ^ 2 := by positivity
    nlinarith

end BlockBand.Native.ErdosRiabov.LemmaK
