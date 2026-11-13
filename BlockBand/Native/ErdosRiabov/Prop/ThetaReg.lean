module

public import BlockBand.Native.ErdosRiabov.Prop.Single
public import BlockBand.Native.ErdosRiabov.LemmaK.Anchor

/-!
# Regularity of `T̂`

Setting: VS data `d`, `m ≥ 4`, `W ≥ 1`, `N = mW`, `S = shortRingProfile d.b m W`, `z ∈ 𝒟`,
`m = semicircleM z`, `T̂_t = vsKernel S m (conj m) t`, `Θ̊^x_t = vsThetaRing S m (conj m) t x`,
`η_t = vsHeight z t`, `Υ_t = polynomialControl N W d.D η_t`, `ℓ_t = ℓ(η_t)`,
`η♭ = etaFlat N W`, `C_K = vsCK d`, `C₁'' = d.C1pp`. No lower bound on `T̂` is claimed. Deterministic: no measure occurs.

The kernel bounds (K2) and (K3) are also restated for `vsThetaRing` and in the `Im m/(Nη_t)` form
(`vsThetaRing_K2`, `vsThetaRing_K3`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Propagator

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.LemmaK
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open scoped BigOperators ComplexConjugate

theorem vsThetaRing_apply {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (t : ℝ)
    (x a b : Fin N) :
    vsThetaRing S μ μ' t x a b = vsKernel S μ μ' t a b - vsKernel S μ μ' t a x := rfl

section Reg

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 z)
include hm hW hz

/-- **(K2) for `Θ̊`**: if `η♭ ≤ η_t` or `t ≤ 1/4`, then
`|Θ̊^x_t(a,b)| ≤ C_K ((d(b,x)+W) ∧ ℓ_t)/ℓ_t (Υ_t(a,b) + Υ_t(a,x))`. -/
theorem vsThetaRing_K2 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hthr : etaFlat (m * W) W ≤ vsHeight z t ∨ t ≤ 1 / 4) (x a b : Fin (m * W)) :
    ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t x a b‖ ≤
      vsCK d * (min ((ErdosRiabov.cyclicDistance (m * W) b x : ℝ) + W)
          (ErdosRiabov.localizationLength (m * W) W (vsHeight z t)) /
        ErdosRiabov.localizationLength (m * W) W (vsHeight z t)) *
      (polynomialControl (m * W) W d.D (vsHeight z t) a b +
        polynomialControl (m * W) W d.D (vsHeight z t) a x) :=
  lemmaK_K2_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos d.C0_ge_one d.D_ge_six hm hW
    hz ht0 ht1 hthr a b x

/-- **(K3) for `T̂` and `Θ̊`**, all `t ∈ [0,1]`:
`|T̂_t(a,b) - Im m/(Nη_t)| ≤ C_K N/W²` and `|Θ̊^x_t(a,b)| ≤ 2 C_K N/W²`; and every entry of
`Π T̂_t` is `Im m/(Nη_t)`. -/
theorem vsThetaRing_K3 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ a b, ‖vsKernel (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t a b -
        (((semicircleM z).im / (((m * W : ℕ) : ℝ) * vsHeight z t) : ℝ) : ℂ)‖ ≤
      vsCK d * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2) ∧
    (∀ x a b,
      ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t x a b‖ ≤
        2 * vsCK d * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2) ∧
    (∀ a b, (vsPi (m * W) *
        vsKernel (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t) a b =
      (((semicircleM z).im / (((m * W : ℕ) : ℝ) * vsHeight z t) : ℝ) : ℂ)) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hS := shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (by omega : 3 ≤ m) hW
  have h3 : ∀ a b,
      ‖vsKernel (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t a b -
        (((semicircleM z).im / (((m * W : ℕ) : ℝ) * vsHeight z t) : ℝ) : ℂ)‖ ≤
      vsCK d * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 := fun a b =>
    lemmaK_K3_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos d.C0_ge_one d.D_ge_six hm hW
      hz ht0 ht1 a b
  refine ⟨h3, fun x a b => ?_, (vsKernel_theta_core hS (hz.im_pos hN) ht0 ht1 ht0 ht1).2.2.2.2.2.1⟩
  rw [vsThetaRing_apply]
  set c : ℂ := (((semicircleM z).im / (((m * W : ℕ) : ℝ) * vsHeight z t) : ℝ) : ℂ)
  calc _ = ‖(vsKernel (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t a b
          - c) - (vsKernel (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t
            a x - c)‖ := by ring_nf
    _ ≤ _ := norm_sub_le _ _
    _ ≤ vsCK d * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 + vsCK d * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 :=
        add_le_add (h3 a b) (h3 a x)
    _ = _ := by ring

/-- **Regularity of `T̂`.** For VS data `d`, `m ≥ 4`,
`W ≥ 1`, `z ∈ 𝒟`, `t ∈ [0,1]` and all sites (notation of the module header):
(1) if `η♭ ≤ η_t` or `t ≤ 1/4`: `|Θ̊^x_t(a,b)| ≤ C_K ((d(b,x)+W)∧ℓ_t)/ℓ_t (Υ_t(a,b)+Υ_t(a,x))`;
(1') `𝓛 ≠ ∅` and `t ≤ t♭` imply `η♭ ≤ η_t` (Lemma *Anchor time* (a));
(2) if `η_t ≤ η♭`: `T̂_t(a,b)` is real and `0 ≤ T̂_t(a,b) ≤ C_K C₁''(Nη_t)⁻¹`;
(3) `|T̂_t(a,b) - Im m/(Nη_t)| ≤ C_K N/W²` and `|Θ̊^x_t(a,b)| ≤ 2C_K N/W²` (all `t`);
(4) if `η_t ≤ η♭`: `(C₁'')⁻¹(Nη_t)⁻¹ ≤ Υ_t(a,b) ≤ C₁''(Nη_t)⁻¹`. -/
theorem thetaRegular_vs {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((etaFlat (m * W) W ≤ vsHeight z t ∨ t ≤ 1 / 4) → ∀ x a b,
      ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t x a b‖ ≤
        vsCK d * (min ((ErdosRiabov.cyclicDistance (m * W) b x : ℝ) + W)
            (ErdosRiabov.localizationLength (m * W) W (vsHeight z t)) /
          ErdosRiabov.localizationLength (m * W) W (vsHeight z t)) *
        (polynomialControl (m * W) W d.D (vsHeight z t) a b +
          polynomialControl (m * W) W d.D (vsHeight z t) a x)) ∧
    ((anchorSet z (m * W) W).Nonempty → t ≤ anchorTime z (m * W) W →
      etaFlat (m * W) W ≤ vsHeight z t) ∧
    (vsHeight z t ≤ etaFlat (m * W) W → ∀ a b,
      (vsKernel (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t a b).im = 0 ∧
      0 ≤ (vsKernel (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t a b).re ∧
      ‖vsKernel (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t a b‖ ≤
        vsCK d * d.C1pp / (((m * W : ℕ) : ℝ) * vsHeight z t)) ∧
    (∀ a b, ‖vsKernel (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t a b -
        (((semicircleM z).im / (((m * W : ℕ) : ℝ) * vsHeight z t) : ℝ) : ℂ)‖ ≤
      vsCK d * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2) ∧
    (∀ x a b,
      ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t x a b‖ ≤
        2 * vsCK d * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2) ∧
    (vsHeight z t ≤ etaFlat (m * W) W → ∀ a b,
      (1 / d.C1pp) * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t)) ≤
        polynomialControl (m * W) W d.D (vsHeight z t) a b ∧
      polynomialControl (m * W) W d.D (vsHeight z t) a b ≤
        d.C1pp * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t))) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have hηt := vsHeight_pos hη ht1
  obtain ⟨hU2a, -, -, hU2d, -⟩ := ups_U2_U8_vs d hm hW hz ht0 le_rfl ht1
  obtain ⟨hK3a, hK3b, -⟩ := vsThetaRing_K3 d hm hW hz ht0 ht1
  obtain ⟨hK1, -, -, hpos⟩ := lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos
    d.C0_ge_one d.D_ge_six hm hW hz ht0 ht1
  refine ⟨fun hthr x a b => vsThetaRing_K2 d hm hW hz ht0 ht1 hthr x a b,
    fun hne hle => (etaFlat_le_iff_le_anchorTime hη
      ((anchorSet_nonempty_iff hη _ _).mp hne) ht1).mpr hle,
    fun hsm a b => ⟨(hpos a b).1, (hpos a b).2, ?_⟩, hK3a, hK3b, fun hsm => hU2d hsm⟩
  have hl := loc_eq_N hN hηt hsm
  have hCK := (vsCK_pos d).le
  refine (hK1 a b).trans ?_
  have h2 := hU2a a b
  rw [hl] at h2
  calc lemmaKConst d.b d.b_pos d.b_lt_half d.kappa d.C0 d.D *
        polynomialControl (m * W) W d.D (vsHeight z t) a b
      ≤ vsCK d * (d.C1pp / (((m * W : ℕ) : ℝ) * vsHeight z t)) :=
        mul_le_mul_of_nonneg_left h2 hCK
    _ = _ := by ring

end Reg

end BlockBand.Native.ErdosRiabov.Propagator
