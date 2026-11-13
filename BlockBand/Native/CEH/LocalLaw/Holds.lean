module

public import BlockBand.Native.CEH.LocalLaw.Bound
public import BlockBand.Native.CEH.Flow.Law
public import BlockBand.Native.CEH.Deterministic.Fields
public import BlockBand.Palm.RelativeLocalizationAdapter

/-!
# CEH local law: `externalLocalGUE_holds`

The averaged and isotropic local laws of Cipolloni–Erdős–Henheik (arXiv:2607.02446v2,
Theorem 2.3, (2.8)–(2.9)) for the deformed GUE `F + G`, `G ~ GUE_N(s/N)`, proved with no
hypotheses as `BlockBand.Native.CEH.externalLocalGUE_holds`, the statement
`BlockBand.Internal.Contracts.Inputs.ExternalLocalGUE`.

The proof runs the zig from zero variance (no global law and no zag). Fix `A, C, ε, δ, D`,
`ξ = min ε δ / 10`, and take `N₀` from two asymptotic facts (`6 + 4 log 2 + 4 log N < N^ξ`,
`32 N^{2+D} < exp(N^{2ξ}/64)`, via `isLittleO_log_rpow_atTop`). For `N ≥ N₀`, `s > 0`, `F`, a
branch `M` and `z` in the local-law domain, run the Hermitian Brownian flow `flowBM` under
`flowLaw N 0` (`flowBM_isHermitianBrownian`) along the characteristic `z_σ = z + (s - σ) m`,
`m = ⟨M(z)⟩`: `R_0 = M`, `R_s = (F + G_s - z)⁻¹`. The parameters are `K = N^ξ`, `θ = K²`, loss
`Λ = N^δ`; the smallness conditions of `zig_bootstrap` follow from `ρ ≤ 1/(π √s)`
(`density_sq_mul_le`), which gives `η_0 / η ≤ 1 + N ≤ 2^N`. The failure probability is at most
`16 N² · 2 exp(-N^{2ξ}/64) ≤ N^{-D}` (`iso_core`, `avg_core`), and the law of `F + G_s` is
transported to `gueSourceLaw` by `hermitianBrownian_isotropicBad_eq` /
`hermitianBrownian_averagedBad_eq`. Zero vectors and `B = 0` give empty bad events.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.LocalLaw

open Filter Topology Asymptotics

/-!
## Asymptotics
-/

theorem eventually_add_mul_log_lt {r : ℝ} (hr : 0 < r) (A B : ℝ) :
    ∀ᶠ x : ℝ in atTop, A + B * Real.log x < x ^ r := by
  have h1 := (isLittleO_log_rpow_atTop hr).bound (show (0 : ℝ) < 1 / (2 * (|B| + 1)) by
    positivity)
  have h2 := (tendsto_rpow_atTop hr).eventually_gt_atTop (2 * |A|)
  filter_upwards [h1, h2, eventually_gt_atTop 0] with x h1 h2 h3
  have hx : 0 < x ^ r := Real.rpow_pos_of_pos h3 r
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx] at h1
  have hB : B * Real.log x ≤ |B| * |Real.log x| := (le_abs_self _).trans (abs_mul _ _).le
  have hA : A ≤ |A| := le_abs_self A
  have h4 : |B| * |Real.log x| ≤ |B| * (1 / (2 * (|B| + 1)) * x ^ r) :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h5 : |B| * (1 / (2 * (|B| + 1)) * x ^ r) ≤ x ^ r / 2 := by
    rw [show |B| * (1 / (2 * (|B| + 1)) * x ^ r) = |B| / (|B| + 1) * (x ^ r / 2) by
      field_simp]
    have h6 : |B| / (|B| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h7 : 0 ≤ x ^ r / 2 := by positivity
    nlinarith
  linarith

theorem eventually_nat_add_mul_log_lt {r : ℝ} (hr : 0 < r) (A B : ℝ) :
    ∀ᶠ N : ℕ in atTop, A + B * Real.log N < (N : ℝ) ^ r :=
  tendsto_natCast_atTop_atTop.eventually (eventually_add_mul_log_lt hr A B)

/-- `32 N² exp(-X/64) ≤ N^{-D}` once `64 log 32 + 64 (2 + D) log N < X`. -/
theorem prob_small {N : ℕ} (hN : 1 ≤ N) {X D : ℝ}
    (h : 64 * Real.log 32 + 64 * (2 + D) * Real.log N < X) :
    32 * (N : ℝ) ^ 2 * Real.exp (-(X / 64)) ≤ (N : ℝ) ^ (-D) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : (0 : ℝ) < (N : ℝ) ^ D := Real.rpow_pos_of_pos hN0 D
  have hlog : Real.log (32 * (N : ℝ) ^ 2 * (N : ℝ) ^ D) < X / 64 := by
    rw [Real.log_mul (by positivity) hD.ne', Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_rpow hN0]
    push_cast
    linarith
  have h2 : 32 * (N : ℝ) ^ 2 * (N : ℝ) ^ D < Real.exp (X / 64) :=
    (Real.log_lt_iff_lt_exp (by positivity)).1 hlog
  rw [Real.rpow_neg hN0.le, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), inv_mul_eq_div,
    le_div_iff₀ hD]
  linarith

end BlockBand.Native.CEH.LocalLaw

namespace BlockBand.Native.CEH

open Filter MeasureTheory Set
open BlockBand.External.CEH BlockBand.Native.CEH.Phase1 BlockBand.Native.CEH.Flow
open BlockBand.Native.CEH.Zig BlockBand.Native.CEH.LocalLaw
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

/-- **CEH Theorem 2.3 for the deformed GUE**, with no hypotheses.

* *Law.* `gueSourceLaw N` (`W ~ GUE_N(1/N)`), so `√s W ~ GUE_N(s/N)`. The resolvent is
  `(F + √s W − z)⁻¹`.
* *Domain.* `CEH.InLocalLawDomain M A ε z`, in both half-planes. Only `Im z ≠ 0` and
  `N |Im z| ρ ≥ N^ε` are used. The deformation bound `s^{-1/2}‖F‖ ≤ C N^A` and the ceiling
  `|z| ≤ √s N^{A+1/ε}` are hypotheses of the statement but not used.
* *Norms.* The isotropic control uses the Euclidean vector norms and `Γ = Im M / Im ⟨M⟩`; the
  averaged control uses the normalized Hilbert–Schmidt norm. Both are the native `isotropicControl`
  and `averagedControl`.
* *Quantifiers.* For fixed `A, C, ε, δ, D` there is one `N₀ > 0`. It depends only on `ξ`
  and `D`, so it is uniform in `A, C`.
* *Uniformity.* The bound holds for all `N ≥ N₀`, uniformly in `s > 0`, `F`, the branch `M`, `z`,
  `x`, `y` and `B`. No limit is taken.
* *Dependencies.* All are hypothesis-free theorems:
  - `BlockBand.Native.CEH.mdeBranchIdentification_holds` (the branch solves the MDE; not the
    `BlockBand.Adapters.CEH` theorem of the same name);
  - `BlockBand.Palm.RelativeLocalization.flowBM_isHermitianBrownian` (the probability space);
  - `hermitianBrownian_measure_eq` (law transport);
  - `isContinuousSemimartingale_reTr_flowResolvent` (Itô), `measure_abs_compensated_ge_le`
    (tail), `zig_bootstrap` (pathwise bootstrap), and the resolvent and MDE algebra of `Phase1`;
  - `semimartingaleItoFormula_holds` and `stoppedSemimartingale_holds`, used inside those
    results. -/
theorem externalLocalGUE_holds : BlockBand.Internal.Contracts.Inputs.ExternalLocalGUE := by
  intro A C ε δ D hε hδ hD
  set ξ := min ε δ / 10 with hξdef
  have hξ : 0 < ξ := by positivity
  have hξε : ξ ≤ ε / 10 := by rw [hξdef]; gcongr; exact min_le_left _ _
  have hξδ : ξ ≤ δ / 10 := by rw [hξdef]; gcongr; exact min_le_right _ _
  have hev := ((eventually_nat_add_mul_log_lt hξ (6 + 4 * Real.log 2) 4).and
    (eventually_nat_add_mul_log_lt (by positivity : (0 : ℝ) < 2 * ξ) (64 * Real.log 32)
      (64 * (2 + D)))).and (eventually_ge_atTop 1)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  refine ⟨max N₁ 1, by positivity, ?_⟩
  intro N hN s hs F _hF M z hdom
  obtain ⟨⟨hE1, hE2⟩, hN1⟩ := hN₁ N ((le_max_left _ _).trans hN)
  have hNpos : 0 < N := hN1
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hNpos
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  obtain ⟨t, rfl⟩ : ∃ t : ℝ≥0, (t : ℝ) = s := ⟨⟨s, hs.le⟩, rfl⟩
  have hMDE : IsManuscriptMDE (t : ℝ) F z (M.matrix z) :=
    (mdeBranchIdentification_holds N hNpos t hs F).2.1 M z hdom.1
  have hz := hdom.1
  set Mz := M.matrix z with hMzdef
  set m := normalizedTrace Mz with hmdef
  set η := |z.im| with hηdef
  set c := |m.im| with hcdef
  set ρ := sourceDensity Mz with hρdef
  have hη : 0 < η := abs_pos.2 hz
  have hc : 0 < c := abs_im_trace_pos hNpos hMDE
  have hcπ : c = Real.pi * ρ := abs_im_normalizedTrace_eq_pi_mul_sourceDensity Mz
  have hρ : 0 < ρ := by
    rw [hcπ] at hc
    exact pos_of_mul_pos_right hc Real.pi_pos.le
  have hdom2 : (N : ℝ) ^ ε ≤ N * η * ρ := hdom.2.1
  have hNε1 : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNr1 hε.le
  have hNηρ : 1 ≤ (N : ℝ) * η * ρ := hNε1.trans hdom2
  -- parameters
  set K := (N : ℝ) ^ ξ with hKdef
  have hK : 0 < K := Real.rpow_pos_of_pos hNr ξ
  have hK2 : K ^ 2 = (N : ℝ) ^ (2 * ξ) := by
    rw [hKdef, ← Real.rpow_two, ← Real.rpow_mul hNr.le, mul_comm]
  have hK4 : (K ^ 2) ^ 2 = (N : ℝ) ^ (4 * ξ) := by
    rw [hK2, ← Real.rpow_two, ← Real.rpow_mul hNr.le]
    congr 1
    ring
  have hK2ε : K ^ 2 ≤ (N : ℝ) ^ ε := hK2 ▸ Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  have hK4ε : (K ^ 2) ^ 2 ≤ (N : ℝ) ^ ε :=
    hK4 ▸ Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  have hK2δ : K ^ 2 ≤ (N : ℝ) ^ δ := hK2 ▸ Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  -- the height ratio
  have hts : (0 : ℝ) ≤ t := t.2
  have hdens := density_sq_mul_le hMDE hz hts hNpos
  have hcs : c * t ≤ N * η := by
    have h1 : 1 ≤ (N : ℝ) * η * c := by
      have e : (N : ℝ) * η * c = Real.pi * (N * η * ρ) := by rw [hcπ]; ring
      rw [e]
      exact hNηρ.trans (le_mul_of_one_le_left (by positivity) (by linarith [Real.pi_gt_three]))
    calc c * t = c * t * 1 := (mul_one _).symm
      _ ≤ c * t * (N * η * c) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (c ^ 2 * t) * (N * η) := by ring
      _ ≤ 1 * (N * η) := mul_le_mul_of_nonneg_right hdens (by positivity)
      _ = N * η := one_mul _
  have hη0 : zigHeight η c t 0 ≤ (1 + N) * η := by
    have e : (1 + (N : ℝ)) * η = η + N * η := by ring
    rw [zigHeight, sub_zero, e]
    linarith
  have hpow : (1 + (N : ℝ)) ≤ 2 ^ N := by
    have : N + 1 ≤ 2 ^ N := Nat.lt_two_pow_self
    exact_mod_cast (by omega : 1 + N ≤ 2 ^ N)
  have hL : zigHeight η c t 0 ≤ 2 ^ N * η :=
    hη0.trans (mul_le_mul_of_nonneg_right hpow hη.le)
  have hη0pos : 0 < zigHeight η c t 0 := zigHeight_pos hη hc.le hts
  have hLg : Real.log (zigHeight η c t 0 / η) ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) hNr.ne']
    refine Real.log_le_log (div_pos hη0pos hη) ?_
    rw [div_le_iff₀ hη]
    exact hη0.trans (mul_le_mul_of_nonneg_right (by linarith) hη.le)
  have hLg0 : 0 ≤ Real.log (zigHeight η c t 0 / η) :=
    Real.log_nonneg ((one_le_div hη).2 (le_zigHeight hc.le hts))
  have hKbig : 6 + 4 * Real.log (zigHeight η c t 0 / η) < K := by linarith
  -- smallness
  have hsmall₁ : 4 * K * (1 + Real.log (zigHeight η c t 0 / η)) < K ^ 2 := by
    have h4 : 4 * (1 + Real.log (zigHeight η c t 0 / η)) < K := by linarith
    calc 4 * K * (1 + Real.log (zigHeight η c t 0 / η))
        = K * (4 * (1 + Real.log (zigHeight η c t 0 / η))) := by ring
      _ < K * K := mul_lt_mul_of_pos_left h4 hK
      _ = K ^ 2 := (sq K).symm
  have hNcη : (N : ℝ) * c * η = Real.pi * (N * η * ρ) := by rw [hcπ]; ring
  have hKρ : K ^ 2 ≤ N * η * ρ := hK2ε.trans hdom2
  have hsmall₂ : 2 * K ^ 2 ≤ N * c * η := by
    rw [hNcη]
    calc 2 * K ^ 2 ≤ 2 * (N * η * ρ) := by linarith
      _ ≤ Real.pi * (N * η * ρ) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (by positivity)
  have hsmall₃ : (K ^ 2) ^ 2 * ρ ≤ K ^ 2 * c ^ 2 * (N * η) := by
    have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by
      have := Real.pi_gt_three
      nlinarith
    have h1 : K ^ 2 ≤ Real.pi ^ 2 * (N * η * ρ) :=
      hKρ.trans (le_mul_of_one_le_left (by positivity) hpi)
    have h2 : K ^ 2 * c ^ 2 * (N * η) = K ^ 2 * (Real.pi ^ 2 * (N * η * ρ)) * ρ := by
      rw [hcπ]; ring
    rw [h2, sq (K ^ 2)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (sq_nonneg K)) hρ.le
  have hsmall₄ : (K ^ 2) ^ 2 ≤ N * η * ρ := hK4ε.trans hdom2
  have hfin : 2 * K + 4 * K * (1 + Real.log (zigHeight η c t 0 / η)) ≤ (N : ℝ) ^ δ := by
    have : 2 * K + 4 * K * (1 + Real.log (zigHeight η c t 0 / η)) ≤ K ^ 2 := by
      calc 2 * K + 4 * K * (1 + Real.log (zigHeight η c t 0 / η))
          = K * (6 + 4 * Real.log (zigHeight η c t 0 / η)) := by ring
        _ ≤ K * K := mul_le_mul_of_nonneg_left hKbig.le hK.le
        _ = K ^ 2 := (sq K).symm
    linarith
  have hρc : ρ ≤ c := by
    rw [hcπ]; exact le_mul_of_one_le_left hρ.le (by linarith [Real.pi_gt_three])
  have hcρ : c ≤ 8 * ρ := by
    rw [hcπ]; exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_le_four]) hρ.le
  -- the probability space
  have hG := BlockBand.Palm.RelativeLocalization.flowBM_isHermitianBrownian (N := N) 0
  have hRs : ∀ ω, pathR F.1 (BlockBand.Palm.RelativeLocalization.flowBM N) z m t ω t =
      (F.1 + BlockBand.Palm.RelativeLocalization.flowBM N t ω -
        z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := by
    intro ω
    simp [pathR, flowResolvent, flowSpectral]
  -- the final numerical bound
  have hprob : ∀ n : ℕ, n ≤ 16 * N ^ 2 →
      ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(K ^ 2 / 64)))) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
    intro n hn
    refine ENNReal.ofReal_le_ofReal ?_
    have hn' : (n : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by exact_mod_cast hn
    have h := prob_small hN1 (X := K ^ 2) (D := D) (by rw [hK2]; exact hE2)
    calc (n : ℝ) * (2 * Real.exp (-(K ^ 2 / 64)))
        ≤ 16 * (N : ℝ) ^ 2 * (2 * Real.exp (-(K ^ 2 / 64))) := by gcongr
      _ = 32 * (N : ℝ) ^ 2 * Real.exp (-(K ^ 2 / 64)) := by ring
      _ ≤ _ := h
  constructor
  · intro x y
    rw [hermitianBrownian_isotropicBad_eq hG t M x y z δ]
    by_cases hx : x = 0
    · subst hx; simp
    by_cases hy : y = 0
    · subst hy; simp
    refine le_trans (measure_mono ?_) ((iso_core hG hNpos hMDE hz hx hy hK hρ hρc hcρ hL
      hsmall₁ hsmall₂ hsmall₃ hsmall₄ hfin hNηρ).trans (hprob _ ?_))
    · intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      rw [hRs, ← sourceMatrixElement_sub]
      exact hω
    · simp only [Fintype.card_fin]
      nlinarith
  · intro B
    rw [hermitianBrownian_averagedBad_eq hG t M B z δ]
    by_cases hB : B = 0
    · subst hB; simp [normalizedTrace]
    refine le_trans (measure_mono ?_) ((avg_core hG hNpos hMDE hz hB hK hρ hρc hL
      hsmall₁ hsmall₂ hsmall₃ hsmall₄ hfin).trans (hprob _ ?_))
    · intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      rw [hRs]
      exact hω
    · simp only [Fintype.card_fin]
      nlinarith

end BlockBand.Native.CEH
