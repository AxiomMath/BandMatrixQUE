module

public import BlockBand.Critical.CommonPort.Residuals
public import BlockBand.Critical.CommonPort.Ladder
public import BlockBand.Critical.CommonPort.Comparison
public import BlockBand.Critical.CommonPort.Fluctuation

/-!
# Common-port mean: deterministic block identities and the ladder bound

Law: `layerLaw W b .common`, conditional on the deformation (every deterministic Hermitian `X`).
Notation: `𝒢 = commonPortResolvent b e X`, `P = meqPortProj 0`, `F = 𝒢P𝒢ᴴ`, `K = z_b - X`,
`ḡ = (ḡ₀, ḡ₁, ḡ_p)` the mean normalized block traces of `𝒢`, `t = (t₀, t₁, t_p)` those of `F`,
`M = (-e - X - diag(c ḡ_a + b ḡ_p))⁻¹`, `Σ = diag(c t_a + b t_p)`, `R₀ = meqResid(𝒢)`,
`R = sdResid(𝒢, F) + sdResid(F, 𝒢ᴴ)`, `δ = matchedDistance b e X`. Norms: operator norms,
complex modulus; entrywise `matrixExpect`.

The identity (from the block structure and the one-resolvent mean equation):
`E[LL*] = K (EF)₁₁ Kᴴ = (KM) Σ (KM)ᴴ + (KM) Σ (KM R₀₁₁)ᴴ + (KM)(R₁₁ Kᴴ)`.

* Section 1, deterministic: `toBlocks11_GPG`, `commonPortLL_eq_K`, `port_add_shift_common`,
  `two_res_top`, `two_res_port`, `mean_det` (the decomposition and its norm bound).
* Section 2, scalar: `ladder_source_bound` (ladder stability + source coefficient).
The assembly inequality is `mean_assembly`; the `mean` clause is
`commonPortMean_mean` and the constructor is `commonPortMean_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical BlockBand.Layers
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. Deterministic identities
-/

section Det

variable {W : ℕ}

/-- `(𝒢 P 𝒢ᴴ)₁₁ = 𝒢₁₂ 𝒢₁₂ᴴ` for the common port projector `P`. -/
theorem toBlocks11_GPG (G : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) :
    (G * meqPortProj 0 * Gᴴ).toBlocks₁₁ = G.toBlocks₁₂ * G.toBlocks₁₂ᴴ := by
  ext i j
  simp only [toBlocks₁₁, toBlocks₁₂, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type,
    meqPortProj, diagonal_apply, conjTranspose_apply]
  simp [Fin.eq_zero, mul_comm]

/-- `LL* = K (𝒢P𝒢ᴴ)₁₁ Kᴴ`. -/
theorem commonPortLL_eq_K (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) :
    commonPortLL b e X ω = matchedLeadK b e X *
      (commonPortResolvent b e X ω * meqPortProj 0 * (commonPortResolvent b e X ω)ᴴ).toBlocks₁₁ *
        (matchedLeadK b e X)ᴴ := by
  rw [toBlocks11_GPG, commonPortLL, commonPortL, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- `P + 𝒮_{c,b}(t) = diag(c t_a + b t_p) ⊕ (1 + b(t₀ + t₁))` (common port). -/
theorem port_add_shift_common (c b : ℂ) (tA : Fin LayerShape.common.blocks → ℂ)
    (tP : Fin LayerShape.common.ports → ℂ) :
    (meqPortProj 0 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) +
        meqShift .common c b tA tP =
      fromBlocks (diagonal fun x : PhysSite W .common => c * tA x.1 + b * tP 0) 0 0
        (diagonal fun _ : PortSite W .common => 1 + b * (tA 0 + tA 1)) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [meqPortProj, meqShift, meqInc, LayerShape.incident, diagonal_apply, Fin.sum_univ_two,
      Fin.eq_zero]
  all_goals (split_ifs <;> simp)

variable {E : ℝ} {z : ℂ} {X : Matrix (PhysSite W .common) (PhysSite W .common) ℂ}
  {c b : ℂ} {gA tA : Fin LayerShape.common.blocks → ℂ} {gP tP : Fin LayerShape.common.ports → ℂ}
  {Fb Hb R : Matrix (LayerSite W .common) (LayerSite W .common) ℂ}

/-- Top block of the two-resolvent equation:
`(𝒟 - 𝒮(g)) F̄ = (P + 𝒮(t)) H̄ + R` gives `T F̄₁₁ = Σ H̄₁₁ + R₁₁`. -/
theorem two_res_top
    (h : (tflConst .common E z X - meqShift .common c b gA gP) * Fb =
      (meqPortProj 0 + meqShift .common c b tA tP) * Hb + R) :
    meqTop .common E X c b gA gP * Fb.toBlocks₁₁ =
      diagonal (fun x : PhysSite W .common => c * tA x.1 + b * tP 0) * Hb.toBlocks₁₁ +
        R.toBlocks₁₁ := by
  rw [meq_D_fromBlocks, port_add_shift_common, ← fromBlocks_toBlocks Fb,
    ← fromBlocks_toBlocks Hb, ← fromBlocks_toBlocks R, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_add] at h
  have h1 := congrArg Matrix.toBlocks₁₁ h
  simpa [toBlocks_fromBlocks₁₁] using h1

/-- Port block of the two-resolvent equation:
`(z - b(g₀ + g₁)) W⁻¹Tr F̄_p = (1 + b(t₀ + t₁)) W⁻¹Tr H̄_p + W⁻¹Tr R_p`. -/
theorem two_res_port
    (h : (tflConst .common E z X - meqShift .common c b gA gP) * Fb =
      (meqPortProj 0 + meqShift .common c b tA tP) * Hb + R) :
    (z - b * (gA 0 + gA 1)) * portBlockTrace Fb 0 =
      (1 + b * (tA 0 + tA 1)) * portBlockTrace Hb 0 + portBlockTrace R 0 := by
  rw [meq_D_fromBlocks, port_add_shift_common, ← fromBlocks_toBlocks Fb,
    ← fromBlocks_toBlocks Hb, fromBlocks_multiply, fromBlocks_multiply] at h
  have hent : ∀ α : Fin W, (z - b * (gA 0 + gA 1)) * Fb (Sum.inr (0, α)) (Sum.inr (0, α)) =
      (1 + b * (tA 0 + tA 1)) * Hb (Sum.inr (0, α)) (Sum.inr (0, α)) +
        R (Sum.inr (0, α)) (Sum.inr (0, α)) := by
    intro α
    have h1 := congrFun (congrFun h (Sum.inr (0, α))) (Sum.inr (0, α))
    simp only [fromBlocks_apply₂₂, Matrix.add_apply, Matrix.zero_mul, zero_add,
      diagonal_mul, toBlocks₂₂, Matrix.of_apply] at h1
    rw [meqPortCoef, meq_sum_inc_common_port] at h1
    exact h1
  unfold portBlockTrace
  rw [mul_left_comm, Finset.mul_sum]
  simp only [hent]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- `(Nᴴ)₁₁ = (N₁₁)ᴴ`. -/
theorem toBlocks11_conjTranspose {n m : Type*} (N : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (Nᴴ).toBlocks₁₁ = (N.toBlocks₁₁)ᴴ := by
  ext i j; simp [toBlocks₁₁]

/-- `W⁻¹ Tr (Nᴴ)_p = conj (W⁻¹ Tr N_p)`. -/
theorem portBlockTrace_conjTranspose {σ : LayerShape}
    (N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (j : Fin σ.ports) :
    portBlockTrace Nᴴ j = conj (portBlockTrace N j) := by
  unfold portBlockTrace
  simp [map_sum, conjTranspose_apply]

/-- Entrywise expectations commute with `ᴴ`. -/
theorem matrixExpect_conjTranspose {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (U : Ω → Matrix ι ι ℂ) :
    matrixExpect μ (fun ω => (U ω)ᴴ) = (matrixExpect μ U)ᴴ := by
  ext x y
  simp only [matrixExpect, Matrix.of_apply, conjTranspose_apply, Complex.star_def]
  exact integral_conj

/-- `‖E U‖ ≤ E ‖U‖` for Bochner integrable `U`. -/
theorem norm_matrixExpect_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} {U : Ω → Matrix ι ι ℂ} (hU : Integrable U μ) :
    ‖matrixExpect μ U‖ ≤ ∫ ω, ‖U ω‖ ∂μ := by
  rw [meq_matrixExpect_eq hU]
  exact norm_integral_le_integral_norm _

/-- `tr_a (A + B) = tr_a A + tr_a B`. -/
theorem blockTrace_add {k : ℕ} (A B : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) (a : Fin k) :
    blockTrace (A + B) a = blockTrace A a + blockTrace B a := by
  unfold blockTrace
  simp [Finset.sum_add_distrib, mul_add]

/-- **The final decomposition** (deterministic): with `V = KM`,
`F̄₁₁ = M Σ Ḡ₁₁ᴴ + M R₁₁`, `Ḡ₁₁ = M + M R₀`:
`K F̄₁₁ Kᴴ - γ = (V - 1) Σ Vᴴ + (Σ - γ) Vᴴ + γ (Vᴴ - 1) + V Σ (V R₀)ᴴ + V (R₁₁ Kᴴ)`, hence
`‖K F̄₁₁ Kᴴ - γ‖ ≤ ‖V-1‖‖Σ‖‖V‖ + ‖Σ-γ‖‖V‖ + |γ|‖V-1‖ + ‖V‖²‖Σ‖‖R₀‖ + ‖V‖‖R₁₁Kᴴ‖`. -/
theorem mean_det {n : Type*} [Fintype n] [DecidableEq n] (K M S F11 G11 R11 R0 : Matrix n n ℂ)
    (γ : ℂ) (hF : F11 = M * S * G11ᴴ + M * R11) (hG : G11 = M + M * R0) :
    ‖K * F11 * Kᴴ - γ • 1‖ ≤
      ‖K * M - 1‖ * ‖S‖ * ‖K * M‖ + ‖S - γ • 1‖ * ‖K * M‖ + ‖γ‖ * ‖K * M - 1‖ +
        ‖K * M‖ ^ 2 * ‖S‖ * ‖R0‖ + ‖K * M‖ * ‖R11 * Kᴴ‖ := by
  set V := K * M with hV
  have hid : K * F11 * Kᴴ - γ • 1 =
      (V - 1) * S * Vᴴ + (S - γ • 1) * Vᴴ + γ • (Vᴴ - 1) + V * S * (V * R0)ᴴ +
        V * (R11 * Kᴴ) := by
    rw [hF, hG]
    simp only [hV, conjTranspose_add, conjTranspose_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.sub_mul, Matrix.smul_mul, smul_sub, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hid]
  have hVh : ‖Vᴴ‖ = ‖V‖ := l2_opNorm_conjTranspose V
  have hVh1 : ‖Vᴴ - 1‖ = ‖V - 1‖ := by
    rw [← l2_opNorm_conjTranspose (V - 1), conjTranspose_sub, conjTranspose_one]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_))
    ?_)
  · refine (l2_opNorm_mul _ _).trans ?_
    rw [hVh]
    exact mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
  · exact (l2_opNorm_mul _ _).trans (le_of_eq (by rw [hVh]))
  · rw [norm_smul, hVh1]
  · refine (l2_opNorm_mul _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    calc ‖V * S‖ * ‖V * R0‖ ≤ (‖V‖ * ‖S‖) * (‖V‖ * ‖R0‖) :=
          mul_le_mul (l2_opNorm_mul _ _) (l2_opNorm_mul _ _) (norm_nonneg _) (by positivity)
      _ = ‖V‖ ^ 2 * ‖S‖ * ‖R0‖ := by ring
  · exact l2_opNorm_mul _ _

end Det

/-!
## 2. The ladder bound in the form used by the assembly
-/

/-- **Source coefficient from the perturbed ladder** (deterministic). Hypotheses of `ladder_stability` with the contraction
`ρ(c + 2b²|ω|) ≤ q₁ < 1`, `ρ ≤ 3`, `|ω| ≤ 2`, and bounds `|ω - 1| ≤ E_ω`, `|r_p| ≤ E_p`,
`|Σ_j A_aj - d| ≤ E_s`, `|r_a| ≤ E_r`. Conclusion, `c = 1 - 2b`, `γ = (1-b)/c`:
`|c t_a + b t_p - γ| ≤ 2 Err'/(1 - q₁) + E_ω/c + E_p`,
`Err' = 3b(E_ω/c + E_p) + γ E_s + E_r`. -/
theorem ladder_source_bound {A : Fin 2 → Fin 2 → ℂ} {t r : Fin 2 → ℂ} {tp rp ω : ℂ}
    {b ρ q₁ : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) (hρ : ∀ a, ∑ j, ‖A a j‖ ≤ ρ) (hρ3 : ρ ≤ 3)
    (hq : ρ * ((1 - 2 * b) + 2 * b ^ 2 * ‖ω‖) ≤ q₁) (hq₁ : q₁ < 1) (hω : ‖ω‖ ≤ 2)
    (ht : ∀ a, t a = ∑ j, A a j * (((1 - 2 * b : ℝ) : ℂ) * t j + (b : ℂ) * tp) + r a)
    (htp : tp = ω * (1 + (b : ℂ) * (t 0 + t 1)) + rp) {Eω Ep Es Er : ℝ}
    (hEω : ‖ω - 1‖ ≤ Eω) (hEp : ‖rp‖ ≤ Ep)
    (hEs : ∀ a, ‖∑ j, A a j - ((1 - b : ℝ) : ℂ)⁻¹‖ ≤ Es) (hEr : ∀ a, ‖r a‖ ≤ Er) (a : Fin 2) :
    ‖((1 - 2 * b : ℝ) : ℂ) * t a + (b : ℂ) * tp - (((1 - b) / (1 - 2 * b) : ℝ) : ℂ)‖ ≤
      2 * ((3 * b * (Eω / (1 - 2 * b) + Ep) + (1 - b) / (1 - 2 * b) * Es + Er) / (1 - q₁)) +
        Eω / (1 - 2 * b) + Ep := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hρ0 : 0 ≤ ρ := (Finset.sum_nonneg fun j _ => norm_nonneg (A 0 j)).trans (hρ 0)
  have hqlt : ρ * ((1 - 2 * b) + 2 * b ^ 2 * ‖ω‖) < 1 := hq.trans_lt hq₁
  have hst := ladder_stability hb0 hb hρ hqlt ht htp
  dsimp only at hst
  obtain ⟨h1, h2⟩ := hst
  set q : ℝ := ρ * ((1 - 2 * b) + 2 * b ^ 2 * ‖ω‖) with hqdef
  set Sd : ℝ := max ‖∑ j, A 0 j - ((1 - b : ℝ) : ℂ)⁻¹‖ ‖∑ j, A 1 j - ((1 - b : ℝ) : ℂ)⁻¹‖
  set Rm : ℝ := max ‖r 0‖ ‖r 1‖
  set Err : ℝ := ρ * b * (‖ω - 1‖ / (1 - 2 * b) + ‖rp‖) + (1 - b) / (1 - 2 * b) * Sd + Rm
  set Err' : ℝ := 3 * b * (Eω / (1 - 2 * b) + Ep) + (1 - b) / (1 - 2 * b) * Es + Er
  have hSd : Sd ≤ Es := max_le (hEs 0) (hEs 1)
  have hRm : Rm ≤ Er := max_le (hEr 0) (hEr 1)
  have hγ0 : 0 ≤ (1 - b) / (1 - 2 * b) := div_nonneg (by linarith) hc.le
  have hEω0 : 0 ≤ Eω := (norm_nonneg _).trans hEω
  have hEp0 : 0 ≤ Ep := (norm_nonneg _).trans hEp
  have hErr0 : 0 ≤ Err := by
    have : 0 ≤ Sd := (norm_nonneg _).trans (le_max_left _ _)
    have : 0 ≤ Rm := (norm_nonneg _).trans (le_max_left _ _)
    positivity
  have hErr : Err ≤ Err' := by
    have e1 : ‖ω - 1‖ / (1 - 2 * b) + ‖rp‖ ≤ Eω / (1 - 2 * b) + Ep :=
      add_le_add (div_le_div_of_nonneg_right hEω hc.le) hEp
    have e0 : 0 ≤ ‖ω - 1‖ / (1 - 2 * b) + ‖rp‖ := by positivity
    have e2 : ρ * b * (‖ω - 1‖ / (1 - 2 * b) + ‖rp‖) ≤ 3 * b * (Eω / (1 - 2 * b) + Ep) := by
      have := mul_le_mul_of_nonneg_right hρ3 hb0
      exact mul_le_mul this e1 e0 (by positivity)
    have e3 := mul_le_mul_of_nonneg_left hSd hγ0
    linarith
  have hq1 : 0 < 1 - q₁ := by linarith
  have hE' : Err / (1 - q) ≤ Err' / (1 - q₁) := by
    have hqq : 1 - q₁ ≤ 1 - q := by linarith
    calc Err / (1 - q) ≤ Err / (1 - q₁) := div_le_div_of_nonneg_left hErr0 hq1 hqq
      _ ≤ Err' / (1 - q₁) := div_le_div_of_nonneg_right hErr hq1.le
  have hE'0 : 0 ≤ Err' / (1 - q₁) := (div_nonneg hErr0 (by linarith)).trans hE'
  refine (ladder_source_le hb0 hb (t a) tp).trans ?_
  have ha := (h1 a).trans hE'
  have hp : ‖tp - (((1 - 2 * b : ℝ)) : ℂ)⁻¹‖ ≤
      2 * b * ‖ω‖ * (Err' / (1 - q₁)) + Eω / (1 - 2 * b) + Ep := by
    refine h2.trans (add_le_add (add_le_add ?_ (div_le_div_of_nonneg_right hEω hc.le)) hEp)
    exact mul_le_mul_of_nonneg_left hE' (by positivity)
  have hb1 : b ≤ 1 := by linarith
  have hbb : b * (2 * b * ‖ω‖) ≤ 1 := by nlinarith [norm_nonneg ω]
  calc (1 - 2 * b) * ‖t a - (((1 - 2 * b : ℝ)) : ℂ)⁻¹‖ + b * ‖tp - (((1 - 2 * b : ℝ)) : ℂ)⁻¹‖
      ≤ (1 - 2 * b) * (Err' / (1 - q₁)) +
          b * (2 * b * ‖ω‖ * (Err' / (1 - q₁)) + Eω / (1 - 2 * b) + Ep) := by
        gcongr
    _ = ((1 - 2 * b) + b * (2 * b * ‖ω‖)) * (Err' / (1 - q₁)) + b * (Eω / (1 - 2 * b) + Ep) := by
        ring
    _ ≤ 2 * (Err' / (1 - q₁)) + 1 * (Eω / (1 - 2 * b) + Ep) := by
        gcongr
        linarith
    _ = 2 * (Err' / (1 - q₁)) + Eω / (1 - 2 * b) + Ep := by ring

end BlockBand.Critical.CommonPort
