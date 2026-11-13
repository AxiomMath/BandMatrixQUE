module

public import BlockBand.GaussianBulk.ExternalSineRemainderLoop

/-!
# The uniform `O(N^{-1/2})` rate of the loop bound

For `t` in a compact subinterval of `(0, ∞)`, density `ρ ≥ v/π`, bounded `ξ` and a polynomially
bounded deformation radius, `loopRemainderBound_rate` gives `loopRemainderBound ≤ C N^{-1/2}`
with `C` uniform in the source `d`. The exponentially small outer terms are absorbed using
`N^p e^{-βN} ≤ (p+1)!/β^{p+1} · N^{-1/2}`. All statements are deterministic real inequalities.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set

/-- `N^{-1/2} = 1/√N`. -/
theorem rpow_neg_half_eq (N : ℕ) : (N:ℝ)^(-(1:ℝ)/2) = 1/Real.sqrt N := by
  rw [show -(1:ℝ)/2 = -(1/2) by ring, Real.rpow_neg (Nat.cast_nonneg N), ← Real.sqrt_eq_rpow,
    one_div]

/-- `N^p e^{-βN} ≤ (p+1)!/β^{p+1} · N^{-1/2}` for `N ≥ 1`, `β > 0`. -/
theorem pow_mul_exp_neg_le (p : ℕ) (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 1 ≤ N) :
    (N:ℝ)^p * Real.exp (-(β*N)) ≤ ((p+1).factorial / β^(p+1)) * (N:ℝ)^(-(1:ℝ)/2) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hf := Real.pow_div_factorial_le_exp (β*N) (by positivity) (p+1)
  have hfac : (0:ℝ) < (p+1).factorial := by exact_mod_cast Nat.factorial_pos _
  have h1 : (N:ℝ)^(p+1) * Real.exp (-(β*N)) ≤ (p+1).factorial / β^(p+1) := by
    rw [div_le_iff₀ hfac, mul_pow] at hf
    rw [le_div_iff₀ (by positivity)]
    have he : Real.exp (β*N) * Real.exp (-(β*N)) = 1 := by rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_right hf (Real.exp_pos (-(β*N))).le
    calc (N:ℝ)^(p+1) * Real.exp (-(β*N)) * β^(p+1)
        = β^(p+1) * (N:ℝ)^(p+1) * Real.exp (-(β*N)) := by ring
      _ ≤ Real.exp (β*N) * (p+1).factorial * Real.exp (-(β*N)) := this
      _ = (p+1).factorial := by rw [mul_comm (Real.exp _) _, mul_assoc, he, mul_one]
  have hsq : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  rw [rpow_neg_half_eq]
  calc (N:ℝ)^p * Real.exp (-(β*N)) = (N:ℝ)^(p+1) * Real.exp (-(β*N)) / N := by
        field_simp; ring
    _ ≤ ((p+1).factorial / β^(p+1)) / N := div_le_div_of_nonneg_right h1 hN0.le
    _ ≤ ((p+1).factorial / β^(p+1)) / Real.sqrt N :=
        div_le_div_of_nonneg_left (by positivity) hsq0 hsq
    _ = ((p+1).factorial / β^(p+1)) * (1 / Real.sqrt N) := by ring

/-- **Uniform rate of the loop bound.** There are `C` and `N₀` such that for `N ≥ N₀`, every source
`d` with `graftedDeformationRadius d ≤ N^(nA+1)`, `t ∈ [tLo, tHi]`, `ρ ≥ v/π` and `|ξ| ≤ Lr`, the
scale condition of the loop bound holds and `loopRemainderBound ≤ C N^{-1/2}`. -/
theorem loopRemainderBound_rate (tLo tHi v Lr : ℝ) (nA : ℕ) (htLo : 0 < tLo) (hle : tLo ≤ tHi)
    (hv : 0 < v) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (d : Fin N → ℝ) (t rho xi : ℝ),
      t ∈ Icc tLo tHi → v/Real.pi ≤ rho → |xi| ≤ Lr →
      graftedDeformationRadius d ≤ (N:ℝ)^(nA+1) →
      0 < N ∧ |xi|/(t*rho) ≤ (N:ℝ)*((tLo*v)^2/(2*tHi^2))*graftedCentralRadius tHi (tLo*v) ∧
        loopRemainderBound d t tHi (tLo*v) rho xi ≤ C * (N:ℝ)^(-(1:ℝ)/2) := by
  have htHi : 0 < tHi := lt_of_lt_of_le htLo hle
  set η := tLo*v with hηdef
  have hη : 0 < η := mul_pos htLo hv
  set c := η^2/(2*tHi^2) with hcdef
  have hc : 0 < c := by positivity
  set r := graftedCentralRadius tHi η with hrdef
  have hr : 0 < r := by
    simp only [hrdef, graftedCentralRadius]; have := Real.sqrt_pos.mpr htHi; positivity
  set kmax := |Lr| * Real.pi / (tLo*v) with hkdef
  have hk0 : 0 ≤ kmax := by positivity
  set β := c*r^2/2 with hβdef
  have hβ : 0 < β := by positivity
  set a16 := η^2/(16*tHi^2)
  set b32 := η^2/(32*tHi^2)
  have ha16 : 0 < a16 := by positivity
  have hb32 : 0 < b32 := by positivity
  set K₀ := Real.exp 4 * verticalMassConstant η tHi / r
  have hK₀ : 0 ≤ K₀ := by
    have : 0 ≤ verticalMassConstant η tHi := by unfold verticalMassConstant; positivity
    positivity
  set CU := 12 + 24*Real.sqrt tHi
  set CCB := localCrossingConstant η tHi * Real.exp (kmax^2/(2*a16)) *
      (Real.pi*Real.sqrt Real.pi/Real.sqrt b32) +
    centralFarConstant η tHi * (Real.exp (kmax^2/(2*c)) * Real.sqrt (2*Real.pi/c))
  refine ⟨K₀ * CU * ((nA+2+1).factorial / β^(nA+2+1)) + 2*CCB,
    max 1 (Nat.ceil (2*kmax/(c*r))), ?_⟩
  intro N hN d t rho xi ht hrho hxi hd
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN1r : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0:ℝ) < N := by linarith
  have hNc : 2*kmax/(c*r) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hNcr : 2*kmax ≤ N*c*r := by
    rw [div_le_iff₀ (by positivity)] at hNc; linarith
  have ht0 : 0 < t := lt_of_lt_of_le htLo ht.1
  have hrho0 : 0 < rho := lt_of_lt_of_le (div_pos hv Real.pi_pos) hrho
  -- the microscopic rate
  have hk : |xi|/(t*rho) ≤ kmax := by
    have h1 : tLo*v/Real.pi ≤ t*rho := by
      rw [mul_div_assoc]
      exact mul_le_mul ht.1 hrho (by positivity) ht0.le
    have h2 : |xi| ≤ |Lr| := hxi.trans (le_abs_self _)
    calc |xi|/(t*rho) ≤ |Lr|/(t*rho) := div_le_div_of_nonneg_right h2 (by positivity)
      _ ≤ |Lr|/(tLo*v/Real.pi) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) h1
      _ = kmax := by simp only [hkdef]; field_simp
  set k := |xi|/(t*rho) with hkk
  have hk0' : 0 ≤ k := by positivity
  refine ⟨by omega, by linarith, ?_⟩
  -- outer factor
  have hKout : outerDecayConstant N t tHi η rho xi ≤ K₀ * Real.exp (-(β*N)) := by
    unfold outerDecayConstant
    rw [← hrdef, ← hkk]
    apply mul_le_mul_of_nonneg_left _ hK₀
    apply Real.exp_le_exp.mpr
    have : N*c*r/2 ≤ N*c*r - k := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right this hr.le
    simp only [hβdef]
    nlinarith
  have hKout0 : 0 ≤ outerDecayConstant N t tHi η rho xi :=
    outerDecayConstant_nonneg N t tHi η rho xi htHi hη
  -- length factor
  have hlen : 2*upperOuterLength d t + 4*Real.sqrt t/N ≤ CU * (N:ℝ)^(nA+2) := by
    unfold upperOuterLength
    have hst : Real.sqrt t ≤ Real.sqrt tHi := Real.sqrt_le_sqrt ht.2
    have hs0 := Real.sqrt_nonneg t
    have hp1 : (1:ℝ) ≤ (N:ℝ)^(nA+1) := one_le_pow₀ hN1r
    have hp2 : (N:ℝ)^(nA+2) = (N:ℝ)^(nA+1) * N := pow_succ _ _
    have hpN : (N:ℝ) ≤ (N:ℝ)^(nA+2) := by rw [hp2]; nlinarith
    have hp1' : (1:ℝ) ≤ (N:ℝ)^(nA+2) := le_trans hN1r hpN
    have h1 : 2*graftedDeformationRadius d + 2*Real.sqrt t ≤ 2*(N:ℝ)^(nA+1) + 2*Real.sqrt tHi := by
      linarith
    have h0 : 0 ≤ 2*graftedDeformationRadius d + 2*Real.sqrt t := by
      have : 0 ≤ graftedDeformationRadius d := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      linarith
    have h2 : (1 + 2*(N:ℝ)) ≤ 3*N := by linarith
    have h3 : (2*graftedDeformationRadius d + 2*Real.sqrt t)*(1 + 2*N) ≤
        (2*(N:ℝ)^(nA+1) + 2*Real.sqrt tHi)*(3*N) := mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : 4*Real.sqrt t/N ≤ 4*Real.sqrt tHi := by
      rw [div_le_iff₀ hN0]; nlinarith
    have hs1 := Real.sqrt_nonneg tHi
    have h5 : (2*(N:ℝ)^(nA+1) + 2*Real.sqrt tHi)*(3*N) =
        6*(N:ℝ)^(nA+2) + 6*(Real.sqrt tHi*N) := by rw [hp2]; ring
    have h6 : Real.sqrt tHi * N ≤ Real.sqrt tHi * (N:ℝ)^(nA+2) :=
      mul_le_mul_of_nonneg_left hpN hs1
    have h7 : Real.sqrt tHi ≤ Real.sqrt tHi * (N:ℝ)^(nA+2) := le_mul_of_one_le_right hs1 hp1'
    have h8 : CU * (N:ℝ)^(nA+2) = 12*(N:ℝ)^(nA+2) + 24*(Real.sqrt tHi * (N:ℝ)^(nA+2)) := by
      simp only [CU]; ring
    rw [h8]
    linarith
  -- central part
  have hCB : centralCrossingBound N t tHi η rho xi ≤ CCB * (N:ℝ)^(-(1:ℝ)/2) := by
    unfold centralCrossingBound
    rw [← hkk, rpow_neg_half_eq]
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
    have e1 : Real.exp (k^2/(2*((N:ℝ)*η^2/(16*tHi^2)))) ≤ Real.exp (kmax^2/(2*a16)) := by
      apply Real.exp_le_exp.mpr
      have : (N:ℝ)*η^2/(16*tHi^2) = N*a16 := by simp only [a16]; ring
      rw [this]
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hk0' hk 2) (by positivity)
      have := mul_le_mul_of_nonneg_right hN1r ha16.le
      linarith
    have e2 : Real.pi*Real.sqrt Real.pi/Real.sqrt ((η^2/(32*tHi^2))*(N:ℝ)) =
        Real.pi*Real.sqrt Real.pi/Real.sqrt b32 * (1/Real.sqrt N) := by
      rw [Real.sqrt_mul hb32.le]
      ring
    have e3 : Real.exp (k^2/(2*(N:ℝ)*horizontalGaussianCoefficient η tHi)) ≤
        Real.exp (kmax^2/(2*c)) := by
      apply Real.exp_le_exp.mpr
      unfold horizontalGaussianCoefficient
      rw [← hcdef]
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hk0' hk 2) (by positivity)
      have := mul_le_mul_of_nonneg_right hN1r hc.le
      linarith
    have e4 : Real.sqrt (Real.pi/((N:ℝ)*horizontalGaussianCoefficient η tHi/2)) =
        Real.sqrt (2*Real.pi/c) * (1/Real.sqrt N) := by
      unfold horizontalGaussianCoefficient
      rw [← hcdef, show Real.pi/((N:ℝ)*c/2) = 2*Real.pi/c / N by ring,
        Real.sqrt_div' _ hN0.le]
      ring
    rw [e2, e4]
    have hL : 0 ≤ localCrossingConstant η tHi := by unfold localCrossingConstant; positivity
    have hF := centralFarConstant_nonneg η tHi hη
    have hq : 0 ≤ 1/Real.sqrt N := by positivity
    have hpp : 0 ≤ Real.pi*Real.sqrt Real.pi/Real.sqrt b32 := by positivity
    calc localCrossingConstant η tHi * Real.exp (k^2/(2*((N:ℝ)*η^2/(16*tHi^2)))) *
            (Real.pi*Real.sqrt Real.pi/Real.sqrt b32 * (1/Real.sqrt N)) +
          centralFarConstant η tHi *
            (Real.exp (k^2/(2*(N:ℝ)*horizontalGaussianCoefficient η tHi)) *
              (Real.sqrt (2*Real.pi/c) * (1/Real.sqrt N)))
        ≤ localCrossingConstant η tHi * Real.exp (kmax^2/(2*a16)) *
            (Real.pi*Real.sqrt Real.pi/Real.sqrt b32 * (1/Real.sqrt N)) +
          centralFarConstant η tHi *
            (Real.exp (kmax^2/(2*c)) * (Real.sqrt (2*Real.pi/c) * (1/Real.sqrt N))) := by
          gcongr
      _ = CCB * (1/Real.sqrt N) := by simp only [CCB]; ring
  -- assemble
  have hexp := pow_mul_exp_neg_le (nA+2) β hβ N hN1
  have hpow0 : 0 ≤ (N:ℝ)^(-(1:ℝ)/2) := by positivity
  unfold loopRemainderBound
  have h1 : outerDecayConstant N t tHi η rho xi * (2*upperOuterLength d t + 4*Real.sqrt t/N) ≤
      K₀ * CU * ((nA+2+1).factorial / β^(nA+2+1)) * (N:ℝ)^(-(1:ℝ)/2) := by
    calc outerDecayConstant N t tHi η rho xi * (2*upperOuterLength d t + 4*Real.sqrt t/N)
        ≤ (K₀ * Real.exp (-(β*N))) * (CU * (N:ℝ)^(nA+2)) :=
          mul_le_mul hKout hlen (by unfold upperOuterLength graftedDeformationRadius; positivity)
            (by positivity)
      _ = K₀ * CU * ((N:ℝ)^(nA+2) * Real.exp (-(β*N))) := by ring
      _ ≤ K₀ * CU * (((nA+2+1).factorial / β^(nA+2+1)) * (N:ℝ)^(-(1:ℝ)/2)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have e : 2*(outerDecayConstant N t tHi η rho xi * upperOuterLength d t +
      centralCrossingBound N t tHi η rho xi) +
        outerDecayConstant N t tHi η rho xi * (4*Real.sqrt t/N) =
      outerDecayConstant N t tHi η rho xi * (2*upperOuterLength d t + 4*Real.sqrt t/N) +
        2*centralCrossingBound N t tHi η rho xi := by ring
  rw [e, add_mul]
  have := mul_le_mul_of_nonneg_left hCB (by norm_num : (0:ℝ) ≤ 2)
  linarith

end BlockBand.GaussianBulk
